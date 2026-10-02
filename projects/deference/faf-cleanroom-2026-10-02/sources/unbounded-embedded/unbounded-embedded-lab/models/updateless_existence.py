#!/usr/bin/env python3
"""
updateless_existence.py — round 2 of thread T2 (unbounded-embedded lab): the two open items of
updateless-self-game.md, §6 (existence of MIXED fixed points under the continuous extension) and
§5.5 (tightness of the repaired trust-bound theorem).

Companion note: updateless-existence.md.  Library: updateless_self_game.py (imported; its tests are
behind `if __name__ == '__main__'`, so the import is side-effect free).

Sections (each prints a header; exact claims end in assertions):
 (1)  continuity of the extended conditional F_s(a;σ) — symbolic check of the three cases
 (2)  Herrmann vs continuous-extension PURE fixed points: FP_ext ⊆ FP_Herr, and a witness instance
      where they differ (a trust-bound Herrmann fixed point that is not an extension fixed point)
 (3)  the §6 instance: an EXACT mixed fixed point (quadratic irrational), support ⊆ argmax and the
      Theorem C′ bound verified in Q(√D) arithmetic
 (4)  500 random instances: pure fixed points (both conventions), mixed fixed points found by the
      indifference solver (exact for one mixed situation, float+Newton otherwise)
 (5)  the FLOORED agent: Kakutani-compatible correspondence; an EXACT mixed floored fixed point that
      VIOLATES U* − δ/(1−δ) (refuting the note's "the mixed version follows in the same way")
 (6)  tightness of Theorem C: LP-in-U inner problem × random/local search over (P_o, π);
      exact verification of the best instances; comparison with δ/(1−δ+δ²) and δ

Exact arithmetic is fractions.Fraction, or the field Q(√D) (class QSqrt) for quadratic irrationals.
Floats are used only inside the searches; every reported extremal instance is re-verified exactly.
"""
from fractions import Fraction as F
import itertools
import math
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import updateless_self_game as usg  # noqa: E402  (side-effect free import)

policies = usg.policies
A2 = ('a', 'b')


# ----------------------------------------------------------------------------------------------
# Q(√D): exact arithmetic for quadratic irrationals  (x = a + b√D, a,b ∈ Q, D ∈ Q_{>0} not a square)
# ----------------------------------------------------------------------------------------------

class QSqrt:
    __slots__ = ('a', 'b', 'D')

    def __init__(self, a, b=0, D=None):
        self.a, self.b, self.D = F(a), F(b), D

    def _lift(self, other):
        if isinstance(other, QSqrt):
            assert self.D == other.D or other.b == 0 or self.b == 0
            return other
        return QSqrt(other, 0, self.D)

    def __add__(self, o):
        o = self._lift(o)
        return QSqrt(self.a + o.a, self.b + o.b, self.D if self.D is not None else o.D)

    __radd__ = __add__

    def __neg__(self):
        return QSqrt(-self.a, -self.b, self.D)

    def __sub__(self, o):
        return self + (-self._lift(o))

    def __rsub__(self, o):
        return self._lift(o) - self

    def __mul__(self, o):
        o = self._lift(o)
        D = self.D if self.D is not None else o.D
        return QSqrt(self.a * o.a + self.b * o.b * (D if D is not None else 0), self.a * o.b + self.b * o.a, D)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = self._lift(o)
        n = o.a * o.a - o.b * o.b * (o.D if o.D is not None else 0)   # norm
        assert n != 0
        conj = QSqrt(o.a, -o.b, o.D if o.D is not None else self.D)
        return (self * conj) * QSqrt(1 / n, 0, self.D)

    def __rtruediv__(self, o):
        return self._lift(o) / self

    def sign(self):
        """exact sign of a + b√D"""
        a, b, D = self.a, self.b, self.D
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        # opposite signs: compare a² with b²D
        if a > 0:   # b < 0
            return 1 if a * a > b * b * D else (-1 if a * a < b * b * D else 0)
        return -1 if a * a > b * b * D else (1 if a * a < b * b * D else 0)

    def __lt__(self, o): return (self - o).sign() < 0
    def __le__(self, o): return (self - o).sign() <= 0
    def __gt__(self, o): return (self - o).sign() > 0
    def __ge__(self, o): return (self - o).sign() >= 0
    def __eq__(self, o): return (self - self._lift(o)).sign() == 0

    def __float__(self):
        return float(self.a) + float(self.b) * math.sqrt(float(self.D)) if self.D is not None else float(self.a)

    def __repr__(self):
        if self.b == 0:
            return str(self.a)
        return f"({self.a} + {self.b}·√{self.D})"


# ----------------------------------------------------------------------------------------------
# mixed policies, product self-hypothesis, extended conditionals
# ----------------------------------------------------------------------------------------------

def product_weight(sigma, pi):
    """σ^⊗(π) = Π_s σ_s(π(s)).  sigma: list of dicts action -> weight (Fraction/QSqrt/float)."""
    w = 1
    for s, a in enumerate(pi):
        w = w * sigma[s].get(a, 0)
    return w


def value_mixed(U, sigma, nS, A):
    """U(σ) = E_{σ^⊗}[U]."""
    return sum(product_weight(sigma, pi) * U[pi] for pi in policies(nS, A))


def U_cond_self(U, sigma, s, a, nS, A):
    """U_a(σ) = E_{σ_{-s}^⊗}[U(a, ·)]  (the product with coordinate s fixed to a)."""
    tot = 0
    for pi in policies(nS, A):
        if pi[s] != a:
            continue
        w = 1
        for t, b in enumerate(pi):
            if t != s:
                w = w * sigma[t].get(b, 0)
        tot = tot + w * U[pi]
    return tot


def po_stats(U, Po, s, a):
    """(p_a, p_a·V_a) = (P_o(π'(s)=a), Σ_{ρ(s)=a} P_o(ρ) U(ρ))."""
    p = F(0)
    pv = F(0)
    for rho, w in Po.items():
        if rho[s] == a and w > 0:
            p += w
            pv += w * U[rho]
    return p, pv


def F_ext(U, Po, delta, sigma, s, a, nS, A):
    """Extended conditional F_s(a;σ) = [(1−δ)σ_s(a)U_a(σ) + δ p_a V_a] / [(1−δ)σ_s(a) + δ p_a],
    := U_a(σ) when the denominator vanishes.  Works for Fraction, QSqrt, float weights."""
    q = sigma[s].get(a, 0)
    Ua = U_cond_self(U, sigma, s, a, nS, A)
    p, pv = po_stats(U, Po, s, a)
    den = (1 - delta) * q + delta * p
    if den == 0:
        return Ua
    return ((1 - delta) * q * Ua + delta * pv) / den


def F_herr(U, Po, delta, sigma, s, a, nS, A):
    """Herrmann's convention: None (unavailable) when (1−δ)σ_s(a) + δ p_a = 0, else the same ratio."""
    q = sigma[s].get(a, 0)
    p, _ = po_stats(U, Po, s, a)
    if (1 - delta) * q + delta * p == 0:
        return None
    return F_ext(U, Po, delta, sigma, s, a, nS, A)


def conds(U, Po, delta, sigma, s, nS, A, convention):
    fn = F_ext if convention == 'ext' else F_herr
    return {a: fn(U, Po, delta, sigma, s, a, nS, A) for a in A}


def is_fixed_point(U, Po, delta, sigma, nS, A, convention='ext', tol=None):
    """supp σ_s ⊆ argmax_a F_s(a;σ) for every s (argmax over available actions under 'herr')."""
    for s in range(nS):
        c = conds(U, Po, delta, sigma, s, nS, A, convention)
        avail = {a: v for a, v in c.items() if v is not None}
        m = max(avail.values())
        for a, q in sigma[s].items():
            if q > 0 and (a not in avail or (avail[a] < m if tol is None else float(m) - float(avail[a]) > tol)):
                return False
    return True


def pure_sigma(pi):
    return [{a: F(1)} for a in pi]


def pure_fixed_points(U, Po, delta, nS, A, convention='ext'):
    return [pi for pi in policies(nS, A) if is_fixed_point(U, Po, delta, pure_sigma(pi), nS, A, convention)]


def trust_bound_holds(U, Po, delta, sigma, s, nS, A, Ustar, convention='ext'):
    c = conds(U, Po, delta, sigma, s, nS, A, convention)
    m = max(v for v in c.values() if v is not None)
    return m >= (1 - delta) * Ustar


# floored agent -------------------------------------------------------------------------------

def floored_allowed(U, Po, delta, sigma, s, nS, A, pistar, convention='ext'):
    """Allowed support at s for the floored agent: {π*(s)} if max F < (1−δ)U*; argmax if >;
    argmax ∪ {π*(s)} at equality (the convex-hull rule that makes the correspondence closed-graph).
    Returns (allowed set, branch)."""
    thr = (1 - delta) * U[pistar]
    c = conds(U, Po, delta, sigma, s, nS, A, convention)
    avail = {a: v for a, v in c.items() if v is not None}
    m = max(avail.values())
    am = {a for a, v in avail.items() if v == m}
    if m < thr:
        return {pistar[s]}, 'reset'
    if m > thr:
        return am, 'argmax'
    return am | {pistar[s]}, 'equality'


def is_floored_fixed_point(U, Po, delta, sigma, nS, A, pistar, convention='ext'):
    for s in range(nS):
        allowed, _ = floored_allowed(U, Po, delta, sigma, s, nS, A, pistar, convention)
        if any(q > 0 and a not in allowed for a, q in sigma[s].items()):
            return False
    return True


def floored_pure_fixed_points(U, Po, delta, nS, A, pistar, convention='ext'):
    return [pi for pi in policies(nS, A) if is_floored_fixed_point(U, Po, delta, pure_sigma(pi), nS, A, pistar, convention)]


def bound(delta):
    return delta / (1 - delta)


# ----------------------------------------------------------------------------------------------
# mixed fixed points for |A| = 2: support patterns + indifference / threshold equations
# ----------------------------------------------------------------------------------------------

def perfect_square_root(x):
    """exact √x for a Fraction x ≥ 0, or None if x is not a rational square."""
    if x < 0:
        return None
    n, d = x.numerator, x.denominator
    rn, rd = math.isqrt(n), math.isqrt(d)
    return F(rn, rd) if rn * rn == n and rd * rd == d else None


def _sigma_from(pattern, qs, exact=True):
    """pattern: tuple over s of 'a' | 'b' | 'mix' | 'thr:a' | 'thr:b' ('thr:c' = c at the threshold, other
    action = π*(s) also in the support).  qs: dict s -> σ_s(a) for the mixed situations."""
    one = F(1) if exact else 1.0
    sigma = []
    for s, pat in enumerate(pattern):
        if pat == 'a':
            sigma.append({'a': one})
        elif pat == 'b':
            sigma.append({'b': one})
        else:
            q = qs[s]
            sigma.append({'a': q, 'b': one - q})
    return sigma


def _residual(U, Po, delta, pattern, qs, nS, Ustar, exact=True):
    """cleared-denominator equations, one per mixed situation:
       'mix'  : F_s(a;σ)·den_b − F_s(b;σ)·den_a  (indifference)
       'thr:c': num_c − (1−δ)U*·den_c            (c exactly at the floor)."""
    sigma = _sigma_from(pattern, qs, exact)
    out = []
    for s, pat in enumerate(pattern):
        if pat in ('a', 'b'):
            continue
        num, den = {}, {}
        for c in A2:
            q = sigma[s].get(c, 0)
            Uc = U_cond_self(U, sigma, s, c, nS, A2)
            p, pv = po_stats(U, Po, s, c)
            num[c] = (1 - delta) * q * Uc + delta * pv
            den[c] = (1 - delta) * q + delta * p
        if pat == 'mix':
            out.append(num['a'] * den['b'] - num['b'] * den['a'])
        else:
            c = pat[-1]
            out.append(num[c] - (1 - delta) * Ustar * den[c])
    return out


def _solve_k1_exact(U, Po, delta, pattern, s, nS, Ustar):
    """one mixed situation: the residual is a polynomial of degree ≤ 2 in q = σ_s(a); solve in Q(√D)."""
    r = [_residual(U, Po, delta, pattern, {s: x}, nS, Ustar)[0] for x in (F(0), F(1, 2), F(1))]
    c0 = r[0]
    c2 = 2 * (r[2] + r[0] - 2 * r[1])
    c1 = r[2] - r[0] - c2
    roots = []
    if c2 == 0:
        if c1 != 0:
            roots.append(QSqrt(-c0 / c1, 0, None))
    else:
        D = c1 * c1 - 4 * c2 * c0
        if D >= 0:
            sq = perfect_square_root(D)
            if sq is not None:
                roots += [QSqrt((-c1 + sq) / (2 * c2), 0, None), QSqrt((-c1 - sq) / (2 * c2), 0, None)]
            else:
                # (−c1 ± √D)/(2c2) = −c1/(2c2) ± √D/(2c2)
                roots += [QSqrt(-c1 / (2 * c2), 1 / (2 * c2), D), QSqrt(-c1 / (2 * c2), -1 / (2 * c2), D)]
    return [q for q in roots if q > 0 and q < 1]


def _newton_multi(U, Po, delta, pattern, mixed, nS, Ustar, rng, starts=60, tol=1e-13):
    """k ≥ 2 mixed situations: damped Newton (finite-difference Jacobian) on the float residual from random
    starts in (0,1)^k; returns distinct interior solutions with residual < tol."""
    import numpy as np
    k = len(mixed)
    Uf = {p: float(v) for p, v in U.items()}
    Pof = {p: float(v) for p, v in Po.items()}
    d = float(delta)

    def res(x):
        qs = {s: x[i] for i, s in enumerate(mixed)}
        return np.array(_residual(Uf, Pof, d, pattern, qs, nS, float(Ustar), exact=False))

    sols = []
    for _ in range(starts):
        x = np.array([rng.random() for _ in range(k)])
        ok = False
        for it in range(80):
            r = res(x)
            if np.max(np.abs(r)) < tol:
                ok = True
                break
            J = np.zeros((k, k))
            h = 1e-7
            for j in range(k):
                e = np.zeros(k); e[j] = h
                J[:, j] = (res(x + e) - res(x - e)) / (2 * h)
            try:
                step = np.linalg.solve(J, -r)
            except np.linalg.LinAlgError:
                break
            lam = 1.0
            while lam > 1e-4:
                xn = x + lam * step
                if np.all(xn > 0) and np.all(xn < 1) and np.max(np.abs(res(xn))) < np.max(np.abs(r)):
                    break
                lam /= 2
            else:
                break
            x = xn
        if ok and np.all(x > 1e-12) and np.all(x < 1 - 1e-12):
            if not any(np.max(np.abs(x - y)) < 1e-9 for y in sols):
                sols.append(x.copy())
    return sols


def mixed_fixed_points(U, Po, delta, nS, Ustar=None, pistar=None, floored=False, rng=None, convention='ext'):
    """All mixed fixed points of the |A|=2 self-game found by pattern enumeration.
    Returns list of (pattern, sigma, exact: bool).  Genuinely mixed = at least one non-pure situation.
    floored=True: patterns may use 'thr:c' (c at the floor, π*(s) also in the support) and the fixed-point
    test is the floored one (reset / argmax / equality-hull)."""
    rng = rng or random.Random(0)
    per_s = []
    for s in range(nS):
        opts = ['a', 'b', 'mix']
        if floored:
            other = 'b' if pistar[s] == 'a' else 'a'
            opts.append('thr:' + other)
        per_s.append(opts)
    found = []
    for pattern in itertools.product(*per_s):
        mixed = [s for s, p in enumerate(pattern) if p not in ('a', 'b')]
        if not mixed:
            continue
        cands = []   # list of (qs dict, exact flag)
        if len(mixed) == 1:
            s = mixed[0]
            for q in _solve_k1_exact(U, Po, delta, pattern, s, nS, Ustar):
                cands.append(({s: q}, True))
        else:
            for x in _newton_multi(U, Po, delta, pattern, mixed, nS, Ustar, rng):
                cands.append(({s: float(x[i]) for i, s in enumerate(mixed)}, False))
        for qs, exact in cands:
            sigma = _sigma_from(pattern, qs, exact)
            if exact:
                Ue, Poe, de = U, Po, delta
            else:
                Ue = {p: float(v) for p, v in U.items()}
                Poe = {p: float(v) for p, v in Po.items()}
                de = float(delta)
            if floored:
                ok = _is_floored_fp_tol(Ue, Poe, de, sigma, nS, pistar, convention, exact)
            else:
                ok = is_fixed_point(Ue, Poe, de, sigma, nS, A2, convention, tol=None if exact else 1e-9)
            if ok:
                found.append((pattern, sigma, exact))
    return found


def _is_floored_fp_tol(U, Po, delta, sigma, nS, pistar, convention, exact):
    if exact:
        return is_floored_fixed_point(U, Po, delta, sigma, nS, A2, pistar, convention)
    thr = (1 - delta) * U[pistar]
    tol = 1e-9
    for s in range(nS):
        c = conds(U, Po, delta, sigma, s, nS, A2, convention)
        avail = {a: v for a, v in c.items() if v is not None}
        m = max(avail.values())
        am = {a for a, v in avail.items() if v > m - tol}
        if m < thr - tol:
            allowed = {pistar[s]}
        elif m > thr + tol:
            allowed = am
        else:
            allowed = am | {pistar[s]}
        if any(q > tol and a not in allowed for a, q in sigma[s].items()):
            return False
    return True


def sigma_str(sigma):
    return ' ; '.join('{' + ', '.join(f"{a}:{(repr(q) if not isinstance(q, float) else f'{q:.6f}')}" for a, q in d.items()) + '}' for d in sigma)


# ----------------------------------------------------------------------------------------------
# (1) continuity of the extended conditional (symbolic)
# ----------------------------------------------------------------------------------------------

def section_1():
    print("(1) continuity of F_s(a;σ) = [(1−δ)qU_a + δp_aV_a]/[(1−δ)q + δp_a]  (symbolic, sympy)")
    import sympy as sp
    q, Ua, pv, p, d = sp.symbols('q U_a pV p delta', real=True)
    Fq = ((1 - d) * q * Ua + d * pv) / ((1 - d) * q + d * p)
    # case p_a = 0 (then p_a V_a = 0 too): the ratio IS U_a for q > 0, so the convention value U_a at q = 0 is its limit
    assert sp.simplify(Fq.subs({p: 0, pv: 0}) - Ua) == 0
    # case δ = 0: same
    assert sp.simplify(Fq.subs({d: 0}) - Ua) == 0
    # case δ p_a > 0: denominator ≥ δ p_a > 0 for all q ∈ [0,1], so the ratio is a quotient of polynomials with
    # nonvanishing denominator — continuous; U_a itself is multilinear in σ_{-s} (a polynomial).
    den = (1 - d) * q + d * p
    assert sp.simplify(den - d * p) == (1 - d) * q   # ≥ 0 on q ≥ 0, δ ≤ 1
    print("  p_a=0 ⇒ F ≡ U_a;  δ=0 ⇒ F ≡ U_a;  δp_a>0 ⇒ denominator ≥ δp_a > 0.  (1) PASSED\n")


# ----------------------------------------------------------------------------------------------
# (2) Herrmann vs continuous extension for PURE fixed points
# ----------------------------------------------------------------------------------------------

def section_2():
    print("(2) Herrmann vs extension, pure fixed points")
    # witness: |S|=1, A={a,b}, U(a)=9/10, U(b)=1, P_o=δ_a, δ=1/10, π*=b
    U = {('a',): F(9, 10), ('b',): F(1)}
    Po = {('a',): F(1)}
    delta = F(1, 10)
    fh = pure_fixed_points(U, Po, delta, 1, A2, 'herr')
    fe = pure_fixed_points(U, Po, delta, 1, A2, 'ext')
    print(f"  witness |S|=1: U(a)=9/10, U(b)=1, P_o=δ_a, δ=1/10.  FP_Herr = {fh},  FP_ext = {fe}")
    assert fh == [('a',), ('b',)] and fe == [('b',)]
    ca = conds(U, Po, delta, pure_sigma(('a',)), 0, 1, A2, 'herr')
    ce = conds(U, Po, delta, pure_sigma(('a',)), 0, 1, A2, 'ext')
    print(f"  at π=a: Herrmann conditionals {ca} (b unavailable; TB holds: 9/10 = (1−δ)U*);  extension {ce} (b is a STRICT argmax)")
    assert ca['b'] is None and ce['b'] == 1 and ce['a'] == F(9, 10) == (1 - delta) * 1
    # the inclusion FP_ext ⊆ FP_Herr on random instances (proof: the extension's argmax is over a superset)
    rng = random.Random(20260825)
    n_diff = 0
    n_lost_all = 0
    N = 1500
    for _ in range(N):
        delta = rng.choice([F(1, 2), F(1, 4), F(1, 10), F(1, 100)])
        U, Po = usg.random_instance(rng, 3, A2, ('a', 'a', 'a'), [F(k, 8) for k in range(9)], max_support=4)
        fh = set(pure_fixed_points(U, Po, delta, 3, A2, 'herr'))
        fe = set(pure_fixed_points(U, Po, delta, 3, A2, 'ext'))
        assert fe <= fh
        n_diff += (fe != fh)
        n_lost_all += int(bool(fh) and not fe)
    print(f"  {N} random |S|=3 instances: FP_ext ⊆ FP_Herr always; FP_ext ≠ FP_Herr in {n_diff}; "
          f"Herrmann has a pure FP but the extension has none in {n_lost_all}.  (2) PASSED\n")
    return n_diff, n_lost_all


# ----------------------------------------------------------------------------------------------
# (3) the §6 instance: exact mixed fixed point
# ----------------------------------------------------------------------------------------------

def instance_s6():
    U = {p: F(0) for p in policies(3, A2)}
    U[('a', 'a', 'a')] = F(1); U[('a', 'b', 'a')] = F(1); U[('b', 'b', 'b')] = F(1); U[('a', 'a', 'b')] = F(3, 4)
    U[('b', 'a', 'b')] = F(1, 2); U[('b', 'a', 'a')] = F(3, 8); U[('b', 'b', 'a')] = F(3, 8); U[('a', 'b', 'b')] = F(1, 8)
    Po = {('a', 'a', 'a'): F(1, 4), ('a', 'b', 'a'): F(1, 4), ('a', 'b', 'b'): F(1, 4), ('b', 'b', 'b'): F(1, 4)}
    return U, Po, F(1, 10), ('a', 'a', 'a')


def section_3():
    print("(3) the §6 instance (no pure fixed point): exact mixed fixed point")
    U, Po, delta, pistar = instance_s6()
    assert pure_fixed_points(U, Po, delta, 3, A2, 'herr') == [] and pure_fixed_points(U, Po, delta, 3, A2, 'ext') == []
    fps = mixed_fixed_points(U, Po, delta, 3, Ustar=F(1))
    exact = [(p, s) for p, s, e in fps if e]
    assert len(exact) == 1 and exact[0][0] == ('mix', 'a', 'a')
    pat, sig = exact[0]
    q = sig[0]['a']
    # closed form: q = (86 + √8801)/180
    q_closed = QSqrt(F(86, 180), F(1, 180), F(8801))
    assert abs(float(q) - float(q_closed)) < 1e-15
    sig = [{'a': q_closed, 'b': 1 - q_closed}, {'a': F(1)}, {'a': F(1)}]
    assert is_fixed_point(U, Po, delta, sig, 3, A2, 'ext') and is_fixed_point(U, Po, delta, sig, 3, A2, 'herr')
    val = value_mixed(U, sig, 3, A2)
    val_closed = QSqrt(F(194, 288), F(1, 288), F(8801))
    assert val == val_closed
    print(f"  σ = (q a + (1−q) b, a, a) with q = (86+√8801)/180 ≈ {float(q_closed):.6f};  U(σ) = (194+√8801)/288 ≈ {float(val):.6f}")
    for s in range(3):
        c = conds(U, Po, delta, sig, s, 3, A2, 'ext')
        tb = trust_bound_holds(U, Po, delta, sig, s, 3, A2, F(1))
        print(f"    s{s}: F(a) ≈ {float(c['a']):.6f}, F(b) ≈ {float(c['b']):.6f}, support {sorted(a for a, w in sig[s].items() if w > 0)}, TB {tb}")
        assert tb
    assert val >= 1 - bound(delta)
    c0 = conds(U, Po, delta, sig, 0, 3, A2, 'ext')
    assert c0['a'] == c0['b']
    print(f"  support ⊆ argmax at every s (exact, Q(√8801)); TB at every s; U(σ) ≥ 1 − δ/(1−δ) = {float(1-bound(delta)):.4f}.")
    others = [(p, sigma_str(s)) for p, s, e in fps if not e]
    print(f"  further mixed fixed points (float, Newton, residual < 1e-13): {others}")
    print("  (3) PASSED\n")


# ----------------------------------------------------------------------------------------------
# (4) random instances: pure (both conventions) and mixed existence
# ----------------------------------------------------------------------------------------------

def section_4(seed=20260825, n_mixed=125, n_pure=2000):
    print("(4) random instances |S|=3, |A|=2, U on the 1/8-grid, |supp P_o| ≤ 4")
    rng = random.Random(seed)
    tot_nomix = 0
    for delta in (F(1, 2), F(1, 4), F(1, 10), F(1, 100)):
        # (a) large pure-only sweep
        nofp_h = nofp_e = nofp_fh = nofp_fe = 0
        hard = []
        for _ in range(n_pure):
            U, Po = usg.random_instance(rng, 3, A2, ('a', 'a', 'a'), [F(k, 8) for k in range(9)], max_support=4)
            fh = pure_fixed_points(U, Po, delta, 3, A2, 'herr')
            fe = pure_fixed_points(U, Po, delta, 3, A2, 'ext')
            ffh = floored_pure_fixed_points(U, Po, delta, 3, A2, ('a', 'a', 'a'), 'herr')
            ffe = floored_pure_fixed_points(U, Po, delta, 3, A2, ('a', 'a', 'a'), 'ext')
            nofp_h += (not fh); nofp_e += (not fe); nofp_fh += (not ffh); nofp_fe += (not ffe)
            if not fe or not ffe:
                hard.append((U, Po, bool(fe), bool(ffe)))
        # (b) mixed finder on every instance without a pure (plain or floored) extension fixed point
        found_plain = found_floor = 0
        n_plain = n_floor = 0
        for U, Po, has_pure, has_floor_pure in hard:
            if not has_pure:
                n_plain += 1
                fps = mixed_fixed_points(U, Po, delta, 3, Ustar=F(1), rng=rng)
                if fps:
                    found_plain += 1
                    for p, s, e in fps:
                        if e:
                            assert value_mixed(U, s, 3, A2) >= 1 - bound(delta) or not any(
                                trust_bound_holds(U, Po, delta, s, t, 3, A2, F(1)) for t in range(3))
                else:
                    tot_nomix += 1
                    print("    NO mixed fixed point found:", U, Po, delta)
            if not has_floor_pure:
                n_floor += 1
                fps = mixed_fixed_points(U, Po, delta, 3, Ustar=F(1), pistar=('a', 'a', 'a'), floored=True, rng=rng)
                found_floor += (1 if fps else 0)
                if not fps:
                    print("    NO mixed FLOORED fixed point found:", U, Po, delta)
        # (c) mixed finder on n_mixed generic instances: how common are mixed fixed points?
        n_any_mixed = 0
        for _ in range(n_mixed):
            U, Po = usg.random_instance(rng, 3, A2, ('a', 'a', 'a'), [F(k, 8) for k in range(9)], max_support=4)
            n_any_mixed += bool(mixed_fixed_points(U, Po, delta, 3, Ustar=F(1), rng=rng))
        print(f"  δ={delta}: of {n_pure}: no pure FP — Herrmann {nofp_h}, extension {nofp_e}; floored: Herrmann {nofp_fh}, extension {nofp_fe}."
              f"  Mixed FP found on {found_plain}/{n_plain} no-pure instances; mixed floored FP on {found_floor}/{n_floor}."
              f"  Generic instances with ≥1 mixed FP: {n_any_mixed}/{n_mixed}.")
    assert tot_nomix == 0
    print("  (4) PASSED\n")


# ----------------------------------------------------------------------------------------------
# (5) the floored agent: an exact mixed floored fixed point violating the bound
# ----------------------------------------------------------------------------------------------

def section_5():
    print("(5) floored agent: mixed fixed point at the equality branch, below U* − δ/(1−δ)")
    delta = F(1, 10)
    U = {('a', 'a'): F(819, 829), ('a', 'b'): F(0), ('b', 'a'): F(0), ('b', 'b'): F(1)}
    Po = {('a', 'a'): F(1)}
    pistar = ('b', 'b')
    sig = [{'a': F(9, 10), 'b': F(1, 10)}, {'a': F(9, 10), 'b': F(1, 10)}]
    for s in range(2):
        c = conds(U, Po, delta, sig, s, 2, A2, 'ext')
        allowed, branch = floored_allowed(U, Po, delta, sig, s, 2, A2, pistar)
        print(f"  s{s}: F(a) = {c['a']}, F(b) = {c['b']}, (1−δ)U* = {(1-delta)}, branch {branch}, allowed {sorted(allowed)}")
        assert c['a'] == 1 - delta and c['b'] < 1 - delta and branch == 'equality'
    assert is_floored_fixed_point(U, Po, delta, sig, 2, A2, pistar, 'ext')
    assert is_floored_fixed_point(U, Po, delta, sig, 2, A2, pistar, 'herr')
    val = value_mixed(U, sig, 2, A2)
    print(f"  U(σ) = {val} ≈ {float(val):.4f}  <  U* − δ/(1−δ) = {1-bound(delta)} ≈ {float(1-bound(delta)):.4f};  gap {1-val} ≈ {float(1-val):.4f} ≈ {float((1-val)/delta):.3f}·δ")
    assert val < 1 - bound(delta)
    # it is NOT a fixed point of the plain agent (b is not an argmax at either situation)
    assert not is_fixed_point(U, Po, delta, sig, 2, A2, 'ext')
    # the symmetric family q(1−δ−q) = δ²/(1−δ) with U(aa)=1, P_o=δ_aa: gap → 2δ
    print("  family (U(aa)=U(bb)=1, U(ab)=U(ba)=0, P_o=δ_aa, π*=bb, σ_s = q a + (1−q) b with q² − (1−δ)q + δ²/(1−δ) = 0):")
    for d in (F(1, 4), F(1, 10), F(1, 100)):
        Dd = (1 - d) ** 2 - 4 * d * d / (1 - d)
        q = QSqrt((1 - d) / 2, F(1, 2), Dd)
        U1 = {('a', 'a'): F(1), ('a', 'b'): F(0), ('b', 'a'): F(0), ('b', 'b'): F(1)}
        sg = [{'a': q, 'b': 1 - q}, {'a': q, 'b': 1 - q}]
        assert is_floored_fixed_point(U1, Po, d, sg, 2, A2, pistar, 'ext')
        v = value_mixed(U1, sg, 2, A2)
        print(f"    δ={d}: q ≈ {float(q):.6f}, U(σ) ≈ {float(v):.6f}, gap ≈ {float(1-v):.6f} = {float((1-v)/d):.4f}·δ  (bound gap δ/(1−δ) = {float(bound(d)):.6f})")
        assert v < 1 - bound(d)
    print("  (5) PASSED\n")


# ----------------------------------------------------------------------------------------------
# (6) tightness of Theorem C: sup of the gap U* − U(π) over instances with a pure fixed point π
#     WLOG π = a^S (relabel actions per situation).  Inner problem: for fixed P_o the fixed-point,
#     trust-bound and normalization constraints are LINEAR in U ⇒ LP (scipy/HiGHS).  Outer: search over P_o.
# ----------------------------------------------------------------------------------------------

def lp_gap(w, delta, nS, tb_sits, convention, rho_star, pols=None):
    """min U(π) s.t. π = a^nS is a pure fixed point (convention 'herr' or 'ext'), TB at every s in tb_sits,
    U(ρ*) = 1, U ∈ [0,1].  w: dict policy -> float weight (P_o).  Returns (gap, U dict) or (None, None)."""
    from scipy.optimize import linprog
    import numpy as np
    pols = pols or policies(nS, A2)
    idx = {p: i for i, p in enumerate(pols)}
    pi = tuple('a' for _ in range(nS))
    n = len(pols)
    A_ub, b_ub = [], []

    def row_self(s):
        """coefficients of (1−δ)U(π) + δ Σ_{ρ(s)=a} w_ρ U(ρ)  and the scalar (1−δ) + δ p^s_a"""
        r = np.zeros(n)
        r[idx[pi]] += 1 - delta
        pa = 0.0
        for rho, wr in w.items():
            if rho[s] == 'a' and wr > 0:
                r[idx[rho]] += delta * wr
                pa += wr
        return r, (1 - delta) + delta * pa

    for s in range(nS):
        rs, ds = row_self(s)
        # fixed point: F_s(a) ≥ F_s(b)
        pb = sum(wr for rho, wr in w.items() if rho[s] == 'b' and wr > 0)
        if pb > 0:
            rb = np.zeros(n)
            for rho, wr in w.items():
                if rho[s] == 'b' and wr > 0:
                    rb[idx[rho]] += wr
            # rs·U · pb ≥ ds · rb·U   ⇔  ds·rb − pb·rs ≤ 0
            A_ub.append(ds * rb - pb * rs); b_ub.append(0.0)
        elif convention == 'ext':
            dev = tuple('b' if t == s else 'a' for t in range(nS))
            rb = np.zeros(n); rb[idx[dev]] = 1.0
            A_ub.append(ds * rb - rs); b_ub.append(0.0)
        if s in tb_sits:
            # rs·U ≥ (1−δ)·ds·U*  with U* = 1
            A_ub.append(-rs); b_ub.append(-(1 - delta) * ds)
    c = np.zeros(n); c[idx[pi]] = 1.0
    bounds = [(0.0, 1.0)] * n
    bounds[idx[rho_star]] = (1.0, 1.0)
    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=bounds, method='highs')
    if res.status != 0:
        return None, None
    return 1.0 - res.x[idx[pi]], {p: float(res.x[idx[p]]) for p in pols}


def best_gap_for_w(w, delta, nS, tb_sits, convention):
    pols = policies(nS, A2)
    pi = tuple('a' for _ in range(nS))
    best = (-1.0, None, None)
    for rs in pols:
        if rs == pi:
            continue
        g, U = lp_gap(w, delta, nS, tb_sits, convention, rs, pols)
        if g is not None and g > best[0]:
            best = (g, rs, U)
    return best


def search_gap(delta, nS, tb_sits, convention, rng, n_random=300, n_local=6, verbose=False):
    """random supports + Dirichlet weights, then Nelder–Mead (softmax-parametrized) from the best few."""
    import numpy as np
    from scipy.optimize import minimize
    pols = policies(nS, A2)
    m = len(pols)

    def w_from(x, supp):
        e = np.exp(x - np.max(x))
        e = e / e.sum()
        return {p: float(e[i]) for i, p in enumerate(supp)}

    cands = []
    for _ in range(n_random):
        k = rng.randint(1, m)
        supp = rng.sample(pols, k)
        x = np.array([rng.gauss(0, 1.5) for _ in supp])
        g, rs, U = best_gap_for_w(w_from(x, supp), delta, nS, tb_sits, convention)
        cands.append((g, supp, x))
    cands.sort(key=lambda t: -t[0])
    best = (cands[0][0], None, None, None)
    for g0, supp, x0 in cands[:n_local]:
        f = lambda x: -best_gap_for_w(w_from(x, supp), delta, nS, tb_sits, convention)[0]
        res = minimize(f, x0, method='Nelder-Mead', options={'xatol': 1e-9, 'fatol': 1e-12, 'maxiter': 4000})
        g = -res.fun
        if g > best[0]:
            w = w_from(res.x, supp)
            gg, rs, U = best_gap_for_w(w, delta, nS, tb_sits, convention)
            best = (gg, w, rs, U)
    return best


def verify_exact_instance(w, U, delta, nS, tb_sits, convention, rho_star, bump=F(1, 10**5), denom=10**8):
    """Round (w, U) to rationals, raise U(π) by `bump` (which only helps every constraint), and check EXACTLY:
    π = a^nS is a pure fixed point, TB at tb_sits, U(ρ*) = 1, U ∈ [0,1].  Returns the exact gap or None."""
    pi = tuple('a' for _ in range(nS))
    wr = {p: F(v).limit_denominator(denom) for p, v in w.items() if v > 1e-12}
    tot = sum(wr.values())
    wr = {p: v / tot for p, v in wr.items()}
    Ur = {p: min(F(1), max(F(0), F(v).limit_denominator(denom))) for p, v in U.items()}
    Ur[rho_star] = F(1)
    Ur[pi] = min(F(1), Ur[pi] + bump)
    sig = pure_sigma(pi)
    if not is_fixed_point(Ur, wr, delta, sig, nS, A2, convention):
        return None, wr, Ur
    if not all(trust_bound_holds(Ur, wr, delta, sig, s, nS, A2, F(1), convention) for s in tb_sits):
        return None, wr, Ur
    assert max(Ur.values()) == 1
    return 1 - Ur[pi], wr, Ur


def family_T3(n, theta, g, delta):
    """π = a^n, U(π) = 1−g; good policies ρ_i = π with b at s_i (i=1..n−1), U = 1, P_o-mass (1−θ)/(n−1) each;
    one polluter b^n with U = 0 and mass θ.  Returns (U, Po, π)."""
    pi = tuple('a' for _ in range(n))
    U = {p: F(0) for p in policies(n, A2)}
    U[pi] = 1 - g
    Po = {}
    for i in range(1, n):
        rho = tuple('b' if t == i else 'a' for t in range(n))
        U[rho] = F(1)
        Po[rho] = (1 - theta) / (n - 1)
    Po[tuple('b' for _ in range(n))] = theta
    return U, Po, pi


def family_T3_max_gap(n, delta, tb_all, samples=4000):
    """largest g (exact rational, found by bisection over a rational grid in θ) such that T3(n, θ, g) is a
    fixed point with TB at s_0 (tb_all=False) or at every s (True).  Conditions (all exact):
      TB at s_0:  g ≤ δ + δ²(1−θ)/(1−δ)
      TB at s_i:  g ≤ δ + δ²(n−2)w/(1−δ),  w = (1−θ)/(n−1)
      FP at s_i:  w/(w+θ) ≤ [(1−δ)(1−g) + δ(n−2)w]/[(1−δ) + δ(n−2)w]     (FP at s_0 is automatic: V_b = 0)"""
    best = (F(0), None)
    for k in range(1, samples):
        theta = F(k, samples)
        w = (1 - theta) / (n - 1)
        g = delta + delta * delta * (1 - theta) / (1 - delta)
        if tb_all and n > 2:
            g = min(g, delta + delta * delta * (n - 2) * w / (1 - delta))
        if tb_all and n == 2:
            g = min(g, delta)      # TB at s_1: F_{s_1}(a) = 1−g ≥ 1−δ
        # FP at s_i: solve for the largest g:  (1−δ)(1−g) + δ(n−2)w ≥ (w/(w+θ))·[(1−δ) + δ(n−2)w]
        rhs = (w / (w + theta)) * ((1 - delta) + delta * (n - 2) * w)
        g_fp = 1 - (rhs - delta * (n - 2) * w) / (1 - delta)
        g = min(g, g_fp)
        if g > best[0]:
            best = (g, theta)
    return best


def section_6(seed=20260825, deltas=(F(1, 2), F(1, 4), F(1, 10), F(1, 100)), n_random=300, sizes=(2, 3)):
    print("(6) tightness of Theorem C: sup gap over instances with a pure fixed point (LP inner × search outer; floats)")
    rng = random.Random(seed)
    results = {}
    for delta in deltas:
        d = float(delta)
        c1 = d / (1 - d + d * d)
        print(f"  δ={delta}: conjectured (§5.5) sups: TB-one δ/(1−δ+δ²) = {c1:.6f}, TB-all δ = {d:.6f};  Theorem C bound δ/(1−δ) = {d/(1-d):.6f}")
        for nS in sizes:
            for tb_name, tb_sits in (('TB-one', {0}), ('TB-all', set(range(nS)))):
                for conv in ('herr', 'ext'):
                    g, w, rs, U = search_gap(d, nS, tb_sits, conv, rng, n_random=n_random)
                    ge, wr, Ur = verify_exact_instance(w, U, delta, nS, tb_sits, conv, rs)
                    results[(delta, nS, tb_name, conv)] = (g, ge, wr, Ur, rs)
                    print(f"    |S|={nS} {tb_name} {conv}: search gap {g:.6f}; exact-verified rational instance gap "
                          f"{(float(ge) if ge is not None else float('nan')):.6f}; ρ*={''.join(rs)}, supp P_o={[''.join(p) for p in wr]}")
                    assert ge is not None and abs(float(ge) - g) < 3e-5, "exact re-verification failed"
        # the T3 family: exact gaps for growing n
        print(f"    family T3(n): one polluter b^n diluting n−1 good single-deviation policies (exact rationals):")
        for n in (2, 3, 4, 6, 10, 30):
            g1, th1 = family_T3_max_gap(n, delta, False)
            g2, th2 = family_T3_max_gap(n, delta, True)
            U1, Po1, pi1 = family_T3(n, th1, g1, delta)
            assert is_fixed_point(U1, Po1, delta, pure_sigma(pi1), n, A2, 'ext') and trust_bound_holds(U1, Po1, delta, pure_sigma(pi1), 0, n, A2, F(1))
            U2, Po2, pi2 = family_T3(n, th2, g2, delta)
            assert is_fixed_point(U2, Po2, delta, pure_sigma(pi2), n, A2, 'ext') and all(trust_bound_holds(U2, Po2, delta, pure_sigma(pi2), s, n, A2, F(1)) for s in range(n))
            assert g1 <= bound(delta) and g2 <= bound(delta)
            print(f"      n={n:2d}: TB-one gap {float(g1):.6f} (θ={float(th1):.4f}),  TB-all gap {float(g2):.6f} (θ={float(th2):.4f})   [δ/(1−δ) = {d/(1-d):.6f}]")
    print("  (6) done\n")
    return results
