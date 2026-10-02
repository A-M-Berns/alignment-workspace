#!/usr/bin/env python3
"""
updateless_self_game.py — exact-rational model for thread T2 of the unbounded-embedded lab:
the author's proposed theorem "a UDT1.0 agent that (1-δ)-believes its policy is UDT1.1 is ε-optimal".

Everything is fractions.Fraction; there are no float assertions anywhere.

THE MODEL (founding sketches §3).  Finite situations S = {0,..,n-1}, finite actions A, policies
π ∈ A^S (tuples), utility U : A^S → [0,1], π* ∈ argmax U.  A UDT1.0 agent with belief μ over
policies plays at s:   argmax_a  E_μ[U(π') | π'(s) = a]   (pointwise EDT conditional).
Zero-probability actions:  'herrmann' = unavailable (default; Herrmann's convention),
'zero' = value 0, 'unconditional' = value E_μ[U].  A zero-probability action can never be a
STRICT argmax under any of the three conventions (E_μ[U] is a convex combination of the
available conditionals), so the three conventions differ only in tie-breaking; every
counterexample below has a strict argmax at every situation and is therefore convention-free.
"(1-δ)-believes it is UDT1.1"  :=  μ = (1-δ)·δ_{π*} + δ·P_o.

Sections (each prints a header and ends with assertions):
 (i)   exact verification of the founding-sketch counterexample
 (ii)  EXHAUSTIVE search |S|=2, |A|=2 over a rational grid  → worst gap
 (iii) randomized search |S|=3: smallest δ, smallest support, scaling of the worst gap as δ→0;
       and the FIXED-INSTANCE margin theorem (for fixed (U,P_o) the loss vanishes for small δ)
 (iv)  self-consistent fixed points (μ = (1-δ)δ_π + δP_o, π the agent's own policy): Stag Hunt
       and random instances; the repaired bound at every trust-bound fixed point; tightness
 (v)   the FLOORED agent: all fixed points within the bound
 (vi)  chosen-vs-enacted: product corruption of π* — margin theorem and a near-tie counterexample
"""
from fractions import Fraction as F
import itertools
import random
import sys

# ----------------------------------------------------------------------------------------------
# core
# ----------------------------------------------------------------------------------------------

def policies(nS, A):
    return list(itertools.product(A, repeat=nS))


def mixture(delta, self_policy, Po):
    """μ = (1-δ)·δ_{self_policy} + δ·P_o  as a dict policy -> Fraction (only positive entries)."""
    mu = {}
    if 1 - delta > 0:
        mu[self_policy] = mu.get(self_policy, F(0)) + (1 - delta)
    for pi, w in Po.items():
        if w > 0:
            mu[pi] = mu.get(pi, F(0)) + delta * w
    return mu


def conditionals(U, mu, s, A, convention='herrmann'):
    """E_μ[U(π') | π'(s) = a] for each a ∈ A.  None = unavailable (herrmann)."""
    num = {a: F(0) for a in A}
    den = {a: F(0) for a in A}
    tot = F(0)
    for pi, w in mu.items():
        if w == 0:
            continue
        num[pi[s]] += w * U[pi]
        den[pi[s]] += w
        tot += w * U[pi]
    out = {}
    for a in A:
        if den[a] > 0:
            out[a] = num[a] / den[a]
        elif convention == 'herrmann':
            out[a] = None
        elif convention == 'zero':
            out[a] = F(0)
        elif convention == 'unconditional':
            out[a] = tot
        else:
            raise ValueError(convention)
    return out


def argmax_set(cond):
    avail = {a: v for a, v in cond.items() if v is not None}
    m = max(avail.values())
    return tuple(sorted(a for a, v in avail.items() if v == m)), m


def realized_policies(U, mu, nS, A, convention='herrmann'):
    """All realized policies (product over situations of the argmax sets) + the max values."""
    sets, maxes = [], []
    for s in range(nS):
        am, m = argmax_set(conditionals(U, mu, s, A, convention))
        sets.append(am)
        maxes.append(m)
    return list(itertools.product(*sets)), maxes, sets


def trust_bound_ok(maxes, delta, Ustar):
    return [m >= (1 - delta) * Ustar for m in maxes]


def fmt(x):
    return str(x) if x is not None else '—'


def pstr(pi):
    return ''.join(str(a) for a in pi)


# ----------------------------------------------------------------------------------------------
# (i) the founding-sketch counterexample, exactly
# ----------------------------------------------------------------------------------------------

def section_i():
    print("=" * 96)
    print("(i) Founding-sketch §3 counterexample, exact rationals")
    print("=" * 96)
    nS, A = 3, ('a', 'b')
    pistar = ('a', 'a', 'a')
    eta = F(1, 100)
    delta = F(1, 10)
    U = {pi: F(0) for pi in policies(nS, A)}
    U[('a', 'a', 'a')] = F(1)
    U[('b', 'b', 'b')] = 1 - eta
    Po = {('b', 'b', 'b'): F(1, 2), ('a', 'a', 'b'): F(1, 2)}
    mu = mixture(delta, pistar, Po)
    Ustar = U[pistar]
    for conv in ('herrmann', 'zero', 'unconditional'):
        real, maxes, sets = realized_policies(U, mu, nS, A, conv)
        print(f"convention={conv}")
        for s in range(nS):
            c = conditionals(U, mu, s, A, conv)
            print(f"  s={s}: E[U|a]={fmt(c['a'])} ≈ {float(c['a']) if c['a'] is not None else '—'}, "
                  f"E[U|b]={fmt(c['b'])} ≈ {float(c['b']) if c['b'] is not None else '—'};  argmax={sets[s]};  "
                  f"TB: max={maxes[s]} >= (1-δ)U*={(1-delta)*Ustar}: {maxes[s] >= (1-delta)*Ustar}")
        assert len(real) == 1, "argmax must be unique at every situation"
        rho = real[0]
        print(f"  realized policy = {pstr(rho)},  U(realized) = {U[rho]},  U(π*) = {Ustar},  gap = {Ustar - U[rho]}")
        assert rho == ('b', 'b', 'a')
        assert U[rho] == 0 and Ustar == 1
        assert all(trust_bound_ok(maxes, delta, Ustar))
    # exact conditionals quoted in the sketch
    c1 = conditionals(U, mu, 0, A)
    assert c1['a'] == F(9, 10) / F(95, 100) == F(18, 19) and c1['b'] == F(99, 100)
    c3 = conditionals(U, mu, 2, A)
    assert c3['a'] == 1 and c3['b'] == F(99, 200)
    # the mass in the belief on the realized policy is ZERO (the belief is not self-consistent)
    assert mu.get(('b', 'b', 'a'), F(0)) == 0
    print("  belief mass on the realized policy (b,b,a):", mu.get(('b', 'b', 'a'), F(0)))

    # scaling: the family works for every δ with η < δR/(1-δ+δR), R = P_o(aab)
    print("\n  scaling in δ (η = δR/(2(1-δ+δR)), R=1/2): gap stays 1")
    for delta in (F(1, 2), F(1, 10), F(1, 100), F(1, 1000), F(1, 10**6), F(1, 10**9)):
        R = F(1, 2)
        eta = delta * R / (1 - delta + delta * R) / 2
        U2 = dict(U)
        U2[('b', 'b', 'b')] = 1 - eta
        mu2 = mixture(delta, pistar, Po)
        real, maxes, sets = realized_policies(U2, mu2, nS, A)
        assert len(real) == 1 and real[0] == ('b', 'b', 'a') and U2[real[0]] == 0
        assert all(trust_bound_ok(maxes, delta, 1))
        print(f"    δ={delta}: η={eta} realized={pstr(real[0])} gap={1 - U2[real[0]]} TB holds at all s: True")
    print("  (i) PASSED\n")


# ----------------------------------------------------------------------------------------------
# (ii) exhaustive |S|=2, |A|=2
# ----------------------------------------------------------------------------------------------

def compositions(total, parts):
    """All tuples of `parts` nonneg ints summing to `total`."""
    if parts == 1:
        yield (total,)
        return
    for i in range(total + 1):
        for rest in compositions(total - i, parts - 1):
            yield (i,) + rest


def section_ii():
    print("=" * 96)
    print("(ii) EXHAUSTIVE search |S|=2, |A|=2:  U(π*)=1, other U ∈ {0,1/4,1/2,3/4,1}, P_o weights in 1/8ths, δ ∈ {1/10,1/4,1/2}")
    print("=" * 96)
    nS, A = 2, ('a', 'b')
    pols = policies(nS, A)          # aa, ab, ba, bb
    pistar = ('a', 'a')
    grid = [F(k, 4) for k in range(5)]
    deltas = [F(1, 10), F(1, 4), F(1, 2)]
    others = [pi for pi in pols if pi != pistar]
    results = {}
    n_inst = 0
    for delta in deltas:
        worst_unique = (F(0), None)      # worst gap among instances with a unique argmax everywhere
        worst_unique_uniqopt = (F(0), None)  # ... and π* the unique maximizer of U
        worst_adv = (F(0), None)         # adversarial tie-breaking
        worst_by_support = {}
        n_pos = 0
        n_pos_uniq = 0
        n_conv_diff = 0
        for uvals in itertools.product(grid, repeat=len(others)):
            U = {pistar: F(1)}
            for pi, u in zip(others, uvals):
                U[pi] = u
            unique_opt = all(u < 1 for u in uvals)
            for comp in compositions(8, len(pols)):
                Po = {pi: F(c, 8) for pi, c in zip(pols, comp) if c > 0}
                n_inst += 1
                mu = mixture(delta, pistar, Po)
                real, maxes, sets = realized_policies(U, mu, nS, A)
                gaps = [1 - U[r] for r in real]
                # convention check: (a) Herrmann's argmax set ⊆ the other conventions' sets at every s;
                # (b) a zero-probability action is never a STRICT argmax under 'zero'/'unconditional'.
                for conv in ('zero', 'unconditional'):
                    _, _, sets2 = realized_policies(U, mu, nS, A, conv)
                    for s in range(nS):
                        if not set(sets[s]) <= set(sets2[s]):
                            n_conv_diff += 1
                        if len(sets2[s]) == 1 and sets2[s][0] not in sets[s]:
                            n_conv_diff += 1
                supp = len(Po)
                g_adv = max(gaps)
                if g_adv > worst_adv[0]:
                    worst_adv = (g_adv, (delta, dict(U), dict(Po), real))
                if len(real) == 1:
                    g = gaps[0]
                    if g > 0:
                        n_pos += 1
                    if g > worst_unique[0]:
                        worst_unique = (g, (delta, dict(U), dict(Po), real, maxes))
                    if unique_opt and g > worst_unique_uniqopt[0]:
                        worst_unique_uniqopt = (g, (delta, dict(U), dict(Po), real, maxes))
                    if g > worst_by_support.get(supp, (F(0), None))[0]:
                        worst_by_support[supp] = (g, (delta, dict(U), dict(Po), real, maxes))
                    if unique_opt and g > 0:
                        n_pos_uniq += 1
        results[delta] = dict(worst_unique=worst_unique, worst_adv=worst_adv,
                              worst_unique_uniqopt=worst_unique_uniqopt,
                              worst_by_support=worst_by_support, n_pos=n_pos, n_pos_uniq=n_pos_uniq,
                              n_conv_diff=n_conv_diff)
        g, inst = worst_unique
        print(f"δ={delta}: worst gap (strict argmax everywhere) = {g};  instances with positive gap = {n_pos};  "
              f"with π* the unique optimum = {n_pos_uniq};  convention violations (Herrmann ⊄ other, or zero-prob strict argmax) = {n_conv_diff}")
        if inst is not None:
            d, U, Po, real, maxes = inst
            mu_w = mixture(d, pistar, Po)
            all_avail = all(any(q[s] == a for q in mu_w) for s in range(nS) for a in A)
            print(f"   witness: U={{{', '.join(pstr(k)+':'+str(v) for k,v in U.items())}}}  "
                  f"P_o={{{', '.join(pstr(k)+':'+str(v) for k,v in Po.items())}}}  realized={pstr(real[0])}  "
                  f"TB at each s: {trust_bound_ok(maxes, d, F(1))};  every action has positive belief mass at every s: {all_avail}")
            assert all_avail
        g2, inst2 = worst_unique_uniqopt
        if inst2 is not None:
            d, U, Po, real, maxes = inst2
            print(f"   worst with π* the UNIQUE optimum: gap={g2}; U={{{', '.join(pstr(k)+':'+str(v) for k,v in U.items())}}}  "
                  f"P_o={{{', '.join(pstr(k)+':'+str(v) for k,v in Po.items())}}}  realized={pstr(real[0])}")
        print(f"   worst gap by |supp P_o|: " + ", ".join(f"{k}:{v[0]}" for k, v in sorted(worst_by_support.items())))
        print(f"   worst gap with adversarial tie-breaking = {worst_adv[0]}")
        assert n_conv_diff == 0
    print(f"instances examined per δ: {n_inst // len(deltas)}")
    # Assertions: the sketch's claim "two situations cannot do this" is refuted on this grid.
    for delta in deltas:
        assert results[delta]['worst_unique'][0] == 1, results[delta]['worst_unique']
        assert results[delta]['worst_adv'][0] == 1
        # support 1 never gives a strict-argmax loss; support 2 already gives total loss
        wbs = results[delta]['worst_by_support']
        assert wbs.get(1, (F(0), None))[0] == 0
        assert wbs[2][0] == 1
    # unique-optimum witnesses need U(bb) > E[U|s0=a] ≥ (1-δ)/(1-δ+7δ/8) on this grid: total loss at δ=1/2 (U(bb)=3/4 > 8/15);
    # at δ=1/4 the grid's 3/4 is below the threshold 24/31, so only the finer analytic family below shows it (every δ).
    assert results[F(1, 2)]['worst_unique_uniqopt'][0] == 1
    # the analytic 2-situation family, for every δ, with π* the UNIQUE optimum:
    print("\n  analytic |S|=2 family (π* unique optimum): P_o = ½δ_ab + ½δ_bb, U(aa)=1, U(ab)=0, U(ba)=0, U(bb)=1-η, η=δ/(2(2-δ))")
    for delta in (F(1, 2), F(1, 10), F(1, 100), F(1, 10**6), F(1, 10**9)):
        eta = delta / (2 * (2 - delta))
        U = {('a', 'a'): F(1), ('a', 'b'): F(0), ('b', 'a'): F(0), ('b', 'b'): 1 - eta}
        Po = {('a', 'b'): F(1, 2), ('b', 'b'): F(1, 2)}
        mu = mixture(delta, pistar, Po)
        real, maxes, sets = realized_policies(U, mu, nS, A)
        c0 = conditionals(U, mu, 0, A)
        assert c0['a'] == (1 - delta) / (1 - delta / 2)
        assert c0['b'] == 1 - eta > c0['a']
        assert len(real) == 1 and real[0] == ('b', 'a') and U[real[0]] == 0
        assert all(trust_bound_ok(maxes, delta, 1))
        assert mu.get(('b', 'a'), F(0)) == 0
        print(f"    δ={delta}: E[U|s0=a]={c0['a']}, E[U|s0=b]={c0['b']}; realized=ba, gap=1, TB holds everywhere")
    print("  (ii) PASSED — the founding sketch's '|S|=2 cannot do this' is REFUTED\n")
    return results


# ----------------------------------------------------------------------------------------------
# (iii) randomized |S|=3
# ----------------------------------------------------------------------------------------------

def random_instance(rng, nS, A, pistar, ugrid, max_support, allow_pistar_in_Po=True):
    pols = policies(nS, A)
    U = {pi: rng.choice(ugrid) for pi in pols}
    U[pistar] = F(1)
    k = rng.randint(1, max_support)
    cands = pols if allow_pistar_in_Po else [p for p in pols if p != pistar]
    supp = rng.sample(cands, k)
    ws = [rng.randint(1, 8) for _ in supp]
    tot = sum(ws)
    Po = {pi: F(w, tot) for pi, w in zip(supp, ws)}
    return U, Po


def po_margin(U, Po, pistar, nS, A):
    """m = min over s, a' ≠ π*(s) with P_o(s=a')>0 of  U* - E_{P_o}[U | π'(s)=a']  (None if no such a')."""
    Ustar = U[pistar]
    m = None
    for s in range(nS):
        c = conditionals(U, Po, s, A)
        for a in A:
            if a != pistar[s] and c[a] is not None:
                v = Ustar - c[a]
                m = v if m is None else min(m, v)
    return m


def section_iii(seed=20260824):
    print("=" * 96)
    print("(iii) RANDOMIZED search |S|=3, |A|=2 (belief (1-δ)δ_{π*} + δP_o, NOT self-consistent)")
    print("=" * 96)
    rng = random.Random(seed)
    nS, A = 3, ('a', 'b')
    pistar = ('a', 'a', 'a')
    deltas = [F(1, 2), F(1, 4), F(1, 10), F(1, 100), F(1, 1000), F(1, 10**6)]
    N = 6000
    summary = {}
    for delta in deltas:
        ugrid = [F(k, 8) for k in range(9)] + [1 - delta / 4, 1 - delta / 8]
        worst = (F(0), None)
        worst_uniqopt = (F(0), None)
        best_small_support = None   # smallest support achieving gap >= 1/2 (strict argmax)
        n_pos = 0
        for _ in range(N):
            U, Po = random_instance(rng, nS, A, pistar, ugrid, max_support=4)
            mu = mixture(delta, pistar, Po)
            real, maxes, sets = realized_policies(U, mu, nS, A)
            if len(real) != 1:
                continue
            g = 1 - U[real[0]]
            uniq = all(U[p] < 1 for p in U if p != pistar)
            if g > 0:
                n_pos += 1
            if g > worst[0]:
                worst = (g, (U, Po, real[0], maxes))
            if uniq and g > worst_uniqopt[0]:
                worst_uniqopt = (g, (U, Po, real[0], maxes))
            if g >= F(1, 2):
                if best_small_support is None or len(Po) < best_small_support[0]:
                    best_small_support = (len(Po), g, U, Po, real[0])
        summary[delta] = (worst[0], worst_uniqopt[0], best_small_support[0] if best_small_support else None, n_pos)
        print(f"δ={delta}: worst gap={worst[0]}  (π* unique optimum: {worst_uniqopt[0]});  "
              f"smallest |supp P_o| with gap ≥ 1/2: {best_small_support[0] if best_small_support else None};  "
              f"positive-gap instances: {n_pos}/{N}")
        if worst[1] is not None:
            U, Po, r, maxes = worst[1]
            print(f"   witness: realized={pstr(r)} U(realized)={U[r]}  P_o={{{', '.join(pstr(k)+':'+str(v) for k,v in Po.items())}}}  "
                  f"TB at each s: {trust_bound_ok(maxes, delta, F(1))}")
        assert worst[0] == 1, "expected total loss at every δ"
        assert worst_uniqopt[0] == 1, "expected total loss with π* the unique optimum"
        assert best_small_support[0] == 2, "smallest support should be 2 (support 1 needs ties)"
    print("  worst gap as δ→0 stays exactly 1 (does NOT vanish).")

    # support 1: no strict-argmax loss ever; with ties + adversarial tie-breaking, total loss.
    print("\n  support-1 P_o: strict argmax ⇒ realized = π* (proof: at s, E[U|π*(s)] = U*, E[U|π_o(s)] = U(π_o) ≤ U*);")
    print("  with a tie (U(π_o) = U*) and ADVERSARIAL tie-breaking the realized policy can be off-support with U = 0:")
    U = {('a', 'a'): F(1), ('b', 'b'): F(1), ('a', 'b'): F(0), ('b', 'a'): F(0)}
    Po = {('b', 'b'): F(1)}
    for delta in (F(1, 10), F(1, 10**6)):
        mu = mixture(delta, ('a', 'a'), Po)
        real, maxes, sets = realized_policies(U, mu, 2, A)
        assert sets == [('a', 'b'), ('a', 'b')] and ('a', 'b') in real and U[('a', 'b')] == 0
        print(f"    δ={delta}: argmax sets {sets}; adversarial realized ab, U=0; uniform-tie expected U = {sum(U[r] for r in real)/len(real)}")
    # random support-1 check, strict case
    rng2 = random.Random(seed + 1)
    for _ in range(3000):
        U, Po = random_instance(rng2, nS, A, pistar, [F(k, 8) for k in range(9)], max_support=1)
        delta = rng2.choice(deltas)
        mu = mixture(delta, pistar, Po)
        real, maxes, sets = realized_policies(U, mu, nS, A)
        if len(real) == 1:
            assert real[0] == pistar

    # FIXED-INSTANCE margin theorem: for fixed (U, P_o) with P_o-margin m > 0, realized = π* once δ < m/U*.
    print("\n  fixed-instance margin theorem (PROVED in the .md): m := min_{s, a'≠π*(s), P_o(s=a')>0} (U* − E_{P_o}[U|s=a']) > 0")
    print("  ⇒ for δ < m/U* the realized policy is exactly π*  (checked on random instances):")
    rng3 = random.Random(seed + 2)
    n_checked = 0
    n_margin_zero_dev = 0
    for _ in range(4000):
        U, Po = random_instance(rng3, nS, A, pistar, [F(k, 8) for k in range(9)], max_support=4)
        m = po_margin(U, Po, pistar, nS, A)
        if m is None:
            continue
        if m > 0:
            for delta in (m / 2, m / 4, m / 100):
                mu = mixture(delta, pistar, Po)
                real, maxes, sets = realized_policies(U, mu, nS, A)
                assert real == [pistar], (U, Po, delta, real)
                n_checked += 1
        else:
            # m == 0: some deviation is supported by fully-optimal P_o-mass; it ties or beats π*(s) at EVERY δ>0
            mu = mixture(F(1, 10**6), pistar, Po)
            real, maxes, sets = realized_policies(U, mu, nS, A)
            if real != [pistar]:
                n_margin_zero_dev += 1
    print(f"    {n_checked} (instance, δ) pairs with δ < m/U*: realized = π* in all;  margin-0 instances deviating/tying at δ=1e-6: {n_margin_zero_dev}")
    assert n_checked > 500
    print("  (iii) PASSED\n")
    return summary


# ----------------------------------------------------------------------------------------------
# (iv) self-consistent fixed points
# ----------------------------------------------------------------------------------------------

def fixed_points(U, Po, delta, nS, A, convention='herrmann'):
    """Pure fixed points of the self-consistent UDT1.0 agent: π with π(s) ∈ argmax_a E_{μ_π}[U|s=a] ∀s.
    Returns list of (π, maxes, sets, ps) where ps[s] = P_o(π'(s)=π(s))."""
    out = []
    for pi in policies(nS, A):
        mu = mixture(delta, pi, Po)
        ok = True
        maxes, sets, ps = [], [], []
        for s in range(nS):
            am, m = argmax_set(conditionals(U, mu, s, A, convention))
            if pi[s] not in am:
                ok = False
                break
            maxes.append(m)
            sets.append(am)
            ps.append(sum(w for q, w in Po.items() if q[s] == pi[s]))
        if ok:
            out.append((pi, maxes, sets, ps))
    return out


def repaired_bound(delta):
    return delta / (1 - delta)


def check_repaired(U, Po, delta, nS, A, Ustar, fps):
    """At every fixed point with TB at some s: U(π) ≥ U* − δ/(1−δ) and the p-dependent bound at each TB situation."""
    for pi, maxes, sets, ps in fps:
        tb = trust_bound_ok(maxes, delta, Ustar)
        if any(tb):
            assert U[pi] >= Ustar - repaired_bound(delta), (pi, U[pi], Ustar, delta)
            for s in range(nS):
                if tb[s]:
                    p = ps[s]
                    assert U[pi] >= Ustar * (1 - delta + delta * p) - delta * p / (1 - delta)


def section_iv(seed=20260824):
    print("=" * 96)
    print("(iv) SELF-CONSISTENT fixed points  μ = (1-δ)δ_π + δP_o  (π = the agent's own policy)")
    print("=" * 96)
    A = ('S', 'H')
    nS = 2
    # Stag Hunt, b=4, c=3, utilities = sum of payoffs / (2b): SS=1, HH=c/b=3/4, SH=HS=c/(2b)=3/8
    U = {('S', 'S'): F(1), ('H', 'H'): F(3, 4), ('S', 'H'): F(3, 8), ('H', 'S'): F(3, 8)}
    Po = {('S', 'H'): F(1, 2), ('H', 'S'): F(1, 2)}
    pistar = ('S', 'S')
    print("Stag Hunt (SS=1, HH=3/4, SH=HS=3/8), P_o = ½δ_SH + ½δ_HS:")
    for delta in (F(1, 20), F(1, 10), F(1, 5), F(1, 4), F(3, 10), F(1, 2), F(9, 10)):
        fps = fixed_points(U, Po, delta, nS, A)
        desc = []
        for pi, maxes, sets, ps in fps:
            tb = trust_bound_ok(maxes, delta, F(1))
            desc.append(f"{pstr(pi)}[U={U[pi]}, TB={tb}, max={maxes[0]}]")
        print(f"  δ={delta}: fixed points: " + "; ".join(desc) + f";  bound U* − δ/(1−δ) = {1 - repaired_bound(delta)}")
        names = [fp[0] for fp in fps]
        assert ('S', 'S') in names and ('H', 'H') in names   # both are fixed points for every δ
        check_repaired(U, Po, delta, nS, A, F(1), fps)
        hh = [fp for fp in fps if fp[0] == ('H', 'H')][0]
        tb_hh = trust_bound_ok(hh[1], delta, F(1))
        # exact TB condition at HH: E[U|H] = ((1-δ)·3/4 + (δ/2)·3/8)/(1-δ/2) ≥ 1-δ
        lhs = ((1 - delta) * F(3, 4) + (delta / 2) * F(3, 8)) / (1 - delta / 2)
        assert tb_hh[0] == (lhs >= 1 - delta)
        assert all(trust_bound_ok([fp for fp in fps if fp[0] == ('S', 'S')][0][1], delta, F(1)))
    # HH violates TB iff δ < δ_c where (1-δ)(3/4) + (δ/2)(3/8) = (1-δ)(1-δ/2): solve exactly on the grid
    print("  HH is a fixed point for EVERY δ; it violates TB for small δ (trap), satisfies it for large δ (bound vacuous).")
    print("  SS is a fixed point for every δ and satisfies TB for every δ.")

    # the counterexample instance of (i): which policies are self-consistent fixed points?
    print("\nCounterexample instance of (i) as a self-game (δ=1/10):")
    A2 = ('a', 'b')
    nS2 = 3
    U2 = {pi: F(0) for pi in policies(nS2, A2)}
    U2[('a', 'a', 'a')] = F(1)
    U2[('b', 'b', 'b')] = F(99, 100)
    Po2 = {('b', 'b', 'b'): F(1, 2), ('a', 'a', 'b'): F(1, 2)}
    delta = F(1, 10)
    fps = fixed_points(U2, Po2, delta, nS2, A2)
    for pi, maxes, sets, ps in fps:
        print(f"  fixed point {pstr(pi)}: U={U2[pi]}, TB={trust_bound_ok(maxes, delta, F(1))}, bound={1 - repaired_bound(delta)}")
    names = [fp[0] for fp in fps]
    assert ('a', 'a', 'a') not in names       # π* is NOT a fixed point of the self-consistent agent here
    assert ('b', 'b', 'b') in names
    assert ('b', 'b', 'a') not in names       # the original counterexample's realized policy is not self-consistent
    check_repaired(U2, Po2, delta, nS2, A2, F(1), fps)

    # tightness families
    print("\nTightness of the repaired bound U(π) ≥ U* − δ/(1−δ):")
    print("  family T1 (|S|=2, TB required at s0 only): π=(a,b), P_o=(1-θ)δ_aa+θδ_ba, U(aa)=1, U(ba)=0, U(ab)=1-g, g=θ=δ/(1-δ+δ²)")
    for delta in (F(1, 2), F(1, 4), F(1, 10), F(1, 100)):
        theta = delta / (1 - delta + delta * delta)
        g = theta
        U3 = {('a', 'a'): F(1), ('b', 'a'): F(0), ('a', 'b'): 1 - g, ('b', 'b'): F(0)}
        Po3 = {('a', 'a'): 1 - theta, ('b', 'a'): theta}
        fps = fixed_points(U3, Po3, delta, 2, A2)
        fp = [f for f in fps if f[0] == ('a', 'b')]
        assert fp, "π=(a,b) should be a fixed point"
        pi, maxes, sets, ps = fp[0]
        tb = trust_bound_ok(maxes, delta, F(1))
        assert tb[0] and maxes[0] == 1 - delta   # TB at s0 holds with EQUALITY
        assert (not tb[1]) or delta >= F(1, 2)   # TB at s1 fails for small δ (g > δ)
        check_repaired(U3, Po3, delta, 2, A2, F(1), fps)
        print(f"    δ={delta}: gap g={g} (= {float(g):.6f}),  bound δ/(1−δ)={repaired_bound(delta)} (= {float(repaired_bound(delta)):.6f}),  "
              f"δ={float(delta):.6f};  TB at s0: {tb[0]} (equality), at s1: {tb[1]}")
    print("  family T2 (|S|=3, TB at ALL situations): π=(a,b,a), P_o=(1-θ)δ_aaa+θδ_aab, U(aaa)=1, U(aab)=0, U(aba)=1-δ, θ=δ")
    for delta in (F(1, 4), F(1, 10), F(1, 100)):
        theta = delta
        U4 = {pi: F(0) for pi in policies(3, A2)}
        U4[('a', 'a', 'a')] = F(1)
        U4[('a', 'b', 'a')] = 1 - delta
        Po4 = {('a', 'a', 'a'): 1 - theta, ('a', 'a', 'b'): theta}
        fps = fixed_points(U4, Po4, delta, 3, A2)
        fp = [f for f in fps if f[0] == ('a', 'b', 'a')]
        assert fp
        pi, maxes, sets, ps = fp[0]
        tb = trust_bound_ok(maxes, delta, F(1))
        assert all(tb)
        check_repaired(U4, Po4, delta, 3, A2, F(1), fps)
        print(f"    δ={delta}: gap = {1 - U4[pi]} = δ;  TB at all s: {tb};  argmax sets {sets} (tie at s1)")

    # random instances: enumerate fixed points, check the repaired bound at all TB fixed points, record tightness/existence
    print("\nRandom instances (|S|=3, |A|=2, U on grid 1/8, |supp P_o| ≤ 4):")
    rng = random.Random(seed)
    nS, A = 3, ('a', 'b')
    pistar = ('a', 'a', 'a')
    stats = {}
    for delta in (F(1, 2), F(1, 4), F(1, 10), F(1, 100)):
        n = 3000
        n_nofp = 0
        n_tbfp = 0
        worst_ratio = F(0)     # (U* − U(π)) / (δ/(1−δ)) over TB fixed points
        worst_gap = F(0)
        worst_gap_alltb = F(0)
        n_pistar_notfp = 0
        for _ in range(n):
            U, Po = random_instance(rng, nS, A, pistar, [F(k, 8) for k in range(9)], max_support=4)
            fps = fixed_points(U, Po, delta, nS, A)
            check_repaired(U, Po, delta, nS, A, F(1), fps)
            if not fps:
                n_nofp += 1
            if pistar not in [f[0] for f in fps]:
                n_pistar_notfp += 1
            for pi, maxes, sets, ps in fps:
                tb = trust_bound_ok(maxes, delta, F(1))
                if any(tb):
                    n_tbfp += 1
                    g = 1 - U[pi]
                    worst_gap = max(worst_gap, g)
                    worst_ratio = max(worst_ratio, g / repaired_bound(delta))
                if all(tb):
                    worst_gap_alltb = max(worst_gap_alltb, 1 - U[pi])
        stats[delta] = (n_nofp, n_tbfp, worst_gap, worst_ratio, worst_gap_alltb, n_pistar_notfp)
        print(f"  δ={delta}: instances with NO pure fixed point: {n_nofp}/{n};  π* not a fixed point: {n_pistar_notfp}/{n};  "
              f"TB fixed points seen: {n_tbfp};  worst gap at a TB fixed point: {worst_gap} (= {float(worst_gap):.4f}; "
              f"δ/(1−δ) = {float(repaired_bound(delta)):.4f}, ratio {float(worst_ratio):.3f});  worst gap with TB at ALL s: {worst_gap_alltb} (= {float(worst_gap_alltb):.4f}, δ = {float(delta):.4f})")
    print("  (iv) PASSED — the repaired bound held at every trust-bound fixed point examined\n")
    return stats


# ----------------------------------------------------------------------------------------------
# (v) the floored agent
# ----------------------------------------------------------------------------------------------

def floored_fixed_points(U, Po, delta, nS, A, pistar, convention='herrmann'):
    """Pure fixed points of the FLOORED agent: at s, if max_a E[U|a] < (1-δ)U* play π*(s); if > play an argmax;
    at equality either is allowed (mixing)."""
    Ustar = U[pistar]
    out = []
    for pi in policies(nS, A):
        mu = mixture(delta, pi, Po)
        ok = True
        maxes, modes = [], []
        for s in range(nS):
            am, m = argmax_set(conditionals(U, mu, s, A, convention))
            thr = (1 - delta) * Ustar
            if m < thr:
                allowed = (pistar[s],)
                mode = 'reset'
            elif m > thr:
                allowed = am
                mode = 'argmax'
            else:
                allowed = tuple(sorted(set(am) | {pistar[s]}))
                mode = 'equality'
            if pi[s] not in allowed:
                ok = False
                break
            maxes.append(m)
            modes.append(mode)
        if ok:
            out.append((pi, maxes, modes))
    return out


def section_v(seed=20260824):
    print("=" * 96)
    print("(v) FLOORED agent: reset to π*(s) when max_a E[U|a] < (1-δ)U*, else argmax (mix at equality)")
    print("=" * 96)
    A = ('a', 'b')
    # counterexample instance
    nS = 3
    U = {pi: F(0) for pi in policies(nS, A)}
    U[('a', 'a', 'a')] = F(1)
    U[('b', 'b', 'b')] = F(99, 100)
    Po = {('b', 'b', 'b'): F(1, 2), ('a', 'a', 'b'): F(1, 2)}
    pistar = ('a', 'a', 'a')
    delta = F(1, 10)
    fps = floored_fixed_points(U, Po, delta, nS, A, pistar)
    print("counterexample instance, δ=1/10, floored fixed points:")
    for pi, maxes, modes in fps:
        print(f"  {pstr(pi)}: U={U[pi]}, modes={modes}, bound={1 - repaired_bound(delta)}")
        assert U[pi] >= 1 - repaired_bound(delta)
    assert [f[0] for f in fps] == [('b', 'b', 'b')]
    # Stag Hunt: the trap HH is eliminated by the floor exactly when it violates TB
    A2 = ('S', 'H')
    U2 = {('S', 'S'): F(1), ('H', 'H'): F(3, 4), ('S', 'H'): F(3, 8), ('H', 'S'): F(3, 8)}
    Po2 = {('S', 'H'): F(1, 2), ('H', 'S'): F(1, 2)}
    print("Stag Hunt, floored fixed points:")
    for delta in (F(1, 20), F(1, 10), F(1, 5), F(1, 4), F(3, 10), F(1, 2)):
        fps = floored_fixed_points(U2, Po2, delta, 2, A2, ('S', 'S'))
        names = [f[0] for f in fps]
        print(f"  δ={delta}: {[pstr(n) for n in names]}  (bound U* − δ/(1−δ) = {1 - repaired_bound(delta)})")
        assert ('S', 'S') in names
        for pi, maxes, modes in fps:
            assert U2[pi] >= 1 - repaired_bound(delta)
        plain = [f[0] for f in fixed_points(U2, Po2, delta, 2, A2)]
        hh_tb = all(trust_bound_ok([f for f in fixed_points(U2, Po2, delta, 2, A2) if f[0] == ('H', 'H')][0][1], delta, F(1)))
        assert (('H', 'H') in names) == hh_tb
    # random instances
    print("Random instances (|S|=3, |A|=2): all floored fixed points within the bound; existence of pure fixed points:")
    rng = random.Random(seed)
    nS = 3
    pistar = ('a', 'a', 'a')
    for delta in (F(1, 2), F(1, 4), F(1, 10), F(1, 100)):
        n = 3000
        n_nofp = 0
        n_fp = 0
        worst = F(0)
        n_reset_fp = 0
        for _ in range(n):
            U, Po = random_instance(rng, nS, A, pistar, [F(k, 8) for k in range(9)], max_support=4)
            fps = floored_fixed_points(U, Po, delta, nS, A, pistar)
            if not fps:
                n_nofp += 1
            for pi, maxes, modes in fps:
                n_fp += 1
                g = 1 - U[pi]
                assert g <= repaired_bound(delta), (U, Po, pi, delta)
                worst = max(worst, g)
                if 'reset' in modes:
                    n_reset_fp += 1
        print(f"  δ={delta}: fixed points {n_fp} over {n} instances (no pure fixed point: {n_nofp});  "
              f"worst gap {worst} (= {float(worst):.4f}) vs bound {float(repaired_bound(delta)):.4f};  fixed points with a reset situation: {n_reset_fp}")
    print("  (v) PASSED — every pure floored fixed point examined is within U* − δ/(1−δ)\n")


# ----------------------------------------------------------------------------------------------
# (vi) chosen vs enacted
# ----------------------------------------------------------------------------------------------

def corruption_belief(pistar, delta, nS, A):
    """Product measure: each coordinate = π*(s) w.p. 1-δ, else uniform over the other actions."""
    mu = {}
    others = {s: [a for a in A if a != pistar[s]] for s in range(nS)}
    for pi in policies(nS, A):
        w = F(1)
        for s in range(nS):
            if pi[s] == pistar[s]:
                w *= (1 - delta)
            else:
                w *= delta / len(others[s])
        if w > 0:
            mu[pi] = w
    return mu


def base_margin(U, pistar, nS, A):
    """m_s = U(π*) − max_{a≠π*(s)} U(a, π*_{-s}); returns min over s."""
    m = None
    for s in range(nS):
        for a in A:
            if a == pistar[s]:
                continue
            q = list(pistar)
            q[s] = a
            v = U[pistar] - U[tuple(q)]
            m = v if m is None else min(m, v)
    return m


def section_vi(seed=20260824):
    print("=" * 96)
    print("(vi) CHOSEN vs ENACTED: belief = independent per-situation corruption of π* at rate δ")
    print("=" * 96)
    A = ('a', 'b')
    nS = 3
    pistar = ('a', 'a', 'a')
    # Reading C1: the agent conditions on its ENACTED action; under a product belief the conditional is
    # E_{μ_{-s}}[U(a, π'_{-s})] (an intervention), so the CHOSEN policy is argmax of that.
    print("near-tie example: U = 1 on all policies except U(aab)=0 and U(bba)=ε; base ties U(baa)=U(aba)=U(aaa)=1")
    for eps in (F(1, 100), F(1, 10**6)):
        for delta in (F(1, 4), F(1, 10), F(1, 100), F(1, 10**6)):
            U = {pi: F(1) for pi in policies(nS, A)}
            U[('a', 'a', 'b')] = F(0)
            U[('b', 'b', 'a')] = eps
            mu = corruption_belief(pistar, delta, nS, A)
            assert sum(mu.values()) == 1
            real, maxes, sets = realized_policies(U, mu, nS, A)
            c0 = conditionals(U, mu, 0, A)
            # exact first-order formula: E[U|s0=b] − E[U|s0=a] = δ(1-δ)ε  (with U(bbb)=1)
            assert c0['b'] - c0['a'] == delta * (1 - delta) * eps
            assert len(real) == 1 and real[0] == ('b', 'b', 'a') and U[real[0]] == eps, (delta, real)
            # the believed problem's optimum (corrupted-utility): Ũ(π) = E[U(corrupt(π))]
            def Ut(pi):
                return sum(w * U[q] for q, w in corruption_belief(pi, delta, nS, A).items())
            print(f"  ε={eps}, δ={delta}: chosen policy = {pstr(real[0])}, U(chosen)={U[real[0]]}, U(π*)=1;  "
                  f"Ũ(chosen)={float(Ut(real[0])):.6f}, Ũ(π*)={float(Ut(pistar)):.6f}, max_π Ũ={float(max(Ut(p) for p in policies(nS, A))):.6f}")
    print("  ⇒ under reading C1 the chosen policy can be far from optimal at every δ (near-tie), loss → 1 as ε → 0.")

    # margin theorem: if m_s > 2ρ, ρ = 1-(1-δ)^{|S|-1}, at every s then chosen = π* exactly
    print("\nmargin theorem (PROVED in the .md): m := min_s [U(π*) − max_{a≠π*(s)} U(a, π*_{-s})] > 2(1−(1−δ)^{|S|−1}) ⇒ chosen = π*")
    rng = random.Random(seed)
    n_checked = 0
    n_viol_without_margin = 0
    n_without_margin = 0
    for _ in range(3000):
        U = {pi: rng.choice([F(k, 8) for k in range(9)]) for pi in policies(nS, A)}
        U[pistar] = F(1)
        m = base_margin(U, pistar, nS, A)
        delta = rng.choice([F(1, 4), F(1, 10), F(1, 100), F(1, 1000)])
        rho = 1 - (1 - delta) ** (nS - 1)
        mu = corruption_belief(pistar, delta, nS, A)
        real, maxes, sets = realized_policies(U, mu, nS, A)
        if m > 2 * rho:
            assert real == [pistar], (U, delta, real)
            n_checked += 1
        else:
            n_without_margin += 1
            if real != [pistar]:
                n_viol_without_margin += 1
    print(f"  margin satisfied: {n_checked} instances, chosen = π* in all;  margin NOT satisfied: {n_without_margin}, of which chosen ≠ π* (or tie): {n_viol_without_margin}")
    assert n_checked > 300

    # Reading C2: belief over the CHOSEN policy is (1-δ)δ_{π*} + δP_o, enactment adds independent noise at rate ν.
    # The noise factors out: the conditional on the chosen action is E_μ[Ũ_ν | π'(s)=a] with Ũ_ν the noise-smoothed utility.
    print("\nreading C2 (belief on the CHOSEN policy, independent enactment noise ν): counterexample (i) with U replaced by Ũ_ν")
    nS = 3
    U = {pi: F(0) for pi in policies(nS, A)}
    U[('a', 'a', 'a')] = F(1)
    U[('b', 'b', 'b')] = F(99, 100)
    Po = {('b', 'b', 'b'): F(1, 2), ('a', 'a', 'b'): F(1, 2)}
    delta = F(1, 10)
    for nu in (F(0), F(1, 1000), F(1, 100), F(1, 20)):
        Ut = {}
        for pi in policies(nS, A):
            Ut[pi] = sum(w * U[q] for q, w in corruption_belief(pi, nu, nS, A).items()) if nu > 0 else U[pi]
        mu = mixture(delta, pistar, Po)
        real, maxes, sets = realized_policies(Ut, mu, nS, A)
        print(f"  ν={nu}: chosen = {[pstr(r) for r in real]}, Ũ(chosen) = {[float(Ut[r]) for r in real]}, Ũ(π*) = {float(Ut[pistar]):.5f}")
        if nu <= F(1, 100):
            assert real == [('b', 'b', 'a')]
    print("  ⇒ the counterexample survives small enactment noise (strict inequalities are open conditions).")
    print("  (vi) PASSED\n")


# ----------------------------------------------------------------------------------------------

if __name__ == '__main__':
    section_i()
    r2 = section_ii()
    r3 = section_iii()
    r4 = section_iv()
    section_v()
    section_vi()
    print("ALL ASSERTIONS PASSED")
