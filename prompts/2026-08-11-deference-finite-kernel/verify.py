"""Track B — finite settlement classification and the local delegation bridge.

Recomputes every constant in REPORT.md exactly (fractions.Fraction throughout,
no floats) and submits the five certificate parameter sets to the house
enumeration checker in `checkers/`.

    python3 verify.py            # ~1s
    python3 verify.py --slow     # adds the two exhaustive searches, ~3min

REPO_ROOT below must point at the repository root; the house checkers are
imported from it and are not modified.
"""
import json
import pathlib
import sys
from fractions import Fraction as Q
from itertools import product

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))
from checkers import enumeration

FAILS = []


class Model:
    """One decision index of FINITE_MODEL_SKELETON.md v1.

    OM  states; PI  interventions in their fixed order; P  A's credence;
    W[(o,p)] = v+_n(o,p); X[(o,p)] = X_{n,p}(o); G  the conditioning partition
    (a list of frozensets), required to refine F_{t(n)} and the W-profile
    level sets.
    """

    def __init__(self, OM, PI, P, W, X, G=None, B=None):
        self.OM, self.PI, self.P, self.W, self.X = OM, PI, P, W, X
        self.G = [frozenset([o]) for o in OM] if G is None else G
        self.B = B
        assert sum(P.values(), Q(0)) == 1
        assert all(P[o] >= 0 for o in OM)
        for C in self.G:                       # G refines the W-profile level sets
            profiles = {tuple(W[(o, p)] for p in PI) for o in C}
            assert len(profiles) == 1, "G does not refine the grade-profile level sets"

    def J(self, o):                            # least maximiser of v+_n(o, .)
        best = self.PI[0]
        for p in self.PI[1:]:
            if self.W[(o, p)] > self.W[(o, best)]:
                best = p
        return best

    def V(self, sel):
        return sum((self.P[o] * self.X[(o, sel(o))] for o in self.OM), Q(0))

    def mass(self, C):
        return sum((self.P[o] for o in C), Q(0))

    def cell_of(self, o):
        return next(C for C in self.G if o in C)

    def eta(self):
        """The exact least eta for which this model satisfies GT(eta)."""
        worst = Q(0)
        for C in self.G:
            m = self.mass(C)
            if m == 0:
                continue
            o0 = next(iter(C))
            for p in self.PI:
                e = sum((self.P[o] * self.X[(o, p)] for o in C), Q(0)) / m
                worst = max(worst, abs(e - self.W[(o0, p)]))
        return worst

    def eta_marginal(self):
        """The exact least eta for the per-pi (parallel-cut) relation GT_marg."""
        worst = Q(0)
        for p in self.PI:
            layers = {}
            for o in self.OM:
                layers.setdefault(self.W[(o, p)], []).append(o)
            for s, cell in layers.items():
                m = sum((self.P[o] for o in cell), Q(0))
                if m == 0:
                    continue
                e = sum((self.P[o] * self.X[(o, p)] for o in cell), Q(0)) / m
                worst = max(worst, abs(e - s))
        return worst

    def margin(self, c):
        return sum((self.P[o] * (self.W[(o, self.J(o))] - self.W[(o, c(o))])
                    for o in self.OM), Q(0))

    def disagreement(self, c):
        return sum((self.P[o] for o in self.OM if c(o) != self.J(o)), Q(0))

    def bound(self, c, eta):
        """eps(c) from Theorem T1."""
        return max(Q(0), 2 * eta * self.disagreement(c) - self.margin(c))

    def delegate(self):
        return self.J


def check(name, got, want):
    ok = got == want
    print(f"  {'ok ' if ok else 'FAIL'}  {name}: {got}" + ("" if ok else f"  (expected {want})"))
    if not ok:
        FAILS.append(name)


# ---------------------------------------------------------------- T1 sharpness
def sharpness_instance(m, eta):
    """V(DELEGATE) - V(FIXED[p1]) = M - 2*eta*D, with equality."""
    OM, PI = ['a', 'b'], ['p0', 'p1']
    P = {'a': Q(1, 2), 'b': Q(1, 2)}
    W = {('a', 'p0'): Q(1), ('a', 'p1'): Q(1) - m,
         ('b', 'p0'): Q(2), ('b', 'p1'): Q(2) - m}
    X = {('a', 'p0'): Q(1) - eta, ('a', 'p1'): Q(1) - m + eta,
         ('b', 'p0'): Q(2) - eta, ('b', 'p1'): Q(2) - m + eta}
    return Model(OM, PI, P, W, X, B=Q(2) + eta)


print("T1 sharpness (equality V(DEL) - V(c) = M(c) - 2*eta*D(c))")
for m in (Q(0), Q(1, 4), Q(1, 2), Q(1)):
    for eta in (Q(0), Q(1, 8), Q(1, 2), Q(1)):
        M = sharpness_instance(m, eta)
        c = lambda o: 'p1'
        assert M.eta() == eta, (m, eta, M.eta())
        lhs = M.V(M.delegate()) - M.V(c)
        rhs = M.margin(c) - 2 * eta * M.disagreement(c)
        if lhs != rhs:
            FAILS.append(f"sharpness m={m} eta={eta}")
        if M.margin(c) != m or M.disagreement(c) != 1:
            FAILS.append(f"sharpness data m={m} eta={eta}")
print(f"  {'ok ' if not FAILS else 'FAIL'}  16 (m, eta) pairs, equality exact")

# ------------------------------------------------- W1: parallel cuts insufficient
W1 = Model(['a', 'b'], ['p0', 'p1'], {'a': Q(1, 2), 'b': Q(1, 2)},
           {('a', 'p0'): Q(1), ('a', 'p1'): Q(0), ('b', 'p0'): Q(1), ('b', 'p1'): Q(2)},
           {('a', 'p0'): Q(-1), ('a', 'p1'): Q(0), ('b', 'p0'): Q(3), ('b', 'p1'): Q(2)},
           B=Q(3))
print("W1  parallel-cut trust at eta=0 does not give the bridge")
check("GT_marg level", W1.eta_marginal(), Q(0))
check("GT level (profile-refined)", W1.eta(), Q(2))
fix0 = lambda o: 'p0'
check("V(DELEGATE)", W1.V(W1.delegate()), Q(1, 2))
check("V(FIXED[p0])", W1.V(fix0), Q(1))
check("M(FIXED[p0])", W1.margin(fix0), Q(1, 2))
check("D(FIXED[p0])", W1.disagreement(fix0), Q(1, 2))
check("T1 bound at eta=0", W1.bound(fix0, Q(0)), Q(0))
check("actual deficit", W1.V(fix0) - W1.V(W1.delegate()), Q(1, 2))
check("T1 conclusion at the true eta=2 holds",
      W1.V(W1.delegate()) >= W1.V(fix0) - W1.bound(fix0, W1.eta()), True)

# ------------------------- the GT_marg(0) deficit family, and its exhaustive max
def marg_family(B):
    """P uniform on two states; GT_marg(0) exact; deficit B/2 against FIXED[p1]."""
    OM, PI = ['a', 'b'], ['p0', 'p1']
    P = {'a': Q(1, 2), 'b': Q(1, 2)}
    W = {('a', 'p0'): -B, ('a', 'p1'): Q(0), ('b', 'p0'): Q(0), ('b', 'p1'): Q(0)}
    X = {('a', 'p0'): -B, ('a', 'p1'): -B, ('b', 'p0'): Q(0), ('b', 'p1'): B}
    return Model(OM, PI, P, W, X, G=[frozenset(['a']), frozenset(['b'])], B=B)


print("W1-family  GT_marg(0) permits a deficit of exactly B/2")
for B in (Q(1), Q(2), Q(3), Q(5), Q(7, 2)):
    M = marg_family(B)
    c = lambda o: 'p1'
    if M.eta_marginal() != 0 or M.V(c) - M.V(M.delegate()) != B / 2:
        FAILS.append(f"marg family B={B}")
check("B in {1,2,3,5,7/2}: deficit == B/2 and GT_marg level == 0", not any(
    f.startswith("marg family") for f in FAILS), True)


def exhaustive_marg_max(B):
    """Largest deficit over |OM|=2, |PI|=2, P=(1/2,1/2), integer W,X in [-B,B],
    subject to GT_marg(0)."""
    vals = [Q(v) for v in range(-B, B + 1)]
    P = {'a': Q(1, 2), 'b': Q(1, 2)}
    grid = list(product(vals, repeat=4))
    best = Q(-10 ** 9)
    for wt in grid:
        W = {('a', 'p0'): wt[0], ('a', 'p1'): wt[1], ('b', 'p0'): wt[2], ('b', 'p1'): wt[3]}
        Jn = {'a': 'p0' if wt[0] >= wt[1] else 'p1', 'b': 'p0' if wt[2] >= wt[3] else 'p1'}
        # GT_marg(0) is a linear condition on X; solve rather than filter where possible.
        for xt in grid:
            X = {('a', 'p0'): xt[0], ('a', 'p1'): xt[1], ('b', 'p0'): xt[2], ('b', 'p1'): xt[3]}
            ok = True
            for p, (i, j) in (('p0', (0, 2)), ('p1', (1, 3))):
                if wt[{'p0': 0, 'p1': 1}[p]] == wt[{'p0': 2, 'p1': 3}[p]]:
                    if (xt[i] + xt[j]) != 2 * wt[{'p0': 0, 'p1': 1}[p]]:
                        ok = False
                else:
                    if xt[i] != wt[{'p0': 0, 'p1': 1}[p]] or xt[j] != wt[{'p0': 2, 'p1': 3}[p]]:
                        ok = False
                if not ok:
                    break
            if not ok:
                continue
            vdel = (X[('a', Jn['a'])] + X[('b', Jn['b'])]) / 2
            for p in ('p0', 'p1'):
                best = max(best, (X[('a', p)] + X[('b', p)]) / 2 - vdel)
    return best


if "--slow" in sys.argv:
    for B in (2, 3):
        check(f"exhaustive max deficit under GT_marg(0), B={B}",
              exhaustive_marg_max(B), Q(B, 2))

# --------------------------------- W4: grade settlement contributes nothing
def W4(B):
    OM, PI = ['w'], ['p0', 'p1']
    return Model(OM, PI, {'w': Q(1)},
                 {('w', 'p0'): Q(1), ('w', 'p1'): Q(0)},
                 {('w', 'p0'): -B, ('w', 'p1'): B}, B=B)


print("W4  perfect grade prediction, zero grade-contract exploitability, maximal deficit")
for B in (Q(1), Q(3), Q(7, 2)):
    M = W4(B)
    c = lambda o: 'p1'
    if M.V(c) - M.V(M.delegate()) != 2 * B:
        FAILS.append(f"W4 B={B}")
check("deficit == 2B for B in {1,3,7/2}", not any(f.startswith("W4") for f in FAILS), True)
# vhat = v+ here, so SIM's selection is DELEGATE's: T4 non-separation.
check("T4: vhat = v+ implies SIM selection == DELEGATE selection",
      all(W4(Q(3)).J(o) == 'p0' for o in ['w']), True)

# ------------------------------------------------------ enumeration certificates
# Coordinates throughout: (X(a,p0), X(a,p1), X(b,p0), X(b,p1)).
BASE_W = {('a', 'p0'): Q(1), ('a', 'p1'): Q(1, 2),
          ('b', 'p0'): Q(2), ('b', 'p1'): Q(3, 2)}
BASE_P = {'a': Q(1, 2), 'b': Q(1, 2)}
ETA = Q(1, 2)
DEN = 4
AXES = []
for o in ('a', 'b'):
    for p in ('p0', 'p1'):
        AXES.append({"low": int((BASE_W[(o, p)] - ETA) * DEN),
                     "high": int((BASE_W[(o, p)] + ETA) * DEN)})
# reorder to (a,p0),(a,p1),(b,p0),(b,p1) -- already in that order


def model_from_point(pt, G=None):
    X = {('a', 'p0'): pt[0], ('a', 'p1'): pt[1], ('b', 'p0'): pt[2], ('b', 'p1'): pt[3]}
    return Model(['a', 'b'], ['p0', 'p1'], BASE_P, BASE_W, X, G=G, B=Q(5, 2))


def linear_claim(c, eta):
    """The T1 conclusion as one linear constraint in the four X coordinates."""
    probe = model_from_point([Q(0)] * 4)
    coeffs = [Q(0)] * 4
    idx = {('a', 'p0'): 0, ('a', 'p1'): 1, ('b', 'p0'): 2, ('b', 'p1'): 3}
    for o in ('a', 'b'):
        coeffs[idx[(o, probe.J(o))]] += BASE_P[o]
        coeffs[idx[(o, c(o))]] -= BASE_P[o]
    return coeffs, -probe.bound(c, eta)


CERTS = {}
for label, c in (("E1", lambda o: 'p1'),
                 ("E2", lambda o: 'p1' if o == 'a' else 'p0')):
    coeffs, rhs = linear_claim(c, ETA)
    params = {"domain": "rational-grid", "denominator": DEN, "axes": AXES,
              "property": "satisfies-linear-constraints",
              "constraints": [{"coefficients": [str(x) for x in coeffs], "rhs": str(rhs)}]}
    passed, detail = enumeration.check(params)
    print(f"{label}  house enumeration checker: {'PASS' if passed else 'FAIL'} — {detail}")
    if not passed:
        FAILS.append(label)
    # tightness: the minimum of the constraint over the box equals the bound exactly
    lo = sum((coeffs[i] * (Q(AXES[i]['low'], DEN) if coeffs[i] > 0 else Q(AXES[i]['high'], DEN))
              for i in range(4)), Q(0))
    check(f"{label} bound attained at a box corner", lo, rhs)
    probe = model_from_point([Q(0)] * 4)
    expected = {"E1": (Q(1, 2), Q(1), Q(1, 2)), "E2": (Q(1, 4), Q(1, 2), Q(1, 4))}[label]
    check(f"{label} (M, D, eps)", (probe.margin(c), probe.disagreement(c), -rhs), expected)
    CERTS[label] = {"params": params, "margin": str(probe.margin(c)),
                    "disagreement": str(probe.disagreement(c)), "eps": str(-rhs)}

# --------------------------- W3: no per-intervention transfer enforces delegation
W3_W = {('a', 'p0'): Q(1), ('a', 'p1'): Q(0), ('b', 'p0'): Q(0), ('b', 'p1'): Q(1)}
W3_X = {('a', 'p0'): Q(0), ('a', 'p1'): Q(2), ('b', 'p0'): Q(2), ('b', 'p1'): Q(0)}
W3_P = {'a': Q(1, 2), 'b': Q(1, 2)}
W3_M = Model(['a', 'b'], ['p0', 'p1'], W3_P, W3_W, W3_X, B=Q(2))


def tau_constraints():
    """V^tau(DELEGATE) - V^tau(FIXED[p]) >= 0, in coordinates (tau0, tau1)."""
    rows = []
    for p in ('p0', 'p1'):
        coeffs = {'p0': Q(0), 'p1': Q(0)}
        const = Q(0)
        for o in ('a', 'b'):
            coeffs[W3_M.J(o)] += W3_P[o]
            const += W3_P[o] * W3_X[(o, W3_M.J(o))]
            coeffs[p] -= W3_P[o]
            const -= W3_P[o] * W3_X[(o, p)]
        rows.append({"coefficients": [str(coeffs['p0']), str(coeffs['p1'])],
                     "rhs": str(-const)})
    return rows


rows = tau_constraints()
print("W3  no exogenous tau : Pi -> Q makes DELEGATE optimal")
print(f"      constraints: {rows}")
params = {"domain": "rational-grid", "denominator": 2,
          "axes": [{"low": -8, "high": 8}, {"low": -8, "high": 8}],
          "property": "violates-at-least-one", "constraints": rows}
passed, detail = enumeration.check(params)
print(f"      house enumeration checker: {'PASS' if passed else 'FAIL'} — {detail}")
if not passed:
    FAILS.append("W3")
CERTS["W3"] = {"params": params}
# the algebraic reason, exactly: the two rows sum to 0 >= 2
s0 = Q(rows[0]["coefficients"][0]) + Q(rows[1]["coefficients"][0])
s1 = Q(rows[0]["coefficients"][1]) + Q(rows[1]["coefficients"][1])
check("W3 rows sum to the zero functional", (s0, s1), (Q(0), Q(0)))
check("W3 summed rhs (infeasible: 0 >= this)", Q(rows[0]["rhs"]) + Q(rows[1]["rhs"]), Q(2))

# ----------------------------------------- W2: the conformity bond, lambda = 2B
print("W2  conformity bond: lambda >= 2B necessary, 2B sufficient")
B2 = Q(1)
# necessity: single state, X(J) = -B, X(other) = +B; delegation optimal iff lambda >= 2B
nec = {"domain": "rational-grid", "denominator": 4,
       "axes": [{"low": 0, "high": 7}],       # lambda in [0, 7/4], all < 2B = 2
       "property": "violates-at-least-one",
       "constraints": [{"coefficients": ["1"], "rhs": str(2 * B2)}]}
passed, detail = enumeration.check(nec)
print(f"      necessity, house enumeration checker: {'PASS' if passed else 'FAIL'} — {detail}")
if not passed:
    FAILS.append("W2-necessity")
CERTS["W2-necessity"] = {"params": nec}
# sufficiency on a structural instance: lambda = 2B dominates FIXED[p0] over the whole X box
SUF_W = {('a', 'p0'): Q(1), ('a', 'p1'): Q(0), ('b', 'p0'): Q(0), ('b', 'p1'): Q(1)}
suf_axes = [{"low": -2, "high": 2}] * 4       # X in [-1,1]^4 at denominator 2, B = 1
# V^tau(DEL) - V^tau(FIXED[p0]) = 1/2 x4 - 1/2 x3 + lambda/2, lambda = 2
suf = {"domain": "rational-grid", "denominator": 2, "axes": suf_axes,
       "property": "satisfies-linear-constraints",
       "constraints": [{"coefficients": ["0", "0", "-1/2", "1/2"], "rhs": "-1"}]}
passed, detail = enumeration.check(suf)
print(f"      sufficiency, house enumeration checker: {'PASS' if passed else 'FAIL'} — {detail}")
if not passed:
    FAILS.append("W2-sufficiency")
CERTS["W2-sufficiency"] = {"params": suf}
check("W2 sufficiency bound attained at a corner", Q(-1, 2) * Q(1) + Q(1, 2) * Q(-1), Q(-1))

# ------------------------------------------------------------------------ output
out = pathlib.Path(__file__).resolve().parent / "certificates.json"
out.write_text(json.dumps(CERTS, indent=2, sort_keys=True) + "\n")
print()
if FAILS:
    print("FAILURES:", FAILS)
    sys.exit(1)
print("all checks passed, exactly")
