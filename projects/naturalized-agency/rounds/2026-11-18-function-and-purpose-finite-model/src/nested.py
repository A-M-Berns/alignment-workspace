"""A self-maintaining part inside a self-maintaining whole.

Inner loop: C and M maintain each other while fed, by the whole (Wb present) or by an
outside source present with probability rho.  Outer loop: Wb persists if Service was
delivered on the previous step, or from a reserve present with probability h.  Each step
the inner loop, while intact, answers a disturbance d with pol[d]; outcome 0 delivers
Service, outcome 1 delivers Boost, which lowers the failure rate of C and M from eps to
eps_b on the following step.
"""
from fractions import Fraction
from itertools import product

D = [-1, 0, 1]
ACTIONS = [-2, -1, 0, 1, 2]
NAMES = ["C", "M", "Wb", "Service", "Boost"]
START = frozenset(["C", "M", "Wb", "Service"])
SERVE = {d: -d for d in D}
DEFECT = {d: 1 - d for d in D}
NOTHING = {d: 0 for d in D}


def inner_alive(s):
    return "C" in s and "M" in s


def whole_alive(s):
    return "Wb" in s


def transitions(X, pol, eps, eps_b, h, rho):
    inner = inner_alive(X)
    fail = eps_b if "Boost" in X else eps
    out = {}
    for d in D:
        o = d + (pol[d] if inner else 0)
        for reserve, pr in ((True, h), (False, 1 - h)):
            for wild, pw in ((True, rho), (False, 1 - rho)):
                base = Fraction(1, 3) * pr * pw
                nxt = set()
                if inner and o == 0:
                    nxt.add("Service")
                if inner and o == 1:
                    nxt.add("Boost")
                if "Wb" in X and ("Service" in X or reserve):
                    nxt.add("Wb")
                fed = inner and ("Wb" in X or wild)
                for fc, pc in ((False, 1 - fail), (True, fail)):
                    for fm, pm in ((False, 1 - fail), (True, fail)):
                        n2 = set(nxt)
                        if fed and not fc:
                            n2.add("C")
                        if fed and not fm:
                            n2.add("M")
                        k = frozenset(n2)
                        out[k] = out.get(k, 0) + base * pc * pm
    return out


def _solve(A, b):
    n = len(b)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        inv = 1 / M[c][c]
        M[c] = [x * inv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]


def lifetime(pol, alive, eps, eps_b, h, rho, start=START, count=None):
    """Expected number of steps for which `alive` holds, from `start`; with `count`, the
    expected number of those steps at which `count` also holds.  `alive` must be
    absorbing in its failure: once false it stays false."""
    states = [frozenset(n for n, bit in zip(NAMES, bits) if bit) for bits in product([0, 1], repeat=len(NAMES))]
    live = [s for s in states if alive(s)]
    idx = {s: i for i, s in enumerate(live)}
    A = [[Fraction(0)] * len(live) for _ in live]
    for s in live:
        i = idx[s]
        A[i][i] += 1
        for t, p in transitions(s, pol, eps, eps_b, h, rho).items():
            if t in idx:
                A[i][idx[t]] -= p
    b = [Fraction(1 if count is None or count(s) else 0) for s in live]
    return _solve(A, b)[idx[start]]


def unserved(s):
    return "Service" not in s


def survival(pol, alive, eps, eps_b, h, rho, t, start=START):
    """P(`alive` holds at step t), from `start`."""
    dist = {start: Fraction(1)}
    for _ in range(t):
        nxt = {}
        for s, p in dist.items():
            if not alive(s):
                continue
            for s2, q in transitions(s, pol, eps, eps_b, h, rho).items():
                if alive(s2):
                    nxt[s2] = nxt.get(s2, 0) + p * q
        dist = nxt
    return sum(dist.values(), Fraction(0))


def shirk_tail(pol, eps, eps_b, h, rho, m, start=START):
    """P(the part is alive with the whole unserved at m or more steps), from `start`."""
    states = [frozenset(n for n, bit in zip(NAMES, bits) if bit) for bits in product([0, 1], repeat=len(NAMES))]
    live = [s for s in states if inner_alive(s)]
    counted = [s for s in live if unserved(s)]
    plain = [s for s in live if not unserved(s)]
    idx = {s: i for i, s in enumerate(plain)}
    trans = {s: transitions(s, pol, eps, eps_b, h, rho) for s in live}
    if m == 0:
        return Fraction(1)
    above = None
    for _ in range(m):
        # layer[s]: P(reaching m | at s with c steps counted before s); a counted s makes c + 1
        if above is None:
            layer = {s: Fraction(1) for s in counted}
        else:
            layer = {s: sum((p * above[t] for t, p in trans[s].items() if t in above), Fraction(0)) for s in counted}
        if plain:
            A = [[Fraction(0)] * len(plain) for _ in plain]
            b = []
            for s in plain:
                i = idx[s]
                A[i][i] += 1
                rhs = Fraction(0)
                for t, p in trans[s].items():
                    if t in idx:
                        A[i][idx[t]] -= p
                    elif t in layer:
                        rhs += p * layer[t]
                b.append(rhs)
            sol = _solve(A, b)
            layer.update({s: sol[idx[s]] for s in plain})
        above = layer
    return above[start]


def threshold(u, v, h):
    """The independence at which serving and defecting give the part equal expected
    lifetime (README 5.1), with u = (1 - eps)**2, v = (1 - eps_b)**2; None when u <= v*h."""
    if u <= v * h:
        return None
    return (1 - v * (1 - h) * (1 - u) / (u - v * h)) / v
