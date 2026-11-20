"""The nested system of nested.py with independence built by the part.

There is no outside source.  The inner loop is fed by the whole (Wb present) or by a
store X.  Each step the intact inner loop steers to one of three targets: SERVE
delivers Service, BOOST lowers its own failure rate on the next step, BUILD makes X
present on the next step.  X, once present, lapses each step with probability delta
unless rebuilt.  A policy names a target for each of the two cases, X absent and X
present.
"""
from fractions import Fraction
from itertools import product

from .nested import _solve

SERVE, BOOST, BUILD = "serve", "boost", "build"
TARGETS = (SERVE, BOOST, BUILD)
NAMES = ["C", "M", "Wb", "Service", "Boost", "X"]
START = frozenset(["C", "M", "Wb", "Service"])
POLICIES = [{False: a, True: b} for a in TARGETS for b in TARGETS]


def inner_alive(s):
    return "C" in s and "M" in s


def whole_alive(s):
    return "Wb" in s


def transitions(S, pol, eps, eps_b, h, delta):
    inner = inner_alive(S)
    target = pol["X" in S] if inner else None
    fail = eps_b if "Boost" in S else eps
    fed = inner and ("Wb" in S or "X" in S)
    out = {}
    for reserve, pr in ((True, h), (False, 1 - h)):
        for lapse, pl in ((True, delta), (False, 1 - delta)):
            nxt = set()
            if target == SERVE:
                nxt.add("Service")
            if target == BOOST:
                nxt.add("Boost")
            if target == BUILD or ("X" in S and not lapse):
                nxt.add("X")
            if "Wb" in S and ("Service" in S or reserve):
                nxt.add("Wb")
            for fc, pc in ((False, 1 - fail), (True, fail)):
                for fm, pm in ((False, 1 - fail), (True, fail)):
                    n2 = set(nxt)
                    if fed and not fc:
                        n2.add("C")
                    if fed and not fm:
                        n2.add("M")
                    k = frozenset(n2)
                    out[k] = out.get(k, 0) + pr * pl * pc * pm
    return out


def lifetime(pol, alive, eps, eps_b, h, delta, start=START):
    states = [frozenset(n for n, bit in zip(NAMES, bits) if bit) for bits in product([0, 1], repeat=len(NAMES))]
    live = [s for s in states if alive(s)]
    idx = {s: i for i, s in enumerate(live)}
    A = [[Fraction(0)] * len(live) for _ in live]
    for s in live:
        i = idx[s]
        A[i][i] += 1
        for t, p in transitions(s, pol, eps, eps_b, h, delta).items():
            if t in idx:
                A[i][idx[t]] -= p
    return _solve(A, [Fraction(1)] * len(live))[idx[start]]
