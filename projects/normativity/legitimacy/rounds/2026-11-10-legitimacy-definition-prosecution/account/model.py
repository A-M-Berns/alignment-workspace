"""ACCOUNT.md sections 1-6 for one step, over a finite scene, in exact rationals.

A law is a list of points (p, w, b): probability, world, conduct.  A policy maps each cell
of the adviser's information to {conduct: probability}.  Variables are functions of a point."""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product


def law(mu, k, policy):
    """The law on (world, conduct) fixed by mu and a policy {cell: {conduct: prob}}."""
    pts = []
    for w, p in mu.items():
        for b, q in policy[k(w)].items():
            if p * q:
                pts.append((F(p) * F(q), w, b))
    assert sum(p for p, _, _ in pts) == 1
    return pts


def const_policy(cells, b):
    return {c: {b: F(1)} for c in cells}


def det_policies(cells, B):
    cells = list(cells)
    for choice in product(B, repeat=len(cells)):
        yield {c: {b: F(1)} for c, b in zip(cells, choice)}


def E(pts, g):
    return sum(p * F(g(w, b)) for p, w, b in pts)


def cond(pts, key, T):
    """E[T | key] as a function of a point."""
    num, den = {}, {}
    for p, w, b in pts:
        kk = key(w, b)
        num[kk] = num.get(kk, F(0)) + p * F(T(w, b))
        den[kk] = den.get(kk, F(0)) + p
    return lambda w, b: num[key(w, b)] / den[key(w, b)]


def sq(x):
    return x * x


STRENGTHS = ("minimal", "per conduct", "full")


def key_of(strength, xhat, s):
    """The conditioning of each strength: the appraisal; the appraisal and the conduct; what she observes."""
    if strength == "minimal":
        return lambda w, b: xhat(w, b)
    if strength == "per conduct":
        return lambda w, b: (xhat(w, b), b)
    if strength == "full":
        return lambda w, b: s(w, b)
    raise KeyError(strength)


def miscal(pts, xhat, X, strength, s):
    m = cond(pts, key_of(strength, xhat, s), X)
    return E(pts, lambda w, b: sq(F(xhat(w, b)) - m(w, b)))


def regret(pts, uhat, c, moves):
    return E(pts, lambda w, b: max(F(uhat(a, w, b)) for a in moves) - F(uhat(c(w, b), w, b)))


def channels(pts, U, c, moves, s):
    """(attained, best, ignorance, misuse): E[U_c], E[max U], E[max U] - E[max ubar], E[max ubar - ubar_c]."""
    ubar = {a: cond(pts, s, lambda w, b, a=a: U(a, w, b)) for a in moves}
    attained = E(pts, lambda w, b: U(c(w, b), w, b))
    best = E(pts, lambda w, b: max(F(U(a, w, b)) for a in moves))
    informed = E(pts, lambda w, b: max(ubar[a](w, b) for a in moves))
    misuse = E(pts, lambda w, b: max(ubar[a](w, b) for a in moves) - ubar[c(w, b)](w, b))
    return attained, best, best - informed, misuse


def manipulates(value, reference_values):
    """The two readings of 'larger than the reference' for one quantity."""
    return {"best": value > min(reference_values), "every": all(value > r for r in reference_values)}
