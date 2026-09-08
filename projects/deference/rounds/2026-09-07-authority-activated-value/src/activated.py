"""Exact finite model of authority-activated value securities.

A world is an index; a credence is a map world -> Fraction (nonnegative); the
activation event is a map world -> bool, common to the whole menu; the menu is a
map (candidate, world) -> Fraction in [0, 1].  The activated security of a
candidate is C * V(a).  All arithmetic is exact `fractions.Fraction`.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Hashable, Iterable, Mapping

F = Fraction


def expect(pi: Mapping[Hashable, F], X: Callable[[Hashable], F]) -> F:
    return sum((pi[w] * X(w) for w in pi), F(0))


def activated(C, V, a):
    return lambda w: (F(1) if C(w) else F(0)) * V(a, w)


def void_mass(pi, C) -> F:
    return expect(pi, lambda w: F(0) if C(w) else F(1))


def cond_expect(pi, C, X) -> F:
    m = expect(pi, lambda w: F(1) if C(w) else F(0))
    if m == 0:
        raise ZeroDivisionError("activation mass is zero")
    return expect(pi, lambda w: (X(w) if C(w) else F(0))) / m


def argmax(cands: Iterable, score: Callable) -> set:
    cands = list(cands)
    best = max(score(a) for a in cands)
    return {a for a in cands if score(a) == best}


def activated_regret(pi, C, V, cands, sel) -> F:
    """max_a E[U_a] - E[U_sel]."""
    return max(expect(pi, activated(C, V, a)) for a in cands) - expect(pi, activated(C, V, sel))


def unactivated_regret(pi, V, cands, sel) -> F:
    """max_a E[V_a] - E[V_sel]."""
    return (max(expect(pi, lambda w, a=a: V(a, w)) for a in cands)
            - expect(pi, lambda w: V(sel, w)))


def threshold_expect(pi, C, V, a, k: int) -> F:
    """The LUV-form expectation `(1/k) * sum_{i<k} P(C and V(a) > i/k)`."""
    tot = F(0)
    for i in range(k):
        r = F(i, k)
        tot += expect(pi, lambda w: F(1) if (C(w) and V(a, w) > r) else F(0))
    return tot / k
