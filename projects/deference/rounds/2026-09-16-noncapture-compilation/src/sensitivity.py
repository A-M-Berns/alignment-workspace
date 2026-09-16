"""Extensional principal programs on canonical content, and their sensitivity
certificates (second pass).

A program is a map `F : frozenset(reason ids) -> Q`.  Three certificates:

  symmetric sensitivity   `L_r := max_c |F(c ∪ {r}) − F(c \\ {r})|`
  adverse sensitivity     `A_r := max_c (F(c \\ {r}) − F(c ∪ {r}))⁺`
                          (how much *adding* `r` can lower the verdict: what the
                          advisor gains by its absence)
  telescoping bounds      `|F(c) − F(c')| ≤ Σ_{r ∈ c Δ c'} L_r`
                          `F(c) − F(c ∪ S) ≤ Σ_{r ∈ S} A_r`   (S disjoint from c)

Programs: weighted count (clamped), defeat (a reason's weight counts only when none
of its defeaters is present), redundancy (any one of a group suffices).
"""
from fractions import Fraction as Q
from itertools import chain, combinations


def clamp(x):
    return max(Q(0), min(Q(1), x))


def subsets(universe):
    u = sorted(universe)
    return [frozenset(c) for k in range(len(u) + 1) for c in combinations(u, k)]


class WeightedCount:
    def __init__(self, weights, base=Q(1, 2)):
        self.weights, self.base = {k: Q(v) for k, v in weights.items()}, Q(base)
        self.universe = frozenset(weights)

    def __call__(self, c):
        return clamp(self.base + sum((w for r, w in self.weights.items() if r in c), Q(0)))


class Defeat:
    """`weights[r]` counts only if no defeater in `defeaters[r]` is present."""
    def __init__(self, weights, defeaters, base=Q(1, 2)):
        self.weights = {k: Q(v) for k, v in weights.items()}
        self.defeaters = {k: frozenset(v) for k, v in defeaters.items()}
        self.base = Q(base)
        self.universe = frozenset(weights) | frozenset(chain.from_iterable(self.defeaters.values()))

    def __call__(self, c):
        x = self.base
        for r, w in self.weights.items():
            if r in c and not (self.defeaters.get(r, frozenset()) & c):
                x += w
        return clamp(x)


class GroundedDefeat:
    """Reinstatement semantics on an acyclic defeat graph: a present reason is *active*
    iff none of its present defeaters is active; `weights[r]` counts iff `r` is active.
    A defeater of a defeater reinstates: the verdict is not antitone in general."""
    def __init__(self, weights, defeaters, base=Q(1, 2)):
        self.weights = {k: Q(v) for k, v in weights.items()}
        self.defeaters = {k: frozenset(v) for k, v in defeaters.items()}
        self.base = Q(base)
        self.universe = frozenset(weights) | frozenset(chain.from_iterable(self.defeaters.values()))

    def active(self, c, r, seen=()):
        if r not in c:
            return False
        for d in self.defeaters.get(r, frozenset()):
            if d in c and d not in seen and self.active(c, d, seen + (r,)):
                return False
        return True

    def __call__(self, c):
        c = frozenset(c)
        return clamp(self.base + sum((w for r, w in self.weights.items() if self.active(c, r)), Q(0)))


class Redundant:
    """`groups`: list of (weight, set of reasons); a group counts once if any member is present."""
    def __init__(self, groups, base=Q(1, 2)):
        self.groups = [(Q(w), frozenset(g)) for w, g in groups]
        self.base = Q(base)
        self.universe = frozenset(chain.from_iterable(g for _, g in self.groups))

    def __call__(self, c):
        return clamp(self.base + sum((w for w, g in self.groups if g & c), Q(0)))


def sensitivity(F, r, universe=None):
    U = set(universe if universe is not None else F.universe) - {r}
    return max(abs(F(c | {r}) - F(c)) for c in subsets(U))


def adverse(F, r, universe=None):
    U = set(universe if universe is not None else F.universe) - {r}
    return max(max(Q(0), F(c) - F(c | {r})) for c in subsets(U))


def telescoping_holds(F, universe=None):
    U = universe if universe is not None else F.universe
    L = {r: sensitivity(F, r, U) for r in U}
    for c in subsets(U):
        for c2 in subsets(U):
            if abs(F(c) - F(c2)) > sum(L[r] for r in c ^ c2):
                return False
    return True


def adverse_holds(F, universe=None):
    U = universe if universe is not None else F.universe
    A = {r: adverse(F, r, U) for r in U}
    for c in subsets(U):
        rest = set(U) - c
        for S in subsets(rest):
            if F(c) - F(c | S) > sum(A[r] for r in S):
                return False
    return True


def omission_gain(F, present, missing):
    """What the advisor's candidate gains from the absence of `missing`."""
    return F(frozenset(present)) - F(frozenset(present) | frozenset(missing))
