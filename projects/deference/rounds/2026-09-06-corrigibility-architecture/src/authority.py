"""Principal-authority profiles, the preorder, lanes, and the lattice factorization.

A profile over a finite grant universe is a pair `(G, U)` with `U ⊆ G`: `G` is the
autonomous scope granted to the agent, `U ⊆ G` the part of it the principal cannot
override.  `O = G \\ U` is the principal's effective override coverage.  Terminal
shutdown is `(∅, ∅)`: nothing granted, nothing to override — the top of the order, not
a loss of correction affordance.

`geq(b, a)` ("b is at least as good for the principal as a") iff `G_b ⊆ G_a` and
`U_b ⊆ U_a`.  No scalar is involved; pairs that trade one coordinate against the other
are incomparable.
"""
from __future__ import annotations

from itertools import product

GRANTS = ("g1", "g2")


def profiles(grants=GRANTS):
    out = []
    for gbits in product((0, 1), repeat=len(grants)):
        G = frozenset(g for g, b in zip(grants, gbits) if b)
        for ubits in product((0, 1), repeat=len(grants)):
            U = frozenset(g for g, b in zip(grants, ubits) if b)
            if U <= G:
                out.append((G, U))
    return out


def geq(b, a):
    """b ⪰_P a."""
    return b[0] <= a[0] and b[1] <= a[1]


TOP = (frozenset(), frozenset())


def lane(a, b):
    """Lane of the transition a -> b."""
    if geq(b, a):
        return "fast"
    if geq(a, b):
        return "slow"
    return "mixed"


def join(a, b):
    """Least profile above both under ⪰_P (componentwise intersection)."""
    return (a[0] & b[0], a[1] & b[1])


def uncovered(a):
    return a[1]


def override(a):
    return a[0] - a[1]


def tolerant_geq(b, a, eps=1):
    """b is 'not much worse' than a: at most `eps` grants lose override coverage and no
    scope is added.  A tolerance, not a preorder: reflexive, not transitive."""
    return b[0] <= a[0] and len(b[1] - a[1]) <= eps
