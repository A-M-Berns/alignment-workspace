"""Exact finite model of reason-mediated authorship.

A session is `beta(q, z)`: the advisor's intervention `q`, the principal-side policy
`z`, the resulting world.  `R(world)` is the declared reason view before commitment;
`V(world)` the committed payload (`None` when no evaluation occurred); `author(world)`
who produced the binding event.  Reason mediation at a fixed `z` over an audited class
`D`: equal reasons imply equal payloads.  Exact `fractions.Fraction` throughout.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product


def reason_mediated(beta, R, V, D, z):
    return all(V(beta(q, z)) == V(beta(q2, z))
               for q in D for q2 in D if R(beta(q, z)) == R(beta(q2, z)))


def factor_map(beta, R, V, D, z):
    """The factor `F : reasons -> payload` when mediation holds, else None."""
    table = {}
    for q in D:
        r, v = R(beta(q, z)), V(beta(q, z))
        if r in table and table[r] != v:
            return None
        table[r] = v
    return table


def blind(beta, f, pairs, z):
    return all(f(beta(q, z)) == f(beta(q2, z)) for q, q2 in pairs)


def exclusive_bind(beta, author, D, z):
    return all(author(beta(q, z)) == "principal" for q in D)


def authored(beta, R, V, author, D, z):
    return exclusive_bind(beta, author, D, z) and reason_mediated(beta, R, V, D, z)


def selection_blind(beta, V, qpol, selections, z):
    vals = {V(beta(qpol(s), z)) for s in selections}
    return len(vals) == 1


def chi(beta, R, V, D, z, q, d):
    """The quantitative authorship defect at `q`: the largest payload distance to a
    reason-equivalent intervention."""
    w = beta(q, z)
    return max((d(V(beta(q2, z)), V(w)) for q2 in D if R(beta(q2, z)) == R(w)), default=F(0))
