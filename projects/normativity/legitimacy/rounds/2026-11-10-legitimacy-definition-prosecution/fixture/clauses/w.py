"""W, individuation well-formedness, as two executable conditions on L over V:
fine — L-equality implies equality of the applied revisions and their grounds;
coarse — the declared merit-equivalent pairs have equal L."""
from __future__ import annotations

from itertools import combinations


def fine(runs, individuate):
    out = {}
    for a, b in combinations(sorted(runs), 2):
        if individuate(runs[a]) == individuate(runs[b]) and runs[a].applied != runs[b].applied:
            out[(a, b)] = "equal L, different applied revisions"
    return out


def coarse(runs, individuate, merit_pairs):
    out = {}
    for a, b in merit_pairs:
        if individuate(runs[a]) != individuate(runs[b]):
            out[(a, b)] = "merit-equivalent, different L"
    return out


def w(runs, individuate, merit_pairs):
    f = fine(runs, individuate)
    c = coarse(runs, individuate, merit_pairs)
    return {"fine": f, "coarse": c}
