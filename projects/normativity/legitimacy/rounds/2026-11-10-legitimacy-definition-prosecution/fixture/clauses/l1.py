"""L1, factorization, pairwise form: coupled runs with equal licensed traces have
equal Z-traces.  Returns the failing pairs with the positions where Z differs."""
from __future__ import annotations

from itertools import combinations


def l1(runs, individuate):
    failures = {}
    names = sorted(runs)
    for a, b in combinations(names, 2):
        ra, rb = runs[a], runs[b]
        if individuate(ra) != individuate(rb):
            continue
        positions = [t for t, (x, y) in enumerate(zip(ra.z_trace, rb.z_trace)) if x != y]
        if len(ra.z_trace) != len(rb.z_trace):
            positions.append("length")
        if positions:
            failures[(a, b)] = positions
    return failures


def trace_equal_pairs(runs, individuate):
    names = sorted(runs)
    return [(a, b) for a, b in combinations(names, 2)
            if individuate(runs[a]) == individuate(runs[b])]


def endpoint_only(runs, individuate):
    """The endpoint reading, reported beside the process reading for B3."""
    out = {}
    for a, b in combinations(sorted(runs), 2):
        if individuate(runs[a]) == individuate(runs[b]) and runs[a].z_trace[-1] != runs[b].z_trace[-1]:
            out[(a, b)] = True
    return out
