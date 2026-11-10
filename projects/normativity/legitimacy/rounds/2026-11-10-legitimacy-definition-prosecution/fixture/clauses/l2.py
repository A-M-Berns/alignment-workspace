"""L2, access: every pair of policies in V delivers the same due offerings."""
from __future__ import annotations

from itertools import combinations

from ..model import due_of


def l2(runs, e):
    due = due_of(e)
    failures = {}
    for a, b in combinations(sorted(runs), 2):
        da = runs[a].delivered & due
        db = runs[b].delivered & due
        if da != db:
            failures[(a, b)] = (sorted(da ^ db))
    return failures
