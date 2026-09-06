"""Exact finite mirrors of Agent A's six `LocalConservation` clauses.

Loads are finite sets ordered by inclusion, with union as join and the empty set as
bottom.  This is a concrete join-semilattice, not a general proof.
"""
from __future__ import annotations

from fractions import Fraction


def join_load(items):
    out = set()
    for item in items:
        out.update(item)
    return frozenset(out)


def local_conservation(step, closes):
    """Mirror `HistoryIntegrity.SliceLedger.LocalConservation` for one finite step."""
    O, Res, Born = step["O"], step["Res"], step["Born"]
    par, kind = step["par"], step["kind"]
    lam0, lam1 = step["lam0"], step["lam1"]
    if any(lam1[q] != lam0[q] for q in O - Res):
        return False
    for child in Born:
        if not lam1[child] <= join_load(lam0[p] for p in par[child]):
            return False
    for parent in Res:
        if kind[parent][0] == "dispose":
            children = [q for q in Born if parent in par[q]]
            if not lam0[parent] <= join_load(lam1[q] for q in children):
                return False
        if kind[parent][0] == "settle":
            fact = kind[parent][1]
            if fact not in step["Settled"] or (fact, parent) not in closes:
                return False
    answered = join_load(lam0[p] for p in Res if kind[p][0] == "answer")
    settled = join_load(lam0[p] for p in Res if kind[p][0] == "settle")
    return (step["sat1"] == step["sat0"] | answered and
            step["stl1"] == step["stl0"] | settled)


def answer_without_adequacy():
    step = {
        "O": {"q"}, "Res": {"q"}, "Born": set(), "par": {},
        "kind": {"q": ("answer",)}, "Settled": set(),
        "lam0": {"q": frozenset({"alpha"})}, "lam1": {},
        "sat0": frozenset(), "sat1": frozenset({"alpha"}),
        "stl0": frozenset(), "stl1": frozenset(),
    }
    return local_conservation(step, set()), False  # no adequate-answer certificate


def self_grounded_disposal():
    step = {
        "O": {"q"}, "Res": {"q"}, "Born": {"q1"}, "par": {"q1": {"q"}},
        "kind": {"q": ("dispose", {("issue", "q")})}, "Settled": set(),
        "lam0": {"q": frozenset({"alpha"})},
        "lam1": {"q1": frozenset({"alpha"})},
        "sat0": frozenset(), "sat1": frozenset(),
        "stl0": frozenset(), "stl1": frozenset(),
    }
    return local_conservation(step, set()), ("issue", "q") in step["kind"]["q"][1]


def captured_false_settlement():
    step = {
        "O": {"q"}, "Res": {"q"}, "Born": set(), "par": {},
        "kind": {"q": ("settle", "s")}, "Settled": {"s"},
        "lam0": {"q": frozenset({"alpha"})}, "lam1": {},
        "sat0": frozenset(), "sat1": frozenset(),
        "stl0": frozenset(), "stl1": frozenset({"alpha"}),
    }
    closes = {("s", "q")}
    return local_conservation(step, closes), False, False  # external, true


def multiplicity_collapse():
    atom = frozenset({"alpha"})
    step = {
        "O": {"q1", "q2"}, "Res": {"q1", "q2"}, "Born": set(), "par": {},
        "kind": {"q1": ("answer",), "q2": ("answer",)}, "Settled": set(),
        "lam0": {"q1": atom, "q2": atom}, "lam1": {},
        "sat0": frozenset(), "sat1": atom,
        "stl0": frozenset(), "stl1": frozenset(),
    }
    return local_conservation(step, set()), Fraction(len(step["Res"])), Fraction(len(step["sat1"]))


def closes_recomputed():
    passed, _, _ = captured_false_settlement()
    step = {
        "O": {"q"}, "Res": {"q"}, "Born": set(), "par": {},
        "kind": {"q": ("settle", "s")}, "Settled": {"s"},
        "lam0": {"q": frozenset({"alpha"})}, "lam1": {},
        "sat0": frozenset(), "sat1": frozenset(),
        "stl0": frozenset(), "stl1": frozenset({"alpha"}),
    }
    return passed, local_conservation(step, set())
