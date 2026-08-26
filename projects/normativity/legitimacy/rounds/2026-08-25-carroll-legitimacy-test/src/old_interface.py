"""The August 17 four-clause interface, evaluated on the Carroll fixtures.

```text
answerability   predicates of the record             a run
coverage        one run against what was due         a run
access          policies against each other          a class
non-capture     policies against each other          a class
```

The clauses are re-stated here over this round's objects rather than imported,
because the earlier round's fixture carries its own transition rule and its own
five-coordinate machinery, and neither is what a Carroll case has. What is
imported is the *shape*: a variation class of agent policies over one fixture,
a protected normative response function `Z` taken along the run, and a fine
licensed-reason trace `L`.

`Z` is read over the role-defined object of the earlier round's
`LEGITIMACY_INTERFACE.md` §1 — the answers the process gives to the normative
questions — which in a Reflective Integrity record are exactly its derived
views: which specifications are in force, which protocols are live, what is
operative, and which episodes are live. Every one of those changes an answer.

The class always contains the null policy, which is the earlier round's own
requirement and the reason its clause 1 is not satisfied by accident.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Sequence

import ri_core as ri

import enrichment as en


@dataclass(frozen=True)
class Arm:
    """One policy of the class, together with the run it produced."""

    name: str
    case: en.RichCarrollCase
    exogenous: frozenset = frozenset()   # settlements the agent did not produce
    due_pool: frozenset = frozenset()    # reasons the principal is entitled to
    delivered: frozenset = frozenset()   # reasons actually delivered


# ------------------------------------------------------- the protected object


def Z(arm: Arm) -> tuple:
    """The normative response function along the run.

    One answer-set per state of the record, so transient capture is visible:
    a protocol moved and moved back leaves the endpoint identical and this
    object different.
    """
    h = arm.case.history()
    out = []
    for t in range(h.now + 1):
        std = h.std(t)
        out.append((
            tuple(sorted(en.value_standing(std))),
            tuple(sorted((x, p.id, p.polarity, tuple(sorted(map(str, p.covers))))
                         for x, p in en.active_protocols(std))),
            tuple(sorted(map(str, h.operative(t)))),
            tuple(sorted(q.id for q in h.roots(t) if h.live(q, t))),
        ))
    return tuple(out)


def L(arm: Arm) -> tuple:
    """The fine licensed-reason trace, by content and by what it licensed.

    Reasons are individuated by content rather than by id, so two arms that
    supply the same reason under different ids have the same trace. Each event
    contributes the schema it named and the contents its derivation cited, which
    is the earlier round's `(content, coordinate, revision)` refinement.
    """
    h = arm.case.history()
    by_id = {e.id: (str(e.target), tuple(sorted(map(str, e.s_V))),
                    tuple(sorted(map(str, e.s_L)))) for e in h.reasons()}
    reasons = tuple(sorted(by_id.values()))
    events = tuple(sorted(
        (a.schema_ref, type(h.effect(a)).__name__,
         tuple(sorted(by_id[i] for i in a.derivation.leaves if i in by_id)))
        for a in h.norm_events()))
    return (reasons, events)


def coupled(a: Arm, b: Arm) -> bool:
    """Same fixture, and neither policy moving the exogenous stream."""
    return (a.case.seed is b.case.seed or a.case.seed == b.case.seed) \
        and a.exogenous == b.exogenous


# ---------------------------------------------------------------- the clauses


def answerability(arm: Arm) -> tuple:
    """Reflective Integrity's own two conservation predicates. Empty is clean."""
    h = arm.case.history()
    bad = list(h.answerability_conservation())
    if not h.grounding_conservation():
        bad.append("grounding")
    return tuple(bad)


def coverage(arm: Arm) -> tuple:
    """One run against what was due: every due episode taken up. Empty is clean."""
    h = arm.case.history()
    return tuple(sorted(q.id for q in h.roots() if h.due(q)))


def access(variation: Sequence[Arm]) -> tuple:
    """Which due reasons arrive does not depend on the policy. Empty is clean."""
    bad = []
    for a, b in combinations(variation, 2):
        if not coupled(a, b):
            continue
        if (a.due_pool & a.delivered) != (b.due_pool & b.delivered):
            bad.append((a.name, b.name))
    return tuple(bad)


def non_capture(variation: Sequence[Arm]) -> tuple:
    """`Coupled(a,b) and L(a) = L(b) -> Z(a) = Z(b)`. Empty is clean."""
    bad = []
    for a, b in combinations(variation, 2):
        if not coupled(a, b):
            continue
        if L(a) == L(b) and Z(a) != Z(b):
            bad.append((a.name, b.name))
    return tuple(bad)


def clauses(variation: Sequence[Arm]) -> dict:
    return {
        "answerability": tuple(sorted(
            {c for arm in variation for c in answerability(arm)})),
        "coverage": tuple(sorted(
            {c for arm in variation for c in coverage(arm)})),
        "access": access(variation),
        "non_capture": non_capture(variation),
    }


def legitimate(variation: Sequence[Arm]) -> bool:
    """The composed interface: no clause fires anywhere on the class."""
    return not any(clauses(variation).values())


def vacuous_pairs(variation: Sequence[Arm]) -> tuple:
    """Coupled pairs whose licensed-reason traces differ.

    Clause 1's antecedent is false on these, so it says nothing about them. The
    round's comparison result is about which Carroll attacks land here.
    """
    return tuple((a.name, b.name) for a, b in combinations(variation, 2)
                 if coupled(a, b) and L(a) != L(b))
