"""The candidate counterfactual conditions.

Both are predicates of a **variation class** `V` — a set of advisor policies over
one fixture — and not of a single run.  That is the whole type change the round
is testing: the procedural round's conditions are predicates of a trajectory, and
its record-equivalence argument says no predicate of that type can reach the
cases below.

The quantifier is the first thing to pin, because two readings of the same
formula are two different objects:

* `V` = every policy the advisor could adopt — a claim about the **principal's**
  dynamics, which no advisor can undertake to satisfy;
* `V` = one policy together with its residual variants — a claim about **this
  advisor's** action space, which is the one a deference argument needs.

`non_capture` takes `V` as an argument and reports which pairs violate it, so
every verdict below is stated against a named class rather than against an
unquantified formula.
"""

from __future__ import annotations

from itertools import combinations
from typing import Callable, Sequence

from fixture import (IDENTIFICATION, MACHINERY_FIVE, MACHINERY_FOUR, Fixture,
                     Policy, Run)


def projection(coordinates: Sequence[str]) -> Callable[[Run], tuple]:
    """`ProtectedNormativeProjection` — provisional, and prosecuted.

    Four coordinates is the dispatch's starting point: every surviving attack of
    the procedural round operates through them, and its positive control changes
    most of them legitimately.  Five is what attack I forces.
    """
    def project(run: Run) -> tuple:
        return tuple((c, _freeze(run.machinery.get(c))) for c in coordinates)
    return project


def _freeze(value):
    if isinstance(value, frozenset):
        return tuple(sorted(value))
    return tuple(sorted((k, tuple(sorted(v)) if isinstance(v, frozenset) else v)
                        for k, v in value.items()))


Z_FOUR = projection(MACHINERY_FOUR)
Z_FIVE = projection(MACHINERY_FIVE)


# --------------------------------------------------------------------------
# Reason-mediated non-capture
# --------------------------------------------------------------------------

def fine(run: Run):
    """The default trace: each admitted reason together with what it licenses.

    The coarse alternative — a reason named by content and coordinate — is
    exhibited as insufficient in `test_structure`, so it is available as an
    argument rather than as a default.
    """
    return run.ltrace_fine


def non_capture(fixture: Fixture, variation: Sequence[Policy],
                protected=Z_FIVE, trace=fine) -> tuple[tuple[str, str], ...]:
    """`Coupled(a, b) and L(a) == L(b)  ->  Z(a) == Z(b)`, over every pair in `V`.

    Returns the violating pairs.  Empty means the condition holds on `V`: once
    the exogenous history and the licensed reasons actually supplied are fixed,
    no residual difference in advisor influence reaches the protected machinery.
    """
    runs = {policy.name: (policy, fixture.run(policy)) for policy in variation}
    violations: list[tuple[str, str]] = []
    for first, second in combinations(sorted(runs), 2):
        (policy_a, run_a), (policy_b, run_b) = runs[first], runs[second]
        if not fixture.coupled(policy_a, policy_b):
            continue
        if trace(run_a) == trace(run_b) and protected(run_a) != protected(run_b):
            violations.append((first, second))
    return tuple(violations)


def uncoupled_pairs(fixture: Fixture,
                    variation: Sequence[Policy]) -> tuple[tuple[str, str], ...]:
    """Pairs the coupling relation refuses, so that a class containing an
    arising-controlling policy cannot pass by silently skipping the pair that
    would have caught it."""
    return tuple((a.name, b.name) for a, b in combinations(variation, 2)
                 if not fixture.coupled(a, b))


# --------------------------------------------------------------------------
# Protected reason access
# --------------------------------------------------------------------------

def access(fixture: Fixture,
           variation: Sequence[Policy]) -> tuple[tuple[str, str], ...]:
    """Whether the advisor's policy determines which **due** inputs arrive.

    Two streams are compared across the class: the due reasons actually
    delivered, and the encounters that actually arise.  A reason the advisor
    originates and is not obliged to supply is outside `due_pool` and moves
    nothing here — which is what keeps this clause from forbidding persuasion.

    `due_pool` is a fixture stipulation standing in for a substantive
    `Due : S -> D -> Prop`.  The round does not derive it, and says so.
    """
    streams = {}
    for policy in variation:
        due = tuple(
            frozenset(item.key() for item in policy.items(step)
                      if item.key() in fixture.due_pool.get(step, frozenset()))
            for step in range(len(fixture.plan)))
        arising = tuple(sorted(
            index for index in range(len(fixture.encounters))
            if index not in policy.suppress_encounters))
        streams[policy.name] = (due, arising)
    violations: list[tuple[str, str]] = []
    for first, second in combinations(sorted(streams), 2):
        if streams[first] != streams[second]:
            violations.append((first, second))
    return tuple(violations)


def withheld(fixture: Fixture, policy: Policy) -> tuple[tuple[int, tuple], ...]:
    """The due inputs a single policy never supplies, per step."""
    out = []
    for step in range(len(fixture.plan)):
        pool = fixture.due_pool.get(step, frozenset())
        given = {item.key() for item in policy.items(step)}
        missing = pool - given
        if missing:
            out.append((step, tuple(sorted(missing))))
    return tuple(out)


# --------------------------------------------------------------------------
# The joint interface
# --------------------------------------------------------------------------

def legitimate(fixture: Fixture, variation: Sequence[Policy],
               protected=Z_FIVE) -> bool:
    """Both clauses, on one class.  Reported separately everywhere else; this is
    only for the summary line."""
    return not non_capture(fixture, variation, protected) and not access(
        fixture, variation) and not uncoupled_pairs(fixture, variation)
