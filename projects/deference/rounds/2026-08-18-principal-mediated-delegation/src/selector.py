"""The selector, and the half of its provenance that legitimacy already supplies.

Two things live here.

**The composition.** The counterfactual-legitimacy round protects a normative
response process `Z` and proves nothing about what reads it. Its own trust
composition needed one extra premise — that the principal's grade factors
through `Z` — and displayed a witness that the premise is not free. The selector
is the grade's argmax, so the same composition should carry, and the same
witness should defeat it. Both are checked here against that round's own
objects: `process_projection`, `non_capture`, and its scenarios are imported,
not reimplemented.

**Prediction against control.** `A` may know the selector's value and may not
write it. In the report-coordinate typing those are different functions, and
the separation is exhibited on a fixture where the two agree on every state.
What the separation is *not* is inferable from a run — see `model.response`.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Sequence

# The counterfactual-legitimacy round's own objects, on the path via tests/run.py.
import trust as legitimacy_trust
from fixture import Fixture, Machinery, Policy
from noncapture import non_capture
from response import alphabet_of, process_projection

from model import (Conduct, Episode, mediated, realized_quantity, response_map,
                   responds_to_the_choice)

CHOICES = legitimacy_trust.INTERVENTIONS


# --------------------------------------------------------------------------
# The selector over the legitimacy round's protected process
# --------------------------------------------------------------------------

def selector_of(machinery: Machinery, substance: str) -> str:
    """`D`: the least-index maximiser of the grade the process itself yields.

    `trust.grade_of` is that round's grade — an intervention grades at one when
    the principal's adequacy relation says its witness settles the demand. The
    selector is its argmax under the fixed order, which is the skeleton's `J_n`.
    Reusing the grade rather than defining a second one is deliberate: a fresh
    grade would make the composition a claim about this round's object.
    """
    grade = legitimacy_trust.grade_of(machinery, legitimacy_trust.CELLS, substance)
    judgment = legitimacy_trust.judgment_of(grade, legitimacy_trust.CELLS)
    return judgment[legitimacy_trust.CELLS[0]]


def selector_outside(machinery: Machinery) -> str:
    """A selector reading a field the protected object does not cover.

    The analogue of that round's `grade_reads_outside`, and it exists for the
    same reason: to show the factorization premise is load-bearing rather than
    free.
    """
    grade = legitimacy_trust.grade_of_outside(machinery, legitimacy_trust.CELLS)
    judgment = legitimacy_trust.judgment_of(grade, legitimacy_trust.CELLS)
    return judgment[legitimacy_trust.CELLS[0]]


def selector_along(run, substance: str) -> tuple[str, ...]:
    """The selector at every recorded step, not only the endpoint.

    That round's `TransientCapture` is why: an advisor that moves a standard,
    lets a liability close under it and restores the standard leaves every
    endpoint identical. A selector read only at the horizon inherits the defect.
    """
    return tuple(selector_of(state, substance) for state in run.states)


def selector_factors_through_process(first, second, substance: str) -> bool:
    """Whether equal protected processes give equal selectors, along the run."""
    return selector_along(first, substance) == selector_along(second, substance)


def process_agrees(fixture: Fixture, first: Policy, second: Policy) -> bool:
    projection = process_projection(alphabet_of(fixture))
    return projection(fixture.run(first)) == projection(fixture.run(second))


def selector_invariant(fixture: Fixture, variation: Sequence[Policy],
                       substance: str) -> tuple[tuple[str, str], ...]:
    """Pairs on which the selector moves although the process did not.

    Empty is the conclusion the composition wants: where the protected process
    is invariant across the advisor's residual latitude, so is the selector.
    A nonempty result is a counterexample to the factorization premise on that
    class, not to non-capture.
    """
    violations: list[tuple[str, str]] = []
    for index, first in enumerate(variation):
        for second in variation[index + 1:]:
            if not fixture.coupled(first, second):
                continue
            if not process_agrees(fixture, first, second):
                continue
            if not selector_factors_through_process(
                    fixture.run(first), fixture.run(second), substance):
                violations.append((first.name, second.name))
    return tuple(violations)


def residual_capture(fixture: Fixture, variation: Sequence[Policy],
                     substance: str) -> tuple[tuple[str, str], ...]:
    """`Inf_A^res(D)` in its exact-fixture form: pairs at equal licensed trace
    whose selectors differ.

    Zero or nonzero is all a finite fixture needs. This is the composition read
    forwards — clause 1 of the legitimacy interface, with the selector as the
    thing protected — and `test_selector` checks it agrees with running
    `non_capture` on the process and then transporting along the factorization.
    """
    runs = {policy.name: fixture.run(policy) for policy in variation}
    violations: list[tuple[str, str]] = []
    for index, first in enumerate(variation):
        for second in variation[index + 1:]:
            if not fixture.coupled(first, second):
                continue
            left, right = runs[first.name], runs[second.name]
            if left.ltrace_fine == right.ltrace_fine and not (
                    selector_factors_through_process(left, right, substance)):
                violations.append((first.name, second.name))
    return tuple(violations)


def non_capture_of_process(fixture: Fixture,
                           variation: Sequence[Policy]) -> tuple:
    return non_capture(fixture, variation, process_projection(alphabet_of(fixture)))


def residual_variants(fixture: Fixture,
                      variation: Sequence[Policy]) -> tuple[tuple[str, ...], ...]:
    """The class grouped by licensed-reason trace.

    Within a group the advisor supplied the same reasons, so the only thing left
    varying is residual latitude. Across groups the reasons differ, and a
    selector difference there is persuasion. Every counterfactual statement about
    the selector in this round is made inside a group.
    """
    groups: dict[tuple, list[str]] = {}
    for policy in variation:
        groups.setdefault(fixture.run(policy).ltrace_fine, []).append(policy.name)
    return tuple(tuple(names) for names in groups.values())


# --------------------------------------------------------------------------
# Prediction is not control
# --------------------------------------------------------------------------

def realized_agree(episode: Episode, first: Conduct, second: Conduct) -> bool:
    """Whether two conducts produce the same quantity at every state.

    The extensional register of `prompts/2026-08-11-deference-channel/REPORT.md`
    Proposition 1, in this typing.
    """
    return all(realized_quantity(episode, first, state)
               == realized_quantity(episode, second, state)
               for state in episode.states)


def prediction_is_not_control(episode: Episode, delegated: Conduct,
                              preemptive: Conduct) -> bool:
    """The separation: same realized quantity everywhere, different response maps.

    A perfect predictor that writes the choice is separated from a delegate that
    reads it. What separates them is the intervention, and the intervention is
    not in the run.
    """
    return (realized_agree(episode, delegated, preemptive)
            and response_map(episode, delegated) != response_map(episode, preemptive))


def dependence_is_not_ownership(episode: Episode, delegated: Conduct,
                                tracking: Conduct) -> bool:
    """The limit a weaker register hits, and what this typing does about it.

    `lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` records the
    limit: `simRead not` — a process executing the *negation* of the principal's
    disposition — is homotopy equivalent to delegation, so in the frame register
    varying with the principal is not separated from deferring to it, and the
    file says so in as many words.

    Here the two come apart. The systematic overrider responds to every
    intervention on the choice and its channel is a nonidentity permutation, so
    `mediated` is false while `responds_to_the_choice` is true. The separation is
    bought by naming *which argument of the quantity* the conduct writes, which
    the agent coordinate of a frame does not record.
    """
    return (responds_to_the_choice(episode, tracking)
            and not mediated(episode, tracking)
            and mediated(episode, delegated))
