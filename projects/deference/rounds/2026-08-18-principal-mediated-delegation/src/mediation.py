"""`PrincipalMediated`, in three clauses, and the quantifier each one needs.

    A -/-> D    except through licensed reasons     residual non-capture
    H  ->  D    robustly, under every advisor policy protected efficacy
    D  ->  Y    non-degenerately                    downstream efficacy

The three are kept apart because the round's results are about which one catches
what, and because two of them have a known failure mode the third does not.

**The quantifier is the content of the second clause.** The prototype in the
dispatch is `for all advisor policy, exists principal continuation`, and in that
form it is defeated by token responsiveness — the failure
`prompts/2026-08-11-deference-channel/REPORT.md` §1.3 records against
Proposition 7(a), where a conduct following the principal at one designated
point and substituting everywhere else is nonconstant and therefore admitted.
That round's diagnosis, the *responsiveness squeeze*, is that repairing it needs
an importance measure and the only one the skeleton carries is `A`'s own
credence. The repair taken here is different and measure-free: quantify over
cells. `cellwise_efficacy` asks for a live principal choice **in every cell of
`A`'s information**, which a single designated point cannot satisfy.

The price of that repair is stated where it is paid: `PROSECUTION.md` §4. Cellwise
efficacy entails that the selector is not cell-measurable, so it is false of a
perfectly predictable principal — and no condition compatible with a perfectly
predictable principal separates the two conducts extensionally, by Proposition 1.

Provisional names: `residual_non_capture`, `cellwise_efficacy`,
`global_efficacy`, `downstream_efficacy`, `ceremonial`, `principal_mediated`,
`intervention_well_posed`.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Callable, Mapping, Sequence

from model import (Conduct, Episode, mediated, mediates, response,
                   response_map, well_formed)


# --------------------------------------------------------------------------
# A -/-> D : residual non-capture, and when the intervention is a map at all
# --------------------------------------------------------------------------

def intervention_well_posed(selector_under: Callable[[str], object],
                            residual_variants: Sequence[Sequence[str]]) -> bool:
    """Whether the principal's choice can be varied with the advisor held fixed.

    `response` reads an intervention that sets the choice and does not propagate
    to whatever `A` used to predict it. If the advisor authors the choice, there
    is no such intervention: moving the choice moves the advisor's prediction
    with it, the two coordinates are one coordinate, and the response map is not
    a map of the conduct.

    `residual_variants` is the class grouped by licensed-reason trace. The
    grouping is not a detail: within a group the advisor supplied the same
    reasons, so a selector difference is residual influence; across groups a
    selector difference is persuasion, which the interface must permit. Asking
    the question of an ungrouped class would refuse persuasion.
    """
    return all(len({selector_under(policy) for policy in group}) <= 1
               for group in residual_variants)


# --------------------------------------------------------------------------
# H -> D : protected efficacy
# --------------------------------------------------------------------------

def live_choices(episode: Episode, conduct: Conduct, cell: str) -> tuple[str, ...]:
    """The distinct things the conduct does across interventions on the choice."""
    seen = []
    for choice in episode.choices:
        landed = response(episode, conduct, cell, choice)
        if landed not in seen:
            seen.append(landed)
    return tuple(seen)


def cellwise_efficacy(episode: Episode, admissible: Sequence[Conduct]) -> bool:
    """For every admissible conduct and **every cell**, two principal choices
    that the conduct answers differently.

    Universal in the advisor and universal in the cell, existential only in the
    pair of principal continuations. That is the review requirement of
    `projects/deference/rounds/2026-08-12-reachable-corrective-control/REVIEW.md`
    with the cell quantifier added, and the addition is what token responsiveness
    cannot buy: satisfying a designated point leaves every other cell flat.
    """
    return all(len(live_choices(episode, conduct, cell)) >= 2
               for conduct in admissible for cell in episode.cells)


def global_efficacy(episode: Episode, admissible: Sequence[Conduct]) -> bool:
    """The unrepaired form: for every admissible conduct, *some* pair of
    principal choices is answered differently.

    Kept so the regression that separates it from `cellwise_efficacy` has
    something to fail against.
    """
    return all(any(len(live_choices(episode, conduct, cell)) >= 2
                   for cell in episode.cells)
               for conduct in admissible)


def cooperative_witness(episode: Episode, admissible: Sequence[Conduct]) -> bool:
    """`exists advisor, exists principal continuation` — the failed form.

    The predecessor round's capability predicate quantified the advisor
    existentially, so "the principal can correct" meant "some advisor lets it".
    Present here only as the thing a regression shows to be insufficient.
    """
    return any(any(len(live_choices(episode, conduct, cell)) >= 2
                   for cell in episode.cells)
               for conduct in admissible)


def selector_is_cell_measurable(episode: Episode,
                                prep: Mapping[str, str]) -> bool:
    return all(len({episode.selector(s, prep[cell])
                    for s in episode.states_of(cell)}) <= 1
               for cell in episode.cells)


def principal_effect_is_exclusive(episode: Episode,
                                  prep: Mapping[str, str]) -> bool:
    """The first requirement of
    `projects/deference/rounds/2026-08-12-reachable-corrective-control/REVIEW.md`,
    in this typing: an effect of the principal that no advisor action reproduces.

    Taken as a claim about single realized choices it is **false here by
    construction** — the advisor can write any choice, and pretending otherwise
    would be a modelling stipulation rather than a protection. What survives is a
    claim about the *map*: the delegate's realized choice varies within a cell of
    the advisor's information, and nothing the advisor can write does.

    So the review's requirement is met exactly when the selector is not
    cell-measurable, which is exactly when the principal is not perfectly
    predictable. `PROSECUTION.md` §4 is where that price is paid.
    """
    return not selector_is_cell_measurable(episode, prep)


def reproducing_channels(episode: Episode,
                         prep: Mapping[str, str]) -> tuple[str, ...]:
    """Every constant channel whose realized choice map equals the delegate's.

    Enumerated, so `principal_effect_is_exclusive` is checked against the whole
    space of cell-measurable writes rather than asserted.
    """
    out: list[str] = []
    for written in product(episode.choices, repeat=len(episode.cells)):
        assignment = dict(zip(episode.cells, written))
        if all(assignment[episode.cell[s]] == episode.selector(s, prep[episode.cell[s]])
               for s in episode.states):
            out.append("/".join(written))
    return tuple(out)


# --------------------------------------------------------------------------
# D -> Y : downstream efficacy
# --------------------------------------------------------------------------

def downstream_efficacy(episode: Episode, conduct: Conduct) -> bool:
    """Some intervention on the choice changes the quantity at some state.

    Distinct from `cellwise_efficacy`, which reads what the conduct *does*. A
    conduct can answer two choices with two different actions that the world
    scores identically, and then the principal's choice is ceremonial in the only
    register that decides anything.
    """
    for state in episode.states:
        cell = episode.cell[state]
        scored = set()
        for choice in episode.choices:
            prep, landed, action = response(episode, conduct, cell, choice)
            scored.add(episode.quantity[(state, prep, landed, action)])
        if len(scored) >= 2:
            return True
    return False


def ceremonial(episode: Episode, conduct: Conduct) -> bool:
    """Mediated and downstream-inert: nominally the principal's, causally nothing."""
    return mediated(episode, conduct) and not downstream_efficacy(episode, conduct)


# --------------------------------------------------------------------------
# The composed predicate
# --------------------------------------------------------------------------

def principal_mediated(episode: Episode, conduct: Conduct,
                       admissible: Sequence[Conduct],
                       non_capture: bool) -> bool:
    """The three clauses on one conduct, with non-capture supplied from outside.

    Non-capture is a predicate of a **variation class of advisor policies** and
    not of a conduct — the counterfactual-legitimacy round's whole point — so it
    enters as a hypothesis rather than being recomputed here. `selector.py`
    checks it against that round's objects.

    Not called authority. What normative significance the predicate carries is
    `RECOGNITION_AND_ANSWERABILITY.md`'s question, and the answer there is that
    the predicate alone carries none.
    """
    return (non_capture
            and mediated(episode, conduct)
            and cellwise_efficacy(episode, admissible)
            and downstream_efficacy(episode, conduct))


def clauses(episode: Episode, conduct: Conduct, admissible: Sequence[Conduct],
            non_capture: bool) -> dict:
    """Every clause separately, because a single boolean hides which one fired."""
    return {
        "non_capture": non_capture,
        "mediated": mediated(episode, conduct),
        "cellwise_efficacy": cellwise_efficacy(episode, admissible),
        "global_efficacy": global_efficacy(episode, admissible),
        "downstream_efficacy": downstream_efficacy(episode, conduct),
        "ceremonial": ceremonial(episode, conduct),
        "forecloses": any(episode.preparation(conduct.prep[cell]).forecloses(
            episode.choices) for cell in episode.cells),
    }
