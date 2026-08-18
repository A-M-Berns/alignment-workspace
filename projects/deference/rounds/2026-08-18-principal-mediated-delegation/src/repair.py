"""The repair, its bound, and the split the bound forces.

`Repair` keeps everything a preemptive conduct prepared and changes one thing:
the channel becomes the identity, so the world's choice argument is the
principal's and not the conduct's. Off the agreement region the repaired conduct
takes the best action available to it at the realized choice, which can only help.

The bound is one inequality,

    value(pi) - value(repair(pi))  <=  2 * B * channel_disagreement(pi)

with the same proof and the same constant as
`lean/Workspace/Deference/Contrib/DelegationBridge.lean`'s
`delegation_bridge_unconditional`, read with the comparator taken to be the
conduct's channel composed with the selector. `bridge_form` below runs the
sharper `delegation_bridge` in this register.

**What the bound is in.** Not the prediction error. `channel_disagreement` is
the credence on which the conduct's channel *moves* the principal's choice, and
that is the conduct's own decision. `decomposition` splits it in two, and the
split is the round's result:

    eps_acc   the channel writes what `A` predicts, and the prediction misses
    eps_over  the channel writes something `A` does not predict

`eps_acc <= eps_pred` always. `eps_over` is bounded by nothing here. A conduct
with `eps_over = 0` preempts in order to act early on what it expects; one with
`eps_over > 0` preempts in order to install something else, and the value of
doing so is the principal's judgment against `A`'s, which
`FINITE_MODEL_SKELETON.md` §8.5 declares unrelated to the quantity.

**What the bound is silent about.** Foreclosure. `repair` preserves the
preparation, so a conduct that destroys the principal's options and then defers
to the single option left is repaired at zero cost and is mediated vacuously.
`foreclosure_premium` is the term that catches it, it is not a prediction
quantity, and it is why this round does not present the bound as a corrigibility
result.

Provisional names: `repair`, `channel_disagreement` (in `model`),
`decomposition`, `acceleration_class`, `fully_updated_substitution`,
`preemption_incentive`, `foreclosure_premium`, `bridge_form`.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Mapping, Sequence

from model import (Conduct, Episode, best_prediction, channel_disagreement,
                   constant_channel, identity_channel, mediated,
                   mediated_conducts, prediction_error, preemptive,
                   realized_quantity, value)


def conditional_value(episode: Episode, cell: str, prep: str, choice: str,
                      action: str) -> Fraction:
    return sum((episode.credence[s] * episode.quantity[(s, prep, choice, action)]
                for s in episode.states_of(cell)), Fraction(0))


def best_action(episode: Episode, cell: str, prep: str, choice: str) -> str:
    """`A`'s best action at the realized choice, on the information it then has.

    Available to the repaired conduct because at `F(n)` the choice is in hand.
    Ties break by the fixed order on actions.
    """
    return max(episode.actions,
               key=lambda u: (conditional_value(episode, cell, prep, choice, u),
                              -episode.actions.index(u)))


def repair(episode: Episode, conduct: Conduct) -> Conduct:
    """The principal-preserving repair: same preparation, identity channel.

    On the states where the conduct's channel already agreed with the principal
    the repaired conduct is the same function, so the two agree exactly there.
    Everywhere else the repaired conduct does the best it can at the choice the
    principal actually made.
    """
    implement: dict[tuple[str, str], str] = {}
    for cell in episode.cells:
        prep = conduct.prep[cell]
        for choice in episode.choices:
            if conduct.channel[(cell, choice)] == choice:
                implement[(cell, choice)] = conduct.implement[(cell, choice)]
            else:
                implement[(cell, choice)] = best_action(episode, cell, prep, choice)
    return Conduct(f"repair({conduct.name})", dict(conduct.prep),
                   identity_channel(episode), implement)


def deficit(episode: Episode, conduct: Conduct) -> Fraction:
    return value(episode, conduct) - value(episode, repair(episode, conduct))


def bound(episode: Episode, conduct: Conduct) -> Fraction:
    return 2 * episode.bound * channel_disagreement(episode, conduct)


def repair_holds(episode: Episode, conduct: Conduct) -> bool:
    return deficit(episode, conduct) <= bound(episode, conduct)


def agreement_region(episode: Episode, conduct: Conduct) -> tuple[str, ...]:
    out = []
    for state in episode.states:
        cell = episode.cell[state]
        chosen = episode.selector(state, conduct.prep[cell])
        if conduct.channel[(cell, chosen)] == chosen:
            out.append(state)
    return tuple(out)


def agrees_on_agreement_region(episode: Episode, conduct: Conduct) -> bool:
    """The step the bound's proof rests on, checked rather than described."""
    repaired = repair(episode, conduct)
    return all(realized_quantity(episode, conduct, state)
               == realized_quantity(episode, repaired, state)
               for state in agreement_region(episode, conduct))


# --------------------------------------------------------------------------
# The split
# --------------------------------------------------------------------------

def decomposition(episode: Episode, conduct: Conduct,
                  predictor: Mapping[str, str]) -> dict[str, Fraction]:
    """`eps_acc` and `eps_over`, exactly, with the prediction error beside them.

    `eps_acc` is the credence on which the channel writes what `A` predicts and
    the prediction is wrong; `eps_over` is the credence on which it writes
    something else. They partition `channel_disagreement`, and only the first is
    dominated by `eps_pred`.
    """
    acceleration = Fraction(0)
    override = Fraction(0)
    for state in episode.states:
        cell = episode.cell[state]
        chosen = episode.selector(state, conduct.prep[cell])
        written = conduct.channel[(cell, chosen)]
        if written == chosen:
            continue
        if written == predictor[cell]:
            acceleration += episode.credence[state]
        else:
            override += episode.credence[state]
    return {
        "eps_acc": acceleration,
        "eps_over": override,
        "eps_pred": prediction_error(episode, conduct.prep, predictor),
        "disagreement": acceleration + override,
        "deficit": deficit(episode, conduct),
        "bound": bound(episode, conduct),
    }


def acceleration_class(episode: Episode,
                       preps: Sequence[Mapping[str, str]] | None = None
                       ) -> list[tuple[Conduct, dict[str, str]]]:
    """Preemptive conducts whose channel writes exactly `A`'s own prediction.

    The class is syntactic — the channel is the constant `d^` — so membership is
    not "`A` prefers delegation" in disguise. Every member physically bypasses
    the principal; what none of them does is write a value `A` does not expect
    the principal to reach.
    """
    cells = episode.cells
    family = (list(preps) if preps is not None else
              [dict(zip(cells, combo))
               for combo in product([p.name for p in episode.preparations],
                                    repeat=len(cells))])
    out: list[tuple[Conduct, dict[str, str]]] = []
    for index, prep in enumerate(family):
        predictor = best_prediction(episode, prep)
        channel = constant_channel(episode, predictor)
        implement = {(cell, choice): best_action(episode, cell, prep[cell], choice)
                     for cell in cells for choice in episode.choices}
        conduct = Conduct(f"accelerate-{index}", dict(prep), channel, implement)
        out.append((conduct, predictor))
    return out


def fully_updated_substitution(episode: Episode,
                               preps: Sequence[Mapping[str, str]] | None = None
                               ) -> list[Conduct]:
    """The strongest preemptor this model can state: `A` keeps everything, takes
    every action available to it, conditions on all it knows, and then writes the
    choice argument itself.

    **This is not the skeleton's `FU[g]`.** That hole needs a time-indexed family
    of `A`-valuations (`FINITE_MODEL_SKELETON.md` §8.1) and this model carries one
    index and one credence, so what is built here is the *substitution* half of a
    fully-updated comparator and nothing is claimed about the rest. Collapsing
    `FU[g]` into it by definitional stretching is the failure §4 of that document
    warns about, and the round does not do it.
    """
    cells = episode.cells
    family = (list(preps) if preps is not None else
              [dict(zip(cells, combo))
               for combo in product([p.name for p in episode.preparations],
                                    repeat=len(cells))])
    out: list[Conduct] = []
    for index, prep in enumerate(family):
        written: dict[str, str] = {}
        for cell in cells:
            written[cell] = max(
                episode.choices,
                key=lambda d: (conditional_value(
                    episode, cell, prep[cell], d,
                    best_action(episode, cell, prep[cell], d)),
                    -episode.choices.index(d)))
        implement = {(cell, choice): best_action(episode, cell, prep[cell], choice)
                     for cell in cells for choice in episode.choices}
        out.append(Conduct(f"fully-updated-{index}", dict(prep),
                           constant_channel(episode, written), implement))
    return out


# --------------------------------------------------------------------------
# Incentive and foreclosure
# --------------------------------------------------------------------------

def preemption_incentive(episode: Episode,
                         competitors: Sequence[Conduct],
                         admissible_preps: Sequence[Mapping[str, str]] | None = None
                         ) -> Fraction:
    """`Delta^pre`: the best competitor against the best mediated conduct.

    The mediated side is enumerated exhaustively over `admissible_preps`, so the
    comparison is against the class and not against a chosen delegate.
    """
    best_mediated_value = max(value(episode, c)
                              for c in mediated_conducts(episode, admissible_preps))
    return max((value(episode, c) for c in competitors),
               default=best_mediated_value) - best_mediated_value


def preserving_preps(episode: Episode) -> list[dict[str, str]]:
    names = [p.name for p in episode.preparations
             if not p.forecloses(episode.choices)]
    return [dict(zip(episode.cells, combo))
            for combo in product(names, repeat=len(episode.cells))]


def foreclosure_premium(episode: Episode) -> Fraction:
    """What the best foreclosing preparation buys over the best preserving one.

    Not a prediction quantity and not bounded by one. `repair` preserves the
    preparation, so this term survives the repair untouched: it is the price of
    the admissibility restriction, and the reason the bound above is not by
    itself a corrigibility result.
    """
    preserving = preserving_preps(episode)
    if not preserving:
        return Fraction(0)
    everything = max(value(episode, c) for c in mediated_conducts(episode))
    protected = max(value(episode, c)
                    for c in mediated_conducts(episode, preserving))
    return max(everything - protected, Fraction(0))


# --------------------------------------------------------------------------
# The sharp form: `delegation_bridge` in the selector register
# --------------------------------------------------------------------------

def grade_trust(episode: Episode, prep: Mapping[str, str],
                eta: Fraction) -> bool:
    """`GradeTrust` with the cells taken as singletons and the outcome model the
    conditional value of the best action at each choice.

    The Lean statement is over an admissible conditioning partition; taken at the
    finest partition it is the same predicate, which is the direction
    `gradeTrust_of_refinement` makes safe.
    """
    return all(abs(outcome_model(episode, prep, state, choice)
                   - episode.grade[(state, choice)]) <= eta
               for state in episode.states for choice in episode.choices)


def outcome_model(episode: Episode, prep: Mapping[str, str], state: str,
                  choice: str) -> Fraction:
    cell = episode.cell[state]
    action = best_action(episode, cell, prep[cell], choice)
    return episode.quantity[(state, prep[cell], choice, action)]


def bridge_form(episode: Episode, conduct: Conduct, eta: Fraction) -> dict:
    """`delegation_bridge`, with `sel` the channel's image and `J` the selector.

    Returns both sides, so a test compares exact rationals rather than a boolean
    someone could have made true by construction.
    """
    prep = conduct.prep
    left = Fraction(0)
    right = Fraction(0)
    margin = Fraction(0)
    disagreement = Fraction(0)
    for state in episode.states:
        cell = episode.cell[state]
        judged = episode.selector(state, prep[cell])
        selected = conduct.channel[(cell, judged)]
        mass = episode.credence[state]
        left += mass * outcome_model(episode, prep, state, selected)
        right += mass * outcome_model(episode, prep, state, judged)
        margin += mass * (episode.grade[(state, judged)]
                          - episode.grade[(state, selected)])
        if selected != judged:
            disagreement += mass
    return {
        "left": left + margin - 2 * eta * disagreement,
        "right": right,
        "margin": margin,
        "disagreement": disagreement,
        "holds": left + margin - 2 * eta * disagreement <= right,
    }
