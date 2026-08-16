"""Driving the repository's existing Theorem 18 learner on the evolving process.

The learner is not reimplemented here. `BlumMansourLearner` from the item-30
round is instantiated against a loss process it was never built for — one whose
loss vectors are produced by a scorekeeping state the learner's own past actions
have shaped.

That it can be is the point. The learner consumes a per-round map list and a
per-round loss vector and asks nothing about where either came from, which is
exactly the interface the source theorem's proof needs: a sequence of `(p^t,
ell^t)` pairs with `ell^t` determined before the sample at `t`.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from actual import ActualRun, loss_vector, replenishing
from fixture import C, H
from learning import LAMBDA, defect, public_status, step
from phi_learner import BlumMansourLearner
from scorekeeping import Agent, State
from surgical import SurgicalRepair, identity_indices


def rule_maps(
    repairs: Sequence[SurgicalRepair], state: State, learner: Agent, critic: Agent
) -> Tuple[Tuple[int, ...], ...]:
    """The date-`t` map list: the identity rule first, then each surgical repair."""
    status = public_status(state, learner, critic)
    maps = [identity_indices(LAMBDA)]
    maps.extend(repair.indices(status, LAMBDA) for repair in repairs)
    return tuple(maps)


def run_learner(
    start: State,
    repairs: Sequence[SurgicalRepair],
    horizon: int,
    *,
    learner: Agent = H,
    critic: Agent = C,
    loss_max: Fraction = Fraction(22),
    precision: int = 60,
) -> ActualRun:
    """One evolving trajectory driven by the repository's Theorem 18 learner.

    The realized action is the highest-mass label, ties broken by the fixed
    alphabet order. That keeps the run deterministic and every number exact; the
    mixed-mass quantity the theorem bounds does not depend on the realization
    rule, and the state evolution is a legitimate adaptive environment under any
    of them.
    """
    engine = BlumMansourLearner(
        horizon, len(LAMBDA), len(repairs) + 1, loss_max=loss_max, precision=precision
    )
    states: List[State] = []
    mixes: List[Dict[str, Fraction]] = []
    losses: List[Dict[str, Fraction]] = []
    played: List[str] = []

    state = start
    for _ in range(horizon):
        state = replenishing(state, critic, learner)
        maps = rule_maps(repairs, state, learner, critic)
        prepared = engine.prepare(maps)
        distribution = {
            label: prepared.distribution[i] for i, label in enumerate(LAMBDA)
        }
        vector = loss_vector(state, learner, critic)
        states.append(state)
        mixes.append(distribution)
        losses.append(vector)
        engine.update(prepared, [vector[label] for label in LAMBDA])
        action = max(LAMBDA, key=lambda a: (distribution[a], -LAMBDA.index(a)))
        played.append(action)
        state = step(state, learner, critic, action)
    return ActualRun(tuple(states), tuple(mixes), tuple(losses), tuple(played))
