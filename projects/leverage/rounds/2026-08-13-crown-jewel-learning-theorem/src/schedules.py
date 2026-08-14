"""Exposure schedules, and the margin derivation on the concrete loss.

Two exposure regimes, so the denominator can be shown to matter:

`dense`   the reason is raised at every date, `M_T = T`
`sparse`  the reason is raised on a thinning schedule, `M_T = Theta(sqrt(T))`

Under `sparse`, `Q_T/T -> 0` is uninformative — it would hold even if the learner
mishandled every single occasion — while `Q_T/M_T` is the quantity that says
whether the reason was answered.
"""
from __future__ import annotations

from fractions import Fraction
from math import isqrt
from typing import Callable, Dict, List, Sequence, Tuple

from actual import loss_vector, replenishing
from conditional import MarginCertificate
from fixture import C, H, W, base_state
from learning import (
    ACKNOWLEDGE,
    HOLD,
    LAMBDA,
    W_EXPOSED_UNACKNOWLEDGED,
    defect,
    public_status,
    step,
)
from moves import Move, apply_move
from scorekeeping import Agent, State

# --------------------------------------------------------------- schedules


def dense(date: int) -> bool:
    """Raise on every date."""
    return True


def sparse(date: int) -> bool:
    """Raise on perfect squares, so `M_T` grows like `sqrt(T)`."""
    root = isqrt(date)
    return root * root == date


def exposure_count(schedule: Callable[[int], bool], horizon: int) -> int:
    return sum(1 for date in range(horizon) if schedule(date))


def scheduled_environment(
    schedule: Callable[[int], bool]
) -> Callable[[State, Agent, Agent, int], State]:
    """Raise a burden only on the schedule's dates."""

    def environment(state: State, critic: Agent, learner: Agent, date: int) -> State:
        if not schedule(date):
            return state
        return replenishing(state, critic, learner)

    return environment


# ------------------------------------------------------- the margin, derived

#: `acknowledge` discharges one exposed unacknowledged consequence, worth
#: `W_EXPOSED_UNACKNOWLEDGED`. The side condition is what stops the discharge
#: being paid for elsewhere: taking up the content must not itself expose a new
#: consequence or preclude anything.
ACKNOWLEDGE_MARGIN = MarginCertificate(
    repair="answer_the_exposed_burden",
    discharges="one exposed unacknowledged consequential commitment",
    weight=W_EXPOSED_UNACKNOWLEDGED,
    side_condition="closure-inert and compatible",
)


def acknowledge_side_condition(
    state: State, learner: Agent, critic: Agent
) -> bool:
    """The public predicate the derived margin needs.

    Taking up the least exposed unacknowledged content must add no *further*
    exposed unacknowledged content and must preclude nothing. Both are read from
    the scorekeeping state; neither reads a loss.
    """
    exposed = state.exposed_unacknowledged(critic, learner)
    if not exposed:
        return False
    after = step(state, learner, critic, ACKNOWLEDGE)
    grew = after.exposed_unacknowledged(critic, learner) - (exposed - {min(exposed)})
    precluded_before = state.precluded_commitments(critic, learner)
    precluded_after = after.precluded_commitments(critic, learner)
    return not grew and precluded_after <= precluded_before


def observed_margin(state: State, learner: Agent, critic: Agent) -> Fraction:
    """The margin that actually obtains at this state, computed from the losses."""
    losses = loss_vector(state, learner, critic)
    return losses[HOLD] - losses[ACKNOWLEDGE]


def exposed_start() -> State:
    """A position with one exposed consequence and nothing else outstanding."""
    return apply_move(base_state(), Move("query", C, other=H, content=W))
