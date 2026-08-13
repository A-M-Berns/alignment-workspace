"""An evolving scorekeeping process, and the local-versus-replay question.

The recurrence witness in `test_learning` re-files the same position at every
date. That makes the loss exogenous and the comparison additive **by
construction**, which is the hypothesis the learning track's own applicability
audit places outside its additive reduction.

Here the state carries forward. A repair at date `t` changes the position the
date `t+1` loss is read from, so the comparator's intervention has downstream
consequences. Two quantities can then differ:

    local regret   sum over dates of  [ loss(actual) - loss(transformed) ]
                   with both read at the *actual* trajectory's state

    replay regret  loss of the actual run  minus  loss of the run in which the
                   comparator was applied at every date and the state evolved
                   accordingly

`distortion` is their difference. The additive reduction the online-learning
theorem uses is exactly the assumption that this is zero; the question this
module exists to answer is how it grows with the horizon.

The environment is deliberately thin: at each date it exposes one further
consequential commitment, in a fixed order, and does nothing else. That is
enough to make the state evolve without introducing an arrival process.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, List, Sequence, Tuple

from learning import (
    LAMBDA,
    Program,
    defect,
    interpret,
    public_status,
    step,
)
from moves import Move, apply_move
from scorekeeping import Agent, Content, State


def expose_next(state: State, critic: Agent, learner: Agent) -> State:
    """The environment's move: raise the least unexposed consequence, if any.

    Fixed, public, and independent of what the learner did — an exogenous
    demand process, not a response to the learner's play.
    """
    pending = sorted(
        c
        for c in state.unacknowledged_consequences(critic, learner)
        if not state.is_exposed(learner, c)
    )
    if not pending:
        return state
    return apply_move(state, Move("query", critic, other=learner, content=pending[0]))


#: A second environment, which replenishes the *licensing condition* rather than
#: only the exposures. The critic acquires an entitled ground and challenges with
#: it, so live challenges keep arriving instead of running out.
#:
#: This exists because the first environment made one comparator look bounded for
#: the wrong reason. A comparator that can only fire a bounded number of times has
#: bounded distortion trivially, and distinguishing that from a structural
#: stability property is the whole question.
REPLENISH_SCHEDULE = (("u", "a_rho"), ("s", "beta"))


def replenish(state: State, critic: Agent, learner: Agent) -> State:
    """Raise a fresh entitled challenge where one is available."""
    live = {c.content for c in state.live_challenges(critic, learner)}
    for ground, target in REPLENISH_SCHEDULE:
        if target in live or (learner, target) in state.vindications:
            continue
        if target not in state.commitments(critic, learner):
            continue
        working = state
        if ground not in state.ack[critic]:
            working = apply_move(working, Move("assert", critic, content=ground))
        after = apply_move(
            working,
            Move("challenge", critic, other=learner, content=target, ground=ground),
        )
        if len(after.live_challenges(critic, learner)) > len(
            state.live_challenges(critic, learner)
        ):
            return after
    return state


@dataclass(frozen=True)
class Run:
    losses: Tuple[Fraction, ...]
    states: Tuple[State, ...]

    @property
    def total(self) -> Fraction:
        return sum(self.losses, Fraction(0))


def run_trajectory(
    start: State,
    learner: Agent,
    critic: Agent,
    horizon: int,
    policy: Callable[[State, int], str],
    environment: Callable[[State, Agent, Agent], State] = expose_next,
) -> Run:
    """Play `horizon` dates, letting the state carry forward.

    Each date: the environment moves, the loss of the resulting position is
    recorded, the learner plays, and the state carries to the next date.
    """
    losses: List[Fraction] = []
    states: List[State] = []
    state = start
    for date in range(horizon):
        state = environment(state, critic, learner)
        states.append(state)
        losses.append(defect(state, learner, critic))
        state = step(state, learner, critic, policy(state, date))
    return Run(tuple(losses), tuple(states))


def local_regret(
    start: State,
    learner: Agent,
    critic: Agent,
    horizon: int,
    program: Program,
    base_label: str,
    environment: Callable[[State, Agent, Agent], State] = expose_next,
) -> Fraction:
    """Regret measured the way the additive reduction measures it.

    At each date of the **actual** trajectory, compare the loss the played label
    leaves against the loss the transformed label would have left, without
    letting the transformation affect what comes next.
    """
    total = Fraction(0)
    state = start
    for _ in range(horizon):
        state = environment(state, critic, learner)
        status = public_status(state, learner, critic)
        played = base_label
        swapped = interpret(program, status, played)
        after_played = step(state, learner, critic, played)
        after_swapped = step(state, learner, critic, swapped)
        total += defect(after_played, learner, critic) - defect(
            after_swapped, learner, critic
        )
        state = after_played
    return total


def replay_regret(
    start: State,
    learner: Agent,
    critic: Agent,
    horizon: int,
    program: Program,
    base_label: str,
    environment: Callable[[State, Agent, Agent], State] = expose_next,
) -> Fraction:
    """Regret measured by replaying the whole run under the transformation.

    The transformed trajectory evolves: applying the repair at date `t` changes
    the position at `t+1`, so its later losses are its own.
    """
    actual = run_trajectory(
        start, learner, critic, horizon, lambda s, d: base_label, environment
    )
    transformed = run_trajectory(
        start,
        learner,
        critic,
        horizon,
        lambda s, d: interpret(program, public_status(s, learner, critic), base_label),
        environment,
    )
    return actual.total - transformed.total


def distortion(
    start: State,
    learner: Agent,
    critic: Agent,
    horizon: int,
    program: Program,
    base_label: str,
    environment: Callable[[State, Agent, Agent], State] = expose_next,
) -> Fraction:
    """`|local - replay|`. Zero is what the additive reduction assumes."""
    local = local_regret(start, learner, critic, horizon, program, base_label, environment)
    replay = replay_regret(
        start, learner, critic, horizon, program, base_label, environment
    )
    return abs(local - replay)


def distortion_profile(
    start: State,
    learner: Agent,
    critic: Agent,
    horizons: Sequence[int],
    program: Program,
    base_label: str,
) -> List[Tuple[int, Fraction, Fraction, Fraction]]:
    """`(horizon, local, replay, distortion)` at each horizon. Exact rationals."""
    out = []
    for horizon in horizons:
        local = local_regret(start, learner, critic, horizon, program, base_label)
        replay = replay_regret(start, learner, critic, horizon, program, base_label)
        out.append((horizon, local, replay, abs(local - replay)))
    return out
