"""The actual trajectory, and the two quantities that must not be confused.

One evolving run. The learner's action at `t` changes the state carried into
`t+1`, so the loss process is endogenous in the ordinary sense: `ell_t = G(S_t)`
and `S_t` depends on every action before `t`.

Two quantities are computed from that one run.

**Local modification regret** — the source theorem's object. At each date the
transformed distribution is scored against the loss vector that actually obtained
at that date. The comparator's own trajectory is never built.

**Replay** — the previous round's object. The comparator is applied from the
start, the state evolves under it, and the two runs are compared. This diverges,
and the point of this round is that it does not have to be computed at all for
the local claim.

The environment replenishes: burdens keep arriving and challenges keep being
raised, so the targeted pattern recurs. A pattern that can occur only once
disappears for reasons that have nothing to do with learning.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Dict, List, Mapping, Sequence, Tuple

from evolving import expose_next
from fixture import A, ALPHA, A_RHO, BETA, C, H, Q, R, S, U, W, base_state
from learning import LAMBDA, defect, public_status, step
from moves import Move, apply_move
from scorekeeping import Agent, State
from surgical import (
    SurgicalRepair,
    round_bad_mass,
    round_gap,
    round_regret,
)

#: Grounds the critic can acquire, and what each lets it challenge.
CHALLENGE_SCHEDULE = ((U, A_RHO), (S, BETA))


def replenishing(state: State, critic: Agent, learner: Agent) -> State:
    """Raise a fresh burden, or a fresh entitled challenge, every date.

    Exogenous in the sense that matters for the source theorem: it is a fixed
    rule, and it never inspects the learner's current sample. It does read the
    state, which the learner's past actions have shaped — that is exactly the
    adaptive-in-the-strict-past generation the source theorem permits.
    """
    raised = expose_next(state, critic, learner)
    if raised != state:
        return raised
    live = {c.content for c in state.live_challenges(critic, learner)}
    for ground, target in CHALLENGE_SCHEDULE:
        if target in live or (learner, target) not in {
            (learner, t) for t in state.commitments(critic, learner)
        }:
            continue
        if (learner, target) in state.vindications:
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


def loss_vector(state: State, learner: Agent, critic: Agent) -> Dict[str, Fraction]:
    """`ell_t`: the defect each label would leave, read at the actual state."""
    return {
        label: defect(step(state, learner, critic, label), learner, critic)
        for label in LAMBDA
    }


Mixed = Mapping[str, Fraction]
Policy = Callable[[State, int], Mixed]


def point_mass(label: str) -> Dict[str, Fraction]:
    return {a: (Fraction(1) if a == label else Fraction(0)) for a in LAMBDA}


@dataclass(frozen=True)
class ActualRun:
    """One evolving trajectory and everything read off it."""

    states: Tuple[State, ...]
    mixed: Tuple[Dict[str, Fraction], ...]
    losses: Tuple[Dict[str, Fraction], ...]
    played: Tuple[str, ...]

    @property
    def horizon(self) -> int:
        return len(self.states)


def run_actual(
    start: State,
    learner: Agent,
    critic: Agent,
    horizon: int,
    policy: Policy,
    environment: Callable[[State, Agent, Agent], State] = replenishing,
    realize: Callable[[Mixed, int], str] | None = None,
) -> ActualRun:
    """Play `horizon` dates on one evolving trajectory.

    `policy` returns the mixed distribution at each date. `realize` turns it into
    the action actually taken, which is what carries the state forward; the
    default takes the highest-mass label, breaking ties by the fixed alphabet
    order, so the run is deterministic and the arithmetic is exact.
    """
    if realize is None:
        def realize(mixed: Mixed, date: int) -> str:
            return max(LAMBDA, key=lambda a: (mixed[a], -LAMBDA.index(a)))

    states: List[State] = []
    mixes: List[Dict[str, Fraction]] = []
    losses: List[Dict[str, Fraction]] = []
    played: List[str] = []

    state = start
    for date in range(horizon):
        state = environment(state, critic, learner)
        distribution = dict(policy(state, date))
        states.append(state)
        mixes.append(distribution)
        losses.append(loss_vector(state, learner, critic))
        action = realize(distribution, date)
        played.append(action)
        state = step(state, learner, critic, action)
    return ActualRun(tuple(states), tuple(mixes), tuple(losses), tuple(played))


# ----------------------------------------------------- the local quantities


def local_regret(run: ActualRun, repair: SurgicalRepair, learner: Agent, critic: Agent) -> Fraction:
    """`L_{H,I} - L_{H,I,F}` on the actual trajectory. No replay anywhere."""
    total = Fraction(0)
    for state, mixed, losses in zip(run.states, run.mixed, run.losses):
        status = public_status(state, learner, critic)
        total += round_regret(mixed, losses, repair, status)
    return total


def bad_mass(run: ActualRun, repair: SurgicalRepair, learner: Agent, critic: Agent) -> Fraction:
    """`Q_T`: cumulative mixed mass on (selector fires, action = b)."""
    total = Fraction(0)
    for state, mixed in zip(run.states, run.mixed):
        status = public_status(state, learner, critic)
        total += round_bad_mass(mixed, repair, status)
    return total


def minimum_gap(run: ActualRun, repair: SurgicalRepair, learner: Agent, critic: Agent) -> Fraction | None:
    """The least `loss(b) - loss(r)` over dates where the selector fires.

    `None` when the selector never fires — which is a vacuity report, not a
    `delta` of zero, and the tests check for it rather than reading a bound off
    an empty set.
    """
    gaps = []
    for state, losses in zip(run.states, run.losses):
        status = public_status(state, learner, critic)
        if repair.fires(status):
            gaps.append(round_gap(losses, repair, status))
    return min(gaps) if gaps else None


def selected_dates(run: ActualRun, repair: SurgicalRepair, learner: Agent, critic: Agent) -> int:
    return sum(
        1
        for state in run.states
        if repair.fires(public_status(state, learner, critic))
    )


# ------------------------------------------------------------ the replay control


def replay_totals(
    start: State,
    learner: Agent,
    critic: Agent,
    horizon: int,
    repair: SurgicalRepair,
    base_label: str,
    environment: Callable[[State, Agent, Agent], State] = replenishing,
) -> Tuple[Fraction, Fraction]:
    """`(actual total, comparator-trajectory total)` — the object this round avoids.

    Computed only to show that it diverges while the local claim stands. Nothing
    in `local_regret` reads it.
    """
    def constant(state: State, date: int) -> Mixed:
        return point_mass(base_label)

    def transformed(state: State, date: int) -> Mixed:
        status = public_status(state, learner, critic)
        image = repair.transformation(status)
        return point_mass(image[base_label])

    actual = run_actual(start, learner, critic, horizon, constant, environment)
    other = run_actual(start, learner, critic, horizon, transformed, environment)
    total_actual = sum(
        (losses[action] for losses, action in zip(actual.losses, actual.played)),
        Fraction(0),
    )
    total_other = sum(
        (losses[action] for losses, action in zip(other.losses, other.played)),
        Fraction(0),
    )
    return total_actual, total_other


def loaded_start() -> State:
    """The position the runs start from: a challenge live, the applicability chain in play."""
    state = apply_move(base_state(), Move("challenge", C, other=H, content=Q, ground=R))
    return apply_move(state, Move("assert", H, content=ALPHA))
