"""The online-learning face of the scorekeeping state.

Three objects, in the shape the existing generic interface asks for.

`Lambda`      a fixed eight-label response alphabet, horizon-independent, with no
              date, content or occasion identity in a label. Decoding a label at
              a state is occasion-local, by a fixed total order.

`public_loss` a bounded prospective action-indexed loss read from a *second*
              scorekeeper's attributions. Its inputs are that scorekeeper's
              practice and the learner's public acknowledgments. The learner has
              no move that writes either the scorekeeper's practice or the
              scorekeeper's attributions, which is where resistance to
              self-erasure comes from.

`PROGRAMS`    nine declarative comparator records. A record holds a kind and no
              callable. The interpreter reads `PublicStatus`, which carries
              scorekeeping statuses and carries no loss, charge, profitability,
              future or horizon field.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, FrozenSet, Optional, Tuple

from moves import Illegal, Move, apply_move
from scorekeeping import Agent, Content, State

# ------------------------------------------------------------------ alphabet

HOLD = "hold"
ACKNOWLEDGE = "acknowledge"
VINDICATE = "vindicate"
SUSPEND = "suspend"
REOPEN = "reopen"
DEFER = "defer"
SELF_REVISE = "self-revise"
DISAVOW = "disavow"

LAMBDA: Tuple[str, ...] = (
    HOLD,
    ACKNOWLEDGE,
    VINDICATE,
    SUSPEND,
    REOPEN,
    DEFER,
    SELF_REVISE,
    DISAVOW,
)


def _least(contents) -> Optional[Content]:
    """The fixed total order the occasion-local decoder uses."""
    return min(contents) if contents else None


def decode(state: State, learner: Agent, critic: Agent, label: str) -> Optional[Move]:
    """The occasion-local decoder `d_t`. A label with nothing to act on is a no-op.

    Every branch reads only the public scorekeeping position. The two labels a
    laundering strategy would reach for — `self-revise` and `disavow` — are in the
    alphabet on purpose, so that the loss can be shown not to fall when they are
    played.
    """
    if label == HOLD:
        return None

    if label == ACKNOWLEDGE:
        content = _least(state.unacknowledged_consequences(critic, learner))
        if content is None or state.vocabulary.is_practical(content):
            return None
        return Move("assert", learner, content=content)

    if label == VINDICATE:
        live = sorted(state.live_challenges(critic, learner), key=lambda c: c.content)
        if not live:
            return None
        challenge = live[0]
        return Move(
            "vindicate", learner, content=challenge.content, other=challenge.challenger
        )

    if label == SUSPEND:
        blocked = state.blocked(critic, learner) & state.ack[learner]
        content = _least(blocked)
        if content is None:
            return None
        return Move("disavow", learner, content=content)

    if label == REOPEN:
        live = sorted(state.live_challenges(critic, learner), key=lambda c: c.content)
        if not live:
            return None
        return Move(
            "query", learner, content=live[0].content, other=live[0].challenger
        )

    if label == DEFER:
        options = sorted(
            (source, content)
            for source, content in state.testimony_permitted
            if source != learner
        )
        if not options:
            return None
        source, content = options[0]
        return Move("defer", learner, content=content, other=source)

    if label == SELF_REVISE:
        rules = sorted(state.practice[learner].committive, key=lambda r: (r[1], sorted(r[0])))
        if not rules:
            return None
        return Move("revise_committive", learner, rule=rules[0], present=False)

    if label == DISAVOW:
        content = _least(state.ack[learner])
        if content is None:
            return None
        return Move("disavow", learner, content=content)

    raise ValueError(f"no such label: {label}")


def step(state: State, learner: Agent, critic: Agent, label: str) -> State:
    """Play a label. An illegal decoded move is a no-op, so every label is total."""
    move = decode(state, learner, critic, label)
    if move is None:
        return state
    try:
        return apply_move(state, move)
    except Illegal:
        return state


# ---------------------------------------------------------------------- loss

#: Defect weights. Exact rationals; no result depends on a float.
W_UNACKNOWLEDGED = Fraction(1, 2)
W_LIVE_CHALLENGE = Fraction(1)
W_DEFEATED = Fraction(1, 2)
W_UNSUPPORTED_PRACTICAL = Fraction(1)


def defect(state: State, learner: Agent, critic: Agent) -> Fraction:
    """The public answerability defect of a position, read from the critic's score.

    Four components, each a count over a finite content set:

    - consequential commitments the learner has not acknowledged;
    - entitled challenges against the learner that are unvindicated;
    - commitments whose entitlement is defeated;
    - practical commitments the learner has no authority to act on.

    Every input is either the learner's public acknowledgments or the critic's own
    practice. Nothing here reads the learner's practice, so revising it moves
    nothing in this number.
    """
    return (
        W_UNACKNOWLEDGED * len(state.unacknowledged_consequences(critic, learner))
        + W_LIVE_CHALLENGE * len(state.live_challenges(critic, learner))
        + W_DEFEATED * len(state.defeated_commitments(critic, learner))
        + W_UNSUPPORTED_PRACTICAL * len(state.unsupported_practical(critic, learner))
    )


def loss_bound(state: State) -> Fraction:
    """`ell_max`: the defect cannot exceed this, for any position over this vocabulary."""
    size = len(state.vocabulary.contents)
    return (
        W_UNACKNOWLEDGED * size
        + W_LIVE_CHALLENGE * size
        + W_DEFEATED * size
        + W_UNSUPPORTED_PRACTICAL * size
    )


def loss_vector(
    state: State, learner: Agent, critic: Agent
) -> Dict[str, Fraction]:
    """Prospective full-information loss: the defect each label would leave behind."""
    return {
        label: defect(step(state, learner, critic, label), learner, critic)
        for label in LAMBDA
    }


# ------------------------------------------------------------- public status


@dataclass(frozen=True)
class PublicStatus:
    """The sealed context a comparator guard may read.

    Scorekeeping statuses only. There is deliberately no loss, charge, saving,
    profitability, account, horizon, weight, future-state or comparative-advantage
    field, and `test_learning` asserts the schema to keep it that way. A guard
    cannot be written that consults what a transformation is worth.
    """

    has_unacknowledged: bool
    has_live_challenge: bool
    vindication_available: bool
    has_defeated_acknowledgment: bool
    testimony_available: bool
    has_unsupported_practical: bool


PROHIBITED_STATUS_FIELDS = (
    "loss",
    "charge",
    "saving",
    "profit",
    "profitability",
    "account",
    "balance",
    "horizon",
    "weight",
    "future",
    "advantage",
    "regret",
    "tariff",
)


def public_status(state: State, learner: Agent, critic: Agent) -> PublicStatus:
    live = state.live_challenges(critic, learner)
    vindication_available = False
    for challenge in live:
        move = Move(
            "vindicate", learner, content=challenge.content, other=challenge.challenger
        )
        try:
            apply_move(state, move)
        except Illegal:
            continue
        vindication_available = True
        break
    return PublicStatus(
        has_unacknowledged=bool(state.unacknowledged_consequences(critic, learner)),
        has_live_challenge=bool(live),
        vindication_available=vindication_available,
        has_defeated_acknowledgment=bool(
            state.blocked(critic, learner) & state.ack[learner]
        ),
        testimony_available=any(
            source != learner for source, _ in state.testimony_permitted
        ),
        has_unsupported_practical=bool(state.unsupported_practical(critic, learner)),
    )


# ----------------------------------------------------------------- programs


@dataclass(frozen=True)
class Program:
    """A declarative comparator. Holds a kind and no callable."""

    identifier: str
    kind: str


PROGRAMS: Tuple[Program, ...] = (
    Program("identity", "identity"),
    Program("acknowledge_exposed", "acknowledge_exposed"),
    Program("vindicate_live", "vindicate_live"),
    Program("suspend_defeated", "suspend_defeated"),
    Program("reopen_not_disavow", "reopen_not_disavow"),
    Program("defer_where_permitted", "defer_where_permitted"),
    Program("refuse_self_revision", "refuse_self_revision"),
    Program("answer_then_acknowledge", "answer_then_acknowledge"),
    Program("suspend_then_acknowledge", "suspend_then_acknowledge"),
)


def interpret(program: Program, status: PublicStatus, label: str) -> str:
    """The fixed interpreter. One program, one syntax, a map indexed by public status.

    The map a program induces varies with the state because the guard reads the
    state. The program does not. That is exactly the history-indexed modification
    rule the source online-learning theorem admits, and it is what the uniform
    state-independent reading of the comparator class gets wrong.
    """
    kind = program.kind

    if kind == "identity":
        return label

    if kind == "acknowledge_exposed":
        return ACKNOWLEDGE if status.has_unacknowledged else label

    if kind == "vindicate_live":
        return VINDICATE if status.vindication_available else label

    if kind == "suspend_defeated":
        return SUSPEND if status.has_defeated_acknowledgment else label

    if kind == "reopen_not_disavow":
        # Reopening rather than erasing: a disavowal aimed at a challenged content
        # is replaced by putting the question, which leaves the burden standing.
        if label == DISAVOW and status.has_live_challenge:
            return REOPEN
        return label

    if kind == "defer_where_permitted":
        return DEFER if status.testimony_available else label

    if kind == "refuse_self_revision":
        return HOLD if label == SELF_REVISE else label

    if kind == "answer_then_acknowledge":
        if status.vindication_available:
            return VINDICATE
        if status.has_unacknowledged:
            return ACKNOWLEDGE
        return label

    if kind == "suspend_then_acknowledge":
        if status.has_defeated_acknowledgment:
            return SUSPEND
        if status.has_unacknowledged:
            return ACKNOWLEDGE
        return label

    raise ValueError(f"no such program kind: {kind}")


def transformation(
    program: Program, state: State, learner: Agent, critic: Agent
) -> Dict[str, str]:
    """`F^t_phi(x_t)`: the label map this program induces at this state."""
    status = public_status(state, learner, critic)
    return {label: interpret(program, status, label) for label in LAMBDA}
