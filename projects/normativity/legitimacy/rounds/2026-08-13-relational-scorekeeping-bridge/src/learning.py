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
QUERY = "query"
DEFER = "defer"
SELF_REVISE = "self-revise"
DISAVOW = "disavow"

LAMBDA: Tuple[str, ...] = (
    HOLD,
    ACKNOWLEDGE,
    VINDICATE,
    SUSPEND,
    QUERY,
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
        content = _least(state.exposed_unacknowledged(critic, learner))
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
        # Suspension, not retraction. The commitment survives; what stops is
        # deploying the content as an entitlement-bearing premise. Applies to any
        # precluded commitment, acknowledged or consequential, because an
        # undercut applicability claim need not have been asserted outright.
        content = _least(state.precluded_commitments(critic, learner))
        if content is None:
            return None
        return Move("suspend", learner, content=content)

    if label == QUERY:
        live = sorted(state.live_challenges(critic, learner), key=lambda c: c.content)
        if not live:
            return None
        # Putting the question publicly. `query` writes an exposure, which is a
        # real state change on a content not already raised, and redundant on one
        # a challenge has already raised. The comparator that uses this label
        # carries its force in the substitution *away from* `disavow`, not in the
        # query — which is why the label says what the move does and no more.
        return Move("query", learner, content=live[0].content, other=learner)

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
W_EXPOSED_UNACKNOWLEDGED = Fraction(1, 2)
W_LIVE_CHALLENGE = Fraction(1)
W_PRECLUDED = Fraction(1, 2)
W_UNSUPPORTED_PRACTICAL = Fraction(1)


def defect(state: State, learner: Agent, critic: Agent) -> Fraction:
    """The theorem-facing loss: the learner's *relational answerability* defect.

    Three components, each a count over a finite content set:

    - consequential commitments that have been publicly raised and not
      acknowledged — exposed, not merely entailed;
    - entitled unvindicated challenges against a commitment still in force;
    - commitments whose entitlement is materially precluded and not suspended.

    Every input is one of `ack[learner]`, `practice[critic]`, `ack[critic]`,
    `challenges`, `exposures`, `vindications`, `suspensions`. The learner writes
    `ack[learner]`, its own suspensions, and its own vindications — all of which
    are recognised answers — and writes none of the rest.

    **The practical-authority term is deliberately absent.** See
    `practical_authority_defect`, and `LOSS_DEPENDENCY_AUDIT.md` for why
    including it made the loss self-launderable.
    """
    return (
        W_EXPOSED_UNACKNOWLEDGED * len(state.exposed_unacknowledged(critic, learner))
        + W_LIVE_CHALLENGE * len(state.live_challenges(critic, learner))
        + W_PRECLUDED * len(state.precluded_commitments(critic, learner))
    )


def practical_authority_defect(
    state: State, learner: Agent, critic: Agent
) -> Fraction:
    """Practical commitments the learner has no authority to act on.

    **Not theorem-facing.** This term reads the grant relation, and an agent
    holding authority over its own authority can discharge it by granting itself
    the subject — answering nothing. The same coordinate that protects the
    principal's corrective capability on the corrigibility arc is what makes this
    term self-launderable on the learning arc. Kept, measured, and excluded from
    `defect` until it has a non-self-launderable semantics.
    """
    return W_UNSUPPORTED_PRACTICAL * len(
        state.unsupported_practical(critic, learner)
    )


def loss_bound(state: State) -> Fraction:
    """`ell_max`: the defect cannot exceed this, for any position over this vocabulary."""
    size = len(state.vocabulary.contents)
    return (
        W_EXPOSED_UNACKNOWLEDGED * size
        + W_LIVE_CHALLENGE * size
        + W_PRECLUDED * size
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
    challenged_content_is_practical: bool
    #: Whether some live challenger holds practical authority over the corrective
    #: subject. A *property* of the challenger, not its name: enough to separate
    #: challenges that differ in standing, without letting a guard key on identity
    #: and so smuggle back the indexing the fixed-program reading exists to avoid.
    challenger_holds_corrective_authority: bool


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


def public_status(
    state: State, learner: Agent, critic: Agent, corrective_subject: str = "correction"
) -> PublicStatus:
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
        has_unacknowledged=bool(state.exposed_unacknowledged(critic, learner)),
        has_live_challenge=bool(live),
        vindication_available=vindication_available,
        has_defeated_acknowledgment=bool(
            state.precluded_commitments(critic, learner)
        ),
        testimony_available=any(
            source != learner for source, _ in state.testimony_permitted
        ),
        has_unsupported_practical=bool(state.unsupported_practical(critic, learner)),
        challenged_content_is_practical=any(
            state.vocabulary.is_practical(c.content)
            for c in state.live_challenges(critic, learner)
        ),
        challenger_holds_corrective_authority=any(
            state.has_authority(c.challenger, corrective_subject)
            for c in state.live_challenges(critic, learner)
        ),
    )


# ----------------------------------------------------------------- programs


@dataclass(frozen=True)
class Program:
    """A declarative comparator. Holds a kind, a certificate, and no callable.

    `certificate` names the **positive public reason** that licenses this
    transformation. Lawfulness is that a licensing reason is present, not that
    the transformation lowers anything: `certify` below reads `PublicStatus` and
    is never given a loss.
    """

    identifier: str
    kind: str
    certificate: str


#: The public normative reasons that can license a transformation. Each is a
#: predicate of `PublicStatus`, evaluated by `certify`. `none` is the identity's,
#: which needs no licence because it changes nothing.
CERTIFICATES = (
    "none",
    "exposed_consequential_burden",
    "defeated_applicability",
    "live_challenge_with_available_justification",
    "live_unresolved_challenge",
    "testimonial_entitlement_route",
    "no_licence_for_standards_revision",
)


def certify(certificate: str, status: PublicStatus) -> bool:
    """Whether the public reason this certificate names is present.

    The compilation step. It sees six booleans of scorekeeping status and has no
    access to the loss, to a saving, to a future state, or to a date. A
    transformation is normatively lawful at a state when its certificate holds
    there; whether it happens to help is a separate question the learner asks and
    the compiler does not.
    """
    if certificate == "none":
        return True
    if certificate == "exposed_consequential_burden":
        return status.has_unacknowledged
    if certificate == "defeated_applicability":
        return status.has_defeated_acknowledgment
    if certificate == "live_challenge_with_available_justification":
        return status.vindication_available
    if certificate == "live_unresolved_challenge":
        return status.has_live_challenge
    if certificate == "testimonial_entitlement_route":
        return status.testimony_available
    if certificate == "no_licence_for_standards_revision":
        # Refusing a move needs no positive licence: declining to revise one's
        # own standards is always available.
        return True
    raise ValueError(f"no such certificate: {certificate}")


PROGRAMS: Tuple[Program, ...] = (
    Program("identity", "identity", "none"),
    Program("acknowledge_exposed", "acknowledge_exposed", "exposed_consequential_burden"),
    Program(
        "vindicate_live",
        "vindicate_live",
        "live_challenge_with_available_justification",
    ),
    Program("suspend_defeated", "suspend_defeated", "defeated_applicability"),
    Program("query_not_disavow", "query_not_disavow", "live_unresolved_challenge"),
    Program(
        "defer_where_permitted", "defer_where_permitted", "testimonial_entitlement_route"
    ),
    Program(
        "refuse_self_revision",
        "refuse_self_revision",
        "no_licence_for_standards_revision",
    ),
    Program(
        "answer_then_acknowledge",
        "answer_then_acknowledge",
        "live_challenge_with_available_justification",
    ),
    Program(
        "suspend_then_acknowledge", "suspend_then_acknowledge", "defeated_applicability"
    ),
)


def is_lawful(program: Program, status: PublicStatus) -> bool:
    """Whether this program is normatively licensed at this public status."""
    return certify(program.certificate, status)


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

    if kind == "query_not_disavow":
        # Refusing the erasure. A disavowal aimed at a challenged content is
        # replaced by putting the question, so the commitment stays in force and
        # the challenge stays live instead of lapsing with its basis.
        if label == DISAVOW and status.has_live_challenge:
            return QUERY
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
