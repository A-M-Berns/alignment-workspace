"""The normative move grammar, and the one structural fact it is built to carry.

Every move is agent-indexed, and the index decides which coordinate it writes:

    Assert / Disavow / UndertakePractical  write  ack[mover]      and nothing else
    Revise*                                write  practice[mover] and nothing else
    Challenge / Query / Defer / Vindicate  write  bookkeeping     and nothing else
    Grant / Revoke                         write  grants          under a precondition
    Perform                                writes performed       under a precondition

Undertaking is something only the undertaker does. No agent has a move that
writes another agent's acknowledgments or another agent's practice. That is not
a permission bit; it is the shape of the move set, and `writes_of` below is what
the tests enumerate over.

Doxastic moves are open to every agent: anyone may assert, challenge, query,
defer and revise their own practice, without holding anything. Practical moves
are the only ones with an authority precondition. This is what stops the regress
— the practice does not need a norm licensing each normative transition, because
the doxastic transitions are unconditioned and the practical ones bottom out in
the initial grants.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from typing import FrozenSet, Optional, Tuple

from scorekeeping import (
    Agent,
    Challenge,
    Content,
    Grant,
    Rule,
    State,
    Subject,
    authority_over,
    pair,
)


class Illegal(Exception):
    """A move whose precondition the practice does not supply."""


# The coordinates of `State` a move may touch. Used by the enumeration that
# establishes principal-exclusive effects, so it is data rather than prose.
COORDINATES = (
    "ack",
    "practice",
    "grants",
    "challenges",
    "vindications",
    "deferrals",
    "performed",
    "exposures",
    "suspensions",
)


@dataclass(frozen=True)
class Move:
    kind: str
    mover: Agent
    content: Optional[Content] = None
    other: Optional[Agent] = None
    ground: Optional[Content] = None
    subject: Optional[Subject] = None
    rule: Optional[Rule] = None
    incompatible: Optional[FrozenSet[Content]] = None
    present: bool = True

    def __str__(self) -> str:  # pragma: no cover - display only
        bits = [self.kind, self.mover]
        for label, value in (
            ("content", self.content),
            ("other", self.other),
            ("ground", self.ground),
            ("subject", self.subject),
        ):
            if value is not None:
                bits.append(f"{label}={value}")
        return "(" + " ".join(bits) + ")"


DOXASTIC_KINDS = (
    "assert",
    "disavow",
    "suspend",
    "query",
    "challenge",
    "vindicate",
    "defer",
    "revise_committive",
    "revise_permissive",
    "revise_incompatible",
)
PRACTICAL_KINDS = ("undertake", "perform", "grant", "revoke")


def writes_of(kind: str) -> Tuple[str, ...]:
    """Which state coordinates a move of this kind can alter."""
    return {
        "assert": ("ack",),
        "disavow": ("ack",),
        "undertake": ("ack",),
        "query": ("exposures",),
        "challenge": ("challenges", "exposures"),
        "suspend": ("suspensions",),
        "vindicate": ("vindications",),
        "defer": ("deferrals",),
        "revise_committive": ("practice",),
        "revise_permissive": ("practice",),
        "revise_incompatible": ("practice",),
        "grant": ("grants",),
        "revoke": ("grants",),
        "perform": ("performed",),
    }[kind]


def apply_move(state: State, move: Move) -> State:
    """Transition. Raises `Illegal` where the practice supplies no precondition."""
    kind = move.kind
    mover = move.mover

    if kind in ("assert", "undertake"):
        content = move.content
        if content not in state.vocabulary.contents:
            raise Illegal(f"no such content: {content}")
        practical = state.vocabulary.is_practical(content)
        if kind == "undertake" and not practical:
            raise Illegal("undertake is for practical contents")
        if kind == "assert" and practical:
            raise Illegal("assert is for doxastic contents")
        return state.with_ack(mover, state.ack[mover] | {content})

    if kind == "disavow":
        # Removes an acknowledgment and nothing else. What other scorekeepers
        # attribute is recomputed from the new acknowledgments under their own
        # practices, which is where T1 comes from.
        return state.with_ack(mover, state.ack[mover] - {move.content})

    if kind == "query":
        # Putting the question publicly. This is what makes a latent
        # consequential commitment *due*: it writes an exposure, so the burden
        # becomes chargeable. Without this the label `reopen` would decode to a
        # move with no state effect at all.
        return replace(
            state, exposures=state.exposures | {(move.other, move.content)}
        )

    if kind == "challenge":
        # A challenge exposes what it challenges: raising it is one way of making
        # a consequence due.
        challenge = Challenge(mover, move.other, move.content, move.ground)
        return replace(
            state,
            challenges=state.challenges | {challenge},
            exposures=state.exposures | {(move.other, move.content)},
        )

    if kind == "vindicate":
        # Discharging a burden means displaying a justification the *challenger's*
        # practice recognises: an inference the challenger endorses, from premises
        # the challenger already takes the mover to be entitled to, to the content.
        # Where an undercutter has blocked one of those premises there is no such
        # display, and the burden stands — which is what makes the burden real
        # rather than automatically dischargeable.
        content = move.content
        challenger = move.other
        practice = state.practice[challenger]
        if content in state.blocked(challenger, mover):
            raise Illegal("the content is materially precluded, not merely queried")
        entitled = state.default_entitlements(challenger, mover)
        # Demonstrating *entitlement* requires an entitlement-preserving route.
        # A committive rule transmits commitment and settles nothing about title,
        # so it cannot vindicate.
        supported = content in entitled or any(
            premises <= entitled and conclusion == content
            for premises, conclusion in practice.permissive
        )
        if not supported:
            raise Illegal("no justification the challenger's practice recognises")
        return replace(state, vindications=state.vindications | {(mover, content)})

    if kind == "suspend":
        # Publicly suspending reliance on a content, without retracting
        # commitment to it. The commitment stays in force and stays attributable;
        # what stops is deployment of the content as an entitlement-bearing
        # premise. This is the disposition an undercut applicability claim calls
        # for, and it is not disavowal.
        return replace(
            state, suspensions=state.suspensions | {(mover, move.content)}
        )

    if kind == "defer":
        return replace(
            state, deferrals=state.deferrals | {(mover, move.other, move.content)}
        )

    if kind == "revise_committive":
        practice = state.practice[mover].with_committive(move.rule, move.present)
        return state.with_practice(mover, practice)

    if kind == "revise_permissive":
        practice = state.practice[mover].with_permissive(move.rule, move.present)
        return state.with_practice(mover, practice)

    if kind == "revise_incompatible":
        practice = state.practice[mover].with_incompatible(
            move.incompatible, move.present
        )
        return state.with_practice(mover, practice)

    if kind in ("grant", "revoke"):
        # Altering `holder`'s authority is itself a practical move, over the
        # reserved subject `authority:<holder>`. Asserting that one is authorized
        # is not on this branch at all — it is an `assert`, and it writes `ack`.
        holder = move.other
        required = authority_over(holder)
        if not state.has_authority(mover, required):
            raise Illegal(f"{mover} lacks authority over {required}")
        grant = Grant(holder, move.subject)
        grants = (
            state.grants | {grant} if kind == "grant" else state.grants - {grant}
        )
        return replace(state, grants=grants)

    if kind == "perform":
        content = move.content
        if not state.vocabulary.is_practical(content):
            raise Illegal("perform is for practical contents")
        if not state.may_perform(mover, content):
            raise Illegal(f"{mover} lacks authority over {content}")
        return replace(state, performed=state.performed + ((mover, content),))

    raise Illegal(f"no such move kind: {kind}")


def is_legal(state: State, move: Move) -> bool:
    try:
        apply_move(state, move)
    except Illegal:
        return False
    return True


def altered_coordinates(before: State, after: State) -> Tuple[str, ...]:
    """Which coordinates actually differ. The enumerations compare against this."""
    changed = []
    for name in COORDINATES:
        if getattr(before, name) != getattr(after, name):
            changed.append(name)
    return tuple(changed)


def altered_agents(before: State, after: State) -> Tuple[Agent, ...]:
    """Which agents' `ack` or `practice` differ."""
    changed = []
    for agent in before.agents:
        if before.ack[agent] != after.ack[agent] or (
            before.practice[agent] != after.practice[agent]
        ):
            changed.append(agent)
    return tuple(changed)
