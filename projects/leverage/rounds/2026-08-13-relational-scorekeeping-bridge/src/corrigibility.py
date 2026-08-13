"""The corrigibility face: standing, scope, and protected effective access.

The bar this has to clear is the one the deference line's adversarial review set,
and it is set against that line's own failure — an advisor whose action coordinate
strictly contained the principal's, and a capability predicate that quantified the
advisor existentially, so that "the principal can correct" meant only "some
advisor action lets it".

    1. at least one principal corrective effect is reproducible by no advisor action;
    2. future corrective capability is robust to *every* advisor policy.

Both are decided here by enumeration over the advisor's whole move set, and both
turn on structure rather than on a field. The two structural facts are:

    undertaking is agent-indexed  — no agent has a move writing another's
                                    acknowledgments or another's practice;
    authority is scoped           — altering an agent's grants is itself a
                                    practical move over a reserved subject, and
                                    the advisor holds no grant over any of them.

`advisor_moves` is the enumeration the theorems quantify over, and it is
generated from the grammar rather than declared, so a move added to the grammar
without a matching authority precondition would show up here as a refutation.
"""
from __future__ import annotations

from dataclasses import replace
from typing import FrozenSet, Iterable, List, Sequence, Set, Tuple

from moves import Illegal, Move, apply_move, is_legal
from scorekeeping import (
    Agent,
    Content,
    Grant,
    State,
    Subject,
    authority_over,
    pair,
)


def all_moves(state: State, mover: Agent) -> List[Move]:
    """Every move of the grammar this agent could attempt, legal or not.

    Generated from the vocabulary and the population, not listed by hand. The
    enumerations below filter to the legal ones; keeping the illegal ones in the
    generator is what makes "the advisor cannot do this" a fact about the
    preconditions rather than about what someone remembered to write down.
    """
    moves: List[Move] = []
    contents = sorted(state.vocabulary.contents)
    others = [a for a in state.agents if a != mover]
    subjects = sorted(
        {state.vocabulary.subject_of(c) for c in state.vocabulary.practical}
        | {authority_over(a) for a in state.agents}
    )

    for content in contents:
        practical = state.vocabulary.is_practical(content)
        moves.append(Move("undertake" if practical else "assert", mover, content=content))
        moves.append(Move("disavow", mover, content=content))
        moves.append(Move("suspend", mover, content=content))
        if practical:
            moves.append(Move("perform", mover, content=content))
        for other in others:
            moves.append(Move("query", mover, content=content, other=other))
            moves.append(Move("defer", mover, content=content, other=other))
            moves.append(Move("vindicate", mover, content=content, other=other))
            for ground in contents:
                moves.append(
                    Move("challenge", mover, content=content, other=other, ground=ground)
                )

    for rule in sorted(
        {r for a in state.agents for r in state.practice[a].committive},
        key=lambda r: (r[1], sorted(r[0])),
    ):
        for present in (True, False):
            moves.append(
                Move("revise_committive", mover, rule=rule, present=present)
            )
    for rule in sorted(
        {r for a in state.agents for r in state.practice[a].permissive},
        key=lambda r: (r[1], sorted(r[0])),
    ):
        for present in (True, False):
            moves.append(
                Move("revise_permissive", mover, rule=rule, present=present)
            )
    for incompatible in sorted(
        {i for a in state.agents for i in state.practice[a].incompatible},
        key=sorted,
    ):
        for present in (True, False):
            moves.append(
                Move("revise_incompatible", mover, incompatible=incompatible, present=present)
            )

    for holder in state.agents:
        for subject in subjects:
            for kind in ("grant", "revoke"):
                moves.append(Move(kind, mover, other=holder, subject=subject))

    return moves


def legal_moves(state: State, mover: Agent) -> List[Move]:
    return [m for m in all_moves(state, mover) if is_legal(state, m)]


def successors(state: State, mover: Agent) -> List[Tuple[Move, State]]:
    out = []
    for move in legal_moves(state, mover):
        try:
            out.append((move, apply_move(state, move)))
        except Illegal:  # pragma: no cover - filtered above
            continue
    return out


# ------------------------------------------------ principal-exclusive effect


def principal_exclusive_effects(
    state: State, principal: Agent, advisor: Agent
) -> List[Move]:
    """Principal moves whose successor state no legal advisor move produces.

    Quantified over the advisor's entire legal move set at the same state. This is
    the first of the review's two requirements, and it is the one the predecessor
    could not meet: there, every principal successor was reproducible.
    """
    advisor_successors = {s for _, s in successors(state, advisor)}
    out = []
    for move, after in successors(state, principal):
        if after == state:
            continue
        if after not in advisor_successors:
            out.append(move)
    return out


def advisor_can_reproduce(
    state: State, principal: Agent, advisor: Agent, move: Move
) -> bool:
    after = apply_move(state, move)
    return any(s == after for _, s in successors(state, advisor))


# ------------------------------------------- advisor-robust future capability


def corrective_capability(state: State, principal: Agent, subject: Subject) -> bool:
    """Whether the principal presently holds the authority a correction needs.

    A predicate over the grant relation, read by `apply_move`'s precondition. It is
    not an inert bit: removing the grant makes the corrective move raise, and the
    enumerations below are what show the difference is visible in the transition.
    """
    return state.has_authority(principal, subject)


def advisor_can_alter_grants(state: State, advisor: Agent) -> bool:
    """Whether any grant or revoke by the advisor has its precondition met.

    The precondition of `grant` and `revoke` reads the grant relation and nothing
    else, so this predicate is a function of the grant relation alone. That is
    what makes the induction below exact rather than depth-limited: if the advisor
    cannot alter the grants here, the grants are unchanged after any advisor move,
    so the same predicate is false at the successor, and so on without bound.
    """
    return any(
        state.has_authority(advisor, authority_over(holder)) for holder in state.agents
    )


def capability_survives_every_advisor_policy(
    state: State, principal: Agent, advisor: Agent, subject: Subject
) -> bool:
    """The review's second requirement, quantified universally and without a horizon.

    The predecessor's capability predicate quantified the advisor existentially, so
    "the principal can correct" meant "some advisor action lets it". Here the claim
    is that *no* advisor run of *any* length removes the capability, and it is
    established by an invariant rather than by search:

        the capability is a predicate of the grant relation;
        the grant relation is altered only by `grant` and `revoke`;
        their precondition is a predicate of the grant relation;
        the advisor's fails here, so the grant relation is fixed along every
        advisor run, and with it the capability.

    `reachable_under_advisor` cross-checks the conclusion by brute force on a
    restricted move set, so the argument is verified and not merely stated.
    """
    return corrective_capability(state, principal, subject) and not (
        advisor_can_alter_grants(state, advisor)
    )


def reachable_under_advisor(
    state: State, advisor: Agent, depth: int, budget: int = 20000
) -> Set[State]:
    """Every state the advisor alone reaches within `depth` moves.

    Exponential in the branching factor, so it exists to cross-check the invariant
    above on small cases rather than to decide anything. Raises rather than
    truncating if the budget is exhausted: a search that silently stopped early
    would report the invariant as holding on a set it never finished exploring.
    """
    frontier = {state}
    seen = {state}
    for _ in range(depth):
        following: Set[State] = set()
        for current in frontier:
            for _, after in successors(current, advisor):
                if after not in seen:
                    seen.add(after)
                    following.add(after)
                    if len(seen) > budget:
                        raise RuntimeError("reachability budget exhausted")
        frontier = following
        if not frontier:
            break
    return seen


def grant_moves_only(state: State, mover: Agent) -> List[Move]:
    """The advisor's authority-altering moves, for the bounded cross-check.

    Restricting the enumeration is sound for the question it is asked: the
    invariant is about the grant relation, and these are the only moves that write
    it. `test_corrigibility` checks that claim over the whole grammar separately.
    """
    subjects = sorted(
        {state.vocabulary.subject_of(c) for c in state.vocabulary.practical}
        | {authority_over(a) for a in state.agents}
    )
    return [
        Move(kind, mover, other=holder, subject=subject)
        for holder in state.agents
        for subject in subjects
        for kind in ("grant", "revoke")
    ]


# ------------------------------------------------------ standing and access


def has_normative_standing(
    state: State, principal: Agent, target: Agent, content: Content, ground: Content
) -> bool:
    """Whether the practice gives the principal a challenge with force here.

    Standing is derived, not stored: the principal must be entitled — from the
    target's own scorekeeping perspective — to a ground materially incompatible
    with the content. There is no standing bit to set.
    """
    from scorekeeping import Challenge

    challenge = Challenge(principal, target, content, ground)
    return state.challenge_is_entitled(target, challenge)


def has_effective_access(
    state: State, principal: Agent, advisor: Agent, subject: Subject
) -> bool:
    """Whether the principal's corrective move stays available under every advisor run."""
    return capability_survives_every_advisor_policy(state, principal, advisor, subject)


def real_answerability(
    state: State,
    principal: Agent,
    advisor: Agent,
    content: Content,
    ground: Content,
    subject: Subject,
) -> bool:
    """The provisional combined predicate: standing *and* protected effective access.

    Both conjuncts, prosecuted for independence in `test_corrigibility`. Neither
    implies the other, and each has a witness where it holds alone.
    """
    return has_normative_standing(
        state, principal, advisor, content, ground
    ) and has_effective_access(state, principal, advisor, subject)
