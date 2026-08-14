"""The relational scorekeeping state and its derived normative statuses.

The one equation the round turns on:

    commitments_i(j) = closure of Ack_j under I_i

What scorekeeper `i` attributes to agent `j` is the consequential closure of
`j`'s *public acknowledgments* under `i`'s *own* inferential practice. Nothing
in that expression is under `j`'s control except `Ack_j`. Revising `I_j` moves
what `j` attributes to itself and to everyone else, and moves nothing that any
other scorekeeper attributes to `j`.

Contents are opaque atoms. Practical contents carry a subject matter, which is
what scoped practical authority is scoped to.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Dict, FrozenSet, Iterable, Mapping, Tuple

Agent = str
Content = str
Subject = str

Rule = Tuple[FrozenSet[Content], Content]


# ---------------------------------------------------------------- vocabulary


@dataclass(frozen=True)
class Vocabulary:
    """Which contents exist, and which of them are practical.

    A practical content is one whose acknowledgment is a commitment to act. It
    carries the subject matter its performance falls under; authority to perform
    it is authority over that subject matter, not over the content.
    """

    contents: FrozenSet[Content]
    practical: Mapping[Content, Subject]

    def is_practical(self, c: Content) -> bool:
        return c in self.practical

    def subject_of(self, c: Content) -> Subject:
        return self.practical[c]


# ------------------------------------------------------------------ practice


@dataclass(frozen=True)
class Practice:
    """One agent's endorsed material inferential proprieties.

    `committive` rules preserve commitment: anyone committed to every premise is
    committed to the conclusion. `permissive` rules preserve entitlement:
    entitlement to every premise entitles to the conclusion without compelling
    it. `incompatible` holds unordered pairs: commitment to either member
    precludes entitlement to the other.
    """

    committive: FrozenSet[Rule] = frozenset()
    permissive: FrozenSet[Rule] = frozenset()
    incompatible: FrozenSet[FrozenSet[Content]] = frozenset()

    def with_committive(self, rule: Rule, present: bool) -> "Practice":
        rules = set(self.committive)
        rules.add(rule) if present else rules.discard(rule)
        return replace(self, committive=frozenset(rules))

    def with_permissive(self, rule: Rule, present: bool) -> "Practice":
        rules = set(self.permissive)
        rules.add(rule) if present else rules.discard(rule)
        return replace(self, permissive=frozenset(rules))

    def with_incompatible(self, pair: FrozenSet[Content], present: bool) -> "Practice":
        pairs = set(self.incompatible)
        pairs.add(pair) if present else pairs.discard(pair)
        return replace(self, incompatible=frozenset(pairs))


def rule(premises: Iterable[Content], conclusion: Content) -> Rule:
    return (frozenset(premises), conclusion)


def pair(a: Content, b: Content) -> FrozenSet[Content]:
    return frozenset((a, b))


# --------------------------------------------------------------- bookkeeping


@dataclass(frozen=True)
class Challenge:
    """A recorded challenge. Its normative force is not stored here.

    Whether this challenge does anything is `State.challenge_is_entitled`, read
    off the challenger's entitlement to a ground incompatible with the target,
    from the perspective doing the reading. The record is bookkeeping; the force
    is derived.
    """

    challenger: Agent
    target: Agent
    content: Content
    ground: Content


@dataclass(frozen=True)
class Grant:
    """Scoped practical authority: `holder` may perform moves over `subject`.

    Practical authority is a relation between an agent and a subject matter. It
    is not heritable the way testimonial authority is: holding it confers no
    power to confer it. Power to confer is itself a grant, over the reserved
    subject `AUTHORITY_OVER(holder)`.
    """

    holder: Agent
    subject: Subject


AUTHORITY = "authority"


def authority_over(holder: Agent) -> Subject:
    """The reserved subject matter of altering `holder`'s practical authority."""
    return f"{AUTHORITY}:{holder}"


# --------------------------------------------------------------------- state


@dataclass(frozen=True, eq=False)
class State:
    """The whole public scorekeeping position.

    `ack` is the public record of what each agent has acknowledged: assertions
    are public performances, so every scorekeeper reads the same one. The
    perspectival difference between scorekeepers comes entirely from `practice`,
    not from differing observation. That is deliberate — it is what makes the
    round's central attack sharp, because the attacked architecture's obstruction
    was that no predicate of a shared record separates two positions.
    """

    vocabulary: Vocabulary
    ack: Mapping[Agent, FrozenSet[Content]]
    practice: Mapping[Agent, Practice]
    grants: FrozenSet[Grant] = frozenset()
    challenges: FrozenSet[Challenge] = frozenset()
    vindications: FrozenSet[Tuple[Agent, Content]] = frozenset()
    deferrals: FrozenSet[Tuple[Agent, Agent, Content]] = frozenset()
    testimony_permitted: FrozenSet[Tuple[Agent, Content]] = frozenset()
    performed: Tuple[Tuple[Agent, Content], ...] = ()
    #: `(target, content)` pairs that have been publicly raised as requiring a
    #: response — by a query, a challenge, or a demand. What makes a latent
    #: consequential commitment into a burden that is *due*.
    exposures: FrozenSet[Tuple[Agent, Content]] = frozenset()
    #: `(agent, content)` pairs where the agent has publicly suspended reliance
    #: on the content without retracting commitment to it. Distinct from
    #: disavowal: the commitment stays in force and stays attributable.
    suspensions: FrozenSet[Tuple[Agent, Content]] = frozenset()

    # -- identity ----------------------------------------------------------

    def key(self) -> Tuple:
        """A canonical value. States are compared and hashed by it.

        The reachability enumerations put states in sets, so this is what decides
        when two positions count as the same one. Every coordinate is included:
        two positions differing anywhere are different states, which is what keeps
        "no advisor action produces this successor" from being won by an omission.
        """
        return (
            tuple(sorted(self.vocabulary.contents)),
            tuple(sorted(self.vocabulary.practical.items())),
            tuple(sorted((a, tuple(sorted(c))) for a, c in self.ack.items())),
            tuple(sorted(self.practice.items())),
            tuple(sorted((g.holder, g.subject) for g in self.grants)),
            tuple(
                sorted(
                    (c.challenger, c.target, c.content, c.ground)
                    for c in self.challenges
                )
            ),
            tuple(sorted(self.vindications)),
            tuple(sorted(self.deferrals)),
            tuple(sorted(self.testimony_permitted)),
            self.performed,
            tuple(sorted(self.exposures)),
            tuple(sorted(self.suspensions)),
        )

    def __eq__(self, other) -> bool:
        return isinstance(other, State) and self.key() == other.key()

    def __hash__(self) -> int:
        return hash(self.key())

    # -- agents ------------------------------------------------------------

    @property
    def agents(self) -> Tuple[Agent, ...]:
        return tuple(sorted(self.ack))

    # -- consequential commitment -----------------------------------------

    def commitments(self, scorekeeper: Agent, target: Agent) -> FrozenSet[Content]:
        """What `scorekeeper` attributes `target` to be committed to.

        The closure of the target's acknowledgments under the *scorekeeper's*
        committive rules. This is the round's load-bearing definition.
        """
        practice = self.practice[scorekeeper]
        current = set(self.ack[target])
        changed = True
        while changed:
            changed = False
            for premises, conclusion in practice.committive:
                if premises <= current and conclusion not in current:
                    current.add(conclusion)
                    changed = True
        return frozenset(current)

    def unacknowledged_consequences(
        self, scorekeeper: Agent, target: Agent
    ) -> FrozenSet[Content]:
        """Consequential commitments the target has not acknowledged."""
        return self.commitments(scorekeeper, target) - self.ack[target]

    # -- entitlement -------------------------------------------------------

    def blocked(self, scorekeeper: Agent, target: Agent) -> FrozenSet[Content]:
        """Contents whose entitlement is precluded by an attributed commitment.

        Commitment to either member of a materially incompatible pair precludes
        entitlement to the other. Blocking is computed from the commitments, so it
        does not depend on the entitlement closure and the closure below stays
        monotone.
        """
        practice = self.practice[scorekeeper]
        committed = self.commitments(scorekeeper, target)
        out = set()
        for incompatible_pair in practice.incompatible:
            first, second = tuple(sorted(incompatible_pair))
            if first in committed:
                out.add(second)
            if second in committed:
                out.add(first)
        return frozenset(out)

    def default_entitlements(
        self, scorekeeper: Agent, target: Agent, follow_deferrals: bool = True
    ) -> FrozenSet[Content]:
        """Entitlement before any challenge is weighed.

        The least set containing every acknowledgment, closed under the
        **permissive** rules and under permitted testimony, admitting nothing that
        is blocked or suspended. Because a blocked content never enters the set,
        nothing derived from it enters either: an undercutter defeats entitlement
        to the whole downstream, while leaving every commitment along it in force.

        Committive rules do **not** appear here. Commitment-preserving and
        entitlement-preserving inference are separate relations, and a pattern
        that transmits both is declared in both. That separation is what makes an
        unentitled commitment — committed, never entitled, not precluded — a state
        the model can express.
        """
        practice = self.practice[scorekeeper]
        blocked = self.blocked(scorekeeper, target)
        suspended = {c for a, c in self.suspensions if a == target}
        rules = practice.permissive
        entitled = {
            c
            for c in self.ack[target]
            if c not in blocked and c not in suspended
        }

        changed = True
        while changed:
            changed = False
            for premises, conclusion in rules:
                if conclusion in entitled or conclusion in blocked:
                    continue
                if conclusion in suspended:
                    continue
                if premises <= entitled:
                    entitled.add(conclusion)
                    changed = True
            if not follow_deferrals:
                continue
            for deferrer, source, content in self.deferrals:
                if deferrer != target or content in entitled or content in blocked:
                    continue
                if (source, content) not in self.testimony_permitted:
                    continue
                # Testimonial paths are not chained: the source's own entitlement
                # is read without deferral, which is the finite form of refusing
                # to let self-citation originate entitlement.
                if content in self.default_entitlements(
                    scorekeeper, source, follow_deferrals=False
                ):
                    entitled.add(content)
                    changed = True
        return frozenset(entitled)

    def challenge_is_entitled(self, scorekeeper: Agent, challenge: Challenge) -> bool:
        """Whether `scorekeeper` takes the challenge to have force.

        A challenge has force when the challenger is entitled to a ground that is
        materially incompatible with the challenged content — commitment to the
        ground precludes entitlement to the target. The challenger's own standing
        is read at default level: challenges do not challenge each other in this
        model, which is a declared stratification rather than a claim about
        Brandom's practice.
        """
        practice = self.practice[scorekeeper]
        if pair(challenge.ground, challenge.content) not in practice.incompatible:
            return False
        grounds = self.default_entitlements(scorekeeper, challenge.challenger)
        return challenge.ground in grounds

    def live_challenges(
        self, scorekeeper: Agent, target: Agent
    ) -> FrozenSet[Challenge]:
        """Entitled, unvindicated challenges against a commitment still in force.

        A challenge lapses when the target is no longer committed to what was
        challenged. Retracting the basis is a recognised disposition and clears
        the burden; retracting only the acknowledgment does not, because the
        commitment survives by closure. That difference is T1.
        """
        committed = self.commitments(scorekeeper, target)
        return frozenset(
            c
            for c in self.challenges
            if c.target == target
            and c.content in committed
            and self.challenge_is_entitled(scorekeeper, c)
            and (target, c.content) not in self.vindications
        )

    def entitlements(self, scorekeeper: Agent, target: Agent) -> FrozenSet[Content]:
        """Entitlement after live challenges are subtracted."""
        entitled = set(self.default_entitlements(scorekeeper, target))
        for challenge in self.live_challenges(scorekeeper, target):
            entitled.discard(challenge.content)
        return frozenset(entitled)

    def precluded_commitments(
        self, scorekeeper: Agent, target: Agent
    ) -> FrozenSet[Content]:
        """Commitments whose entitlement is *precluded*, and not yet suspended.

        Narrower than "committed and not entitled". A commitment that was simply
        never entitled — reached by a committive rule with no permissive
        counterpart — is not a defect; it is an ordinary consequence awaiting a
        demand. What is a defect is holding a commitment while also holding
        something materially incompatible with it.

        A suspension discounts the charge, but only where this scorekeeper takes
        the content to be blocked. Suspending what the scorekeeper does not
        regard as undercut buys nothing, so the discount cannot be self-awarded.
        """
        suspended = {c for a, c in self.suspensions if a == target}
        return frozenset(
            c
            for c in self.commitments(scorekeeper, target)
            & self.blocked(scorekeeper, target)
            if c not in suspended
        )

    def unentitled_commitments(
        self, scorekeeper: Agent, target: Agent
    ) -> FrozenSet[Content]:
        """Committed and not entitled. A diagnostic, not a loss term."""
        return self.commitments(scorekeeper, target) - self.entitlements(
            scorekeeper, target
        )

    def is_exposed(self, target: Agent, content: Content) -> bool:
        return (target, content) in self.exposures

    def exposed_unacknowledged(
        self, scorekeeper: Agent, target: Agent
    ) -> FrozenSet[Content]:
        """Consequential commitments that are due: publicly raised, not acknowledged.

        Consequential closure alone is not a debt. Attributing every consequence
        of what someone has said is what a scorekeeper does; requiring them to
        have acknowledged all of it would be a logical-omniscience norm. What
        makes a consequence chargeable is that someone has raised it.
        """
        return frozenset(
            c
            for c in self.unacknowledged_consequences(scorekeeper, target)
            if self.is_exposed(target, c)
        )

    # -- practical authority ----------------------------------------------

    def has_authority(self, holder: Agent, subject: Subject) -> bool:
        return Grant(holder, subject) in self.grants

    def may_perform(self, agent: Agent, content: Content) -> bool:
        """Whether the practice licenses `agent` to perform a practical content.

        Read off the grant relation, not off anything the agent has asserted.
        """
        if not self.vocabulary.is_practical(content):
            return False
        return self.has_authority(agent, self.vocabulary.subject_of(content))

    def unsupported_practical(
        self, scorekeeper: Agent, target: Agent
    ) -> FrozenSet[Content]:
        """Practical commitments the target holds without authority to act on."""
        return frozenset(
            c
            for c in self.commitments(scorekeeper, target)
            if self.vocabulary.is_practical(c) and not self.may_perform(target, c)
        )

    # -- edits -------------------------------------------------------------

    def with_ack(self, agent: Agent, contents: FrozenSet[Content]) -> "State":
        ack = dict(self.ack)
        ack[agent] = contents
        return replace(self, ack=ack)

    def with_practice(self, agent: Agent, practice: Practice) -> "State":
        practices = dict(self.practice)
        practices[agent] = practice
        return replace(self, practice=practices)
