"""Recognition, reciprocal answerability, and what they do not buy.

The dispatch asks whether a local anti-usurpation comparison can be derived from
a thin enough reciprocal-answerability predicate, and asks for the derivation to
be prosecuted for circularity. The answer this module supports is in three parts.

**The scope is derivable, and that is the thin part.** A liability needs a scope
— what the debtor owes an account *for* — and stipulating "the principal's choice"
is stipulating standing. Here the scope is read off `A`'s own conduct: a conduct
whose implementation table is indexed by the choice is a conduct that treats the
choice as the other party's contribution, and reciprocity turns being held
answerable into owing an account. `reciprocal_scope` computes it. A conduct whose
implementation ignores the choice generates no scope, and then usurpation is not
statable — which is a limit and is reported as one.

**The liability opens.** With that scope, a conduct whose channel is not the
identity changes the relation within it, the trigger fires, and no operation
available to `A` closes it: `discharge` refuses a debtor discharging itself, and
removing the claimant leaves the liability live.

**The liability does not decide anything.** `model.value` does not read the
ledger, and cannot be made to without becoming the authority bonus this round is
forbidden to pay. So the step from a live undefeated liability to a non-preferred
conduct is a further primitive. It is taken here as a **constraint on the
admissible set** rather than as a term in the objective, and the round's one
quantitative claim about it is `price_of_the_norm`: obeying the constraint costs
at most what `repair.py` bounds.

Provisional names: `Liability`, `Ledger`, `reciprocal_scope`,
`agency_recognition`, `reciprocal_answerability`, `recognizes`,
`relation_change`, `opens_a_liability`, `answerable_admissible`,
`price_of_the_norm`.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction
from typing import FrozenSet, Iterable, Mapping, Sequence

from model import (Conduct, Episode, identity_channel, mediated, realized_quantity,
                   response_map, value)

LIVE = "live"
ANSWERED = "answered"
DISCHARGED = "discharged"


@dataclass(frozen=True)
class Liability:
    claimant: str
    debtor: str
    scope: str
    trigger: str
    basis: str
    status: str = LIVE


@dataclass(frozen=True)
class Ledger:
    entries: FrozenSet[Liability] = frozenset()
    population: FrozenSet[str] = frozenset()

    def live(self) -> tuple[Liability, ...]:
        return tuple(sorted((e for e in self.entries if e.status != DISCHARGED),
                            key=lambda e: (e.claimant, e.debtor, e.scope)))

    def open(self, liability: Liability) -> "Ledger":
        return replace(self, entries=self.entries | {liability})

    def answer(self, liability: Liability, basis: str) -> "Ledger":
        """An answer is an answer. It does not close the liability."""
        if liability not in self.entries:
            raise KeyError("no such liability")
        answered = replace(liability, status=ANSWERED, basis=basis)
        return replace(self, entries=(self.entries - {liability}) | {answered})

    def discharge(self, liability: Liability, by: str) -> "Ledger":
        """Licensed discharge. **A debtor cannot release itself.**

        The rule is structural rather than a policy: it is what makes the
        liability an object of a *relation* instead of a note the debtor keeps.
        """
        if liability not in self.entries:
            raise KeyError("no such liability")
        if by == liability.debtor:
            raise PermissionError("unilateral self-release")
        if by != liability.claimant:
            raise PermissionError("discharge by a third party")
        closed = replace(liability, status=DISCHARGED)
        return replace(self, entries=(self.entries - {liability}) | {closed})

    def remove(self, agent: str) -> "Ledger":
        """Delete an agent from the population, leaving the ledger alone.

        The clause that makes answerability reciprocal rather than a convenience:
        the account is not discharged by removing the party owed it.
        """
        return replace(self, population=self.population - {agent})

    def transport(self, renaming: Mapping[str, str]) -> "Ledger":
        """Carry the ledger through a change of who occupies a role."""
        moved = frozenset(
            replace(e, claimant=renaming.get(e.claimant, e.claimant),
                    debtor=renaming.get(e.debtor, e.debtor))
            for e in self.entries)
        return Ledger(moved, frozenset(renaming.get(a, a) for a in self.population))


# --------------------------------------------------------------------------
# Recognition
# --------------------------------------------------------------------------

def agency_recognition(episode: Episode, admissible: Sequence[Conduct]) -> bool:
    """`A`'s own conduct space distinguishes conducts that realize identically.

    The thinnest form of "the principal is a distinct locus of choice" the round
    could find that is not a stipulation: `A`'s representation is not the quotient
    by realized behaviour. Two admissible conducts producing the same quantity at
    every state and answering an intervention on the choice differently is exactly
    the separation `selector.prediction_is_not_control` reports.
    """
    for index, first in enumerate(admissible):
        for second in admissible[index + 1:]:
            realizes_alike = all(
                realized_quantity(episode, first, state)
                == realized_quantity(episode, second, state)
                for state in episode.states)
            if realizes_alike and (response_map(episode, first)
                                   != response_map(episode, second)):
                return True
    return False


def reciprocal_scope(episode: Episode, conduct: Conduct) -> frozenset[str]:
    """What `A`'s own conduct treats as the other party's contribution.

    A conduct whose implementation varies with the choice is one that holds the
    choice responsible for how the episode goes. Reciprocity is the claim that
    holding a party answerable for a coordinate is owing that party an account
    for changes to it, so the scope is derived rather than named.

    Empty for a conduct that ignores the choice — which is the honest limit:
    against such a conduct usurpation of the choice is not a relation change at
    all, and this route says nothing.
    """
    for cell in episode.cells:
        actions = {conduct.implement[(cell, d)] for d in episode.choices}
        if len(actions) >= 2:
            return frozenset({"choice"})
    return frozenset()


def reciprocal_answerability(ledger: Ledger, advisor: str, principal: str,
                             scope: str) -> bool:
    """Three conditions, each checked by trying to break it.

    There is a liability in the scope with `A` as debtor; `A` cannot discharge
    it; and removing the principal does not close it.
    """
    candidates = [e for e in ledger.entries
                  if e.debtor == advisor and e.claimant == principal
                  and e.scope == scope]
    if not candidates:
        return False
    liability = candidates[0]
    try:
        ledger.discharge(liability, by=advisor)
        return False
    except PermissionError:
        pass
    return bool(ledger.remove(principal).live())


def recognizes(episode: Episode, admissible: Sequence[Conduct], ledger: Ledger,
               advisor: str, principal: str, scope: str) -> bool:
    return (agency_recognition(episode, admissible)
            and reciprocal_answerability(ledger, advisor, principal, scope))


# --------------------------------------------------------------------------
# The trigger, stated without naming usurpation
# --------------------------------------------------------------------------

def relation_change(episode: Episode, baseline: Conduct, conduct: Conduct,
                    scope: frozenset[str]) -> bool:
    """Whether the conduct changes, within the scope, what the standing relation
    made of the claimant's choice.

    The scope restricts the comparison to the choice argument. Two conducts
    differing only in which action they take at the same realized choice do not
    trigger; a conduct that changes which choice the world sees does.
    """
    if "choice" not in scope:
        return False
    return any(response_map(episode, baseline)[key][1]
               != response_map(episode, conduct)[key][1]
               for key in response_map(episode, baseline))


def opens_a_liability(episode: Episode, baseline: Conduct, conduct: Conduct,
                      ledger: Ledger, advisor: str, principal: str) -> Ledger:
    """The scope is read off the **standing** relation, not off the candidate.

    Reading it off the candidate would let a conduct escape the account by
    ceasing to read the principal's choice, and the escape route is the point:
    it exists either way and is reported in `RECOGNITION_AND_ANSWERABILITY.md`
    §4. Reading the baseline at least makes it a change to the standing relation
    rather than a private redefinition of the scope.
    """
    scope = reciprocal_scope(episode, baseline)
    if not relation_change(episode, baseline, conduct, scope):
        return ledger
    return ledger.open(Liability(principal, advisor, "choice",
                                 "relation-change", "unanswered"))


def leaves_a_live_liability(episode: Episode, baseline: Conduct,
                            conduct: Conduct, ledger: Ledger, advisor: str,
                            principal: str) -> bool:
    return bool(opens_a_liability(episode, baseline, conduct, ledger,
                                  advisor, principal).live())


# --------------------------------------------------------------------------
# The residual primitive, as a constraint rather than a bonus
# --------------------------------------------------------------------------

def answerable_admissible(episode: Episode, baseline: Conduct,
                          competitors: Sequence[Conduct], ledger: Ledger,
                          advisor: str, principal: str) -> list[Conduct]:
    """The competitors that leave no live undefeated liability.

    A constraint on the set, not a term in `value`. The difference is not
    cosmetic: a bonus large enough to make delegation win is a way of asserting
    the conclusion, and a constraint has a price that can be computed.
    """
    return [c for c in competitors
            if not leaves_a_live_liability(episode, baseline, c, ledger,
                                           advisor, principal)]


def price_of_the_norm(episode: Episode, baseline: Conduct,
                      competitors: Sequence[Conduct], ledger: Ledger,
                      advisor: str, principal: str) -> Fraction:
    """What obeying the constraint costs, in the ordinary register.

    The round's one quantitative statement about the normative side: with the
    competitor class restricted to the acceleration conducts and no foreclosing
    preparation admissible, this is bounded by `repair.bound`.
    """
    allowed = answerable_admissible(episode, baseline, competitors, ledger,
                                    advisor, principal)
    if not allowed:
        raise ValueError("the constraint is unsatisfiable on this class")
    return (max(value(episode, c) for c in competitors)
            - max(value(episode, c) for c in allowed))


def initial_ledger(advisor: str = "A", principal: str = "H") -> Ledger:
    return Ledger(frozenset(), frozenset({advisor, principal}))
