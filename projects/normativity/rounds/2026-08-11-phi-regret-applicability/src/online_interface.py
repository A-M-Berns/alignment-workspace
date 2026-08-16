"""Causal action-map and changing-action-set adapters for item 29.

This module does not implement a regret learner.  It exposes the object that a
Blum--Mansour modification-rule algorithm would consume and checks the two
encodings used in the applicability note.  Arithmetic in the helpers is exact.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction as Q
from typing import Hashable, Mapping, Sequence, TypeVar

from src.certificates import ADMITTED, DEFAULT_POLICY, LawfulEditCertificate, PolicySuite, check
from src.model import (
    BASIS_DECLINE,
    BASIS_DEFAULT,
    BASIS_MERITS,
    CERTIFIER_FOOTPRINT,
    GUARD_FOOTPRINT,
    ActualHistory,
    Accounting,
    Occasion,
    PrefixReader,
    Response,
    ServiceCosts,
    response_for,
)
from src.replay import Comparator, charge_of


class PreActionReader(PrefixReader):
    """A date-t reader that exposes reasons and the occasion, but only responses < t.

    The preparation reader uses ``<= t`` for every table.  That is correct for
    historical replay but lets a guard read the transcript's date-t response.
    An online modification rule must instead receive the candidate action as its
    explicit argument, before that action has been selected.
    """

    def response(self, occasion_id: str) -> Response | None:
        self._read("responses")  # noqa: SLF001 -- enforcing a narrower view
        occasion = next((o for o in self._occasions  # noqa: SLF001
                         if o.occasion_id == occasion_id), None)
        if occasion is None or occasion.date >= self.date:
            return None
        return self._responses.get(occasion_id)  # noqa: SLF001


def sealed_legality_state(history: ActualHistory, date: int) -> ActualHistory:
    """Remove future and profitability data before arbitrary rule code runs.

    The preparation footprint omitted a virtual ``charges`` table but still
    exposed schedule tariffs, account names, and the complete history through
    the reader object.  Since charge is derived from those tariffs, omission of
    the table did not enforce the advertised independence.  This adapter makes
    the theorem-facing boundary extensional: rule code receives no actual
    tariff, account, future response, or future reason record.
    """
    occasions = []
    for occasion in history.actual_occasions():
        if occasion.date > date:
            continue
        schedule = replace(occasion.schedule, default_tariff=Q(0),
                           refusal_tariff=Q(0))
        occasions.append(replace(occasion, account="legality:hidden",
                                 schedule=schedule))
    reasons = []
    for reason in history.reasons:
        if reason.filed_at > date:
            continue
        defeated = reason.defeated_at if reason.defeated_at is not None and reason.defeated_at <= date else None
        suspended = reason.suspended_at if reason.suspended_at is not None and reason.suspended_at <= date else None
        reasons.append(replace(reason, defeated_at=defeated,
                               suspended_at=suspended))
    responses = {}
    by_id = {o.occasion_id: o for o in history.actual_occasions()}
    for identifier, response in history.responses.items():
        occasion = by_id.get(identifier)
        if occasion is not None and occasion.date < date:
            responses[identifier] = response
    obligations = tuple(o for o in history.obligations if o.filed_at <= date)
    return ActualHistory(
        f"{history.history_id}|legality@{date}", date + 1, tuple(occasions),
        responses, tuple(reasons), obligations,
        ServiceCosts(Q(0), Q(0), Q(0), Q(0)),
        Accounting({}, suspends=False), ())


def available_actions(occasion: Occasion) -> tuple[Response, ...]:
    """The schedule-relative response set declared by the preparation spec."""
    schedule = occasion.schedule
    actions = [
        response_for(occasion, BASIS_MERITS, verdict=schedule.positive_verdict),
        response_for(occasion, BASIS_MERITS, verdict=schedule.negative_verdict),
        response_for(occasion, BASIS_DEFAULT),
    ]
    actions.extend(response_for(occasion, BASIS_DECLINE, tolled=k)
                   for k in range(schedule.service_window + 1))
    return tuple(actions)


def induced_action_map(history: ActualHistory, occasion: Occasion,
                       comparator: Comparator, actions: Sequence[Response], *,
                       policy: PolicySuite = DEFAULT_POLICY,
                       fired_before: bool = False) -> Mapping[Response, Response]:
    """Compile a fixed comparator program into its causal date-t map A_t -> A_t.

    Admission is recomputed for every candidate input.  Rejection and an absent
    proposal are identity.  Closure is checked rather than supplied by padding.
    """
    action_set = frozenset(actions)
    result: dict[Response, Response] = {}
    legal_history = sealed_legality_state(history, occasion.date)
    occasions = legal_history.actual_occasions()
    legal_occasion = next(o for o in occasions
                          if o.occasion_id == occasion.occasion_id)
    for candidate in actions:
        if comparator.once and fired_before:
            result[candidate] = candidate
            continue
        guard_reader = PreActionReader(legal_history, occasion.date, GUARD_FOOTPRINT,
                                       responses=legal_history.responses,
                                       occasions=occasions)
        if not comparator.guard(guard_reader, legal_occasion, candidate):
            result[candidate] = candidate
            continue
        proposal = comparator.propose(guard_reader, legal_occasion, candidate)
        if proposal is None:
            result[candidate] = candidate
            continue
        replacement, grounds, authority = proposal
        if replacement not in action_set:
            raise ValueError("comparator replacement is unavailable at this occasion")
        certificate = LawfulEditCertificate(
            f"online:{comparator.phi_id}:{occasion.occasion_id}",
            occasion.occasion_id, occasion.date, candidate, replacement,
            tuple(grounds), authority)
        certifier = PreActionReader(legal_history, occasion.date, CERTIFIER_FOOTPRINT,
                                    responses=legal_history.responses,
                                    occasions=occasions)
        verdict = check(certificate, certifier, policy=policy)
        result[candidate] = replacement if verdict.status == ADMITTED else candidate
    return result


A = TypeVar("A", bound=Hashable)


@dataclass(frozen=True)
class PaddedRound:
    """A finite-union encoding of one changing-action-set round."""

    actions: tuple[A, ...]
    available: frozenset[A]
    retract: Mapping[A, A]
    loss: Mapping[A, Q]

    def validate(self) -> None:
        if not self.available:
            raise ValueError("the available set must be inhabited")
        if set(self.retract) != set(self.actions):
            raise ValueError("the retraction must be total on the union")
        if any(self.retract[a] not in self.available for a in self.actions):
            raise ValueError("the retraction must land in the available set")
        if any(self.retract[a] != a for a in self.available):
            raise ValueError("the retraction must fix available actions")

    def padded_loss(self, action: A) -> Q:
        return Q(self.loss[self.retract[action]])

    def compile_map(self, local_map: Mapping[A, A]) -> Mapping[A, A]:
        self.validate()
        if set(local_map) != set(self.available):
            raise ValueError("the local map must be total on the available set")
        if any(local_map[a] not in self.available for a in self.available):
            raise ValueError("the local map must close on the available set")
        return {a: local_map[self.retract[a]] for a in self.actions}


def expected_loss(distribution: Mapping[A, Q], loss: Mapping[A, Q]) -> Q:
    return sum((Q(distribution.get(a, 0)) * Q(value)
                for a, value in loss.items()), Q(0))


def pushforward(distribution: Mapping[A, Q], transform: Mapping[A, A]) -> Mapping[A, Q]:
    out: dict[A, Q] = {}
    for action, mass in distribution.items():
        target = transform[action]
        out[target] = out.get(target, Q(0)) + Q(mass)
    return out


def matrix_push(distribution: Mapping[A, Q],
                rows: Mapping[A, Mapping[A, Q]]) -> Mapping[A, Q]:
    out: dict[A, Q] = {}
    for source, mass in distribution.items():
        for target, probability in rows[source].items():
            out[target] = out.get(target, Q(0)) + Q(mass) * Q(probability)
    return out


def stationary_support_is_available(padded: PaddedRound,
                                    distribution: Mapping[A, Q],
                                    rows: Mapping[A, Mapping[A, Q]]) -> bool:
    """Check the support step in the padding proof on exact finite data."""
    padded.validate()
    pushed = matrix_push(distribution, rows)
    if any(Q(pushed.get(a, 0)) != Q(distribution.get(a, 0))
           for a in padded.actions):
        raise ValueError("the supplied distribution is not stationary")
    if any(target not in padded.available and probability
           for row in rows.values() for target, probability in row.items()):
        raise ValueError("a transition leaves the available set")
    return all(Q(distribution.get(a, 0)) == 0
               for a in padded.actions if a not in padded.available)


def charge_vector(occasion: Occasion, actions: Sequence[Response]) -> Mapping[Response, Q]:
    return {action: charge_of(occasion, action) for action in actions}
