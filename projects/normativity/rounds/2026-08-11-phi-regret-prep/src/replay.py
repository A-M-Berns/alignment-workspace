"""Replay semantics, the charge accounting, and resource feasibility.

Given an actual finite run and a comparator, `replay` produces the counterfactual
run the comparator would have produced. v1 is deliberately conservative, and the
conservatism is configurable rather than assumed so that the cost of each freeze
is measurable: `guard_on` chooses between actual-prefix and replayed-prefix
guards, and `filings` chooses between frozen and endogenous arrival of
occasions that an earlier disposition caused.

Three quantities stay apart throughout, and the report keeps them in separate
fields for that reason: whether an edit was **licensed** (the certificate),
whether the run was **affordable** (declared service work), and what it **cost**
(the charge accounting). Nothing here combines them.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as Q
from typing import Callable, Mapping, Sequence

from src.certificates import (
    ADMITTED,
    DEFAULT_POLICY,
    LawfulEditCertificate,
    PolicySuite,
    check,
)
from src.model import (
    BASIS_DECLINE,
    BASIS_MERITS,
    CERTIFIER_FOOTPRINT,
    GUARD_FOOTPRINT,
    Accounting,
    ActualHistory,
    LedgerEffect,
    Occasion,
    PrefixReader,
    Response,
    reader_at,
)

GUARD_ON_ACTUAL = "actual"
GUARD_ON_REPLAY = "replay"
FILINGS_FROZEN = "frozen"
FILINGS_ENDOGENOUS = "endogenous"

#: The response an account under suspension can give. Service is withdrawn, so
#: no merits ruling is available and nothing is tolled.
SUSPENDED_RESPONSE = Response(BASIS_DECLINE, None, 0, LedgerEffect())


Guard = Callable[[PrefixReader, Occasion, Response], bool]
Propose = Callable[[PrefixReader, Occasion, Response],
                   "tuple[Response, tuple[str, ...], str] | None"]


@dataclass(frozen=True)
class Comparator:
    """A conditional local edit rule.

    `guard` decides whether the rule applies at an occasion; `propose` supplies
    the replacement together with the grounds it cites and the authority it
    claims. Neither may read the charge table: both run under `GUARD_FOOTPRINT`,
    which does not declare it.
    """

    phi_id: str
    guard: Guard
    propose: Propose
    once: bool = False
    guard_on: str = GUARD_ON_ACTUAL
    description: str = ""


def identity_comparator() -> Comparator:
    return Comparator("phi:identity", lambda r, o, a: False,
                      lambda r, o, a: None,
                      description="the actual run, replayed")


@dataclass(frozen=True)
class OccasionOutcome:
    occasion_id: str
    date: int
    account: str
    response: Response
    charge: Q
    fired: bool
    verdict_status: str
    verdict_code: str
    suspended: bool


@dataclass(frozen=True)
class ReplayRun:
    run_id: str
    outcomes: tuple[OccasionOutcome, ...]
    total_charge: Q
    per_account: Mapping[str, Q]
    suspension_dates: Mapping[str, int]
    firings: tuple[str, ...]
    rejections: tuple[tuple[str, str], ...]
    feasible: bool
    overrun_dates: tuple[int, ...]

    @property
    def responses(self) -> Mapping[str, Response]:
        return {o.occasion_id: o.response for o in self.outcomes}

    def charge_at(self, occasion_id: str) -> Q:
        for outcome in self.outcomes:
            if outcome.occasion_id == occasion_id:
                return outcome.charge
        raise KeyError(occasion_id)

    @property
    def touched_accounts(self) -> tuple[str, ...]:
        return tuple(sorted({o.account for o in self.outcomes
                             if o.occasion_id in self.firings}))


def charge_of(occasion: Occasion, response: Response) -> Q:
    """The one interpretable charge quantity this test uses.

    Merits costs nothing; a scheduled default costs the frozen default tariff;
    a decline accrues the refusal tariff over the dates of the service window
    that are not tolled. Derived from the record, never supplied (`CD-J8`,
    `CD-J9`).

    An occasion whose own decision obligation has been struck from the record
    shows nothing owed and therefore accrues nothing. That is what makes burden
    laundering profitable, and it is why the charge rule has to be able to
    express it: an accounting in which erasure were free of consequence would
    make the corresponding certificate check untestable.
    """
    schedule = occasion.schedule
    if f"d:{occasion.occasion_id}" in response.ledger.drops:
        return Q(0)
    if response.basis == BASIS_MERITS:
        return Q(0)
    if response.basis == "default":
        return Q(schedule.default_tariff)
    dates = max(0, schedule.service_window - response.tolled)
    return Q(schedule.refusal_tariff) * dates


def _occasions_for(history: ActualHistory, decided: Mapping[str, Response],
                   mode: str) -> tuple[Occasion, ...]:
    live = list(history.base_occasions)
    for filing in history.filings:
        source = (history.responses if mode == FILINGS_FROZEN else decided)
        response = source.get(filing.trigger_occasion)
        if response is not None and response.basis == filing.fires_when_basis:
            live.extend(filing.occasions)
    return tuple(sorted(live, key=lambda o: (o.date, o.occasion_id)))


def replay(history: ActualHistory, comparator: Comparator, *,
           policy: PolicySuite = DEFAULT_POLICY,
           filings: str = FILINGS_FROZEN,
           run_id: str | None = None) -> ReplayRun:
    """Produce the counterfactual run, deterministically.

    One forward pass over dates. At each occasion the guard is evaluated on the
    declared prefix; if it fires, the proposed replacement is put to the
    certificate check, and only an `ADMITTED` verdict changes the response.
    Everything the edit does not touch is carried from the actual run unchanged.
    """
    decided: dict[str, Response] = {}
    outcomes: list[OccasionOutcome] = []
    balances: dict[str, Q] = {}
    suspended_from: dict[str, int] = {}
    firings: list[str] = []
    rejections: list[tuple[str, str]] = []
    work_by_date: dict[int, Q] = {}
    fired_once = False

    def settle_reserves(date: int) -> None:
        if not history.accounting.suspends:
            return
        for name, balance in balances.items():
            reserve = Q(history.accounting.reserves.get(name, 0))
            if balance > reserve and name not in suspended_from:
                suspended_from[name] = date

    current_date: int | None = None
    while True:
        occasions = _occasions_for(history, decided, filings)
        pending = [o for o in occasions if o.occasion_id not in decided]
        if not pending:
            break
        occasion = pending[0]
        if current_date is not None and occasion.date != current_date:
            settle_reserves(current_date)
        current_date = occasion.date
        account = history.accounting.account_of(occasion)
        stop = suspended_from.get(account)
        is_suspended = stop is not None and occasion.date > stop
        actual = history.responses.get(occasion.occasion_id)
        if actual is None:
            raise KeyError(f"no actual response for {occasion.occasion_id!r}")

        if is_suspended:
            response, status, code, fired = SUSPENDED_RESPONSE, "", "", False
        else:
            response, status, code, fired = actual, "", "", False
            if not (comparator.once and fired_once):
                source = (history.responses if comparator.guard_on == GUARD_ON_ACTUAL
                          else decided)
                view = reader_at(history, occasion.date, GUARD_FOOTPRINT,
                                 responses=source, occasions=occasions)
                if comparator.guard(view, occasion, actual):
                    proposal = comparator.propose(view, occasion, actual)
                    if proposal is not None:
                        replacement, grounds, authority = proposal
                        certificate = LawfulEditCertificate(
                            f"edit:{comparator.phi_id}:{occasion.occasion_id}",
                            occasion.occasion_id, occasion.date, actual,
                            replacement, tuple(grounds), authority)
                        certifier = reader_at(history, occasion.date,
                                              CERTIFIER_FOOTPRINT,
                                              responses=source,
                                              occasions=occasions)
                        verdict = check(certificate, certifier, policy=policy)
                        status, code = verdict.status, verdict.code
                        if verdict.status == ADMITTED:
                            response, fired, fired_once = replacement, True, True
                            firings.append(occasion.occasion_id)
                        else:
                            rejections.append((occasion.occasion_id, verdict.code))

        decided[occasion.occasion_id] = response
        amount = charge_of(occasion, response)
        balances[account] = balances.get(account, Q(0)) + amount
        work_by_date[occasion.date] = (work_by_date.get(occasion.date, Q(0))
                                       + history.costs.work_of(response))
        outcomes.append(OccasionOutcome(occasion.occasion_id, occasion.date, account,
                                        response, amount, fired, status, code,
                                        is_suspended))

    if current_date is not None:
        settle_reserves(current_date)

    overrun = tuple(sorted(d for d, used in work_by_date.items()
                           if used > Q(history.costs.per_date_work)))
    return ReplayRun(run_id or f"{history.history_id}|{comparator.phi_id}",
                     tuple(outcomes), sum((o.charge for o in outcomes), Q(0)),
                     dict(sorted(balances.items())), dict(sorted(suspended_from.items())),
                     tuple(firings), tuple(rejections), not overrun, overrun)


def actual_run(history: ActualHistory, *, policy: PolicySuite = DEFAULT_POLICY,
               filings: str = FILINGS_FROZEN) -> ReplayRun:
    """The actual history, produced by the same machinery as every replay.

    Using one code path for both is what makes the comparison meaningful: the
    actual and counterfactual losses are the same function of the same objects.
    """
    return replay(history, identity_comparator(), policy=policy, filings=filings,
                  run_id=f"{history.history_id}|actual")


def faithful(history: ActualHistory, run: ReplayRun) -> bool:
    """Whether replaying the identity reproduces the recorded responses.

    A history for which this fails is malformed — it records dispositions its own
    suspension rule would not have permitted — and no regret computed against it
    means anything.
    """
    for outcome in run.outcomes:
        if history.responses.get(outcome.occasion_id) != outcome.response:
            return False
    return True
