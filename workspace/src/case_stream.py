"""The case stream: arrivals, admission, capacity, and the liability accounting.

The target is the demand result: **persistent substantive silence is not
cost-free**.  Everything here is an accounting identity over exact rationals.
Nothing is an incentive, optimization, or learning claim: the results say what
the record must show, never what anyone will do.

Finiteness discipline.  Dates run over an unbounded but finitely-realized
horizon, as books already do.  LIVE state is finite at every date: the language
and schema set are fixed and finite; the intake queue is finite; the set of OPEN
obligations is finite at every date, enforced by admission (a query accrues
nothing before it is admitted, and at most `admission_capacity` queries are
admitted per date).  Accumulated liability is a finite exact rational at every
date.  No structure grows except the append-only record.

Per decision D3 admission is an intake queue with per-date capacity derived from
declared service work, fairness is finite overtaking, and the refusal clock runs
from ADMISSION, not from filing.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction as Q
from typing import Iterable, Mapping, Sequence

from src.grammar import Grounds


@dataclass(frozen=True)
class ServiceCosts:
    """Capacity in existing mechanism quantities: declared service work."""

    per_date_work: Q
    merits_work: Q
    default_work: Q
    admission_work: Q

    @property
    def ruling_capacity(self) -> int:
        """How many merits rulings one date's declared work affords."""
        if self.merits_work <= 0:
            raise ValueError("merits work must be positive")
        return int(Q(self.per_date_work) / Q(self.merits_work))

    @property
    def admission_capacity(self) -> int:
        if self.admission_work <= 0:
            raise ValueError("admission work must be positive")
        return int(Q(self.per_date_work) / Q(self.admission_work))


@dataclass(frozen=True)
class Arrival:
    """One well-formed query arriving at a date."""

    query_id: str
    date: int
    substantive: bool
    stakes: Q = Q(1)


@dataclass(frozen=True)
class StreamPolicy:
    """What the record shows the learner did, per date.  Not a decision rule.

    `merits_rulings` and `default_rulings` are counts the record exhibits; this
    module never selects them.  A policy here is a transcript, not an agent.
    """

    policy_id: str
    merits_per_date: int = 0
    defaults_per_date: int = 0


@dataclass(frozen=True)
class SolvencyCoupling:
    """The flow-side insolvency trigger: liability draws down a finite account."""

    account_balance: Q
    enabled: bool = True

    def triggered(self, accumulated: Q) -> bool:
        return self.enabled and Q(accumulated) > Q(self.account_balance)


@dataclass(frozen=True)
class StreamSchedule:
    refusal_tariff: Q
    default_tariff: Q
    declared_default_rate_bound: Q | None = None
    rate_window: int = 4


@dataclass(frozen=True)
class DateRecord:
    date: int
    admitted: tuple[str, ...]
    queued: int
    open_after: int
    merits: int
    defaults: int
    refusal_accrued: Q
    default_accrued: Q
    accumulated: Q
    insolvent: bool


@dataclass(frozen=True)
class StreamReport:
    horizon: int
    records: tuple[DateRecord, ...]
    admitted_total: int
    substantive_admitted: int
    rulings_total: int
    defaults_total: int
    accumulated_liability: Q
    insolvency_date: int | None
    never_admitted: tuple[str, ...]
    max_wait: int

    @property
    def open_at_end(self) -> int:
        return self.records[-1].open_after if self.records else 0

    @property
    def liability_bounded_by(self) -> Q:
        return self.accumulated_liability


def run_stream(arrivals: Sequence[Arrival], costs: ServiceCosts,
               schedule: StreamSchedule, policy: StreamPolicy,
               coupling: SolvencyCoupling, horizon: int, *,
               admission: bool = True) -> StreamReport:
    """Simulate the accounting.  Deterministic and exact; selects nothing.

    With `admission=False` the intake queue is bypassed — every arrival is open
    from its arrival date — which is the `CS-N2` ablation.
    """
    queue: list[Arrival] = []
    open_ids: list[str] = []
    admitted_on: dict[str, int] = {}
    records: list[DateRecord] = []
    accumulated = Q(0)
    insolvency_date: int | None = None
    merits_total = defaults_total = 0
    by_date: dict[int, list[Arrival]] = {}
    for arrival in arrivals:
        by_date.setdefault(arrival.date, []).append(arrival)

    for date in range(horizon):
        # Arrivals join the intake queue in arrival order (finite overtaking).
        queue.extend(sorted(by_date.get(date, []), key=lambda a: a.query_id))
        if admission:
            capacity = costs.admission_capacity
            admitted_now = queue[:capacity]
            queue = queue[capacity:]
        else:
            admitted_now, queue = queue, []
        for arrival in admitted_now:
            admitted_on[arrival.query_id] = date
            open_ids.append(arrival.query_id)

        # Rulings close open obligations, oldest first.
        merits = min(policy.merits_per_date, len(open_ids))
        remaining_work = Q(costs.per_date_work) - merits * Q(costs.merits_work)
        affordable_defaults = int(remaining_work / Q(costs.default_work)) if (
            costs.default_work > 0 and remaining_work > 0) else 0
        defaults = min(policy.defaults_per_date, len(open_ids) - merits,
                       affordable_defaults)
        closed = merits + defaults
        open_ids = open_ids[closed:]
        merits_total += merits
        defaults_total += defaults

        # Refusal runs from admission, per D3, on whatever is still open.
        refusal = Q(len(open_ids)) * Q(schedule.refusal_tariff)
        default_charge = Q(defaults) * Q(schedule.default_tariff)
        accumulated += refusal + default_charge
        if insolvency_date is None and coupling.triggered(accumulated):
            insolvency_date = date
        records.append(DateRecord(
            date, tuple(a.query_id for a in admitted_now), len(queue), len(open_ids),
            merits, defaults, refusal, default_charge, accumulated,
            insolvency_date is not None))

    waits = [admitted_on[a.query_id] - a.date for a in arrivals
             if a.query_id in admitted_on]
    return StreamReport(
        horizon, tuple(records), len(admitted_on),
        sum(1 for a in arrivals if a.substantive and a.query_id in admitted_on),
        merits_total, defaults_total, accumulated, insolvency_date,
        tuple(sorted(a.query_id for a in arrivals if a.query_id not in admitted_on)),
        max(waits) if waits else 0)


# --------------------------------------------------------------------------
# The demand results, as checked accounting properties
# --------------------------------------------------------------------------


def lower_density(arrivals: Sequence[Arrival], horizon: int) -> Q:
    """Substantive arrivals per date over the horizon."""
    if horizon <= 0:
        return Q(0)
    return Q(sum(1 for a in arrivals if a.substantive and a.date < horizon), horizon)


def dates_in_arrears(report: StreamReport) -> int:
    """Dates on which something admitted was still open.

    `CS-J1` bounds this by `accumulated / refusal_tariff`: each such date accrues
    at least one tariff unit, so bounded liability bounds arrears.
    """
    return sum(1 for record in report.records if record.open_after > 0)


@dataclass(frozen=True)
class TrilemmaVerdict:
    """`CS-J2`.  At least one branch holds on every admitted substantive stream."""

    unbounded_liability: bool
    insolvent: bool
    rate_matches: bool
    defaults_counted: int

    @property
    def holds(self) -> bool:
        return self.unbounded_liability or self.insolvent or self.rate_matches


def trilemma(report: StreamReport, bound: Q) -> TrilemmaVerdict:
    return TrilemmaVerdict(
        report.accumulated_liability > Q(bound),
        report.insolvency_date is not None,
        report.open_at_end == 0 and report.never_admitted == (),
        report.defaults_total)


def default_resolution_rate(report: StreamReport,
                            arrivals: Sequence[Arrival]) -> Q:
    """Stakes-weighted default share of resolutions; merits coverage is `1 - rate`."""
    stakes = {a.query_id: Q(a.stakes) for a in arrivals}
    resolved = report.rulings_total + report.defaults_total
    if resolved == 0:
        return Q(0)
    average = (sum(stakes.values(), Q(0)) / Q(len(stakes))) if stakes else Q(1)
    return Q(report.defaults_total, resolved) * average / average


def merits_coverage(report: StreamReport, arrivals: Sequence[Arrival]) -> Q:
    return Q(1) - default_resolution_rate(report, arrivals)


def aggregate_default_grounds(report: StreamReport, arrivals: Sequence[Arrival],
                              schedule: StreamSchedule,
                              grounds_id: str) -> Grounds | None:
    """`CS-J4`.  Grounds when the computed rate exceeds the book's declared bound.

    The bound is book content and therefore itself objectionable; nothing here
    canonicalizes a window.
    """
    if schedule.declared_default_rate_bound is None:
        return None
    rate = default_resolution_rate(report, arrivals)
    if rate <= Q(schedule.declared_default_rate_bound):
        return None
    window = (max(0, report.horizon - schedule.rate_window), report.horizon)
    return Grounds(grounds_id, {"window": window, "rate": rate,
                                "bound": Q(schedule.declared_default_rate_bound)})


@dataclass(frozen=True)
class CombinedLiability:
    """Objection charges and docket tariffs accumulating against one book.

    Charges run per date while an objection stands; tariffs are docket
    liabilities.  They are different quantities keyed on different coordinates,
    so the two accountings compose by addition — provided no single event is
    counted in both.  `disjoint` is that check, and it is the whole content of
    the no-double-counting lemma.
    """

    charge_keys: tuple[tuple[str, int], ...]
    tariff_keys: tuple[tuple[str, int], ...]
    charge_total: Q
    tariff_total: Q

    @property
    def disjoint(self) -> bool:
        return not (set(self.charge_keys) & set(self.tariff_keys))

    @property
    def total(self) -> Q:
        return Q(self.charge_total) + Q(self.tariff_total)


def combine_liabilities(charges: Mapping[tuple[str, int], Q],
                        report: StreamReport) -> CombinedLiability:
    """Compose an extraction-mode siege with a case stream, without double count."""
    tariffs = {("docket", record.date): record.refusal_accrued + record.default_accrued
               for record in report.records}
    return CombinedLiability(
        tuple(sorted(charges)), tuple(sorted(tariffs)),
        sum(charges.values(), Q(0)), sum(tariffs.values(), Q(0)))


# --------------------------------------------------------------------------
# T6: the patron fence, resolved by reuse
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Fence:
    """A declared account boundary.  Pooled systems declare none."""

    fence_id: str
    inside_accounts: tuple[str, ...]
    declared: bool = True


@dataclass(frozen=True)
class Transfer:
    """A patron payment toward a docket liability."""

    transfer_id: str
    from_account: str
    to_account: str
    amount: Q


def crosses_fence(transfer: Transfer, fence: Fence) -> bool:
    """A transfer crosses when exactly one endpoint is inside a declared fence."""
    if not fence.declared:
        return False
    inside = set(fence.inside_accounts)
    return (transfer.from_account in inside) != (transfer.to_account in inside)


def cross_subsidy_grounds(transfer: Transfer, fence: Fence,
                          grounds_id: str) -> Grounds | None:
    """Patron-funded decline is chargeable exactly when it crosses a declared fence.

    This is the existing cross-subsidy conduct objection, not a new type: its
    judge footprint is declared natively in the grammar catalog.  In a pooled
    system no fence is declared, nothing crosses, and nothing fires.
    """
    if not crosses_fence(transfer, fence):
        return None
    return Grounds(grounds_id, {"transfer_id": transfer.transfer_id,
                                "fence_id": fence.fence_id,
                                "amount": Q(transfer.amount)})


FENCED = Fence("fence:mechanism", ("account:mechanism",), declared=True)
POOLED = Fence("fence:none", (), declared=False)
PATRON_TRANSFER = Transfer("t:patron", "account:patron", "account:mechanism", Q(1))
