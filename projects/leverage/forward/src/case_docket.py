"""The case docket and its adjudication protocol.

The answerability ledger records what the learner owes an answer to.  The case
docket records the practical questions it must dispose of, and the adjudication
protocol decides whether the active credal book supports a merits ruling or only
a scheduled default — or nothing, in which case the learner declines and the
obligation stays open at a cost.

Five things stay separate:

    case demand  !=  answer generation  !=  merits certification
                 !=  practical ruling   !=  operative force

A ruling is not a belief settlement.  A default is not a normative belief.
Neither enters the settled empirical or logical record.  Nothing here generates
responses, models parties, or optimizes anything: tariffs are accounted
liabilities, not incentives.

The credal interval is supplied input from the existing book layer.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction as Q
from typing import Callable, Iterable, Mapping, Sequence

from src.answerability import (
    BoundaryDisposition,
    Cover,
    Discharge,
    Dispose,
    FileObligation,
    FileResponse,
    LedgerLog,
    Obligation,
    ProceduralClosure,
    Response,
    verify_ledger,
)

BASIS_MERITS = "merits"
BASIS_DEFAULT = "default"
BASIS_TAGS = (BASIS_MERITS, BASIS_DEFAULT)


@dataclass(frozen=True)
class ProcedureSchedule:
    """Revisable but prospective procedural content, not a constitution.

    Only what the four results need: the threshold, the verdict labels, the
    fallback, and the two tariffs.  It is challengeable; its application to an
    already-filed query is frozen unless an authorized amendment says otherwise.
    """

    claim_type_id: str
    schedule_version: int
    target_rule: str
    threshold: Q
    positive_verdict: str
    negative_verdict: str
    fallback_verdict: str
    default_tariff: Q
    refusal_tariff: Q
    basis: str

    def well_formed(self) -> bool:
        return (Q(0) < Q(self.threshold) < Q(1)
                and self.default_tariff >= 0 and self.refusal_tariff >= 0
                and bool(self.basis) and bool(self.target_rule)
                and len({self.positive_verdict, self.negative_verdict,
                         self.fallback_verdict}) >= 2)


@dataclass(frozen=True)
class Query:
    """Thin: the claim type and the schedule version bound when it arrived."""

    query_id: str
    case_id: str
    claim_type_id: str
    bound_schedule_version: int
    target_instance: str


@dataclass(frozen=True)
class CredalInterval:
    """Exact rational credence supplied by the active book."""

    book_version: int
    target: str
    lower: Q
    upper: Q

    def well_formed(self) -> bool:
        return Q(0) <= Q(self.lower) <= Q(self.upper) <= Q(1)


@dataclass(frozen=True)
class MeritsCertificate:
    """Constructible only by `certify_merits` from an actual credal interval.

    A ruling identifier cannot be turned into one: there is no field a default
    could populate, and the verifier recomputes the direction from the interval
    the active book supplied.  Default non-evidence is a property of the type,
    not of a naming convention.
    """

    certificate_id: str
    query_id: str
    target: str
    book_version: int
    schedule_version: int
    interval: CredalInterval
    threshold: Q
    direction: str


@dataclass(frozen=True)
class Ruling:
    ruling_id: str
    query_id: str
    verdict: str
    basis_tag: str
    certificate_ids: tuple[str, ...]
    book_version: int
    bound_schedule_version: int


@dataclass(frozen=True)
class RetrospectiveAmendment:
    amendment_id: str
    query_id: str
    old_schedule_version: int
    new_schedule_version: int
    authorization: str
    consequence: str


@dataclass(frozen=True)
class LiabilityEntry:
    kind: str
    query_id: str
    amount: Q
    step: int


@dataclass(frozen=True)
class DocketObstruction:
    code: str
    query_ids: tuple[str, ...]
    detail: str


@dataclass(frozen=True)
class AdjudicationReport:
    accepted: bool
    rulings: tuple[Ruling, ...]
    liabilities: tuple[LiabilityEntry, ...]
    open_decisions: tuple[str, ...]
    obstructions: tuple[DocketObstruction, ...]
    ledger_accepted: bool

    @property
    def total_liability(self) -> Q:
        return sum((entry.amount for entry in self.liabilities), Q(0))


EligibilityOracle = Callable[[Query, ProcedureSchedule], bool]


def target_rule_eligibility(query: Query, schedule: ProcedureSchedule) -> bool:
    """The supplied target-binding check.  No schema discovery happens here."""
    return (query.claim_type_id == schedule.claim_type_id
            and query.bound_schedule_version == schedule.schedule_version
            and query.target_instance.startswith(schedule.target_rule))


def merits_direction(interval: CredalInterval, threshold: Q) -> str | None:
    """Positive if the lower bound clears the threshold, negative if the upper
    bound falls short, otherwise no merits verdict is available."""
    if not interval.well_formed():
        return None
    if Q(interval.lower) >= Q(threshold):
        return "positive"
    if Q(interval.upper) < Q(threshold):
        return "negative"
    return None


def certify_merits(query: Query, schedule: ProcedureSchedule,
                   interval: CredalInterval,
                   certificate_id: str) -> MeritsCertificate | None:
    direction = merits_direction(interval, schedule.threshold)
    if direction is None or interval.target != query.target_instance:
        return None
    return MeritsCertificate(certificate_id, query.query_id, query.target_instance,
                             interval.book_version, schedule.schedule_version,
                             interval, Q(schedule.threshold), direction)


def _obstruct(store: list[DocketObstruction], code: str, queries: Iterable[str],
              detail: str) -> None:
    store.append(DocketObstruction(code, tuple(queries), detail))


# --------------------------------------------------------------------------
# Identity integrity
# --------------------------------------------------------------------------


def _unique(store: list[DocketObstruction], label: str, code: str,
            items: Iterable[tuple[str, object]]) -> dict[str, object]:
    """Build an index without letting a later entry silently erase an earlier one."""
    index: dict[str, object] = {}
    for key, value in items:
        if key in index:
            _obstruct(store, code, (key,), f"duplicate {label} identifier {key!r}")
            continue
        index[key] = value
    return index


def decision_obligation(query: Query, event_id: str, version: int) -> Obligation:
    """Filing a well-formed query creates an identified decision obligation."""
    return Obligation(f"d:{query.query_id}", "decision", version, event_id,
                      f"query:{query.query_id}", query.target_instance)


def adjudicate(
    queries: Sequence[Query],
    schedules: Sequence[ProcedureSchedule],
    intervals: Mapping[str, CredalInterval],
    rulings: Sequence[Ruling],
    certificates: Sequence[MeritsCertificate],
    *,
    filed_step: int = 0,
    horizon_step: int = 0,
    amendments: Sequence[RetrospectiveAmendment] = (),
    ledger: LedgerLog | None = None,
    eligibility: EligibilityOracle = target_rule_eligibility,
) -> AdjudicationReport:
    """Check every ruling against the schedule bound at filing and the book.

    Nothing here decides what is true.  It decides whether the record shows that
    a merits verdict was available, or that a scheduled default was taken, or
    that the learner declined and still owes an answer.
    """
    obstructions: list[DocketObstruction] = []
    by_version = _unique(obstructions, "schedule-version", "docket.duplicate_schedule",
                         (((s.claim_type_id, s.schedule_version), s) for s in schedules))
    amended = {a.query_id: a for a in amendments if a.authorization and a.consequence}
    for amendment in amendments:
        if not amendment.authorization or not amendment.consequence:
            _obstruct(obstructions, "docket.unauthorized_retrospective_amendment",
                      (amendment.query_id,),
                      "a retrospective amendment needs authorization and a recorded "
                      "discrepancy or liability consequence")
    for schedule in schedules:
        if not schedule.well_formed():
            _obstruct(obstructions, "docket.malformed_schedule", (),
                      f"schedule {schedule.claim_type_id}"
                      f"@{schedule.schedule_version} is malformed")

    query_index = _unique(obstructions, "query", "docket.duplicate_query",
                          ((q.query_id, q) for q in queries))
    certificate_index = _unique(obstructions, "certificate", "docket.duplicate_certificate",
                                ((c.certificate_id, c) for c in certificates))
    _unique(obstructions, "ruling", "docket.duplicate_ruling_id",
            ((r.ruling_id, r) for r in rulings))
    bound: dict[str, ProcedureSchedule] = {}
    for query in queries:
        version = query.bound_schedule_version
        amendment = amended.get(query.query_id)
        if amendment is not None and amendment.old_schedule_version == version:
            version = amendment.new_schedule_version
        schedule = by_version.get((query.claim_type_id, version))
        if schedule is None:
            _obstruct(obstructions, "docket.unbound_schedule", (query.query_id,),
                      "the query names no available schedule version")
            continue
        # Eligibility is about claim type and target binding, not about which
        # schedule version an authorized amendment later applied.
        if not eligibility(query, replace(
                schedule, schedule_version=query.bound_schedule_version)):
            _obstruct(obstructions, "docket.query_not_well_formed", (query.query_id,),
                      "the query does not bind its claim type's target rule")
            continue
        bound[query.query_id] = schedule

    liabilities: list[LiabilityEntry] = []
    ruled: set[str] = set()
    for ruling in rulings:
        query = query_index.get(ruling.query_id)
        schedule = bound.get(ruling.query_id)
        if query is None or schedule is None:
            _obstruct(obstructions, "docket.ruling_without_query", (ruling.query_id,),
                      "a ruling names no well-formed query")
            continue
        if ruling.query_id in ruled:
            _obstruct(obstructions, "docket.duplicate_ruling", (ruling.query_id,),
                      "one query receives at most one ruling")
            continue
        if ruling.basis_tag not in BASIS_TAGS:
            _obstruct(obstructions, "docket.unknown_basis_tag", (ruling.query_id,),
                      "a ruling is tagged merits or default")
            continue
        if ruling.bound_schedule_version != schedule.schedule_version:
            _obstruct(obstructions, "docket.stale_schedule", (ruling.query_id,),
                      "the ruling cites a schedule version other than the one bound "
                      "to this query")
            continue
        if ruling.basis_tag == BASIS_MERITS:
            if not ruling.certificate_ids:
                _obstruct(obstructions, "docket.merits_without_certificate",
                          (ruling.query_id,),
                          "a merits ruling needs a threshold-clearing certificate")
                continue
            certificate = certificate_index.get(ruling.certificate_ids[0])
            if certificate is None:
                _obstruct(obstructions, "docket.forged_certificate", (ruling.query_id,),
                          "the cited certificate does not exist")
                continue
            interval = intervals.get(query.target_instance)
            problems = []
            if certificate.query_id != ruling.query_id:
                problems.append("certificate is for another query")
            if certificate.target != query.target_instance:
                problems.append("certificate is for another target")
            if certificate.schedule_version != schedule.schedule_version:
                problems.append("certificate cites another schedule version")
            if Q(certificate.threshold) != Q(schedule.threshold):
                problems.append("certificate cites another threshold")
            if interval is None or certificate.book_version != interval.book_version:
                problems.append("certificate cites another book version")
            elif (certificate.interval.lower, certificate.interval.upper) != (
                    interval.lower, interval.upper):
                problems.append("certificate cites another interval")
            recomputed = (merits_direction(interval, schedule.threshold)
                          if interval is not None else None)
            if recomputed is None or recomputed != certificate.direction:
                problems.append("the interval does not clear the threshold as claimed")
            expected = (schedule.positive_verdict if certificate.direction == "positive"
                        else schedule.negative_verdict)
            if ruling.verdict != expected:
                problems.append("the verdict does not match the certified direction")
            if problems:
                _obstruct(obstructions, "docket.unsupported_merits", (ruling.query_id,),
                          "; ".join(problems))
                continue
        else:
            if ruling.certificate_ids:
                _obstruct(obstructions, "docket.default_citing_certificate",
                          (ruling.query_id,),
                          "a default ruling is not supported by a merits certificate")
                continue
            if ruling.verdict != schedule.fallback_verdict:
                _obstruct(obstructions, "docket.default_not_fallback", (ruling.query_id,),
                          "a default ruling issues the bound fallback verdict")
                continue
            liabilities.append(LiabilityEntry("default", ruling.query_id,
                                              Q(schedule.default_tariff), 0))
        ruled.add(ruling.query_id)

    # Refusal accrues automatically for every unruled query over the elapsed
    # horizon.  It is derived from the clock and the frozen tariff, never
    # supplied, so an unruled query cannot be omitted from the accounting.
    elapsed = max(0, horizon_step - filed_step)
    for query_id in sorted(bound):
        if query_id in ruled:
            continue
        schedule = bound[query_id]
        for step in range(elapsed):
            liabilities.append(LiabilityEntry("refusal", query_id,
                                              Q(schedule.refusal_tariff),
                                              filed_step + step))

    open_decisions = tuple(sorted(
        query.query_id for query in queries
        if query.query_id in bound and query.query_id not in ruled))
    ledger_accepted = True
    if ledger is not None:
        ledger_report = verify_ledger(ledger)
        ledger_accepted = ledger_report.accepted
        closed = set(ledger_report.closed)
        for query in queries:
            identifier = f"d:{query.query_id}"
            if query.query_id in ruled and identifier in ledger_report.live:
                _obstruct(obstructions, "docket.ruling_without_ledger_disposition",
                          (query.query_id,),
                          "a ruling was issued while the decision obligation stays open")
            if query.query_id not in ruled and identifier in closed:
                _obstruct(obstructions, "docket.ledger_closed_without_ruling",
                          (query.query_id,),
                          "the decision obligation was closed with no ruling")

    return AdjudicationReport(
        not obstructions and ledger_accepted, tuple(rulings), tuple(liabilities),
        open_decisions, tuple(obstructions), ledger_accepted)


def default_disposition(query: Query, event_id: str, version: int,
                        authorization: str, *, ruling_id: str,
                        fallback_verdict: str) -> tuple[ProceduralClosure,
                                                        BoundaryDisposition]:
    """The typed procedural closure for a scheduled default.

    Not a withdrawal and not a loss.  The obligation was disposed of by schedule;
    no substantive claim was endorsed, withdrawn, settled, or made true; no
    merits coverage was created; and the underlying material stays challengeable.
    """
    return (
        ProceduralClosure(event_id, version, f"d:{query.query_id}", fallback_verdict,
                          ruling_id, authorization),
        BoundaryDisposition(f"{event_id}:bd", version, f"d:{query.query_id}",
                            "procedural", authorization, (event_id,)),
    )


def merits_ledger_events(query: Query, certificate: MeritsCertificate, version: int,
                         authorization: str) -> tuple:
    """The merits path through the ledger: response, coverage edge, discharge."""
    response_id = f"r:{query.query_id}"
    return (
        FileResponse(f"e:resp:{query.query_id}", version,
                     Response(response_id, "decision", version, authorization)),
        Cover(f"e:cover:{query.query_id}", version, response_id,
              f"d:{query.query_id}", certificate.certificate_id, authorization),
        Discharge(f"e:disc:{query.query_id}", version, f"d:{query.query_id}",
                  f"e:cover:{query.query_id}"),
        BoundaryDisposition(f"e:bd:{query.query_id}", version, f"d:{query.query_id}",
                            "discharge", authorization,
                            (f"e:cover:{query.query_id}", f"e:disc:{query.query_id}")),
    )


# --------------------------------------------------------------------------
# The adjudication transaction
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class RefusalClock:
    """The explicit horizon refusal liability is derived from.

    An instantaneous snapshot has `filed == horizon`, so no time has elapsed and
    no refusal charge exists.  A longitudinal evaluation has `horizon > filed`,
    and the charge is `(horizon - filed) * refusal_tariff` — derived, never
    supplied by the caller.
    """

    filed_step: int
    horizon_step: int

    @property
    def elapsed(self) -> int:
        return max(0, self.horizon_step - self.filed_step)


@dataclass(frozen=True)
class AdjudicationTransaction:
    """One attempted disposition, with everything that authorizes it.

    Not a bundle of references: `verify_transaction` establishes each identity
    and each relation between them.
    """

    transaction_id: str
    query: Query
    schedule: ProcedureSchedule
    obligation_id: str
    basis: str
    clock: RefusalClock
    ruling: Ruling | None = None
    certificate: MeritsCertificate | None = None
    interval: CredalInterval | None = None
    ledger_event_ids: tuple[str, ...] = ()
    boundary_event_id: str | None = None
    liabilities: tuple[LiabilityEntry, ...] = ()

    @property
    def is_decline(self) -> bool:
        return self.ruling is None


@dataclass(frozen=True)
class TransactionReport:
    transaction_id: str
    accepted: bool
    basis: str
    obstructions: tuple[DocketObstruction, ...]
    derived_liabilities: tuple[LiabilityEntry, ...]

    @property
    def total_liability(self) -> Q:
        return sum((entry.amount for entry in self.derived_liabilities), Q(0))


def _event_obligation(event) -> str | None:
    """Which obligation a ledger event concerns, including filings."""
    if isinstance(event, FileObligation):
        return event.obligation.obligation_id
    return getattr(event, "obligation_id", None) or getattr(event, "parent_id", None)


def verify_transaction(transaction: AdjudicationTransaction, ledger: LedgerLog,
                       *, adequacy_intervals: Mapping[str, CredalInterval] = {},
                       ) -> TransactionReport:
    """Check that the ruling cannot misstate any of the facts that authorize it."""
    obstructions: list[DocketObstruction] = []
    query, schedule = transaction.query, transaction.schedule
    identifier = query.query_id

    if not schedule.well_formed():
        _obstruct(obstructions, "docket.malformed_schedule", (identifier,),
                  "the governing schedule is malformed")
    if query.claim_type_id != schedule.claim_type_id:
        _obstruct(obstructions, "docket.claim_type_mismatch", (identifier,),
                  "the query's claim type is not the schedule's")
    if query.bound_schedule_version != schedule.schedule_version:
        _obstruct(obstructions, "docket.stale_schedule", (identifier,),
                  "the transaction applies a schedule version the query is not bound to")
    if not target_rule_eligibility(query, schedule):
        _obstruct(obstructions, "docket.query_not_well_formed", (identifier,),
                  "the query does not bind the schedule's target rule")
    if transaction.obligation_id != f"d:{identifier}":
        _obstruct(obstructions, "docket.obligation_from_wrong_query", (identifier,),
                  "the transaction names a decision obligation of another query")

    report = verify_ledger(ledger)
    if not report.accepted:
        _obstruct(obstructions, "docket.ledger_rejected", (identifier,),
                  "the ledger segment carrying this transaction is not accepted")
    by_event = {event.event_id: event for event in ledger.events}
    for reference in transaction.ledger_event_ids:
        event = by_event.get(reference)
        if event is None:
            _obstruct(obstructions, "docket.missing_ledger_event", (identifier,),
                      f"ledger event {reference!r} does not exist")
            continue
        target = _event_obligation(event)
        if target is not None and target != transaction.obligation_id:
            _obstruct(obstructions, "docket.foreign_ledger_event", (identifier,),
                      f"ledger event {reference!r} concerns another obligation")

    state = {**report.live, **report.closed}.get(transaction.obligation_id)
    if state is None:
        _obstruct(obstructions, "docket.missing_decision_obligation", (identifier,),
                  "the decision obligation was never filed")
    elif state.obligation.carrier != query.target_instance and not transaction.is_decline:
        pass

    boundary = by_event.get(transaction.boundary_event_id or "")
    if transaction.boundary_event_id is not None and not isinstance(
            boundary, BoundaryDisposition):
        _obstruct(obstructions, "docket.missing_boundary_disposition", (identifier,),
                  "the named boundary record is not a boundary disposition")
        boundary = None

    ruling = transaction.ruling
    if transaction.basis not in BASIS_TAGS + ("decline",):
        _obstruct(obstructions, "docket.unknown_basis_tag", (identifier,),
                  "a transaction is merits, default, or decline")
    if ruling is not None and ruling.basis_tag != transaction.basis:
        _obstruct(obstructions, "docket.basis_mismatch", (identifier,),
                  "the ruling's basis tag is not the transaction's")
    if ruling is not None and ruling.query_id != identifier:
        _obstruct(obstructions, "docket.ruling_for_wrong_query", (identifier,),
                  "the ruling answers another query")
    if ruling is not None and ruling.bound_schedule_version != schedule.schedule_version:
        _obstruct(obstructions, "docket.stale_schedule", (identifier,),
                  "the ruling cites another schedule version")

    derived: list[LiabilityEntry] = []

    if transaction.basis == BASIS_MERITS:
        certificate, interval = transaction.certificate, transaction.interval
        if ruling is None or certificate is None or interval is None:
            _obstruct(obstructions, "docket.merits_without_certificate", (identifier,),
                      "a merits transaction needs a ruling, a certificate, and an interval")
        else:
            if ruling.certificate_ids[:1] != (certificate.certificate_id,):
                _obstruct(obstructions, "docket.forged_certificate", (identifier,),
                          "the ruling does not cite this certificate")
            supplied = adequacy_intervals.get(query.target_instance, interval)
            problems = []
            if certificate.query_id != identifier:
                problems.append("certificate is for another query")
            if certificate.target != query.target_instance:
                problems.append("certificate is for another target")
            if interval.target != query.target_instance:
                problems.append("the interval is for another target")
            if certificate.schedule_version != schedule.schedule_version:
                problems.append("certificate cites another schedule version")
            if Q(certificate.threshold) != Q(schedule.threshold):
                problems.append("certificate cites another threshold")
            if certificate.book_version != interval.book_version:
                problems.append("certificate cites another book version")
            if ruling.book_version != interval.book_version:
                problems.append("the ruling cites another book version")
            if (supplied.lower, supplied.upper) != (interval.lower, interval.upper):
                problems.append("the interval is not the one the book supplied")
            recomputed = merits_direction(interval, schedule.threshold)
            if recomputed is None or recomputed != certificate.direction:
                problems.append("the interval does not clear the threshold as claimed")
            expected = (schedule.positive_verdict if certificate.direction == "positive"
                        else schedule.negative_verdict)
            if ruling.verdict != expected:
                problems.append("the verdict does not match the certified direction")
            if problems:
                _obstruct(obstructions, "docket.unsupported_merits", (identifier,),
                          "; ".join(problems))
        if state is not None and state.closure_kind != "discharge":
            _obstruct(obstructions, "docket.merits_without_discharge", (identifier,),
                      f"a merits ruling requires a merits discharge, found "
                      f"{state.closure_kind!r}")
        if boundary is not None and boundary.outcome != "discharge":
            _obstruct(obstructions, "docket.boundary_basis_mismatch", (identifier,),
                      f"a merits ruling requires a discharge boundary, found "
                      f"{boundary.outcome!r}")
        if transaction.liabilities:
            _obstruct(obstructions, "docket.merits_with_liability", (identifier,),
                      "a merits ruling creates no default or refusal liability")

    elif transaction.basis == BASIS_DEFAULT:
        if ruling is None:
            _obstruct(obstructions, "docket.default_without_ruling", (identifier,),
                      "a default transaction needs its ruling")
        else:
            if transaction.certificate is not None or ruling.certificate_ids:
                _obstruct(obstructions, "docket.default_citing_certificate", (identifier,),
                          "a default is not supported by a merits certificate")
            if ruling.verdict != schedule.fallback_verdict:
                _obstruct(obstructions, "docket.default_not_fallback", (identifier,),
                          "a default issues the frozen fallback verdict")
        if state is not None and state.closure_kind != "procedural":
            _obstruct(obstructions, "docket.default_without_procedural_closure",
                      (identifier,),
                      f"a default requires a typed procedural closure, found "
                      f"{state.closure_kind!r}")
        if state is not None and state.coverage_events:
            _obstruct(obstructions, "docket.default_with_coverage", (identifier,),
                      "a default creates no merits coverage")
        if boundary is not None and boundary.outcome != "procedural":
            _obstruct(obstructions, "docket.boundary_basis_mismatch", (identifier,),
                      f"a default requires a procedural boundary, found "
                      f"{boundary.outcome!r}")
        derived.append(LiabilityEntry("default", identifier,
                                      Q(schedule.default_tariff), transaction.clock.filed_step))

    else:  # decline
        if ruling is not None:
            _obstruct(obstructions, "docket.declined_and_ruled", (identifier,),
                      "a decline transaction records no ruling")
        if state is not None and state.status.value == "closed":
            _obstruct(obstructions, "docket.ledger_closed_without_ruling", (identifier,),
                      "the decision obligation was closed with no ruling")
        for step in range(transaction.clock.elapsed):
            derived.append(LiabilityEntry("refusal", identifier,
                                          Q(schedule.refusal_tariff),
                                          transaction.clock.filed_step + step))

    if transaction.liabilities and tuple(transaction.liabilities) != tuple(derived):
        _obstruct(obstructions, "docket.liability_mismatch", (identifier,),
                  "the declared liabilities are not the ones the schedule and clock "
                  "generate")

    return TransactionReport(transaction.transaction_id, not obstructions,
                             transaction.basis, tuple(obstructions), tuple(derived))


@dataclass(frozen=True)
class CaseStreamLiabilities:
    """Typed output for the later bounded-force or solvency machinery."""

    horizon_step: int
    default_total: Q
    refusal_total: Q
    entries: tuple[LiabilityEntry, ...]
    open_decisions: tuple[str, ...]

    @property
    def total(self) -> Q:
        return self.default_total + self.refusal_total


def case_stream_liabilities(reports: Sequence[TransactionReport], horizon_step: int,
                            open_decisions: Sequence[str] = ()) -> CaseStreamLiabilities:
    entries = tuple(entry for report in reports for entry in report.derived_liabilities)
    default_total = sum((e.amount for e in entries if e.kind == "default"), Q(0))
    refusal_total = sum((e.amount for e in entries if e.kind == "refusal"), Q(0))
    return CaseStreamLiabilities(horizon_step, default_total, refusal_total, entries,
                                 tuple(sorted(open_decisions)))
