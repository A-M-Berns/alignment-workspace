"""The answerability ledger: identified obligations through conceptual revision.

`LG-X1` showed that an unresolved-burden Boolean does not compose: two owed
answers may merge onto one occurrence and be closed by one terminal record.  The
naive correction — one witness answers one obligation — is also wrong, because a
single proof, decision, or evidential record may legitimately answer several
questions.

The invariant this module implements is neither:

    Every open obligation has its own identity and receives an explicit,
    authorized disposition.  A single response may discharge several obligations
    only when its adequacy for each is separately represented.

The ledger is a **demand record**.  It records what the learner owes an answer
to.  It does not generate answers, does not make a proposed answer
authoritative, does not choose an ontology, and does not endorse warrants.

Nothing in `src/migration.py` is changed.  The ledger is a separate object: an
append-only event log whose live state is a fold, so composition of histories is
concatenation of logs.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Callable, Iterable, Mapping, Sequence


class ObligationStatus(str, Enum):
    """The smallest adequate algebra: closure kind lives in the disposition."""

    OPEN = "open"
    SUSPENDED = "suspended"
    CLOSED = "closed"


CLOSURE_KINDS = ("discharge", "withdrawal", "loss", "procedural")
SUBSTANTIVE_CLOSURE_KINDS = ("withdrawal", "loss")
COMPLETION_RULES = ("all", "any", "none")

# The three systems compared in `ANSWERABILITY_LEDGER.md` §7.
SYSTEM_BIT = "burden-bit"
SYSTEM_RIVALROUS = "one-response-one-obligation"
SYSTEM_COVERAGE = "certified-coverage"
SYSTEMS = (SYSTEM_BIT, SYSTEM_RIVALROUS, SYSTEM_COVERAGE)


@dataclass(frozen=True)
class Obligation:
    """An identified answerability obligation.

    Every field prevents a demonstrated failure:
    `obligation_id` prevents `LG-X1`; `origin_version` with `origin_event`
    prevents cross-version identifier collision; `kind` prevents a response
    answering the wrong sort of question; `carrier` is what a migration
    retargets; `basis` prevents unauthorized obligation creation; `lineage`
    records refinement and identification provenance.
    """

    obligation_id: str
    kind: str
    origin_version: int
    origin_event: str
    basis: str
    carrier: str
    lineage: tuple[str, ...] = ()

    @property
    def origin(self) -> tuple[int, str]:
        return (self.origin_version, self.origin_event)


@dataclass(frozen=True)
class Response:
    response_id: str
    kind: str
    version: int
    basis: str


# --------------------------------------------------------------------------
# Events.  The log is append-only; nothing is ever rewritten.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Event:
    event_id: str
    version: int


@dataclass(frozen=True)
class FileObligation(Event):
    obligation: Obligation


@dataclass(frozen=True)
class Carry(Event):
    obligation_id: str
    carrier: str
    authorization: str


@dataclass(frozen=True)
class Suspend(Event):
    obligation_id: str
    reason: str
    authorization: str


@dataclass(frozen=True)
class Refine(Event):
    parent_id: str
    children: tuple[Obligation, ...]
    completion_rule: str
    authorization: str


@dataclass(frozen=True)
class Identify(Event):
    """An equivalence certificate.  It does *not* merge obligations.

    It licenses one adequacy argument to ground a coverage edge for each of the
    identified obligations, so both keep their own identity and their own
    disposition record.  `ANSWERABILITY_LEDGER.md` §5 compares this with merger.
    """

    obligation_ids: tuple[str, ...]
    certificate: str
    authorization: str
    grounds: str = ""


@dataclass(frozen=True)
class FileResponse(Event):
    response: Response


@dataclass(frozen=True)
class Cover(Event):
    """One edge of `Answers subset R x D`, with its own adequacy certificate."""

    response_id: str
    obligation_id: str
    adequacy_ref: str
    authorization: str
    identification_ref: str | None = None


@dataclass(frozen=True)
class Discharge(Event):
    obligation_id: str
    coverage_event_id: str


@dataclass(frozen=True)
class Dispose(Event):
    obligation_id: str
    kind: str
    witness: str
    authorization: str


@dataclass(frozen=True)
class ProceduralClosure(Event):
    """A decision obligation disposed of by schedule, not answered or abandoned.

    This is not a withdrawal and not a loss.  It says: a practical verdict issued
    under the frozen fallback, no substantive normative claim was endorsed,
    withdrawn, settled, or made true, no merits coverage was created, and the
    underlying normative material remains independently challengeable.
    """

    obligation_id: str
    fallback_verdict: str
    ruling_ref: str
    authorization: str


@dataclass(frozen=True)
class Reopen(Event):
    obligation_id: str
    undercutter_ref: str
    authorization: str


BOUNDARY_OUTCOMES = ("continue", "continue-suspended", "refine", "discharge",
                     "terminal", "procedural")


@dataclass(frozen=True)
class BoundaryDisposition(Event):
    """The one unambiguous outcome an open obligation receives at a boundary.

    Coordinated subrecords — a retarget together with a suspension — are named
    in `subrecords`; what may not happen is two top-level dispositions, or none.
    A coverage edge is not a disposition, and a filed response is not one.
    """

    obligation_id: str
    outcome: str
    authorization: str
    subrecords: tuple[str, ...] = ()


@dataclass(frozen=True)
class LedgerLog:
    log_id: str
    events: tuple[Event, ...] = ()

    def __add__(self, other: "LedgerLog") -> "LedgerLog":
        return LedgerLog(f"{self.log_id}+{other.log_id}", self.events + other.events)

    def prefix(self, version: int) -> "LedgerLog":
        return LedgerLog(f"{self.log_id}|<={version}",
                         tuple(e for e in self.events if e.version <= version))


# --------------------------------------------------------------------------
# Verdicts
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class LedgerObstruction:
    code: str
    obligation_ids: tuple[str, ...]
    event_id: str
    version: int
    detail: str


@dataclass(frozen=True)
class ObligationState:
    obligation: Obligation
    status: ObligationStatus
    carrier: str
    closure_kind: str | None
    closure_event: str | None
    coverage_events: tuple[str, ...]
    reopened: int


@dataclass(frozen=True)
class LedgerReport:
    log_id: str
    system: str
    accepted: bool
    live: Mapping[str, ObligationState]
    closed: Mapping[str, ObligationState]
    coverage: tuple[tuple[str, str, str], ...]
    obstructions: tuple[LedgerObstruction, ...]

    @property
    def open_ids(self) -> tuple[str, ...]:
        return tuple(sorted(
            identifier for identifier, state in self.live.items()
            if state.status is not ObligationStatus.CLOSED))


AdequacyOracle = Callable[[Cover, Obligation, Response], bool]


def structural_adequacy(cover: Cover, obligation: Obligation, response: Response) -> bool:
    """The parametric default: structure only, never substantive truth.

    The theorem in `ANSWERABILITY_LEDGER.md` §6 is stated for an arbitrary
    oracle; this one checks that an adequacy certificate was supplied and that
    the response is of the kind the question asks for.
    """
    return bool(cover.adequacy_ref) and response.kind == obligation.kind


def _issue(store: list[LedgerObstruction], code: str, obligations: Iterable[str],
           event: Event, detail: str) -> None:
    store.append(LedgerObstruction(code, tuple(sorted(obligations)), event.event_id,
                                   event.version, detail))


def verify_ledger(log: LedgerLog, *, system: str = SYSTEM_COVERAGE,
                  adequacy: AdequacyOracle = structural_adequacy,
                  transition_versions: Sequence[int] = ()) -> LedgerReport:
    """Fold the log and check the local transition conditions.

    Acceptance is never defined as "the global result is good": every condition
    below is a property of one event and the state it acts on.
    """
    if system not in SYSTEMS:
        raise ValueError(system)
    obstructions: list[LedgerObstruction] = []
    states: dict[str, ObligationState] = {}
    responses: dict[str, Response] = {}
    covers: dict[str, Cover] = {}
    identifications: dict[str, Identify] = {}
    refinements: dict[str, tuple[tuple[str, ...], str]] = {}
    covered_by_response: dict[str, list[str]] = {}
    seen_events: set[str] = set()
    last_version = None

    # 1.1 Global identifier integrity.  No later insertion may silently
    # overwrite an earlier record, and a linear ledger never travels backwards.
    for event in log.events:
        if event.event_id in seen_events:
            _issue(obstructions, "ledger.duplicate_event_id", (), event,
                   "an event identifier is reused")
        seen_events.add(event.event_id)
        if last_version is not None and event.version < last_version:
            _issue(obstructions, "ledger.version_out_of_order", (), event,
                   "a linear ledger may not append an event at an earlier version")
        last_version = event.version if last_version is None else max(last_version,
                                                                     event.version)

    def open_state(identifier: str) -> ObligationState | None:
        state = states.get(identifier)
        return state if state is not None else None

    for event in log.events:
        if isinstance(event, FileObligation):
            obligation = event.obligation
            if obligation.obligation_id in states:
                _issue(obstructions, "ledger.duplicate_obligation_id",
                       (obligation.obligation_id,), event,
                       "an obligation identifier is filed twice")
                continue
            if not obligation.basis:
                _issue(obstructions, "ledger.unauthorized_origin",
                       (obligation.obligation_id,), event,
                       "an obligation needs a named origin basis")
            if (obligation.origin_version, obligation.origin_event) != (
                    event.version, event.event_id):
                _issue(obstructions, "ledger.origin_not_bound_to_filing",
                       (obligation.obligation_id,), event,
                       "an obligation's origin must be the filing event that created it")
            states[obligation.obligation_id] = ObligationState(
                obligation, ObligationStatus.OPEN, obligation.carrier, None, None, (), 0)
        elif isinstance(event, FileResponse):
            if event.response.response_id in responses:
                _issue(obstructions, "ledger.duplicate_response_id", (), event,
                       "a response identifier is filed twice")
                continue
            responses[event.response.response_id] = event.response
        elif isinstance(event, Carry):
            state = open_state(event.obligation_id)
            if state is None:
                _issue(obstructions, "ledger.unknown_obligation",
                       (event.obligation_id,), event, "carry names no filed obligation")
                continue
            if state.status is ObligationStatus.CLOSED:
                _issue(obstructions, "ledger.event_on_closed_obligation",
                       (event.obligation_id,), event, "a closed obligation cannot be carried")
                continue
            if not event.authorization:
                _issue(obstructions, "ledger.unauthorized_transition",
                       (event.obligation_id,), event, "carry needs an authorization")
            states[event.obligation_id] = replace(state, carrier=event.carrier)
        elif isinstance(event, Suspend):
            state = open_state(event.obligation_id)
            if state is None or state.status is ObligationStatus.CLOSED:
                _issue(obstructions, "ledger.unknown_obligation",
                       (event.obligation_id,), event, "suspend names no open obligation")
                continue
            if not event.authorization or not event.reason:
                _issue(obstructions, "ledger.unauthorized_transition",
                       (event.obligation_id,), event,
                       "suspension needs a reason and an authorization")
            states[event.obligation_id] = replace(state, status=ObligationStatus.SUSPENDED)
        elif isinstance(event, Refine):
            state = open_state(event.parent_id)
            if state is None or state.status is ObligationStatus.CLOSED:
                _issue(obstructions, "ledger.unknown_obligation", (event.parent_id,),
                       event, "refine names no open parent obligation")
                continue
            if event.completion_rule not in COMPLETION_RULES:
                _issue(obstructions, "ledger.unknown_completion_rule",
                       (event.parent_id,), event, "refinement needs a declared rule")
            if not event.children:
                _issue(obstructions, "ledger.empty_refinement", (event.parent_id,), event,
                       "refinement needs at least one child obligation")
            for child in event.children:
                if child.obligation_id in states:
                    _issue(obstructions, "ledger.duplicate_obligation_id",
                           (child.obligation_id,), event, "child identifier already filed")
                    continue
                states[child.obligation_id] = ObligationState(
                    replace(child, lineage=child.lineage + (event.parent_id,)),
                    ObligationStatus.OPEN, child.carrier, None, None, (), 0)
            refinements[event.parent_id] = (
                tuple(c.obligation_id for c in event.children), event.completion_rule)
        elif isinstance(event, Identify):
            missing = [i for i in event.obligation_ids if i not in states]
            if missing or len(event.obligation_ids) < 2:
                _issue(obstructions, "ledger.unknown_obligation",
                       tuple(event.obligation_ids), event,
                       "identification needs at least two filed obligations")
                continue
            if not event.certificate or not event.authorization:
                _issue(obstructions, "ledger.identification_without_certificate",
                       event.obligation_ids, event,
                       "identification needs an explicit certificate and authorization")
                continue
            if event.grounds == "carrier-merger":
                _issue(obstructions, "ledger.identification_by_carrier_merger",
                       event.obligation_ids, event,
                       "two questions do not become one because their carriers merged")
                continue
            identifications[event.event_id] = event
        elif isinstance(event, Cover):
            obligation_state = states.get(event.obligation_id)
            response = responses.get(event.response_id)
            if obligation_state is None or response is None:
                _issue(obstructions, "ledger.unknown_coverage_endpoint",
                       (event.obligation_id,), event,
                       "a coverage edge names a missing response or obligation")
                continue
            if obligation_state.status is ObligationStatus.CLOSED:
                _issue(obstructions, "ledger.event_on_closed_obligation",
                       (event.obligation_id,), event,
                       "a closed obligation cannot receive new coverage")
                continue
            if not event.authorization:
                _issue(obstructions, "ledger.coverage_unauthorized",
                       (event.obligation_id,), event,
                       "a coverage edge needs an authorization")
                continue
            if not adequacy(event, obligation_state.obligation, response):
                _issue(obstructions, "ledger.coverage_inadequate",
                       (event.obligation_id,), event,
                       "the adequacy certificate does not admit this response for "
                       "this obligation")
                continue
            if event.identification_ref is not None:
                certificate = identifications.get(event.identification_ref)
                if certificate is None or event.obligation_id not in certificate.obligation_ids:
                    _issue(obstructions, "ledger.identification_not_licensed",
                           (event.obligation_id,), event,
                           "a coverage edge cites an identification that does not exist "
                           "or does not include this obligation")
                    continue
            shared = [
                other for other in covers.values()
                if other.response_id == event.response_id
                and other.adequacy_ref == event.adequacy_ref
                and other.obligation_id != event.obligation_id
            ]
            if shared and event.identification_ref is None:
                _issue(obstructions, "ledger.shared_adequacy_without_identification",
                       (event.obligation_id,) + tuple(o.obligation_id for o in shared), event,
                       "one adequacy argument may ground edges to several obligations "
                       "only when an identification certificate says they are the "
                       "same question")
                continue
            if system == SYSTEM_RIVALROUS and covered_by_response.get(event.response_id):
                _issue(obstructions, "ledger.response_not_rivalrous",
                       (event.obligation_id,), event,
                       "this system permits one response to answer only one obligation")
                continue
            if event.event_id in covers:
                _issue(obstructions, "ledger.duplicate_coverage_id", (), event,
                       "a coverage-edge identifier is reused")
                continue
            covered_by_response.setdefault(event.response_id, []).append(event.obligation_id)
            covers[event.event_id] = event
            states[event.obligation_id] = replace(
                obligation_state,
                coverage_events=obligation_state.coverage_events + (event.event_id,))
        elif isinstance(event, Discharge):
            state = states.get(event.obligation_id)
            if state is None:
                _issue(obstructions, "ledger.unknown_obligation",
                       (event.obligation_id,), event, "discharge names no filed obligation")
                continue
            if state.status is ObligationStatus.CLOSED:
                _issue(obstructions, "ledger.event_on_closed_obligation",
                       (event.obligation_id,), event, "already closed")
                continue
            cover = covers.get(event.coverage_event_id)
            if cover is None:
                _issue(obstructions, "ledger.discharge_without_coverage",
                       (event.obligation_id,), event,
                       "discharge needs an accepted coverage edge; a filed response "
                       "is not itself a discharge")
                continue
            if cover.obligation_id != event.obligation_id:
                _issue(obstructions, "ledger.implicit_co_discharge",
                       (event.obligation_id, cover.obligation_id), event,
                       "this coverage edge answers a different obligation; an "
                       "obligation is not discharged because another obligation on "
                       "the same carrier was answered")
                continue
            children, rule = refinements.get(event.obligation_id, ((), "none"))
            if children and not _completion_met(children, states, rule):
                _issue(obstructions, "ledger.parent_discharged_early",
                       (event.obligation_id,) + children, event,
                       f"the declared completion rule {rule!r} is not satisfied")
                continue
            states[event.obligation_id] = replace(
                state, status=ObligationStatus.CLOSED, closure_kind="discharge",
                closure_event=event.event_id)
        elif isinstance(event, Dispose):
            state = states.get(event.obligation_id)
            if state is None or state.status is ObligationStatus.CLOSED:
                _issue(obstructions, "ledger.unknown_obligation",
                       (event.obligation_id,), event, "dispose names no open obligation")
                continue
            if event.kind not in SUBSTANTIVE_CLOSURE_KINDS:
                _issue(obstructions, "ledger.invalid_disposition",
                       (event.obligation_id,), event,
                       "a substantive terminal disposition is a withdrawal or an "
                       "authorized loss; a scheduled default uses ProceduralClosure")
                continue
            if not event.witness or not event.authorization:
                _issue(obstructions, "ledger.unauthorized_transition",
                       (event.obligation_id,), event,
                       "a terminal disposition needs a witness and an authorization")
                continue
            states[event.obligation_id] = replace(
                state, status=ObligationStatus.CLOSED, closure_kind=event.kind,
                closure_event=event.event_id)
        elif isinstance(event, ProceduralClosure):
            state = states.get(event.obligation_id)
            if state is None or state.status is ObligationStatus.CLOSED:
                _issue(obstructions, "ledger.unknown_obligation",
                       (event.obligation_id,), event,
                       "procedural closure names no open obligation")
                continue
            if not event.authorization or not event.ruling_ref or not event.fallback_verdict:
                _issue(obstructions, "ledger.unauthorized_transition",
                       (event.obligation_id,), event,
                       "a procedural closure names its ruling, its fallback verdict, "
                       "and an authorization")
                continue
            if state.coverage_events:
                _issue(obstructions, "ledger.procedural_closure_with_coverage",
                       (event.obligation_id,), event,
                       "an obligation with merits coverage is not disposed of by schedule")
                continue
            states[event.obligation_id] = replace(
                state, status=ObligationStatus.CLOSED, closure_kind="procedural",
                closure_event=event.event_id)
        elif isinstance(event, Reopen):
            state = states.get(event.obligation_id)
            if state is None or state.status is not ObligationStatus.CLOSED:
                _issue(obstructions, "ledger.unknown_obligation",
                       (event.obligation_id,), event, "reopen names no closed obligation")
                continue
            if not event.undercutter_ref or not event.authorization:
                _issue(obstructions, "ledger.reopen_without_undercutter",
                       (event.obligation_id,), event,
                       "reopening needs a named undercutter and an authorization")
                continue
            states[event.obligation_id] = replace(
                state, status=ObligationStatus.OPEN, closure_kind=None,
                closure_event=None, reopened=state.reopened + 1)

    # 1.3 Atomic migration-boundary dispositions.  Exactly one coherent
    # top-level disposition per obligation open immediately before the boundary.
    by_event = {event.event_id: event for event in log.events}
    for version in transition_versions:
        marker = Event(f"transition:{version}", version)
        dispositions: dict[str, list[BoundaryDisposition]] = {}
        for event in log.events:
            if isinstance(event, BoundaryDisposition) and event.version == version:
                dispositions.setdefault(event.obligation_id, []).append(event)
        before = _fold_status(log.prefix(version - 1), system, adequacy)
        for identifier, status in sorted(before.items()):
            if status is ObligationStatus.CLOSED:
                continue
            declared = dispositions.get(identifier, [])
            if not declared:
                _issue(obstructions, "ledger.no_boundary_disposition", (identifier,),
                       marker, "an open obligation crosses a migration with no "
                               "top-level disposition; coverage and responses are "
                               "not dispositions")
                continue
            if len(declared) > 1:
                _issue(obstructions, "ledger.conflicting_boundary_disposition",
                       (identifier,), marker,
                       f"{len(declared)} top-level dispositions for one obligation")
                continue
            disposition = declared[0]
            if disposition.outcome not in BOUNDARY_OUTCOMES:
                _issue(obstructions, "ledger.unknown_boundary_outcome", (identifier,),
                       disposition, "unknown boundary outcome")
            if not disposition.authorization:
                _issue(obstructions, "ledger.unauthorized_boundary_disposition",
                       (identifier,), disposition,
                       "a boundary disposition needs an authorization")
            final = states.get(identifier)
            closed = final is not None and final.status is ObligationStatus.CLOSED
            if disposition.outcome in ("discharge", "terminal", "procedural") and not closed:
                _issue(obstructions, "ledger.boundary_outcome_unrealized",
                       (identifier,), disposition,
                       "the declared outcome closes the obligation but it is still open")
            if disposition.outcome in ("continue", "continue-suspended") and closed:
                _issue(obstructions, "ledger.boundary_outcome_unrealized",
                       (identifier,), disposition,
                       "the declared outcome continues the obligation but it was closed")
            _check_boundary_subrecords(obstructions, disposition, identifier, final,
                                       by_event, covers, version)
        claimed: dict[str, str] = {}
        for identifier, declared in sorted(dispositions.items()):
            for disposition in declared:
                for reference in disposition.subrecords:
                    owner = claimed.get(reference)
                    if owner is not None and owner != identifier:
                        _issue(obstructions, "ledger.subrecord_reused",
                               (identifier, owner), disposition,
                               "one ledger record cannot dispose of two obligations")
                    claimed[reference] = identifier
        for identifier in sorted(dispositions):
            if identifier not in before:
                _issue(obstructions, "ledger.boundary_disposition_without_obligation",
                       (identifier,), marker,
                       "a boundary disposition names an obligation that was not open")

    live = {i: s for i, s in states.items() if s.status is not ObligationStatus.CLOSED}
    closed = {i: s for i, s in states.items() if s.status is ObligationStatus.CLOSED}
    coverage = tuple(sorted(
        (cover.response_id, cover.obligation_id, cover.adequacy_ref)
        for cover in covers.values()))
    return LedgerReport(log.log_id, system, not obstructions, live, closed, coverage,
                        tuple(obstructions))


_OUTCOME_REQUIREMENTS = {
    "continue": (Carry,),
    "continue-suspended": (Suspend,),
    "refine": (Refine,),
    "discharge": (Discharge,),
    "terminal": (Dispose,),
    "procedural": (ProceduralClosure,),
}


def _check_boundary_subrecords(obstructions: list[LedgerObstruction],
                               disposition: BoundaryDisposition, identifier: str,
                               final: ObligationState | None,
                               by_event: Mapping[str, Event],
                               covers: Mapping[str, Cover], version: int) -> None:
    """Every named subrecord must exist, concern this obligation, occur at this
    version, have the claimed type, and justify the declared outcome."""
    required = _OUTCOME_REQUIREMENTS.get(disposition.outcome, ())
    if not disposition.subrecords:
        _issue(obstructions, "ledger.boundary_without_subrecords", (identifier,),
               disposition, "a boundary disposition names the records that realize it")
        return
    found: list[Event] = []
    for reference in disposition.subrecords:
        event = by_event.get(reference)
        if event is None:
            _issue(obstructions, "ledger.boundary_subrecord_missing",
                   (identifier,), disposition, f"subrecord {reference!r} does not exist")
            continue
        target = (getattr(event, "obligation_id", None)
                  or getattr(event, "parent_id", None))
        if target != identifier:
            _issue(obstructions, "ledger.boundary_subrecord_foreign", (identifier,),
                   disposition,
                   f"subrecord {reference!r} concerns obligation {target!r}")
            continue
        if event.version != version:
            _issue(obstructions, "ledger.boundary_subrecord_version", (identifier,),
                   disposition, f"subrecord {reference!r} occurs at another version")
            continue
        found.append(event)
    if required and not any(isinstance(e, required) for e in found):
        _issue(obstructions, "ledger.boundary_subrecord_type", (identifier,),
               disposition,
               f"outcome {disposition.outcome!r} needs a "
               f"{required[0].__name__} record among its subrecords")
        return
    if disposition.outcome == "continue-suspended" and (
            final is None or final.status is not ObligationStatus.SUSPENDED):
        _issue(obstructions, "ledger.boundary_outcome_unrealized", (identifier,),
               disposition, "the declared outcome suspends but the obligation is not "
                            "suspended")
    if disposition.outcome == "discharge":
        discharge = next(e for e in found if isinstance(e, Discharge))
        if discharge.coverage_event_id not in covers:
            _issue(obstructions, "ledger.boundary_discharge_without_coverage",
                   (identifier,), disposition,
                   "the named discharge cites no accepted coverage edge")
    if disposition.outcome == "terminal":
        closure = next(e for e in found if isinstance(e, Dispose))
        if closure.kind not in SUBSTANTIVE_CLOSURE_KINDS:
            _issue(obstructions, "ledger.boundary_subrecord_type", (identifier,),
                   disposition, "a terminal outcome names a substantive withdrawal "
                                "or loss")


def _completion_met(children: Sequence[str], states: Mapping[str, ObligationState],
                    rule: str) -> bool:
    closed = [states[c].status is ObligationStatus.CLOSED for c in children if c in states]
    if rule == "all":
        return bool(closed) and all(closed)
    if rule == "any":
        return any(closed)
    return True


def _fold_status(log: LedgerLog, system: str,
                 adequacy: AdequacyOracle) -> Mapping[str, ObligationStatus]:
    report = verify_ledger(log, system=system, adequacy=adequacy)
    return {i: s.status for i, s in list(report.live.items()) + list(report.closed.items())}


# --------------------------------------------------------------------------
# Composition
# --------------------------------------------------------------------------


def compose_ledgers(*logs: LedgerLog) -> LedgerLog:
    """Composition of ledger histories is concatenation of append-only logs."""
    if not logs:
        return LedgerLog("empty", ())
    composed = logs[0]
    for other in logs[1:]:
        composed = composed + other
    return composed


def live_state(report: LedgerReport) -> Mapping[str, tuple[str, str]]:
    """What is still owed: obligation to `(status, carrier)`."""
    return {i: (s.status.value, s.carrier) for i, s in sorted(report.live.items())}


def historical_state(report: LedgerReport) -> Mapping[str, tuple[str, str | None]]:
    """What is settled: obligation to `(closure kind, closure event)`."""
    return {i: (s.closure_kind or "", s.closure_event)
            for i, s in sorted(report.closed.items())}


# --------------------------------------------------------------------------
# The benchmark examples of `ANSWERABILITY_LEDGER.md` §5
# --------------------------------------------------------------------------

EXAMPLES = ("A", "B", "C", "D", "E", "F", "G")


def _obligation(identifier: str, carrier: str, event_id: str, kind: str = "justify",
                version: int = 0) -> Obligation:
    """Origin is bound to the filing event that will carry this obligation."""
    return Obligation(identifier, kind, version, event_id, "auth:challenge", carrier)


def example(name: str) -> tuple[LedgerLog, tuple[int, ...]]:
    """One finite ledger history per benchmark, with its transition versions."""
    d_a = _obligation("d:A", "claim:A", "e:file-A")
    d_b = _obligation("d:B", "claim:B", "e:file-B")
    file_a = FileObligation("e:file-A", 0, d_a)
    file_b = FileObligation("e:file-B", 0, d_b)
    merge_a = Carry("e:carry-A", 1, "d:A", "claim:C", "auth:migration")
    merge_b = Carry("e:carry-B", 1, "d:B", "claim:C", "auth:migration")
    response = FileResponse("e:resp", 1, Response("r:1", "justify", 1, "auth:filing"))
    close = lambda tag, obligation, subs: BoundaryDisposition(
        tag, 1, obligation, "discharge", "auth:migration", subs)
    keep = lambda tag, obligation, subs: BoundaryDisposition(
        tag, 1, obligation, "continue", "auth:migration", subs)

    if name == "A":
        # Two obligations merge onto one carrier; only d:A is covered.
        return LedgerLog("ledger:A", (
            file_a, file_b, merge_a, merge_b, response,
            Cover("e:cover-A", 1, "r:1", "d:A", "adequacy:A", "auth:review"),
            Discharge("e:disc-A", 1, "d:A", "e:cover-A"),
            close("e:bd-A", "d:A", ("e:cover-A", "e:disc-A")),
            keep("e:bd-B", "d:B", ("e:carry-B",)),
        )), (1,)
    if name == "B":
        # The same response independently satisfies both, with two edges.
        return LedgerLog("ledger:B", (
            file_a, file_b, merge_a, merge_b, response,
            Cover("e:cover-A", 1, "r:1", "d:A", "adequacy:A", "auth:review"),
            Cover("e:cover-B", 1, "r:1", "d:B", "adequacy:B", "auth:review"),
            Discharge("e:disc-A", 1, "d:A", "e:cover-A"),
            Discharge("e:disc-B", 1, "d:B", "e:cover-B"),
            close("e:bd-A", "d:A", ("e:cover-A", "e:disc-A")),
            close("e:bd-B", "d:B", ("e:cover-B", "e:disc-B")),
        )), (1,)
    if name == "C":
        # Identification grounded only in the carriers having merged.
        return LedgerLog("ledger:C", (
            file_a, file_b, merge_a, merge_b,
            Identify("e:ident", 1, ("d:A", "d:B"), "certificate:same-carrier",
                     "auth:review", "carrier-merger"),
            keep("e:bd-A", "d:A", ("e:carry-A",)),
            keep("e:bd-B", "d:B", ("e:carry-B",)),
        )), (1,)
    if name == "D":
        # Two duplicate filings, identified by certificate, each discharged by
        # its own edge grounded in one shared adequacy argument.
        return LedgerLog("ledger:D", (
            file_a, file_b, merge_a, merge_b,
            Identify("e:ident", 1, ("d:A", "d:B"), "certificate:same-question",
                     "auth:review", "equivalence-argument"),
            response,
            Cover("e:cover-A", 1, "r:1", "d:A", "adequacy:shared", "auth:review",
                  "e:ident"),
            Cover("e:cover-B", 1, "r:1", "d:B", "adequacy:shared", "auth:review",
                  "e:ident"),
            Discharge("e:disc-A", 1, "d:A", "e:cover-A"),
            Discharge("e:disc-B", 1, "d:B", "e:cover-B"),
            close("e:bd-A", "d:A", ("e:cover-A", "e:disc-A")),
            close("e:bd-B", "d:B", ("e:cover-B", "e:disc-B")),
        )), (1,)
    if name == "E":
        # Refinement: answering one child must not close the parent under "all".
        child_one = _obligation("d:A1", "claim:A1", "e:refine", version=1)
        child_two = _obligation("d:A2", "claim:A2", "e:refine", version=1)
        return LedgerLog("ledger:E", (
            file_a,
            Refine("e:refine", 1, "d:A", (child_one, child_two), "all", "auth:review"),
            response,
            Cover("e:cover-A1", 1, "r:1", "d:A1", "adequacy:A1", "auth:review"),
            Cover("e:cover-A", 1, "r:1", "d:A", "adequacy:A", "auth:review"),
            Discharge("e:disc-A1", 1, "d:A1", "e:cover-A1"),
            Discharge("e:disc-parent", 1, "d:A", "e:cover-A"),
        )), ()
    if name == "F":
        # Discharge, then an undercutter reopens without erasing history.
        return LedgerLog("ledger:F", (
            file_a, response,
            Cover("e:cover-A", 1, "r:1", "d:A", "adequacy:A", "auth:review"),
            Discharge("e:disc-A", 1, "d:A", "e:cover-A"),
            Reopen("e:reopen", 2, "d:A", "undercutter:u1", "auth:review"),
        )), ()
    if name == "G":
        # The endpoint ontology cannot express the target: retarget and suspend,
        # coordinated under one top-level disposition.
        return LedgerLog("ledger:G", (
            file_a,
            Carry("e:legacy", 1, "d:A", "legacy:claim:A", "auth:migration"),
            Suspend("e:susp", 1, "d:A", "inexpressible in the endpoint ontology",
                    "auth:review"),
            BoundaryDisposition("e:bd-A", 1, "d:A", "continue-suspended",
                                "auth:migration", ("e:legacy", "e:susp")),
        )), (1,)
    raise ValueError(name)


# --------------------------------------------------------------------------
# Bounded adversarial search over the three systems
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SystemComparison:
    scenarios: int
    accepted: Mapping[str, int]
    unsafe_accepted: Mapping[str, int]
    legitimate_shared_accepted: Mapping[str, int]
    strictly_more_expressive: bool
    equally_safe: bool
    expressiveness_witnesses: tuple[str, ...]
    safety_witnesses: tuple[str, ...]


def _scenarios() -> Iterable[tuple[str, LedgerLog, bool, bool]]:
    """Small logs over at most two obligations and two responses.

    Yields `(name, log, unsafe, legitimate_shared)` where the two flags are the
    ground truth computed from the raw records, independently of any system.
    """
    obligations = (_obligation("d:0", "claim:0", "e:file0"),
                   _obligation("d:1", "claim:1", "e:file1"))
    for obligation_count in (1, 2):
        for response_count in (1, 2):
            targets = obligations[:obligation_count]
            pairs = [(f"r:{r}", o.obligation_id)
                     for r in range(response_count) for o in targets]
            for cover_mask in range(1 << len(pairs)):
                chosen = [p for index, p in enumerate(pairs) if cover_mask >> index & 1]
                for discharge_mask in range(1 << obligation_count):
                    discharged = [targets[i].obligation_id
                                  for i in range(obligation_count)
                                  if discharge_mask >> i & 1]
                    events: list[Event] = [
                        FileObligation(f"e:file{i}", 0, o)
                        for i, o in enumerate(targets)]
                    events += [FileResponse(f"e:resp{r}", 0,
                                            Response(f"r:{r}", "justify", 0, "auth:filing"))
                               for r in range(response_count)]
                    events += [Cover(f"e:cov{i}", 0, response, obligation,
                                     f"adequacy:{i}", "auth:review")
                               for i, (response, obligation) in enumerate(chosen)]
                    covered = {o: f"e:cov{i}" for i, (_, o) in enumerate(chosen)}
                    events += [Discharge(f"e:dis{i}", 0, o,
                                         covered.get(o, "e:missing"))
                               for i, o in enumerate(discharged)]
                    unsafe = any(o not in covered for o in discharged)
                    shared = any(
                        len([o for r, o in chosen if r == response]) > 1
                        and all(o in discharged for r, o in chosen if r == response)
                        and len(discharged) > 1
                        for response in {r for r, _ in chosen})
                    name = f"s:{obligation_count}{response_count}:{cover_mask}:{discharge_mask}"
                    yield name, LedgerLog(name, tuple(events)), unsafe, shared


def compare_systems() -> SystemComparison:
    """Is certified coverage strictly more expressive than rivalrous witnesses,
    while remaining exactly as safe against the failures the bit system misses?
    """
    accepted = {system: 0 for system in SYSTEMS}
    unsafe_accepted = {system: 0 for system in SYSTEMS}
    shared_accepted = {system: 0 for system in SYSTEMS}
    expressiveness: list[str] = []
    safety: list[str] = []
    total = 0
    for name, log, unsafe, shared in _scenarios():
        total += 1
        verdicts = {}
        for system in SYSTEMS:
            if system == SYSTEM_BIT:
                # No obligation identity: a discharge closes every obligation
                # sharing the carrier of the one it names, and needs no edge.
                ok = True
            else:
                ok = verify_ledger(log, system=system).accepted
            verdicts[system] = ok
            accepted[system] += int(ok)
            if ok and unsafe:
                unsafe_accepted[system] += 1
            if ok and shared:
                shared_accepted[system] += 1
        if verdicts[SYSTEM_COVERAGE] and not verdicts[SYSTEM_RIVALROUS] and shared:
            expressiveness.append(name)
        if verdicts[SYSTEM_COVERAGE] and unsafe:
            safety.append(name)
    return SystemComparison(
        total, accepted, unsafe_accepted, shared_accepted,
        bool(expressiveness) and unsafe_accepted[SYSTEM_COVERAGE] == 0,
        unsafe_accepted[SYSTEM_COVERAGE] == unsafe_accepted[SYSTEM_RIVALROUS] == 0,
        tuple(expressiveness[:5]), tuple(safety[:5]),
    )


# --------------------------------------------------------------------------
# Accepted-segment composition (Gate 1.4)
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SegmentComposition:
    """The exact contract.  `accepted` is the conjunction of all four clauses.

    `second_accepted_under_state` is the acceptance of the second segment's
    events folded onto the state the first segment produced — which is what the
    composite fold checks for exactly those events, and is the only sense in
    which the second segment is verified "under the resulting state".
    """

    composed: LedgerLog
    first_accepted: bool
    compatible: bool
    second_accepted_under_state: bool
    composite_accepted: bool
    obstructions: tuple[LedgerObstruction, ...]

    @property
    def accepted(self) -> bool:
        return (self.first_accepted and self.compatible
                and self.second_accepted_under_state and self.composite_accepted)


def _declared(log: LedgerLog) -> tuple[set[str], set[str], set[str], set[str]]:
    events, obligations, responses, covers = set(), set(), set(), set()
    for event in log.events:
        events.add(event.event_id)
        if isinstance(event, FileObligation):
            obligations.add(event.obligation.obligation_id)
        elif isinstance(event, Refine):
            obligations.update(c.obligation_id for c in event.children)
        elif isinstance(event, FileResponse):
            responses.add(event.response.response_id)
        elif isinstance(event, Cover):
            covers.add(event.event_id)
    return events, obligations, responses, covers


def compose_segments(first: LedgerLog, second: LedgerLog, *,
                     system: str = SYSTEM_COVERAGE,
                     adequacy: AdequacyOracle = structural_adequacy,
                     transition_versions: Sequence[int] = ()) -> SegmentComposition:
    """Compose two independently accepted segments into a linear history.

    Concatenation alone is not the composition theorem.  The content is the
    compatibility conditions: identifier freshness across the seam, nondecreasing
    versions, an active-obligation set the second segment may legitimately act
    on, and no reference to an object the composite does not supply.
    """
    obstructions: list[LedgerObstruction] = []
    composed = first + second
    marker = Event("seam", second.events[0].version if second.events else 0)

    first_events, first_obligations, first_responses, first_covers = _declared(first)
    second_events, second_obligations, second_responses, second_covers = _declared(second)
    for label, shared in (("event", first_events & second_events),
                          ("obligation", first_obligations & second_obligations),
                          ("response", first_responses & second_responses),
                          ("coverage", first_covers & second_covers)):
        if shared:
            _issue(obstructions, "ledger.segment_identifier_collision", sorted(shared),
                   marker, f"the segments reuse a {label} identifier across the seam")

    if first.events and second.events:
        if second.events[0].version < first.events[-1].version:
            _issue(obstructions, "ledger.segment_version_regression", (), marker,
                   "the second segment opens at an earlier version than the first closes")

    opening = verify_ledger(first, system=system, adequacy=adequacy)
    if not opening.accepted:
        _issue(obstructions, "ledger.segment_not_accepted", (), marker,
               "the first segment is not accepted on its own")
    available = set(opening.live) | second_obligations
    closed_before = set(opening.closed)
    for event in second.events:
        target = getattr(event, "obligation_id", None) or getattr(event, "parent_id", None)
        if target is None or isinstance(event, FileObligation):
            continue
        if isinstance(event, Reopen):
            continue
        if target in closed_before:
            _issue(obstructions, "ledger.segment_acts_on_closed_obligation", (target,),
                   event, "the second segment acts on an obligation the first closed")
        elif target not in available:
            _issue(obstructions, "ledger.segment_dangling_reference", (target,), event,
                   "the second segment references an obligation no segment supplies")
        if isinstance(event, Cover) and event.response_id not in (
                first_responses | second_responses):
            _issue(obstructions, "ledger.segment_dangling_reference",
                   (event.response_id,), event,
                   "a coverage edge references a response no segment files")
    composite = verify_ledger(composed, system=system, adequacy=adequacy,
                              transition_versions=transition_versions)
    seam_events = {event.event_id for event in second.events}
    second_under_state = not [
        witness for witness in composite.obstructions
        if witness.event_id in seam_events
    ]
    if not second_under_state:
        _issue(obstructions, "ledger.second_segment_rejected_under_state", (), marker,
               "the second segment's events are not accepted on the state the first "
               "segment produced")
    if not composite.accepted:
        _issue(obstructions, "ledger.composite_not_accepted", (), marker,
               "the concatenated history is not accepted")
    return SegmentComposition(composed, opening.accepted, not obstructions,
                              second_under_state, composite.accepted,
                              tuple(obstructions))
