"""The settlement interface as a formal object.

The composite guarantee is stated over *any* engine satisfying the settlement
interface, with specific engines entering only as witnesses.  That phrasing has
no force until "engine satisfying the interface" is a single formal referent
that a theorem can quantify over.  This module is that referent.

Every clause of the interface appears here as one predicate, carrying the
clause's text verbatim in its docstring, and each is one of two kinds:

- **checkable** -- a computable predicate over declared engine data and a finite
  record prefix.  It returns a verdict with obstructions, and nothing about it
  is taken on anyone's word.
- **declared** -- a hypothesis object carrying its own statement.  The assumed
  residue and the asymptotic halves of the clock and tolerance clauses cannot be
  decided from a finite prefix, so they are *named and carried*, never quietly
  discharged.  A declared clause holds exactly when a matching hypothesis object
  is supplied, and the report says which ones were leaned on.

The split is the honesty mechanism.  An engine that satisfies every checkable
clause has been checked; an engine that satisfies the interface has been checked
*plus* a named list of things nobody checked, and the list is printed.

`ReferenceEngine` is the existence proof that the checkable fragment is jointly
satisfiable: a finite lookup-table pen with declared horizons and a refusing
purse, which is the smallest thing that is an engine at all.

Finiteness discipline.  Procedures, pins, requests, and dates in a record prefix
are finite; every predicate is a total function of that finite prefix.  Nothing
allocates state that grows with date.

All arithmetic is exact rationals.  No floating point.
"""

from __future__ import annotations

from dataclasses import dataclass, field, fields
from fractions import Fraction as Q
from typing import Mapping, Protocol, Sequence, runtime_checkable

from src.coherence import (
    ToleranceDeclaration,
    ToleranceSchedule,
    attribute_breach,
    incoherence,
)
from src.core_geometry import QUARANTINE_OF_FORCE, core_admission
from src.leverage_interval import Book, Language, SettledFact

LOGICAL = "logical"
EMPIRICAL = "empirical"
CHANNELS = (LOGICAL, EMPIRICAL)

ENGINE_INTRINSIC = "E"
MECHANISM_COMPATIBILITY = "M"
CONDUCT_PROTOCOL = "P"

CHECKABLE = "checkable"
DECLARED = "declared"

# Means by which an engine may establish its downside limit (interface P2).
REFUSAL = "refusal"
BOUNDED_BUDGETS = "bounded-budgets"
DOWNSIDE_MEANS = (REFUSAL, BOUNDED_BUDGETS)


# --------------------------------------------------------------------------
# The clause texts, verbatim
# --------------------------------------------------------------------------

CLAUSE_TEXT: Mapping[str, str] = {
    "J1": (
        "(J1) Declared settleable class. The engine declares, as public record, "
        "the procedures it owns, each with its outcome space, channel (logical or "
        "empirical), and - where applicable (C1) - horizon. The settleable class "
        "is the induced family of report variables; nothing outside it is "
        "pinnable by this engine."),
    "J2": (
        "(J2) Write-once, owner-only. Every report variable is pinnable exactly "
        "once, and only by the engine owning its procedure. That is the entire "
        "exclusivity clause, and it makes cross-pin conflict vacuous by "
        "construction: no variable has two pinners or two pins."),
    "J3": (
        "(J3) Migration transport: bridge, never re-settle. Under ontology "
        "migration, pins are historical record and are never re-spoken in the new "
        "vocabulary. Translated content reaches the new ontology through migration "
        "cells in the answerable layer."),
    "C1-logical": (
        "(C1) Completeness, split by channel. Logical channel: define "
        "operationally D-infinity = {phi : the declared deductive process "
        "eventually proves or refutes phi}. The completeness clause is that "
        "D-infinity contains the declared logical jurisdiction - every sentence "
        "the engine claims for deduction is eventually settled - with no rate "
        "promised."),
    "C1-empirical": (
        "(C1) Completeness, split by channel. Empirical channel: "
        "funding-responsive completeness over the declared observable class - "
        "every report variable in the class settles if its procedure is funded "
        "and run, with a declared horizon per procedure."),
    "C2": (
        "(C2) Ripeness and tolling. At admission: a query whose merits would "
        "require settlement faster than a declared horizon is unripe - deferred "
        "without liability. At runtime: settlement arriving later than its "
        "declared horizon, and all dependence on the rateless logical channel, "
        "tolls the affected refusal clocks."),
    "C3": (
        "(C3) Adequacy. The docket's schedules, admission capacity, and deadline "
        "structure must be adequate relative to the declared horizons: an "
        "inequality relating downstream deadlines to upstream horizons, stated per "
        "instance and checkable."),
    "P1": (
        "(P1) Enforcement [minimum]. The engine certifies a fixed core "
        "coefficient theta > 0 (or a [minimum] theta_min for a varying core). The "
        "operative-force cap is void under theta_t -> 0; an engine whose "
        "conviction decays delivers force that evaporates. The [minimum] is a "
        "certified, verifiable commitment."),
    "P2": (
        "(P2) Downside establishment. The engine guarantees a worldwise downside "
        "[limit] -B against the book's holdings. The means are engine-specific - "
        "market refusal where the engine may refuse trades; bounded aggregate "
        "trader budgets where it may not - but the abstract requirement is "
        "uniform, and the establishing means must be declared."),
    "P3": (
        "(P3) Finite gating. Engine-facing instruments are gated: finitely many "
        "live per date, admitted under a fair (finite-overtaking) queue."),
    "P4": (
        "(P4) Declared certificate type. The engine names the soundness guarantee "
        "its belief/pricing process carries - market non-exploitation, minimax "
        "regret, Ville-style validity, conformal coverage, or another declared "
        "type - and the composite guarantee's empirical conjunct is stated "
        "relative to the declared type."),
    "T1": (
        "(T1) [tolerance]-schedule. Engines whose price/belief states are only "
        "approximately coherent at finite times declare a tolerance schedule "
        "epsilon_t. Downstream, the docket runs the robust interval, merits "
        "certificate, and sure-loss objection against the declared schedule; an "
        "exactly coherent engine declares epsilon_t = 0 and the robust forms "
        "reduce to the exact ones."),
    "T2": (
        "(T2) Certification layering. The engine certifies [minimums] (its "
        "epsilon-schedule and horizons); breach of a certified [minimum] is the "
        "engine's, handled by section 7. The book may voluntarily declare tighter "
        "working tolerances or deadlines; breach of a self-declared tighter bound "
        "is the book's, and chargeable - it assumed the risk."),
    "F1": (
        "(F1) Request-keyed subsidy. Subsidies attach syntactically to a "
        "SettlementRequestKey: (target report variable, or theorem-question for "
        "the logical channel; procedure; funder identity; timing). A request key "
        "names a question, never an outcome, so directional funding - 'pay to "
        "settle X at v' - is inexpressible, not merely forbidden."),
    "F2": (
        "(F2) Stopping neutrality. The funder's stopping policy must create no "
        "directional bias in what gets certified. Two named witnesses satisfy it: "
        "a precommitted stopping rule (fixed-horizon experiments), or an "
        "optional-stopping-safe (anytime-valid) certificate."),
    "F3": (
        "(F3) Probe blackout. The funder of a settlement request takes no fresh "
        "positions on its target between funding and pin - the insider pattern of "
        "the corpus's conduct machinery, extended verbatim: blackout window, "
        "disgorgement on violation, one checkable objection type."),
    "F4": (
        "(F4) Funder provenance. Funding profiles are recorded per pin, feeding "
        "the common-source objection surface when one purse bankrolls all premises "
        "of one conclusion."),
    "S8-logical": (
        "Logical channel - [checker] trust. Logical pins are proof-carrying: a pin "
        "on a theorem-question ships a derivation certificate checkable by a fixed "
        "proof [checker]. Derivation is therefore auditable; what remains assumed "
        "is the [checker] itself (soundness of the checker) and the boundedness of "
        "discovery."),
}

CLAUSE_LEVEL: Mapping[str, str] = {
    "J1": ENGINE_INTRINSIC, "J2": ENGINE_INTRINSIC, "J3": MECHANISM_COMPATIBILITY,
    "C1-logical": ENGINE_INTRINSIC, "C1-empirical": ENGINE_INTRINSIC,
    "C2": MECHANISM_COMPATIBILITY, "C3": MECHANISM_COMPATIBILITY,
    "P1": MECHANISM_COMPATIBILITY, "P2": MECHANISM_COMPATIBILITY,
    "P3": MECHANISM_COMPATIBILITY, "P4": ENGINE_INTRINSIC,
    "T1": ENGINE_INTRINSIC, "T2": ENGINE_INTRINSIC,
    "F1": CONDUCT_PROTOCOL, "F2": CONDUCT_PROTOCOL, "F3": CONDUCT_PROTOCOL,
    "F4": CONDUCT_PROTOCOL, "S8-logical": ENGINE_INTRINSIC,
}


# --------------------------------------------------------------------------
# Record citizens
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Procedure:
    """A declared procedure: what the engine owns, and on what terms."""

    procedure_id: str
    channel: str
    outcome_space: tuple[str, ...]
    owner: str
    horizon: int | None = None

    def well_formed(self) -> bool:
        if self.channel not in CHANNELS or len(set(self.outcome_space)) < 2:
            return False
        if self.channel == EMPIRICAL:
            return self.horizon is not None and self.horizon >= 0
        return self.horizon is None


def report_variable(procedure_id: str, date: int) -> str:
    """The report variable of a declared procedure executed at a date."""
    return f"X[{procedure_id}@{date}]"


@dataclass(frozen=True)
class Pin:
    """A dated record event `(report variable, value)`.

    Defined as much by its absences: no basis tag, no stake, no charge stream,
    no objection surface.  `funder_profile` is provenance *about* the pin, read
    by the common-source surface; it is not a column the pin answers for.
    """

    variable_id: str
    procedure_id: str
    date: int
    value: str
    funder_profile: tuple[str, ...] = ()
    derivation: str | None = None
    era: int = 0


@dataclass(frozen=True)
class SettlementRequestKey:
    """A key names a *question*, never an outcome.

    The type is the enforcement.  There is no field in which an outcome could be
    written, so "pay to settle X at v" is not a forbidden request -- it is an
    unconstructible one.  `directional_variants` is the check: the set of keys
    reachable by varying an intended outcome is a single point.
    """

    target: str
    procedure_id: str
    funder_id: str
    requested_date: int
    scheduled_date: int

    @property
    def key_id(self) -> str:
        return (f"key[{self.target}|{self.procedure_id}|{self.funder_id}"
                f"|{self.requested_date}->{self.scheduled_date}]")


def key_field_names() -> tuple[str, ...]:
    return tuple(f.name for f in fields(SettlementRequestKey))


def key_from_intent(target: str, procedure_id: str, funder_id: str,
                    requested_date: int, scheduled_date: int,
                    intended_outcome: str) -> SettlementRequestKey:
    """The key a funder holding an intended outcome is able to write.

    The intended outcome is the one argument with no field to land in.  It is
    dropped here, in the open, and that is the whole of the typed obstruction:
    the map from funding intents to keys forgets the direction, so two funders
    intending opposite settlements of one question write the *same* key.
    """
    del intended_outcome
    return SettlementRequestKey(target, procedure_id, funder_id, requested_date,
                                scheduled_date)


def directional_variants(key: SettlementRequestKey,
                         outcome_space: Sequence[str],
                         ) -> frozenset[SettlementRequestKey]:
    """The image of one question's funding intents under key construction.

    Directional funding is inexpressible exactly when this image is a single
    point for every outcome space: no intended outcome leaves a trace.
    """
    return frozenset(
        key_from_intent(key.target, key.procedure_id, key.funder_id,
                        key.requested_date, key.scheduled_date, outcome)
        for outcome in (tuple(outcome_space) or ("",)))


PRECOMMITTED = "precommitted"
ANYTIME_VALID = "anytime-valid"


@dataclass(frozen=True)
class FundedRequest:
    """A subsidy attached to a key, with its stopping rule and blackout window."""

    request_id: str
    key: SettlementRequestKey
    subsidy: Q
    stopping_rule: str = PRECOMMITTED
    declared_stop: int | None = None
    executed_date: int | None = None
    pinned_variable: str | None = None


@dataclass(frozen=True)
class Position:
    """A position an actor took on a target at a date."""

    actor_id: str
    target: str
    date: int
    fresh: bool = True


@dataclass(frozen=True)
class AdmittedQuery:
    """A docket query with its clock facts, as the record shows them."""

    query_id: str
    admitted_date: int
    deadline: int
    upstream: tuple[str, ...] = ()
    service_work: Q = Q(1)
    ripe: bool = True
    tolled: bool = False
    liability: Q = Q(0)


@dataclass(frozen=True)
class DocketFacts:
    capacity: Q = Q(1)
    queries: tuple[AdmittedQuery, ...] = ()


@dataclass(frozen=True)
class EraFacts:
    """Migration eras and the translation of old vocabulary into new."""

    boundaries: tuple[int, ...] = ()
    translations: tuple[tuple[str, str], ...] = ()

    def era_of(self, date: int) -> int:
        return sum(1 for boundary in self.boundaries if date >= boundary)


@dataclass(frozen=True)
class PricedState:
    """The engine's priced state at a date, with the region it induces.

    This is what makes the tolerance and core clauses *checkable* rather than
    reported: the realized incoherence and the core admissibility are computed
    here from the same objects the docket computes its interval from.
    """

    date: int
    language: Language
    book: Book
    settled: tuple[SettledFact, ...]
    prices: object | None = None          # a `coherence.PriceAssignment`


@dataclass(frozen=True)
class BreachRecord:
    date: int
    declaration: ToleranceDeclaration
    realized: Q
    attributed_to: str
    tolled: bool
    chargeable: bool


@dataclass(frozen=True)
class SettlementRecord:
    """A finite record prefix: everything the checkable clauses read."""

    horizon: int = 0
    pins: tuple[Pin, ...] = ()
    requests: tuple[FundedRequest, ...] = ()
    positions: tuple[Position, ...] = ()
    docket: DocketFacts = field(default_factory=DocketFacts)
    era: EraFacts = field(default_factory=EraFacts)
    priced_states: tuple[PricedState, ...] = ()
    breaches: tuple[BreachRecord, ...] = ()
    live_instruments: tuple[tuple[int, int], ...] = ()
    worst_case_exposure: Q = Q(0)


# --------------------------------------------------------------------------
# The engine
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class EngineDeclaration:
    """Everything the engine puts on the public record about itself."""

    engine_id: str
    procedures: tuple[Procedure, ...]
    tolerance: ToleranceSchedule
    certificate_type: str | None = None
    downside_limit: Q | None = None
    downside_means: str | None = None
    core_minimum: Q | None = None
    gating_capacity: int | None = None
    overtaking_bound: int | None = None
    logical_jurisdiction: tuple[str, ...] = ()

    @property
    def by_id(self) -> Mapping[str, Procedure]:
        return {p.procedure_id: p for p in self.procedures}


@runtime_checkable
class SettlementEngine(Protocol):
    """A pen, a clock, and a purse -- and nothing else."""

    @property
    def declaration(self) -> EngineDeclaration: ...


@dataclass(frozen=True)
class DeclaredHypothesis:
    """A clause nobody checked, carrying its own statement.

    The point of the type is that leaning on an unchecked clause leaves a record
    entry naming what was assumed and who declared it.
    """

    hypothesis_id: str
    clause: str
    statement: str
    declared_by: str

    def __str__(self) -> str:
        return f"{self.hypothesis_id} [{self.clause}] declared by {self.declared_by}"


@dataclass(frozen=True)
class ClauseVerdict:
    clause: str
    level: str
    kind: str
    holds: bool
    obstructions: tuple[str, ...] = ()
    leaned_on: tuple[str, ...] = ()


def _verdict(clause: str, kind: str, obstructions: Sequence[str],
             leaned_on: Sequence[str] = ()) -> ClauseVerdict:
    return ClauseVerdict(clause, CLAUSE_LEVEL[clause], kind, not obstructions,
                         tuple(obstructions), tuple(leaned_on))


def _hypothesis_for(clause: str,
                    hypotheses: Sequence[DeclaredHypothesis],
                    ) -> DeclaredHypothesis | None:
    for hypothesis in hypotheses:
        if hypothesis.clause == clause:
            return hypothesis
    return None


# --------------------------------------------------------------------------
# Jurisdiction clauses
# --------------------------------------------------------------------------


def clause_J1(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Declared settleable class.  Checkable.

    (J1) Declared settleable class. The engine declares, as public record, the
    procedures it owns, each with its outcome space, channel (logical or
    empirical), and - where applicable (C1) - horizon. The settleable class is
    the induced family of report variables; nothing outside it is pinnable by
    this engine.
    """
    obstructions: list[str] = []
    declared = engine.by_id
    for procedure in engine.procedures:
        if not procedure.well_formed():
            obstructions.append(
                f"procedure {procedure.procedure_id!r} is not well declared")
    for pin in record.pins:
        procedure = declared.get(pin.procedure_id)
        if procedure is None:
            obstructions.append(
                f"pin {pin.variable_id!r} names an undeclared procedure")
            continue
        if pin.value not in procedure.outcome_space:
            obstructions.append(
                f"pin {pin.variable_id!r} carries a value outside its outcome space")
        if pin.variable_id != report_variable(pin.procedure_id, pin.date):
            obstructions.append(
                f"pin {pin.variable_id!r} is not the report variable of its procedure "
                "and date")
    return _verdict("J1", CHECKABLE, obstructions)


def clause_J2(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Write-once, owner-only.  Checkable.

    (J2) Write-once, owner-only. Every report variable is pinnable exactly once,
    and only by the engine owning its procedure. That is the entire exclusivity
    clause, and it makes cross-pin conflict vacuous by construction: no variable
    has two pinners or two pins.

    A second pin on one variable is *not* silently tolerated as agreement: the
    interface routes it to the breach stack as a jurisdiction violation, so this
    predicate reports it whether or not the two values agree.
    """
    obstructions: list[str] = []
    seen: dict[str, Pin] = {}
    declared = engine.by_id
    for pin in record.pins:
        if pin.variable_id in seen:
            obstructions.append(
                f"variable {pin.variable_id!r} is pinned twice: a jurisdiction "
                "violation routed to the breach stack")
            continue
        seen[pin.variable_id] = pin
        procedure = declared.get(pin.procedure_id)
        if procedure is not None and procedure.owner != engine.engine_id:
            obstructions.append(
                f"pin {pin.variable_id!r} was written by a non-owning engine")
    return _verdict("J2", CHECKABLE, obstructions)


def clause_J3(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Migration transport: bridge, never re-settle.  Checkable.

    (J3) Migration transport: bridge, never re-settle. Under ontology migration,
    pins are historical record and are never re-spoken in the new vocabulary.
    Translated content reaches the new ontology through migration cells in the
    answerable layer.
    """
    obstructions: list[str] = []
    translation = dict(record.era.translations)
    pinned = {pin.variable_id: pin for pin in record.pins}
    for pin in record.pins:
        if pin.era != record.era.era_of(pin.date):
            obstructions.append(
                f"pin {pin.variable_id!r} records an era its date contradicts")
        image = translation.get(pin.variable_id)
        if image is not None and image in pinned:
            obstructions.append(
                f"pin {pin.variable_id!r} is re-spoken as {image!r} in the new "
                "vocabulary: translated content must reach the new ontology "
                "through the answerable layer")
    return _verdict("J3", CHECKABLE, obstructions)


# --------------------------------------------------------------------------
# Clock clauses
# --------------------------------------------------------------------------


def clause_C1_logical(engine: EngineDeclaration, record: SettlementRecord,
                      hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Logical completeness.  Declared: no finite prefix decides it.

    (C1) Completeness, split by channel. Logical channel: the completeness clause
    is that D-infinity contains the declared logical jurisdiction - every
    sentence the engine claims for deduction is eventually settled - with no rate
    promised.

    "Eventually" is not a property of a prefix, so this is carried as a
    hypothesis object.  The audit's correction is part of what must be declared:
    the operative set is the *decidable* fragment (proves or refutes), which is a
    proper subset of what the process proves.
    """
    hypothesis = _hypothesis_for("C1-logical", hypotheses)
    if hypothesis is None:
        return _verdict("C1-logical", DECLARED,
                        ("no hypothesis object declares logical completeness "
                         "over the declared jurisdiction",))
    if not engine.logical_jurisdiction and any(
            p.channel == LOGICAL for p in engine.procedures):
        return _verdict("C1-logical", DECLARED,
                        ("a logical procedure is declared with an empty declared "
                         "jurisdiction, so the hypothesis has no content",))
    return _verdict("C1-logical", DECLARED, (), (hypothesis.hypothesis_id,))


def clause_C1_empirical(engine: EngineDeclaration, record: SettlementRecord,
                        hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Funding-responsive completeness.  Checkable on the prefix.

    (C1) Completeness, split by channel. Empirical channel: funding-responsive
    completeness over the declared observable class - every report variable in
    the class settles if its procedure is funded and run, with a declared horizon
    per procedure.

    Checkable in exactly the conditional form the clause states: a *funded and
    run* request whose horizon has elapsed inside the prefix must have a pin.
    Unfunded questions are not promised, which is the whole point of the split.
    """
    obstructions: list[str] = []
    declared = engine.by_id
    pinned = {pin.variable_id for pin in record.pins}
    for procedure in engine.procedures:
        if procedure.channel == EMPIRICAL and procedure.horizon is None:
            obstructions.append(
                f"empirical procedure {procedure.procedure_id!r} declares no horizon")
    for request in record.requests:
        procedure = declared.get(request.key.procedure_id)
        if procedure is None or procedure.channel != EMPIRICAL:
            continue
        if request.executed_date is None:
            continue
        due = request.executed_date + (procedure.horizon or 0)
        if due <= record.horizon and request.pinned_variable not in pinned:
            obstructions.append(
                f"request {request.request_id!r} was funded and run, its declared "
                f"horizon elapsed at date {due}, and no pin settles it")
    return _verdict("C1-empirical", CHECKABLE, obstructions)


def clause_C2(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Ripeness and tolling.  Checkable.

    (C2) Ripeness and tolling. At admission: a query whose merits would require
    settlement faster than a declared horizon is unripe - deferred without
    liability. At runtime: settlement arriving later than its declared horizon,
    and all dependence on the rateless logical channel, tolls the affected
    refusal clocks.
    """
    obstructions: list[str] = []
    declared = engine.by_id
    for query in record.docket.queries:
        horizons = [declared[p].horizon for p in query.upstream
                    if p in declared and declared[p].horizon is not None]
        rateless = any(p in declared and declared[p].channel == LOGICAL
                       for p in query.upstream)
        needed = query.admitted_date + (max(horizons) if horizons else 0)
        should_be_unripe = needed > query.deadline
        if should_be_unripe and query.ripe:
            obstructions.append(
                f"query {query.query_id!r} needs settlement by {query.deadline} but "
                f"its declared horizons reach {needed}: it is unripe and was admitted "
                "as ripe")
        if not query.ripe and Q(query.liability) != Q(0):
            obstructions.append(
                f"unripe query {query.query_id!r} accrued liability {query.liability}: "
                "deferral is without liability")
        if rateless and not query.tolled:
            obstructions.append(
                f"query {query.query_id!r} depends on the rateless logical channel "
                "and its clock is not tolled")
    return _verdict("C2", CHECKABLE, obstructions)


def adequacy_inequality(engine: EngineDeclaration,
                        record: SettlementRecord) -> tuple[str, ...]:
    """(C3) in general form: the per-query inequality and the window inequality.

    Per query, with `a` its admission date, `H` the greatest declared horizon
    among its upstream procedures, `W` its declared service work and `k` the
    docket's per-date service capacity:

        a  +  H  +  ceiling(W / k)  <=  deadline.

    Aggregate, writing `release(q) = a + H` for the date a query's downstream
    service may first begin, for every window of dates:

        sum of W over queries with release >= t1 and deadline <= t2
              <=  k * (t2 - t1 + 1).

    The first inequality is the corpus's repaired latency failure generalized --
    a deadline that does not leave room for the upstream horizon plus the
    downstream service is a starvation-by-latency instance waiting to happen.
    The second is what stops a schedule that is adequate query-by-query from
    being jointly impossible: it is the standard single-server feasibility
    condition, over windows delimited by releases and deadlines rather than by
    deadlines alone, and it is necessary as well as sufficient because a window
    can only do the work its capacity supplies.
    """
    obstructions: list[str] = []
    declared = engine.by_id
    capacity = Q(record.docket.capacity)
    if capacity <= 0:
        return ("the docket declares no positive service capacity",)
    for query in record.docket.queries:
        if not query.ripe:
            continue
        horizons = [declared[p].horizon for p in query.upstream
                    if p in declared and declared[p].horizon is not None]
        upstream = max(horizons) if horizons else 0
        service = -((-Q(query.service_work)) // capacity)   # exact ceiling
        if query.admitted_date + upstream + service > query.deadline:
            obstructions.append(
                f"query {query.query_id!r} violates the per-query adequacy "
                f"inequality: {query.admitted_date} + {upstream} + {service} > "
                f"{query.deadline}")
    demands: list[tuple[int, int, Q]] = []
    for query in record.docket.queries:
        if not query.ripe:
            continue
        horizons = [declared[p].horizon for p in query.upstream
                    if p in declared and declared[p].horizon is not None]
        release = query.admitted_date + (max(horizons) if horizons else 0)
        demands.append((release, query.deadline, Q(query.service_work)))
    starts = sorted({release for release, _, _ in demands})
    ends = sorted({deadline for _, deadline, _ in demands})
    for start in starts:
        for end in ends:
            if end < start:
                continue
            total = sum((work for release, deadline, work in demands
                         if release >= start and deadline <= end), Q(0))
            supplied = capacity * Q(end - start + 1)
            if total > supplied:
                obstructions.append(
                    f"the window [{start},{end}] must serve {total} work but "
                    f"supplies only {supplied}")
    return tuple(obstructions)


def clause_C3(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Adequacy.  Checkable.

    (C3) Adequacy. The docket's schedules, admission capacity, and deadline
    structure must be adequate relative to the declared horizons: an inequality
    relating downstream deadlines to upstream horizons, stated per instance and
    checkable.

    On a purely logical jurisdiction the inequality has no upstream term and is
    satisfied with nothing to check, which is coherent design and not coverage:
    the work is carried by C2's tolling, and this clause constrains the empirical
    channel.
    """
    return _verdict("C3", CHECKABLE, adequacy_inequality(engine, record))


# --------------------------------------------------------------------------
# Purse clauses
# --------------------------------------------------------------------------


def clause_P1(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Enforcement core minimum.  Checkable at each recorded date.

    (P1) The engine certifies a fixed core coefficient theta > 0 (or a minimum
    theta_min for a varying core). The operative-force cap is void under
    theta_t -> 0; an engine whose conviction decays delivers force that
    evaporates. The minimum is a certified, verifiable commitment.

    The clause is checkable further than the audit assumed.  The core condition
    is *linear in the reference at fixed coefficient*, so whether the declared
    minimum is satisfiable at a date is a linear program over the priced state,
    and an empty admissible region is a detected condition with a declared
    branch -- quarantine of operative force -- rather than an open question.
    What stays open is only persistence: that the minimum keeps being satisfiable
    as settlement contracts the region.  Persistence is `P1-persistence`, and
    nothing here bounds it, because a per-date check bounds no infimum over time.

    The interface document is **not** amended by this.  Its P1 text is quoted
    above unchanged; the split into a checkable half and a declared half is a
    proposed clause revision, recorded with its wording in the round report for
    the interface's author to adopt or decline.
    """
    obstructions: list[str] = []
    if engine.core_minimum is None or Q(engine.core_minimum) <= 0:
        obstructions.append("the engine certifies no positive core minimum")
        return _verdict("P1", CHECKABLE, obstructions)
    for state in record.priced_states:
        admission = core_admission(state.language, state.book, state.settled,
                                   Q(engine.core_minimum), state.date)
        if not admission.admitted:
            obstructions.append(
                f"no reference at date {state.date} admits the certified core "
                f"minimum {engine.core_minimum}: {admission.consequence}")
    return _verdict("P1", CHECKABLE, obstructions)


def clause_P1_persistence(engine: EngineDeclaration, record: SettlementRecord,
                          hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """That the certified core minimum keeps being satisfiable.  Declared.

    No finite prefix decides a claim about every future date, and nothing in the
    engine's own theory need bound the geometry of the region its prices induce.
    This is the open sub-problem the witness audit logs, carried explicitly.
    """
    hypothesis = _hypothesis_for("P1-persistence", hypotheses)
    if hypothesis is None:
        return ClauseVerdict("P1-persistence", MECHANISM_COMPATIBILITY, DECLARED,
                             False,
                             ("no hypothesis object declares that the certified "
                              "core minimum persists as the region contracts",))
    return ClauseVerdict("P1-persistence", MECHANISM_COMPATIBILITY, DECLARED, True,
                         (), (hypothesis.hypothesis_id,))


def clause_P2(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Downside establishment.  Checkable.

    (P2) Downside establishment. The engine guarantees a worldwise downside
    [limit] -B against the book's holdings. The means are engine-specific -
    market refusal where the engine may refuse trades; bounded aggregate trader
    budgets where it may not - but the abstract requirement is uniform, and the
    establishing means must be declared.
    """
    obstructions: list[str] = []
    if engine.downside_limit is None or Q(engine.downside_limit) < 0:
        obstructions.append("the engine declares no nonnegative downside limit")
    if engine.downside_means not in DOWNSIDE_MEANS:
        obstructions.append(
            f"the establishing means {engine.downside_means!r} is not declared")
    if engine.downside_limit is not None and Q(record.worst_case_exposure) < -Q(
            engine.downside_limit):
        obstructions.append(
            f"recorded worst-case exposure {record.worst_case_exposure} breaches the "
            f"declared limit -{engine.downside_limit}")
    return _verdict("P2", CHECKABLE, obstructions)


def clause_P3(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Finite gating.  Checkable.

    (P3) Finite gating. Engine-facing instruments are gated: finitely many live
    per date, admitted under a fair (finite-overtaking) queue.
    """
    obstructions: list[str] = []
    if engine.gating_capacity is None or engine.gating_capacity < 0:
        obstructions.append("the engine declares no finite gating capacity")
    else:
        for date, live in record.live_instruments:
            if live > engine.gating_capacity:
                obstructions.append(
                    f"date {date} carries {live} live instruments above the declared "
                    f"capacity {engine.gating_capacity}")
    if engine.overtaking_bound is not None:
        for request in record.requests:
            waited = ((request.executed_date if request.executed_date is not None
                       else record.horizon) - request.key.requested_date)
            if waited > engine.overtaking_bound:
                obstructions.append(
                    f"request {request.request_id!r} waited {waited} dates above the "
                    f"declared overtaking bound {engine.overtaking_bound}")
    return _verdict("P3", CHECKABLE, obstructions)


def clause_P4(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Declared certificate type.  Checkable that a type is named.

    (P4) Declared certificate type. The engine names the soundness guarantee its
    belief/pricing process carries - market non-exploitation, minimax regret,
    Ville-style validity, conformal coverage, or another declared type - and the
    composite guarantee's empirical conjunct is stated relative to the declared
    type.

    What is checkable is that a type is named.  That the named type's semantics
    actually hold of this engine is `P4-semantics`, the abstract relation the
    interface leaves as a formalization target.
    """
    if not engine.certificate_type:
        return _verdict("P4", CHECKABLE, ("the engine names no certificate type",))
    return _verdict("P4", CHECKABLE, ())


def clause_P4_semantics(engine: EngineDeclaration, record: SettlementRecord,
                        hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """That the named certificate type's semantics hold of this engine.  Declared.

    This is the interface's abstract certificate relation: under the engine's
    declared semantics, a certificate establishes its advertised guarantee on a
    history.  It is declared rather than checked for two reasons.  The relation
    is parameterized by a semantics the interface deliberately does not fix, so
    there is nothing uniform to compute; and the guarantees engines actually
    carry are properties of whole histories, quantified over all dates and all
    admissible opponents, which no finite prefix decides.
    """
    hypothesis = _hypothesis_for("P4-semantics", hypotheses)
    if hypothesis is None:
        return ClauseVerdict("P4-semantics", ENGINE_INTRINSIC, DECLARED, False,
                             ("no hypothesis object declares that the named "
                              "certificate type's semantics hold of this engine",))
    return ClauseVerdict("P4-semantics", ENGINE_INTRINSIC, DECLARED, True, (),
                         (hypothesis.hypothesis_id,))


# --------------------------------------------------------------------------
# Tolerance clauses
# --------------------------------------------------------------------------


def realized_incoherence(state: PricedState) -> Q | None:
    """The incoherence of a priced state, or `None` when it carries no prices.

    Measured against logic plus pins, never the book: what the engine owes is
    that its prices are near coherent, not that the book built on them stayed
    feasible.
    """
    if state.prices is None:
        return None
    report = incoherence(state.language, state.settled, state.prices)
    return None if report.value is None else Q(report.value)


def clause_T1(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Tolerance schedule conformance.  Checkable on the prefix.

    (T1) Engines whose price/belief states are only approximately coherent at
    finite times declare a tolerance schedule epsilon_t. Downstream, the docket
    runs the robust interval, merits certificate, and sure-loss objection against
    the declared schedule; an exactly coherent engine declares epsilon_t = 0 and
    the robust forms reduce to the exact ones.

    Conformance is checkable because the realized incoherence is now a defined,
    computed quantity in the same units as the schedule.  What is *not* checked
    here is that the declaration is any use: a maximal declaration conforms
    forever and certifies nothing.  That is `tolerance_is_working`, and the
    interface should be read as requiring it separately.
    """
    obstructions: list[str] = []
    for state in record.priced_states:
        realized = realized_incoherence(state)
        if realized is None:
            continue
        declared = engine.tolerance.at(state.date)
        if realized > declared:
            obstructions.append(
                f"date {state.date} realized incoherence {realized} above the "
                f"declared tolerance {declared}")
    return _verdict("T1", CHECKABLE, obstructions)


def clause_T2(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Certification layering.  Checkable.

    (T2) Certification layering. The engine certifies [minimums] (its
    epsilon-schedule and horizons); breach of a certified [minimum] is the
    engine's, handled by section 7. The book may voluntarily declare tighter
    working tolerances or deadlines; breach of a self-declared tighter bound is
    the book's, and chargeable - it assumed the risk.
    """
    obstructions: list[str] = []
    for breach in record.breaches:
        expected = attribute_breach(breach.declaration, Q(breach.realized))
        if (expected.attributed_to != breach.attributed_to
                or expected.tolled != breach.tolled
                or expected.chargeable != breach.chargeable):
            obstructions.append(
                f"the breach at date {breach.date} is recorded as "
                f"{breach.attributed_to!r} (tolled={breach.tolled}, "
                f"chargeable={breach.chargeable}) but the layering makes it "
                f"{expected.attributed_to!r} (tolled={expected.tolled}, "
                f"chargeable={expected.chargeable})")
        if Q(breach.declaration.engine_certified) != engine.tolerance.at(breach.date):
            obstructions.append(
                f"the breach at date {breach.date} cites a certified tolerance the "
                "engine's declared schedule does not carry")
    return _verdict("T2", CHECKABLE, obstructions)


# --------------------------------------------------------------------------
# Conduct clauses
# --------------------------------------------------------------------------


def clause_F1(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Request-keyed subsidy.  Checkable, and partly typed.

    (F1) Request-keyed subsidy. Subsidies attach syntactically to a
    SettlementRequestKey: (target report variable, or theorem-question for the
    logical channel; procedure; funder identity; timing). A request key names a
    question, never an outcome, so directional funding - "pay to settle X at v" -
    is inexpressible, not merely forbidden.
    """
    obstructions: list[str] = []
    expected = ("target", "procedure_id", "funder_id", "requested_date",
                "scheduled_date")
    if key_field_names() != expected:
        obstructions.append(
            f"the request key's fields are {key_field_names()}, not the declared "
            f"question-naming quadruple {expected}")
    declared = engine.by_id
    for request in record.requests:
        if Q(request.subsidy) < 0:
            obstructions.append(f"request {request.request_id!r} carries a negative "
                                "subsidy")
        procedure = declared.get(request.key.procedure_id)
        if procedure is None:
            obstructions.append(
                f"request {request.request_id!r} keys a procedure this engine has "
                "not declared")
            continue
        if len(directional_variants(request.key, procedure.outcome_space)) != 1:
            obstructions.append(
                f"request {request.request_id!r} admits more than one key across "
                "intended outcomes: the key is directional")
    return _verdict("F1", CHECKABLE, obstructions)


def clause_F2(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Stopping neutrality.  Checkable per request.

    (F2) Stopping neutrality. The funder's stopping policy must create no
    directional bias in what gets certified. Two named witnesses satisfy it: a
    precommitted stopping rule (fixed-horizon experiments), or an
    optional-stopping-safe (anytime-valid) certificate.
    """
    obstructions: list[str] = []
    for request in record.requests:
        if request.stopping_rule == PRECOMMITTED:
            if request.declared_stop is None:
                obstructions.append(
                    f"request {request.request_id!r} claims a precommitted rule but "
                    "declares no stop date")
            elif (request.executed_date is not None
                    and request.executed_date != request.declared_stop):
                obstructions.append(
                    f"request {request.request_id!r} stopped at "
                    f"{request.executed_date}, not at its precommitted "
                    f"{request.declared_stop}")
        elif request.stopping_rule == ANYTIME_VALID:
            if not engine.certificate_type:
                obstructions.append(
                    f"request {request.request_id!r} leans on an anytime-valid "
                    "certificate from an engine that names no certificate type")
        else:
            obstructions.append(
                f"request {request.request_id!r} names no recognized stopping "
                "witness")
    return _verdict("F2", CHECKABLE, obstructions)


def clause_F3(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Probe blackout.  Checkable.

    (F3) Probe blackout. The funder of a settlement request takes no fresh
    positions on its target between funding and pin - the insider pattern of the
    corpus's conduct machinery, extended verbatim: blackout window, disgorgement
    on violation, one checkable objection type.
    """
    obstructions: list[str] = []
    for request in record.requests:
        start = request.key.requested_date
        end = (request.executed_date if request.executed_date is not None
               else record.horizon)
        for position in record.positions:
            if (position.actor_id == request.key.funder_id
                    and position.target == request.key.target
                    and position.fresh and start <= position.date <= end):
                obstructions.append(
                    f"funder {position.actor_id!r} took a fresh position on "
                    f"{position.target!r} at date {position.date}, inside the "
                    f"blackout window [{start},{end}] of request "
                    f"{request.request_id!r}")
    return _verdict("F3", CHECKABLE, obstructions)


def clause_F4(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Funder provenance.  Checkable.

    (F4) Funder provenance. Funding profiles are recorded per pin, feeding the
    common-source objection surface when one purse bankrolls all premises of one
    conclusion.
    """
    obstructions: list[str] = []
    funded = {request.pinned_variable: request.key.funder_id
              for request in record.requests if request.pinned_variable}
    for pin in record.pins:
        funder = funded.get(pin.variable_id)
        if funder is not None and funder not in pin.funder_profile:
            obstructions.append(
                f"pin {pin.variable_id!r} was funded by {funder!r} and does not "
                "record it in its funding profile")
    return _verdict("F4", CHECKABLE, obstructions)


def clause_S8_logical(engine: EngineDeclaration, record: SettlementRecord,
                      hypotheses: Sequence[DeclaredHypothesis] = ()) -> ClauseVerdict:
    """Proof-carrying logical pins.  Checkable that a derivation ships.

    Logical pins are proof-carrying: a pin on a theorem-question ships a
    derivation certificate checkable by a fixed proof checker.  Derivation is
    therefore auditable; what remains assumed is the checker itself.

    This is the audit's second delta made a requirement of the interface rather
    than of the engine's own theory: an engine whose pen emits sentences without
    derivations fails here, and the remedy is to emit the pair.
    """
    obstructions: list[str] = []
    declared = engine.by_id
    for pin in record.pins:
        procedure = declared.get(pin.procedure_id)
        if procedure is not None and procedure.channel == LOGICAL and not pin.derivation:
            obstructions.append(
                f"logical pin {pin.variable_id!r} ships no derivation certificate")
    return _verdict("S8-logical", CHECKABLE, obstructions)


# --------------------------------------------------------------------------
# The interface as one object
# --------------------------------------------------------------------------

CHECKABLE_CLAUSES = (
    ("J1", clause_J1), ("J2", clause_J2), ("J3", clause_J3),
    ("C1-empirical", clause_C1_empirical), ("C2", clause_C2), ("C3", clause_C3),
    ("P1", clause_P1), ("P2", clause_P2), ("P3", clause_P3), ("P4", clause_P4),
    ("T1", clause_T1), ("T2", clause_T2),
    ("F1", clause_F1), ("F2", clause_F2), ("F3", clause_F3), ("F4", clause_F4),
    ("S8-logical", clause_S8_logical),
)

DECLARED_CLAUSES = (
    ("C1-logical", clause_C1_logical),
    ("P1-persistence", clause_P1_persistence),
    ("P4-semantics", clause_P4_semantics),
)

ALL_CLAUSES = CHECKABLE_CLAUSES + DECLARED_CLAUSES


@dataclass(frozen=True)
class InterfaceReport:
    engine_id: str
    verdicts: tuple[ClauseVerdict, ...]

    @property
    def by_clause(self) -> Mapping[str, ClauseVerdict]:
        return {verdict.clause: verdict for verdict in self.verdicts}

    @property
    def checkable_hold(self) -> bool:
        return all(v.holds for v in self.verdicts if v.kind == CHECKABLE)

    @property
    def declared_hold(self) -> bool:
        return all(v.holds for v in self.verdicts if v.kind == DECLARED)

    @property
    def satisfies_interface(self) -> bool:
        return self.checkable_hold and self.declared_hold

    @property
    def failing(self) -> tuple[str, ...]:
        return tuple(v.clause for v in self.verdicts if not v.holds)

    @property
    def leaned_on(self) -> tuple[str, ...]:
        return tuple(sorted({h for v in self.verdicts for h in v.leaned_on}))

    @property
    def obstructions(self) -> tuple[str, ...]:
        return tuple(o for v in self.verdicts for o in v.obstructions)


def evaluate_interface(engine: EngineDeclaration, record: SettlementRecord,
                       hypotheses: Sequence[DeclaredHypothesis] = (),
                       clauses: Sequence[str] | None = None) -> InterfaceReport:
    """Evaluate every clause, or a named subset, against a finite record prefix."""
    wanted = set(clauses) if clauses is not None else None
    verdicts = []
    for name, predicate in ALL_CLAUSES:
        if wanted is not None and name not in wanted:
            continue
        verdicts.append(predicate(engine, record, hypotheses))
    return InterfaceReport(engine.engine_id, tuple(verdicts))


def satisfies(engine: EngineDeclaration, record: SettlementRecord,
              hypotheses: Sequence[DeclaredHypothesis] = (),
              clauses: Sequence[str] | None = None) -> bool:
    """The predicate a theorem quantifies over: "engine satisfying these clauses"."""
    return evaluate_interface(engine, record, hypotheses, clauses).satisfies_interface


# --------------------------------------------------------------------------
# The trivial reference engine
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ReferenceEngine:
    """A finite lookup-table pen, declared horizons, and a refusing purse.

    The smallest thing that is an engine at all, and the existence proof that the
    checkable fragment is jointly satisfiable.  Its pen is a table from
    (procedure, date) to an outcome; its clock is the declared horizons; its
    purse refuses, so its worldwise downside limit is zero and it establishes it
    by the first of P2's two named means.

    It certifies exact coherence, which it can honour because it prices nothing
    it cannot reproduce -- the table *is* the priced state.  Nothing about it is
    interesting; that is the point.
    """

    engine_id: str = "engine:reference"
    table: tuple[tuple[str, int, str], ...] = ()

    @property
    def declaration(self) -> EngineDeclaration:
        return EngineDeclaration(
            engine_id=self.engine_id,
            procedures=(
                Procedure("proc:thermometer", EMPIRICAL, ("cold", "warm"),
                          self.engine_id, horizon=2),
                Procedure("proc:decide", LOGICAL, ("proved", "refuted"),
                          self.engine_id),
            ),
            tolerance=ToleranceSchedule("tolerance:exact", {}, Q(0)),
            certificate_type="lookup-table exactness",
            downside_limit=Q(0),
            downside_means=REFUSAL,
            core_minimum=Q(1, 4),
            gating_capacity=2,
            overtaking_bound=4,
            logical_jurisdiction=("phi",),
        )

    def outcome(self, procedure_id: str, date: int) -> str | None:
        for name, when, value in self.table:
            if name == procedure_id and when == date:
                return value
        return None


def reference_record() -> SettlementRecord:
    """A finite prefix on which the reference engine satisfies every checkable clause."""
    from src.coherence import PriceAssignment
    from src.leverage_interval import Endorsement

    language = Language(("w1", "w2", "w3"),
                        {"A": ("w1", "w2"), "B": ("w2", "w3"), "C": ("w2",)})
    book = Book(1, (Endorsement("e:A", (Q(1), Q(1), Q(0)), Q(3, 5)),))
    prices = PriceAssignment(1, {"A": Q(3, 5), "B": Q(2, 5)})
    state = PricedState(0, language, book, (), prices)

    key = SettlementRequestKey("X[proc:thermometer@1]", "proc:thermometer",
                               "funder:a", 0, 1)
    request = FundedRequest("r:1", key, Q(1), PRECOMMITTED, declared_stop=1,
                            executed_date=1,
                            pinned_variable=report_variable("proc:thermometer", 1))
    pins = (
        Pin(report_variable("proc:thermometer", 1), "proc:thermometer", 1, "warm",
            ("funder:a",)),
        Pin(report_variable("proc:decide", 2), "proc:decide", 2, "proved",
            (), derivation="derivation:phi"),
    )
    docket = DocketFacts(capacity=Q(1), queries=(
        AdmittedQuery("q:empirical", 0, 6, ("proc:thermometer",), Q(1), True, False,
                      Q(0)),
        AdmittedQuery("q:logical", 0, 9, ("proc:decide",), Q(1), True, True, Q(0)),
    ))
    return SettlementRecord(
        horizon=4, pins=pins, requests=(request,), positions=(),
        docket=docket, era=EraFacts(), priced_states=(state,), breaches=(),
        live_instruments=((0, 1), (1, 2), (2, 1)), worst_case_exposure=Q(0))
