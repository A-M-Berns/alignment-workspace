"""The empirical settlement channel, constructed.

The interface says what a settlement engine must supply.  This module builds one
funded path end to end on the existing docket machinery: a request naming a
question, an observation procedure with a declared outcome space and horizon, a
scheduled execution, and the pin that results -- with the pin's three downstream
effects wired to the interval computer and the objection surface that already
exist.

Three things are worth reading closely, because they are where a construction
can quietly cheat.

**The request key cannot express a direction.**  The key type carries a target,
a procedure, a funder and timing, and there is no field an outcome could be
written into.  This is a typed obstruction in the grammar's sense: directional
funding is not forbidden by a check that could be forgotten, it is
unconstructible.  `directional_variants` is the check that the construction
respects the type.

**The executor cannot see the book.**  `execute` takes the procedure, the date,
and the world -- and nothing else.  The faithfulness axiom says a pin's value
has no dependence on the book's states or any funding profile beyond the
declared inputs and the world; the signature makes that path *unwritable in this
implementation*.  That is a disclosure, not a proof: the axiom is about every
possible engine, and a type here constrains only this one.  What it does buy is
that no later edit can smuggle the dependence in without changing a signature
that the tests read.

**A pin has no answerability columns.**  The pin type carries no basis tag, no
stake, no charge stream, and no objection surface.  `pin_has_no_answerability_columns`
checks that structurally rather than by convention.

Finiteness discipline.  Procedures, requests, pins and dates are finite; the
scheduler runs over a finite horizon; every quantity is exact rational.

All arithmetic is exact rationals.  No floating point.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.case_stream import Transfer
from src.grammar import Grounds
from src.leverage_interval import (
    Book,
    Language,
    LeverageInterval,
    SettledFact,
    compute_interval,
)
from src.settlement_interface import (
    EMPIRICAL,
    LOGICAL,
    PRECOMMITTED,
    AdmittedQuery,
    DocketFacts,
    EngineDeclaration,
    FundedRequest,
    Pin,
    Position,
    Procedure,
    SettlementRecord,
    SettlementRequestKey,
    adequacy_inequality,
    directional_variants,
    report_variable,
)


# --------------------------------------------------------------------------
# Procedures and the world
# --------------------------------------------------------------------------


def observation_procedure(procedure_id: str, outcome_space: Sequence[str],
                          horizon: int, owner: str) -> Procedure:
    """An observation procedure: a declared outcome space and a declared horizon.

    Experiments, unlike proofs, have schedules, so the empirical channel's
    completeness is conditional on funding and its horizon is per procedure.
    """
    if horizon < 0:
        raise ValueError("a declared horizon is nonnegative")
    if len(set(outcome_space)) < 2:
        raise ValueError("an outcome space with fewer than two values settles nothing")
    return Procedure(procedure_id, EMPIRICAL, tuple(outcome_space), owner, horizon)


World = Mapping[tuple[str, int], str]


def execute(procedure: Procedure, date: int, world: World) -> str | None:
    """Run a declared procedure at a date against the world.

    The signature is the point.  Conditional on the declared procedure, its
    declared inputs, and the realized world, the value has nowhere else to come
    from: there is no book parameter and no funder parameter, so no extra path
    from purse to pin value can be written here.  Performativity is still
    permitted, and deliberately so -- an agent whose actions change the world
    changes `world`, and the pin faithfully reports the world the agent helped
    make.
    """
    value = world.get((procedure.procedure_id, date))
    if value is None:
        return None
    if value not in procedure.outcome_space:
        raise ValueError(
            f"the world returned {value!r}, outside {procedure.procedure_id!r}'s "
            "declared outcome space")
    return value


def executor_cannot_read_the_book() -> bool:
    """Is the faithfulness path unwritable in this executor's signature?"""
    import inspect

    parameters = tuple(inspect.signature(execute).parameters)
    return parameters == ("procedure", "date", "world")


# --------------------------------------------------------------------------
# Requests
# --------------------------------------------------------------------------


def settlement_request(target: str, procedure: Procedure, funder_id: str,
                       requested_date: int, scheduled_date: int, subsidy: Q,
                       request_id: str, declared_stop: int | None = None,
                       ) -> FundedRequest:
    """Key a subsidy to a question.  The intended outcome has nowhere to go."""
    if scheduled_date < requested_date:
        raise ValueError("a request cannot be scheduled before it is requested")
    key = SettlementRequestKey(target, procedure.procedure_id, funder_id,
                               requested_date, scheduled_date)
    stop = declared_stop if declared_stop is not None else scheduled_date
    return FundedRequest(request_id, key, Q(subsidy), PRECOMMITTED, stop, None, None)


def request_is_directional(request: FundedRequest,
                           outcome_space: Sequence[str]) -> bool:
    """Could a funder's intended outcome be read back off this key?"""
    return len(directional_variants(request.key, outcome_space)) > 1


def pin_has_no_answerability_columns() -> bool:
    """The pin type carries none of the columns the answerability ledger tracks."""
    names = {f.name for f in fields(Pin)}
    forbidden = {"basis", "basis_tag", "stake", "stakes", "charge", "charges",
                 "objection", "objections", "liability"}
    return not (names & forbidden)


# --------------------------------------------------------------------------
# Scheduled execution, and the pin
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ExecutionOutcome:
    """What running a scheduled request produced."""

    request: FundedRequest
    pin: Pin | None
    executed_date: int | None
    missed_horizon: bool
    detail: str


def run_request(request: FundedRequest, procedure: Procedure, world: World,
                horizon_now: int) -> ExecutionOutcome:
    """Request, then scheduled execution, then pin -- or a missed horizon.

    The declared horizon is the promise: a procedure scheduled at `d` settles by
    `d + horizon`.  Running past it is an engine breach, and the outcome says so
    rather than silently producing a late pin as though nothing happened.
    """
    if procedure.channel != EMPIRICAL:
        raise ValueError("this path is the empirical channel")
    scheduled = request.key.scheduled_date
    due = scheduled + (procedure.horizon or 0)
    value = execute(procedure, scheduled, world)
    if value is None:
        return ExecutionOutcome(
            request, None, None, due <= horizon_now,
            "the procedure was scheduled and returned nothing by its declared horizon"
            if due <= horizon_now else "the procedure has not yet come due")
    variable = report_variable(procedure.procedure_id, scheduled)
    pin = Pin(variable, procedure.procedure_id, scheduled, value,
              (request.key.funder_id,))
    return ExecutionOutcome(request, pin, scheduled, False,
                            "settled within the declared horizon")


def pinned(outcome: ExecutionOutcome) -> FundedRequest:
    """The request as the record carries it after execution."""
    from dataclasses import replace

    return replace(outcome.request, executed_date=outcome.executed_date,
                   pinned_variable=None if outcome.pin is None
                   else outcome.pin.variable_id)


# --------------------------------------------------------------------------
# The pin's three downstream effects
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class BridgeWarrant:
    """An endorsed, defeasible bridge from a report variable to a world claim.

    The reliability of every procedure is answerable content, so the bridge is
    where a disagreement between two procedures lives.  The pin itself is never
    the target of one.
    """

    warrant_id: str
    variable_id: str
    world_claim: str
    direction: str
    endorsed: bool = True


def constrain(language: Language, book: Book, pins: Sequence[Pin],
              valuation: Mapping[str, Q], target: str) -> LeverageInterval:
    """Effect one: the pin's equalities enter the region, permanently.

    `valuation` reads a pin's declared outcome into the numeric value its
    sentence takes -- the bridge from an outcome label to a probability
    constraint is declared, not inferred.
    """
    settled = tuple(SettledFact(pin.variable_id, Q(valuation[pin.value]))
                    for pin in pins if pin.value in valuation
                    and language.licenses(pin.variable_id))
    return compute_interval(language, book, settled, target)


@dataclass(frozen=True)
class WorldInstrument:
    """A world-mode instrument referencing a report variable."""

    instrument_id: str
    variable_id: str
    holder: str
    counterparty: str
    payoff: Mapping[str, Q]


def resolve(instruments: Sequence[WorldInstrument], pin: Pin) -> tuple[Transfer, ...]:
    """Effect two: instruments referencing the variable resolve at the pinned value.

    The pin executes wealth transfers, which is why pins are never clawed back:
    a reopened settlement would be a fresh exploitation surface of the recycling
    species the corpus already refuted.
    """
    transfers: list[Transfer] = []
    for instrument in instruments:
        if instrument.variable_id != pin.variable_id:
            continue
        amount = Q(instrument.payoff.get(pin.value, Q(0)))
        transfers.append(Transfer(f"t:{instrument.instrument_id}",
                                  instrument.counterparty, instrument.holder,
                                  amount))
    return tuple(transfers)


def grounding_evidence(pin: Pin, world_claim: str, warrant: BridgeWarrant,
                       grounds_id: str) -> Grounds | None:
    """Effect three: the pin is citable as evidence, never the target.

    The grounds carry the pin and the bridge warrant that reaches the world
    claim from it.  The warrant is endorsed, defeasible content; the pin is not.
    """
    if warrant.variable_id != pin.variable_id or warrant.world_claim != world_claim:
        return None
    if not warrant.endorsed:
        return None
    return Grounds(grounds_id, {"variable_id": pin.variable_id, "value": pin.value,
                                "world_claim": world_claim,
                                "warrant_id": warrant.warrant_id,
                                "direction": warrant.direction})


# --------------------------------------------------------------------------
# Clock discipline
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class RipenessVerdict:
    query_id: str
    ripe: bool
    needed_by: int
    reachable_by: int
    liability: Q
    detail: str


def ripeness_gate(query: AdmittedQuery,
                  procedures: Mapping[str, Procedure]) -> RipenessVerdict:
    """A query whose merits need settlement faster than a horizon is unripe.

    Unripe means deferred *without liability*: the gate refuses the query and
    charges nothing.  A query hanging on the rateless logical channel is
    admitted and tolls indefinitely rather than being refused -- never-settling
    exposed content is permanently unripe, and neither state accrues unearned
    book liability.
    """
    horizons = [procedures[p].horizon for p in query.upstream
                if p in procedures and procedures[p].horizon is not None]
    rateless = any(p in procedures and procedures[p].channel == LOGICAL
                   for p in query.upstream)
    reachable = query.admitted_date + (max(horizons) if horizons else 0)
    if rateless:
        return RipenessVerdict(query.query_id, True, query.deadline, reachable, Q(0),
                               "admitted against the rateless channel and tolled")
    if reachable > query.deadline:
        return RipenessVerdict(query.query_id, False, query.deadline, reachable, Q(0),
                               "unripe: no declared horizon reaches the deadline, "
                               "deferred without liability")
    return RipenessVerdict(query.query_id, True, query.deadline, reachable, Q(0),
                           "ripe: a declared horizon reaches the deadline")


@dataclass(frozen=True)
class TollRecord:
    """A clock paused because the substrate, not the book, was late."""

    query_id: str
    procedure_id: str
    declared_horizon: int
    actual: int
    tolled_dates: int
    chargeable_to_book: bool


def toll_missed_horizon(query: AdmittedQuery, procedure: Procedure,
                        actual_settlement_date: int) -> TollRecord | None:
    """A procedure past its declared horizon tolls the clocks it touches.

    The breach is the engine's, so nothing is chargeable to the book: substrate
    failure never converts into unearned book liability.
    """
    if procedure.horizon is None:
        return None
    due = query.admitted_date + procedure.horizon
    if actual_settlement_date <= due:
        return None
    return TollRecord(query.query_id, procedure.procedure_id, procedure.horizon,
                      actual_settlement_date, actual_settlement_date - due, False)


# --------------------------------------------------------------------------
# C3, proved for this channel
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ServiceOutcome:
    query_id: str
    release: int
    deadline: int
    completed: int | None

    @property
    def met(self) -> bool:
        return self.completed is not None and self.completed <= self.deadline


def serve_earliest_deadline_first(engine: EngineDeclaration, docket: DocketFacts,
                                  horizon: int) -> tuple[ServiceOutcome, ...]:
    """Serve the ripe admitted queries, earliest deadline first, at capacity.

    Work within a date is divisible across queries, so this is the preemptive
    single-server schedule, for which earliest-deadline-first is optimal: if any
    schedule meets every deadline, this one does.
    """
    declared = engine.by_id
    remaining: list[list] = []
    for query in docket.queries:
        if not query.ripe:
            continue
        horizons = [declared[p].horizon for p in query.upstream
                    if p in declared and declared[p].horizon is not None]
        release = query.admitted_date + (max(horizons) if horizons else 0)
        remaining.append([query.query_id, release, query.deadline,
                          Q(query.service_work), None])
    capacity = Q(docket.capacity)
    for date in range(horizon + 1):
        available = capacity
        for item in sorted(remaining, key=lambda r: (r[2], r[0])):
            if available <= 0:
                break
            if item[1] > date or item[3] <= 0:
                continue
            spent = min(available, item[3])
            item[3] -= spent
            available -= spent
            if item[3] == 0 and item[4] is None:
                item[4] = date
    return tuple(ServiceOutcome(item[0], item[1], item[2], item[4])
                 for item in remaining)


def adequacy_implies_no_missed_deadline(engine: EngineDeclaration,
                                        record: SettlementRecord) -> tuple[bool, bool]:
    """`(adequacy holds, every ripe query met its deadline)` for this channel.

    The theorem this checks: on the constructed channel, if the adequacy
    inequality holds -- per query, the deadline leaves room for the upstream
    horizon plus the downstream service, and over every window the released work
    fits the capacity the window supplies -- then earliest-deadline-first meets
    every deadline.  The window inequality is exactly the demand condition, and
    the per-query inequality is the single-query case of it, so a missed
    deadline exhibits a window whose demand exceeded its supply.

    Returned as a pair so a caller can exhibit both the satisfied instance and a
    violating one, rather than only asserting the implication.
    """
    adequate = not adequacy_inequality(engine, record)
    outcomes = serve_earliest_deadline_first(engine, record.docket, record.horizon)
    return adequate, all(outcome.met for outcome in outcomes)


# --------------------------------------------------------------------------
# Conduct
# --------------------------------------------------------------------------


def stopping_rule_is_precommitted(request: FundedRequest) -> bool:
    """`F2` as a checkable property of one request."""
    return (request.stopping_rule == PRECOMMITTED
            and request.declared_stop is not None
            and (request.executed_date is None
                 or request.executed_date == request.declared_stop))


def stopping_is_outcome_independent(request: FundedRequest, procedure: Procedure,
                                    worlds: Sequence[World],
                                    horizon: int) -> bool:
    """The neutrality content: replay under different worlds, same stop date.

    A precommitted rule creates no directional bias exactly when the date the
    funder stops does not depend on what the interim outcomes were.  Two worlds
    differing on the target must produce the same stop date; if they do not, the
    rule was not precommitted whatever it was called.
    """
    stops = set()
    for world in worlds:
        outcome = run_request(request, procedure, world, horizon)
        stops.add(outcome.executed_date)
    return len(stops) <= 1


def probe_blackout_grounds(request: FundedRequest, positions: Sequence[Position],
                           grounds_id: str, pin_date: int | None = None,
                           ) -> Grounds | None:
    """`F3`.  Grounds when the funder took a fresh position inside the window.

    The window runs from funding to pin.  A position by anyone else, a stale
    position, or a position outside the window is not this objection.
    """
    start = request.key.requested_date
    end = pin_date if pin_date is not None else (
        request.executed_date if request.executed_date is not None else start)
    offenders = tuple(
        (p.actor_id, p.target, p.date) for p in positions
        if p.actor_id == request.key.funder_id and p.target == request.key.target
        and p.fresh and start <= p.date <= end)
    if not offenders:
        return None
    return Grounds(grounds_id, {"request_id": request.request_id,
                                "funder_id": request.key.funder_id,
                                "target": request.key.target,
                                "window": (start, end),
                                "positions": offenders})


@dataclass(frozen=True)
class Inference:
    """A conclusion and the premise pins it rests on."""

    conclusion: str
    premises: tuple[str, ...]


def common_source_grounds(inference: Inference, pins: Sequence[Pin],
                          grounds_id: str) -> Grounds | None:
    """`F4`.  Grounds when one purse bankrolled every premise of one conclusion.

    Recorded funding profiles are what make this checkable: without provenance
    per pin the pattern is invisible, which is why F4 exists at all.
    """
    if not inference.premises:
        return None
    profiles = []
    by_variable = {pin.variable_id: pin for pin in pins}
    for premise in inference.premises:
        pin = by_variable.get(premise)
        if pin is None:
            return None
        profiles.append(set(pin.funder_profile))
    shared = set.intersection(*profiles) if profiles else set()
    if not shared:
        return None
    return Grounds(grounds_id, {"conclusion": inference.conclusion,
                                "premises": tuple(inference.premises),
                                "common_funders": tuple(sorted(shared))})


# --------------------------------------------------------------------------
# The constructed channel, as a displayed instance
# --------------------------------------------------------------------------

CHANNEL_OWNER = "engine:empirical"

THERMOMETER_A = observation_procedure("proc:thermometer-a", ("cold", "warm"), 2,
                                      CHANNEL_OWNER)
THERMOMETER_B = observation_procedure("proc:thermometer-b", ("cold", "warm"), 3,
                                      CHANNEL_OWNER)

WORLD: World = {
    ("proc:thermometer-a", 1): "warm",
    ("proc:thermometer-b", 1): "cold",
}


def constructed_channel(deadline: int = 8) -> Mapping[str, object]:
    """The funded path, run: request, execution, pin, and the docket around it.

    `deadline` is exposed so the adequate instance and the violating one differ
    in exactly one declared number.
    """
    from src.coherence import EXACT_SCHEDULE
    from src.settlement_interface import REFUSAL

    engine = EngineDeclaration(
        engine_id=CHANNEL_OWNER,
        procedures=(THERMOMETER_A, THERMOMETER_B),
        tolerance=EXACT_SCHEDULE,
        certificate_type="declared-outcome-space exactness",
        downside_limit=Q(2), downside_means=REFUSAL,
        core_minimum=Q(1, 4), gating_capacity=4, overtaking_bound=6)
    request = settlement_request(
        report_variable("proc:thermometer-a", 1), THERMOMETER_A, "funder:a", 0, 1,
        Q(1), "r:a")
    outcome = run_request(request, THERMOMETER_A, WORLD, 6)
    docket = DocketFacts(capacity=Q(1), queries=(
        AdmittedQuery("q:warm", 0, deadline, ("proc:thermometer-a",), Q(2), True,
                      False, Q(0)),
        AdmittedQuery("q:cold", 0, deadline, ("proc:thermometer-b",), Q(2), True,
                      False, Q(0)),
    ))
    record = SettlementRecord(
        horizon=6,
        pins=() if outcome.pin is None else (outcome.pin,),
        requests=(pinned(outcome),), positions=(), docket=docket,
        priced_states=(), live_instruments=((0, 1), (1, 2)),
        worst_case_exposure=Q(0))
    return {"engine": engine, "request": request, "outcome": outcome,
            "record": record, "procedures": {p.procedure_id: p
                                             for p in engine.procedures}}
