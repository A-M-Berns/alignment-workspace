"""The empirical channel, the conduct witnesses, and the two-engine instance.

Folder-local; readable against `THEORY_12` alone.

Three things are worth reading closely, because they are where a construction
can quietly cheat.

**The request key cannot express a direction.** The key type carries a target, a
procedure, a funder and timing, and there is no field an outcome could be
written into. Directional funding is unconstructible, not forbidden by a check
that could be forgotten.

**The executor cannot see the book.** `execute` takes the procedure, the date,
and the world -- nothing else. The faithfulness axiom says a settlement's value
has no dependence on the book's states or any funding profile beyond the
declared inputs and the world; this signature makes that path unwritable *in
this implementation*. That is a disclosure, not a proof: the axiom quantifies
over every engine, and a type here constrains only this one.

**A settlement event has no answerability columns.** Its type carries no basis
tag, no stake, no charge stream, and no objection surface -- checked
structurally rather than by convention.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, replace
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.composite import (
    EMPIRICAL,
    LOGICAL,
    PRECOMMITTED,
    REFUSAL,
    Declaration,
    Docket,
    Position,
    Procedure,
    Query,
    Record,
    Request,
    RequestKey,
    Settlement,
    adequacy,
    directional_variants,
    report_variable,
)
from src.coherence import EXACT, Schedule
from src.grammar import Grounds
from src.interval import (
    Book,
    Endorsement,
    Interval,
    Language,
    SettledFact,
    compute_interval,
)

World = Mapping[tuple[str, int], str]


# --------------------------------------------------------------------------
# Procedures, execution, and settlement
# --------------------------------------------------------------------------


def observation_procedure(procedure_id: str, outcomes: Sequence[str], horizon: int,
                          owner: str) -> Procedure:
    if horizon < 0:
        raise ValueError("a declared horizon is nonnegative")
    if len(set(outcomes)) < 2:
        raise ValueError("an outcome space with fewer than two values settles nothing")
    return Procedure(procedure_id, EMPIRICAL, tuple(outcomes), owner, horizon)


def execute(procedure: Procedure, date: int, world: World) -> str | None:
    """Run a declared procedure at a date against the world. The signature is the point."""
    value = world.get((procedure.procedure_id, date))
    if value is None:
        return None
    if value not in procedure.outcome_space:
        raise ValueError(f"the world returned {value!r}, outside the declared space")
    return value


def executor_is_blind() -> bool:
    """Is the faithfulness path unwritable in this executor's signature?"""
    import inspect

    return tuple(inspect.signature(execute).parameters) == ("procedure", "date", "world")


def settlement_has_no_answerability_columns() -> bool:
    names = {f.name for f in fields(Settlement)}
    forbidden = {"basis", "basis_tag", "stake", "stakes", "charge", "charges",
                 "objection", "objections", "liability"}
    return not (names & forbidden)


def settlement_request(target: str, procedure: Procedure, funder_id: str,
                       requested: int, scheduled: int, subsidy: Q,
                       request_id: str, declared_stop: int | None = None) -> Request:
    if scheduled < requested:
        raise ValueError("a request cannot be scheduled before it is requested")
    key = RequestKey(target, procedure.procedure_id, funder_id, requested, scheduled)
    return Request(request_id, key, Q(subsidy), PRECOMMITTED,
                   declared_stop if declared_stop is not None else scheduled, None, None)


def request_is_directional(request: Request, outcomes: Sequence[str]) -> bool:
    return len(directional_variants(request.key, outcomes)) > 1


@dataclass(frozen=True)
class Execution:
    request: Request
    settlement: Settlement | None
    executed_date: int | None
    missed_horizon: bool
    detail: str


def run_request(request: Request, procedure: Procedure, world: World,
                now: int) -> Execution:
    """Request, scheduled execution, settlement -- or a missed horizon."""
    if procedure.channel != EMPIRICAL:
        raise ValueError("this path is the empirical channel")
    scheduled = request.key.scheduled_date
    due = scheduled + (procedure.horizon or 0)
    value = execute(procedure, scheduled, world)
    if value is None:
        return Execution(request, None, None, due <= now,
                         "scheduled and returned nothing by its declared horizon"
                         if due <= now else "not yet due")
    variable = report_variable(procedure.procedure_id, scheduled)
    return Execution(request, Settlement(variable, procedure.procedure_id, scheduled,
                                         value, (request.key.funder_id,)),
                     scheduled, False, "settled within the declared horizon")


def recorded(execution: Execution) -> Request:
    return replace(execution.request, executed_date=execution.executed_date,
                   settled_variable=None if execution.settlement is None
                   else execution.settlement.variable_id)


# --------------------------------------------------------------------------
# The three downstream effects
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class BridgeWarrant:
    """An endorsed, defeasible bridge from a report variable to a world claim."""

    warrant_id: str
    variable_id: str
    world_claim: str
    direction: str
    endorsed: bool = True


def constrain(language: Language, book: Book, events: Sequence[Settlement],
              valuation: Mapping[str, Q], target: str) -> Interval:
    """Effect one: the equalities enter the region, permanently."""
    settled = tuple(SettledFact(e.variable_id, Q(valuation[e.value])) for e in events
                    if e.value in valuation and language.licenses(e.variable_id))
    return compute_interval(language, book, settled, target)


@dataclass(frozen=True)
class Instrument:
    instrument_id: str
    variable_id: str
    holder: str
    counterparty: str
    payoff: Mapping[str, Q]


@dataclass(frozen=True)
class Transfer:
    transfer_id: str
    from_account: str
    to_account: str
    amount: Q


def resolve(instruments: Sequence[Instrument],
            event: Settlement) -> tuple[Transfer, ...]:
    """Effect two: instruments referencing the variable resolve at the settled value."""
    return tuple(Transfer(f"t:{i.instrument_id}", i.counterparty, i.holder,
                          Q(i.payoff.get(event.value, Q(0))))
                 for i in instruments if i.variable_id == event.variable_id)


def grounding(event: Settlement, world_claim: str, warrant: BridgeWarrant,
              grounds_id: str) -> Grounds | None:
    """Effect three: citable as evidence, never the target of an objection."""
    if warrant.variable_id != event.variable_id or warrant.world_claim != world_claim:
        return None
    if not warrant.endorsed:
        return None
    return Grounds(grounds_id, {"variable_id": event.variable_id, "value": event.value,
                                "world_claim": world_claim,
                                "warrant_id": warrant.warrant_id,
                                "direction": warrant.direction})


# --------------------------------------------------------------------------
# Clock discipline
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Ripeness:
    query_id: str
    ripe: bool
    reachable_by: int
    liability: Q
    detail: str


def ripeness_gate(query: Query, procedures: Mapping[str, Procedure]) -> Ripeness:
    """A query needing settlement faster than a horizon is unripe, without liability."""
    horizons = [procedures[p].horizon for p in query.upstream
                if p in procedures and procedures[p].horizon is not None]
    rateless = any(p in procedures and procedures[p].channel == LOGICAL
                   for p in query.upstream)
    reach = query.admitted_date + (max(horizons) if horizons else 0)
    if rateless:
        return Ripeness(query.query_id, True, reach, Q(0),
                        "admitted against the rateless channel and tolled")
    if reach > query.deadline:
        return Ripeness(query.query_id, False, reach, Q(0),
                        "unripe: no declared horizon reaches the deadline, deferred "
                        "without liability")
    return Ripeness(query.query_id, True, reach, Q(0),
                    "ripe: a declared horizon reaches the deadline")


@dataclass(frozen=True)
class Toll:
    query_id: str
    procedure_id: str
    declared_horizon: int
    actual: int
    tolled_dates: int
    chargeable_to_book: bool


def toll_missed_horizon(query: Query, procedure: Procedure,
                        actual: int) -> Toll | None:
    """A procedure past its declared horizon tolls; nothing is charged to the book."""
    if procedure.horizon is None:
        return None
    due = query.admitted_date + procedure.horizon
    if actual <= due:
        return None
    return Toll(query.query_id, procedure.procedure_id, procedure.horizon, actual,
                actual - due, False)


@dataclass(frozen=True)
class Service:
    query_id: str
    release: int
    deadline: int
    completed: int | None

    @property
    def met(self) -> bool:
        return self.completed is not None and self.completed <= self.deadline


def serve(declaration: Declaration, docket: Docket, horizon: int) -> tuple[Service, ...]:
    """Serve ripe admitted queries earliest-deadline-first at the declared capacity.

    Work within a date is divisible across queries, so this is the preemptive
    single-server schedule, for which earliest-deadline-first is optimal: if any
    schedule meets every deadline, this one does.
    """
    known = declaration.by_id
    items: list[list] = []
    for q in docket.queries:
        if not q.ripe:
            continue
        horizons = [known[p].horizon for p in q.upstream
                    if p in known and known[p].horizon is not None]
        items.append([q.query_id, q.admitted_date + (max(horizons) if horizons else 0),
                      q.deadline, Q(q.service_work), None])
    capacity = Q(docket.capacity)
    for date in range(horizon + 1):
        available = capacity
        for item in sorted(items, key=lambda r: (r[2], r[0])):
            if available <= 0:
                break
            if item[1] > date or item[3] <= 0:
                continue
            spent = min(available, item[3])
            item[3] -= spent
            available -= spent
            if item[3] == 0 and item[4] is None:
                item[4] = date
    return tuple(Service(i[0], i[1], i[2], i[4]) for i in items)


def adequacy_implies_deadlines(declaration: Declaration,
                               record: Record) -> tuple[bool, bool]:
    """`(adequacy holds, every ripe query met its deadline)` on this channel."""
    return (not adequacy(declaration, record),
            all(s.met for s in serve(declaration, record.docket, record.horizon)))


# --------------------------------------------------------------------------
# Conduct
# --------------------------------------------------------------------------


def precommitted(request: Request) -> bool:
    return (request.stopping_rule == PRECOMMITTED and request.declared_stop is not None
            and (request.executed_date is None
                 or request.executed_date == request.declared_stop))


def stopping_is_outcome_independent(request: Request, procedure: Procedure,
                                    worlds: Sequence[World], horizon: int) -> bool:
    """Replay under different worlds: the stop date must not move."""
    return len({run_request(request, procedure, w, horizon).executed_date
                for w in worlds}) <= 1


def blackout_grounds(request: Request, positions: Sequence[Position], grounds_id: str,
                     settled_date: int | None = None) -> Grounds | None:
    start = request.key.requested_date
    end = settled_date if settled_date is not None else (
        request.executed_date if request.executed_date is not None else start)
    offenders = tuple((p.actor_id, p.target, p.date) for p in positions
                      if p.actor_id == request.key.funder_id
                      and p.target == request.key.target and p.fresh
                      and start <= p.date <= end)
    if not offenders:
        return None
    return Grounds(grounds_id, {"request_id": request.request_id,
                                "funder_id": request.key.funder_id,
                                "target": request.key.target,
                                "window": (start, end), "positions": offenders})


@dataclass(frozen=True)
class Inference:
    conclusion: str
    premises: tuple[str, ...]


def common_source_grounds(inference: Inference, events: Sequence[Settlement],
                          grounds_id: str) -> Grounds | None:
    if not inference.premises:
        return None
    by_id = {e.variable_id: e for e in events}
    profiles = []
    for premise in inference.premises:
        event = by_id.get(premise)
        if event is None:
            return None
        profiles.append(set(event.funder_profile))
    shared = set.intersection(*profiles) if profiles else set()
    if not shared:
        return None
    return Grounds(grounds_id, {"conclusion": inference.conclusion,
                                "premises": tuple(inference.premises),
                                "common_funders": tuple(sorted(shared))})


# --------------------------------------------------------------------------
# The constructed channel
# --------------------------------------------------------------------------

CHANNEL_OWNER = "engine:empirical"
LOGICAL_OWNER = "engine:deductive"

THERMOMETER_A = observation_procedure("proc:thermometer-a", ("cold", "warm"), 2,
                                      CHANNEL_OWNER)
THERMOMETER_B = observation_procedure("proc:thermometer-b", ("cold", "warm"), 3,
                                      CHANNEL_OWNER)
WORLD: World = {("proc:thermometer-a", 1): "warm", ("proc:thermometer-b", 1): "cold"}


def empirical_engine(tolerance: Schedule = EXACT) -> Declaration:
    return Declaration(CHANNEL_OWNER, (THERMOMETER_A, THERMOMETER_B), tolerance,
                       "declared-outcome-space exactness", Q(2), REFUSAL, Q(1, 4), 4, 6)


def constructed_channel(deadline: int = 8) -> Mapping[str, object]:
    """The funded path, run end to end, with the docket around it."""
    engine = empirical_engine()
    request = settlement_request(report_variable("proc:thermometer-a", 1),
                                 THERMOMETER_A, "funder:a", 0, 1, Q(1), "r:a")
    execution = run_request(request, THERMOMETER_A, WORLD, 6)
    docket = Docket(Q(1), (
        Query("q:warm", 0, deadline, ("proc:thermometer-a",), Q(2), True, False, Q(0)),
        Query("q:cold", 0, deadline, ("proc:thermometer-b",), Q(2), True, False, Q(0))))
    record = Record(horizon=6,
                    settlements=() if execution.settlement is None
                    else (execution.settlement,),
                    requests=(recorded(execution),), docket=docket,
                    live_instruments=((0, 1), (1, 2)))
    return {"engine": engine, "request": request, "execution": execution,
            "record": record, "procedures": {p.procedure_id: p
                                             for p in engine.procedures}}


# --------------------------------------------------------------------------
# Two engines
# --------------------------------------------------------------------------

LOGICAL_ACCOUNT = "account:logical"
EMPIRICAL_ACCOUNT = "account:empirical"
LOGICAL_RESERVE = "account:logical-reserve"
EMPIRICAL_RESERVE = "account:empirical-reserve"


@dataclass(frozen=True)
class Fence:
    """A declared account boundary enclosing one provenance's whole family."""

    fence_id: str
    inside: tuple[str, ...]
    declared: bool = True


LOGICAL_FENCE = Fence("fence:logical", (LOGICAL_ACCOUNT, LOGICAL_RESERVE))
EMPIRICAL_FENCE = Fence("fence:empirical", (EMPIRICAL_ACCOUNT, EMPIRICAL_RESERVE))
POOLED = Fence("fence:none", (), declared=False)


def crosses(transfer: Transfer, fence: Fence) -> bool:
    if not fence.declared:
        return False
    inside = set(fence.inside)
    return (transfer.from_account in inside) != (transfer.to_account in inside)


def cross_subsidy_grounds(transfer: Transfer, fence: Fence,
                          grounds_id: str) -> Grounds | None:
    if not crosses(transfer, fence):
        return None
    return Grounds(grounds_id, {"transfer_id": transfer.transfer_id,
                                "fence_id": fence.fence_id,
                                "amount": Q(transfer.amount)})


FENCED_TRANSFER = Transfer("t:within-empirical", EMPIRICAL_ACCOUNT, EMPIRICAL_RESERVE,
                           Q(1))
CROSSING_TRANSFER = Transfer("t:logical-pays-empirical", LOGICAL_ACCOUNT,
                             EMPIRICAL_ACCOUNT, Q(1))


@dataclass(frozen=True)
class LookupProver:
    """A finite table of decided sentences: the deductive engine, at its smallest."""

    engine_id: str = LOGICAL_OWNER
    table: tuple[tuple[str, str, str], ...] = (
        ("phi", "proved", "derivation:phi"),
        ("psi", "refuted", "derivation:not-psi"))

    @property
    def jurisdiction(self) -> tuple[str, ...]:
        return tuple(s for s, _, _ in self.table)

    @property
    def procedures(self) -> tuple[Procedure, ...]:
        return tuple(Procedure(f"proc:decide-{s}", LOGICAL, ("proved", "refuted"),
                               self.engine_id) for s in self.jurisdiction)

    @property
    def declaration(self) -> Declaration:
        return Declaration(self.engine_id, self.procedures, EXACT, "table exactness",
                           Q(0), REFUSAL, Q(1, 4), 2, 4, self.jurisdiction)

    def settlements(self, date: int = 1) -> tuple[Settlement, ...]:
        return tuple(Settlement(report_variable(f"proc:decide-{s}", date),
                                f"proc:decide-{s}", date, v, (), d)
                     for s, v, d in self.table)


def jurisdictions_disjoint(engines: Sequence[Declaration]) -> tuple[str, ...]:
    obs, seen = [], {}
    for e in engines:
        for p in e.procedures:
            if p.owner != e.engine_id:
                obs.append(f"{p.procedure_id!r} is declared by {e.engine_id!r} but "
                           f"names owner {p.owner!r}")
            if p.procedure_id in seen:
                obs.append(f"{p.procedure_id!r} is claimed by both {seen[p.procedure_id]!r}"
                           f" and {e.engine_id!r}")
            seen[p.procedure_id] = e.engine_id
    return tuple(obs)


@dataclass(frozen=True)
class Disagreement:
    events: tuple[Settlement, ...]
    warrants: tuple[BridgeWarrant, ...]
    distinct_variables: bool
    settlement_conflict: bool
    region_infeasible: bool


def disagreement_witness() -> Disagreement:
    """Two procedures disagreeing about one world claim, with no settled-record conflict."""
    events = (Settlement(report_variable("proc:thermometer-a", 1), "proc:thermometer-a",
                         1, "warm", ("funder:a",)),
              Settlement(report_variable("proc:thermometer-b", 1), "proc:thermometer-b",
                         1, "cold", ("funder:b",)))
    warrants = (BridgeWarrant("w:a", events[0].variable_id, "the room is hot",
                              "supports"),
                BridgeWarrant("w:b", events[1].variable_id, "the room is hot",
                              "undercuts"))
    language = Language(("hot", "mild"), {"H": ("hot",)})
    book = Book(1, (Endorsement("bridge:a", (Q(1), Q(0)), Q(3, 4)),
                    Endorsement("bridge:b", (Q(-1), Q(0)), Q(-1, 4))))
    interval = compute_interval(language, book, (), "H")
    ids = {e.variable_id for e in events}
    return Disagreement(events, warrants, len(ids) == len(events),
                        len(ids) != len(events), interval.infeasible)


@dataclass(frozen=True)
class Clock:
    channel: str
    frozen: bool
    tolled_by_breach: bool
    tolled_rateless: bool

    @property
    def tolled(self) -> bool:
        return self.tolled_by_breach or self.tolled_rateless


def quarantine(breached: str, queries: Sequence[tuple[str, str]]) -> tuple[Clock, ...]:
    """Freeze the channel in breach; leave every other channel running.

    The two tolling causes are reported separately on purpose: the rateless
    channel is tolled under the ripeness clause whatever happens elsewhere, so a
    single flag would let that masquerade as a failure of isolation.
    """
    return tuple(Clock(channel, channel == breached, channel == breached,
                       channel == LOGICAL) for _, channel in queries)


@dataclass(frozen=True)
class Purse:
    limits: tuple[tuple[str, Q], ...]
    fenced_sum: Q
    exposures: tuple[tuple[str, Q], ...]
    within_limits: bool
    crossing: Grounds | None


def compose_purse(engines: Sequence[Declaration], exposures: Mapping[str, Q],
                  transfers: Sequence[Transfer] = ()) -> Purse:
    """Per-provenance limits, their fenced sum, and what a crossing costs."""
    limits = tuple((e.engine_id, Q(e.downside_limit if e.downside_limit is not None
                                   else 0)) for e in engines)
    recorded_exposures = tuple((k, Q(v)) for k, v in sorted(exposures.items()))
    within = all(Q(v) <= dict(limits).get(k, Q(0)) for k, v in recorded_exposures)
    crossing = None
    for transfer in transfers:
        for fence in (LOGICAL_FENCE, EMPIRICAL_FENCE):
            if crosses(transfer, fence):
                crossing = cross_subsidy_grounds(transfer, fence,
                                                 f"g:cross-{transfer.transfer_id}")
                break
        if crossing is not None:
            break
    return Purse(limits, sum((v for _, v in limits), Q(0)), recorded_exposures,
                 within, crossing)


def two_engine_instance() -> Mapping[str, object]:
    prover = LookupProver()
    logical, empirical = prover.declaration, empirical_engine()
    docket = Docket(Q(2), (
        Query("q:warm", 0, 8, ("proc:thermometer-a",), Q(2), True, False, Q(0)),
        Query("q:phi", 0, 9, ("proc:decide-phi",), Q(1), True, True, Q(0))))
    record = Record(horizon=6, settlements=prover.settlements(1), docket=docket,
                    live_instruments=((0, 1), (1, 2)))
    return {"prover": prover, "logical": logical, "empirical": empirical,
            "record": record, "disjoint": jurisdictions_disjoint((logical, empirical))}
