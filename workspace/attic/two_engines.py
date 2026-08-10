"""Two engines, one mechanism: the minimal multi-engine instance.

One deductive engine (a finite lookup-table prover) and one empirical engine
(the constructed observation channel), with disjoint declared jurisdictions and
per-provenance fenced subsidy accounts.  The point of building two rather than
one is that three properties of the interface are invisible with a single
engine, and each gets a witness here.

**Redundancy is welcome, and it never reaches the settled record.**  Two
thermometers bearing on one world claim are two procedures, hence two report
variables, hence two pins that cannot conflict -- write-once is about a
variable, and no variable has two pinners.  Their disagreement is real and it
lives, constitutively, in the answerable layer: two endorsed bridge warrants
pulling opposite ways make the *book's* region infeasible, which is a sure-loss
objection against the book, not a contradiction in the record.  That is the
whole content of the write-once clause's redundancy provision, and
`disagreement_witness` displays it.

**Breach is isolated by channel.**  A tolerance breach in the empirical channel
quarantines that channel; the logical channel runs on.  The witness distinguishes
tolling *caused by the breach* from the tolling the rateless logical channel
already carries under the ripeness clause, because otherwise "the logical
channel is untolled" would be false for a reason that has nothing to do with
isolation.

**The purse composes only inside its fences.**  Each engine declares its own
downside limit; the mechanism's exposure is bounded by the fenced sum exactly
when no transfer crosses between provenances.  A crossing transfer is the
existing cross-subsidy objection, fired on a declared-fence violation between
the two provenances -- reused, not reinvented.

Finiteness discipline.  Two engines, finitely many procedures, pins, accounts
and transfers.

All arithmetic is exact rationals.  No floating point.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.case_stream import Fence, Transfer, cross_subsidy_grounds, crosses_fence
from src.coherence import EXACT_SCHEDULE, ToleranceSchedule
from src.grammar import Grounds
from src.leverage_interval import (
    Book,
    Endorsement,
    Language,
    SettledFact,
    compute_interval,
    sure_loss_grounds,
)
from src.settlement_channel import (
    THERMOMETER_A,
    THERMOMETER_B,
    BridgeWarrant,
    observation_procedure,
)
from src.settlement_interface import (
    EMPIRICAL,
    LOGICAL,
    REFUSAL,
    AdmittedQuery,
    DocketFacts,
    EngineDeclaration,
    Pin,
    Procedure,
    SettlementRecord,
    report_variable,
)

LOGICAL_OWNER = "engine:deductive"
EMPIRICAL_OWNER = "engine:empirical"

LOGICAL_ACCOUNT = "account:logical"
EMPIRICAL_ACCOUNT = "account:empirical"

LOGICAL_RESERVE = "account:logical-reserve"
EMPIRICAL_RESERVE = "account:empirical-reserve"

# A provenance's fence encloses that provenance's whole account family, so a
# transfer inside one provenance does not cross and a transfer between the two
# does.  A fence around a single account would make every movement a crossing
# and the objection would carry no information.
LOGICAL_FENCE = Fence("fence:logical", (LOGICAL_ACCOUNT, LOGICAL_RESERVE),
                      declared=True)
EMPIRICAL_FENCE = Fence("fence:empirical", (EMPIRICAL_ACCOUNT, EMPIRICAL_RESERVE),
                        declared=True)


# --------------------------------------------------------------------------
# The two engines
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class LookupProver:
    """A finite lookup-table prover: the deductive engine, at its smallest.

    Its pen decides the sentences in its table and nothing else, which is
    exactly the declaration discipline the completeness clause needs -- the
    declared jurisdiction lies inside the decidable fragment because the table
    *is* the decidable fragment.  Its purse refuses.
    """

    engine_id: str = LOGICAL_OWNER
    table: tuple[tuple[str, str, str], ...] = (
        ("phi", "proved", "derivation:phi"),
        ("psi", "refuted", "derivation:not-psi"),
    )

    @property
    def jurisdiction(self) -> tuple[str, ...]:
        return tuple(sentence for sentence, _, _ in self.table)

    @property
    def procedures(self) -> tuple[Procedure, ...]:
        return tuple(Procedure(f"proc:decide-{sentence}", LOGICAL,
                               ("proved", "refuted"), self.engine_id)
                     for sentence in self.jurisdiction)

    @property
    def declaration(self) -> EngineDeclaration:
        return EngineDeclaration(
            engine_id=self.engine_id, procedures=self.procedures,
            tolerance=EXACT_SCHEDULE,
            certificate_type="lookup-table exactness",
            downside_limit=Q(0), downside_means=REFUSAL,
            core_minimum=Q(1, 4), gating_capacity=2, overtaking_bound=4,
            logical_jurisdiction=self.jurisdiction)

    def pins(self, date: int = 1) -> tuple[Pin, ...]:
        return tuple(
            Pin(report_variable(f"proc:decide-{sentence}", date),
                f"proc:decide-{sentence}", date, value, (), derivation)
            for sentence, value, derivation in self.table)


def empirical_engine(tolerance: ToleranceSchedule = EXACT_SCHEDULE,
                     ) -> EngineDeclaration:
    """The observation apparatus, declared as an engine of its own."""
    return EngineDeclaration(
        engine_id=EMPIRICAL_OWNER, procedures=(THERMOMETER_A, THERMOMETER_B),
        tolerance=tolerance,
        certificate_type="declared-outcome-space exactness",
        downside_limit=Q(2), downside_means=REFUSAL,
        core_minimum=Q(1, 4), gating_capacity=4, overtaking_bound=6)


# --------------------------------------------------------------------------
# Disjoint jurisdictions
# --------------------------------------------------------------------------


def jurisdictions_disjoint(engines: Sequence[EngineDeclaration]) -> tuple[str, ...]:
    """Every procedure is owned by exactly one engine, and owners match.

    Write-once is owner-only, so overlapping jurisdictions would make the clause
    unenforceable: two engines could each write the same variable once.
    """
    obstructions: list[str] = []
    seen: dict[str, str] = {}
    for engine in engines:
        for procedure in engine.procedures:
            if procedure.owner != engine.engine_id:
                obstructions.append(
                    f"procedure {procedure.procedure_id!r} is declared by "
                    f"{engine.engine_id!r} but names owner {procedure.owner!r}")
            if procedure.procedure_id in seen:
                obstructions.append(
                    f"procedure {procedure.procedure_id!r} is claimed by both "
                    f"{seen[procedure.procedure_id]!r} and {engine.engine_id!r}")
            seen[procedure.procedure_id] = engine.engine_id
    return tuple(obstructions)


# --------------------------------------------------------------------------
# Witness (a): disagreement entirely in the answerable layer
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class DisagreementWitness:
    pins: tuple[Pin, ...]
    warrants: tuple[BridgeWarrant, ...]
    distinct_variables: bool
    pin_conflict: bool
    region_infeasible: bool
    answerable_grounds: Grounds | None


def disagreement_witness() -> DisagreementWitness:
    """Two thermometers disagreeing about one world claim, with no pin conflict.

    Thermometer A returns warm at date one and thermometer B returns cold at
    date one.  These are distinct procedures, so distinct report variables, so
    two pins that write-once cannot bring into conflict: nothing in the settled
    record is contradictory, and no clause is breached.

    The disagreement is nonetheless real, and it appears exactly where the
    interface says it should.  Each pin reaches the world claim through an
    endorsed bridge warrant, and the two warrants pull opposite ways; compiled
    into the book they make its region infeasible, which the existing sure-loss
    surface reports against the *book*.  The engines are untouched.
    """
    pins = (
        Pin(report_variable("proc:thermometer-a", 1), "proc:thermometer-a", 1,
            "warm", ("funder:a",)),
        Pin(report_variable("proc:thermometer-b", 1), "proc:thermometer-b", 1,
            "cold", ("funder:b",)),
    )
    warrants = (
        BridgeWarrant("w:a", pins[0].variable_id, "the room is hot", "supports"),
        BridgeWarrant("w:b", pins[1].variable_id, "the room is hot", "undercuts"),
    )
    language = Language(("hot", "mild"), {"H": ("hot",)})
    book = Book(1, (
        Endorsement("bridge:a", (Q(1), Q(0)), Q(3, 4)),
        Endorsement("bridge:b", (Q(-1), Q(0)), Q(-1, 4)),
    ))
    interval = compute_interval(language, book, (), "H")
    grounds = sure_loss_grounds(interval, "g:thermometer-disagreement")
    variables = {pin.variable_id for pin in pins}
    return DisagreementWitness(
        pins, warrants, len(variables) == len(pins),
        len(variables) != len(pins), interval.infeasible, grounds)


# --------------------------------------------------------------------------
# Witness (b): breach isolation
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ChannelClock:
    """A channel's clock state, with the two tolling causes kept apart."""

    channel: str
    frozen: bool
    tolled_by_breach: bool
    tolled_rateless: bool

    @property
    def tolled(self) -> bool:
        return self.tolled_by_breach or self.tolled_rateless


def quarantine(breached_channel: str,
               queries: Sequence[tuple[str, str]]) -> tuple[ChannelClock, ...]:
    """Freeze the channel in breach; leave every other channel running.

    `queries` pairs a query identifier with the channel it depends on.  The two
    tolling causes are reported separately on purpose: the rateless logical
    channel is tolled under the ripeness clause whatever happens elsewhere, so
    reporting a single flag would make isolation look like a success it had not
    earned.
    """
    clocks: list[ChannelClock] = []
    for query_id, channel in queries:
        clocks.append(ChannelClock(
            channel, frozen=channel == breached_channel,
            tolled_by_breach=channel == breached_channel,
            tolled_rateless=channel == LOGICAL))
    return tuple(clocks)


@dataclass(frozen=True)
class IsolationWitness:
    clocks: tuple[ChannelClock, ...]
    empirical_frozen: bool
    logical_frozen: bool
    logical_tolled_by_breach: bool
    logical_still_running: bool


def breach_isolation_witness() -> IsolationWitness:
    """A tolerance breach in the empirical channel leaves the logical one running."""
    clocks = quarantine(EMPIRICAL, (
        ("q:warm", EMPIRICAL), ("q:cold", EMPIRICAL), ("q:phi", LOGICAL)))
    empirical = tuple(c for c in clocks if c.channel == EMPIRICAL)
    logical = tuple(c for c in clocks if c.channel == LOGICAL)
    return IsolationWitness(
        clocks,
        all(c.frozen for c in empirical),
        any(c.frozen for c in logical),
        any(c.tolled_by_breach for c in logical),
        all(not c.frozen and not c.tolled_by_breach for c in logical))


# --------------------------------------------------------------------------
# Witness (c): the composed purse
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ComposedPurse:
    """Per-provenance limits, their fenced sum, and what a crossing costs."""

    limits: tuple[tuple[str, Q], ...]
    fenced_sum: Q
    exposures: tuple[tuple[str, Q], ...]
    within_limits: bool
    crossing: Grounds | None


def compose_purse(engines: Sequence[EngineDeclaration],
                  exposures: Mapping[str, Q],
                  transfers: Sequence[Transfer] = ()) -> ComposedPurse:
    """The mechanism's exposure against the fenced sum, and the crossing objection.

    Each engine's downside limit is declared separately and bounds only its own
    provenance.  The mechanism's total exposure is bounded by the sum *provided*
    the fences hold: a transfer from one provenance's account to the other's
    moves loss across a declared boundary, and the bound over the pair stops
    meaning anything about either.  That crossing is the existing cross-subsidy
    objection, and it is reused verbatim.
    """
    limits = tuple((e.engine_id, Q(e.downside_limit if e.downside_limit is not None
                                   else 0)) for e in engines)
    fenced_sum = sum((value for _, value in limits), Q(0))
    recorded = tuple((name, Q(value)) for name, value in sorted(exposures.items()))
    within = all(Q(value) <= dict(limits).get(name, Q(0))
                 for name, value in recorded)
    crossing: Grounds | None = None
    for transfer in transfers:
        for fence in (LOGICAL_FENCE, EMPIRICAL_FENCE):
            if crosses_fence(transfer, fence):
                crossing = cross_subsidy_grounds(transfer, fence,
                                                 f"g:cross-{transfer.transfer_id}")
                break
        if crossing is not None:
            break
    return ComposedPurse(limits, fenced_sum, recorded, within, crossing)


FENCED_TRANSFER = Transfer("t:within-empirical", EMPIRICAL_ACCOUNT,
                           EMPIRICAL_RESERVE, Q(1))
CROSSING_TRANSFER = Transfer("t:logical-pays-empirical", LOGICAL_ACCOUNT,
                             EMPIRICAL_ACCOUNT, Q(1))


# --------------------------------------------------------------------------
# The instance
# --------------------------------------------------------------------------


def two_engine_instance() -> Mapping[str, object]:
    """Both engines, their disjointness check, and a record covering both."""
    prover = LookupProver()
    logical = prover.declaration
    empirical = empirical_engine()
    docket = DocketFacts(capacity=Q(2), queries=(
        AdmittedQuery("q:warm", 0, 8, ("proc:thermometer-a",), Q(2), True, False,
                      Q(0)),
        AdmittedQuery("q:phi", 0, 9, ("proc:decide-phi",), Q(1), True, True, Q(0)),
    ))
    record = SettlementRecord(
        horizon=6, pins=prover.pins(1), requests=(), positions=(), docket=docket,
        priced_states=(), live_instruments=((0, 1), (1, 2)),
        worst_case_exposure=Q(0))
    return {"prover": prover, "logical": logical, "empirical": empirical,
            "record": record, "docket": docket,
            "disjoint": jurisdictions_disjoint((logical, empirical))}
