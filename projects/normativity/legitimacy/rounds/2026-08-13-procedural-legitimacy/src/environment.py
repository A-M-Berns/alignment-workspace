"""The target `L*`, stated against something the reasoner does not control.

A sufficiency question needs an independent target, so `L*` is defined here
against an **environment**: the authority that was actually conferred, what
grounds actually bear on, which demands actually arise, and what actually settles
them.  None of this is a record the reasoner writes; all of it is what the
reasoner is answerable *to*.

This is the whole methodological point of the round.  The four candidate
conditions are predicates of a record.  `L*` is not.  Whether the first entail
the second is then a real question rather than a definitional one, and a
counterexample is adjudicated by the environment rather than by taste.

The environment is a modelling device, not a claim that such a structure exists
or is knowable.  It stands in for "what a fully informed critic would say", which
is the only referent against which "the reasoner should have confronted that" can
mean anything.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Mapping, Sequence


@dataclass(frozen=True)
class ObjectiveDemand:
    """A normative demand that arises whether or not the reasoner notices it.

    `substance` is what would have to be addressed for the demand to be met.  It
    is deliberately an opaque token: the model needs demands to have identity and
    to be satisfiable-or-not, and needs nothing else about them.
    """

    demand_id: str
    arises_at: int
    substance: str
    entitled: bool = True


@dataclass(frozen=True)
class Environment:
    """What the reasoner is answerable to.

    `conferred` — the scope an external authority actually granted a root ground.
    `bears_on` — the coordinates a ground's content actually bears on.
    `settles` — the substances a witness actually settles.
    `demands` — what actually arises.

    The reasoner's own machinery has counterparts of the middle two, and the gap
    between the two copies is where this round's result lives.
    """

    conferred: Mapping[str, frozenset[str]] = field(default_factory=dict)
    bears_on: Mapping[str, frozenset[str]] = field(default_factory=dict)
    settles: Mapping[str, frozenset[str]] = field(default_factory=dict)
    demands: tuple[ObjectiveDemand, ...] = ()
    service_window: int = 1

    def demand(self, demand_id: str) -> ObjectiveDemand | None:
        for item in self.demands:
            if item.demand_id == demand_id:
                return item
        return None


# --------------------------------------------------------------------------
# The four clauses of L*
# --------------------------------------------------------------------------

L_NON_MANUFACTURE = "lstar.authority_not_conferred"
L_CONFRONTATION = "lstar.entitled_demand_unconfronted"
L_LICENSING = "lstar.ground_does_not_bear"
L_SUBSTANCE = "lstar.discharge_does_not_settle"


@dataclass(frozen=True)
class LStarFailure:
    clause: str
    subject: str
    at: int
    detail: str = ""


@dataclass(frozen=True)
class LStarReport:
    failures: tuple[LStarFailure, ...]

    @property
    def legitimate(self) -> bool:
        return not self.failures

    def clauses(self) -> tuple[str, ...]:
        return tuple(sorted({f.clause for f in self.failures}))


@dataclass(frozen=True)
class Use:
    """One exercise of authority, as the record shows it, ready for adjudication.

    A trajectory is projected into a list of these before `L*` is evaluated, so
    the target does not depend on the shape of the trajectory representation.
    """

    at: int
    ground_id: str
    content: str
    coordinate: str
    claimed_scope: frozenset[str]
    root_ids: frozenset[str]


@dataclass(frozen=True)
class Discharge:
    """One terminal closure, with what the reasoner offered as backing."""

    at: int
    liability_id: str
    substance: str
    witness: str


@dataclass(frozen=True)
class Confrontation:
    """One demand the reasoner actually took up, and when."""

    demand_id: str
    at: int


def lstar(environment: Environment, uses: Sequence[Use],
          discharges: Sequence[Discharge],
          confrontations: Sequence[Confrontation]) -> LStarReport:
    """Adjudicate a trajectory's projection against the environment.

    Four clauses, matching the four things the target says a procedure owes:
    exercise only authority that was granted, confront what arises, use reasons
    only where they bear, and close a demand only on something that settles it.
    """
    failures: list[LStarFailure] = []

    for use in uses:
        granted: set[str] = set()
        for root in use.root_ids:
            granted |= set(environment.conferred.get(root, frozenset()))
        outside = set(use.claimed_scope) - granted
        if outside:
            failures.append(LStarFailure(
                L_NON_MANUFACTURE, use.ground_id, use.at,
                f"claims {sorted(outside)} beyond what its roots were granted"))
        if use.coordinate not in environment.bears_on.get(use.content, frozenset()):
            failures.append(LStarFailure(
                L_LICENSING, use.ground_id, use.at,
                f"{use.content} does not bear on {use.coordinate}"))

    # Keyed on substance, not on the reasoner's name for the question: taking up
    # a narrowly-formulated inquiry does not confront a demand whose substance it
    # does not carry, and that is what makes formulation manipulation adjudicable.
    taken = {c.demand_id: c.at for c in confrontations}
    for demand in environment.demands:
        if not demand.entitled:
            continue
        when = taken.get(demand.substance)
        if when is None or when > demand.arises_at + environment.service_window:
            failures.append(LStarFailure(
                L_CONFRONTATION, demand.demand_id, demand.arises_at,
                "never confronted" if when is None else f"confronted late at {when}"))

    for closure in discharges:
        if closure.substance not in environment.settles.get(closure.witness, frozenset()):
            failures.append(LStarFailure(
                L_SUBSTANCE, closure.liability_id, closure.at,
                f"{closure.witness} does not settle {closure.substance}"))

    return LStarReport(tuple(failures))
