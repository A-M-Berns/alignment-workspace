"""The paired-run model: one principal, one exogenous history, many advisor policies.

The procedural-legitimacy round's fixture is imported rather than copied, so the
trajectories prosecuted here are objects of exactly the type its four conditions
and its target `L*` already read.  What this module adds is the smallest
structure in which a counterfactual question can be posed: an advisor with an
intervention channel, and a `Fixture` that manufactures coupled runs by holding
everything except the advisor policy fixed.

Two channels reach the principal's protected machinery, and the model is
uninteresting without both.

**The reason channel.** An advisor item whose ground is provenance-valid and
whose content the principal's *current* bearing relation says bears on the
coordinate is a licensed reason; the principal adopts what it proposes, citing
the item's own ground.

**The residual channel.** An item that is *not* a licensed reason is adopted
anyway when a non-reason feature of its delivery crosses a threshold —
repetition, salience, or bare presence, selected by `ResidualRule`.  The
principal then cites `g-root`, the conferred authority it genuinely holds over
its own machinery, so the record is indistinguishable from an autonomous
revision.

The second channel is what makes reason-mediated non-capture falsifiable rather
than definitional.  If advisor input could only enter through the reason port,
`Z = F(E, L)` would hold by construction of the transition rule and the
prosecution would be theatre.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Mapping, Sequence

from conditions import (ADEQUACY, BEARING, ENTITLEMENT, GENERATION, Edit,
                        Encounter, Inquiry, State, Trajectory, evaluate,
                        project)
from environment import Environment, LStarReport, lstar
from forest import DISCHARGE, IDENTIFY, REFINE, SUSPEND
from provenance import CONFERRED, DERIVED, Ground, GroundStore, provenance_valid

VERDICT = "verdict"
SUBSTANCE = "s-harm"

#: The fifth machinery coordinate.  It is not a field of the procedural round's
#: `State`, and no condition there reads it; attack I is what forces it.
IDENTIFICATION = "identification"

#: A writable field that answers no normative question.  See `Machinery.noise`.
NOISE = "noise"

MACHINERY_FIVE = (GENERATION, ENTITLEMENT, BEARING, ADEQUACY, IDENTIFICATION)
MACHINERY_FOUR = (GENERATION, ENTITLEMENT, BEARING, ADEQUACY)
MACHINERY_ALL = MACHINERY_FIVE + (NOISE,)

#: Deterministic closure order.  Cheap witnesses are tried first, which is what
#: makes a widened adequacy relation bite without the advisor writing a
#: discharge.
WITNESS_ORDER = ("w-cheap", "w-partial", "w-narrow", "w-welfare", "w-real")

ROOT = Ground("g-root", 0, "settlement-report",
              frozenset({VERDICT, BEARING, ADEQUACY, GENERATION, ENTITLEMENT}),
              origin=CONFERRED, filed_by="settlement")

CONFERRED_SCOPE = {"g-root": ROOT.scope}


# --------------------------------------------------------------------------
# Advisor input
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Proposal:
    """A machinery change, as an argument for it would state it.

    `key is None` replaces the whole coordinate; otherwise the entry is set, or
    deleted when `value is None`.
    """

    coordinate: str
    key: str | None
    value: object

    def signature(self) -> tuple:
        value = self.value
        if isinstance(value, frozenset):
            value = tuple(sorted(value))
        elif isinstance(value, Mapping):
            value = tuple(sorted(
                (k, tuple(sorted(v)) if isinstance(v, frozenset) else v)
                for k, v in value.items()))
        return (self.coordinate, self.key, value)


@dataclass(frozen=True)
class Item:
    """One advisor-originating input, with its content and its delivery.

    `content`, `coordinate` and `ground_id` are what a licensing judgment reads.
    `repetitions`, `salience` and `position` are delivery: features of how the
    input arrives that no normative practice in this fixture treats as reasons.
    Keeping the two groups in one record and separating them in the predicates
    is the point; a model that only carried the first could not state the
    question.
    """

    content: str
    coordinate: str
    proposal: Proposal
    ground_id: str = "g-root"
    repetitions: int = 1
    salience: str = "plain"
    position: int = 0

    def key(self) -> tuple[str, str]:
        """How a reason is named."""
        return (self.content, self.coordinate)

    def fine_key(self) -> tuple:
        """How a reason is named, together with what it licenses.

        `test_structure` exhibits why the first is not enough: two proposals
        offered under one name make the coarse trace agree while the protected
        state diverges, with no residual channel involved at all.
        """
        return (self.content, self.coordinate, self.proposal.signature())


@dataclass(frozen=True)
class Policy:
    """An advisor's whole intervention, declared up front.

    `suppress_encounters` is the channel by which an advisor controls what
    *arises* rather than what the principal makes of what arises.  A policy that
    uses it is not coupled to one that does not — see `Fixture.coupled`.
    """

    name: str
    messages: Mapping[int, tuple[Item, ...]] = field(default_factory=dict)
    suppress_encounters: frozenset[int] = frozenset()

    def items(self, step: int) -> tuple[Item, ...]:
        return tuple(self.messages.get(step, ()))


NULL = Policy("null")


# --------------------------------------------------------------------------
# The principal
# --------------------------------------------------------------------------

RESIDUAL_RULES = ("repetition", "salience", "presence", "none")


def residual_pressure(rule: str, item: Item) -> bool:
    """Whether a non-reason feature of delivery is enough to move the principal.

    Several rules rather than one, because a result that held for a single
    hand-picked susceptibility would be a result about that susceptibility.
    `none` is the principal with no residual channel at all; it exists so a test
    can show what the condition's content depends on.
    """
    if rule == "none":
        return False
    if rule == "repetition":
        return item.repetitions >= 3
    if rule == "salience":
        return item.salience == "high"
    if rule == "presence":
        return item.repetitions >= 1
    raise ValueError(rule)


@dataclass(frozen=True)
class Machinery:
    """The principal's five protected coordinates, carried alongside the
    procedural round's `State` because that state has only four."""

    generation: Mapping[str, str]
    entitlement: frozenset[str]
    bearing: Mapping[str, frozenset[str]]
    adequacy: Mapping[str, frozenset[str]]
    identification: frozenset[str]
    #: A mutable field no normative question reads.  It exists so a test can
    #: show the protected object is defined by what the process answers rather
    #: than by which fields happen to be writable.
    noise: frozenset[str] = frozenset()

    def get(self, coordinate: str):
        return {GENERATION: self.generation, ENTITLEMENT: self.entitlement,
                BEARING: self.bearing, ADEQUACY: self.adequacy,
                IDENTIFICATION: self.identification, NOISE: self.noise}[coordinate]


def apply_proposal(machinery: Machinery, proposal: Proposal) -> Machinery:
    current = machinery.get(proposal.coordinate)
    if proposal.key is None:
        updated = proposal.value
    elif isinstance(current, frozenset):
        updated = (current | {proposal.key}) if proposal.value else (
            current - {proposal.key})
    else:
        updated = dict(current)
        if proposal.value is None:
            updated.pop(proposal.key, None)
        else:
            updated[proposal.key] = proposal.value
    return replace(machinery, **{proposal.coordinate: updated})


def licensed(machinery: Machinery, store: GroundStore, item: Item,
             step: int) -> bool:
    """Whether the practice presently treats this item as a reason for its
    coordinate: provenance-valid authority, and content the principal's own
    bearing relation says bears there.

    Reads the pre-step machinery only.  It never reads delivery, never reads a
    later state, and never reads whether adopting the proposal turns out well.
    """
    verdict = provenance_valid(store, item.ground_id, item.coordinate, step)
    if not verdict.valid:
        return False
    return item.coordinate in machinery.bearing.get(item.content, frozenset())


def _first_adequate(machinery: Machinery, substance: str) -> str | None:
    for witness in WITNESS_ORDER:
        if substance in machinery.adequacy.get(witness, frozenset()):
            return witness
    return None


# --------------------------------------------------------------------------
# The principal's standing plan
# --------------------------------------------------------------------------
#
# Actions are the principal's own algorithm, identical across coupled arms.  A
# guarded action that finds its precondition unmet is a no-op, which is how one
# arm's advisor influence produces a different trajectory from the same plan.
#
#   ("docket",)                       docket every entitled generated inquiry
#   ("split", target, branches)       refine
#   ("merge", targets, survivor)      identify, but only under a held licence
#   ("close", target)                 discharge on the first adequate witness,
#                                     read against the substance the liability
#                                     was *filed* under
#   ("suspend", target)
#   ("defeat", ground_id, coordinate, value)
#   ("revise", proposal)              the principal's own revision


@dataclass(frozen=True)
class Run:
    trajectory: Trajectory
    machinery: Machinery
    #: The machinery before every step, and after the last.  The protected
    #: object is a property of this sequence, not of its final element.
    states: tuple[Machinery, ...]
    ltrace: tuple[frozenset[tuple[str, str]], ...]
    ltrace_fine: tuple[frozenset[tuple], ...]
    delivered: tuple[frozenset[tuple[str, str]], ...]
    encounters: tuple[Encounter, ...]
    environment: Environment

    def four(self):
        return evaluate(self.trajectory)

    def target(self) -> LStarReport:
        return self.target_against(self.environment)

    def target_against(self, environment: Environment) -> LStarReport:
        uses, discharges, confrontations = project(self.trajectory)
        return lstar(environment, uses, discharges, confrontations)

    def record(self) -> tuple:
        """Everything an auditor holding the joint record could read."""
        return (self.trajectory.edits, self.encounters, self.ltrace,
                self.ltrace_fine, self.delivered)


@dataclass(frozen=True)
class Fixture:
    """Everything a run needs except the advisor policy.

    Two runs of one fixture share initial state, exogenous encounters, the
    principal's algorithm, the ground store and the environment, and differ only
    in the policy.  That is the coupling relation, enforced by construction
    rather than asserted after the fact.
    """

    name: str
    machinery: Machinery
    encounters: tuple[Encounter, ...]
    plan: tuple[tuple[tuple, ...], ...]
    environment: Environment
    grounds: GroundStore = GroundStore((ROOT,))
    rule: str = "repetition"
    due_pool: Mapping[int, frozenset[tuple[str, str]]] = field(
        default_factory=dict)
    capacity: int = 2
    #: When set, the residual channel applies *this* revision and ignores what
    #: the item argued for — a principal moved by exposure alone.  It is the
    #: finite analogue of the dose-response note's content-blind advisee, and
    #: exists to be run against its content-mediated twin.
    content_blind: Proposal | None = None

    def coupled(self, first: Policy, second: Policy) -> bool:
        """Whether varying between these two policies keeps the exogenous
        history fixed.  An advisor that suppresses an encounter changes what
        arises, and the pair is then not a counterfactual pair at all."""
        return first.suppress_encounters == second.suppress_encounters

    def run(self, policy: Policy) -> Run:
        machinery = self.machinery
        encounters = tuple(e for index, e in enumerate(self.encounters)
                           if index not in policy.suppress_encounters)
        states: list[Machinery] = []
        origin: dict[str, str] = {}
        liabilities: dict[str, frozenset[str]] = {}
        closed: set[str] = set()
        edits: list[Edit] = []
        ltrace: list[frozenset[tuple[str, str]]] = []
        ltrace_fine: list[frozenset[tuple]] = []
        delivered: list[frozenset[tuple[str, str]]] = []

        for step in range(len(self.plan)):
            states.append(machinery)
            before = machinery
            items = policy.items(step)
            delivered.append(frozenset(i.key() for i in items))
            admitted: set[tuple[str, str]] = set()
            admitted_fine: set[tuple] = set()
            cited: list[tuple[str, str]] = []
            moved: set[str] = set()

            for item in sorted(items, key=lambda i: (i.position, i.content)):
                if licensed(before, self.grounds, item, step):
                    admitted.add(item.key())
                    admitted_fine.add(item.fine_key())
                    machinery = apply_proposal(machinery, item.proposal)
                    if item.proposal.coordinate not in (IDENTIFICATION, NOISE):
                        cited.append((item.ground_id, item.proposal.coordinate))
                        moved.add(item.proposal.coordinate)
                elif residual_pressure(self.rule, item):
                    proposal = self.content_blind or item.proposal
                    machinery = apply_proposal(machinery, proposal)
                    if proposal.coordinate not in (IDENTIFICATION, NOISE):
                        cited.append(("g-root", proposal.coordinate))
                        moved.add(proposal.coordinate)
            ltrace.append(frozenset(admitted))
            ltrace_fine.append(frozenset(admitted_fine))

            moves: dict[str, str] = {}
            dispositions: dict[str, tuple[str, tuple[str, ...], str | None]] = {}
            dockets: list[Inquiry] = []

            for action in self.plan[step]:
                kind = action[0]
                if kind == "docket":
                    for encounter in encounters:
                        if encounter.at != step:
                            continue
                        substance = before.generation.get(encounter.kind)
                        if substance is None or substance not in before.entitlement:
                            continue
                        inquiry_id = f"q-{encounter.kind}-{encounter.at}"
                        dockets.append(Inquiry(inquiry_id, substance, encounter.at))
                        origin[inquiry_id] = substance
                        liabilities[inquiry_id] = frozenset({substance})
                elif kind == "split":
                    _, target, branches = action
                    if target not in liabilities or target in closed:
                        continue
                    dispositions[target] = (REFINE, tuple(branches), "w-split")
                    for branch in branches:
                        origin[branch] = origin[target]
                        liabilities[branch] = liabilities[target]
                    closed.add(target)
                elif kind == "merge":
                    _, targets, survivor = action
                    if not before.identification:
                        continue
                    if any(t not in liabilities or t in closed for t in targets):
                        continue
                    for target in targets:
                        dispositions[target] = (IDENTIFY, (survivor,),
                                                sorted(before.identification)[0])
                        closed.add(target)
                    origin[survivor] = origin[targets[0]]
                    liabilities[survivor] = frozenset().union(
                        *(liabilities[t] for t in targets))
                elif kind == "close":
                    _, target = action
                    if target not in liabilities or target in closed:
                        continue
                    witness = _first_adequate(before, origin[target])
                    if witness is None:
                        dispositions[target] = (SUSPEND, (), "route-later")
                    else:
                        dispositions[target] = (DISCHARGE, (), witness)
                        closed.add(target)
                elif kind == "suspend":
                    _, target = action
                    if target not in liabilities or target in closed:
                        continue
                    dispositions[target] = (SUSPEND, (), "route-later")
                elif kind == "defeat":
                    _, ground_id, coordinate, value = action
                    ground = self.grounds.get(ground_id)
                    if ground is None:
                        continue
                    if coordinate not in before.bearing.get(ground.content,
                                                            frozenset()):
                        continue
                    if not provenance_valid(self.grounds, ground_id, coordinate,
                                            step).valid:
                        continue
                    moves[coordinate] = value
                    cited.append((ground_id, coordinate))
                elif kind == "revise":
                    proposal = action[1]
                    machinery = apply_proposal(machinery, proposal)
                    if proposal.coordinate not in (IDENTIFICATION, NOISE):
                        cited.append(("g-root", proposal.coordinate))
                        moved.add(proposal.coordinate)
                else:
                    raise ValueError(kind)

            machinery_moves = {c: machinery.get(c) for c in sorted(moved)}
            edits.append(Edit(f"{self.name}-{step}", moves=moves,
                              machinery_moves=machinery_moves,
                              cited=tuple(cited),
                              dispositions=dispositions,
                              dockets=tuple(dockets)))

        initial = State(0, {VERDICT: "open"}, self.machinery.bearing,
                        self.machinery.adequacy, self.machinery.generation,
                        self.machinery.entitlement, {})
        trajectory = Trajectory(initial, tuple(edits), encounters,
                                self.grounds, capacity=self.capacity)
        states.append(machinery)
        return Run(trajectory, machinery, tuple(states), tuple(ltrace),
                   tuple(ltrace_fine), tuple(delivered), encounters,
                   self.environment)
