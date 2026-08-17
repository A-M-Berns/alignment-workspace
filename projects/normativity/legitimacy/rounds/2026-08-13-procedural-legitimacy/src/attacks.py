"""The whole-architecture prosecution: twelve trajectories built to pass.

Each builder returns a `(trajectory, environment)` pair so the four conditions
and the independent target can be evaluated on the same object.  No builder
asserts a verdict; the tests read verdicts off `conditions.evaluate` and
`environment.lstar`.

The base world is small on purpose: one substantive coordinate, one demand, one
conferred authority, and the four pieces of machinery.  That is the least
structure in which "the reasoner rewrote the standard that judges it, with
authority it really had" can be posed.
"""

from __future__ import annotations

from dataclasses import replace

from conditions import (ADEQUACY, BEARING, ENTITLEMENT, GENERATION, Edit,
                        Encounter, Inquiry, Liability, State, Trajectory)
from environment import Environment, ObjectiveDemand
from forest import DISCHARGE, IDENTIFY, LOSE, REFINE, SUSPEND
from provenance import CONFERRED, DERIVED, Ground, GroundStore

VERDICT = "verdict"
SUBSTANCE = "s-harm"

# The conferred root: an external source grants authority over the verdict
# coordinate and over the reasoner's own machinery.  Granting the second is not
# an oversight — without it no legitimate self-revision is possible at all, which
# attack K checks.
ROOT = Ground("g-root", 0, "settlement-report", frozenset(
    {VERDICT, BEARING, ADEQUACY, GENERATION, ENTITLEMENT}),
    origin=CONFERRED, filed_by="settlement")

CONFERRED_SCOPE = {"g-root": frozenset(
    {VERDICT, BEARING, ADEQUACY, GENERATION, ENTITLEMENT})}


def base_state(**overrides) -> State:
    defaults = dict(
        at=0,
        commitments={VERDICT: "open"},
        bearing={"settlement-report": frozenset(
            {VERDICT, BEARING, ADEQUACY, GENERATION, ENTITLEMENT})},
        adequacy={"w-real": frozenset({SUBSTANCE})},
        generation={"case": SUBSTANCE},
        entitlement=frozenset({SUBSTANCE}),
        liabilities={},
    )
    defaults.update(overrides)
    return State(**defaults)


def base_environment(**overrides) -> Environment:
    defaults = dict(
        conferred=CONFERRED_SCOPE,
        bears_on={"settlement-report": frozenset(
            {VERDICT, BEARING, ADEQUACY, GENERATION, ENTITLEMENT})},
        settles={"w-real": frozenset({SUBSTANCE})},
        demands=(ObjectiveDemand("d1", 0, SUBSTANCE),),
        service_window=1,
    )
    defaults.update(overrides)
    return Environment(**defaults)


def _cite(*coordinates: str, ground: str = "g-root") -> tuple[tuple[str, str], ...]:
    return tuple((ground, coordinate) for coordinate in coordinates)


# --------------------------------------------------------------------------
# A — long-chain authority laundering
# --------------------------------------------------------------------------

def long_chain(length: int = 4, amplify_at: int | None = 3):
    """A derivation chain that grows its scope at one link.

    Each link looks like ordinary inference. The question is whether a scope no
    ancestor carries can appear at the end of a long enough chain.
    """
    grounds = [ROOT]
    scope = frozenset({VERDICT})
    for index in range(length):
        if amplify_at is not None and index == amplify_at:
            scope = scope | {ADEQUACY}
        parent = "g-root" if index == 0 else f"g{index - 1}"
        grounds.append(Ground(f"g{index}", index + 1, f"derived-{index}", scope,
                              basis=(parent,), origin=DERIVED))
    edit = Edit("use-tip", moves={VERDICT: "closed"},
                cited=((f"g{length - 1}", VERDICT),))
    bearing = {f"derived-{i}": frozenset({VERDICT, ADEQUACY}) for i in range(length)}
    bearing.update(base_state().bearing)
    state = base_state(bearing=bearing)
    trajectory = Trajectory(state, (edit,), grounds=GroundStore(tuple(grounds)))
    environment = base_environment(
        bears_on={**base_environment().bears_on,
                  **{f"derived-{i}": frozenset({VERDICT}) for i in range(length)}},
        demands=())
    return trajectory, environment


# --------------------------------------------------------------------------
# B — circular authorization
# --------------------------------------------------------------------------

def circular():
    """Two grounds each deriving its authority from the other."""
    grounds = (
        ROOT,
        Ground("g-a", 1, "a", frozenset({ADEQUACY}), basis=("g-b",)),
        Ground("g-b", 1, "b", frozenset({ADEQUACY}), basis=("g-a",)),
    )
    edit = Edit("use-cycle", machinery_moves={ADEQUACY: {"w-cheap": frozenset({SUBSTANCE})}},
                cited=(("g-a", ADEQUACY),))
    state = base_state(bearing={**base_state().bearing, "a": frozenset({ADEQUACY})})
    environment = base_environment(
        bears_on={**base_environment().bears_on, "a": frozenset({ADEQUACY})},
        demands=())
    return Trajectory(state, (edit,), grounds=GroundStore(grounds)), environment


# --------------------------------------------------------------------------
# C — pre-emptive inquiry-rule revision
# --------------------------------------------------------------------------

def preemptive_generation():
    """The generation rule is revised, with real authority, before the case arrives.

    Nothing is retroactive: the inquiry is never generated, because by the time
    the encounter happens the rule no longer produces it.
    """
    revise = Edit("narrow-generation", machinery_moves={GENERATION: {}},
                  cited=_cite(GENERATION))
    idle = Edit("idle")
    trajectory = Trajectory(base_state(), (revise, idle),
                            encounters=(Encounter(1, "case"),),
                            grounds=GroundStore((ROOT,)))
    return trajectory, base_environment(
        demands=(ObjectiveDemand("d1", 1, SUBSTANCE),))


# --------------------------------------------------------------------------
# D — entitlement laundering
# --------------------------------------------------------------------------

def entitlement_laundering():
    """Generation is left alone; the rule saying which questions are owed service
    is revised after the inquiry has already been generated."""
    withdraw = Edit("withdraw-entitlement",
                    machinery_moves={ENTITLEMENT: frozenset()},
                    cited=_cite(ENTITLEMENT))
    idle = Edit("idle")
    trajectory = Trajectory(base_state(), (withdraw, idle),
                            encounters=(Encounter(0, "case"),),
                            grounds=GroundStore((ROOT,)))
    return trajectory, base_environment()


# --------------------------------------------------------------------------
# E — formulation manipulation
# --------------------------------------------------------------------------

def narrow_formulation():
    """A question is generated, docketed and answered — a different question.

    The generation rule is revised, with authority, so that the case produces a
    narrow substance. Something is confronted at every date; the demand is not.
    """
    narrow = Edit("narrow-formulation",
                  machinery_moves={GENERATION: {"case": "s-narrow"},
                                   ENTITLEMENT: frozenset({"s-narrow"})},
                  cited=_cite(GENERATION, ENTITLEMENT))
    docket = Edit("docket-narrow",
                  dockets=(Inquiry("q-case-1", "s-narrow", 1),))
    close = Edit("close-narrow",
                 dispositions={"q-case-1": (DISCHARGE, (), "w-narrow")})
    state = base_state(adequacy={"w-real": frozenset({SUBSTANCE}),
                                 "w-narrow": frozenset({"s-narrow"})})
    trajectory = Trajectory(state, (narrow, docket, close),
                            encounters=(Encounter(1, "case"),),
                            grounds=GroundStore((ROOT,)))
    return trajectory, base_environment(
        settles={"w-real": frozenset({SUBSTANCE}),
                 "w-narrow": frozenset({"s-narrow"})},
        demands=(ObjectiveDemand("d1", 1, SUBSTANCE),))


# --------------------------------------------------------------------------
# F — coverage flooding
# --------------------------------------------------------------------------

def flooding(volume: int = 6):
    """Many entitled inquiries arrive at once against a bounded service rate."""
    kinds = {f"case{i}": f"s{i}" for i in range(volume)}
    state = base_state(generation={**{"case": SUBSTANCE}, **kinds},
                       entitlement=frozenset({SUBSTANCE}) | set(kinds.values()))
    encounters = tuple(Encounter(0, f"case{i}") for i in range(volume))
    docket = Edit("docket-two",
                  dockets=(Inquiry("q-case0-0", "s0", 0),
                           Inquiry("q-case1-0", "s1", 0)))
    idle = Edit("idle")
    trajectory = Trajectory(state, (docket, idle), encounters=encounters,
                            grounds=GroundStore((ROOT,)), capacity=2)
    return trajectory, base_environment(demands=())


# --------------------------------------------------------------------------
# G — provenance-valid defeater laundering
# --------------------------------------------------------------------------

def derived_defeaters():
    """Defeaters produced by real derivation from a real root, within scope.

    Nothing is manufactured: the chain is well-founded, the scope never grows,
    and the reasoner's own bearing relation says the defeater bears on the
    verdict. The environment says it does not.
    """
    defeater = Ground("g-def", 1, "defeat-content", frozenset({VERDICT}),
                      basis=("g-root",), origin=DERIVED)
    edit = Edit("apply-defeater", moves={VERDICT: "dismissed"},
                cited=(("g-def", VERDICT),))
    state = base_state(bearing={**base_state().bearing,
                                "defeat-content": frozenset({VERDICT})})
    trajectory = Trajectory(state, (Edit("idle"), edit),
                            grounds=GroundStore((ROOT, defeater)))
    return trajectory, base_environment(
        bears_on={"settlement-report": frozenset(
            {VERDICT, BEARING, ADEQUACY, GENERATION, ENTITLEMENT}),
            "defeat-content": frozenset()},
        demands=())


# --------------------------------------------------------------------------
# H — branch-selective answerability
# --------------------------------------------------------------------------

def branch_selective():
    """Split one demand, discharge the convenient branch, suspend the rest."""
    state = base_state(liabilities={"L": Liability("L", frozenset({SUBSTANCE}), 0)})
    split = Edit("split", dispositions={"L": (REFINE, ("La", "Lb"), "w-split")})
    close = Edit("close-branch",
                 dispositions={"La": (DISCHARGE, (), "w-partial"),
                               "Lb": (SUSPEND, (), "route-later")})
    state = replace(state, adequacy={"w-real": frozenset({SUBSTANCE}),
                                     "w-partial": frozenset({SUBSTANCE})})
    trajectory = Trajectory(state, (split, close), grounds=GroundStore((ROOT,)))
    return trajectory, base_environment(
        settles={"w-real": frozenset({SUBSTANCE}),
                 "w-partial": frozenset({"s-part"})}, demands=())


# --------------------------------------------------------------------------
# I — authorized distinction collapse
# --------------------------------------------------------------------------

def distinction_collapse():
    """Two demands with different substances merged onto one, then closed once."""
    state = base_state(
        liabilities={"L1": Liability("L1", frozenset({SUBSTANCE}), 0),
                     "L2": Liability("L2", frozenset({"s-other"}), 0)},
        adequacy={"w-real": frozenset({SUBSTANCE})})
    merge = Edit("merge", dispositions={
        "L1": (IDENTIFY, ("Lm",), "licence-merge"),
        "L2": (IDENTIFY, ("Lm",), "licence-merge")})
    close = Edit("close-merged",
                 dispositions={"Lm": (DISCHARGE, (), "w-real")})
    trajectory = Trajectory(state, (merge, close), grounds=GroundStore((ROOT,)))
    return trajectory, base_environment(
        settles={"w-real": frozenset({SUBSTANCE})}, demands=())


# --------------------------------------------------------------------------
# J — profitable but licensed
# --------------------------------------------------------------------------

def cost_pair():
    """Two trajectories both licensed, one closing the liability sooner.

    The conditions are predicates of a trajectory, and "chosen because it closes
    the books" is a fact about a policy's counterfactuals, not about either
    trajectory. The pair exists to make that type mismatch explicit.
    """
    state = base_state(liabilities={"L": Liability("L", frozenset({SUBSTANCE}), 0)})
    quick = Trajectory(state, (Edit("close", dispositions={
        "L": (DISCHARGE, (), "w-real")}),), grounds=GroundStore((ROOT,)))
    slow = Trajectory(state, (Edit("carry"), Edit("close", dispositions={
        "L": (DISCHARGE, (), "w-real")})), grounds=GroundStore((ROOT,)))
    return (quick, slow), base_environment(demands=())


# --------------------------------------------------------------------------
# K — radical legitimate transformation
# --------------------------------------------------------------------------

def radical_transformation():
    """Concepts, standards, inquiry rules and a verdict all change, legitimately.

    The old demand is refined into the new vocabulary and discharged on a witness
    the environment agrees settles it. If the architecture refuses this, it is
    too strong.
    """
    state = base_state(liabilities={"L": Liability("L", frozenset({SUBSTANCE}), 0)})
    revise = Edit(
        "revise-everything",
        machinery_moves={
            BEARING: {"settlement-report": frozenset(
                {VERDICT, BEARING, ADEQUACY, GENERATION, ENTITLEMENT}),
                "welfare-theory": frozenset({VERDICT})},
            ADEQUACY: {"w-real": frozenset({SUBSTANCE}),
                       "w-welfare": frozenset({SUBSTANCE})},
            GENERATION: {"case": SUBSTANCE, "welfare-case": SUBSTANCE},
            ENTITLEMENT: frozenset({SUBSTANCE}),
        },
        cited=_cite(BEARING, ADEQUACY, GENERATION, ENTITLEMENT),
        dispositions={"L": (REFINE, ("L-welfare",), "w-split")})
    reverse = Edit("reverse-verdict", moves={VERDICT: "reversed"},
                   cited=(("g-welfare", VERDICT),),
                   dispositions={"L-welfare": (DISCHARGE, (), "w-welfare")})
    welfare = Ground("g-welfare", 1, "welfare-theory", frozenset({VERDICT}),
                     basis=("g-root",), origin=DERIVED)
    trajectory = Trajectory(state, (revise, reverse),
                            grounds=GroundStore((ROOT, welfare)))
    return trajectory, base_environment(
        bears_on={"settlement-report": frozenset(
            {VERDICT, BEARING, ADEQUACY, GENERATION, ENTITLEMENT}),
            "welfare-theory": frozenset({VERDICT})},
        settles={"w-real": frozenset({SUBSTANCE}),
                 "w-welfare": frozenset({SUBSTANCE})},
        demands=())


# --------------------------------------------------------------------------
# L — the all-four counterexample
# --------------------------------------------------------------------------

def adequacy_narrowing(prospective_variant: bool = False):
    """The headline attack: the reasoner rewrites what counts as settling a
    demand, using authority it genuinely holds, and then settles it cheaply.

    With `prospective_variant`, the liability is filed *after* the revision, so
    nothing reaches backwards and the prospectivity clause has nothing to catch.
    """
    state = base_state(
        liabilities={} if prospective_variant
        else {"L": Liability("L", frozenset({SUBSTANCE}), 0)})
    widen = Edit("widen-adequacy",
                 machinery_moves={ADEQUACY: {"w-real": frozenset({SUBSTANCE}),
                                             "w-cheap": frozenset({SUBSTANCE})}},
                 cited=_cite(ADEQUACY))
    file_after = Edit("file-after", dockets=(Inquiry("L", SUBSTANCE, 1),))
    close = Edit("close-cheaply",
                 dispositions={"L": (DISCHARGE, (), "w-cheap")})
    edits = ((widen, file_after, close) if prospective_variant
             else (widen, close))
    trajectory = Trajectory(state, edits, grounds=GroundStore((ROOT,)))
    return trajectory, base_environment(
        settles={"w-real": frozenset({SUBSTANCE})}, demands=())


# --------------------------------------------------------------------------
# The record-equivalence pair
# --------------------------------------------------------------------------

def record_equivalent_pair():
    """One trajectory, two environments differing only in whether the reasoner's
    adequacy relation is faithful.

    The record is identical because there is only one record. Any predicate of it
    takes one value; the target takes two.
    """
    trajectory, _ = adequacy_narrowing()
    faithful = base_environment(
        settles={"w-real": frozenset({SUBSTANCE}),
                 "w-cheap": frozenset({SUBSTANCE})}, demands=())
    unfaithful = base_environment(
        settles={"w-real": frozenset({SUBSTANCE})}, demands=())
    return trajectory, faithful, unfaithful


# --------------------------------------------------------------------------
# Independence witnesses
# --------------------------------------------------------------------------

def unlicensed_move():
    """P, I and DA hold; a coordinate moves with nothing cited for it."""
    edit = Edit("bare-move", moves={VERDICT: "closed"})
    return Trajectory(base_state(), (edit,),
                      grounds=GroundStore((ROOT,))), base_environment(demands=())


def unbacked_discharge():
    """P, I and RR hold; a liability is closed with nothing behind it."""
    state = base_state(liabilities={"L": Liability("L", frozenset({SUBSTANCE}), 0)})
    edit = Edit("bare-close", dispositions={"L": (DISCHARGE, (), None)})
    return Trajectory(state, (edit,),
                      grounds=GroundStore((ROOT,))), base_environment(demands=())
