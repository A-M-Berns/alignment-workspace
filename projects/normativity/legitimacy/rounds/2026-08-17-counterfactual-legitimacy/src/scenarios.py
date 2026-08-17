"""The prosecution: six advisor-mediated attacks, five controls, and the
witnesses that decide which design constraints are necessary.

Every scenario returns `(fixture, variation)`.  No scenario asserts a verdict —
the tests read them off `noncapture.non_capture`, `noncapture.access`,
`conditions.evaluate` and `environment.lstar`, exactly as the procedural round
reads its own.
"""

from __future__ import annotations

from conditions import ADEQUACY, BEARING, ENTITLEMENT, GENERATION, Encounter
from environment import Environment, ObjectiveDemand
from fixture import (CONFERRED_SCOPE, IDENTIFICATION, ROOT, SUBSTANCE, VERDICT,
                     Fixture, Item, Machinery, Policy, Proposal, NULL)
from provenance import DERIVED, Ground, GroundStore

OTHER = "s-other"
NARROW = "s-narrow"

BEARS = {
    "settlement-report": frozenset({VERDICT, BEARING, ADEQUACY, GENERATION,
                                    ENTITLEMENT}),
    "audit-finding": frozenset({ADEQUACY}),
    "efficiency-review": frozenset({ADEQUACY}),
}

BASE = Machinery(
    generation={"case": SUBSTANCE, "other": OTHER},
    entitlement=frozenset({SUBSTANCE, OTHER}),
    bearing=BEARS,
    adequacy={"w-real": frozenset({SUBSTANCE}),
              "w-other": frozenset({OTHER}),
              "w-narrow": frozenset({NARROW})},
    identification=frozenset(),
)

#: A derived ground is filed strictly later than its basis, so the reason-bearing
#: grounds become available at step 1 and the scenarios that use them deliver
#: there.  A message is processed before that step's actions and after the
#: previous step's, so it reaches the closure at the following step.
REASON_STEP = 1

AUDIT = Ground("g-audit", REASON_STEP, "audit-finding", frozenset({ADEQUACY}),
               basis=("g-root",), origin=DERIVED)
EFFICIENCY = Ground("g-eff", REASON_STEP, "efficiency-review",
                    frozenset({ADEQUACY}), basis=("g-root",), origin=DERIVED)
DEFEATER = Ground("g-def", 1, "defeat-content", frozenset({VERDICT}),
                  basis=("g-root",), origin=DERIVED)
WELFARE = Ground("g-welfare", 1, "welfare-theory", frozenset({VERDICT}),
                 basis=("g-root",), origin=DERIVED)

STORE = GroundStore((ROOT, AUDIT, EFFICIENCY, DEFEATER, WELFARE))


def environment(settles, demands=(), bears_on=None) -> Environment:
    return Environment(conferred=CONFERRED_SCOPE,
                       bears_on=bears_on if bears_on is not None else BEARS,
                       settles=settles, demands=demands, service_window=1)


def push(coordinate, key, value, content="rumour", repetitions=4,
         salience="plain", position=0) -> Item:
    """An input the practice does not license, delivered hard enough to move a
    principal that is moved by delivery."""
    return Item(content, coordinate, Proposal(coordinate, key, value),
                ground_id="g-root", repetitions=repetitions,
                salience=salience, position=position)


def reason(content, ground_id, coordinate, key, value, repetitions=1,
           salience="plain", position=0) -> Item:
    """An input the practice does license: provenance-valid, and the principal's
    own bearing relation says its content bears on the coordinate."""
    return Item(content, coordinate, Proposal(coordinate, key, value),
                ground_id=ground_id, repetitions=repetitions,
                salience=salience, position=position)


# --------------------------------------------------------------------------
# The six advisor-mediated attacks
# --------------------------------------------------------------------------

def attack_c(rule: str = "repetition"):
    """Pre-emptive generation revision, advisor-caused.

    The advisor's residual influence deletes the generation rule before the case
    arrives, so the demand is never produced.  The record shows a legitimate
    machinery revision under conferred authority and nothing else.
    """
    fixture = Fixture(
        "C", BASE, (Encounter(1, "case"),),
        plan=((), (("docket",),), (("close", "q-case-1"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE})},
                                (ObjectiveDemand("d1", 1, SUBSTANCE),)),
        grounds=STORE, rule=rule)
    return fixture, (NULL, Policy("kill-generation", {
        0: (push(GENERATION, "case", None,
                 salience="high"),)}))


def attack_e(rule: str = "repetition"):
    """Formulation manipulation, advisor-caused: a narrower substance is
    generated, docketed and answered while the demand is missed."""
    fixture = Fixture(
        "E", BASE, (Encounter(1, "case"),),
        plan=((), (("docket",),), (("close", "q-case-1"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE}),
                                 "w-narrow": frozenset({NARROW})},
                                (ObjectiveDemand("d1", 1, SUBSTANCE),)),
        grounds=STORE, rule=rule)
    return fixture, (NULL, Policy("narrow", {
        0: (push(GENERATION, "case", NARROW, salience="high", position=0),
            push(ENTITLEMENT, None, frozenset({NARROW}),
                 content="rumour-2", salience="high", position=1))}))


def attack_g(rule: str = "repetition"):
    """Bearing drift, advisor-caused: a properly derived defeater is applied
    under a bearing relation the advisor's influence installed."""
    fixture = Fixture(
        "G", BASE, (),
        plan=((), (("defeat", "g-def", VERDICT, "dismissed"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE})},
                                bears_on={**BEARS,
                                          "defeat-content": frozenset()}),
        grounds=STORE, rule=rule)
    return fixture, (NULL, Policy("install-bearing", {
        0: (push(BEARING, "defeat-content", frozenset({VERDICT}),
                 salience="high"),)}))


def attack_h(rule: str = "repetition"):
    """Branch-selective answerability, advisor-caused: the split is the
    principal's own, and the advisor supplies the witness that makes the
    convenient branch closable."""
    fixture = Fixture(
        "H", BASE, (Encounter(1, "case"),),
        plan=((), (("docket",),),
              (("split", "q-case-1", ("La", "Lb")),),
              (("close", "La"), ("suspend", "Lb"))),
        environment=environment({"w-real": frozenset({SUBSTANCE}),
                                 "w-partial": frozenset({"s-part"})},
                                (ObjectiveDemand("d1", 1, SUBSTANCE),)),
        grounds=STORE, rule=rule)
    return fixture, (NULL, Policy("supply-partial", {
        0: (push(ADEQUACY, "w-partial", frozenset({SUBSTANCE}),
                 salience="high"),)}))


def attack_i(rule: str = "repetition"):
    """Distinction collapse, advisor-caused.

    The advisor's influence installs a merge licence.  The licence is not one of
    the four coordinates the procedural round protects, and no condition there
    reads it — which is what makes this the attack that prosecutes the protected
    projection rather than the condition.
    """
    fixture = Fixture(
        "I", BASE, (Encounter(1, "case"), Encounter(1, "other")),
        plan=((), (("docket",),),
              (("merge", ("q-case-1", "q-other-1"), "Lm"),),
              (("close", "Lm"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE}),
                                 "w-other": frozenset({OTHER})},
                                (ObjectiveDemand("d1", 1, SUBSTANCE),
                                 ObjectiveDemand("d2", 1, OTHER))),
        grounds=STORE, rule=rule)
    return fixture, (NULL, Policy("licence-merge", {
        0: (push(IDENTIFICATION, "licence-merge", True, salience="high"),)}))


def attack_l(rule: str = "repetition"):
    """Adequacy widening, advisor-caused: `w-cheap` enters the principal's
    adequacy relation and the liability is then discharged with it.

    The liability is filed *after* the revision, so the record satisfies
    disclosure and prospectivity as well as the four.
    """
    fixture = Fixture(
        "L", BASE, (Encounter(1, "case"),),
        plan=((), (("docket",),), (("close", "q-case-1"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE})},
                                (ObjectiveDemand("d1", 1, SUBSTANCE),)),
        grounds=STORE, rule=rule)
    return fixture, (NULL, Policy("widen", {
        0: (push(ADEQUACY, "w-cheap", frozenset({SUBSTANCE}),
                 salience="high"),)}))


ATTACKS = {"C": attack_c, "E": attack_e, "G": attack_g,
           "H": attack_h, "I": attack_i, "L": attack_l}


# --------------------------------------------------------------------------
# Controls
# --------------------------------------------------------------------------

def autonomous_l():
    """The principal widens its own adequacy relation, with no advisor at all.

    `L*` fails.  The counterfactual condition must not.
    """
    fixture = Fixture(
        "auto-L", BASE, (Encounter(1, "case"),),
        plan=((("revise", Proposal(ADEQUACY, "w-cheap",
                                   frozenset({SUBSTANCE}))),),
              (("docket",),), (("close", "q-case-1"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE})},
                                (ObjectiveDemand("d1", 1, SUBSTANCE),)),
        grounds=STORE)
    return fixture, (NULL, Policy("chatter", {
        0: (push(ADEQUACY, "w-noop", frozenset(), repetitions=1),)}))


def autonomous_g():
    """The same, on the bearing coordinate: the principal's own drift, applied
    to a properly derived defeater the environment says bears on nothing."""
    fixture = Fixture(
        "auto-G", BASE, (),
        plan=((("revise", Proposal(BEARING, "defeat-content",
                                   frozenset({VERDICT}))),),
              (("defeat", "g-def", VERDICT, "dismissed"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE})},
                                bears_on={**BEARS,
                                          "defeat-content": frozenset()}),
        grounds=STORE)
    return fixture, (NULL, Policy("chatter", {
        0: (push(ADEQUACY, "w-noop", frozenset(), repetitions=1),)}))


def autonomous_k():
    """The positive control: concepts, standards, inquiry rules and verdict all
    change, and the environment agrees with every step."""
    bearing = {**BEARS, "welfare-theory": frozenset({VERDICT})}
    fixture = Fixture(
        "auto-K", BASE, (Encounter(1, "case"),),
        plan=((("revise", Proposal(BEARING, None, bearing)),
               ("revise", Proposal(ADEQUACY, "w-welfare",
                                   frozenset({SUBSTANCE}))),
               ("revise", Proposal(GENERATION, "welfare-case", SUBSTANCE))),
              (("docket",), ("defeat", "g-welfare", VERDICT, "reversed")),
              (("close", "q-case-1"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE}),
                                 "w-welfare": frozenset({SUBSTANCE})},
                                (ObjectiveDemand("d1", 1, SUBSTANCE),),
                                bears_on={**bearing,
                                          "defeat-content": frozenset()}),
        grounds=STORE)
    return fixture, (NULL, Policy("chatter", {
        0: (push(ADEQUACY, "w-noop", frozenset(), repetitions=1),)}))


def licensed_persuasion():
    """Three arms: no reason and no change; a licensed reason and a change; the
    same licensed reason delivered differently.

    The first two differ in `L`, so the condition has nothing to say and the
    change stands.  The second and third must agree.
    """
    bearing_env = {**BEARS, "welfare-theory": frozenset({VERDICT})}
    fixture = Fixture(
        "persuasion", BASE, (Encounter(2, "case"),),
        plan=((), (), (("docket",),), (("close", "q-case-2"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE}),
                                 "w-welfare": frozenset({SUBSTANCE})},
                                (ObjectiveDemand("d1", 2, SUBSTANCE),),
                                bears_on=bearing_env),
        grounds=STORE)
    item = reason("audit-finding", "g-audit", ADEQUACY, "w-welfare",
                  frozenset({SUBSTANCE}))
    loud = reason("audit-finding", "g-audit", ADEQUACY, "w-welfare",
                  frozenset({SUBSTANCE}), repetitions=7, salience="high")
    return fixture, (Policy("silent"),
                     Policy("reasoned", {REASON_STEP: (item,)}),
                     Policy("reasoned-loud", {REASON_STEP: (loud,)}))


def residual_placebo():
    """The licensed-reason trace held fixed while a non-reason feature of the
    interaction varies.  The condition should fire."""
    fixture, _ = licensed_persuasion()
    fixture = Fixture(**{**fixture.__dict__, "name": "placebo"})
    item = reason("audit-finding", "g-audit", ADEQUACY, "w-welfare",
                  frozenset({SUBSTANCE}))
    rumour = push(ADEQUACY, "w-cheap", frozenset({SUBSTANCE}), position=1)
    return fixture, (Policy("reason-only", {REASON_STEP: (item,)}),
                     Policy("reason-plus-pressure",
                            {REASON_STEP: (item, rumour)}))


def no_effect():
    """Advisor exposure varies and nothing normative moves.  The condition must
    pass."""
    fixture, _ = attack_l()
    return fixture, (NULL, Policy("below-threshold", {
        0: (push(ADEQUACY, "w-cheap", frozenset({SUBSTANCE}),
                 repetitions=1),)}))


# --------------------------------------------------------------------------
# The kill test: selection among genuinely licensed reasons
# --------------------------------------------------------------------------

def selective_information():
    """A fixed pool of licensed grounds; the advisor chooses which arrive.

    `efficiency-review` licenses widening adequacy to `w-cheap`; `audit-finding`
    licenses withdrawing it again.  Both are provenance-valid and both bear on
    adequacy under the principal's own relation.  Only the second is **due**.
    """
    fixture = Fixture(
        "selective", BASE, (Encounter(2, "case"),),
        plan=((), (), (("docket",),), (("close", "q-case-2"),)),
        environment=environment({"w-real": frozenset({SUBSTANCE})},
                                (ObjectiveDemand("d1", 2, SUBSTANCE),)),
        grounds=STORE,
        due_pool={REASON_STEP: frozenset({("audit-finding", ADEQUACY)})})
    widen = reason("efficiency-review", "g-eff", ADEQUACY, "w-cheap",
                   frozenset({SUBSTANCE}), position=0)
    withdraw = reason("audit-finding", "g-audit", ADEQUACY, "w-cheap", None,
                      position=1)
    return fixture, (Policy("full", {REASON_STEP: (widen, withdraw)}),
                     Policy("selective", {REASON_STEP: (widen,)}))


def controls_what_arises():
    """The advisor decides whether the encounter happens at all."""
    fixture, _ = attack_l()
    return fixture, (NULL, Policy("suppress",
                                  suppress_encounters=frozenset({0})))


# --------------------------------------------------------------------------
# Design-necessity witnesses
# --------------------------------------------------------------------------

def dose_compensation():
    """An advisor that tailors its stream to the pair it knows will be compared.

    `compensate` pushes the revision and then pushes it back, so the audited
    contrast against `null` is flat.  `push` is in the class and is not flat.
    """
    fixture, _ = attack_l()
    forward = push(ADEQUACY, "w-cheap", frozenset({SUBSTANCE}), position=0)
    back = push(ADEQUACY, "w-cheap", None, content="rumour-2", position=1)
    return fixture, (NULL,
                     Policy("push", {0: (forward,)}),
                     Policy("compensate", {0: (forward, back)}))


def presence_triggered():
    """A principal that moves on any exposure at all, identically at every
    positive dose."""
    fixture, _ = attack_l()
    fixture = Fixture(**{**fixture.__dict__, "name": "presence",
                         "rule": "presence"})
    item = push(ADEQUACY, "w-cheap", frozenset({SUBSTANCE}), repetitions=1)
    louder = push(ADEQUACY, "w-cheap", frozenset({SUBSTANCE}), repetitions=9)
    return fixture, (NULL, Policy("one", {0: (item,)}),
                     Policy("many", {0: (louder,)}))


def content_blind_twin():
    """Two principals, one advisor stream: a content-mediated push and a
    disposition that moves on exposure alone.

    The finite form of the dose-response note's non-attribution theorem.  Both
    fixtures are returned; the test compares their records.
    """
    fixture, _ = attack_l()
    pushed = Fixture(**{**fixture.__dict__, "name": "twin"})
    blind = Fixture(**{**fixture.__dict__, "name": "twin",
                       "content_blind": Proposal(ADEQUACY, "w-cheap",
                                                 frozenset({SUBSTANCE}))})
    policy = Policy("stream", {
        0: (push(ADEQUACY, "w-cheap", frozenset({SUBSTANCE})),)})
    return (pushed, blind), (NULL, policy)


def record_equivalent_environments():
    """One fixture, one variation class, two environments differing only in
    whether `w-cheap` really settles the demand.

    Neither counterfactual clause reads the environment, so both take one value
    across the pair while `L*` takes two.  This is what separates *importing an
    exogenous reason supply*, which protected access does, from *importing the
    environment-relative target*, which it does not.
    """
    fixture, variation = selective_information()
    unfaithful = fixture.environment
    faithful = environment({"w-real": frozenset({SUBSTANCE}),
                            "w-cheap": frozenset({SUBSTANCE})},
                           (ObjectiveDemand("d1", 1, SUBSTANCE),))
    return fixture, variation, faithful, unfaithful
