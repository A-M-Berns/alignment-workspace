"""The episodes the attacks run on.

Every one is exact: integer or rational credences, rational quantities, no
floats. Each is built to make one thing happen and is named after it. Several
attacks in the dispatch land on the same episode, which is recorded in
`PROSECUTION.md` rather than papered over by building near-duplicates.

The choice alphabet is two throughout. Two is enough for every separation the
round claims and it keeps the exhaustive enumerations in `repair.py` finite by
inspection rather than by budget.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Callable, Mapping, Sequence

from model import (Conduct, Episode, Preparation, constant_channel,
                   identity_channel, permuted_channel)

CHOICES = ("d0", "d1")
ACTIONS = ("u0", "u1")
ONE = Fraction(1)
HALF = Fraction(1, 2)


def build(name: str, credence: Mapping[str, Fraction],
          cell: Mapping[str, str], preparations: Sequence[Preparation],
          grade: Mapping[tuple[str, str], Fraction],
          quantity: Callable[[str, str, str, str], Fraction],
          choices: Sequence[str] = CHOICES,
          actions: Sequence[str] = ACTIONS,
          bound: Fraction = ONE) -> Episode:
    states = tuple(credence)
    table = {(s, p.name, d, u): Fraction(quantity(s, p.name, d, u))
             for s in states for p in preparations
             for d in choices for u in actions}
    return Episode(name=name, states=states, cell=dict(cell),
                   credence=dict(credence), choices=tuple(choices),
                   preparations=tuple(preparations), actions=tuple(actions),
                   grade=dict(grade), quantity=table, bound=bound)


KEEP = Preparation("keep", CHOICES)
SEIZE = Preparation("seize", ("d0",))
COMMIT_0 = Preparation("commit-d0", CHOICES)
COMMIT_1 = Preparation("commit-d1", CHOICES)
HEDGE = Preparation("hedge", CHOICES)


def _grade_tracking(states: Mapping[str, str]) -> dict[tuple[str, str], Fraction]:
    """The principal grades its own designated choice at one and the other at zero.

    A fixture stipulation about the principal, not a hypothesis relating the
    grade to the quantity. Where a fixture wants those to disagree it says so in
    its quantity.
    """
    return {(state, choice): (ONE if choice == want else Fraction(0))
            for state, want in states.items() for choice in CHOICES}


# --------------------------------------------------------------------------
# 1. Perfect prediction, identical realized quantity, different response maps
# --------------------------------------------------------------------------

def perfect_prediction() -> Episode:
    """One cell, one state. The selector is cell-measurable, so `A` predicts it
    exactly, and a conduct writing the prediction realizes what delegation
    realizes at every state."""
    return build(
        "perfect-prediction",
        credence={"s0": ONE},
        cell={"s0": "c0"},
        preparations=(KEEP,),
        grade=_grade_tracking({"s0": "d0"}),
        quantity=lambda s, q, d, u: ONE if d == "d0" else Fraction(-1))


def perfect_prediction_pair(episode: Episode) -> tuple[Conduct, Conduct]:
    delegate = Conduct("delegate", {"c0": "keep"}, identity_channel(episode),
                       {("c0", d): "u0" for d in episode.choices})
    preemptor = Conduct("preempt", {"c0": "keep"},
                        constant_channel(episode, {"c0": "d0"}),
                        {("c0", d): "u0" for d in episode.choices})
    return delegate, preemptor


def systematic_overrider(episode: Episode) -> Conduct:
    """A conduct whose channel is a nonidentity permutation of the choice.

    It answers every intervention on the principal's choice and defers to none
    of them. The frame register of
    `lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` identifies this
    with delegation — `simRead not` is homotopy equivalent to `delegated` — and
    the channel typing does not.
    """
    return Conduct("override-systematic", {"c0": "keep"},
                   permuted_channel(episode, {"d0": "d1", "d1": "d0"}),
                   {("c0", d): "u0" for d in episode.choices})


# --------------------------------------------------------------------------
# 2. Committed preparation: preemption genuinely gains, and the gain is eps_pred
# --------------------------------------------------------------------------

def committed_preparation() -> Episode:
    """The preparation pays only if it matches the realized choice.

    This is the dispatch's irreversible preparation, its early-commitment
    feasibility restriction, its noncommuting prepare-and-let-choose and its
    time-sensitive opportunity, all of which are the same structure: an action
    taken before the choice is known whose value depends on the choice.

    Neither preparation forecloses. Both are available to a mediated conduct.
    What preemption buys is that the commitment always matches, because the
    conduct wrote the choice.
    """
    def quantity(state: str, prep: str, choice: str, action: str) -> Fraction:
        if prep == "hedge":
            return HALF
        return ONE if prep == f"commit-{choice}" else Fraction(-1)

    return build(
        "committed-preparation",
        credence={"s0": Fraction(3, 4), "s1": Fraction(1, 4)},
        cell={"s0": "c0", "s1": "c0"},
        preparations=(COMMIT_0, COMMIT_1, HEDGE),
        grade=_grade_tracking({"s0": "d0", "s1": "d1"}),
        quantity=quantity)


# --------------------------------------------------------------------------
# 3. Override after full update: prediction exact, deficit maximal
# --------------------------------------------------------------------------

def override_after_full_update() -> Episode:
    """`A` predicts the principal exactly and writes something else.

    The grade and the quantity disagree completely, which the skeleton permits:
    "the relation between `v+` and `X` — none" (§8.5). Nothing in this round
    supplies it, so nothing in this round bounds what happens here.
    """
    return build(
        "override-after-full-update",
        credence={"s0": ONE},
        cell={"s0": "c0"},
        preparations=(KEEP,),
        grade=_grade_tracking({"s0": "d0"}),
        quantity=lambda s, q, d, u: Fraction(-1) if d == "d0" else ONE)


# --------------------------------------------------------------------------
# 4. Foreclosure: the repair is exact and the protection is gone
# --------------------------------------------------------------------------

def foreclosing_preparation() -> Episode:
    """A preparation that leaves the principal one option, and pays for it.

    The dispatch's collapsed selector range, and — with the premium read as what
    `A` needs rather than what it prefers — its survival case. `seize` is not a
    channel: a conduct taking it can be the identity on everything the principal
    can still reach, so `mediates` holds vacuously and the repair costs nothing.
    """
    def quantity(state: str, prep: str, choice: str, action: str) -> Fraction:
        if prep == "seize":
            return ONE
        want = "d0" if state == "s0" else "d1"
        return HALF if choice == want else Fraction(-1)

    return build(
        "foreclosing-preparation",
        credence={"s0": HALF, "s1": HALF},
        cell={"s0": "c0", "s1": "c0"},
        preparations=(KEEP, SEIZE),
        grade=_grade_tracking({"s0": "d0", "s1": "d1"}),
        quantity=quantity)


# --------------------------------------------------------------------------
# 5. Ceremonial: the choice is the principal's and reaches nothing
# --------------------------------------------------------------------------

def ceremonial_choice() -> Episode:
    """The quantity does not read the choice at all."""
    return build(
        "ceremonial-choice",
        credence={"s0": HALF, "s1": HALF},
        cell={"s0": "c0", "s1": "c0"},
        preparations=(KEEP,),
        grade=_grade_tracking({"s0": "d0", "s1": "d1"}),
        quantity=lambda s, q, d, u: HALF)


# --------------------------------------------------------------------------
# 6. Token responsiveness: one live cell, everything else written
# --------------------------------------------------------------------------

def two_cell() -> Episode:
    """Two information cells, so a conduct can defer in one and write in the other."""
    def quantity(state: str, prep: str, choice: str, action: str) -> Fraction:
        want = {"s0": "d0", "s1": "d1", "s2": "d0", "s3": "d1"}[state]
        return ONE if choice == want else Fraction(-1)

    return build(
        "two-cell",
        credence={"s0": Fraction(1, 4), "s1": Fraction(1, 4),
                  "s2": Fraction(1, 4), "s3": Fraction(1, 4)},
        cell={"s0": "c0", "s1": "c0", "s2": "c1", "s3": "c1"},
        preparations=(KEEP,),
        grade=_grade_tracking({"s0": "d0", "s1": "d1",
                               "s2": "d0", "s3": "d1"}),
        quantity=quantity)


def token_responsive(episode: Episode) -> Conduct:
    """Defers in `c0`, writes a constant in `c1`.

    `prompts/2026-08-11-deference-channel/REPORT.md` §1.3 records this shape as
    what defeats Proposition 7(a)'s nonconstancy criterion. Here it is what
    separates the cellwise efficacy clause from the global one.
    """
    channel = dict(identity_channel(episode))
    for choice in episode.choices:
        channel[("c1", choice)] = "d0"
    return Conduct("token-responsive", {c: "keep" for c in episode.cells},
                   channel, {(c, d): "u0" for c in episode.cells
                             for d in episode.choices})


def fully_deferring(episode: Episode, prep: str | None = None) -> Conduct:
    """Defer everywhere, on the episode's first preparation unless told otherwise."""
    chosen = prep or episode.preparations[0].name
    return Conduct("defer", {c: chosen for c in episode.cells},
                   identity_channel(episode),
                   {(c, d): "u0" for c in episode.cells for d in episode.choices})


# --------------------------------------------------------------------------
# 7. The unread payload
# --------------------------------------------------------------------------

def persuasion_moves_the_selector():
    """A licensed reason that changes which choice the principal makes.

    The counterfactual-legitimacy round's persuasion control does not reach the
    selector — its reason lands on a witness neither choice is identified with —
    so a control that does reach it is built here rather than claimed of theirs.
    The reason is licensed by the same ground, at the same coordinate, under the
    principal's own bearing relation; only what it proposes differs.

    Legitimate persuasion must remain possible, and the round's answer is that it
    does: this pair changes the selector and fires no clause.
    """
    import scenarios
    from fixture import ADEQUACY, Policy, SUBSTANCE

    fixture, _ = scenarios.licensed_persuasion()
    replacement = {"w-cheap": frozenset({SUBSTANCE}),
                   "w-other": frozenset({"s-other"}),
                   "w-narrow": frozenset({"s-narrow"})}
    item = scenarios.reason("audit-finding", "g-audit", ADEQUACY, None,
                            replacement)
    return fixture, (Policy("silent"),
                     Policy("reasoned-adequacy",
                            {scenarios.REASON_STEP: (item,)}))


def with_unread_payload(conduct: Conduct, payload: str) -> Conduct:
    """The same conduct with a different name and nothing else.

    There is no authorization field to set, so the dispatch's spoofed-provenance
    attack has nothing to write. The test that goes with this shows the model
    has no such field by exhibiting that every verdict is a function of
    `(prep, channel, implement)`.
    """
    return Conduct(f"{conduct.name}::{payload}", dict(conduct.prep),
                   dict(conduct.channel), dict(conduct.implement))
