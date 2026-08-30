"""Exact finite fixtures for transition-level Proper Exercise and locality.

The module deliberately has no probability and no floating-point arithmetic.
It tests the proposed interface, not a complete normative semantics.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Hashable, Optional, Union


Burden = Hashable


@dataclass(frozen=True)
class Disposal:
    kind: str
    sound: bool


@dataclass(frozen=True)
class Carry:
    successors: tuple[Burden, ...]
    sound_pairs: frozenset[tuple[Burden, Burden]]


Outcome = Union[Disposal, Carry]


@dataclass(frozen=True)
class TransportStep:
    """One typed PE step plus the structural facts supplied by Continuity."""

    pre_live: frozenset[Burden]
    post_live: frozenset[Burden]
    affected: frozenset[Burden]
    actually_changed: frozenset[Burden]
    outcomes: dict[Burden, Outcome]
    authorized: bool = True

    def pe_sound(self) -> bool:
        # Affected-completeness prevents certificates from hiding changed burdens.
        if not self.actually_changed <= self.affected:
            return False
        if not self.affected <= self.pre_live:
            return False
        if set(self.outcomes) != set(self.affected):
            return False
        for source, outcome in self.outcomes.items():
            if isinstance(outcome, Disposal):
                if not outcome.sound:
                    return False
            else:
                targets = set(outcome.successors)
                if not targets or not targets <= self.post_live:
                    return False
                if any((source, target) not in outcome.sound_pairs for target in targets):
                    return False
        # Unaffected carriers cannot disappear. This is the Continuity-side check.
        return (self.pre_live - self.affected) <= self.post_live

    def legitimate(self) -> bool:
        return self.authorized and self.pe_sound()


def evolve_frontier(
    frontier: frozenset[Burden], step: TransportStep
) -> tuple[frozenset[Burden], frozenset[tuple[Burden, str]]]:
    """Relationally transport a semantic frontier through one sound step."""

    if not step.pe_sound() or not frontier <= step.pre_live:
        raise ValueError("unsound PE step or non-live frontier")
    live: set[Burden] = set()
    receipts: set[tuple[Burden, str]] = set()
    for burden in frontier:
        if burden not in step.affected:
            live.add(burden)
            continue
        outcome = step.outcomes[burden]
        if isinstance(outcome, Disposal):
            receipts.add((burden, outcome.kind))
        else:
            live.update(outcome.successors)
    return frozenset(live), frozenset(receipts)


def answerability_conserved(initial: Burden, steps: tuple[TransportStep, ...]) -> bool:
    """Finite form: a live frontier remains unless every branch is disposed."""

    frontier = frozenset((initial,))
    receipts: set[tuple[Burden, str]] = set()
    for step in steps:
        try:
            frontier, new_receipts = evolve_frontier(frontier, step)
        except ValueError:
            return False
        receipts.update(new_receipts)
        if not frontier:
            return bool(receipts)
    return bool(frontier) or bool(receipts)


@dataclass(frozen=True)
class CoverageClose:
    authorized: bool
    active_post: bool
    represented_post: bool
    adequate_route_post: bool
    disposed_post: bool
    terminal: bool
    successor_carrier: bool

    def prefix_only_accepts(self, adequate_route_pre: bool) -> bool:
        return self.authorized and adequate_route_pre

    def pe_resolve(self) -> bool:
        if not self.authorized:
            return False
        unresolved = self.active_post and not self.represented_post and not self.disposed_post
        if not unresolved:
            return True
        # A route implements the contract, but does not discharge an ongoing burden.
        if self.terminal:
            return self.successor_carrier and self.adequate_route_post
        return self.successor_carrier


@dataclass(frozen=True)
class MetEdge:
    met_pre: bool
    met_post: bool
    witness: Optional[str]

    def pe_met(self) -> bool:
        if self.met_pre or not self.met_post:
            return True
        return self.witness in {
            "receipt-and-registration",
            "direct-satisfaction",
            "authorized-obsolescence",
            "target-disposition",
        }


RESPONSE_RULES = {
    "identity": {0: "a0", 1: "a1"},
    "always-a0": {0: "a0", 1: "a0"},
}


def response_structure_same(r0: str, r1: str) -> bool:
    return all(RESPONSE_RULES[r0][y] == RESPONSE_RULES[r1][y] for y in (0, 1))


def realized_action(rule: str, receipt: int) -> str:
    return RESPONSE_RULES[rule][receipt]


def liability_rows() -> tuple[bool, bool, bool, Fraction]:
    profiles = ((0, 1), (1, 0))
    row1 = lambda v: Fraction(v[0]) >= Fraction(3, 4)
    row2 = lambda v: Fraction(v[1]) >= Fraction(3, 4)
    one = any(row1(v) for v in profiles)
    two = any(row2(v) for v in profiles)
    joint = any(row1(v) and row2(v) for v in profiles)
    # Dual average asks for 3/4 while every profile supplies only 1/2.
    deficit = Fraction(3, 4) - max(Fraction(v[0] + v[1], 2) for v in profiles)
    return one, two, joint, deficit


def exhaustive_one_step_transport() -> bool:
    """Exhaust the Boolean one-burden cases admitted by pe_sound."""

    for affected, changed, dispose, post_live in product((False, True), repeat=4):
        pre = frozenset(("b",))
        affected_set = frozenset(("b",)) if affected else frozenset()
        changed_set = frozenset(("b",)) if changed else frozenset()
        post = frozenset(("b2",)) if post_live else frozenset()
        if not affected:
            post = post | pre if post_live else post
            outcomes: dict[Burden, Outcome] = {}
        elif dispose:
            outcomes = {"b": Disposal("valid", True)}
        else:
            outcomes = {"b": Carry(("b2",), frozenset({("b", "b2")}))}
        step = TransportStep(pre, post, affected_set, changed_set, outcomes)
        if step.pe_sound():
            frontier, receipts = evolve_frontier(pre, step)
            if not frontier and not receipts:
                return False
    return True
