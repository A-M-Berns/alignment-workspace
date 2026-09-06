"""Exact finite mirrors for the History Integrity countermodels."""

from dataclasses import dataclass
from fractions import Fraction
from typing import FrozenSet

Atom = str
Load = FrozenSet[Atom]


@dataclass(frozen=True)
class Step:
    before_live: Load
    after_live: Load
    answered: Load
    closed: Load

    def before_account(self) -> Load:
        return self.before_live

    def after_account(self) -> Load:
        return self.after_live | self.answered | self.closed

    def conserved(self) -> bool:
        return self.before_account() == self.after_account()


def hollow_disposal() -> Step:
    return Step(frozenset({"a"}), frozenset(), frozenset(), frozenset())


def faithful_disposal() -> Step:
    return Step(frozenset({"a"}), frozenset({"a"}), frozenset(), frozenset())


def closure_admissible(*, settled: bool, closes: bool, prior_licence: bool) -> bool:
    return settled and closes and prior_licence


@dataclass(frozen=True)
class Reconsideration:
    old_token_terminal: bool
    old_closure_event_present: bool
    review_obligation_fresh: bool
    carried_load: Fraction


def append_only_reconsideration() -> Reconsideration:
    return Reconsideration(True, True, True, Fraction(1, 1))
