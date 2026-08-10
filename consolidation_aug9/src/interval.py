"""The credal interval computed from a finite language, the settled record, and a book.

Folder-local. Definitions are restated here rather than imported, per the
clarity rule: this module is readable against `THEORY_9` alone.

A **language** is a finite set of worlds together with, for each sentence in a
finite fragment, the worlds at which it is true. A **settled fact** is an
incorrigible equality written by a settlement engine. An **endorsement** is one
compiled book commitment, a one-sided constraint on the credal state. The
**feasible set** is the set of probability assignments over the worlds
satisfying the simplex, every settled equality, and every endorsement; the
**credal interval** of a target is the exact rational minimum and maximum of the
target's probability over that set.

Two polytopes are named separately and never conflated. `coherence_polytope` is
logic plus the settled record and nothing else -- what an *engine's* prices are
obliged to be near. `docket_polytope` adds the book's endorsements -- what the
*docket* computes intervals against. Charging the right party turns on the
distinction; see `THEORY_11` and the guard witness in the ledger.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.exact import Constraint, Optimum, dual_weights, optimize, vertices

SIMPLEX = "simplex."
SETTLED = "settled:"
BOOK = "book:"
INCORRIGIBLE = (SIMPLEX, SETTLED)


@dataclass(frozen=True)
class Language:
    """A finite world set and the sentences true at each world."""

    worlds: tuple[str, ...]
    truth: Mapping[str, tuple[str, ...]]

    def licenses(self, sentence: str) -> bool:
        return sentence in self.truth

    def indicator(self, sentence: str) -> tuple[Q, ...]:
        true_at = set(self.truth.get(sentence, ()))
        return tuple(Q(1) if w in true_at else Q(0) for w in self.worlds)

    @property
    def size(self) -> int:
        return len(self.worlds)


@dataclass(frozen=True)
class Endorsement:
    """One compiled book commitment: `coefficients . p >= rhs`."""

    endorsement_id: str
    coefficients: tuple[Q, ...]
    rhs: Q = Q(0)


@dataclass(frozen=True)
class SettledFact:
    """A settlement event's downstream constraint: an incorrigible equality."""

    sentence: str
    value: Q


@dataclass(frozen=True)
class Book:
    book_version: int
    endorsements: tuple[Endorsement, ...] = ()


def simplex_rows(size: int) -> tuple[Constraint, ...]:
    rows = [Constraint(SIMPLEX + "total", tuple(Q(1) for _ in range(size)), Q(1), True)]
    for index in range(size):
        rows.append(Constraint(
            f"{SIMPLEX}nonneg:{index}",
            tuple(Q(1) if p == index else Q(0) for p in range(size)), Q(0)))
    return tuple(rows)


def settled_rows(language: Language,
                 settled: Sequence[SettledFact]) -> tuple[Constraint, ...]:
    return tuple(Constraint(SETTLED + f.sentence, language.indicator(f.sentence),
                            Q(f.value), True) for f in settled)


def endorsement_rows(language: Language, book: Book) -> tuple[Constraint, ...]:
    rows = []
    for e in book.endorsements:
        if len(e.coefficients) != language.size:
            raise ValueError(f"endorsement {e.endorsement_id} has the wrong width")
        rows.append(Constraint(BOOK + e.endorsement_id,
                               tuple(Q(c) for c in e.coefficients), Q(e.rhs)))
    return tuple(rows)


def coherence_polytope(language: Language,
                       settled: Sequence[SettledFact]) -> tuple[Constraint, ...]:
    """Logic plus the settled record. The book is deliberately absent."""
    return simplex_rows(language.size) + settled_rows(language, settled)


def docket_polytope(language: Language, book: Book,
                    settled: Sequence[SettledFact]) -> tuple[Constraint, ...]:
    """Book plus the settled record: what the docket computes intervals against."""
    return coherence_polytope(language, settled) + endorsement_rows(language, book)


@dataclass(frozen=True)
class Witness:
    assignment: tuple[Q, ...]
    value: Q
    active: tuple[str, ...]


@dataclass(frozen=True)
class Interval:
    book_version: int
    target: str
    lower: Q | None
    upper: Q | None
    lower_witness: Witness | None
    upper_witness: Witness | None
    lower_dual: tuple[tuple[str, Q], ...] | None
    upper_dual: tuple[tuple[str, Q], ...] | None
    infeasible: bool
    licensed: bool = True

    def well_formed(self) -> bool:
        return (self.licensed and not self.infeasible and self.lower is not None
                and self.upper is not None
                and Q(0) <= self.lower <= self.upper <= Q(1))


def interval_over(rows: Sequence[Constraint], language: Language, target: str,
                  book_version: int) -> Interval:
    """The credal interval of a target over an arbitrary constraint set."""
    if not language.licenses(target):
        return Interval(book_version, target, None, None, None, None, None, None,
                        False, licensed=False)
    size = language.size
    objective = language.indicator(target)
    found = vertices(rows, size)
    if not found:
        return Interval(book_version, target, None, None, None, None, None, None, True)
    scored = [(sum((a * b for a, b in zip(objective, p)), Q(0)), p, act)
              for p, act in found]
    low, low_p, low_act = min(scored, key=lambda t: t[0])
    high, high_p, high_act = max(scored, key=lambda t: t[0])
    active = lambda names: [r for r in rows if r.source in set(names)]
    return Interval(
        book_version, target, low, high,
        Witness(low_p, low, low_act), Witness(high_p, high, high_act),
        dual_weights(active(low_act), size, objective),
        dual_weights(active(high_act), size, tuple(-c for c in objective)),
        False)


def compute_interval(language: Language, book: Book,
                     settled: Sequence[SettledFact], target: str) -> Interval:
    """The credal interval against the docket polytope."""
    return interval_over(docket_polytope(language, book, settled), language, target,
                         book.book_version)


def threshold_direction(interval: Interval, threshold: Q) -> str | None:
    """Positive when the lower end clears; negative when the upper end falls short."""
    if not interval.well_formed():
        return None
    if Q(interval.lower) >= Q(threshold):
        return "positive"
    if Q(interval.upper) < Q(threshold):
        return "negative"
    return None
