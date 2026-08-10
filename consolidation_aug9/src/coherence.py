"""The finite-time incoherence functional and the tolerance-robust docket.

Folder-local; readable against `THEORY_11` alone.

**Definition (incoherence).** For a finite price assignment over the current
language fragment, the incoherence is the minimal uniform distance from the
displayed prices to the coherent assignments:

    incoherence(prices) = min over coherent p of max over priced s of
                          | <indicator(s), p> - price(s) |

where *coherent* means lying in the coherence polytope -- logic plus the settled
record, never the book.

**The normalization.** Two facts make the scale meaningful rather than an
artifact of presentation. Each priced row is a sentence indicator, whose
coefficients are `0/1` and whose expectation ranges over the whole unit
interval, so a value of one means some displayed sentence is priced at the
opposite end of its entire attainable range. And the accompanying certificate's
price-row multipliers carry total absolute mass at most one -- a normalization
that is **forced, not chosen**: it is the tolerance column of the dual system.
A certificate reporting excess `gamma` therefore reports it in the same units as
a declared schedule, so `gamma > epsilon` is a comparison and not a units error.

**What is never relaxed.** The robust forms relax the book's compiled
endorsements, because those are the content the docket reads. They never relax
the simplex, which is definitional, and never relax a settled equality, which is
incorrigible. Relaxing a settled equality would let a declared tolerance buy
back settled content.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.exact import Constraint, dual_weights, optimize
from src.interval import (
    INCORRIGIBLE,
    Book,
    Interval,
    Language,
    SettledFact,
    coherence_polytope,
    compute_interval,
    docket_polytope,
    interval_over,
    threshold_direction,
)


@dataclass(frozen=True)
class Prices:
    """A finite price assignment over the current language fragment."""

    state_version: int
    values: Mapping[str, Q]

    @property
    def sentences(self) -> tuple[str, ...]:
        return tuple(sorted(self.values))

    def well_formed(self) -> bool:
        return all(Q(0) <= Q(v) <= Q(1) for v in self.values.values())


@dataclass(frozen=True)
class Certificate:
    """Signed weights on priced sentences bounding the incoherence from below.

    Guarantee, checked by `verify` without trusting the extraction: for every
    coherent assignment `p`,

        sum_s w_s ( price(s) - <indicator(s), p> )  >=  excess,

    and since the total absolute mass is at most one, the largest single
    deviation is at least `excess` as well.
    """

    multipliers: tuple[tuple[str, Q], ...]
    excess: Q
    mass: Q

    @property
    def normalized(self) -> bool:
        return Q(self.mass) <= Q(1)


@dataclass(frozen=True)
class IncoherenceReport:
    state_version: int
    value: Q | None
    witness: tuple[Q, ...] | None
    certificate: Certificate | None
    infeasible: bool

    @property
    def coherent(self) -> bool:
        return self.value == Q(0)


def _lift(row: Constraint, extra: Q = Q(0)) -> Constraint:
    return Constraint(row.source, row.coefficients + (extra,), row.rhs, row.equality)


def incoherence(language: Language, settled: Sequence[SettledFact],
                prices: Prices) -> IncoherenceReport:
    """The functional, by one exact linear program in the lifted variable."""
    stray = [s for s in prices.sentences if not language.licenses(s)]
    if stray:
        raise ValueError(f"priced sentences outside the language fragment: {stray}")
    size = language.size
    rows = [_lift(r) for r in coherence_polytope(language, settled)]
    rows.append(Constraint("tolerance.nonneg",
                           tuple(Q(0) for _ in range(size)) + (Q(1),), Q(0)))
    for s in prices.sentences:
        ind = language.indicator(s)
        price = Q(prices.values[s])
        rows.append(Constraint(f"price+:{s}", ind + (Q(1),), price))
        rows.append(Constraint(f"price-:{s}", tuple(-c for c in ind) + (Q(1),), -price))
    objective = tuple(Q(0) for _ in range(size)) + (Q(1),)
    best = optimize(rows, size + 1, objective, "min")
    if best is None:
        return IncoherenceReport(prices.state_version, None, None, None, True)
    certificate = None
    if best.value > Q(0):
        certificate = _extract(rows, size, best.active, language, settled, prices)
    return IncoherenceReport(prices.state_version, best.value, best.point[:size],
                             certificate, False)


def _extract(rows: Sequence[Constraint], size: int, active: Sequence[str],
             language: Language, settled: Sequence[SettledFact],
             prices: Prices) -> Certificate | None:
    live = [r for r in rows if r.source in set(active)]
    objective = [Q(0)] * size + [Q(1)]
    weights = dual_weights(live, size + 1, objective)
    if weights is None:
        return None
    signed: dict[str, Q] = {}
    for source, weight in weights:
        if source.startswith("price+:"):
            signed[source[7:]] = signed.get(source[7:], Q(0)) + weight
        elif source.startswith("price-:"):
            signed[source[7:]] = signed.get(source[7:], Q(0)) - weight
    multipliers = tuple(sorted((s, w) for s, w in signed.items() if w != 0))
    if not multipliers:
        return None
    mass = sum((abs(w) for _, w in multipliers), Q(0))
    if mass == 0 or mass > Q(1):
        return None
    excess = certified_excess(language, settled, prices, multipliers)
    return None if excess is None else Certificate(multipliers, excess, mass)


def certified_excess(language: Language, settled: Sequence[SettledFact],
                     prices: Prices,
                     multipliers: Sequence[tuple[str, Q]]) -> Q | None:
    """Recompute the bound a multiplier vector certifies, by its own program.

    This never reads the extraction's arithmetic, so it is a check and not a
    restatement of what the extraction already said.
    """
    size = language.size
    combined = [Q(0)] * size
    constant = Q(0)
    for sentence, weight in multipliers:
        ind = language.indicator(sentence)
        constant += Q(weight) * Q(prices.values[sentence])
        for i in range(size):
            combined[i] -= Q(weight) * ind[i]
    best = optimize(coherence_polytope(language, settled), size, tuple(combined), "min")
    return None if best is None else constant + best.value


def verify(language: Language, settled: Sequence[SettledFact], prices: Prices,
           certificate: Certificate) -> bool:
    if not certificate.normalized:
        return False
    excess = certified_excess(language, settled, prices, certificate.multipliers)
    return excess is not None and excess >= Q(certificate.excess)


def prices_are_coherent(language: Language, settled: Sequence[SettledFact],
                        prices: Prices) -> bool:
    """Is some coherent assignment reproducing every displayed price exactly?"""
    rows = list(coherence_polytope(language, settled))
    for s in prices.sentences:
        rows.append(Constraint(f"exact:{s}", language.indicator(s),
                               Q(prices.values[s]), True))
    size = language.size
    return optimize(rows, size, tuple(Q(0) for _ in range(size)), "min") is not None


# --------------------------------------------------------------------------
# The tolerance-robust docket
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Schedule:
    """A declared tolerance per date."""

    schedule_id: str
    values: Mapping[int, Q]
    default: Q = Q(0)

    def at(self, date: int) -> Q:
        return Q(self.values.get(date, self.default))

    @property
    def exact(self) -> bool:
        return Q(self.default) == 0 and all(Q(v) == 0 for v in self.values.values())


EXACT = Schedule("tolerance:exact", {}, Q(0))


def relax(rows: Sequence[Constraint], tolerance: Q) -> tuple[Constraint, ...]:
    """Relax every relaxable row, each scaled to maximum coefficient magnitude one."""
    if Q(tolerance) < 0:
        raise ValueError("a tolerance is nonnegative")
    out = []
    for row in rows:
        if any(row.source.startswith(p) for p in INCORRIGIBLE):
            out.append(row)
            continue
        scale = max((abs(Q(c)) for c in row.coefficients), default=Q(0))
        out.append(row if scale == 0 else Constraint(
            row.source, row.coefficients, Q(row.rhs) - Q(tolerance) * scale,
            row.equality))
    return tuple(out)


def robust_interval(language: Language, book: Book, settled: Sequence[SettledFact],
                    target: str, tolerance: Q) -> Interval:
    """The interval against the relaxed docket polytope.

    At tolerance zero the relaxed row list is elementwise equal to the exact
    one, so this *is* the exact program, not merely equal to its answer.
    """
    rows = relax(docket_polytope(language, book, settled), Q(tolerance))
    return interval_over(rows, language, target, book.book_version)


def reduces_at_zero(language: Language, book: Book,
                    settled: Sequence[SettledFact], target: str) -> bool:
    exact_rows = docket_polytope(language, book, settled)
    if relax(exact_rows, Q(0)) != tuple(exact_rows):
        return False
    return (robust_interval(language, book, settled, target, Q(0))
            == compute_interval(language, book, settled, target))


@dataclass(frozen=True)
class MeritsCertificate:
    certificate_id: str
    target: str
    tolerance: Q
    threshold: Q
    direction: str
    interval: Interval


def robust_merits(language: Language, book: Book, settled: Sequence[SettledFact],
                  target: str, threshold: Q, tolerance: Q,
                  certificate_id: str) -> MeritsCertificate | None:
    interval = robust_interval(language, book, settled, target, tolerance)
    direction = threshold_direction(interval, Q(threshold))
    if direction is None:
        return None
    return MeritsCertificate(certificate_id, target, Q(tolerance), Q(threshold),
                             direction, interval)


def robust_sure_loss(language: Language, settled: Sequence[SettledFact],
                     prices: Prices, tolerance: Q) -> Mapping[str, object] | None:
    """Grounds when the engine's incoherence strictly exceeds the declared schedule.

    This is an objection against the *engine*. The book's own sure loss --
    endorsements jointly infeasible with the settled record -- is a different
    objection with a different respondent, and it is the infeasibility of the
    docket polytope, not this.
    """
    report = incoherence(language, settled, prices)
    if report.infeasible or report.value is None:
        return None
    if Q(report.value) <= Q(tolerance) or report.certificate is None:
        return None
    if not verify(language, settled, prices, report.certificate):
        return None
    return {"multipliers": report.certificate.multipliers,
            "excess": Q(report.certificate.excess),
            "mass": Q(report.certificate.mass),
            "declared_tolerance": Q(tolerance)}


def tolerance_is_working(language: Language, book: Book,
                         settled: Sequence[SettledFact], target: str,
                         threshold: Q, tolerance: Q) -> bool:
    """Non-vacuity: does the robust interval still strictly separate?"""
    return threshold_direction(
        robust_interval(language, book, settled, target, Q(tolerance)),
        Q(threshold)) is not None


def working_boundary(language: Language, book: Book, settled: Sequence[SettledFact],
                     target: str, threshold: Q,
                     denominator: int = 240) -> tuple[Q, Q]:
    """`(last working, first not working)` over the stated rational grid.

    Bisection is sound because the predicate is monotone: a larger tolerance
    relaxes every relaxable row by at least as much, so the interval only
    widens and separation once lost is never regained.
    """
    if denominator <= 0:
        raise ValueError("the grid denominator is positive")
    step = Q(1, denominator)
    if not tolerance_is_working(language, book, settled, target, threshold, Q(0)):
        return Q(0), Q(0)
    if tolerance_is_working(language, book, settled, target, threshold, Q(1)):
        return Q(1), Q(1) + step
    low, high = 0, denominator
    while high - low > 1:
        mid = (low + high) // 2
        if tolerance_is_working(language, book, settled, target, threshold, mid * step):
            low = mid
        else:
            high = mid
    return low * step, high * step


# --------------------------------------------------------------------------
# Certification layering
# --------------------------------------------------------------------------

ENGINE_BREACH = "engine"
BOOK_BREACH = "book"
NO_BREACH = "none"


@dataclass(frozen=True)
class Layering:
    """What the engine certified, and what the book voluntarily declared on top."""

    date: int
    engine_certified: Q
    book_declared: Q | None = None

    def well_formed(self) -> bool:
        return Q(self.engine_certified) >= 0 and (
            self.book_declared is None
            or Q(0) <= Q(self.book_declared) <= Q(self.engine_certified))


@dataclass(frozen=True)
class Attribution:
    date: int
    realized: Q
    party: str
    tolled: bool
    chargeable: bool


def attribute(layering: Layering, realized: Q) -> Attribution:
    """Who carries a tolerance breach, and what follows."""
    if not layering.well_formed():
        raise ValueError("a book tolerance must not exceed the engine's certified one")
    realized = Q(realized)
    if realized > Q(layering.engine_certified):
        return Attribution(layering.date, realized, ENGINE_BREACH, True, False)
    if layering.book_declared is not None and realized > Q(layering.book_declared):
        return Attribution(layering.date, realized, BOOK_BREACH, False, True)
    return Attribution(layering.date, realized, NO_BREACH, False, False)
