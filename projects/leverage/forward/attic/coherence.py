"""The finite-time incoherence functional and the tolerance-robust docket.

`T1` of the settlement interface declares a tolerance schedule and says the
docket runs "the robust interval, merits certificate, and sure-loss objection
against the declared schedule".  Before this module that governed an undefined
quantity: nothing said what it means for a price assignment to be *within* a
tolerance.  This module defines it, computes it exactly, and reduces the robust
forms to the exact ones at tolerance zero.

**Naming.**  The quantity is the minimal uniform distance from a displayed price
assignment to the coherent assignments.  The natural word for it is on this
tree's retired-vocabulary list, so it is called the **incoherence** throughout:
prices are `epsilon`-coherent exactly when their incoherence is at most
`epsilon`.  See `DEVIATIONS.md` D-SI-1.

**The normalization, stated.**  The functional is the uniform (max-over-priced-
sentences) distance:

    incoherence(prices) = min over feasible p of max over priced s of
                          | <indicator(s), p> - price(s) |

Two facts make the scale meaningful rather than an artifact.  Each priced row is
a sentence indicator, whose coefficients are `0/1` and whose expectation ranges
over `[0,1]`; so a value of `1` means some displayed sentence is priced at the
opposite end of its whole attainable range, which is a genuine extreme and not a
rescaling.  And the accompanying certificate's multipliers carry total absolute
mass at most one -- a normalization that is *forced*, not chosen: it is the
tolerance column of the dual system.  A certificate reporting excess `gamma`
therefore reports it in the same units as the declared schedule, so
`gamma > epsilon` is a comparison and not a units error.

**Two polytopes, never conflated.**  This module names both and keeps them
apart, because charging the wrong party turns on the distinction.

- `coherence_polytope` -- logic plus pins, and **nothing else**.  This is the
  set the *engine's* prices are obliged to be near, so it is the set the
  incoherence functional measures against.  The book's endorsements are not in
  it.
- `docket_polytope` -- book plus pins: what the docket computes its interval and
  its merits certificate against, and what the robust forms inflate by the
  declared tolerance.

An engine is answerable for its prices, not for what the book endorsed on top of
them.  If the two sets were conflated, a book whose endorsements are jointly
infeasible with the pins would register as engine incoherence, and the layering
clause would then toll an engine breach where it should charge a book breach --
the opposite party, and the opposite consequence.  The guard is a test: prices
that are exactly coherent score zero even when the book around them is
infeasible.

**What is not relaxed.**  The robust forms relax the *book's* compiled
endorsements, because those are the content the docket reads.  They never relax
the simplex (definitional) and never relax a pin (incorrigible, per interface
section 1: a pin fixes the variable's whole propositional family).  Relaxing a
pin would let a tolerance buy back settled content, which is exactly the
recycling species the corpus refuted.

Finiteness discipline.  The world set, the priced sentence set, and the
constraint list are finite; every quantity here is an exact rational computed by
vertex enumeration over finitely many subsets.  No live state grows with date.

All arithmetic is exact rationals.  No floating point.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.grammar import Grounds
from src.leverage_interval import (
    Book,
    Constraint,
    Language,
    LeverageInterval,
    SettledFact,
    _vertices,
    build_constraints,
    compute_interval,
    threshold_direction,
)

# Sources that a tolerance never relaxes.
INCORRIGIBLE_PREFIXES = ("simplex.", "settled:")


# --------------------------------------------------------------------------
# The two polytopes
# --------------------------------------------------------------------------


def coherence_polytope(language: Language,
                       settled: Sequence[SettledFact]) -> tuple[Constraint, ...]:
    """Logic plus pins: what the *engine's* prices are obliged to be near.

    The book is deliberately absent.  Coherence is a property of a price state
    against the language and the settled record; what the book went on to
    endorse is the book's affair, and holding the engine to it would charge a
    book breach to the engine.
    """
    return build_constraints(language, Book(0, ()), settled)


def docket_polytope(language: Language, book: Book,
                    settled: Sequence[SettledFact]) -> tuple[Constraint, ...]:
    """Book plus pins: what the docket computes its interval against."""
    return build_constraints(language, book, settled)


# --------------------------------------------------------------------------
# A small exact linear program, by vertex enumeration
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Optimum:
    """The attained value of a linear objective over a pointed polyhedron."""

    value: Q
    point: tuple[Q, ...]
    active: tuple[str, ...]


def optimize(constraints: Sequence[Constraint], dimension: int,
             objective: Sequence[Q], sense: str = "min") -> Optimum | None:
    """Exact optimum of `objective . x` over the constraint set, or `None`.

    The feasible sets this module builds are pointed (every variable is bounded
    below and the tolerance variable is bounded below by zero), so a bounded
    objective attains its optimum at a vertex and enumeration is exact.
    """
    if sense not in ("min", "max"):
        raise ValueError("sense must be 'min' or 'max'")
    vertices = _vertices(constraints, dimension)
    if not vertices:
        return None
    scored = [(sum((a * b for a, b in zip(objective, point)), Q(0)), point, active)
              for point, active in vertices]
    value, point, active = (min if sense == "min" else max)(scored,
                                                            key=lambda item: item[0])
    return Optimum(value, tuple(point), tuple(active))


def _lift(constraint: Constraint, extra: Q = Q(0)) -> Constraint:
    """Extend a constraint over `p` to one over `(p, tolerance)`."""
    return Constraint(constraint.source, constraint.coefficients + (extra,),
                      constraint.rhs, constraint.equality)


# --------------------------------------------------------------------------
# The incoherence functional
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class PriceAssignment:
    """A finite price assignment over the current language fragment."""

    book_version: int
    prices: Mapping[str, Q]

    @property
    def sentences(self) -> tuple[str, ...]:
        return tuple(sorted(self.prices))

    def well_formed(self) -> bool:
        return all(Q(0) <= Q(value) <= Q(1) for value in self.prices.values())


@dataclass(frozen=True)
class IncoherenceCertificate:
    """A normalized combination of priced rows bounding the incoherence below.

    `multipliers` are the signed weights on the priced sentences.  Their total
    absolute mass is at most one -- the normalization the dual forces -- so the
    reported `excess` is directly comparable to a declared tolerance.

    The guarantee, checked by `verify_certificate` without trusting the
    extraction: for every feasible assignment `p`,

        sum_s multiplier(s) * ( price(s) - <indicator(s), p> )  >=  excess,

    and since the absolute mass is at most one, the largest single deviation is
    at least `excess` as well.
    """

    multipliers: tuple[tuple[str, Q], ...]
    excess: Q
    absolute_mass: Q

    @property
    def normalized(self) -> bool:
        return Q(self.absolute_mass) <= Q(1)


@dataclass(frozen=True)
class IncoherenceReport:
    book_version: int
    value: Q | None
    witness: tuple[Q, ...] | None
    certificate: IncoherenceCertificate | None
    infeasible: bool

    @property
    def coherent(self) -> bool:
        return self.value == Q(0)


def _price_rows(language: Language, assignment: PriceAssignment,
                ) -> tuple[Constraint, ...]:
    """The two tolerance rows per priced sentence, over `(p, tolerance)`."""
    rows: list[Constraint] = []
    for sentence in assignment.sentences:
        indicator = language.indicator(sentence)
        price = Q(assignment.prices[sentence])
        rows.append(Constraint(f"price+:{sentence}", indicator + (Q(1),), price))
        rows.append(Constraint(f"price-:{sentence}",
                               tuple(-c for c in indicator) + (Q(1),), -price))
    return tuple(rows)


def incoherence(language: Language, settled: Sequence[SettledFact],
                assignment: PriceAssignment) -> IncoherenceReport:
    """The minimal uniform distance from the displayed prices to coherence.

    Measured against `coherence_polytope` -- logic plus pins, never the book.
    The program minimizes the tolerance variable subject to every priced
    sentence sitting within it of its expectation.  Exact, by vertex enumeration.
    """
    unlicensed = [s for s in assignment.sentences if not language.licenses(s)]
    if unlicensed:
        raise ValueError(f"priced sentences outside the language fragment: {unlicensed}")
    base = coherence_polytope(language, settled)
    size = len(language.worlds)
    lifted = [_lift(c) for c in base]
    lifted.append(Constraint("tolerance.nonneg",
                             tuple(Q(0) for _ in range(size)) + (Q(1),), Q(0)))
    lifted.extend(_price_rows(language, assignment))
    objective = tuple(Q(0) for _ in range(size)) + (Q(1),)
    optimum = optimize(lifted, size + 1, objective, "min")
    if optimum is None:
        return IncoherenceReport(assignment.book_version, None, None, None, True)
    certificate = None
    if optimum.value > Q(0):
        certificate = _extract_certificate(lifted, size, optimum, language,
                                           settled, assignment)
    return IncoherenceReport(assignment.book_version, optimum.value,
                             optimum.point[:size], certificate, False)


def _extract_certificate(lifted: Sequence[Constraint], size: int, optimum: Optimum,
                         language: Language, settled: Sequence[SettledFact],
                         assignment: PriceAssignment,
                         ) -> IncoherenceCertificate | None:
    """Read the priced-row multipliers off the optimal active set.

    The extraction is a search for active-set weights reproducing the objective;
    whatever it returns is then *verified* against an independent program, so a
    wrong extraction is caught rather than believed.
    """
    active = set(optimum.active)
    rows = [c for c in lifted if c.source in active]
    weights = _solve_active(rows, size + 1)
    if weights is None:
        return None
    priced: dict[str, Q] = {}
    for source, weight in weights:
        if source.startswith("price+:"):
            priced[source[7:]] = priced.get(source[7:], Q(0)) + weight
        elif source.startswith("price-:"):
            priced[source[7:]] = priced.get(source[7:], Q(0)) - weight
    if not priced:
        return None
    multipliers = tuple(sorted((s, w) for s, w in priced.items() if w != 0))
    mass = sum((abs(w) for _, w in multipliers), Q(0))
    if mass == 0 or mass > Q(1):
        return None
    excess = certificate_excess(language, settled, assignment, multipliers)
    if excess is None:
        return None
    return IncoherenceCertificate(multipliers, excess, mass)


def _solve_active(rows: Sequence[Constraint], dimension: int,
                  ) -> tuple[tuple[str, Q], ...] | None:
    """Nonnegative active-set weights reproducing the tolerance objective."""
    from itertools import combinations

    from src.migration import _solve_square

    target = [Q(0)] * (dimension - 1) + [Q(1)]
    for subset in combinations(range(len(rows)), min(dimension, len(rows))):
        matrix = [[rows[index].coefficients[column] for index in subset]
                  for column in range(dimension)]
        solution = _solve_square(matrix, target)
        if solution is None:
            continue
        if any(value < 0 for value, index in zip(solution, subset)
               if not rows[index].equality):
            continue
        reproduced = all(
            sum((weight * rows[index].coefficients[column]
                 for weight, index in zip(solution, subset)), Q(0)) == target[column]
            for column in range(dimension))
        if reproduced:
            return tuple((rows[index].source, value)
                         for value, index in zip(solution, subset))
    return None


def certificate_excess(language: Language, settled: Sequence[SettledFact],
                       assignment: PriceAssignment,
                       multipliers: Sequence[tuple[str, Q]]) -> Q | None:
    """The bound a multiplier vector certifies, recomputed independently.

    `min over coherent p of sum_s w_s (price(s) - <indicator(s), p>)`, which is
    an exact linear program over `coherence_polytope`.  This never reads the
    extraction's arithmetic, so it is a check and not a restatement.
    """
    base = coherence_polytope(language, settled)
    size = len(language.worlds)
    combined = [Q(0)] * size
    constant = Q(0)
    for sentence, weight in multipliers:
        indicator = language.indicator(sentence)
        constant += Q(weight) * Q(assignment.prices[sentence])
        for index in range(size):
            combined[index] -= Q(weight) * indicator[index]
    optimum = optimize(base, size, tuple(combined), "min")
    if optimum is None:
        return None
    return constant + optimum.value


def verify_certificate(language: Language, settled: Sequence[SettledFact],
                       assignment: PriceAssignment,
                       certificate: IncoherenceCertificate) -> bool:
    """Is the certificate sound: normalized, and its excess actually attained?"""
    if not certificate.normalized:
        return False
    excess = certificate_excess(language, settled, assignment,
                                certificate.multipliers)
    return excess is not None and excess >= Q(certificate.excess)


# --------------------------------------------------------------------------
# The two sanity theorems
# --------------------------------------------------------------------------


def prices_are_feasible(language: Language, settled: Sequence[SettledFact],
                        assignment: PriceAssignment) -> bool:
    """Is there a coherent assignment reproducing every displayed price exactly?"""
    base = list(coherence_polytope(language, settled))
    for sentence in assignment.sentences:
        base.append(Constraint(f"exact:{sentence}", language.indicator(sentence),
                               Q(assignment.prices[sentence]), True))
    size = len(language.worlds)
    return optimize(base, size, tuple(Q(0) for _ in range(size)), "min") is not None


def incoherence_is_zero_iff_feasible(language: Language,
                                     settled: Sequence[SettledFact],
                                     assignment: PriceAssignment) -> bool:
    """Sanity theorem 1, as a checked biconditional on an instance."""
    report = incoherence(language, settled, assignment)
    feasible = prices_are_feasible(language, settled, assignment)
    if report.infeasible:
        return not feasible
    return report.coherent == feasible


def incoherence_is_monotone(language: Language, settled: Sequence[SettledFact],
                            assignment: PriceAssignment,
                            added: Sequence[SettledFact] = ()) -> bool:
    """Sanity theorem 2: adding constraints never lowers the incoherence.

    Adding a constraint shrinks the coherent set, and a minimum over a subset is
    at least the minimum over the set, so the functional is nondecreasing.  The
    constraints that can be added are pins and logical relations -- not
    endorsements, which are not in this polytope at all.  This checks the
    inequality on an instance; the argument is the one sentence above.
    """
    before = incoherence(language, settled, assignment)
    after = incoherence(language, tuple(settled) + tuple(added), assignment)
    if after.infeasible:
        return True
    if before.infeasible:
        return False
    return Q(after.value) >= Q(before.value)


# --------------------------------------------------------------------------
# The tolerance-robust docket
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ToleranceSchedule:
    """A declared tolerance per date.  `exact` is the schedule identically zero."""

    schedule_id: str
    values: Mapping[int, Q]
    default: Q = Q(0)

    def at(self, date: int) -> Q:
        return Q(self.values.get(date, self.default))

    @property
    def exact(self) -> bool:
        return Q(self.default) == Q(0) and all(Q(v) == Q(0) for v in self.values.values())


EXACT_SCHEDULE = ToleranceSchedule("tolerance:exact", {}, Q(0))


def relax(constraints: Sequence[Constraint], tolerance: Q) -> tuple[Constraint, ...]:
    """Relax every relaxable row by the tolerance, under the stated normalization.

    A row is relaxable when it is neither the simplex nor a pin.  Each row is
    scaled to maximum coefficient magnitude one before the tolerance is
    subtracted, so the same tolerance means the same thing on every row.
    """
    if Q(tolerance) < 0:
        raise ValueError("a tolerance is nonnegative")
    relaxed: list[Constraint] = []
    for constraint in constraints:
        if any(constraint.source.startswith(p) for p in INCORRIGIBLE_PREFIXES):
            relaxed.append(constraint)
            continue
        scale = max((abs(Q(c)) for c in constraint.coefficients), default=Q(0))
        if scale == 0:
            relaxed.append(constraint)
            continue
        relaxed.append(Constraint(constraint.source, constraint.coefficients,
                                  Q(constraint.rhs) - Q(tolerance) * scale,
                                  constraint.equality))
    return tuple(relaxed)


def robust_interval(language: Language, book: Book, settled: Sequence[SettledFact],
                    target: str, tolerance: Q) -> LeverageInterval:
    """The interval computed against the relaxed feasible set.

    At tolerance zero every relaxable row keeps its own right-hand side, so the
    constraint set is *identical* to the exact one and this is the exact
    interval -- not merely equal to it.  `robust_reduces_at_zero` checks that.
    """
    if Q(tolerance) == Q(0):
        return compute_interval(language, book, settled, target)
    relaxed = relax(build_constraints(language, book, settled), tolerance)
    return _interval_from(relaxed, language, book.book_version, target)


def _interval_from(constraints: Sequence[Constraint], language: Language,
                   book_version: int, target: str) -> LeverageInterval:
    from src.leverage_interval import (
        DualCertificate,
        InfeasibilityCertificate,
        PrimalWitness,
        _dual,
    )

    if not language.licenses(target):
        return LeverageInterval(book_version, target, None, None, None, None, None,
                                None, False, None, licensed=False)
    size = len(language.worlds)
    objective = language.indicator(target)
    vertices = _vertices(constraints, size)
    if not vertices:
        return LeverageInterval(
            book_version, target, None, None, None, None, None, None, True,
            InfeasibilityCertificate(
                tuple((c.source, Q(1)) for c in constraints
                      if not any(c.source.startswith(p) for p in ("simplex.",))),
                "no probability assignment satisfies the relaxed constraint set"))
    scored = [(sum((a * b for a, b in zip(objective, point)), Q(0)), point, active)
              for point, active in vertices]
    low, low_point, low_active = min(scored, key=lambda item: item[0])
    high, high_point, high_active = max(scored, key=lambda item: item[0])
    return LeverageInterval(
        book_version, target, low, high,
        PrimalWitness(low_point, low, low_active),
        PrimalWitness(high_point, high, high_active),
        _dual(constraints, low_active, objective, "lower"),
        _dual(constraints, high_active, objective, "upper"),
        False, None)


def robust_reduces_at_zero(language: Language, book: Book,
                           settled: Sequence[SettledFact], target: str) -> bool:
    """The reduction theorem for the interval, checked on an instance.

    Not a remark: the relaxed constraint list at tolerance zero is elementwise
    equal to the exact one, so the two programs are the same program.
    """
    exact = build_constraints(language, book, settled)
    relaxed = relax(exact, Q(0))
    if relaxed != tuple(exact):
        return False
    return (robust_interval(language, book, settled, target, Q(0))
            == compute_interval(language, book, settled, target))


@dataclass(frozen=True)
class RobustMeritsCertificate:
    """A merits direction certified against the relaxed set at a declared tolerance."""

    certificate_id: str
    target: str
    book_version: int
    tolerance: Q
    interval: LeverageInterval
    threshold: Q
    direction: str


def robust_certify_merits(language: Language, book: Book,
                          settled: Sequence[SettledFact], target: str,
                          threshold: Q, tolerance: Q,
                          certificate_id: str) -> RobustMeritsCertificate | None:
    """Certify only what survives the declared tolerance.

    At tolerance zero this is the exact merits certification: the interval is
    the exact interval and the direction rule is the docket's own.
    """
    interval = robust_interval(language, book, settled, target, tolerance)
    direction = threshold_direction(interval, Q(threshold))
    if direction is None:
        return None
    return RobustMeritsCertificate(certificate_id, target, book.book_version,
                                   Q(tolerance), interval, Q(threshold), direction)


def robust_sure_loss_grounds(language: Language, settled: Sequence[SettledFact],
                             assignment: PriceAssignment, tolerance: Q,
                             grounds_id: str) -> Grounds | None:
    """The tolerance-robust sure-loss objection, against the *engine*.

    Its grounds are a normalized certificate of incoherence strictly exceeding
    the declared schedule.  Conformance is not an opinion: the excess and the
    schedule are the same units by the stated normalization.

    This objection is about the engine's prices and is measured on
    `coherence_polytope`.  The book's own sure-loss -- endorsements jointly
    infeasible with the pins -- is a *different* objection with a different
    respondent, and it already has one: the existing infeasibility grounds on
    the docket interval.  Keeping them apart is what stops a book breach being
    tolled as an engine breach.
    """
    report = incoherence(language, settled, assignment)
    if report.infeasible or report.value is None:
        return None
    if Q(report.value) <= Q(tolerance) or report.certificate is None:
        return None
    if not verify_certificate(language, settled, assignment, report.certificate):
        return None
    return Grounds(grounds_id, {
        "multipliers": report.certificate.multipliers,
        "excess": Q(report.certificate.excess),
        "absolute_mass": Q(report.certificate.absolute_mass),
        "declared_tolerance": Q(tolerance),
        "book_version": assignment.book_version})


# --------------------------------------------------------------------------
# Non-vacuity, as a computable check
# --------------------------------------------------------------------------


def tolerance_is_working(language: Language, book: Book,
                         settled: Sequence[SettledFact], target: str,
                         threshold: Q, tolerance: Q) -> bool:
    """Is the declared tolerance *working* at this date for this displayed book?

    Working means the robust interval still strictly separates: some merits
    direction survives the relaxation.  The audit's observation that a sound but
    maximal declaration is useless is exactly this predicate returning `False`
    at tolerance one, where the relaxed interval degenerates.
    """
    interval = robust_interval(language, book, settled, target, Q(tolerance))
    return threshold_direction(interval, Q(threshold)) is not None


def working_boundary(language: Language, book: Book,
                     settled: Sequence[SettledFact], target: str, threshold: Q,
                     denominator: int = 240) -> tuple[Q, Q]:
    """The schedule value at which this book's merits certificate stops clearing.

    Returned as the certified pair `(last working, first not working)` over the
    stated rational grid.  Both endpoints are verified by recomputation, so the
    pair is exact evidence about that grid, not an estimate of a limit.

    Bisection is sound here because the predicate is monotone: a larger
    tolerance relaxes a superset of rows by at least as much, so the robust
    interval only widens, and separation once lost is never regained.
    """
    if denominator <= 0:
        raise ValueError("the grid denominator is positive")
    step = Q(1, denominator)
    if not tolerance_is_working(language, book, settled, target, threshold, Q(0)):
        return Q(0), Q(0)
    if tolerance_is_working(language, book, settled, target, threshold, Q(1)):
        return Q(1), Q(1) + step
    low, high = 0, denominator          # low works, high does not
    while high - low > 1:
        middle = (low + high) // 2
        if tolerance_is_working(language, book, settled, target, threshold,
                                middle * step):
            low = middle
        else:
            high = middle
    return low * step, high * step


# --------------------------------------------------------------------------
# T2: certification layering
# --------------------------------------------------------------------------

ENGINE_BREACH = "engine"
BOOK_BREACH = "book"
NO_BREACH = "none"


@dataclass(frozen=True)
class ToleranceDeclaration:
    """What the engine certified, and what the book voluntarily declared on top.

    The book's tighter working tolerance is *book content*: it enters the record
    as the book's own declared standard, so breaching it is chargeable to the
    book.  Breaching the engine's certified tolerance is the engine's, and tolls.
    """

    date: int
    engine_certified: Q
    book_declared: Q | None = None

    def well_formed(self) -> bool:
        return Q(self.engine_certified) >= 0 and (
            self.book_declared is None
            or Q(0) <= Q(self.book_declared) <= Q(self.engine_certified))


@dataclass(frozen=True)
class BreachAttribution:
    date: int
    realized: Q
    attributed_to: str
    tolled: bool
    chargeable: bool
    detail: str


def attribute_breach(declaration: ToleranceDeclaration,
                     realized: Q) -> BreachAttribution:
    """`T2`.  Who carries a tolerance breach, and what follows from it.

    Above the engine's certified tolerance the cost is the engine's: the clocks
    the breach touches toll, and nothing is chargeable to the book -- substrate
    failure never converts into unearned book liability.  Between the book's
    voluntary tighter tolerance and the engine's certified one, the book assumed
    the risk: chargeable, and no tolling.
    """
    if not declaration.well_formed():
        raise ValueError("a book tolerance must be at most the engine's certified one")
    realized = Q(realized)
    if realized > Q(declaration.engine_certified):
        return BreachAttribution(
            declaration.date, realized, ENGINE_BREACH, True, False,
            "realized incoherence exceeded the engine's certified tolerance")
    if (declaration.book_declared is not None
            and realized > Q(declaration.book_declared)):
        return BreachAttribution(
            declaration.date, realized, BOOK_BREACH, False, True,
            "realized incoherence exceeded the book's voluntarily declared tolerance")
    return BreachAttribution(declaration.date, realized, NO_BREACH, False, False,
                             "within every declared tolerance")
