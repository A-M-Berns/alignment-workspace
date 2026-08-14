"""The core condition under settlement contraction: two readings, and the transport.

The frozen operative-force interface asks for a witnessed reference `q` and a
fixed core coefficient with

    q + theta * (P - q)  contained in  S,

and the joint theorem inherits it verbatim.  When settlement pins collapse
dimensions the phrase `P` becomes ambiguous, and the two readings are not
equivalent -- one of them is empty.

**Ambient reading.**  `P` is the ambient simplex over the whole world set.  A pin
is an exact equality, so `S` lies inside a hyperplane, while the homothet of the
ambient simplex has the simplex's own dimension for every positive coefficient.
A set of dimension `d` does not contain a set of dimension `d`, positioned by a
positive homothety, unless the containing set is all of it.  So the ambient
reading voids on the first non-trivial exact pin, for *every* positive
coefficient.  `ambient_voids_witness` displays the two-sentence instance.

**Relative reading.**  `P` is re-read as the post-pin feasible simplex: the
probability assignments consistent with the pins alone, before any endorsement.
The core condition is taken relative to that.  This is the reading that survives
settlement, and `transport_lemma` is the sense in which it is stable.

**The linear reformulation, which does the work.**  Containment of the homothet
is equivalent to a finite system that is *linear in the reference at fixed
coefficient*: for each endorsement row `c . x >= r` and each vertex `v` of the
relative simplex,

    (1 - theta) * <c, q>  +  theta * <c, v>  >=  r,

and minimizing the left side over vertices replaces the whole vertex family by
one number per row.  Two consequences run through this module.  Whether a
declared coefficient is satisfiable *right now* is therefore a linear program,
not an open question -- that is the clipping adapter of the composition theorem.
And the maximal satisfiable coefficient is the boundary of a monotone predicate,
so it is bracketed exactly by bisection and pinned in closed form whenever a
single row binds.

Finiteness discipline.  Worlds, endorsement rows, and pins are finite; every
quantity is an exact rational from vertex enumeration or a closed form.

All arithmetic is exact rationals.  No floating point.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.coherence import optimize
from src.joint_tightening import core_vertices
from src.leverage_interval import (
    Book,
    Constraint,
    Endorsement,
    Language,
    SettledFact,
    build_constraints,
    _vertices,
)


# --------------------------------------------------------------------------
# The two ambient objects
# --------------------------------------------------------------------------


def simplex_constraints(size: int) -> tuple[Constraint, ...]:
    """The ambient simplex: total one, every coordinate nonnegative."""
    rows = [Constraint("simplex.total", tuple(Q(1) for _ in range(size)), Q(1), True)]
    for index in range(size):
        rows.append(Constraint(
            f"simplex.nonneg:{index}",
            tuple(Q(1) if position == index else Q(0) for position in range(size)),
            Q(0)))
    return tuple(rows)


def ambient_vertices(size: int) -> tuple[tuple[Q, ...], ...]:
    """The vertices of the ambient simplex: the point masses."""
    return tuple(tuple(Q(1) if position == index else Q(0) for position in range(size))
                 for index in range(size))


def relative_vertices(language: Language,
                      settled: Sequence[SettledFact]) -> tuple[tuple[Q, ...], ...]:
    """The vertices of the post-pin feasible simplex: the quotient by the pins.

    This is the ambient simplex intersected with every pin equality, and nothing
    else -- no endorsement enters, because the relative reading re-reads the
    *ambient* object, not the endorsed region.
    """
    size = len(language.worlds)
    rows = list(simplex_constraints(size))
    for fact in settled:
        rows.append(Constraint(f"settled:{fact.sentence}",
                               language.indicator(fact.sentence), Q(fact.value), True))
    return tuple(point for point, _ in _vertices(rows, size))


def endorsement_rows(language: Language, book: Book) -> tuple[Constraint, ...]:
    """The endorsed rows alone, which are what the core must be contained in."""
    size = len(language.worlds)
    rows: list[Constraint] = []
    for endorsement in book.endorsements:
        if len(endorsement.coefficients) != size:
            raise ValueError(f"endorsement {endorsement.endorsement_id} has wrong width")
        rows.append(Constraint(f"book:{endorsement.endorsement_id}",
                               tuple(Q(c) for c in endorsement.coefficients),
                               Q(endorsement.rhs)))
    return tuple(rows)


def _dot(left: Sequence[Q], right: Sequence[Q]) -> Q:
    return sum((Q(a) * Q(b) for a, b in zip(left, right)), Q(0))


# --------------------------------------------------------------------------
# The two readings, as predicates
# --------------------------------------------------------------------------


def core_holds(reference: Sequence[Q], theta: Q,
               vertices: Sequence[Sequence[Q]],
               rows: Sequence[Constraint],
               pins: Sequence[Constraint] = ()) -> bool:
    """Is the homothet of `vertices` about `reference` inside the endorsed region?

    The core is the convex hull of the shrunk vertices and each row is a
    half-space, so checking the shrunk vertices decides containment.  Pin
    equalities are checked as well when supplied: a core that leaves the pinned
    hyperplane is not inside the settled record's region.
    """
    if not Q(0) < Q(theta) <= Q(1):
        raise ValueError("the core coefficient lies in (0,1]")
    shrunk = core_vertices(reference, Q(theta), vertices)
    for point in shrunk:
        for row in rows:
            if _dot(row.coefficients, point) < Q(row.rhs):
                return False
        for pin in pins:
            if _dot(pin.coefficients, point) != Q(pin.rhs):
                return False
    return True


def ambient_core_holds(language: Language, book: Book,
                       settled: Sequence[SettledFact],
                       reference: Sequence[Q], theta: Q) -> bool:
    """The ambient reading: the homothet of the *whole* simplex must fit."""
    size = len(language.worlds)
    pins = tuple(Constraint(f"settled:{f.sentence}", language.indicator(f.sentence),
                            Q(f.value), True) for f in settled)
    return core_holds(reference, theta, ambient_vertices(size),
                      endorsement_rows(language, book), pins)


def relative_core_holds(language: Language, book: Book,
                        settled: Sequence[SettledFact],
                        reference: Sequence[Q], theta: Q) -> bool:
    """The relative reading: the homothet of the post-pin simplex must fit."""
    return core_holds(reference, theta, relative_vertices(language, settled),
                      endorsement_rows(language, book))


# --------------------------------------------------------------------------
# The linear reformulation and the clipping adapter
# --------------------------------------------------------------------------


def row_minimum(row: Constraint, vertices: Sequence[Sequence[Q]]) -> Q:
    return min(_dot(row.coefficients, vertex) for vertex in vertices)


def row_maximum(row: Constraint, vertices: Sequence[Sequence[Q]]) -> Q:
    return max(_dot(row.coefficients, vertex) for vertex in vertices)


def core_admissible_constraints(theta: Q, vertices: Sequence[Sequence[Q]],
                                rows: Sequence[Constraint],
                                base: Sequence[Constraint],
                                ) -> tuple[Constraint, ...]:
    """The references admitting the coefficient, as a linear system.

    `(1 - theta) <c, q> >= r - theta * min_v <c, v>` for each endorsed row, on
    top of the pinned simplex.  At `theta = 1` the left side vanishes and the
    system is the constant test `min_v <c, v> >= r`, which is the honest reading:
    a coefficient of one demands the whole relative simplex already satisfy the
    endorsement.
    """
    if not Q(0) < Q(theta) <= Q(1):
        raise ValueError("the core coefficient lies in (0,1]")
    system = list(base)
    for row in rows:
        minimum = row_minimum(row, vertices)
        system.append(Constraint(
            f"core:{row.source}",
            tuple((Q(1) - Q(theta)) * Q(c) for c in row.coefficients),
            Q(row.rhs) - Q(theta) * minimum))
    return tuple(system)


def core_admissible_reference(language: Language, book: Book,
                              settled: Sequence[SettledFact],
                              theta: Q) -> tuple[Q, ...] | None:
    """A reference admitting the declared coefficient, or `None` if there is none.

    This is `P1` made checkable at a date: the clipping adapter restricts the
    reference to this region, and an empty region is a detected condition with a
    declared consequence, not a silent failure.
    """
    size = len(language.worlds)
    base = list(simplex_constraints(size))
    for fact in settled:
        base.append(Constraint(f"settled:{fact.sentence}",
                               language.indicator(fact.sentence), Q(fact.value), True))
    system = core_admissible_constraints(
        theta, relative_vertices(language, settled),
        endorsement_rows(language, book), base)
    optimum = optimize(system, size, tuple(Q(0) for _ in range(size)), "min")
    return None if optimum is None else optimum.point


def clipping_adapter_admits(language: Language, book: Book,
                            settled: Sequence[SettledFact], theta_minimum: Q) -> bool:
    """Does the declared core minimum survive at this date, under the relative reading?"""
    return core_admissible_reference(language, book, settled, theta_minimum) is not None


FORCE_GRANTED = "operative force granted at the declared core minimum"
QUARANTINE_OF_FORCE = "quarantine of operative force: no reference admits the minimum"


@dataclass(frozen=True)
class CoreAdmission:
    """The clipping adapter's verdict at one date, with its declared consequence.

    The adapter restricts the reference to the admissible region.  When that
    region is empty the adapter does not proceed on a coefficient it cannot
    support and does not silently shrink the declared minimum: emptiness is a
    *detected* condition with a declared branch, which is the quarantine clause
    of the breach stack applied to operative force.
    """

    theta_minimum: Q
    reference: tuple[Q, ...] | None
    date: int | None = None

    @property
    def admitted(self) -> bool:
        return self.reference is not None

    @property
    def consequence(self) -> str:
        return FORCE_GRANTED if self.admitted else QUARANTINE_OF_FORCE


def core_admission(language: Language, book: Book, settled: Sequence[SettledFact],
                   theta_minimum: Q, date: int | None = None) -> CoreAdmission:
    """Run the clipping adapter at a date: a linear program with a declared branch."""
    return CoreAdmission(
        Q(theta_minimum),
        core_admissible_reference(language, book, settled, theta_minimum), date)


# --------------------------------------------------------------------------
# The maximal satisfiable coefficient
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class CoreBound:
    """What is known exactly about the maximal satisfiable core coefficient.

    `working` is verified satisfiable by an exhibited reference; `failing` is
    verified unsatisfiable by emptiness of the linear system.  `upper_bound` is
    the closed-form per-row bound, which is exact whenever one row binds.

    `working == 0` together with `exact` says every positive coefficient fails,
    which is the voided case; `working == 0` without `exact` says only that the
    grid found nothing.
    """

    working: Q
    failing: Q | None
    witness: tuple[Q, ...] | None
    upper_bound: Q
    exact: bool

    @property
    def brackets(self) -> tuple[Q, Q | None]:
        return self.working, self.failing


def single_row_core_coefficient(minimum: Q, rhs: Q, maximum: Q) -> Q:
    """Closed form for one endorsed row: `(M - r) / (M - m)`.

    With one row the best reference is any maximizer of the row, where the
    condition reads `(1 - theta) M + theta m >= r`.  No reference does better,
    because the condition forces `(1 - theta) <c, q> + theta m >= r` and
    `<c, q>` is at most `M`.  Both directions are one line, which is why this is
    the only case with an exact point rather than a bracket.
    """
    minimum, rhs, maximum = Q(minimum), Q(rhs), Q(maximum)
    if maximum < rhs:
        return Q(0)
    if maximum == minimum:
        return Q(1)
    return min(Q(1), (maximum - rhs) / (maximum - minimum))


def core_upper_bound(vertices: Sequence[Sequence[Q]],
                     rows: Sequence[Constraint]) -> Q:
    """`min` over rows of the closed form: an exact upper bound in general.

    Each row alone already caps the coefficient, and the joint condition implies
    every single-row condition, so the minimum is an upper bound.  It need not
    be attained when two rows pull the reference in different directions.
    """
    if not rows:
        return Q(1)
    return min(single_row_core_coefficient(row_minimum(row, vertices), Q(row.rhs),
                                           row_maximum(row, vertices))
               for row in rows)


def max_core_coefficient(language: Language, book: Book,
                         settled: Sequence[SettledFact],
                         denominator: int = 720) -> CoreBound:
    """Bracket the maximal satisfiable coefficient exactly, over a stated grid.

    Satisfiability is monotone: a reference admitting a coefficient admits every
    smaller one, because the smaller homothet is a convex combination of the
    reference and the larger homothet, both inside the region.  So bisection is
    sound, and both returned endpoints are verified by recomputation.
    """
    if denominator <= 0:
        raise ValueError("the grid denominator is positive")
    rows = endorsement_rows(language, book)
    vertices = relative_vertices(language, settled)
    bound = core_upper_bound(vertices, rows)
    if not vertices:
        return CoreBound(Q(0), None, None, bound, False)
    if not rows:
        witness = core_admissible_reference(language, book, settled, Q(1))
        return CoreBound(Q(1), None, witness, Q(1), True)
    if bound == 0:
        # The closed-form per-row bound is itself zero, so no positive
        # coefficient can survive: the answer is exact and it is zero.
        return CoreBound(Q(0), None, None, Q(0), True)
    step = Q(1, denominator)
    if clipping_adapter_admits(language, book, settled, bound):
        witness = core_admissible_reference(language, book, settled, bound)
        return CoreBound(bound, None, witness, bound, True)
    if not clipping_adapter_admits(language, book, settled, step):
        return CoreBound(Q(0), step, None, bound, False)
    low, high = 1, denominator
    while high - low > 1:
        middle = (low + high) // 2
        if clipping_adapter_admits(language, book, settled, middle * step):
            low = middle
        else:
            high = middle
    working = low * step
    return CoreBound(working, high * step,
                     core_admissible_reference(language, book, settled, working),
                     bound, False)


# --------------------------------------------------------------------------
# The transport lemma, and the dependent-pin failure
# --------------------------------------------------------------------------


def pin_is_independent(language: Language, reference: Sequence[Q],
                       pin: SettledFact) -> bool:
    """Is the pin *confirmed* by the incumbent reference?

    This is the sense of independence the transport lemma needs, and it is the
    checkable one: the pin is independent of the endorsed content when the
    reference those endorsements support already assigns the pinned value.  A
    pin the incumbent contradicts is correlated with the endorsements through
    the reference they jointly determine, and it is exactly those that break
    transport.
    """
    return _dot(language.indicator(pin.sentence), reference) == Q(pin.value)


def transport_lemma(language: Language, book: Book,
                    settled: Sequence[SettledFact], reference: Sequence[Q],
                    theta: Q, pin: SettledFact) -> bool:
    """Pinning commutes with the relative core across an independent pin.

    Statement.  Let the relative core condition hold at `reference` with
    coefficient `theta`, and let the new pin be confirmed by `reference`.  Then
    the relative core condition holds at the *same* reference and the *same*
    coefficient after the pin.

    Proof.  Write `H` for the pinned hyperplane.  The post-pin relative simplex
    is contained in the pre-pin one, so every shrunk vertex after the pin is a
    shrunk point before it, hence in the endorsed region by hypothesis.  And
    `reference` lies in `H` by independence while each post-pin vertex lies in
    `H` by construction, so the whole segment between them lies in `H` because
    `H` is affine.  The shrunk points therefore lie in the endorsed region and
    in `H`, which is the post-pin condition.  The lemma is checked below on the
    instance as well as argued here.
    """
    if not pin_is_independent(language, reference, pin):
        raise ValueError("the transport lemma is stated for confirmed pins")
    if not relative_core_holds(language, book, settled, reference, theta):
        raise ValueError("the lemma assumes the core condition before the pin")
    return relative_core_holds(language, book, tuple(settled) + (pin,), reference,
                               theta)


@dataclass(frozen=True)
class PinEffect:
    """What one pin did to the maximal satisfiable coefficient."""

    sentence: str
    value: Q
    independent: bool
    before: Q
    after: Q
    transported: bool | None

    @property
    def collapsed(self) -> bool:
        return Q(self.after) == Q(0)


def pin_effect(language: Language, book: Book, settled: Sequence[SettledFact],
               reference: Sequence[Q], theta: Q, pin: SettledFact,
               denominator: int = 720) -> PinEffect:
    """Classify one pin: independent or not, and what it cost the coefficient."""
    before = max_core_coefficient(language, book, settled, denominator)
    after = max_core_coefficient(language, book, tuple(settled) + (pin,), denominator)
    independent = pin_is_independent(language, reference, pin)
    transported: bool | None = None
    if independent and relative_core_holds(language, book, settled, reference, theta):
        transported = transport_lemma(language, book, settled, reference, theta, pin)
    return PinEffect(pin.sentence, Q(pin.value), independent, before.working,
                     after.working, transported)


@dataclass(frozen=True)
class TrajectoryReport:
    """The coefficient as pins accumulate, and the smallest value reached."""

    stages: tuple[tuple[str, Q], ...]
    coefficients: tuple[Q, ...]
    minimum: Q
    survives: bool
    declared_minimum: Q


def accumulate_pins(language: Language, book: Book,
                    pins: Sequence[SettledFact], declared_minimum: Q,
                    denominator: int = 720) -> TrajectoryReport:
    """Track the maximal satisfiable coefficient along a finite pin trajectory.

    The reported minimum is over the *searched* trajectory.  Nothing here is an
    asymptotic claim: this is finite-instance evidence about displayed kernels.
    """
    settled: list[SettledFact] = []
    coefficients = [max_core_coefficient(language, book, settled, denominator).working]
    stages: list[tuple[str, Q]] = []
    for pin in pins:
        settled.append(pin)
        stages.append((pin.sentence, Q(pin.value)))
        coefficients.append(
            max_core_coefficient(language, book, settled, denominator).working)
    smallest = min(coefficients)
    return TrajectoryReport(tuple(stages), tuple(coefficients), smallest,
                            smallest >= Q(declared_minimum), Q(declared_minimum))


# --------------------------------------------------------------------------
# Displayed witnesses
# --------------------------------------------------------------------------


def ambient_voids_witness() -> Mapping[str, object]:
    """The two-sentence instance on which the ambient reading voids.

    Two worlds, two sentences, one pin.  Pinning the first sentence at one half
    forces the single assignment `(1/2, 1/2)`, so the endorsed region is that
    point, while the homothet of the ambient simplex about it is a segment of
    positive length for every positive coefficient.  No coefficient survives.
    """
    language = Language(("w1", "w2"), {"A": ("w1",), "B": ("w2",)})
    book = Book(1, ())
    settled = (SettledFact("A", Q(1, 2)),)
    reference = (Q(1, 2), Q(1, 2))
    coefficients = (Q(1, 2), Q(1, 10), Q(1, 100), Q(1, 1000))
    ambient = tuple((c, ambient_core_holds(language, book, settled, reference, c))
                    for c in coefficients)
    relative = tuple((c, relative_core_holds(language, book, settled, reference, c))
                     for c in coefficients)
    return {"language": language, "book": book, "settled": settled,
            "reference": reference, "ambient": ambient, "relative": relative}


def ambient_voids_nondegenerate() -> Mapping[str, object]:
    """The same voiding where the endorsed region is a segment, not a point.

    Three worlds; the pin leaves a one-dimensional region, so the failure cannot
    be dismissed as the region having collapsed to a single assignment.
    """
    language = Language(("w1", "w2", "w3"),
                        {"A": ("w1", "w2"), "B": ("w2",)})
    book = Book(1, ())
    settled = (SettledFact("A", Q(1, 2)),)
    reference = (Q(1, 4), Q(1, 4), Q(1, 2))
    coefficients = (Q(1, 2), Q(1, 10), Q(1, 1000))
    ambient = tuple((c, ambient_core_holds(language, book, settled, reference, c))
                    for c in coefficients)
    relative = tuple((c, relative_core_holds(language, book, settled, reference, c))
                     for c in coefficients)
    return {"language": language, "book": book, "settled": settled,
            "reference": reference, "ambient": ambient, "relative": relative,
            "region_dimension": 1}


def dependent_pin_failure() -> Mapping[str, object]:
    """A dependent pin destroying a relative core that an independent one keeps.

    Three worlds; the book endorses `p1 >= 1/2`; before any pin the relative
    reading admits coefficient one half at the reference `(1,0,0)`, which is the
    closed form `(M - r) / (M - m) = (1 - 1/2) / (1 - 0)`.  Pinning the second
    world's sentence at one half contradicts that reference, and the post-pin
    endorsed region is the single assignment `(1/2, 1/2, 0)` while the post-pin
    relative simplex is a segment: no positive coefficient survives.
    """
    language = Language(("w1", "w2", "w3"),
                        {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
    book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),))
    reference = (Q(1), Q(0), Q(0))
    dependent = SettledFact("B", Q(1, 2))
    independent = SettledFact("B", Q(0))
    return {"language": language, "book": book, "reference": reference,
            "dependent": dependent, "independent": independent}


def small_instance_search(denominator: int = 720) -> Mapping[str, object]:
    """Exact-rational sweep over small instances, classifying every pin.

    Three worlds, one endorsed row drawn from a small rational family, and every
    pin from a small family.  Each `(row, pin)` pair is classified by whether the
    pin is confirmed by the incumbent reference, whether transport holds, and
    whether the maximal coefficient survives.
    """
    worlds = ("w1", "w2", "w3")
    truth = {"A": ("w1",), "B": ("w2",), "C": ("w3",), "AB": ("w1", "w2")}
    language = Language(worlds, truth)
    rows = (
        ("e:A>=1/2", (Q(1), Q(0), Q(0)), Q(1, 2)),
        ("e:A>=1/4", (Q(1), Q(0), Q(0)), Q(1, 4)),
        ("e:AB>=1/2", (Q(1), Q(1), Q(0)), Q(1, 2)),
        ("e:AB>=3/4", (Q(1), Q(1), Q(0)), Q(3, 4)),
    )
    pins = tuple(SettledFact(sentence, value)
                 for sentence in ("A", "B", "C")
                 for value in (Q(0), Q(1, 4), Q(1, 2)))
    independent_transport = 0
    independent_total = 0
    dependent_collapsed: list[tuple[str, str, Q]] = []
    dependent_reduced: list[tuple[str, str, Q, Q, Q]] = []
    dependent_total = 0
    for name, coefficients, rhs in rows:
        book = Book(1, (Endorsement(name, coefficients, rhs),))
        before = max_core_coefficient(language, book, (), denominator)
        if before.working == 0 or before.witness is None:
            continue
        reference, theta = before.witness, before.working
        for pin in pins:
            after = max_core_coefficient(language, book, (pin,), denominator)
            if not relative_vertices(language, (pin,)):
                continue
            if pin_is_independent(language, reference, pin):
                independent_total += 1
                if transport_lemma(language, book, (), reference, theta, pin):
                    independent_transport += 1
            else:
                dependent_total += 1
                if after.working == 0:
                    dependent_collapsed.append((name, pin.sentence, Q(pin.value)))
                elif after.working < theta:
                    dependent_reduced.append((name, pin.sentence, Q(pin.value),
                                              theta, after.working))
    return {"independent_total": independent_total,
            "independent_transport": independent_transport,
            "dependent_total": dependent_total,
            "dependent_collapsed": tuple(dependent_collapsed),
            "dependent_reduced": tuple(dependent_reduced)}
