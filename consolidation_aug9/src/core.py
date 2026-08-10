"""Core geometry: the two readings of the core condition, and transport under settlement.

Folder-local; readable against `THEORY_11` alone.

The enforcement clause asks for a witnessed reference `q` and a core coefficient
`theta > 0` with `q + theta(P - q)` inside the endorsed region `S`. When
settlement collapses dimensions, "P" becomes ambiguous, and the two readings are
not equivalent -- one is empty.

**Ambient reading:** `P` is the whole simplex over the language. A settled
equality puts `S` inside a hyperplane while the homothet keeps the simplex's own
dimension, so containment fails for every positive coefficient from the first
non-trivial settlement onward.

**Relative reading:** `P` is the post-settlement simplex -- the assignments
consistent with the settled record alone, before any endorsement. This is the
reading that survives.

**The linear reformulation**, which does all the work: containment is equivalent
to a finite system that is *linear in the reference at fixed coefficient*. For
each endorsed row `c . x >= r` and each vertex `v` of the relative simplex,

    (1 - theta) <c, q>  +  theta <c, v>  >=  r,

and minimizing the left side over vertices replaces the whole vertex family by
one number per row. Hence: satisfiability of a declared coefficient at a date is
a linear program, and the maximal coefficient is the boundary of a monotone
predicate.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Mapping, Sequence

from src.exact import Constraint, optimize, vertices
from src.interval import (
    Book,
    Endorsement,
    Language,
    SettledFact,
    coherence_polytope,
    endorsement_rows,
    simplex_rows,
)


def ambient_vertices(size: int) -> tuple[tuple[Q, ...], ...]:
    """The point masses: the vertices of the whole simplex."""
    return tuple(tuple(Q(1) if p == i else Q(0) for p in range(size))
                 for i in range(size))


def relative_vertices(language: Language,
                      settled: Sequence[SettledFact]) -> tuple[tuple[Q, ...], ...]:
    """Vertices of the post-settlement simplex: the simplex cut by the settled record.

    No endorsement enters. The relative reading re-reads the *ambient* object,
    not the endorsed region.
    """
    return tuple(p for p, _ in vertices(coherence_polytope(language, settled),
                                        language.size))


def homothet(reference: Sequence[Q], theta: Q,
             region_vertices: Sequence[Sequence[Q]]) -> tuple[tuple[Q, ...], ...]:
    """The vertices of `q + theta(P - q)`."""
    if not Q(0) < Q(theta) <= Q(1):
        raise ValueError("the core coefficient lies in (0,1]")
    return tuple(tuple(Q(q) + Q(theta) * (Q(v) - Q(q)) for q, v in zip(reference, vertex))
                 for vertex in region_vertices)


def _dot(a: Sequence[Q], b: Sequence[Q]) -> Q:
    return sum((Q(x) * Q(y) for x, y in zip(a, b)), Q(0))


def core_holds(reference: Sequence[Q], theta: Q,
               region_vertices: Sequence[Sequence[Q]],
               rows: Sequence[Constraint],
               equalities: Sequence[Constraint] = ()) -> bool:
    """Is the homothet inside the endorsed region (and the settled hyperplanes)?

    The core is the convex hull of the shrunk vertices and each endorsed row is
    a half-space, so checking the shrunk vertices decides containment.
    """
    for point in homothet(reference, theta, region_vertices):
        if any(_dot(r.coefficients, point) < Q(r.rhs) for r in rows):
            return False
        if any(_dot(e.coefficients, point) != Q(e.rhs) for e in equalities):
            return False
    return True


def ambient_core_holds(language: Language, book: Book,
                       settled: Sequence[SettledFact], reference: Sequence[Q],
                       theta: Q) -> bool:
    equalities = tuple(Constraint("settled:" + f.sentence,
                                  language.indicator(f.sentence), Q(f.value), True)
                       for f in settled)
    return core_holds(reference, theta, ambient_vertices(language.size),
                      endorsement_rows(language, book), equalities)


def relative_core_holds(language: Language, book: Book,
                        settled: Sequence[SettledFact], reference: Sequence[Q],
                        theta: Q) -> bool:
    return core_holds(reference, theta, relative_vertices(language, settled),
                      endorsement_rows(language, book))


# --------------------------------------------------------------------------
# The linear reformulation, the clipping adapter, and the maximal coefficient
# --------------------------------------------------------------------------


def row_minimum(row: Constraint, region_vertices: Sequence[Sequence[Q]]) -> Q:
    return min(_dot(row.coefficients, v) for v in region_vertices)


def row_maximum(row: Constraint, region_vertices: Sequence[Sequence[Q]]) -> Q:
    return max(_dot(row.coefficients, v) for v in region_vertices)


def admissible_rows(theta: Q, region_vertices: Sequence[Sequence[Q]],
                    rows: Sequence[Constraint],
                    base: Sequence[Constraint]) -> tuple[Constraint, ...]:
    """The references admitting the coefficient, as a linear system in `q`."""
    if not Q(0) < Q(theta) <= Q(1):
        raise ValueError("the core coefficient lies in (0,1]")
    system = list(base)
    for row in rows:
        system.append(Constraint(
            "core:" + row.source,
            tuple((Q(1) - Q(theta)) * Q(c) for c in row.coefficients),
            Q(row.rhs) - Q(theta) * row_minimum(row, region_vertices)))
    return tuple(system)


def admissible_reference(language: Language, book: Book,
                         settled: Sequence[SettledFact],
                         theta: Q) -> tuple[Q, ...] | None:
    """A reference admitting the declared coefficient, or `None` if none exists."""
    size = language.size
    system = admissible_rows(theta, relative_vertices(language, settled),
                             endorsement_rows(language, book),
                             coherence_polytope(language, settled))
    best = optimize(system, size, tuple(Q(0) for _ in range(size)), "min")
    return None if best is None else best.point


FORCE_GRANTED = "operative force granted at the declared core minimum"
QUARANTINE = "quarantine of operative force: no reference admits the minimum"


@dataclass(frozen=True)
class Admission:
    """The clipping adapter's verdict at one date, with its declared consequence."""

    core_minimum: Q
    reference: tuple[Q, ...] | None
    date: int | None = None

    @property
    def admitted(self) -> bool:
        return self.reference is not None

    @property
    def consequence(self) -> str:
        return FORCE_GRANTED if self.admitted else QUARANTINE


def clipping_adapter(language: Language, book: Book, settled: Sequence[SettledFact],
                     core_minimum: Q, date: int | None = None) -> Admission:
    return Admission(Q(core_minimum),
                     admissible_reference(language, book, settled, core_minimum), date)


def single_row_coefficient(minimum: Q, rhs: Q, maximum: Q) -> Q:
    """Closed form for one endorsed row: `(M - r) / (M - m)`."""
    minimum, rhs, maximum = Q(minimum), Q(rhs), Q(maximum)
    if maximum < rhs:
        return Q(0)
    if maximum == minimum:
        return Q(1)
    return min(Q(1), (maximum - rhs) / (maximum - minimum))


def coefficient_upper_bound(region_vertices: Sequence[Sequence[Q]],
                            rows: Sequence[Constraint]) -> Q:
    """The per-row minimum: an exact upper bound, attained when one row binds."""
    if not rows:
        return Q(1)
    return min(single_row_coefficient(row_minimum(r, region_vertices), Q(r.rhs),
                                      row_maximum(r, region_vertices)) for r in rows)


@dataclass(frozen=True)
class CoefficientBound:
    working: Q
    failing: Q | None
    witness: tuple[Q, ...] | None
    upper_bound: Q
    exact: bool


def max_coefficient(language: Language, book: Book, settled: Sequence[SettledFact],
                    denominator: int = 720) -> CoefficientBound:
    """Bracket the maximal satisfiable coefficient exactly over a stated grid.

    Satisfiability is monotone -- a reference admitting a coefficient admits
    every smaller one, since the smaller homothet is a convex combination of the
    reference and the larger homothet, both inside the region -- so bisection is
    sound and both endpoints are verified by recomputation.
    """
    if denominator <= 0:
        raise ValueError("the grid denominator is positive")
    rows = endorsement_rows(language, book)
    region = relative_vertices(language, settled)
    bound = coefficient_upper_bound(region, rows)
    if not region:
        return CoefficientBound(Q(0), None, None, bound, False)
    if not rows:
        return CoefficientBound(Q(1), None,
                                admissible_reference(language, book, settled, Q(1)),
                                Q(1), True)
    if bound == 0:
        return CoefficientBound(Q(0), None, None, Q(0), True)
    admits = lambda t: admissible_reference(language, book, settled, t) is not None
    if admits(bound):
        return CoefficientBound(bound, None,
                                admissible_reference(language, book, settled, bound),
                                bound, True)
    step = Q(1, denominator)
    if not admits(step):
        return CoefficientBound(Q(0), step, None, bound, False)
    low, high = 1, denominator
    while high - low > 1:
        mid = (low + high) // 2
        if admits(mid * step):
            low = mid
        else:
            high = mid
    working = low * step
    return CoefficientBound(working, high * step,
                            admissible_reference(language, book, settled, working),
                            bound, False)


# --------------------------------------------------------------------------
# Transport
# --------------------------------------------------------------------------


def confirmed_by(language: Language, reference: Sequence[Q],
                 fact: SettledFact) -> bool:
    """Does the incumbent reference already assign the settled value?

    This is the sense of independence the transport lemma needs, and it is
    checkable. A settlement the incumbent contradicts is correlated with the
    endorsed content through the reference they jointly determine.
    """
    return _dot(language.indicator(fact.sentence), reference) == Q(fact.value)


def transport(language: Language, book: Book, settled: Sequence[SettledFact],
              reference: Sequence[Q], theta: Q, fact: SettledFact) -> bool:
    """Settlement commutes with the relative core across a confirmed settlement."""
    if not confirmed_by(language, reference, fact):
        raise ValueError("the transport lemma is stated for confirmed settlements")
    if not relative_core_holds(language, book, settled, reference, theta):
        raise ValueError("the lemma assumes the core condition before the settlement")
    return relative_core_holds(language, book, tuple(settled) + (fact,), reference,
                               theta)


@dataclass(frozen=True)
class Trajectory:
    stages: tuple[tuple[str, Q], ...]
    coefficients: tuple[Q, ...]
    minimum: Q
    survives: bool
    declared_minimum: Q


def accumulate(language: Language, book: Book, facts: Sequence[SettledFact],
               declared_minimum: Q, denominator: int = 720) -> Trajectory:
    """The maximal coefficient along a finite settlement trajectory.

    The reported minimum is over the *searched* trajectory. Nothing here is an
    asymptotic claim.
    """
    settled: list[SettledFact] = []
    coefficients = [max_coefficient(language, book, settled, denominator).working]
    stages: list[tuple[str, Q]] = []
    for fact in facts:
        settled.append(fact)
        stages.append((fact.sentence, Q(fact.value)))
        coefficients.append(max_coefficient(language, book, settled, denominator).working)
    smallest = min(coefficients)
    return Trajectory(tuple(stages), tuple(coefficients), smallest,
                      smallest >= Q(declared_minimum), Q(declared_minimum))


# --------------------------------------------------------------------------
# Displayed witnesses
# --------------------------------------------------------------------------


def ambient_voids_two_sentence() -> Mapping[str, object]:
    """Two worlds, two sentences, one settlement: no positive coefficient survives."""
    language = Language(("w1", "w2"), {"A": ("w1",), "B": ("w2",)})
    book = Book(1, ())
    settled = (SettledFact("A", Q(1, 2)),)
    reference = (Q(1, 2), Q(1, 2))
    coefficients = (Q(1, 2), Q(1, 10), Q(1, 100), Q(1, 1000))
    return {"language": language, "book": book, "settled": settled,
            "reference": reference,
            "ambient": tuple((c, ambient_core_holds(language, book, settled,
                                                    reference, c))
                             for c in coefficients),
            "relative": tuple((c, relative_core_holds(language, book, settled,
                                                      reference, c))
                              for c in coefficients)}


def ambient_voids_nondegenerate() -> Mapping[str, object]:
    """The same voiding where the post-settlement region is a segment, not a point."""
    language = Language(("w1", "w2", "w3"), {"A": ("w1", "w2"), "B": ("w2",)})
    book = Book(1, ())
    settled = (SettledFact("A", Q(1, 2)),)
    reference = (Q(1, 4), Q(1, 4), Q(1, 2))
    coefficients = (Q(1, 2), Q(1, 10), Q(1, 1000))
    return {"language": language, "book": book, "settled": settled,
            "reference": reference,
            "ambient": tuple((c, ambient_core_holds(language, book, settled,
                                                    reference, c))
                             for c in coefficients),
            "relative": tuple((c, relative_core_holds(language, book, settled,
                                                      reference, c))
                              for c in coefficients)}


def dependent_settlement() -> Mapping[str, object]:
    """A settlement the reference contradicts destroys a core a confirmed one keeps."""
    language = Language(("w1", "w2", "w3"),
                        {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
    book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),))
    return {"language": language, "book": book, "reference": (Q(1), Q(0), Q(0)),
            "dependent": SettledFact("B", Q(1, 2)),
            "confirmed": SettledFact("B", Q(0))}


def sweep(denominator: int = 720) -> Mapping[str, object]:
    """Exact-rational sweep over small instances, classifying every settlement."""
    language = Language(("w1", "w2", "w3"),
                        {"A": ("w1",), "B": ("w2",), "C": ("w3",), "AB": ("w1", "w2")})
    rows = (("e:A>=1/2", (Q(1), Q(0), Q(0)), Q(1, 2)),
            ("e:A>=1/4", (Q(1), Q(0), Q(0)), Q(1, 4)),
            ("e:AB>=1/2", (Q(1), Q(1), Q(0)), Q(1, 2)),
            ("e:AB>=3/4", (Q(1), Q(1), Q(0)), Q(3, 4)))
    facts = tuple(SettledFact(s, v) for s in ("A", "B", "C")
                  for v in (Q(0), Q(1, 4), Q(1, 2)))
    confirmed_total = confirmed_transport = dependent_total = 0
    collapsed: list[tuple[str, str, Q]] = []
    reduced: list[tuple[str, str, Q, Q, Q]] = []
    for name, coefficients, rhs in rows:
        book = Book(1, (Endorsement(name, coefficients, rhs),))
        before = max_coefficient(language, book, (), denominator)
        if before.working == 0 or before.witness is None:
            continue
        reference, theta = before.witness, before.working
        for fact in facts:
            if not relative_vertices(language, (fact,)):
                continue
            after = max_coefficient(language, book, (fact,), denominator)
            if confirmed_by(language, reference, fact):
                confirmed_total += 1
                if transport(language, book, (), reference, theta, fact):
                    confirmed_transport += 1
            else:
                dependent_total += 1
                if after.working == 0:
                    collapsed.append((name, fact.sentence, Q(fact.value)))
                elif after.working < theta:
                    reduced.append((name, fact.sentence, Q(fact.value), theta,
                                    after.working))
    return {"confirmed_total": confirmed_total,
            "confirmed_transport": confirmed_transport,
            "dependent_total": dependent_total,
            "collapsed": tuple(collapsed), "reduced": tuple(reduced)}
