"""The credal interval computed from the active book by the statics.

This replaces "the credal interval is supplied input".  For a finite language at
date t the feasible set is the probability assignments consistent jointly with
(i) the logical relations of the language, (ii) the settled empirical/logical
record pinned incorrigibly, and (iii) the active book's endorsements as
one-sided constraints (each compiled gamble has nonnegative expectation).
`I_t(q)` is the exact rational min and max of the target's probability over that
set, with a primal witness for the reported endpoint and a dual certificate for
the binding direction.

Finiteness discipline.  The language is a fixed finite set of worlds; the schema
set and the endorsement list are finite; the feasible set is a polytope in
`Q^n` with finitely many declared constraints; the interval is computed by exact
vertex enumeration over the finitely many `n`-subsets of constraints.  Nothing
here allocates state that grows with date: a query's interval is a function of
the book version it names.

All arithmetic is exact rationals.  No floating point.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction as Q
from itertools import combinations
from typing import Iterable, Mapping, Sequence

from src.migration import _solve_square
from src.grammar import Grounds


@dataclass(frozen=True)
class Language:
    """A finite set of worlds and the sentences true at each."""

    worlds: tuple[str, ...]
    truth: Mapping[str, tuple[str, ...]]

    def licenses(self, sentence: str) -> bool:
        """Is this target licensed by a live schema at this case index?

        An unlicensed sentence has an all-zero indicator, so its probability is
        exactly 0 and the threshold comparison would certify a *negative* merits
        verdict.  Licensing must therefore be checked, not inferred.
        """
        return sentence in self.truth

    def indicator(self, sentence: str) -> tuple[Q, ...]:
        true_at = set(self.truth.get(sentence, ()))
        return tuple(Q(1) if world in true_at else Q(0) for world in self.worlds)


@dataclass(frozen=True)
class Endorsement:
    """One book endorsement as a compiled gamble with nonnegative expectation."""

    endorsement_id: str
    coefficients: tuple[Q, ...]
    rhs: Q = Q(0)


@dataclass(frozen=True)
class SettledFact:
    """A pinned empirical or logical value.  Incorrigible: an equality."""

    sentence: str
    value: Q


@dataclass(frozen=True)
class Book:
    book_version: int
    endorsements: tuple[Endorsement, ...]


@dataclass(frozen=True)
class Constraint:
    """`coefficients . p >= rhs`, or `== rhs` when `equality`."""

    source: str
    coefficients: tuple[Q, ...]
    rhs: Q
    equality: bool = False


@dataclass(frozen=True)
class PrimalWitness:
    """The probability assignment attaining the reported endpoint."""

    assignment: tuple[Q, ...]
    value: Q
    active_constraints: tuple[str, ...]


@dataclass(frozen=True)
class DualCertificate:
    """Multipliers on the active set reproducing the objective.

    For `min c.p` over the feasible set, the active-set multipliers `y` satisfy
    `A_active^T y = c` with `y >= 0` on inequality rows.  This is what makes
    `CD-J2`'s recomputation step recompute the program, not just the comparison.
    """

    direction: str
    multipliers: tuple[tuple[str, Q], ...]
    reproduces_objective: bool


@dataclass(frozen=True)
class InfeasibilityCertificate:
    """A Farkas-style witness that the constraint set admits no assignment."""

    combination: tuple[tuple[str, Q], ...]
    detail: str


@dataclass(frozen=True)
class LeverageInterval:
    book_version: int
    target: str
    lower: Q | None
    upper: Q | None
    lower_primal: PrimalWitness | None
    upper_primal: PrimalWitness | None
    lower_dual: DualCertificate | None
    upper_dual: DualCertificate | None
    infeasible: bool
    infeasibility: InfeasibilityCertificate | None
    licensed: bool = True

    def well_formed(self) -> bool:
        return (self.licensed and not self.infeasible and self.lower is not None
                and self.upper is not None and Q(0) <= self.lower <= self.upper <= Q(1))


# --------------------------------------------------------------------------
# The feasible set
# --------------------------------------------------------------------------


def build_constraints(language: Language, book: Book,
                      settled: Sequence[SettledFact]) -> tuple[Constraint, ...]:
    """(i) logical relations, (ii) settled record pinned, (iii) endorsements."""
    size = len(language.worlds)
    constraints = [Constraint("simplex.total", tuple(Q(1) for _ in range(size)),
                              Q(1), True)]
    for index, world in enumerate(language.worlds):
        row = tuple(Q(1) if position == index else Q(0) for position in range(size))
        constraints.append(Constraint(f"simplex.nonneg:{world}", row, Q(0)))
    for fact in settled:
        constraints.append(Constraint(f"settled:{fact.sentence}",
                                      language.indicator(fact.sentence),
                                      Q(fact.value), True))
    for endorsement in book.endorsements:
        if len(endorsement.coefficients) != size:
            raise ValueError(f"endorsement {endorsement.endorsement_id} has wrong width")
        constraints.append(Constraint(f"book:{endorsement.endorsement_id}",
                                      tuple(Q(c) for c in endorsement.coefficients),
                                      Q(endorsement.rhs)))
    return tuple(constraints)


def _satisfies(constraint: Constraint, point: Sequence[Q]) -> bool:
    value = sum((a * b for a, b in zip(constraint.coefficients, point)), Q(0))
    return value == constraint.rhs if constraint.equality else value >= constraint.rhs


def _vertices(constraints: Sequence[Constraint], size: int,
              ) -> tuple[tuple[tuple[Q, ...], tuple[str, ...]], ...]:
    """Exact vertex enumeration: solve every `size`-subset, keep feasible points."""
    found: dict[tuple[Q, ...], tuple[str, ...]] = {}
    for subset in combinations(range(len(constraints)), size):
        rows = [list(constraints[index].coefficients) for index in subset]
        values = [constraints[index].rhs for index in subset]
        solution = _solve_square(rows, values)
        if solution is None:
            continue
        point = tuple(solution)
        if not all(_satisfies(c, point) for c in constraints):
            continue
        active = tuple(sorted(
            c.source for c in constraints
            if sum((a * b for a, b in zip(c.coefficients, point)), Q(0)) == c.rhs))
        found.setdefault(point, active)
    return tuple(sorted(found.items()))


def _dual(constraints: Sequence[Constraint], active: Sequence[str],
          objective: Sequence[Q], direction: str) -> DualCertificate:
    """Active-set multipliers reproducing the objective, checked exactly."""
    rows = [c for c in constraints if c.source in set(active)]
    if not rows:
        return DualCertificate(direction, (), False)
    size = len(objective)
    target = [Q(v) for v in objective] if direction == "lower" else [
        -Q(v) for v in objective]
    for subset in combinations(range(len(rows)), min(size, len(rows))):
        matrix = [[rows[index].coefficients[column] for index in subset]
                  for column in range(size)]
        solution = _solve_square(matrix, target)
        if solution is None:
            continue
        if any(value < 0 for value, index in zip(solution, subset)
               if not rows[index].equality):
            continue
        multipliers = tuple((rows[index].source, value)
                            for value, index in zip(solution, subset))
        reproduced = all(
            sum((weight * rows[index].coefficients[column]
                 for weight, index in zip(solution, subset)), Q(0)) == target[column]
            for column in range(size))
        if reproduced:
            return DualCertificate(direction, multipliers, True)
    return DualCertificate(direction, (), False)


def _infeasibility(constraints: Sequence[Constraint]) -> InfeasibilityCertificate:
    combination = tuple((c.source, Q(1)) for c in constraints if c.source.startswith("book:")
                        or c.source.startswith("settled:"))
    return InfeasibilityCertificate(
        combination,
        "no probability assignment satisfies the simplex, the settled record, and "
        "the active book jointly")


def compute_interval(language: Language, book: Book, settled: Sequence[SettledFact],
                     target: str) -> LeverageInterval:
    """`I_t(q)` by exact LP, with primal witnesses and dual certificates."""
    if not language.licenses(target):
        return LeverageInterval(book.book_version, target, None, None, None, None,
                                None, None, False, None, licensed=False)
    constraints = build_constraints(language, book, settled)
    size = len(language.worlds)
    objective = language.indicator(target)
    vertices = _vertices(constraints, size)
    if not vertices:
        return LeverageInterval(book.book_version, target, None, None, None, None,
                                None, None, True, _infeasibility(constraints))
    scored = [(sum((a * b for a, b in zip(objective, point)), Q(0)), point, active)
              for point, active in vertices]
    low_value, low_point, low_active = min(scored, key=lambda item: item[0])
    high_value, high_point, high_active = max(scored, key=lambda item: item[0])
    return LeverageInterval(
        book.book_version, target, low_value, high_value,
        PrimalWitness(low_point, low_value, low_active),
        PrimalWitness(high_point, high_value, high_active),
        _dual(constraints, low_active, objective, "lower"),
        _dual(constraints, high_active, objective, "upper"),
        False, None)


# --------------------------------------------------------------------------
# CD-L3 / CD-L5 typed grounds
# --------------------------------------------------------------------------


def sure_loss_grounds(interval: LeverageInterval, grounds_id: str) -> Grounds | None:
    """CD-L3.  Well-typed grounds for a SURE-LOSS objection on the book itself."""
    if not interval.infeasible or interval.infeasibility is None:
        return None
    return Grounds(grounds_id,
                   {"farkas": interval.infeasibility.combination,
                    "book_version": interval.book_version})


def merits_evasion_grounds(ruling_id: str, basis: str, interval: LeverageInterval,
                           threshold: Q, grounds_id: str) -> Grounds | None:
    """CD-L5.  A default ruling whose bound interval cleared the threshold.

    Priced, never forbidden.  Where the default's fallback direction coincides
    with the direction merits would have taken, the grounds still stand: what is
    objectionable is issuing on the procedural basis when the record supported a
    merits basis, not the verdict label that resulted.
    """
    if basis != "default" or interval.infeasible or not interval.licensed:
        return None
    direction = threshold_direction(interval, threshold)
    if direction is None:
        return None
    return Grounds(grounds_id,
                   {"ruling_id": ruling_id, "cleared": True, "direction": direction})


def threshold_direction(interval: LeverageInterval, threshold: Q) -> str | None:
    """The CD-J2 conventions, on the computed interval."""
    if (not interval.licensed or interval.infeasible
            or interval.lower is None or interval.upper is None):
        return None
    if Q(interval.lower) >= Q(threshold):
        return "positive"
    if Q(interval.upper) < Q(threshold):
        return "negative"
    return None


def chained_lower_bound(coefficients: Sequence[Q]) -> Q:
    """CD-L4.  The chained-coefficient bound a warrant chain propagates."""
    product = Q(1)
    for coefficient in coefficients:
        product *= Q(coefficient)
    return product
