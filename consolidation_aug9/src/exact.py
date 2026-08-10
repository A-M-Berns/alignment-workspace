"""Exact rational linear algebra and linear programming over finite polytopes.

Folder-local and self-contained: nothing here imports from any repository. All
arithmetic is exact rationals; there is no floating point anywhere in this
package.

The single algorithmic primitive is **vertex enumeration**. Every polyhedron in
this monograph is described by finitely many rational half-spaces and equalities
in a finite-dimensional space, and every one of them is pointed -- each carries
either the probability simplex (bounding all coordinates) or an explicit
nonnegativity row on the one free variable. A linear objective bounded on a
pointed polyhedron attains its optimum at a vertex, so enumerating the solutions
of every square subsystem and keeping the feasible ones decides feasibility and
optimality exactly.

Complexity is irrelevant here and correctness is not: every instance displayed
in this package has at most four coordinates and at most a dozen rows.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations
from typing import Sequence


@dataclass(frozen=True)
class Constraint:
    """`coefficients . x >= rhs`, or `== rhs` when `equality` is set.

    `source` is a stable label used to report which rows are active at an
    optimum and to name the rows a certificate combines.
    """

    source: str
    coefficients: tuple[Q, ...]
    rhs: Q
    equality: bool = False

    def value_at(self, point: Sequence[Q]) -> Q:
        return sum((Q(a) * Q(b) for a, b in zip(self.coefficients, point)), Q(0))

    def satisfied_by(self, point: Sequence[Q]) -> bool:
        value = self.value_at(point)
        return value == Q(self.rhs) if self.equality else value >= Q(self.rhs)

    def tight_at(self, point: Sequence[Q]) -> bool:
        return self.value_at(point) == Q(self.rhs)


def solve_square(matrix: Sequence[Sequence[Q]], values: Sequence[Q]) -> tuple[Q, ...] | None:
    """Exact Gaussian elimination; `None` when the system is singular.

    Partial pivoting is by first nonzero rather than by magnitude, which is
    sound because the arithmetic is exact and no rounding error accumulates.
    """
    size = len(values)
    if any(len(row) != size for row in matrix):
        return None
    rows = [[Q(c) for c in row] + [Q(v)] for row, v in zip(matrix, values)]
    for column in range(size):
        pivot = next((r for r in range(column, size) if rows[r][column] != 0), None)
        if pivot is None:
            return None
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [entry / scale for entry in rows[column]]
        for other in range(size):
            if other == column or rows[other][column] == 0:
                continue
            factor = rows[other][column]
            rows[other] = [a - factor * b for a, b in zip(rows[other], rows[column])]
    return tuple(row[size] for row in rows)


def vertices(constraints: Sequence[Constraint], dimension: int,
             ) -> tuple[tuple[tuple[Q, ...], tuple[str, ...]], ...]:
    """Every vertex of the described polyhedron, with its active row labels."""
    found: dict[tuple[Q, ...], tuple[str, ...]] = {}
    for subset in combinations(range(len(constraints)), dimension):
        solution = solve_square(
            [list(constraints[i].coefficients) for i in subset],
            [constraints[i].rhs for i in subset])
        if solution is None:
            continue
        point = tuple(solution)
        if not all(c.satisfied_by(point) for c in constraints):
            continue
        found.setdefault(point, tuple(sorted(c.source for c in constraints
                                             if c.tight_at(point))))
    return tuple(sorted(found.items()))


@dataclass(frozen=True)
class Optimum:
    value: Q
    point: tuple[Q, ...]
    active: tuple[str, ...]


def optimize(constraints: Sequence[Constraint], dimension: int,
             objective: Sequence[Q], sense: str = "min") -> Optimum | None:
    """Exact optimum over a pointed polyhedron, or `None` when it is empty."""
    if sense not in ("min", "max"):
        raise ValueError("sense must be 'min' or 'max'")
    found = vertices(constraints, dimension)
    if not found:
        return None
    scored = [(sum((a * b for a, b in zip(objective, point)), Q(0)), point, active)
              for point, active in found]
    value, point, active = (min if sense == "min" else max)(scored, key=lambda t: t[0])
    return Optimum(value, tuple(point), tuple(active))


def feasible(constraints: Sequence[Constraint], dimension: int) -> bool:
    return bool(vertices(constraints, dimension))


def dual_weights(rows: Sequence[Constraint], dimension: int,
                 objective: Sequence[Q]) -> tuple[tuple[str, Q], ...] | None:
    """Nonnegative weights on the given rows reproducing the objective.

    Used to read a certificate off an optimal active set. Whatever this returns
    is verified independently by recomputation before it is believed, so a
    failure of the search is a missing certificate and never a false one.
    """
    target = [Q(v) for v in objective]
    for subset in combinations(range(len(rows)), min(dimension, len(rows))):
        matrix = [[rows[i].coefficients[column] for i in subset]
                  for column in range(dimension)]
        solution = solve_square(matrix, target)
        if solution is None:
            continue
        if any(value < 0 for value, i in zip(solution, subset) if not rows[i].equality):
            continue
        reproduced = all(
            sum((w * rows[i].coefficients[column] for w, i in zip(solution, subset)),
                Q(0)) == target[column]
            for column in range(dimension))
        if reproduced:
            return tuple((rows[i].source, w) for w, i in zip(solution, subset))
    return None
