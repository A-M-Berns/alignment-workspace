"""The core condition, compiled to a trader.

The settlement interface's enforcement clause does not ask that a credal state
lie in the endorsed region. It asks that the reference be *deep* in it: writing
`P` for the post-settlement simplex and `S` for the endorsed region inside it,

    q + theta (P - q)  contained in  S .

That is a stronger demand than membership, and it is the demand the round's first
pass did not reach. It is reachable, because the settlement interface already
proves the set of admissible references is a polytope with one explicit rational
row per endorsement — and a rational row is exactly what the constraint-to-trade
compiler consumes.

This module carries the bridge from an endorsement plus a declared coefficient to
a row a trader can be compiled from, and the one condition that bridge needs:
the endorsement must be **priceable**, meaning its coefficient vector over worlds
is a combination of the indicators of sentences the market actually prices. An
endorsement that is not a functional of priced sentence values names a constraint
no trade can express, whatever mechanism is used.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from deduction import _solve
from enforcement import Row
from market import ONE, ZERO, Fragment, Vector, dot


def indicator(fragment: Fragment, name: str,
              worlds: Sequence[Sequence[Fraction]]) -> Vector:
    """A priced sentence's `0/1` vector over the plausible worlds."""
    index = fragment.index(name)
    return tuple(w[index] for w in worlds)


def priceable_coefficients(coefficient: Sequence[Fraction],
                           fragment: Fragment,
                           worlds: Sequence[Sequence[Fraction]]
                           ) -> Vector | None:
    """Write an endorsement's world-coefficient vector in priced sentences.

    Returns `a` with `coefficient = sum_s a_s * indicator(s)` over the plausible
    worlds, or `None` when no such combination exists. In the second case the
    endorsement is unpriceable: its value is not determined by what the market
    displays, so no trading strategy can respond to a violation of it.
    """
    names = fragment.names
    columns = [indicator(fragment, s, worlds) for s in names]
    matrix = [[columns[j][i] for j in range(len(names))] + [Fraction(coefficient[i])]
              for i in range(len(worlds))]
    return _particular_solution(matrix, len(names))


def _particular_solution(augmented: list[list[Fraction]],
                         unknowns: int) -> Vector | None:
    """Exact Gauss-Jordan on an augmented system; any particular solution.

    Rank deficiency is ordinary here — settlement shrinks the world list, and
    several priced sentences can agree on the surviving worlds — so the solver
    must return a solution when the system is consistent and underdetermined,
    and `None` only when it is genuinely inconsistent. Free variables are set to
    zero.
    """
    rows = [row[:] for row in augmented]
    pivots: list[int] = []
    row_index = 0
    for column in range(unknowns):
        pivot = next((r for r in range(row_index, len(rows)) if rows[r][column] != 0),
                     None)
        if pivot is None:
            continue
        rows[row_index], rows[pivot] = rows[pivot], rows[row_index]
        inverse = ONE / rows[row_index][column]
        rows[row_index] = [x * inverse for x in rows[row_index]]
        for r in range(len(rows)):
            if r != row_index and rows[r][column] != 0:
                factor = rows[r][column]
                rows[r] = [x - factor * y for x, y in zip(rows[r], rows[row_index])]
        pivots.append(column)
        row_index += 1
        if row_index == len(rows):
            break
    for r in range(row_index, len(rows)):
        if all(x == 0 for x in rows[r][:unknowns]) and rows[r][unknowns] != 0:
            return None                      # inconsistent
    solution = [ZERO] * unknowns
    for r, column in enumerate(pivots):
        solution[column] = rows[r][unknowns]
    return tuple(solution)


def core_row_in_credal_space(coefficient: Sequence[Fraction], rhs: Fraction,
                             theta: Fraction,
                             worlds: Sequence[Sequence[Fraction]]) -> tuple[Vector, Fraction]:
    """The admissible-reference row for one endorsement at coefficient `theta`.

    The endorsement is `<c, q> >= r` with `c` indexed by **worlds**. The
    post-settlement simplex has the point masses as its vertices, and the value at
    a point mass is `<c, delta_w> = c_w`, so the minimum over the simplex is the
    minimum *entry* of `c` — not a dot product against a world's sentence vector,
    which is a different space. The admissible references are then

        (1 - theta) <c, q>  >=  r - theta * m ,     m = min_w c_w .
    """
    c = tuple(Fraction(x) for x in coefficient)
    theta = Fraction(theta)
    if not (ZERO < theta <= ONE):
        raise ValueError("theta lies in (0, 1]")
    if len(c) != len(worlds):
        raise ValueError("the endorsement is indexed by worlds")
    return c, (Fraction(rhs) - theta * min(c))


def compile_core_row(coefficient: Sequence[Fraction], rhs: Fraction,
                     theta: Fraction, fragment: Fragment,
                     worlds: Sequence[Sequence[Fraction]]) -> Row:
    """An endorsement plus a core minimum, compiled to a row over priced prices.

    Raises when the endorsement is unpriceable, which is the honest failure: the
    compiler declines rather than enforcing something else.
    """
    a = priceable_coefficients(coefficient, fragment, worlds)
    if a is None:
        raise ValueError("endorsement is not priceable in this fragment")
    _, right = core_row_in_credal_space(coefficient, rhs, theta, worlds)
    scale = ONE - Fraction(theta)
    if scale == 0:
        # theta = 1 collapses the condition to `0 >= r - m`. Satisfied by every
        # reference when `r <= m`, and satisfied by none when `r > m` — which is
        # an infeasible request, not a price row. Declining is the feasibility
        # adapter's business and the compiler must not manufacture a satisfiable
        # row out of an unsatisfiable condition.
        if right <= 0:
            return Row(tuple(ZERO for _ in a), ZERO)
        raise ValueError("the core condition is unsatisfiable at this coefficient")
    return Row(tuple(scale * x for x in a), right)


def satisfies_core_condition(price: Sequence[Fraction],
                             priced: Sequence[Fraction],
                             coefficient: Sequence[Fraction], rhs: Fraction,
                             theta: Fraction,
                             worlds: Sequence[Sequence[Fraction]]) -> bool:
    """Check `q + theta (P - q) subset S` from the vertices, in price coordinates.

    The homothet is the convex hull of the shrunk vertices and the endorsed
    region is an intersection of half-spaces, so containment holds exactly when
    every shrunk vertex satisfies the endorsement. At the shrunk vertex the
    endorsement's value is `(1 - theta) <c, q> + theta <c, w>`, and priceability
    is what lets the first term be read off the displayed price as
    `<priced, price>` — a credal state's coordinates are worlds, the market's are
    sentences, and this is the only place the two meet.

    This walks every vertex; the compiled row is the minimum over them, so a test
    comparing the two checks the compilation rather than restating it.
    """
    theta = Fraction(theta)
    endorsed = dot(tuple(Fraction(x) for x in priced),
                   tuple(Fraction(x) for x in price))
    c = tuple(Fraction(x) for x in coefficient)
    return all((ONE - theta) * endorsed + theta * value >= Fraction(rhs)
               for value in c)


def maximal_theta(coefficient: Sequence[Fraction], rhs: Fraction,
                  worlds: Sequence[Sequence[Fraction]]) -> Fraction | None:
    """The single-row closed form `(M - r) / (M - m)` from the interface.

    `None` when the row is constant on the simplex, in which case every
    coefficient works; the value is `0` when no reference supports any positive
    coefficient at all.
    """
    c = tuple(Fraction(x) for x in coefficient)
    if len(c) != len(worlds):
        raise ValueError("the endorsement is indexed by worlds")
    lo, hi = min(c), max(c)
    if hi < Fraction(rhs):
        return ZERO                      # no reference supports any coefficient
    if hi == lo:
        return None                      # constant and satisfied: every theta works
    return (hi - Fraction(rhs)) / (hi - lo)
