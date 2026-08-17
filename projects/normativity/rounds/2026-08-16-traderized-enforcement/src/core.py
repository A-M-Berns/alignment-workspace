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
    rows = [[columns[j][i] for j in range(len(names))] for i in range(len(worlds))]
    target = [Fraction(x) for x in coefficient]
    # Solve the (possibly overdetermined) system exactly by trying square
    # subsystems and verifying the candidate against every row.
    from itertools import combinations
    if len(names) > len(worlds):
        picks = [tuple(range(len(worlds)))]
    else:
        picks = list(combinations(range(len(worlds)), len(names)))
    for pick in picks:
        solution = _solve([rows[i] for i in pick], [target[i] for i in pick])
        if solution is None:
            continue
        if all(sum((solution[j] * rows[i][j] for j in range(len(names))), ZERO)
               == target[i] for i in range(len(worlds))):
            return tuple(solution)
    return None


def core_row_in_credal_space(coefficient: Sequence[Fraction], rhs: Fraction,
                             theta: Fraction,
                             worlds: Sequence[Sequence[Fraction]]) -> tuple[Vector, Fraction]:
    """The admissible-reference row for one endorsement at coefficient `theta`.

    The endorsement is `<c, q> >= r`; the post-settlement simplex has the point
    masses on plausible worlds as its vertices, so the minimum of `<c, .>` over
    it is the minimum over those worlds. The admissible references are then

        (1 - theta) <c, q>  >=  r - theta * m ,     m = min_w <c, w> .
    """
    c = tuple(Fraction(x) for x in coefficient)
    theta = Fraction(theta)
    if not (ZERO < theta <= ONE):
        raise ValueError("theta lies in (0, 1]")
    minimum = min(dot(c, w) for w in worlds)
    return c, (Fraction(rhs) - theta * minimum)


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
    if scale == 0:                       # theta = 1: the row is on the minimum
        return Row(tuple(ZERO for _ in a), ZERO) if right <= 0 else Row(a, right)
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
    return all((ONE - theta) * endorsed + theta * dot(c, w) >= Fraction(rhs)
               for w in worlds)


def maximal_theta(coefficient: Sequence[Fraction], rhs: Fraction,
                  worlds: Sequence[Sequence[Fraction]]) -> Fraction | None:
    """The single-row closed form `(M - r) / (M - m)` from the interface.

    `None` when the row is constant on the simplex, in which case every
    coefficient works; the value is `0` when no reference supports any positive
    coefficient at all.
    """
    c = tuple(Fraction(x) for x in coefficient)
    values = [dot(c, w) for w in worlds]
    lo, hi = min(values), max(values)
    if hi == lo:
        return None
    if hi < Fraction(rhs):
        return ZERO
    return (hi - Fraction(rhs)) / (hi - lo)
