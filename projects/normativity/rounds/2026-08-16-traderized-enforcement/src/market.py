"""Finite priced fragment, worlds, and the market maker's contract.

Exact rationals throughout. A price vector is a tuple of `Fraction` in `[0,1]`
indexed by position in a fixed priced fragment; a world restricted to that
fragment is a tuple of `Fraction` in `{0,1}`, so worlds are the vertices of the
cube the prices live in and both can be fed to the same inner products.

The one object doing real work here is `max_gain`. Logical Induction's market
maker (arXiv:1609.03543, `defprop:markemaker`) returns a belief state satisfying
`W(T_n(p)) <= 2^-n` for *every* world `W`, and a day-`n` strategy's cash term
makes its value at the prevailing prices zero. So the contract is a statement
about one number: the largest value the realised holdings take over the cube.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Iterable, Sequence

Vector = tuple[Fraction, ...]

ZERO = Fraction(0)
ONE = Fraction(1)


def vec(*entries: object) -> Vector:
    """A rational vector from ints, strings, pairs or Fractions."""
    return tuple(Fraction(e) if not isinstance(e, tuple) else Fraction(*e)
                 for e in entries)


def dot(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    if len(u) != len(v):
        raise ValueError("dimension mismatch")
    return sum((a * b for a, b in zip(u, v)), ZERO)


def scale(a: Fraction, u: Sequence[Fraction]) -> Vector:
    return tuple(a * x for x in u)


def add(u: Sequence[Fraction], v: Sequence[Fraction]) -> Vector:
    if len(u) != len(v):
        raise ValueError("dimension mismatch")
    return tuple(a + b for a, b in zip(u, v))


def sub(u: Sequence[Fraction], v: Sequence[Fraction]) -> Vector:
    return add(u, scale(Fraction(-1), v))


def l1(u: Sequence[Fraction]) -> Fraction:
    return sum((abs(x) for x in u), ZERO)


def in_cube(p: Sequence[Fraction]) -> bool:
    return all(ZERO <= x <= ONE for x in p)


def cube_vertices(dimension: int) -> list[Vector]:
    """Every `{0,1}` valuation of the priced fragment."""
    return [tuple(Fraction(b) for b in bits)
            for bits in product((0, 1), repeat=dimension)]


# --- the market maker's contract -------------------------------------------

def holdings_value(coefficients: Sequence[Fraction],
                   prices: Sequence[Fraction],
                   world: Sequence[Fraction]) -> Fraction:
    """Value of a day's realised trade in one world.

    A day-`n` strategy is `sum_phi xi_phi * (phi - p_n(phi))`, so its value in a
    world `W` is `sum_phi xi_phi * (W(phi) - p_n(phi))`. The cash term is not a
    free parameter: it is fixed by the coefficients and the prevailing prices.
    """
    return dot(coefficients, sub(world, prices))


def max_gain(coefficients: Sequence[Fraction],
             prices: Sequence[Fraction]) -> Fraction:
    """`max` over all worlds of the realised trade's value.

    Equals `sum_phi [ xi_phi^+ (1 - p_phi) + xi_phi^- p_phi ]`, because the
    maximising world takes `W(phi) = 1` exactly where the coefficient is
    positive. Every summand is nonnegative, so a bound on this number is a
    bound on each coordinate separately — that is the pinning force the fixed
    point supplies.
    """
    total = ZERO
    for xi, p in zip(coefficients, prices):
        if xi > 0:
            total += xi * (ONE - p)
        elif xi < 0:
            total += (-xi) * p
    return total


def min_value(coefficients: Sequence[Fraction],
              prices: Sequence[Fraction]) -> Fraction:
    """`min` over all worlds: the worst-case single-date loss of a position."""
    total = ZERO
    for xi, p in zip(coefficients, prices):
        if xi > 0:
            total += -xi * p          # worst world prices a long at zero
        elif xi < 0:
            total += xi * (ONE - p)   # worst world prices a short at one
    return total


def satisfies_contract(coefficients: Sequence[Fraction],
                       prices: Sequence[Fraction],
                       slack: Fraction) -> bool:
    """The market maker's guarantee at the displayed prices."""
    return max_gain(coefficients, prices) <= slack


# --- deductive stages and plausible worlds ---------------------------------

class Fragment:
    """A finite priced fragment with a propositional-consistency relation.

    `constraints` are the Boolean relations the fragment's sentences stand in —
    each a predicate on a `{0,1}` assignment — so `pc_worlds` can be computed
    without a propositional prover. A fragment carrying `phi` and `not phi`
    supplies the constraint `w[phi] + w[not phi] == 1`.
    """

    def __init__(self, names: Sequence[str],
                 constraints: Iterable = ()) -> None:
        self.names = tuple(names)
        self.constraints = tuple(constraints)

    @property
    def dimension(self) -> int:
        return len(self.names)

    def index(self, name: str) -> int:
        return self.names.index(name)

    def worlds(self) -> list[Vector]:
        """Propositionally consistent `{0,1}` valuations of the fragment."""
        return [w for w in cube_vertices(self.dimension)
                if all(c(w) for c in self.constraints)]

    def pc_worlds(self, settled: dict[str, int]) -> list[Vector]:
        """Worlds propositionally consistent with a deductive stage.

        `settled` is the stage's content restricted to the fragment: the
        sentences the process has emitted, with the truth value emitting them
        forces.
        """
        out = []
        for w in self.worlds():
            if all(w[self.index(name)] == Fraction(v)
                   for name, v in settled.items()):
                out.append(w)
        return out
