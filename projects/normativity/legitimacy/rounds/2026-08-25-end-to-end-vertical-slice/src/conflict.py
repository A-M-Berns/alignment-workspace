"""Feasibility of a rational row system, with the certificate carrying provenance.

Fourier-Motzkin elimination over the rationals, in the same representation the
repository's Lean `FourierMotzkin.feasible` uses — a constraint is a rational
coefficient list and a constant, read as `sum_i a_i x_i <= b` — with one
addition: every constraint carries the nonnegative multiples of the original
constraints it was built from.

That addition is the whole point. Elimination combines two constraints by a
positive multiple of each, so the multipliers compose linearly, and a derived
`0 <= b` with `b < 0` arrives holding exactly the Farkas certificate

    lambda >= 0 ,  sum_j lambda_j a_j = 0 ,  sum_j lambda_j b_j < 0

whose support names the original rows. Since a compiled row carries its
standing and inequality index, an empty region reports which injunction terms
are jointly responsible, and `certify` recomputes the two identities exactly
rather than trusting the elimination that produced them.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Mapping, Optional, Sequence

ZERO = Fraction(0)


class EliminationBudget(Exception):
    """The elimination exceeded its constraint cap.

    Raised rather than answered, because Fourier-Motzkin's growth is real and a
    procedure that quietly dropped constraints would report feasible on a system
    it had stopped examining.
    """


@dataclass(frozen=True)
class LinCon:
    """`sum_i a_i x_i <= b`, with the multiplier map that derived it."""

    a: tuple
    b: Fraction
    lam: tuple                        # tuple[(tag, Fraction), ...], nonnegative

    def multipliers(self) -> dict:
        out: dict = {}
        for tag, m in self.lam:
            out[tag] = out.get(tag, ZERO) + Fraction(m)
        return {t: m for t, m in out.items() if m != ZERO}


def _combine(p: LinCon, q: LinCon, k: int) -> LinCon:
    """Eliminate `x_k` between a positive and a negative coefficient."""
    sp, sq = Fraction(1, 1) / p.a[k], Fraction(1, 1) / (-q.a[k])
    a = tuple(sp * x + sq * y for x, y in zip(p.a, q.a))
    return LinCon(a, sp * p.b + sq * q.b,
                  tuple((t, m * sp) for t, m in p.lam)
                  + tuple((t, m * sq) for t, m in q.lam))


@dataclass(frozen=True)
class Infeasible:
    """A Farkas certificate: nonnegative multipliers summing the rows to absurdity."""

    multipliers: dict                 # tag -> Fraction, all positive
    residual: Fraction                # sum_j lambda_j b_j, strictly negative

    def sources(self) -> tuple:
        return tuple(sorted(self.multipliers, key=repr))

    def __repr__(self) -> str:
        terms = " + ".join(f"{m}*{t}" for t, m in
                           sorted(self.multipliers.items(), key=lambda kv: repr(kv[0])))
        return f"Infeasible({terms} gives 0 <= {self.residual})"


def certify(constraints: Sequence[LinCon], cert: Infeasible,
            dimension: int) -> bool:
    """Recheck a certificate against the original system, exactly.

    Two identities: the multiplied coefficient vectors cancel, and the
    multiplied constants are negative. Nothing about how the certificate was
    found is trusted.
    """
    by_tag: dict = {}
    for c in constraints:
        tags = c.multipliers()
        if len(tags) != 1:
            return False
        tag = next(iter(tags))
        if tags[tag] != 1 or tag in by_tag:
            return False
        by_tag[tag] = c
    total_a = [ZERO] * dimension
    total_b = ZERO
    for tag, m in cert.multipliers.items():
        if m <= ZERO or tag not in by_tag:
            return False
        c = by_tag[tag]
        for i in range(dimension):
            total_a[i] += m * c.a[i]
        total_b += m * c.b
    return all(x == ZERO for x in total_a) and total_b < ZERO \
        and total_b == cert.residual


def feasible(constraints: Sequence[LinCon], dimension: int,
             cap: int = 4000):
    """Decide real solvability; return `None` when feasible, else a certificate.

    The elimination order is by fewest products first, which keeps the small
    systems this round builds well inside the cap.
    """
    live = [LinCon(tuple(c.a) + (ZERO,) * (dimension - len(c.a)),
                   Fraction(c.b), c.lam) for c in constraints]
    remaining = list(range(dimension))
    while remaining:
        def cost(k: int) -> int:
            pos = sum(1 for c in live if c.a[k] > 0)
            neg = sum(1 for c in live if c.a[k] < 0)
            return pos * neg - pos - neg
        k = min(remaining, key=cost)
        remaining.remove(k)
        pos = [c for c in live if c.a[k] > 0]
        neg = [c for c in live if c.a[k] < 0]
        nxt = [c for c in live if c.a[k] == 0]
        for p in pos:
            for q in neg:
                nxt.append(_combine(p, q, k))
                if len(nxt) > cap:
                    raise EliminationBudget(
                        f"more than {cap} constraints while eliminating "
                        f"coordinate {k}")
        live = nxt
    for c in live:
        if c.b < ZERO:
            return Infeasible(c.multipliers(), c.b)
    return None


# ---------------------------------------------------- the system to decide


def decide(constraints: Sequence[LinCon], dimension: int,
           cap: int = 40000):
    """Feasibility of a *bounded* system; a certificate when it is empty.

    Two steps, because the two answers want different work. Nonemptiness is
    settled by looking for a basic feasible solution: every system decided in
    this round sits inside a bounded box — the price systems inside the cube,
    the weight systems inside the simplex — and a nonempty compact polyhedron
    has an extreme point, which is the intersection of `dimension` linearly
    independent active constraints. Enumerating those subsets answers "nonempty"
    in one pass and never grows the constraint list.

    Only when that finds nothing is the elimination run, and then it is run for
    its by-product rather than its verdict: the multiplier map on the derived
    contradiction is the Farkas certificate, and the certificate is what carries
    provenance back to an injunction term.

    Callers wanting a certificate for a system that may be unbounded should call
    `feasible` directly.
    """
    from geometry import polytope_vertices

    if polytope_vertices(constraints, dimension):
        return None
    return feasible(constraints, dimension, cap=cap)


def cube_constraints(dimension: int) -> list:
    """`0 <= p_i <= 1` for every coordinate, tagged as the cube.

    Present in every system decided here, because a price region that is
    nonempty only outside the cube is empty as a region of credences, and the
    schedule type on the other side asks for vertices in the cube.
    """
    out = []
    for i in range(dimension):
        upper = [ZERO] * dimension
        upper[i] = Fraction(1)
        out.append(LinCon(tuple(upper), Fraction(1), ((("cube", "<=1", i), Fraction(1)),)))
        lower = [ZERO] * dimension
        lower[i] = Fraction(-1)
        out.append(LinCon(tuple(lower), ZERO, ((("cube", ">=0", i), Fraction(1)),)))
    return out


def from_rows(rows: Iterable, dimension: int) -> list:
    """Compiled rows `c . p >= r` as `(-c) . p <= -r`, tagged by provenance."""
    out = []
    for row in rows:
        tag = (row.standing_id, row.injunction_id, row.index)
        out.append(LinCon(tuple(-Fraction(c) for c in row.coefficients),
                          -Fraction(row.rhs), ((tag, Fraction(1)),)))
    return out


def hull_system(rows: Iterable, vertices: Sequence) -> tuple:
    """The system deciding `conv(vertices) ∩ {rows}` in barycentric coordinates.

    The deductive region arrives as a vertex list, and turning a vertex list
    into rows is the facet enumeration the repository deliberately does not
    perform. So the composition is decided in the weights instead: a point of
    the hull is `sum_v lambda_v v` with `lambda >= 0` and `sum lambda_v = 1`,
    and each compiled row becomes one linear constraint on `lambda`. The system
    is feasible exactly when the two regions meet, and a Farkas certificate over
    it names the same injunction terms as one over the price system, because the
    row tags are carried through unchanged.

    Returns `(constraints, dimension)`, ready for `feasible`.
    """
    verts = [tuple(Fraction(x) for x in v) for v in vertices]
    m = len(verts)
    out: list = []
    for j, _ in enumerate(verts):
        e = [ZERO] * m
        e[j] = Fraction(-1)
        out.append(LinCon(tuple(e), ZERO,
                          ((("hull", "weight>=0", j), Fraction(1)),)))
    ones = tuple(Fraction(1) for _ in range(m))
    out.append(LinCon(ones, Fraction(1), ((("hull", "sum<=1"), Fraction(1)),)))
    out.append(LinCon(tuple(-x for x in ones), Fraction(-1),
                      ((("hull", "sum>=1"), Fraction(1)),)))
    for row in rows:
        tag = (row.standing_id, row.injunction_id, row.index)
        coeffs = tuple(
            -sum((Fraction(c) * v[i] for i, c in enumerate(row.coefficients)),
                 ZERO)
            for v in verts)
        out.append(LinCon(coeffs, -Fraction(row.rhs), ((tag, Fraction(1)),)))
    return out, m
