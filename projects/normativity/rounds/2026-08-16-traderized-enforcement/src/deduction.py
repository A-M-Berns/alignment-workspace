"""Deduction as a constraint source, and the exploitation witnesses.

The coherence polytope of a deductive stage is the convex hull of the worlds
propositionally consistent with it, restricted to the priced fragment. That is
the set of price vectors some credal state over plausible worlds reproduces —
Logical Induction's limit-coherence target, read at a finite date.

A region presentation is **world-inclusive** at a date when every world
plausible at that date satisfies every row. World-inclusivity is what makes the
enforcement trader's realised position worth something rather than nothing in
each plausible world, and it is checked here rather than assumed.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Sequence

from enforcement import Region, Row
from market import ONE, ZERO, Fragment, Vector, dot, sub


# --- exact convex-hull membership ------------------------------------------

def _solve(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction] | None:
    """Exact Gaussian elimination on a square rational system."""
    n = len(matrix)
    a = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col] != 0), None)
        if pivot is None:
            return None
        a[col], a[pivot] = a[pivot], a[col]
        inv = ONE / a[col][col]
        a[col] = [x * inv for x in a[col]]
        for r in range(n):
            if r != col and a[r][col] != 0:
                factor = a[r][col]
                a[r] = [x - factor * y for x, y in zip(a[r], a[col])]
    return [a[r][n] for r in range(n)]


def in_convex_hull(point: Sequence[Fraction],
                   vertices: Sequence[Sequence[Fraction]]) -> bool:
    """Whether `point` is a convex combination of `vertices`, exactly.

    By Caratheodory it suffices to look at subsets of size at most `d + 1`, so
    this enumerates those subsets and solves the small rational system for each.
    Exact and terminating; the cost is combinatorial in the vertex count, which
    is why the fixtures keep the fragment small.
    """
    d = len(point)
    verts = [tuple(Fraction(x) for x in v) for v in vertices]
    if not verts:
        return False
    for size in range(1, min(d + 1, len(verts)) + 1):
        for subset in combinations(verts, size):
            # rows: one per coordinate, plus the normalisation; solve in the
            # least-squares-free way by picking an independent square subsystem.
            rows = [[v[i] for v in subset] for i in range(d)]
            rows.append([ONE] * size)
            targets = list(point) + [ONE]
            for pick in combinations(range(d + 1), size):
                sub_matrix = [rows[i] for i in pick]
                sub_rhs = [targets[i] for i in pick]
                lam = _solve(sub_matrix, sub_rhs)
                if lam is None or any(x < 0 for x in lam):
                    continue
                if sum(lam, ZERO) != ONE:
                    continue
                if all(sum((l * v[i] for l, v in zip(lam, subset)), ZERO)
                       == point[i] for i in range(d)):
                    return True
    return False


def coherence_membership(point: Sequence[Fraction],
                         fragment: Fragment,
                         settled: dict[str, int]) -> bool:
    """Whether the displayed price is realised by a credal state over the
    worlds still plausible at this stage."""
    return in_convex_hull(point, fragment.pc_worlds(settled))


# --- deduction presented as rows -------------------------------------------

def settled_rows(fragment: Fragment, settled: dict[str, int]) -> list[Row]:
    """The box rows a deductive stage forces on the priced fragment.

    A sentence the process has emitted is priced at one; a sentence whose
    negation it has emitted is priced at zero. Each is a pair of rows, and each
    row touches one coordinate, so the row violation *is* the coordinatewise
    distance to the region — no constant relating the two is needed.
    """
    rows: list[Row] = []
    d = fragment.dimension
    for name, value in settled.items():
        i = fragment.index(name)
        e = [ONE if k == i else ZERO for k in range(d)]
        target = Fraction(value)
        rows.append(Row(e, target))                       # p_i >= target
        rows.append(Row([-x for x in e], -target))        # p_i <= target
    return rows


def relation_rows(fragment: Fragment) -> list[Row]:
    """Rows for the affine relations every plausible world satisfies.

    Found rather than declared: a candidate row with small integer coefficients
    is kept when every propositionally consistent world of the fragment
    satisfies it with equality, so the pair of rows it induces cannot exclude a
    plausible world.
    """
    worlds = fragment.worlds()
    d = fragment.dimension
    rows: list[Row] = []
    from itertools import product as _product
    for c in _product((-1, 0, 1), repeat=d):
        if all(x == 0 for x in c):
            continue
        values = {dot(tuple(Fraction(x) for x in c), w) for w in worlds}
        if len(values) != 1:
            continue
        (r,) = values
        cf = tuple(Fraction(x) for x in c)
        rows.append(Row(cf, r))
        rows.append(Row(tuple(-x for x in cf), -r))
    return rows


def support_rows(fragment: Fragment, settled: dict[str, int],
                 bound: int = 1) -> list[Row]:
    """The support-function presentation over the still-plausible worlds.

    For each integer coefficient vector `c` within `bound`, the row
    `c . x >= min_{W plausible} c . W`. Two things follow from the right-hand
    side being that minimum rather than anything else. Every plausible world
    satisfies every row, so the presentation is world-inclusive without a side
    condition. And the region contains the convex hull of the plausible worlds,
    with equality once the coefficient family is rich enough to carry the hull's
    facet normals.
    """
    worlds = fragment.pc_worlds(settled)
    if not worlds:
        raise ValueError("no plausible world: the stage is inconsistent")
    rows: list[Row] = []
    from itertools import product as _product
    for c in _product(range(-bound, bound + 1), repeat=fragment.dimension):
        if all(x == 0 for x in c):
            continue
        cf = tuple(Fraction(x) for x in c)
        rows.append(Row(cf, min(dot(cf, w) for w in worlds)))
    return rows


def world_deficit(region: Region, world: Sequence[Fraction]
                  ) -> tuple[Fraction, ...]:
    """Per row, how far the region's right-hand side excludes a world.

    Zero on every row exactly when the region contains the world. This is the
    other half of the liability identity: a date costs the enforcement trader
    something only where a live violation and an excluded plausible world meet
    on the same row.
    """
    return tuple(max(ZERO, row.r - dot(row.c, world)) for row in region.rows)


def liability_identity(trader, region: Region, p: Sequence[Fraction],
                       world: Sequence[Fraction]) -> Fraction:
    """`sum_j beta_j g_j(p) [ (c_j . W - r_j) + g_j(p) ]`.

    Exactly the realised enforcement position's value in `W`, rearranged so the
    two sources of sign are visible separately.
    """
    total = ZERO
    for beta, row in zip(trader.betas, region.rows):
        g = row.violation(p)
        if g:
            total += beta * g * ((dot(row.c, world) - row.r) + g)
    return total


def net_rows(worlds: Sequence[Sequence[Fraction]], dimension: int,
             denominator: int) -> list[Row]:
    """The support-function presentation over a rational net of the `l1` ball.

    The settlement interface measures a price's failure by its **incoherence**,
    the least sup-norm deviation from a credal state, and certifies it with a
    signed weight vector of total absolute mass at most one. Duality makes those
    the same object: the incoherence is the largest row violation over all such
    weight vectors. So enforcing a *net* of them is enforcing incoherence, up to
    how fine the net is — and a net too coarse to carry the tight certificate
    reports no violation at all, which `test_contract` displays.
    """
    axis = [Fraction(i, denominator) for i in range(-denominator, denominator + 1)]
    rows: list[Row] = []
    from itertools import product as _product
    for c in _product(axis, repeat=dimension):
        if all(x == 0 for x in c) or sum(abs(x) for x in c) > ONE:
            continue
        rows.append(Row(c, min(dot(c, w) for w in worlds)))
    return rows


def incoherence_upper(price: Sequence[Fraction],
                      worlds: Sequence[Sequence[Fraction]],
                      denominator: int) -> Fraction:
    """An upper bound on the incoherence, from credal states on a rational grid.

    Exact when the minimising credal state is on the grid, which it is for the
    instances used here; a bound and labelled as one otherwise.
    """
    from itertools import product as _product
    best = None
    count = len(worlds)
    for weights in _product(range(denominator + 1), repeat=count):
        if sum(weights) != denominator:
            continue
        lam = [Fraction(x, denominator) for x in weights]
        realised = tuple(sum((l * w[i] for l, w in zip(lam, worlds)), ZERO)
                         for i in range(len(price)))
        deviation = max(abs(a - b) for a, b in zip(price, realised))
        if best is None or deviation < best:
            best = deviation
    return best if best is not None else ZERO


def deductive_region(fragment: Fragment, settled: dict[str, int]) -> Region:
    """The admissible region traderized deduction enforces at one date."""
    return Region(fragment.dimension,
                  settled_rows(fragment, settled) + relation_rows(fragment))


def world_inclusive(region: Region,
                    plausible: Sequence[Sequence[Fraction]]) -> bool:
    """Every world still plausible satisfies every row."""
    return all(region.contains(w) for w in plausible)


def excluded_plausible_worlds(region: Region,
                              plausible: Sequence[Sequence[Fraction]]
                              ) -> list[Vector]:
    return [tuple(w) for w in plausible if not region.contains(w)]


# --- the exploiting ordinary trader ----------------------------------------

def persistent_gap_trader_worth(prices: Sequence[Sequence[Fraction]],
                                coordinate: int,
                                active: Sequence[bool],
                                world: Sequence[Fraction]) -> Fraction:
    """Net worth of the ordinary trader that buys one share on active dates.

    The trader buys a single share of the tracked sentence on each date it has
    verified the sentence settled true, and abstains otherwise. Its net worth in
    a world is the sum over active dates of `W(phi) - p_i(phi)` — which is the
    quantity a persistent one-sided pricing gap makes grow without bound while
    keeping it bounded below.
    """
    total = ZERO
    for p, on in zip(prices, active):
        if on:
            total += world[coordinate] - p[coordinate]
    return total
