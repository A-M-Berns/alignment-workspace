"""Joint Actionability: reason-relative gain under an aggregated intervention.

A reason presents a position `delta` in the displayed coordinates, a displayed
state `p`, and an admissible region `K` given by rational rows on the unit cube.
Its reason-relative gain against a region is the exact minimum

    g(delta, K, p) = min { <delta, v - p> : v in K } ,

computed by vertex enumeration with exact rationals. `K` always carries the cube
rows, so every polytope here is bounded and the minimum is attained.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Sequence

Vector = Sequence[Fraction]
Row = tuple[tuple[Fraction, ...], Fraction]


def _solve(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction] | None:
    """Exact Gaussian elimination; `None` when the system is not uniquely solved."""
    n = len(matrix)
    a = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col] != 0), None)
        if pivot is None:
            return None
        a[col], a[pivot] = a[pivot], a[col]
        scale = a[col][col]
        a[col] = [x / scale for x in a[col]]
        for r in range(n):
            if r != col and a[r][col] != 0:
                factor = a[r][col]
                a[r] = [x - factor * y for x, y in zip(a[r], a[col])]
    return [a[i][n] for i in range(n)]


class Region:
    """`{ v in [0,1]^dim : <a, v> >= b for each declared row }`."""

    def __init__(self, dim: int, rows: Sequence[Row] = ()):
        self.dim = dim
        self.rows: list[Row] = list(rows)

    def all_rows(self) -> list[Row]:
        cube: list[Row] = []
        for i in range(self.dim):
            lower = [Fraction(0)] * self.dim
            lower[i] = Fraction(1)
            cube.append((tuple(lower), Fraction(0)))
            upper = [Fraction(0)] * self.dim
            upper[i] = Fraction(-1)
            cube.append((tuple(upper), Fraction(-1)))
        return list(self.rows) + cube

    def contains(self, v: Vector) -> bool:
        return all(sum((ai * vi for ai, vi in zip(a, v)), Fraction(0)) >= b
                   for a, b in self.all_rows())

    def vertices(self) -> list[list[Fraction]]:
        rows = self.all_rows()
        found: list[list[Fraction]] = []
        for chosen in combinations(range(len(rows)), self.dim):
            matrix = [list(rows[i][0]) for i in chosen]
            rhs = [rows[i][1] for i in chosen]
            point = _solve(matrix, rhs)
            if point is None or not self.contains(point):
                continue
            if point not in found:
                found.append(point)
        return found

    def is_empty(self) -> bool:
        return not self.vertices()

    def intersect(self, other: "Region") -> "Region":
        if self.dim != other.dim:
            raise ValueError("regions of different dimension")
        return Region(self.dim, list(self.rows) + list(other.rows))


def gain(delta: Vector, region: Region,
         base: Vector | None = None) -> Fraction | None:
    """`min { <delta, v - p> : v in K }`; `None` when the region is empty.

    `delta` is a position, not a state: the quantity is the position's worst
    value over the region relative to the displayed state `p`.
    """
    verts = region.vertices()
    if not verts:
        return None
    origin = list(base) if base is not None else [Fraction(0)] * region.dim
    return min(sum((di * (vi - pi) for di, vi, pi in zip(delta, v, origin)),
                   Fraction(0)) for v in verts)


def scaled_sum(moves: Sequence[Vector], weights: Sequence[Fraction]) -> list[Fraction]:
    """The superposed intervention `sum_r w_r delta_r`."""
    dim = len(moves[0])
    out = [Fraction(0)] * dim
    for move, w in zip(moves, weights):
        for i in range(dim):
            out[i] += w * move[i]
    return out


class Reason:
    """One reason's certified single-reason intervention."""

    def __init__(self, name: str, move: Vector, region: Region,
                 defect: Fraction, margin: Fraction,
                 base: Vector | None = None):
        self.name = name
        self.move = list(move)
        self.region = region
        self.defect = defect
        self.margin = margin
        self.base = list(base) if base is not None else [Fraction(0)] * region.dim

    def individually_actionable(self) -> bool:
        g = gain(self.move, self.region, self.base)
        return g is not None and g >= self.margin * self.defect


def common_region(reasons: Sequence[Reason]) -> Region:
    region = Region(reasons[0].region.dim)
    for r in reasons:
        region = region.intersect(r.region)
    return region


def aggregate_gain(reasons: Sequence[Reason],
                   weights: Sequence[Fraction]) -> Fraction | None:
    """Theorem T4's quantity: the superposed move read against `K = cap_r K^r`."""
    return gain(scaled_sum([r.move for r in reasons], weights),
                common_region(reasons), reasons[0].base)


def aggregate_floor(reasons: Sequence[Reason],
                    weights: Sequence[Fraction]) -> Fraction:
    """`sum_r w_r gamma_r d_r`, the floor T4 claims for the aggregate gain."""
    return sum((w * r.margin * r.defect for r, w in zip(reasons, weights)),
               Fraction(0))


def own_region_gain(reason: Reason, joint_move: Vector) -> Fraction | None:
    """Reason-relative gain of the *joint* move read against that reason's own
    region — the quantity the composition countermodel destroys."""
    return gain(joint_move, reason.region, reason.base)


def compose(moves: Sequence[Vector]) -> list[Fraction]:
    """Sequential application read as a net displacement.

    Each move is applied to the state the previous ones produced, so the net
    displacement is the sum of the *realized* steps rather than of the certified
    ones. In the countermodel the realized steps differ from the certified ones
    because the second move consumes mass the first created.
    """
    dim = len(moves[0])
    out = [Fraction(0)] * dim
    for move in moves:
        for i in range(dim):
            out[i] += move[i]
    return out


# --- named fixtures -------------------------------------------------------


def chain_reasons(margin: Fraction = Fraction(1, 4)) -> list[Reason]:
    """Three modes `x, y, z`; reason 1 wants `x -> y`, reason 2 wants `y -> z`.

    Both regions are nonempty and their intersection is nonempty, so nothing here
    is a conflict of demands.
    """
    x, y, z = 0, 1, 2
    dim = 3

    def row(plus: int, minus: int) -> Row:
        a = [Fraction(0)] * dim
        a[plus] = Fraction(1)
        a[minus] = Fraction(-1)
        return (tuple(a), margin)

    half = Fraction(1, 2)
    base = [half, half, Fraction(0)]
    move1 = [Fraction(0)] * dim
    move1[x], move1[y] = -half, half
    move2 = [Fraction(0)] * dim
    move2[y], move2[z] = -half, half
    return [
        Reason("x->y", move1, Region(dim, [row(y, x)]), half, margin, base),
        Reason("y->z", move2, Region(dim, [row(z, y)]), half, margin, base),
    ]


def conflicting_reasons() -> list[Reason]:
    """Two reasons whose regions have empty intersection; the moves cancel."""
    dim = 2
    up = ((Fraction(1), Fraction(0)), Fraction(3, 4))
    down = ((Fraction(-1), Fraction(0)), Fraction(-1, 4))
    lam = Fraction(1, 2)
    base = [Fraction(1, 2), Fraction(1, 2)]
    return [
        Reason("raise", [lam, Fraction(0)], Region(dim, [up]),
               Fraction(1, 2), Fraction(1, 4), base),
        Reason("lower", [-lam, Fraction(0)], Region(dim, [down]),
               Fraction(1, 2), Fraction(1, 4), base),
    ]


def vanishing_share(horizon: int) -> dict[str, list[Fraction]]:
    """Aggregate Uptake controls a share-weighted sum and says nothing about a
    reason whose share of total service vanishes."""
    one = Fraction(1)
    first = [one] * horizon
    second = [Fraction(1, t + 1) for t in range(horizon)]
    defect_first = [Fraction(0)] * horizon
    defect_second = [one] * horizon
    return {"service_1": first, "service_2": second,
            "defect_1": defect_first, "defect_2": defect_second}
