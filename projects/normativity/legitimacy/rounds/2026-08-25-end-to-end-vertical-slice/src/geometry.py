"""Exact rational geometry: vertex generation, hull membership, projection.

The schedule type the traderization theorem is stated against carries its region
as `RationalPolytope`, which is a nonempty list of rational vertices and a
convex hull over it. The list is not required to be minimal — the structure has
two fields, `verts` and `verts_ne`, and the carrier is the hull of whatever is
listed — so a generating set suffices, and this file produces one without
facet enumeration.

The route is barycentric. `K = conv(P) ∩ {rows}` is the image of

    Lambda = { lambda >= 0 : sum_v lambda_v = 1 , A (sum_v lambda_v v) >= r }

under `lambda |-> sum_v lambda_v v`. `Lambda` has an explicit row presentation,
its vertices are enumerable exactly, and their images generate `K`. Nothing
here needs the facets of `conv(P)`, which is the enumeration the repository
declines to perform.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Optional, Sequence

ZERO = Fraction(0)
ONE = Fraction(1)


class EnumerationBudget(Exception):
    """The vertex enumeration exceeded its subset cap."""


def solve_exact(matrix: Sequence[Sequence[Fraction]],
                rhs: Sequence[Fraction]) -> Optional[list]:
    """Gauss-Jordan on a square rational system; `None` when singular."""
    n = len(matrix)
    a = [list(row) + [Fraction(rhs[i])] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col] != 0), None)
        if pivot is None:
            return None
        a[col], a[pivot] = a[pivot], a[col]
        inv = ONE / a[col][col]
        a[col] = [x * inv for x in a[col]]
        for r in range(n):
            if r != col and a[r][col] != 0:
                f = a[r][col]
                a[r] = [x - f * y for x, y in zip(a[r], a[col])]
    return [a[i][n] for i in range(n)]


def polytope_vertices(constraints: Sequence, dimension: int,
                      cap: int = 200000) -> list:
    """Vertices of `{x : a_j . x <= b_j}`, exactly.

    Each vertex is the solution of some `dimension` constraints taken as
    equalities that satisfies all of them. Brute force over subsets; exact
    throughout, and the cap is raised as an error rather than silently
    truncating, because a truncated enumeration reports a smaller region as if
    it were the region.
    """
    total = len(constraints)
    if dimension == 0:
        return [()] if all(c.b >= ZERO for c in constraints) else []
    count = 1
    for i in range(dimension):
        count = count * (total - i) // (i + 1)
    if count > cap:
        raise EnumerationBudget(
            f"{count} subsets of {total} constraints in dimension {dimension}")
    out: list = []
    for subset in combinations(range(total), dimension):
        rows = [list(constraints[j].a[:dimension]) for j in subset]
        rhs = [constraints[j].b for j in subset]
        x = solve_exact(rows, rhs)
        if x is None:
            continue
        if any(sum((c.a[i] * x[i] for i in range(dimension)), ZERO) > c.b
               for c in constraints):
            continue
        point = tuple(x)
        if point not in out:
            out.append(point)
    return out


def prune(points: Sequence, limit: int = 16) -> list:
    """Drop points that are already in the hull of the others.

    The result still generates the same region — the type on the other side asks
    for a list whose hull is the region, not for its extreme points — and a
    pruned list is what makes a trace readable. Order-dependent when several
    points are mutually redundant, and deterministic for a fixed input order.

    Above `limit` points the pruning is skipped and the list is returned as
    generated. Redundancy costs a reader and nothing else, while the membership
    test is combinatorial in the point count; skipping is therefore sound and
    only ever leaves the list longer.
    """
    kept = [tuple(p) for p in points]
    if len(kept) > limit:
        return kept
    i = 0
    while i < len(kept):
        rest = kept[:i] + kept[i + 1:]
        if rest and in_hull(kept[i], rest):
            kept = rest
        else:
            i += 1
    return kept


def generate_region(vertices: Sequence, rows: Sequence,
                    cap: int = 200000) -> list:
    """A generating vertex list for `conv(vertices) ∩ {rows}`.

    `rows` are compiled rows in the `c . p >= r` convention. The result is a
    list of price points whose convex hull is the intersection, pruned of
    points the rest already generate.
    """
    from conflict import hull_system

    constraints, m = hull_system(rows, vertices)
    weights = polytope_vertices(constraints, m, cap=cap)
    verts = [tuple(Fraction(x) for x in v) for v in vertices]
    d = len(verts[0]) if verts else 0
    out: list = []
    for lam in weights:
        point = tuple(sum((lam[j] * verts[j][i] for j in range(m)), ZERO)
                      for i in range(d))
        if point not in out:
            out.append(point)
    return prune(out)


def in_hull(point: Sequence[Fraction], vertices: Sequence) -> bool:
    """Exact convex-hull membership.

    By Caratheodory a point of the hull of a set in `d` dimensions is a convex
    combination of at most `d + 1` of its members, so the search is over subsets
    of that size and each is one small rational system. Exact and terminating.

    Elimination is not used here. A membership question needs no certificate,
    and Fourier-Motzkin over the weight system grows with the vertex count for
    no return.
    """
    d = len(point)
    verts = [tuple(Fraction(x) for x in v) for v in vertices]
    if not verts:
        return False
    target = tuple(Fraction(x) for x in point)
    if target in verts:
        return True
    rhs = list(target) + [ONE]
    for size in range(1, min(d + 1, len(verts)) + 1):
        for subset in combinations(verts, size):
            rows = [[v[i] for v in subset] for i in range(d)]
            rows.append([ONE] * size)
            lam = solve_rect(rows, rhs)
            if lam is None or any(x < ZERO for x in lam):
                continue
            if all(sum((l * v[i] for l, v in zip(lam, subset)), ZERO)
                   == target[i] for i in range(d)):
                return True
    return False


def solve_rect(rows: Sequence[Sequence[Fraction]],
               rhs: Sequence[Fraction]) -> Optional[list]:
    """A particular solution of a rectangular rational system, or `None`.

    Gauss-Jordan on the augmented matrix, free variables set to zero. `None`
    exactly when the system is inconsistent, so an underdetermined but solvable
    system returns a solution rather than a failure.
    """
    unknowns = len(rows[0]) if rows else 0
    a = [list(r) + [Fraction(rhs[i])] for i, r in enumerate(rows)]
    pivots: list = []
    r = 0
    for col in range(unknowns):
        piv = next((i for i in range(r, len(a)) if a[i][col] != 0), None)
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        inv = ONE / a[r][col]
        a[r] = [x * inv for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][col] != 0:
                f = a[i][col]
                a[i] = [x - f * y for x, y in zip(a[i], a[r])]
        pivots.append(col)
        r += 1
        if r == len(a):
            break
    for i in range(r, len(a)):
        if all(x == 0 for x in a[i][:unknowns]) and a[i][unknowns] != 0:
            return None
    out = [ZERO] * unknowns
    for i, col in enumerate(pivots):
        out[col] = a[i][unknowns]
    return out


def project_onto(point: Sequence[Fraction], vertices: Sequence) -> list:
    """Exact Euclidean projection of a price vector onto a rational polytope.

    Certified by the variational inequality against the vertices, which is
    equivalent to the inequality against the whole hull because every `y - q`
    with `y` in the hull is a nonnegative combination of the `v - q`. This is
    the construction `projection.py` carries in the projection-enforcement
    round, reproduced here rather than imported so that the slice's runner stays
    self-contained.
    """
    verts = [tuple(Fraction(x) for x in v) for v in vertices]
    if not verts:
        raise ValueError("the polytope has no vertices")
    p = [Fraction(x) for x in point]
    best = None
    for size in range(1, len(verts) + 1):
        for subset in combinations(range(len(verts)), size):
            q = _affine_minimiser(p, [verts[j] for j in subset])
            if q is None:
                continue
            if not in_hull(q, verts):
                continue
            if not _variational(p, q, verts):
                continue
            d2 = sum(((a - b) ** 2 for a, b in zip(p, q)), ZERO)
            if best is None or d2 < best[0]:
                best = (d2, q)
    if best is None:
        raise ValueError("no projection found")
    return list(best[1])


def _affine_minimiser(p: Sequence[Fraction], subset: Sequence) -> Optional[tuple]:
    """The nearest point of the affine hull of `subset`, in barycentric form."""
    k = len(subset)
    d = len(p)
    matrix = [[ZERO] * (k + 1) for _ in range(k + 1)]
    rhs = [ZERO] * (k + 1)
    for i in range(k):
        for j in range(k):
            matrix[i][j] = sum((subset[i][t] * subset[j][t] for t in range(d)),
                               ZERO)
        matrix[i][k] = Fraction(-1, 2)
        rhs[i] = sum((subset[i][t] * Fraction(p[t]) for t in range(d)), ZERO)
    for j in range(k):
        matrix[k][j] = ONE
    rhs[k] = ONE
    sol = solve_exact(matrix, rhs)
    if sol is None:
        return None
    lam = sol[:k]
    return tuple(sum((lam[j] * subset[j][t] for j in range(k)), ZERO)
                 for t in range(d))


def _variational(p: Sequence[Fraction], q: Sequence[Fraction],
                 vertices: Sequence) -> bool:
    """`<p - q, v - q> <= 0` for every vertex: the projection certificate."""
    for v in vertices:
        s = sum(((Fraction(p[i]) - q[i]) * (v[i] - q[i]) for i in range(len(q))),
                ZERO)
        if s > ZERO:
            return False
    return True
