"""The exact dual-distance presentation, and the sup-norm distance it measures.

Row conformance is presentation-relative. What makes it intrinsic is a row family
whose largest violation *is* the sup-norm distance to the region, for every price
and with no error term. For a polytope given by its vertices such a family exists,
it is finite and rational, and it is a subset of the support-function rows.

**The construction.** Write `K = conv(V)` for a finite rational `V` in the cube,
and

    h(c)  =  min over v in V of <c, v> ,
    F(p)  =  sup over ||c||_1 <= 1 of ( h(c) - <c, p> ) .

`F(p)` is the sup-norm distance to `K` — ordinary convex duality, with the `l1`
ball appearing because it is the `l_inf` dual ball. Split the ball by which vertex
attains the minimum,

    R_v  =  { c : ||c||_1 <= 1,  <c, v> <= <c, v'>  for every v' in V } ,

so that `B_1 = union of R_v` and `h(c) = <c, v>` on `R_v`. On `R_v` the objective
`h(c) - <c,p>` is *linear* in `c`, so its maximum over the bounded polytope `R_v`
is attained at a vertex. Hence

    N*(V)  =  union over v in V of vertices(R_v)

is a finite rational set, independent of `p`, and

    max over c in N*(V) of ( h(c) - <c,p> )_+   =   dist_inf(p, K)

for every `p`. Two things fall out: the rows `<c, x> >= h(c)` for `c` in `N*(V)`
are an exact H-representation of `K`, and every one of them holds at every `v` in
`V`, so a presentation built this way is world-inclusive by construction.

**What is checked here and what is not.** `linf_distance_to_hull` computes the
distance by exact enumeration of the linear program's basic solutions, which does
not use the duality above, so comparing it against `exact_dual_rows` is a genuine
test rather than a restatement. The duality itself is cited, not reproved.

Everything is exact rational arithmetic. Nothing here is efficient: the vertex
enumeration is naive, and the row count grows with the fragment.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product
from typing import Iterable, Sequence

from enforcement import Row
from market import ZERO

ONE = Fraction(1)

Vector = tuple[Fraction, ...]


def dot(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    return sum((Fraction(a) * Fraction(b) for a, b in zip(u, v)), ZERO)


# --- exact linear algebra over the rationals ------------------------------------

def solve_exact(rows: Sequence[Sequence[Fraction]],
                rhs: Sequence[Fraction]) -> list[Fraction] | None:
    """The unique solution of a square rational system, or `None` if singular."""
    n = len(rhs)
    a = [[Fraction(x) for x in row] + [Fraction(rhs[i])] for i, row in enumerate(rows)]
    for col in range(n):
        pivot = None
        for r in range(col, n):
            if a[r][col] != 0:
                pivot = r
                break
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


# --- the sup-norm distance to a convex hull, by basic-solution enumeration -------

def linf_distance_to_hull(p: Sequence[Fraction],
                          worlds: Sequence[Sequence[Fraction]]) -> Fraction:
    """`min over mu in Delta(V) of ||p - sum mu_v v||_inf`, exactly.

    The linear program in `(mu, eps)` is solved by enumerating its basic
    solutions: every optimum of a linear program over a pointed feasible region is
    attained at one, so the minimum over feasible basic solutions is the value.
    Deliberately independent of the duality this module is about.
    """
    p = tuple(Fraction(x) for x in p)
    V = [tuple(Fraction(x) for x in w) for w in worlds]
    if not V:
        raise ValueError("the hull of no worlds is empty")
    k, d = len(V), len(p)
    n = k + 1                                  # variables: mu_0..mu_{k-1}, eps

    #: every constraint as `coeffs . x <= bound`; the simplex equation is separate.
    cons: list[tuple[list[Fraction], Fraction]] = []
    for v in range(k):                         # -mu_v <= 0
        row = [ZERO] * n
        row[v] = -ONE
        cons.append((row, ZERO))
    for i in range(d):                         # p_i - sum mu_v v_i - eps <= 0
        row = [-V[v][i] for v in range(k)] + [-ONE]
        cons.append((row, -p[i]))
        row = [V[v][i] for v in range(k)] + [-ONE]
        cons.append((row, p[i]))
    row = [ZERO] * n                           # -eps <= 0
    row[k] = -ONE
    cons.append((row, ZERO))

    simplex = ([ONE] * k + [ZERO], ONE)        # sum mu_v = 1

    best: Fraction | None = None
    for pick in combinations(range(len(cons)), n - 1):
        matrix = [simplex[0]] + [cons[i][0] for i in pick]
        target = [simplex[1]] + [cons[i][1] for i in pick]
        point = solve_exact(matrix, target)
        if point is None:
            continue
        if any(dot(c, point) > b for c, b in cons):
            continue
        if abs(sum(point[:k], ZERO) - ONE) != 0:
            continue
        eps = point[k]
        if best is None or eps < best:
            best = eps
    if best is None:                           # pragma: no cover - always feasible
        raise ValueError("the distance program was found infeasible")
    return best


# --- the exact dual-distance presentation ---------------------------------------

def _sign_rows(dimension: int) -> list[Vector]:
    """`<s, c> <= 1` over every sign pattern is `||c||_1 <= 1`."""
    return [tuple(Fraction(x) for x in s)
            for s in product((-1, 1), repeat=dimension)]


def critical_coefficients(worlds: Sequence[Sequence[Fraction]],
                          dimension: int) -> list[Vector]:
    """`N*(V)`: the vertices of each `R_v`, deduplicated.

    `R_v` is the `l1` ball intersected with the cone on which `v` attains the
    minimum. It is bounded, so its vertices are the solutions of the `d`-subsets
    of its constraints that are feasible for the rest.
    """
    V = [tuple(Fraction(x) for x in w) for w in worlds]
    signs = _sign_rows(dimension)
    out: list[Vector] = []
    for v in V:
        cons: list[tuple[Vector, Fraction]] = [(s, ONE) for s in signs]
        for other in V:
            if other == v:
                continue
            #: <c, v> <= <c, other>  i.e.  <c, v - other> <= 0
            cons.append((tuple(a - b for a, b in zip(v, other)), ZERO))
        for pick in combinations(range(len(cons)), dimension):
            matrix = [list(cons[i][0]) for i in pick]
            target = [cons[i][1] for i in pick]
            point = solve_exact(matrix, target)
            if point is None:
                continue
            candidate = tuple(point)
            if any(dot(c, candidate) > b for c, b in cons):
                continue
            if candidate not in out:
                out.append(candidate)
    return out


def support_value(c: Sequence[Fraction],
                  worlds: Sequence[Sequence[Fraction]]) -> Fraction:
    """`h(c) = min over v of <c, v>`."""
    return min(dot(c, w) for w in worlds)


def exact_dual_rows(worlds: Sequence[Sequence[Fraction]],
                    dimension: int) -> list[Row]:
    """The exact dual-distance presentation of `conv(worlds)`.

    Each row is a support-function row `<c, x> >= h(c)` at a critical
    coefficient. The family depends on the worlds alone; the price enters only
    when a violation is read off.
    """
    return [Row(c, support_value(c, worlds))
            for c in critical_coefficients(worlds, dimension)]


def largest_violation(rows: Iterable[Row], p: Sequence[Fraction]) -> Fraction:
    return max((row.violation(p) for row in rows), default=ZERO)


def hoffman_ratio(rows: Iterable[Row], p: Sequence[Fraction],
                  worlds: Sequence[Sequence[Fraction]]) -> Fraction | None:
    """`dist_inf(p, conv V) / max_j g_j(p)`, or `None` when nothing is violated.

    One for an exact dual-distance presentation; unbounded over presentations in
    general, which is what the near-parallel witness displays.
    """
    worst = largest_violation(rows, p)
    if worst == 0:
        return None
    return linf_distance_to_hull(p, worlds) / worst
