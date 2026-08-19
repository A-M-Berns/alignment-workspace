"""Exact rational Euclidean projection onto a rational polytope, and the
projection trader's inequalities, checked in exact arithmetic.

Everything here is `Fraction`-exact.  Nothing floating-point is used, so a test
that passes is a statement about the displayed rational data rather than an
observation about rounding.

The polytope is given by a finite vertex list `V`; `K = conv(V)`.  The projection
is certified by its variational inequality against the vertices, which is
equivalent to the variational inequality against all of `K` because every
`y - q` with `y` in `K` is a nonnegative combination of the `v - q`.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Iterable, Sequence

Vec = Sequence[Fraction]


def dot(u: Vec, v: Vec) -> Fraction:
    return sum((a * b for a, b in zip(u, v)), Fraction(0))


def sub(u: Vec, v: Vec) -> list:
    return [a - b for a, b in zip(u, v)]


def sq_dist(u: Vec, v: Vec) -> Fraction:
    d = sub(u, v)
    return dot(d, d)


def sup_dist(u: Vec, v: Vec) -> Fraction:
    return max((abs(a - b) for a, b in zip(u, v)), default=Fraction(0))


def solve_exact(A: list, b: list):
    """Gaussian elimination over the rationals.  `None` if singular."""
    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]


def satisfies_vi(p: Vec, q: Vec, V: Iterable[Vec]) -> bool:
    """`<p - q, v - q> <= 0` for every vertex — the nearest-point property."""
    d = sub(p, q)
    return all(dot(d, sub(v, q)) <= 0 for v in V)


def project(p: Vec, V: Sequence[Vec]) -> list:
    """The Euclidean nearest point of `conv(V)` to `p`, exactly.

    Enumerates the faces.  Exponential in `len(V)` by design: the point of the
    exercise is exactness, and the same exponential appears in the piece count
    of the compiled expressible feature.
    """
    if not V:
        raise ValueError("the region must be nonempty")
    dim = len(V[0])
    for size in range(1, len(V) + 1):
        for S in combinations(range(len(V)), size):
            k = len(S)
            A = []
            b = []
            for u in S:
                A.append([dot(V[u], V[v]) for v in S] + [Fraction(-1)])
                b.append(dot(V[u], p))
            A.append([Fraction(1)] * k + [Fraction(0)])
            b.append(Fraction(1))
            sol = solve_exact(A, b)
            if sol is None:
                continue
            lam = sol[:k]
            if any(x < 0 for x in lam):
                continue
            q = [sum((lam[i] * V[S[i]][j] for i in range(k)), Fraction(0))
                 for j in range(dim)]
            if satisfies_vi(p, q, V):
                return q
    raise RuntimeError("no face certified the projection; the input is malformed")


def shares(lam: Fraction, p: Vec, q: Vec) -> list:
    """The projection trader's position: `lam * (q - p)`."""
    return [lam * (qi - pi) for pi, qi in zip(p, q)]


def trade_value(zeta: Vec, p: Vec, w: Vec) -> Fraction:
    """The day's value of holding `zeta` at price `p`, assessed at `w`."""
    return dot(zeta, sub(w, p))


# --- the row construction, for the comparison ---------------------------------


def row_violation(c: Vec, r: Fraction, p: Vec) -> Fraction:
    """`max(0, r - <c, p>)`."""
    g = r - dot(c, p)
    return g if g > 0 else Fraction(0)


def row_shares(rows: Sequence, p: Vec) -> list:
    """`sum_j beta_j * g_j(p) * c_j` over rows `(c_j, r_j, beta_j)`."""
    dim = len(p)
    out = [Fraction(0)] * dim
    for c, r, beta in rows:
        g = row_violation(c, r, p)
        if g == 0:
            continue
        for i in range(dim):
            out[i] += beta * g * c[i]
    return out


def max_row_violation(rows: Sequence, p: Vec) -> Fraction:
    return max((row_violation(c, r, p) for c, r, _ in rows), default=Fraction(0))
