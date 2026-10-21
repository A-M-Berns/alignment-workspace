"""Exact rational linear programming: a two-phase tableau simplex with Bland's rule.

Everything is `fractions.Fraction`.  The solver is deliberately small and slow; the
fixtures it serves have at most a hundred variables.

Problems are stated in standard form

    minimise  c . x   subject to   A x = b,  x >= 0,

and the two helpers below reduce `A x <= b` systems, Farkas certificates and bound
certificates to it.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Optional, Sequence

F = Fraction


class LPResult:
    def __init__(self, status: str, x: Optional[list[Fraction]] = None,
                 value: Optional[Fraction] = None):
        self.status = status      # "optimal" | "infeasible" | "unbounded"
        self.x = x
        self.value = value

    def __repr__(self) -> str:
        return f"LPResult({self.status}, value={self.value})"


def _pivot(T: list[list[Fraction]], r: int, s: int) -> None:
    piv = T[r][s]
    T[r] = [v / piv for v in T[r]]
    for i in range(len(T)):
        if i != r and T[i][s] != 0:
            f = T[i][s]
            T[i] = [a - f * b for a, b in zip(T[i], T[r])]


def _run(T: list[list[Fraction]], basis: list[int], ncols: int) -> str:
    """Bland's rule on a tableau whose last row is the objective (to be minimised) and
    whose last column is the right-hand side.  Returns "optimal" or "unbounded"."""
    m = len(T) - 1
    while True:
        obj = T[m]
        s = next((j for j in range(ncols) if obj[j] < 0), None)
        if s is None:
            return "optimal"
        r = None
        best = None
        for i in range(m):
            if T[i][s] > 0:
                ratio = T[i][ncols] / T[i][s]
                if best is None or ratio < best or (ratio == best and basis[i] < basis[r]):
                    best, r = ratio, i
        if r is None:
            return "unbounded"
        _pivot(T, r, s)
        basis[r] = s


def simplex_min(c: Sequence[Fraction], A: Sequence[Sequence[Fraction]],
                b: Sequence[Fraction]) -> LPResult:
    """min c.x s.t. A x = b, x >= 0."""
    m, n = len(A), len(c)
    A = [[F(v) for v in row] for row in A]
    b = [F(v) for v in b]
    c = [F(v) for v in c]
    for i in range(m):
        if b[i] < 0:
            A[i] = [-v for v in A[i]]
            b[i] = -b[i]
    # Phase 1.  A row that already has a unit column (a slack with the right sign)
    # takes it as its basic variable; every other row gets an artificial.
    unit_of_row = {}
    used = set()
    for j in range(n):
        col = [A[i][j] for i in range(m)]
        nz = [i for i in range(m) if col[i] != 0]
        if len(nz) == 1 and col[nz[0]] == 1 and nz[0] not in unit_of_row and j not in used:
            unit_of_row[nz[0]] = j
            used.add(j)
    art_rows = [i for i in range(m) if i not in unit_of_row]
    na = len(art_rows)
    ncols = n + na
    T = []
    for i in range(m):
        art = [F(0)] * na
        if i in art_rows:
            art[art_rows.index(i)] = F(1)
        T.append(A[i] + art + [b[i]])
    obj = [F(0)] * n + [F(1)] * na + [F(0)]
    basis = [0] * m
    for i in range(m):
        if i in unit_of_row:
            basis[i] = unit_of_row[i]
        else:
            basis[i] = n + art_rows.index(i)
            obj = [o - t for o, t in zip(obj, T[i])]
    T.append(obj)
    _run(T, basis, ncols)
    if T[m][ncols] != 0:      # objective row holds -value
        return LPResult("infeasible")
    # drive artificials out of the basis
    rows_to_drop = []
    for i in range(m):
        if basis[i] >= n:
            s = next((j for j in range(n) if T[i][j] != 0), None)
            if s is None:
                rows_to_drop.append(i)
            else:
                _pivot(T, i, s)
                basis[i] = s
    for i in sorted(rows_to_drop, reverse=True):
        del T[i]
        del basis[i]
    m2 = len(T) - 1
    # Phase 2: drop artificial columns, install the real objective.
    T = [row[:n] + [row[ncols]] for row in T]
    obj = c + [F(0)]
    for i in range(m2):
        f = obj[basis[i]]
        if f != 0:
            obj = [o - f * t for o, t in zip(obj, T[i])]
    T[m2] = obj
    status = _run(T, basis, n)
    if status == "unbounded":
        return LPResult("unbounded")
    x = [F(0)] * n
    for i in range(m2):
        x[basis[i]] = T[i][n]
    value = sum(ci * xi for ci, xi in zip(c, x))
    return LPResult("optimal", x, value)


# --- helpers over inequality systems --------------------------------------------------

def minimise_over(rows: Sequence[tuple[Sequence[Fraction], Fraction]], d: int,
                  objective: Sequence[Fraction]) -> LPResult:
    """min objective.x s.t. every row a.x <= b and 0 <= x <= 1.

    Slack variables make each row an equality; the cube is two rows per coordinate."""
    all_rows = list(rows)
    for i in range(d):
        e = [F(0)] * d
        e[i] = F(1)
        all_rows.append((e, F(1)))               # x_i <= 1  (x_i >= 0 is the sign constraint)
    m = len(all_rows)
    A = []
    b = []
    for k, (a, bk) in enumerate(all_rows):
        A.append([F(v) for v in a] + [F(1) if j == k else F(0) for j in range(m)])
        b.append(F(bk))
    c = [F(v) for v in objective] + [F(0)] * m
    res = simplex_min(c, A, b)
    if res.status == "optimal":
        res.x = res.x[:d]
    return res


def interval(rows, d: int, phi: int) -> Optional[tuple[Fraction, Fraction]]:
    """The forced interval [inf x_phi, sup x_phi] over the region, or None if empty."""
    e = [F(0)] * d
    e[phi] = F(1)
    lo = minimise_over(rows, d, e)
    if lo.status != "optimal":
        return None
    hi = minimise_over(rows, d, [-v for v in e])
    return (lo.value, -hi.value)


def feasible(rows, d: int) -> bool:
    return minimise_over(rows, d, [F(0)] * d).status == "optimal"


def cube_rows(d: int) -> list[tuple[list[Fraction], Fraction]]:
    out = []
    for i in range(d):
        e = [F(0)] * d
        e[i] = F(1)
        out.append((e, F(1)))
        out.append(([-v for v in e], F(0)))
    return out


def farkas_certificate(rows, d: int) -> Optional[list[Fraction]]:
    """Nonnegative multipliers over rows ++ cube_rows(d) with zero coefficient sum and
    constant sum -1, or None if the system is feasible.  Verified before return."""
    allrows = list(rows) + cube_rows(d)
    m = len(allrows)
    A = []
    b = []
    for j in range(d):
        A.append([F(allrows[i][0][j]) for i in range(m)])
        b.append(F(0))
    A.append([F(allrows[i][1]) for i in range(m)])
    b.append(F(-1))
    res = simplex_min([F(0)] * m, A, b)
    if res.status != "optimal":
        return None
    lam = res.x
    assert verify_farkas(allrows, d, lam)
    return lam


def verify_farkas(allrows, d: int, lam) -> bool:
    if any(l < 0 for l in lam):
        return False
    for j in range(d):
        if sum(l * F(r[0][j]) for l, r in zip(lam, allrows)) != 0:
            return False
    return sum(l * F(r[1]) for l, r in zip(lam, allrows)) < 0


def bound_certificate(rows, d: int, phi: int, sign: int, value: Fraction):
    """Multipliers over rows ++ cube with coefficient sum sign*e_phi and constant sum
    `value`; certifies sign*x_phi <= value.  None if no such certificate."""
    allrows = list(rows) + cube_rows(d)
    m = len(allrows)
    A = []
    b = []
    for j in range(d):
        A.append([F(allrows[i][0][j]) for i in range(m)])
        b.append(F(sign) if j == phi else F(0))
    A.append([F(allrows[i][1]) for i in range(m)])
    b.append(F(value))
    res = simplex_min([F(0)] * m, A, b)
    if res.status != "optimal":
        return None
    return res.x


def minimal_infeasible_subset(rows, d: int) -> list[int]:
    """Indices of a minimal infeasible subset of `rows` relative to the cube, by the
    deletion filter: drop a row if the rest stays infeasible."""
    assert not feasible(rows, d)
    keep = list(range(len(rows)))
    for i in list(keep):
        trial = [rows[j] for j in keep if j != i]
        if not feasible(trial, d):
            keep.remove(i)
    return keep
