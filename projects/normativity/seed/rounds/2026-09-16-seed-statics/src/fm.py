"""Fourier–Motzkin projection onto one coordinate, mirroring `SeedStatics.lean` §6.

`LinCon` is `(coeffs, const, strict)`; `elim d cs` eliminates the last of `d + 1`
coordinates exactly as the Lean `elim` does; `project` iterates it down to dimension
one with the chosen coordinate moved to position 0 by the transposition `swap(phi, 0)`;
`lo1`/`hi1` read the endpoints.  Used as a cross-check of the simplex on small fixtures.
"""

from __future__ import annotations

from fractions import Fraction

F = Fraction


def getD(l, i):
    return l[i] if i < len(l) else F(0)


def last_coeff(d, c):
    return getD(c[0], d)


def combo_coeffs(d, p, n, l, m):
    return [p * getD(l, i) - n * getD(m, i) for i in range(d)]


def combine(d, cl, cu):
    return (combo_coeffs(d, last_coeff(d, cu), last_coeff(d, cl), cl[0], cu[0]),
            last_coeff(d, cu) * cl[1] - last_coeff(d, cl) * cu[1],
            cl[2] or cu[2])


def elim(d, cs):
    zero = [c for c in cs if last_coeff(d, c) == 0]
    lows = [c for c in cs if last_coeff(d, c) < 0]
    ups = [c for c in cs if last_coeff(d, c) > 0]
    return zero + [combine(d, cl, cu) for cl in lows for cu in ups]


def feasible(d, cs):
    """Lean's `feasible`: eliminate down to dimension zero and check the constants."""
    while d > 0:
        d -= 1
        cs = elim(d, cs)
    return all((c[1] > 0) if c[2] else (c[1] >= 0) for c in cs)


def project(n, cs):
    """Eliminate the last n coordinates of a system over n + 1 coordinates."""
    while n > 0:
        cs = elim(n, cs)
        n -= 1
    return cs


def c0(c):
    return getD(c[0], 0)


def lo1(cs):
    lows = [c[1] / c0(c) for c in cs if c0(c) < 0]
    out = F(0)
    for b in reversed(lows):
        out = max(b, out)
    return out


def hi1(cs):
    ups = [c[1] / c0(c) for c in cs if c0(c) > 0]
    out = F(1)
    for b in reversed(ups):
        out = min(b, out)
    return out


def zero_conditions_ok(cs):
    return all(c[1] >= 0 for c in cs if c0(c) == 0)


def to_lincon(phi, d, row):
    """Row (a, b) over d coordinates, phi moved to position 0 by swap(phi, 0)."""
    a, b = row

    def swap(k):
        if k == phi:
            return 0
        if k == 0:
            return phi
        return k
    return ([F(a[swap(k)]) for k in range(d)], F(b), False)


def fm_interval(rows, d, phi):
    """(lo, hi) or None, by elimination — the algorithm `forcedInterval` in Lean."""
    cube = []
    for i in range(d):
        e = [F(0)] * d
        e[i] = F(1)
        cube.append((e, F(1)))
        cube.append(([-v for v in e], F(0)))
    cs = [to_lincon(phi, d, r) for r in cube + list(rows)]
    cs1 = project(d - 1, cs)
    if not zero_conditions_ok(cs1):
        return None
    lo, hi = lo1(cs1), hi1(cs1)
    if lo > hi:
        return None
    return (lo, hi)
