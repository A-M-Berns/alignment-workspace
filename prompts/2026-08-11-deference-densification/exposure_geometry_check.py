"""Exact-arithmetic checks for the bounded-exposure / harvest geometry of REPORT.md.

Round: prompts/2026-08-11-deference-densification (Track E).
Every number here is a Python int or a fractions.Fraction. No floats appear.

Run:  python3 exposure_geometry_check.py

What it checks, in order:
  1. Lemma 1 (piercing duality) on random window families: greedy-by-right-endpoint
     attains the exhaustive maximum disjoint subfamily, and the greedy piercing set
     pierces every window and has exactly that size.
  2. Theorem 2's integrality on random families: the exact rational LP value of
     max sum(a) subject to a >= 0 and per-point exposure <= 1 equals nu, so
     fractional and overlapping placement buy nothing.  (Vertex enumeration with
     exact rational Gaussian elimination.)
  3. Corollary 4 (orbit formula) against greedy, and the two closed forms.
  4. The regime table and the time-to-force orbit reported in REPORT.md section 1.
  5. The signed-netting witness of REPORT.md section 6.
"""
from fractions import Fraction
from itertools import combinations
import random

# ------------------------------------------------------------------ windows

def windows(F, Omega):
    """Settlement windows I_n = [n, F(n)) for n in Omega."""
    return [(n, F(n)) for n in Omega]


def nu_greedy(iv):
    """Maximum pairwise-disjoint subfamily, greedy by right endpoint."""
    sel, cur = [], None
    for (l, r) in sorted(iv, key=lambda x: (x[1], x[0])):
        if cur is None or l >= cur:
            sel.append((l, r))
            cur = r
    return sel


def nu_brute(iv):
    """Exhaustive maximum pairwise-disjoint subfamily size."""
    for size in range(len(iv), 0, -1):
        for sub in combinations(iv, size):
            s = sorted(sub)
            if all(s[i][1] <= s[i + 1][0] for i in range(len(s) - 1)):
                return size
    return 0


def pierce_greedy(iv):
    """Greedy piercing set: repeatedly take (minimum right endpoint) - 1."""
    P, rem = [], sorted(iv, key=lambda x: (x[1], x[0]))
    while rem:
        p = rem[0][1] - 1
        P.append(p)
        rem = [(l, r) for (l, r) in rem if not (l <= p < r)]
    return P


# ------------------------------------------------------------------ exact LP

def _solve(A, b):
    """Exact rational Gaussian elimination; unique solution, or None."""
    k = len(A[0])
    M = [list(map(Fraction, row)) + [Fraction(bi)] for row, bi in zip(A, b)]
    piv, r = [], 0
    for c in range(k):
        pr = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    if len(piv) < k:
        return None
    for i in range(r, len(M)):
        if M[i][k] != 0:
            return None
    x = [Fraction(0)] * k
    for i, c in enumerate(piv):
        x[c] = M[i][k]
    return x


def lp_max(iv):
    """Exact value of  max sum(a)  subject to  a >= 0  and, at every integer point
    t, total weight of windows containing t at most 1.  Vertex enumeration; the
    feasible region is bounded because the constraint at t = n forces a_n <= 1."""
    k = len(iv)
    pts = sorted({t for (l, r) in iv for t in range(l, r)})
    rows = [[1 if l <= t < r else 0 for (l, r) in iv] for t in pts]
    rhs = [Fraction(1)] * len(pts)
    for j in range(k):
        rows.append([-1 if i == j else 0 for i in range(k)])
        rhs.append(Fraction(0))

    def feasible(x):
        return all(sum(c * xi for c, xi in zip(row, x)) <= b
                   for row, b in zip(rows, rhs))

    best = Fraction(0)
    for idx in combinations(range(len(rows)), k):
        x = _solve([rows[i] for i in idx], [rhs[i] for i in idx])
        if x is not None and feasible(x):
            best = max(best, sum(x))
    return best


# ------------------------------------------------------------------ regimes

def isqrt(n):
    if n < 2:
        return n
    x, y = n, (n + 1) // 2
    while y < x:
        x, y = y, (y + n // y) // 2
    return x


REGIMES = [
    ("F(n) = n+1",          lambda n: n + 1,            lambda T: T + 1),
    ("F(n) = n+8",          lambda n: n + 8,            lambda T: T // 8 + 1),
    ("F(n) = n+isqrt(n)+1", lambda n: n + isqrt(n) + 1, None),
    ("F(n) = 2n+1",         lambda n: 2 * n + 1,        None),
    ("F(n) = 2^n+1",        lambda n: (2 ** n + 1) if n < 4096 else 2 ** 4096, None),
]


def nu_iter(F, T):
    """#{k >= 0 : F^k(0) <= T}, the greedy orbit count for nondecreasing F.
    Values above T are clamped so that fast-growing F does not materialize."""
    n, c = 0, 0
    while n <= T:
        c += 1
        v = F(n)
        n = v if v <= T else T + 1
    return c


def nu(F, closed, T):
    return closed(T) if closed is not None else nu_iter(F, T)


# ------------------------------------------------------------------ checks

def check_duality(trials=4000, seed=20260811):
    rng = random.Random(seed)
    for _ in range(trials):
        k = rng.randint(1, 8)
        iv = [(l, l + rng.randint(1, 7))
              for l in (rng.randint(0, 12) for _ in range(k))]
        n_ = len(nu_greedy(iv))
        assert n_ == nu_brute(iv), ("greedy != exhaustive", iv)
        P = pierce_greedy(iv)
        assert all(any(l <= p < r for p in P) for (l, r) in iv), ("unpierced", iv)
        assert len(P) == n_, ("tau != nu", iv, P)
    return trials


def check_lp(trials=250, seed=8112026):
    rng = random.Random(seed)
    gaps = 0
    for _ in range(trials):
        k = rng.randint(1, 4)
        iv = [(l, l + rng.randint(1, 4))
              for l in (rng.randint(0, 7) for _ in range(k))]
        if lp_max(iv) != Fraction(len(nu_greedy(iv))):
            gaps += 1
            print("  LP/integral gap at", iv)
    return trials, gaps


def netting_witness(T):
    """Signed book with F(n) = 2n+1, unit sizes, alternating signs, and
    D_n = 1 (n even) / 1/2 (n odd).  Returns (sup |net exposure|, harvest,
    gross bound M * Dbar * nu) with M = 1 and Dbar = 1, all exact."""
    F = lambda n: 2 * n + 1
    eps = lambda n: 1 if n % 2 == 0 else -1
    D = lambda n: Fraction(1) if n % 2 == 0 else Fraction(1, 2)
    sup_net = 0
    for t in range(0, 2 * T + 2):
        net = sum(eps(n) for n in range(0, min(t, T) + 1) if F(n) > t)
        sup_net = max(sup_net, abs(net))
    harvest = sum(Fraction(eps(n)) * D(n) for n in range(0, T + 1))
    return sup_net, harvest, nu_iter(F, T)


if __name__ == "__main__":
    print("1. piercing duality, random instances:", check_duality())
    t, g = check_lp()
    print("2. exact-LP instances:", t, "| instances where the LP beats nu:", g)

    print("3. orbit formula and closed forms vs greedy, all T < 300:", end=" ")
    for name, F, closed in REGIMES:
        for T in range(0, 300):
            g_ = len(nu_greedy(windows(F, range(T + 1))))
            assert nu_iter(F, T) == g_, (name, T)
            if closed is not None:
                assert closed(T) == g_, (name, T)
    print("ok")

    Ts = [10, 100, 1000, 10 ** 6, 10 ** 12]
    print()
    print("4a. nu_F(T), exact integers")
    print("    " + "regime".ljust(22) + "".join(str(T).rjust(15) for T in Ts))
    for name, F, closed in REGIMES:
        print("    " + name.ljust(22)
              + "".join(str(nu(F, closed, T)).rjust(15) for T in Ts))

    print()
    print("4b. F^(m-1)(0) = least T at which m units of weight are placeable")
    print("    " + "m".ljust(4) + "".join(n.ljust(18) for n, _, _ in REGIMES))
    for m in range(1, 8):
        row = "    " + str(m).ljust(4)
        for name, F, _ in REGIMES:
            n, blown = 0, False
            for _ in range(m - 1):
                if n > 300:
                    blown = True
                    break
                n = F(n)
            row += ("> 2^300" if blown else str(n)).ljust(18)
        print(row)

    print()
    print("5. signed-netting witness, F(n) = 2n+1, M = 1, Dbar = 1")
    print("    " + "T".rjust(8) + "sup|net|".rjust(10) + "harvest".rjust(12)
          + "gross bound".rjust(14))
    for T in [10, 100, 1000, 10000]:
        s, h, v = netting_witness(T)
        print("    " + str(T).rjust(8) + str(s).rjust(10) + str(h).rjust(12)
              + str(v).rjust(14))
