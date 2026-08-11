"""
Exact-rational verification for TODO `diagonal-calibration` (run 3).

Part 1 (Finding A / clause (i)): the hovering quote
    a_n = 1/2 + 2^-n (n even), 1/2 (n odd),  Y_n = 1[a_n <= 1/2],  delta = 1/4
  All three weightings named in faithful-acceleration-scope.md section 4 fail to
  witness miscalibration:
    - soft high gate  softInd(delta, a_n - 1/2): partial sums bounded (<= 16/3 < 8)
    - soft low gate   softInd(delta, 1/2 - delta - a_n): identically 0
    - uniform weight: average bias (1/N) sum b_n -> 0 (partial sums in [0, 7/2])

Part 2 (clause (ii) instantiation): the hard gate w+_n = 1[a_n > 1/2] on the same
  sequence is the even-days indicator, divergent, with weighted bias ratio >= 1/2.

Part 3 (deletion test): benign settlement (target = 1/2 instead of the inverting
  1[a_n <= 1/2]) with quote a = 1/2: the divergent hard gate carries ZERO bias --
  the inverting settlement is load-bearing.

Part 4 (clause (iv) EXEC garnish -- ILLUSTRATION, NOT EVIDENCE): dithering quotes
  a_n = 1/2 + s_n * eta_n, eta_n -> 0, sides s_n from a fixed deterministic bit
  stream, run against a small gate library.
  4a. NON-summable dither (eta_n = 1/(n+2)): the one-sided soft ramp
      Ind_delta(a_n > 1/2) has support EXACTLY {a_n > 1/2}, so its weight sum is
      ~ sum eta_n / delta = DIVERGENT and it carries bias >= 1/2 on its support:
      the legal soft gate kills every non-summable ditherer (the compiled
      soft_high_kills / soft_low_kills of DiagonalCalibration.lean).
  4b. SUMMABLE dither (eta_n = 1/(n+2)^2): all continuous-in-current-price gates
      have bounded or side-balanced weight; the uniform gate sees only the side
      IMBALANCE; the patient hard gate 1[a_{n-1} > 1/2] reads YESTERDAY's side,
      so it pins the bias exactly when the side pattern is predictable from the
      past (strict alternation) and cancels when it is not (the LCG stream).
  This illustrates the isolated crux: on the summable, side-balanced,
  past-unpredictable dither, every gate in this library fails; whether some legal
  C_A-gate must succeed against A's OWN quote sides is the open step.

All arithmetic is fractions.Fraction. No floats anywhere.
"""

from fractions import Fraction as F

HALF = F(1, 2)
DELTA = F(1, 4)


def softInd(delta, x):
    """max 0 (min 1 (x/delta)) -- FaithfulAccel.softInd, exact."""
    return max(F(0), min(F(1), F(x) / delta))


# ---------------------------------------------------------------- Part 1
def a_hover(n):
    return HALF + F(1, 2) ** n if n % 2 == 0 else HALF


def Y_invert(a):
    return F(1) if a <= HALF else F(0)


def run_part1(N=400):
    high = low = S = F(0)
    checkpoints = {10, 50, 100, 200, 400}
    print("=== Part 1: the hovering quote vs the scope-note section-4 gates ===")
    print(f"{'N':>5} {'sum high gate':>16} {'sum low gate':>13} {'sum bias':>12} {'avg bias':>22}")
    for n in range(N):
        an = a_hover(n)
        high += softInd(DELTA, an - HALF)
        low += softInd(DELTA, HALF - DELTA - an)
        S += an - Y_invert(an)
        m = n + 1
        assert high <= F(16, 3), (n, high)
        assert low == 0, (n, low)
        assert F(0) <= S <= F(7, 2), (n, S)
        if m in checkpoints:
            print(f"{m:>5} {str(high):>16} {str(low):>13} {str(S):>12} {str(S/m):>22}")
    print(f"invariants held for all N <= {N}: high <= 16/3, low == 0, 0 <= S <= 7/2")
    print(f"=> avg bias |S/N| <= (7/2)/N -> 0; three published weightings all fail. OK\n")


# ---------------------------------------------------------------- Part 2
def run_part2(N=400):
    print("=== Part 2: hard gate w+ = 1[a_n > 1/2] on the same sequence ===")
    W = B = F(0)
    for n in range(N):
        an = a_hover(n)
        w = F(1) if an > HALF else F(0)
        assert w == (F(1) if n % 2 == 0 else F(0))  # = even-days indicator
        W += w
        B += w * (an - Y_invert(an))
        if W > 0:
            assert B / W >= HALF, (n, B / W)
    print(f"N={N}: sum w+ = {W} (divergent: = ceil(N/2)), weighted bias ratio = {B/W}")
    print(f"ratio >= 1/2 at every N with positive weight. OK\n")


# ---------------------------------------------------------------- Part 3
def run_part3(N=400):
    print("=== Part 3: deletion test (benign settlement Y = 1/2, quote a = 1/2) ===")
    W = B = F(0)
    for n in range(N):
        an = HALF
        w = F(1) if not (an > HALF) else F(0)   # w- gate: fires every day
        W += w
        B += w * (an - HALF)                     # bias against the BENIGN target
    print(f"N={N}: sum w- = {W} (divergent), weighted bias = {B} (identically zero)")
    assert W == N and B == 0
    print("dichotomy inequality (1/2)*W <= |B| FAILS (e.g. N=1: 1/2 <= 0 is false):")
    print("the inverting settlement is load-bearing. OK\n")


# ---------------------------------------------------------------- Part 4
def lcg_bits(n_bits, seed=12345):
    """Deterministic pseudorandom bits from an LCG (exact integer arithmetic)."""
    m, a, c = 2**31 - 1, 1103515245, 12345
    x = seed
    out = []
    for _ in range(n_bits):
        x = (a * x + c) % m
        out.append((x >> 7) & 1)
    return out


def gate_table(quotes, N):
    bias = [quotes[n] - Y_invert(quotes[n]) for n in range(N)]
    gates = {
        "uniform w=1": [F(1)] * N,
        "soft high Ind_1/4(a>1/2)": [softInd(DELTA, quotes[n] - HALF) for n in range(N)],
        "soft low  Ind_1/4(a<1/2)": [softInd(DELTA, HALF - quotes[n]) for n in range(N)],
        "note's low Ind_1/4(a<1/4)": [softInd(DELTA, HALF - DELTA - quotes[n]) for n in range(N)],
        "patient hard 1[a_{n-1}>1/2]": [F(0)] + [F(1) if quotes[n - 1] > HALF else F(0)
                                                 for n in range(1, N)],
    }
    for gname, g in gates.items():
        W = sum(g)
        B = sum(g[n] * bias[n] for n in range(N))
        ratio = "gate empty" if W == 0 else f"{float(B / W):+.4f}"
        print(f"  {gname:<30} sum w = {float(W):>10.3f}  bias ratio = {ratio}")


def run_part4(N=2000):
    print("=== Part 4 (ILLUSTRATION, NOT EVIDENCE): dithering quotes vs gate library ===")
    lcg_sides = [1 if b else -1 for b in lcg_bits(N)]
    alt_sides = [1 if n % 2 == 0 else -1 for n in range(N)]

    print(f"\n-- 4a. NON-summable dither eta_n = 1/(n+2), LCG sides (N={N}) --")
    quotes = [HALF + lcg_sides[n] * F(1, n + 2) for n in range(N)]
    gate_table(quotes, N)
    print("  reading: the soft HIGH gate diverges (~ 4*sum eta) with ratio ~ +0.5+ --")
    print("  a legal continuous gate kills every non-summable ditherer.")

    print(f"\n-- 4b. SUMMABLE dither eta_n = 1/(n+2)^2, LCG sides (N={N}) --")
    quotes = [HALF + lcg_sides[n] * F(1, (n + 2) ** 2) for n in range(N)]
    gate_table(quotes, N)
    print("  reading: soft gates now have BOUNDED weight (sum eta < pi^2/6); uniform")
    print("  ratio ~ (side imbalance)/2 -> 0 for balanced sides; the patient gate cancels.")

    print(f"\n-- 4c. SUMMABLE dither eta_n = 1/(n+2)^2, strictly alternating sides (N={N}) --")
    quotes = [HALF + alt_sides[n] * F(1, (n + 2) ** 2) for n in range(N)]
    gate_table(quotes, N)
    print("  reading: the PATIENT hard gate (yesterday's side, ledger-readable) pins the")
    print("  bias at ~ -1/2: a past-predictable side pattern is killed by a patient gate.")
    print("\nIsolated crux: on the summable, side-balanced, past-unpredictable dither,")
    print("every gate in this library fails; whether some legal C_A-gate must succeed")
    print("against A's OWN quote sides is exactly the open step named in the writeup.")


if __name__ == "__main__":
    run_part1()
    run_part2()
    run_part3()
    run_part4()
