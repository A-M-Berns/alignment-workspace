"""The Part B fixture in exact rationals, and the two market exhibits.

Four sentences `X, X∧A, X∧A∧Y, Y` on the atoms `X, A, Y`; one warrant occurrence with
strengths `c_P, c_A, c_S` in `(0, 1)`; the three rows it compiles to; the signed gap of
every world on every row; the odds bankroll `3 · max_j c_j/(1 − c_j)`; and two
single-row market exhibits — a budgeted counterparty against a live slack world (the
realized liability stays under the odds bound) and a harmonic buyer against the orphaned
strength row (the realized liability grows without bound while the buyer's budget spend
converges).

Everything is `fractions.Fraction`.  The market maker is the one-coordinate fixed point
that zeroes the aggregate position when it can, which is one valid selection under the
market maker's contract; the exhibits are `test-supported`, not kernel-checked.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

# ---------------------------------------------------------------------------
# Worlds and the priced fragment

COORDS = ("X", "XA", "XAY", "Y")


def payout(x: int, a: int, y: int) -> dict[str, F]:
    """The payout vector of the propositionally consistent world with these atoms."""
    return {"X": F(x), "XA": F(x and a), "XAY": F(x and a and y), "Y": F(y)}


WORLDS = {(x, a, y): payout(x, a, y) for x, a, y in product((0, 1), repeat=3)}
ALL_TRUE = (1, 1, 1)


# ---------------------------------------------------------------------------
# Rows: ⟨coeff, P⟩ ≥ rhs

@dataclass(frozen=True)
class Row:
    name: str
    coeff: dict[str, F]
    rhs: F

    def pairing(self, w: dict[str, F]) -> F:
        return sum((c * w[k] for k, c in self.coeff.items()), F(0))

    def gap(self, w: dict[str, F]) -> F:
        """Signed: positive is surplus, negative is deficit."""
        return self.pairing(w) - self.rhs

    def deficit(self, w: dict[str, F]) -> F:
        return max(F(0), -self.gap(w))

    def satisfied(self, w: dict[str, F]) -> bool:
        return self.gap(w) >= 0


@dataclass(frozen=True)
class Strengths:
    P: F
    A: F
    S: F

    def check(self) -> None:
        for c in (self.P, self.A, self.S):
            if not (F(0) < c < F(1)):
                raise ValueError("strengths lie strictly between 0 and 1")


def premise_row(c: Strengths) -> Row:
    return Row("premise", {"X": F(1)}, c.P)


def applicability_row(c: Strengths) -> Row:
    return Row("applicability", {"XA": F(1), "X": -c.A}, F(0))


def strength_row(c: Strengths) -> Row:
    return Row("strength", {"XAY": F(1), "XA": -c.S}, F(0))


def rows(c: Strengths, applicability_live: bool = True) -> list[Row]:
    out = [premise_row(c)]
    if applicability_live:
        out.append(applicability_row(c))
    out.append(strength_row(c))
    return out


# ---------------------------------------------------------------------------
# The odds bankroll

def odds(c: F) -> F:
    return c / (1 - c)


def rho(c: Strengths) -> F:
    return max(odds(c.P), odds(c.A), odds(c.S))


MARKET_CAPITAL = F(3)  # the market maker's 1 plus the trading firm's floor 2


def bankroll(c: Strengths) -> F:
    return MARKET_CAPITAL * rho(c)


def gap_dominated(c: Strengths, r: F | None = None) -> bool:
    """Every world's deficit on every row is at most `ρ` times the all-true world's
    surplus on that row — the hypothesis of `netWorth_ge_neg_odds`, checked at every
    propositionally consistent world, not only the live ones."""
    r = rho(c) if r is None else r
    w_star = WORLDS[ALL_TRUE]
    return all(-row.gap(w) <= r * row.gap(w_star)
               for row in rows(c) for w in WORLDS.values())


def minimal_rho(c: Strengths) -> F:
    """The least `ρ` for which domination holds: the maximum over rows of the worst
    deficit over the all-true surplus."""
    w_star = WORLDS[ALL_TRUE]
    return max(max(row.deficit(w) for w in WORLDS.values()) / row.gap(w_star)
               for row in rows(c))


# ---------------------------------------------------------------------------
# Settlement semantics as live sets

def live(x_settled: bool, y_eval: bool | None) -> dict[tuple[int, int, int], dict[str, F]]:
    """The live worlds under a settlement state: `X` true if settled, `Y` equal to the
    evaluation if one has landed.  Deductive settlement, evaluation settlement and the
    pegged reading are the same object seen at different states."""
    return {k: w for k, w in WORLDS.items()
            if (not x_settled or k[0] == 1) and (y_eval is None or k[2] == int(y_eval))}


def slack_world_exists(c: Strengths, live_worlds, row_list) -> bool:
    """Some live world clears every listed row strictly."""
    return any(all(row.gap(w) > 0 for row in row_list) for w in live_worlds.values())


def region_points(c: Strengths, row_list, x_pin: F | None, xay_pin: F | None,
                  y_pin: F | None, grid: int = 20) -> list[dict[str, F]]:
    """Rational grid points of the forced region under the given pins (a brute-force
    check of emptiness/nonemptiness; the Lean file carries the exact proofs)."""
    pts = []
    vals = [F(i, grid) for i in range(grid + 1)]
    for x in ([x_pin] if x_pin is not None else vals):
        for xa in vals:
            for xay in ([xay_pin] if xay_pin is not None else vals):
                for y in ([y_pin] if y_pin is not None else vals):
                    p = {"X": x, "XA": xa, "XAY": xay, "Y": y}
                    if all(r.satisfied(p) for r in row_list):
                        pts.append(p)
    return pts


# ---------------------------------------------------------------------------
# One-coordinate market exhibits

def maker_price(r: F, beta: F, k: F) -> F:
    """The price of a sentence the enforcer demands `P ≥ r` at intensity `β`, against a
    counterparty selling `k` units.  The enforcer holds `β·max(0, r − p)` units; the
    maker zeroes the aggregate when it can (`p = r − k/β`), else prices at `0`."""
    p = r - k / beta
    return p if p >= 0 else F(0)


def maker_price_short(r_short: F, beta: F, k: F) -> F:
    """The price of a sentence the enforcer demands `P ≤ r_short` at intensity `β`
    (the orphaned strength row with `X∧A∧Y` pinned to `0` and `r_short = 0`), against a
    counterparty buying `k` units.  The enforcer sells `β·max(0, p − r_short)` units; the
    maker zeroes the aggregate at `p = r_short + k/β`, capped at `1`."""
    p = r_short + k / beta
    return p if p <= 1 else F(1)


@dataclass
class Ledger:
    enforcer_at_deficit: F = F(0)   # the enforcer's cumulative value at the deficit world
    enforcer_at_slack: F = F(0)     # ... at the slack world
    counterparty_spend: F = F(0)    # the counterparty's cumulative loss at the slack world
    units: F = F(0)


def budgeted_seller_run(r: F, beta: F, budget: F, k_max: F, dates: int) -> Ledger:
    """A seller of the premise sentence against the row `P ≥ r`, limited to a cumulative
    loss of `budget` at the slack world (`X` true).  Per unit sold at `p` it loses `1 − p`
    there and gains `p` at the deficit world; the enforcer's book is the mirror image."""
    led = Ledger()
    k = k_max
    p = maker_price(r, beta, k)
    for _ in range(dates):
        # the budgeter admits the day's trade only if its loss at the slack world fits
        # the remaining budget; the seller's schedule is the declared constant `k_max`
        if led.counterparty_spend + k * (1 - p) > budget:
            break
        led.units += k
        led.counterparty_spend += k * (1 - p)
        led.enforcer_at_deficit -= k * p          # the enforcer bought k at p, pays out 0
        led.enforcer_at_slack += k * (1 - p)      # ... pays out 1
    return led


def harmonic_buyer_run(beta: F, c_S: F, dates: int) -> Ledger:
    """A buyer of `X∧A` against the orphaned strength row after `X∧A∧Y` is pinned to `0`:
    the row `P(X∧A∧Y) ≥ c_S P(X∧A)` reads `c_S P(X∧A) ≤ 0`, the enforcer sells
    `β c_S · max(0, c_S p)` units of `X∧A` whenever its price is positive, and the buyer
    takes `k_t = 1/(t+1)` units a day.  At the live world with `X∧A` true the enforcer
    pays out `1` per unit sold; at the live world with `X∧A` false the buyer loses `p`
    per unit — the only live world where the buyer loses anything, and the spend there is
    `Σ k_t p_t = Σ k_t² / (c_S² β)`, which converges."""
    led = Ledger()
    eff_beta = beta * c_S * c_S   # units sold per unit of price: β·c_S·(c_S p)/p
    for t in range(dates):
        k = F(1, t + 1)
        p = maker_price_short(F(0), eff_beta, k)
        led.units += k
        led.counterparty_spend += k * p           # the buyer's loss where X∧A is false
        led.enforcer_at_deficit -= k * (1 - p)    # the enforcer's loss where X∧A is true
        led.enforcer_at_slack += k * p            # its gain where X∧A is false
    return led


def harmonic(n: int) -> F:
    return sum((F(1, t + 1) for t in range(n)), F(0))


# ---------------------------------------------------------------------------
# Item 39, weak: two credal sets with the same projection and different live worlds

def same_projection_different_support() -> tuple[tuple, tuple, dict, dict]:
    """Two point masses on distinct worlds with identical payout vectors on the fragment:
    `A` is invisible when `X` is false.  Their projections coincide; their supports — the
    live worlds a semantic reading would derive — differ."""
    w1, w2 = (0, 0, 0), (0, 1, 0)
    return w1, w2, WORLDS[w1], WORLDS[w2]


# ---------------------------------------------------------------------------
# The fixture's declared numbers

FIXTURE = Strengths(F(4, 5), F(3, 4), F(2, 3))
N1 = 3   # X settled true
N0 = 5   # the applicability port defeated
NE = 8   # the evaluation of Y lands
BETA = F(10)
