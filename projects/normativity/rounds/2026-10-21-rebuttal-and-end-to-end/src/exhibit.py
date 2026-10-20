"""Two market exhibits under the rebuttal rule, exact rationals.

1. `nothing_to_buy`: after `Y` is refuted the enforcer holds no row on `X∧A`; the harmonic
   buyer of the warrant round meets a zero position and the enforcer's book does not move.
2. `cushion_exhibit`: the dispatch's "the same `3ρ`" after a rebuttal is not what the
   account gives.  A counterparty that sold `X∧A∧Y` against the strength row before the
   rebuttal is, after it, ahead by the reopened mass at every live world; the budget floor
   is on cumulative worth at live worlds, so it can sell `X∧A` against the applicability
   row with that cushion, and the enforcer's loss at the world `X` true, `A` false passes
   `3ρ`.  The construction is `odds_A · (2 + 3·odds_S)` on the fixture: `3 · (2 + 6) = 24 > 12`.

Both use the one-coordinate market maker of the warrant round's `fixture.py` (the maker
zeroes the aggregate); they are `test-supported`, not kernel-checked.
"""
from __future__ import annotations

from fractions import Fraction as F

from rebuttal import C, odds


def maker_price_long(r: F, beta: F, k: F) -> F:
    """Enforcer demands `P ≥ r`; counterparty sells `k`; maker zeroes the aggregate."""
    p = r - k / beta
    return p if p >= 0 else F(0)


def nothing_to_buy(beta: F, dates: int) -> dict:
    """After the rebuttal the enforcer holds no row on `X∧A`: its position in `X∧A` is `0`
    at every price, so a buyer of `X∧A` trades against the ordinary market only and the
    enforcer's book is unchanged."""
    position_in_XA = F(0)          # no live row names X∧A after nE
    enforcer_book = F(0)
    for t in range(dates):
        k = F(1, t + 1)
        enforcer_book += position_in_XA * k   # nothing changes hands with the enforcer
    return dict(position=position_in_XA, enforcer_book=enforcer_book, buyer_units=sum(F(1, t + 1) for t in range(dates)))


def cushion_exhibit(c_A: F = C["A"], c_S: F = C["S"], firm_floor: F = F(2), maker: F = F(1)) -> dict:
    """The two-phase exploit.  Phase 1 (before the rebuttal, `X` settled, `Y` open): the
    counterparty sells `X∧A∧Y` to the enforcer's strength row until its loss at the
    all-true world reaches the market's capital `maker + firm_floor = 3`; it sells `U_S`
    units at price `c_S` (the row's level with `P(X∧A) = 1`).  Phase 2 (`Y` refuted; live
    worlds `X` true with `A` true or false): every unit sold pays the counterparty `c_S`
    (the sentence is false), so its cumulative worth at both live worlds is
    `+c_S·U_S`; it may now lose `firm_floor + c_S·U_S` at the world `A` true by selling
    `X∧A` at `c_A` against the applicability row — `U_A = (firm_floor + c_S U_S)/(1 − c_A)`
    units — and at the world `A` false the enforcer loses `c_A` per unit."""
    capital = maker + firm_floor
    U_S = capital / (1 - c_S)                     # phase 1 volume, budget exhausted at all-true
    reopened_mass = c_S * U_S                     # the counterparty's gain at the live worlds
    U_A = (firm_floor + reopened_mass) / (1 - c_A)
    loss_A_false = c_A * U_A                      # the enforcer's loss at (X, ¬A, ¬Y)
    rho = max(odds(c_A), odds(c_S))
    return dict(U_S=U_S, reopened_mass=reopened_mass, U_A=U_A, loss=loss_A_false,
                three_rho=3 * rho, reopened_bound=3 * rho * (2 + rho),
                sharp_bound=odds(c_A) * (3 + 3 * odds(c_S)),
                # consistency with the maker's constant: the enforcer's worth at (X, A, ¬Y)
                enforcer_at_A_true=(1 - c_A) * U_A - reopened_mass)
