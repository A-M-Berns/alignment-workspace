"""Eventual against timely service, normalized transport error, and the
canonical Sharp Timely Service bound.

Three things this module makes exact:

- the **diagonal** assignment, which serves each claim at its own cheap date and
  shows that persistence and eventual full service are the same existence
  question when the total claim mass diverges;
- the **normalized** transport error, an average per unit of claim mass rather
  than a raw sum, which is what the claim-weighted Progress bound consumes;
- the finite-horizon Sharp Timely Service bound, kept in squared form so the
  arithmetic stays rational.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence


# --- the diagonal assignment ---------------------------------------------


def diagonal_assignment(claims: Sequence[Fraction], weights: Sequence[Fraction],
                        budget: Fraction) -> list[int] | None:
    """Serve claim `t` at a later date whose charge fits the tranche `B 2^-(t+1)`.

    Returns the service date per positive claim, or `None` if the horizon runs
    out. Linear date costs, so the charge for claim mass `c` at date `s` is
    `c w_s`.
    """
    out = []
    cursor = 0
    for t, c in enumerate(claims):
        if c == 0:
            continue
        tranche = budget / 2 ** (len(out) + 1)
        found = None
        for s in range(max(cursor + 1, t), len(weights)):
            if c * weights[s] <= tranche:
                found = s
                break
        if found is None:
            return None
        out.append(found)
        cursor = found
    return out


def diagonal_charge(claims: Sequence[Fraction], weights: Sequence[Fraction],
                    dates: Sequence[int]) -> Fraction:
    positive = [c for c in claims if c > 0]
    return sum((c * weights[s] for c, s in zip(positive, dates)), Fraction(0))


# --- normalized transport error ------------------------------------------


def normalized_transport_error(plan: dict[tuple[int, int], Fraction],
                               error: dict[tuple[int, int], Fraction],
                               claim_mass: Fraction) -> Fraction:
    """`(1/C_N) sum_{t,s} T(t,s) eps(t,s)` — an average per unit of claim mass.

    The raw sum is the wrong object: the claim-weighted Progress bound is an
    average, so the transport contribution has to be one too.
    """
    if claim_mass <= 0:
        raise ValueError("no claim mass to normalize against")
    total = sum((mass * error[edge] for edge, mass in plan.items()),
                Fraction(0))
    return total / claim_mass


def modulus_error(plan: dict[tuple[int, int], Fraction],
                  modulus) -> dict[tuple[int, int], Fraction]:
    """`eps(t,s) = omega(s - t)` for forward service."""
    return {(t, s): modulus(s - t) for (t, s) in plan}


def uniform_delay_bound(plan: dict[tuple[int, int], Fraction],
                        modulus, delay: int) -> Fraction:
    """`omega(H)`, which dominates the normalized error of any plan with delay
    at most `H`."""
    for (t, s) in plan:
        if s - t > delay:
            raise ValueError("the plan exceeds the declared delay")
    return modulus(delay)


# --- the canonical bound, in squared form --------------------------------


def sharp_timely_root(budget: Fraction, ceiling: Fraction) -> Fraction:
    """`2 sqrt(B) + sqrt(U)`, exact when `4B` and `U` are perfect squares."""
    return _exact_sqrt(4 * budget) + _exact_sqrt(ceiling)


def sharp_timely_bound(budget: Fraction, ceiling: Fraction,
                       allocation: Fraction) -> Fraction:
    """`(2 sqrt(B) + sqrt(U)) / sqrt(A_N)`, the service-weighted defect bound."""
    if allocation <= 0:
        raise ValueError("no authority was allocated")
    return sharp_timely_root(budget, ceiling) / _exact_sqrt(allocation)


def claim_weighted_bound(budget: Fraction, ceiling: Fraction,
                         allocation: Fraction, lipschitz: Fraction,
                         cap: Fraction, transport: Fraction,
                         defect_bound: Fraction,
                         residual_density: Fraction) -> Fraction:
    """The full finite-horizon right-hand side of the canonical theorem."""
    return (lipschitz * cap * sharp_timely_bound(budget, ceiling, allocation)
            + transport + defect_bound * residual_density)


def _exact_sqrt(a: Fraction) -> Fraction:
    num, den = a.numerator, a.denominator
    rn, rd = _isqrt(num), _isqrt(den)
    if rn * rn != num or rd * rd != den:
        raise ValueError("square root is irrational; choose a perfect square")
    return Fraction(rn, rd)


def _isqrt(n: int) -> int:
    x = int(n ** 0.5)
    while x * x > n:
        x -= 1
    while (x + 1) * (x + 1) <= n:
        x += 1
    return x


# --- deadline insolvency --------------------------------------------------


def required_cost(claims: Sequence[Fraction], weights: Sequence[Fraction],
                  delay: int, now: int) -> Fraction:
    """The exact minimum charge for serving the arrived claims by their
    deadlines, on the linear branch: each claim at the cheapest *future* legal
    date."""
    total = Fraction(0)
    for t, c in enumerate(claims):
        if c == 0:
            continue
        window = [weights[s] for s in range(max(t, now), min(t + delay,
                                                            len(weights) - 1) + 1)]
        if not window:
            raise ValueError("a claim has no remaining legal date")
        total += c * min(window)
    return total


def deadline_insolvent(claims: Sequence[Fraction], weights: Sequence[Fraction],
                       delay: int, now: int,
                       slack: Fraction) -> tuple[bool, Fraction]:
    cost = required_cost(claims, weights, delay, now)
    return cost > slack, cost


# --- named fixtures -------------------------------------------------------


def shallow_dip_weights(blocks: int) -> list[Fraction]:
    """`w_{2^k} = 2^-k`, elsewhere `1` — the sequence the withdrawn countermodel
    used."""
    horizon = 2 ** blocks + 1
    out = [Fraction(1)] * horizon
    for k in range(blocks + 1):
        if 2 ** k < horizon:
            out[2 ** k] = Fraction(1, 2 ** k)
    return out


def bounded_gap_weights(pairs: int) -> list[Fraction]:
    """`w_{2k} = 1/k` and `w_{2k+1} = 1`: the cheap dates have gap two, the
    friction dips, and the sliding-window minima are not summable."""
    out = []
    for k in range(1, pairs + 1):
        out.append(Fraction(1, k))
        out.append(Fraction(1))
    return out
