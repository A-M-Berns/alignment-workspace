"""The joint service objective, and the hypotheses the batching theorem needs.

Three quantities a service schedule controls at once:

    liability        sum_s L_s(a_s)
    settlement friction   sum_s a_s r_s          (the numerator of F(a)^2)
    transport error  sum_{t,s} T(t,s) eps(t,s)

On the sharp charge's linear branch `L_s(a) = a s_s^2 / 4` and `r_s = s_s^2`, so
the first two are the *same* quantity up to a factor of four — which is the whole
content of `SHARP_SERVICEABILITY.md`.

This module also carries the counterexamples fixing the hypotheses of the
bounded-delay batching theorem: splitting can beat an atomic assignment when the
date cost is star-shaped but not concave, and a crossed assignment can beat every
monotone one when the claim masses differ.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Sequence

Cost = Callable[[Fraction], Fraction]


# --- the identity that drives the compression ----------------------------


def linear_branch_cost(depth: Fraction) -> Cost:
    """`L(a) = a s^2 / 4`, the sharp charge below its branch point."""
    return lambda a, s=depth: a * s ** 2 / 4


def friction_numerator(alloc: Sequence[Fraction],
                       depths: Sequence[Fraction]) -> Fraction:
    """`sum_t a_t D_t^2` — an upper bound on `sum_t a_t s_t(omega)^2` at every
    live world, since `D_t` is the supremum of the deficit over live worlds."""
    return sum((a * d ** 2 for a, d in zip(alloc, depths)), Fraction(0))


def linear_charge(alloc: Sequence[Fraction],
                  depths: Sequence[Fraction]) -> Fraction:
    return sum((a * d ** 2 / 4 for a, d in zip(alloc, depths)), Fraction(0))


def branch_points(depths: Sequence[Fraction],
                  scales: Sequence[Fraction]) -> list[Fraction]:
    """`4 m_t / s_t^2`; an allocation at or below this stays on the linear
    branch."""
    return [4 * m / s ** 2 for s, m in zip(depths, scales)]


def on_linear_branch(alloc: Sequence[Fraction], depths: Sequence[Fraction],
                     scales: Sequence[Fraction]) -> bool:
    return all(a <= p for a, p in
               zip(alloc, branch_points(depths, scales)))


# --- the combined per-claim score ----------------------------------------


def combined_score(weights: Sequence[Fraction], frictions: Sequence[Fraction],
                   delay_price: Fraction, liability_price: Fraction,
                   friction_price: Fraction, claim: int,
                   date: int) -> Fraction:
    """`lambda w_s + mu r_s + eps(t,s)` with a linear delay error."""
    return (liability_price * weights[date]
            + friction_price * frictions[date]
            + delay_price * (date - claim))


def best_date(weights: Sequence[Fraction], frictions: Sequence[Fraction],
              delay_price: Fraction, liability_price: Fraction,
              friction_price: Fraction, claim: int, delay: int) -> int:
    window = range(claim, min(claim + delay, len(weights) - 1) + 1)
    return min(window, key=lambda s: combined_score(
        weights, frictions, delay_price, liability_price, friction_price,
        claim, s))


# --- counterexamples fixing the batching hypotheses ----------------------


def star_shaped_not_concave() -> Cost:
    """`L(a) = min(a, 1)` up to `2`, then `a/2`.

    `L(a)/a` is nonincreasing, so the cost is star-shaped; the slope runs
    `1, 0, 1/2`, so it is not concave.
    """
    def cost(a: Fraction) -> Fraction:
        if a <= 1:
            return a
        if a <= 2:
            return Fraction(1)
        return a / 2
    return cost


def splitting_beats_atomic() -> dict:
    """Two legal dates each already carrying load `1`, and a claim of mass `2`.

    Atomic: one date goes to load `3` at cost `3/2`, the other stays at `1` at
    cost `1`. Split evenly: both reach load `2` at cost `1` each.
    """
    cost = star_shaped_not_concave()
    atomic = cost(Fraction(3)) + cost(Fraction(1))
    split = cost(Fraction(2)) + cost(Fraction(2))
    return {"cost": cost, "atomic": atomic, "split": split}


def crossed_beats_monotone() -> dict:
    """Concave costs, unequal claim masses, and a crossed assignment that wins.

    Claim one has mass `1` at date `1` with window `[1,3]`; claim two has mass
    `10` at date `2` with window `[2,4]`. Date two's cost saturates and date
    three's does not, so sending the big claim to the cheap saturating date and
    the small one to the expensive date beats the monotone assignment.
    """
    def flat(a: Fraction) -> Fraction:
        return min(a, Fraction(1) + a / 100)

    def half(a: Fraction) -> Fraction:
        return a / 2

    crossed = half(Fraction(1)) + flat(Fraction(10))
    monotone = flat(Fraction(1)) + half(Fraction(10))
    return {"flat": flat, "half": half,
            "crossed": crossed, "monotone": monotone}


# --- eventual against uniform service ------------------------------------


def geometric_dip_weights(blocks: int) -> list[Fraction]:
    """`w_t = 1` except `w_{2^k} = 4^-k`; the gaps between dips diverge."""
    horizon = 2 ** blocks + 1
    out = [Fraction(1)] * horizon
    for k in range(blocks + 1):
        if 2 ** k < horizon:
            out[2 ** k] = Fraction(1, 4 ** k)
    return out


def eventual_service_cost(blocks: int) -> Fraction:
    """Batch the claims of `(2^k, 2^{k+1}]` onto the dip at `2^{k+1}`.

    Unbounded delay, every claim served, and the total is summable.
    """
    total = Fraction(0)
    for k in range(blocks):
        mass = Fraction(2 ** k)
        weight = Fraction(1, 4 ** (k + 1))
        total += mass * weight
    return total


def uniform_delay_misses(blocks: int, delay: int) -> int:
    """How many claims have window minimum `1` at a fixed deadline — the dates
    more than `delay` after the last dip and before the next."""
    weights = geometric_dip_weights(blocks)
    count = 0
    for t in range(len(weights)):
        window = weights[t:t + delay + 1]
        if window and min(window) == Fraction(1):
            count += 1
    return count


def shallow_dip_weights(blocks: int) -> list[Fraction]:
    """`w_{2^k} = 2^-k`: dips too shallow to carry the block they must absorb,
    so even unbounded-delay full service is unaffordable while persistence
    holds."""
    horizon = 2 ** blocks + 1
    out = [Fraction(1)] * horizon
    for k in range(blocks + 1):
        if 2 ** k < horizon:
            out[2 ** k] = Fraction(1, 2 ** k)
    return out


def shallow_eventual_cost(blocks: int) -> Fraction:
    total = Fraction(0)
    for k in range(blocks):
        total += Fraction(2 ** k) * Fraction(1, 2 ** (k + 1))
    return total
