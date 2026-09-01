"""Persistent affordability: the sequence problem and its causal scheduler.

The conservative worst-case charge for allocating authority `a_t` against a
friction `q_t = D_t sqrt(m_t)` is `q_t sqrt(a_t)`. Writing `x_t = sqrt(a_t)`, a
schedule is affordable and persistent exactly when

    sum_t x_t^2 = infinity      and      sum_t q_t x_t <= B .

Everything here is parametrized by `x` rather than `a`, so no square root is ever
taken and all arithmetic is exact.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence


def authority(x: Sequence[Fraction]) -> list[Fraction]:
    """`a_t = x_t^2`."""
    return [xi * xi for xi in x]


def cumulative_authority(x: Sequence[Fraction]) -> Fraction:
    return sum((xi * xi for xi in x), Fraction(0))


def charge(q: Sequence[Fraction], x: Sequence[Fraction]) -> Fraction:
    return sum((qi * xi for qi, xi in zip(q, x)), Fraction(0))


def max_authority(q: Sequence[Fraction], budget: Fraction) -> Fraction:
    """`max { sum x^2 : x >= 0, <q, x> <= B } = B^2 / (min q)^2`.

    The objective is convex on a simplex-shaped feasible set, so the maximum sits
    at a vertex `B/q_t · e_t`, and the best vertex is the smallest `q_t`.
    """
    smallest = min(q)
    if smallest <= 0:
        raise ValueError("a zero-friction date makes the maximum infinite")
    return budget ** 2 / smallest ** 2


def optimal_concentration(q: Sequence[Fraction], budget: Fraction) -> list[Fraction]:
    """The maximizing schedule: the whole budget on one least-friction date."""
    smallest = min(q)
    index = list(q).index(smallest)
    out = [Fraction(0)] * len(q)
    out[index] = budget / smallest
    return out


# --- the causal scheduler -------------------------------------------------


def doubling_schedule(q: Sequence[Fraction], budget: Fraction,
                      thresholds: Sequence[Fraction] | None = None
                      ) -> list[Fraction]:
    """A causal rule seeing `q_t` at date `t` and choosing `x_t` immediately.

    Hold a threshold `theta_k` and a tranche `b_k = B 2^-(k+1)`. On the first
    date whose friction is at most `theta_k`, spend the tranche in full —
    `x_t = b_k / q_t`, so `a_t = (b_k/q_t)^2 >= (b_k/theta_k)^2` — and advance
    `k`. The tranches sum to at most `B`, and with `theta_k = 2^-k` every trigger
    contributes at least `B^2/4` to the cumulative authority.
    """
    if thresholds is None:
        thresholds = [Fraction(1, 2 ** k) for k in range(len(q) + 1)]
    out = [Fraction(0)] * len(q)
    k = 0
    for t, qt in enumerate(q):
        if k >= len(thresholds):
            break
        if qt <= thresholds[k]:
            tranche = budget / 2 ** (k + 1)
            out[t] = tranche / qt
            k += 1
    return out


def triggers(q: Sequence[Fraction],
             thresholds: Sequence[Fraction] | None = None) -> int:
    if thresholds is None:
        thresholds = [Fraction(1, 2 ** k) for k in range(len(q) + 1)]
    count, k = 0, 0
    for qt in q:
        if k < len(thresholds) and qt <= thresholds[k]:
            count += 1
            k += 1
    return count


# --- signed account against the conservative certificate ------------------


def conservative_charge(q: Sequence[Fraction], x: Sequence[Fraction]) -> Fraction:
    return charge(q, x)


def realized_account(x: Sequence[Fraction], defect: Sequence[Fraction],
                     misfit: Sequence[Fraction]) -> Fraction:
    """`sum_t a_t d_t (d_t - s_t)` on the realized trajectory."""
    return sum((xi * xi * d * (d - s)
                for xi, d, s in zip(x, defect, misfit)), Fraction(0))


# --- account profiles -----------------------------------------------------


class Profile:
    """The account read at each live world, with the live set attached."""

    def __init__(self, values: dict[str, Fraction], live: Sequence[str]):
        self.values = dict(values)
        self.live = list(live)

    def slack(self, floor: Fraction) -> Fraction:
        """`B + min over live worlds` — the scalar Route B uses."""
        return floor + min(self.values[w] for w in self.live)

    def settle(self, survivors: Sequence[str]) -> "Profile":
        """Settlement removes worlds; the profile is unchanged on the rest."""
        for w in survivors:
            if w not in self.live:
                raise ValueError("settlement cannot revive a world")
        return Profile(self.values, survivors)


# --- named fixtures -------------------------------------------------------


def sparse_friction(horizon: int) -> list[Fraction]:
    """Friction pinned at 1 except on the dates `2^k - 1`, where it is `4^-k`."""
    out = []
    k, nxt = 0, 0
    for t in range(horizon):
        if t == nxt:
            out.append(Fraction(1, 4 ** k))
            k += 1
            nxt = 2 ** k - 1
        else:
            out.append(Fraction(1))
    return out


def flat_friction(horizon: int, level: Fraction = Fraction(1)) -> list[Fraction]:
    return [level] * horizon


def decaying_friction(horizon: int) -> list[Fraction]:
    return [Fraction(1, 2 ** t) for t in range(horizon)]
