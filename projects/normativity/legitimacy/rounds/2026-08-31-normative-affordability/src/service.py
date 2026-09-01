"""Allocated service against realized force.

Two reason-indexed quantities, and the whole point of this module is that they are
different:

    a_{t,j} = beta_{t,j}                 allocated authority — predictable
    f_{t,j} = a_{t,j} d_{t,j}            realized corrective force — endogenous

`d_{t,j} = g_{t,j}(P_t)` is the row violation at the market maker's fixed point,
so `f` is not available when the round's control is chosen. The enforcement
modulus bounds the *work* per date,

    sum_j a_{t,j} d_{t,j}^2  <=  slack_t + volume_t ,

which is what makes `a` a usable service variable and `f` an unusable one.

Everything is exact rationals over a finite date range.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence


def conformance_ceiling(alloc: Fraction, budget: Fraction) -> Fraction:
    """The largest violation the modulus permits: `d <= sqrt(budget / a)`.

    Returned squared, since the square root is irrational in general and every
    statement the theory uses is about `d^2`.
    """
    if alloc <= 0:
        raise ValueError("allocated authority is positive")
    return budget / alloc


def capacity(budget: Fraction, allowance: Fraction, depth: Fraction) -> Fraction:
    """`beta <= b^2 / ((eps + M) D^2)` — the authority a per-date liability
    allowance `b` buys, given the date's slack-plus-volume and the worst live
    exclusion depth."""
    if depth <= 0:
        raise ValueError("a zero-depth date has no liability ceiling to invert")
    return allowance ** 2 / (budget * depth ** 2)


class ServiceTrajectory:
    """Dated allocation, realized violation, and signed misfit at one world."""

    def __init__(self, alloc: Sequence[Fraction], defect: Sequence[Fraction],
                 misfit: Sequence[Fraction] | None = None):
        if len(alloc) != len(defect):
            raise ValueError("one violation per allocation")
        if any(a < 0 for a in alloc) or any(d < 0 for d in defect):
            raise ValueError("allocation and violation are nonnegative")
        self.alloc = list(alloc)
        self.defect = list(defect)
        self.misfit = list(misfit) if misfit is not None else [Fraction(0)] * len(alloc)

    # --- the two candidate service measures ------------------------------

    def allocation_total(self) -> Fraction:
        """`A_N = sum a_t` — the predictable service mass."""
        return sum(self.alloc, Fraction(0))

    def force_total(self) -> Fraction:
        """`sum a_t d_t` — PR75's `W_N`, the realized force mass."""
        return sum((a * d for a, d in zip(self.alloc, self.defect)), Fraction(0))

    def allocation_measure(self) -> list[Fraction]:
        total = self.allocation_total()
        if total == 0:
            raise ValueError("no authority was allocated")
        return [a / total for a in self.alloc]

    def force_measure(self) -> list[Fraction]:
        total = self.force_total()
        if total == 0:
            raise ValueError("no force was realized")
        return [a * d / total for a, d in zip(self.alloc, self.defect)]

    # --- the quantities the theorem uses ----------------------------------

    def work_total(self) -> Fraction:
        """`Q_N = sum a_t d_t^2`, what the enforcement modulus bounds."""
        return sum((a * d * d for a, d in zip(self.alloc, self.defect)),
                   Fraction(0))

    def charge_total(self) -> Fraction:
        """`sum a_t d_t s_t`, the misfit charge at the trajectory's world."""
        return sum((a * d * s for a, d, s in
                    zip(self.alloc, self.defect, self.misfit)), Fraction(0))

    def account(self) -> Fraction:
        """`V_N = sum a_t (d_t^2 - d_t s_t)`."""
        return self.work_total() - self.charge_total()

    def expect_defect(self) -> Fraction:
        """`E_{nu^a}[d]`."""
        return sum((m * d for m, d in
                    zip(self.allocation_measure(), self.defect)), Fraction(0))

    def expect_square(self) -> Fraction:
        """`E_{nu^a}[d^2] = Q_N / A_N`."""
        return self.work_total() / self.allocation_total()

    def expect_misfit_square(self) -> Fraction:
        return sum((m * s * s for m, s in
                    zip(self.allocation_measure(), self.misfit)), Fraction(0))

    def obeys_modulus(self, budgets: Sequence[Fraction]) -> bool:
        """`a_t d_t^2 <= budget_t` at every date — the per-date enforcement
        modulus, which is what a legal trajectory must satisfy."""
        return all(a * d * d <= b for a, d, b
                   in zip(self.alloc, self.defect, budgets))


# --- named fixtures -------------------------------------------------------


def perfect_compliance(horizon: int) -> ServiceTrajectory:
    """Authority allocated at every date, and nothing to correct."""
    return ServiceTrajectory([Fraction(1)] * horizon, [Fraction(0)] * horizon)


def successful_learning(horizon: int) -> ServiceTrajectory:
    """Constant authority, geometrically vanishing violation.

    Allocated service diverges; realized force is summable. The reason is
    monitored forever and becomes nearly perfectly satisfied.
    """
    alloc = [Fraction(1)] * horizon
    defect = [Fraction(1, 2 ** t) for t in range(horizon)]
    misfit = [Fraction(1, 2 ** t) for t in range(horizon)]
    return ServiceTrajectory(alloc, defect, misfit)


def saturating(horizon: int) -> ServiceTrajectory:
    """Authority growing quadratically, violation held at the modulus ceiling.

    `a_t = t^2` and `d_t = 1/t` give `a_t d_t^2 = 1`, so the work grows linearly
    while the allocation grows cubically and the mean-square defect vanishes.
    """
    alloc, defect, misfit = [], [], []
    for t in range(1, horizon + 1):
        alloc.append(Fraction(t * t))
        defect.append(Fraction(1, t))
        misfit.append(Fraction(1, 2 ** t))
    return ServiceTrajectory(alloc, defect, misfit)


def friction_floor(horizon: int, floor: Fraction) -> ServiceTrajectory:
    """A norm whose misfit does not vanish: the violation settles at the floor
    and the mean-square defect does not go below it."""
    alloc = [Fraction(1)] * horizon
    defect = [floor] * horizon
    misfit = [floor] * horizon
    return ServiceTrajectory(alloc, defect, misfit)
