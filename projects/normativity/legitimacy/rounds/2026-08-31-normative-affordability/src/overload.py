"""Finite-horizon overload certificates.

The affordability program at horizon `N` with reason set `R`:

    choose  w_t in J_t = conv(V_t)  for each t < N,
    subject to   sum_t w_t^r >= demand_r        (service fidelity)
                 sum_t <cost_t, w_t> <= budget  (settlement-relative safety).

An **overload certificate** is a pair `(y, z)` with `y >= 0` on the demand rows
and `z >= 0` on the safety row whose deficit

    deficit = sum_r y_r demand_r - z budget
              - sum_t max_{v in V_t} ( <y, v> - z <cost_t, v> )

is strictly positive. A positive deficit proves the program infeasible; the
converse is not claimed here, and `EXISTENCE_AND_DUALITY.md` says exactly which
direction is sound for the causal problem.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

Vector = Sequence[Fraction]


def _dot(u: Vector, v: Vector) -> Fraction:
    return sum((a * b for a, b in zip(u, v)), Fraction(0))


class Program:
    def __init__(self, vertex_sets: Sequence[Sequence[Vector]],
                 costs: Sequence[Vector], demand: Vector, budget: Fraction):
        if len(vertex_sets) != len(costs):
            raise ValueError("one cost row per round")
        self.vertex_sets = [[list(v) for v in vs] for vs in vertex_sets]
        self.costs = [list(c) for c in costs]
        self.demand = list(demand)
        self.budget = budget

    def horizon(self) -> int:
        return len(self.vertex_sets)

    def deficit(self, y: Vector, z: Fraction) -> Fraction:
        if any(yi < 0 for yi in y) or z < 0:
            raise ValueError("certificate multipliers are nonnegative")
        supply = Fraction(0)
        for verts, cost in zip(self.vertex_sets, self.costs):
            supply += max(_dot(y, v) - z * _dot(cost, v) for v in verts)
        return _dot(y, self.demand) - z * self.budget - supply

    def certifies_overload(self, y: Vector, z: Fraction) -> bool:
        return self.deficit(y, z) > 0

    def admits(self, schedule: Sequence[Vector],
               weights: Sequence[Sequence[Fraction]]) -> bool:
        """Check a primal witness given as a convex combination per round."""
        if len(schedule) != self.horizon():
            return False
        served = [Fraction(0)] * len(self.demand)
        spent = Fraction(0)
        for w, verts, lam, cost in zip(schedule, self.vertex_sets, weights,
                                       self.costs):
            if len(lam) != len(verts) or any(li < 0 for li in lam):
                return False
            if sum(lam, Fraction(0)) != 1:
                return False
            rebuilt = [sum((li * v[i] for li, v in zip(lam, verts)), Fraction(0))
                       for i in range(len(w))]
            if rebuilt != list(w):
                return False
            for i, wi in enumerate(w):
                served[i] += wi
            spent += _dot(cost, w)
        if spent > self.budget:
            return False
        return all(s >= d for s, d in zip(served, self.demand))


def unit_capacity_program(horizon: int, reasons: int, budget: Fraction,
                          demand: Vector) -> Program:
    """Each round serves one unit of total intensity, and every unit costs one.

    The joint response set is the simplex on `reasons` coordinates together with
    the option of not acting.
    """
    verts: list[list[Fraction]] = [[Fraction(0)] * reasons]
    for r in range(reasons):
        v = [Fraction(0)] * reasons
        v[r] = Fraction(1)
        verts.append(v)
    cost = [Fraction(1)] * reasons
    return Program([verts] * horizon, [cost] * horizon, demand, budget)
