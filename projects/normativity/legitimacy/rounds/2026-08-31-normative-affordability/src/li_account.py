"""The traderized authority account, in the coordinates the source uses.

A row `<c, x> >= r` over a priced fragment. At a displayed price `P` its
**violation** is `g(P) = max(0, r - <c, P>)`; at an assessment world `W` its
**deficit** is `d(W) = max(0, r - <c, W>)`. The compiled enforcement position is

    zeta(P) = sum_j beta_j g_j(P) c_j ,

and its value in a world is `<zeta(P), W - P>`.

Two derived quantities carry the whole account, and keeping them apart is the
point of this module:

    work(P)      = sum_j beta_j g_j(P)^2            what force does at the price
    charge(P, W) = sum_j beta_j g_j(P) d_j(W)       what the world charges for it

The value is at least `work - charge`, with equality when every violated row also
excludes the world. `size(P) = sum_j beta_j g_j(P)` is the intensity variable: it
is the position's row-weighted magnitude, and it is what plays the role of
service intensity in the schematic.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

Vector = Sequence[Fraction]


def dot(u: Vector, v: Vector) -> Fraction:
    return sum((a * b for a, b in zip(u, v)), Fraction(0))


class Row:
    def __init__(self, c: Vector, r: Fraction):
        self.c = list(c)
        self.r = r

    def violation(self, price: Vector) -> Fraction:
        return max(Fraction(0), self.r - dot(self.c, price))

    def deficit(self, world: Vector) -> Fraction:
        return max(Fraction(0), self.r - dot(self.c, world))

    def signed_misfit(self, world: Vector) -> Fraction:
        """`r - <c, W>`, unclipped: positive where the world violates the row and
        negative where it satisfies it with room. The value identity is exact in
        this quantity; the clipped `deficit` is what bounds liability."""
        return self.r - dot(self.c, world)

    def excludes(self, world: Vector) -> bool:
        return self.deficit(world) > 0


class Enforcement:
    """One date's compiled position: rows with intensities."""

    def __init__(self, rows: Sequence[Row], betas: Sequence[Fraction]):
        if len(rows) != len(betas):
            raise ValueError("one intensity per row")
        self.rows = list(rows)
        self.betas = list(betas)

    def position(self, price: Vector) -> list[Fraction]:
        dim = len(price)
        out = [Fraction(0)] * dim
        for row, beta in zip(self.rows, self.betas):
            g = row.violation(price)
            if g == 0:
                continue
            for i in range(dim):
                out[i] += beta * g * row.c[i]
        return out

    def value(self, price: Vector, world: Vector) -> Fraction:
        return dot(self.position(price), [w - p for w, p in zip(world, price)])

    def work(self, price: Vector) -> Fraction:
        return sum((beta * row.violation(price) ** 2
                    for row, beta in zip(self.rows, self.betas)), Fraction(0))

    def charge(self, price: Vector, world: Vector) -> Fraction:
        return sum((beta * row.violation(price) * row.deficit(world)
                    for row, beta in zip(self.rows, self.betas)), Fraction(0))

    def signed_charge(self, price: Vector, world: Vector) -> Fraction:
        return sum((beta * row.violation(price) * row.signed_misfit(world)
                    for row, beta in zip(self.rows, self.betas)), Fraction(0))

    def size(self, price: Vector) -> Fraction:
        return sum((beta * row.violation(price)
                    for row, beta in zip(self.rows, self.betas)), Fraction(0))

    def max_gain(self, price: Vector) -> Fraction:
        """`max over cube vertices of value` — the market maker's contract side."""
        zeta = self.position(price)
        return sum((max(z * (1 - p), z * (0 - p)) for z, p in zip(zeta, price)),
                   Fraction(0))


class Trajectory:
    """A dated sequence of (price, enforcement) with a live-world family."""

    def __init__(self, steps: Sequence[tuple[Vector, Enforcement]],
                 worlds: Sequence[Vector]):
        self.steps = [(list(p), e) for p, e in steps]
        self.worlds = [list(w) for w in worlds]

    def horizon(self) -> int:
        return len(self.steps)

    def cumulative_value(self, world: Vector) -> Fraction:
        return sum((e.value(p, world) for p, e in self.steps), Fraction(0))

    def prefix_values(self, world: Vector) -> list[Fraction]:
        out, total = [], Fraction(0)
        for p, e in self.steps:
            total += e.value(p, world)
            out.append(total)
        return out

    def liability(self) -> Fraction:
        """`B` — the least bound with every prefix value at least `-B`, over the
        live worlds. This is the signed cumulative account with a floor, not a
        sum of per-date worst cases."""
        worst = Fraction(0)
        for world in self.worlds:
            for value in self.prefix_values(world):
                worst = max(worst, -value)
        return worst

    def per_date_robust_loss(self) -> list[Fraction]:
        """`sup over live worlds of the date's loss`, date by date.

        Summing this is the certificate route, and it is strictly conservative:
        the criterion follows one world through time, while this takes a fresh
        supremum at every date.
        """
        out = []
        for p, e in self.steps:
            out.append(max((-e.value(p, w) for w in self.worlds), default=Fraction(0)))
        return [max(Fraction(0), x) for x in out]

    def certificate_charge(self) -> Fraction:
        return sum(self.per_date_robust_loss(), Fraction(0))

    def total_size(self) -> Fraction:
        return sum((e.size(p) for p, e in self.steps), Fraction(0))

    def work_total(self) -> Fraction:
        return sum((e.work(p) for p, e in self.steps), Fraction(0))

    def charge_total(self, world: Vector) -> Fraction:
        return sum((e.charge(p, world) for p, e in self.steps), Fraction(0))

    def service_measure(self) -> list[Fraction]:
        """`nu_N` over dates, weighted by position size."""
        sizes = [e.size(p) for p, e in self.steps]
        total = sum(sizes, Fraction(0))
        if total == 0:
            raise ValueError("no force was applied")
        return [s / total for s in sizes]

    def size_weighted(self, values: Sequence[Fraction]) -> Fraction:
        return sum((m * v for m, v in zip(self.service_measure(), values)),
                   Fraction(0))

    def defects(self) -> list[Fraction]:
        """The size-weighted mean violation at each date."""
        out = []
        for p, e in self.steps:
            size = e.size(p)
            if size == 0:
                out.append(Fraction(0))
                continue
            out.append(sum((beta * row.violation(p) ** 2
                            for row, beta in zip(e.rows, e.betas)),
                           Fraction(0)) / size)
        return out

    def misfits(self, world: Vector) -> list[Fraction]:
        """The size-weighted mean deficit at each date, at one world."""
        out = []
        for p, e in self.steps:
            size = e.size(p)
            if size == 0:
                out.append(Fraction(0))
                continue
            out.append(e.charge(p, world) / size)
        return out

    def signed_misfits(self, world: Vector) -> list[Fraction]:
        """The size-weighted mean *signed* misfit at each date.

        `E_nu[d] - E_nu[signed misfit] = V_N(world) / W_N` is an identity at every
        world, which the clipped version is only where every violated row also
        excludes the world.
        """
        out = []
        for p, e in self.steps:
            size = e.size(p)
            if size == 0:
                out.append(Fraction(0))
                continue
            out.append(e.signed_charge(p, world) / size)
        return out


# --- named fixtures -------------------------------------------------------


def alternating_norm(horizon: int, beta: Fraction = Fraction(8)) -> Trajectory:
    """A norm that alternates which world it excludes, at a fixed price.

    One priced sentence; the two assessment worlds are `0` and `1`; the price is
    held at `1/2`. On even dates the row is `P >= 3/4`, which excludes world `0`;
    on odd dates it is `P <= 1/4`, which excludes world `1`. Every date shows a
    real loss in some live world, and the cumulative account in each world
    oscillates within a fixed band.
    """
    up = Row([Fraction(1)], Fraction(3, 4))
    down = Row([Fraction(-1)], Fraction(-1, 4))
    price = [Fraction(1, 2)]
    steps = [(price, Enforcement([up if t % 2 == 0 else down], [beta]))
             for t in range(horizon)]
    return Trajectory(steps, [[Fraction(0)], [Fraction(1)]])


def decaying_depth(horizon: int) -> Trajectory:
    """A norm excluding the sole live world at every date, enforced forever.

    One sentence, settled true, so the only live world is `1`. The row is
    `P <= 1 - 2^-t`, which excludes it at every date; the displayed price sits at
    `1 - 2^-(t+2)`, so the row is violated at every date. Every date is a real
    loss in the live world and the account still converges.
    """
    steps = []
    for t in range(horizon):
        depth = Fraction(1, 2 ** t)
        row = Row([Fraction(-1)], -(Fraction(1) - depth))
        price = [Fraction(1) - depth / 4]
        steps.append((price, Enforcement([row], [Fraction(1)])))
    return Trajectory(steps, [[Fraction(1)]])


def fixed_depth(horizon: int) -> Trajectory:
    """The same shape with the exclusion depth held fixed: the account diverges."""
    row = Row([Fraction(-1)], Fraction(-1, 2))
    price = [Fraction(3, 4)]
    steps = [(price, Enforcement([row], [Fraction(1)])) for _ in range(horizon)]
    return Trajectory(steps, [[Fraction(1)]])


def compatible_world(horizon: int) -> Trajectory:
    """A row a live world satisfies, and another live world does not.

    Progress reads the account at the *best* live world and needs only one
    compatible world; liability reads it at the worst and does not.
    """
    row = Row([Fraction(1)], Fraction(3, 4))
    price = [Fraction(1, 2)]
    steps = [(price, Enforcement([row], [Fraction(1)])) for _ in range(horizon)]
    return Trajectory(steps, [[Fraction(1)], [Fraction(0)]])
