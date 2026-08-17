"""Semantic credal constraints, their price projections, and what projection loses.

Two objects, and the whole architecture turns on not confusing them.

The **semantic** object is a credal set `C_t ⊆ Δ(Ω_t)`: which probabilistic states
over worlds are admissible. It determines the live worlds, and therefore the
generalized exploitation criterion:

    Ω_t^live  =  { ω : ∃ μ ∈ C_t, μ(ω) > 0 } .

The **price-visible** object is its image under the pricing map,
`K_t = π_t(C_t)`, where `π_t(μ) = Σ_ω μ(ω)·ω` reads off the priced marginals.
That is all a trader can see, and all a trader can enforce.

Projection loses information. `π_t⁻¹(π_t(C))` — the **fibre saturation** of `C` —
contains `C` and is generally larger, so price-space membership does not
reconstruct semantic admissibility. The minimal witness is two priced sentences
with deduction admitting only `00` and `11`: the projection is `{p_A = p_B}`, and
the anticorrelated mixture `½·01 + ½·10` projects into it while putting all its
mass on deductively impossible worlds.

That is why semantics and force are two channels rather than one, and it is a
reason about information rather than about mechanism convenience.

Four types, never blurred: worlds, credences, price vectors, and the map between
the last two.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product
from typing import Sequence

from deduction import _solve, in_convex_hull
from enforcement import Region, Row
from market import ONE, ZERO, Vector, dot, holdings_value, max_gain


def price_of(credence: Sequence[Fraction],
             worlds: Sequence[Sequence[Fraction]]) -> Vector:
    """`π(μ)`: the priced marginals a credence induces."""
    if len(credence) != len(worlds):
        raise ValueError("one weight per world")
    return tuple(sum((m * w[i] for m, w in zip(credence, worlds)), ZERO)
                 for i in range(len(worlds[0])))


def is_credence(credence: Sequence[Fraction]) -> bool:
    return all(x >= 0 for x in credence) and sum(credence, ZERO) == ONE


class CredalSet:
    """`C ⊆ Δ(Ω)`, cut out of the simplex by rational rows in credence space.

    Rows are `⟪a, μ⟫ ≥ b` with `a` indexed by **worlds**, not by sentences. A
    constraint stated in price space becomes such a row by pulling back through
    the pricing map — `saturated_lift` does that, and names the choice, because
    the pullback is a lift and not the only one.
    """

    def __init__(self, worlds: Sequence[Sequence[Fraction]],
                 rows: Sequence[tuple[Sequence[Fraction], Fraction]] = ()) -> None:
        self.worlds = [tuple(Fraction(x) for x in w) for w in worlds]
        self.rows = [(tuple(Fraction(x) for x in a), Fraction(b)) for a, b in rows]

    @property
    def size(self) -> int:
        return len(self.worlds)

    def contains(self, credence: Sequence[Fraction]) -> bool:
        return is_credence(credence) and all(
            dot(a, credence) >= b for a, b in self.rows)

    def vertices(self) -> list[Vector]:
        """The vertices of `C`, exactly, by enumerating tight subsystems."""
        count = self.size
        inequalities: list[tuple[list[Fraction], Fraction]] = [
            ([ONE if k == i else ZERO for k in range(count)], ZERO)
            for i in range(count)]
        inequalities += [(list(a), b) for a, b in self.rows]
        found: list[Vector] = []
        for pick in combinations(range(len(inequalities)), count - 1):
            matrix = [inequalities[i][0] for i in pick] + [[ONE] * count]
            target = [inequalities[i][1] for i in pick] + [ONE]
            solution = _solve(matrix, target)
            if solution is None or any(x < 0 for x in solution):
                continue
            if any(sum((c * s for c, s in zip(coefficients, solution)), ZERO) < right
                   for coefficients, right in inequalities):
                continue
            candidate = tuple(solution)
            if candidate not in found:
                found.append(candidate)
        return found

    def support_capacity(self, index: int) -> Fraction:
        """`θ(ω) = max { μ(ω) : μ ∈ C }`, from `C` and not from any projection."""
        return max((v[index] for v in self.vertices()), default=ZERO)

    def live_worlds(self) -> list[Vector]:
        """`Ω^live`: the worlds some admissible credence gives positive mass."""
        return [w for i, w in enumerate(self.worlds)
                if self.support_capacity(i) > 0]

    def price_vertices(self) -> list[Vector]:
        """`π(vertices)`, whose convex hull is `π(C)` since `π` is linear."""
        out: list[Vector] = []
        for v in self.vertices():
            image = price_of(v, self.worlds)
            if image not in out:
                out.append(image)
        return out

    def projects_to(self, price: Sequence[Fraction]) -> bool:
        """Whether a price vector is in `π(C)`."""
        return in_convex_hull(price, self.price_vertices())

    def saturation_contains(self, credence: Sequence[Fraction]) -> bool:
        """Whether `μ ∈ π⁻¹(π(C))` — admissible *as far as prices can tell*."""
        return is_credence(credence) and self.projects_to(
            price_of(credence, self.worlds))


def delta_of(worlds: Sequence[Sequence[Fraction]],
             admitted: Sequence[Sequence[Fraction]]) -> CredalSet:
    """`Δ(S)`: every credence supported on a subset of the worlds.

    The deductive semantic constraint is this with `S = PC(D_t)`, and that is why
    deductive recovery needs no hypothesis about the pricing map: the live worlds
    of `Δ(S)` are `S` by the definition of support, in both directions.
    """
    rows = []
    for i, w in enumerate(worlds):
        if tuple(w) not in [tuple(a) for a in admitted]:
            basis = [ONE if k == i else ZERO for k in range(len(worlds))]
            rows.append(([-x for x in basis], ZERO))       # μ_i <= 0
    return CredalSet(worlds, rows)


def saturated_lift(worlds: Sequence[Sequence[Fraction]],
                   region: Region) -> CredalSet:
    """`π⁻¹(K)`: the credal set a **price-space** demand lifts to.

    A named choice, not a derivation. A source that supplies only a price-space
    region `K` has said nothing about which credences are admissible, and this is
    the largest lift consistent with what it did say. It is fibre-saturated by
    construction, so it is exactly the semantic state that price observations
    cannot distinguish from.
    """
    rows = []
    for row in region.rows:
        rows.append(([dot(row.c, w) for w in worlds], row.r))
    return CredalSet(worlds, rows)


def is_fibre_saturated(credal: CredalSet, denominator: int) -> bool:
    """Whether `C = π⁻¹(π(C))` on a rational grid of the simplex.

    A grid check, and labelled as one: it exhibits failures exactly and
    establishes equality only over the points it visited.
    """
    for weights in product(range(denominator + 1), repeat=credal.size):
        if sum(weights) != denominator:
            continue
        mu = [Fraction(w, denominator) for w in weights]
        if credal.saturation_contains(mu) and not credal.contains(mu):
            return False
    return True


def saturation_witnesses(credal: CredalSet, denominator: int) -> list[Vector]:
    """Credences in `π⁻¹(π(C))` but not in `C` — the projection's blind spot."""
    out = []
    for weights in product(range(denominator + 1), repeat=credal.size):
        if sum(weights) != denominator:
            continue
        mu = tuple(Fraction(w, denominator) for w in weights)
        if credal.saturation_contains(mu) and not credal.contains(mu):
            out.append(mu)
    return out


def dirac_live(worlds: Sequence[Sequence[Fraction]],
               region: Region) -> list[Vector]:
    """Worlds whose **own price vector** lies in the region.

    **Not a live-world definition**, and recorded rather than deleted: it makes
    `Ω^live` empty for `K = {p(A)=1/2}`. Kept computable for the regressions.
    """
    return [tuple(w) for w in worlds if region.contains(w)]


def preimage_live(worlds: Sequence[Sequence[Fraction]],
                  region: Region) -> list[Vector]:
    """The live worlds of the saturated lift `π⁻¹(K)`.

    Correct as the live worlds *of that credal set*, and **wrong as a recovery of
    a semantic constraint from its projection**: with deduction admitting only
    `00` and `11`, the projection is `{p_A = p_B}` and this returns all four
    worlds. Use `CredalSet.live_worlds` on the semantic object instead.
    """
    return saturated_lift(worlds, region).live_worlds()


# --- expectation against worldwise ------------------------------------------

def expected_value(position: Sequence[Fraction], prices: Sequence[Fraction],
                   credence: Sequence[Fraction],
                   worlds: Sequence[Sequence[Fraction]]) -> Fraction:
    """`E_μ[X]`, which is the position's value at `π(μ)`.

    The identity the round had to unpick: the enforcement inequality bounds the
    position at *price vectors* in the region, so it bounds **expectations** under
    admissible credences and nothing at any individual world.
    """
    return holdings_value(position, prices, price_of(credence, worlds))


def support_bridge_bound(position: Sequence[Fraction],
                         prices: Sequence[Fraction],
                         capacity: Fraction,
                         expectation_floor: Fraction = ZERO) -> Fraction:
    """`X(ω) ≥ (a - (1-θ)U)/θ`, with `U` named as the cube maximum gain.

    One of two sufficient routes from an expectation bound to a worldwise one.
    The other is the deficit bound, which needs no support hypothesis.
    """
    capacity = Fraction(capacity)
    if capacity <= 0:
        raise ValueError("a live world has positive support capacity")
    return (Fraction(expectation_floor)
            - (ONE - capacity) * max_gain(position, prices)) / capacity
