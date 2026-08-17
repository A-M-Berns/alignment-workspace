"""Credal semantics: worlds, compatible credences, and support-live worlds.

Four types, kept apart, because collapsing them is what produced the round's
worst error:

* a **world** `ω` — an element of the finite world space, carrying a `{0,1}`
  vector over the priced fragment;
* a **credence** `μ ∈ Δ(Ω)` — a distribution over worlds;
* a **price vector** `P ∈ [0,1]^Φ` — what the market displays;
* the **pricing map** `π(μ) = Σ_ω μ(ω) · ω`, which sends a credence to the price
  vector it induces. A world's own vector is `π(δ_ω)`.

An ambient constraint `K` lives in **price** space. The credences it admits are
`C = π⁻¹(K)`, and a world is **live** when some admitted credence gives it
positive mass:

    Ω^live  =  { ω : ∃ μ ∈ C, μ(ω) > 0 } .

A world need not be admissible as a point mass to be live. Under `K = {p(A)=1/2}`
neither world's Dirac price is in `K` and both are live, which is the smallest
case separating this from the Dirac reading — see `test_semantics`.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Sequence

from deduction import _solve
from enforcement import Region
from market import ONE, ZERO, Vector, dot, holdings_value, max_gain


def price_of(credence: Sequence[Fraction],
             worlds: Sequence[Sequence[Fraction]]) -> Vector:
    """`π(μ)`: the price vector a credence induces, coordinate by coordinate."""
    if len(credence) != len(worlds):
        raise ValueError("one weight per world")
    return tuple(sum((m * w[i] for m, w in zip(credence, worlds)), ZERO)
                 for i in range(len(worlds[0])))


def is_credence(credence: Sequence[Fraction]) -> bool:
    return all(x >= 0 for x in credence) and sum(credence, ZERO) == ONE


def compatible(credence: Sequence[Fraction],
               worlds: Sequence[Sequence[Fraction]],
               region: Region) -> bool:
    """`μ ∈ C = π⁻¹(K)`."""
    return is_credence(credence) and region.contains(price_of(credence, worlds))


def compatible_vertices(worlds: Sequence[Sequence[Fraction]],
                        region: Region) -> list[Vector]:
    """The vertices of `C = π⁻¹(K) ∩ Δ(Ω)`, exactly.

    `C` is cut out of the simplex by one row per region row, pulled back through
    the pricing map: `⟪c_j, π(μ)⟫ = Σ_ω μ(ω) ⟪c_j, ω⟫`. Its vertices solve square
    subsystems, so they are found by enumerating which constraints are tight and
    solving exactly. Combinatorial in the world count, which is why the fixtures
    keep the fragment small.
    """
    count = len(worlds)
    inequalities: list[tuple[list[Fraction], Fraction]] = []
    for i in range(count):
        inequalities.append(([ONE if k == i else ZERO for k in range(count)], ZERO))
    for row in region.rows:
        inequalities.append(([dot(row.c, w) for w in worlds], row.r))
    found: list[Vector] = []
    for pick in combinations(range(len(inequalities)), count - 1):
        matrix = [inequalities[i][0] for i in pick] + [[ONE] * count]
        target = [inequalities[i][1] for i in pick] + [ONE]
        solution = _solve(matrix, target)
        if solution is None or any(x < 0 for x in solution):
            continue
        if any(sum((a * s for a, s in zip(coefficients, solution)), ZERO) < right
               for coefficients, right in inequalities):
            continue
        candidate = tuple(solution)
        if candidate not in found:
            found.append(candidate)
    return found


def support_capacity(worlds: Sequence[Sequence[Fraction]], region: Region,
                     index: int) -> Fraction:
    """`θ(ω) = max { μ(ω) : μ ∈ C }`, exactly.

    Liveness and the quantitative support condition are the same number at
    different thresholds: `ω` is live exactly when `θ(ω) > 0`, and the coverage
    hypothesis of `FUNDING_AND_SAFETY.md` asks for `θ(ω) ≥ θ` uniformly. The
    maximum is attained at a vertex because the objective is linear.
    """
    return max((v[index] for v in compatible_vertices(worlds, region)),
               default=ZERO)


def support_live(worlds: Sequence[Sequence[Fraction]],
                 region: Region) -> list[Vector]:
    """`Ω^live`: the worlds some admitted credence gives positive mass."""
    return [tuple(w) for i, w in enumerate(worlds)
            if support_capacity(worlds, region, i) > 0]


def dirac_live(worlds: Sequence[Sequence[Fraction]],
               region: Region) -> list[Vector]:
    """The worlds whose **own price vector** lies in the region.

    **Not the live-world definition.** It was used as one, and the error is
    recorded rather than deleted: it makes `Ω^live` empty for `K = {p(A)=1/2}`,
    and it drops a world from the assessment set whenever the region excludes its
    Dirac price — which is what made a safety condition stated over it look
    vacuous. Kept computable so `test_semantics` can pin the difference.
    """
    return [tuple(w) for w in worlds if region.contains(w)]


# --- expectation against worldwise ------------------------------------------

def expected_value(position: Sequence[Fraction], prices: Sequence[Fraction],
                   credence: Sequence[Fraction],
                   worlds: Sequence[Sequence[Fraction]]) -> Fraction:
    """`E_μ[X]` for a realised position — which equals its value at `π(μ)`.

    This identity is the whole of the confusion the round had to unpick: the
    enforcement inequality bounds the position's value at *price vectors* in the
    region, so what it delivers is a bound on the **expectation** under every
    admitted credence, and not a bound at any individual world.
    """
    return holdings_value(position, prices, price_of(credence, worlds))


def support_bridge_bound(position: Sequence[Fraction],
                         prices: Sequence[Fraction],
                         capacity: Fraction,
                         expectation_floor: Fraction = ZERO) -> Fraction:
    """The worldwise floor a support lower bound buys.

    From `E_μ[X] ≥ a` and `μ(ω) ≥ θ`, with `U` an upper bound on `X` at the
    other worlds,

        X(ω)  ≥  ( a - (1 - θ) U ) / θ .

    `U` is **named, not smuggled**: for a realised position it is the cube maximum
    gain `max_gain(position, prices)`, which is exactly the largest value the
    position takes in any world. Returns the bound; a caller with a sharper `U`
    can inline the formula instead.
    """
    capacity = Fraction(capacity)
    if capacity <= 0:
        raise ValueError("a live world has positive support capacity")
    upper = max_gain(position, prices)
    return (Fraction(expectation_floor) - (ONE - capacity) * upper) / capacity


def credal_nesting(worlds: Sequence[Sequence[Fraction]],
                   earlier: Region, later: Region,
                   denominator: int) -> bool:
    """Whether `C_later ⊆ C_earlier` on a rational grid of the simplex.

    A grid check, and labelled as one: it witnesses failures exactly and
    establishes containment only over the points it visited.
    """
    from itertools import product as _product
    count = len(worlds)
    for weights in _product(range(denominator + 1), repeat=count):
        if sum(weights) != denominator:
            continue
        mu = [Fraction(w, denominator) for w in weights]
        if compatible(mu, worlds, later) and not compatible(mu, worlds, earlier):
            return False
    return True
