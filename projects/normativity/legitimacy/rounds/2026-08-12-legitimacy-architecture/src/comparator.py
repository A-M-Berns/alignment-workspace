"""The comparator class a constraint structure induces, and when it is empty of
content.

An online-learning statement over legitimate trajectories needs a class of
counterfactual transformations that are themselves legitimacy-preserving.  The
constraint structure suggests one immediately: the maps of the response space
that carry admissible responses to admissible responses, uniformly along the
trajectory.

    Phi(F) = { phi : A -> A  |  for every Gamma in F, phi(Gamma) subset Gamma }

This module computes that class, characterizes it exactly, and exhibits the
condition under which it collapses to the identity — which is the point at which
a regret statement against it says nothing.

Everything here is finite and exhaustive; `A` is a declared finite response space
and the checks enumerate all `|A|^|A|` maps.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable, Sequence


Map = tuple[int, ...]


def all_maps(size: int) -> tuple[Map, ...]:
    """Every function from a size-`n` set to itself, as tuples."""
    return tuple(product(range(size), repeat=size))


def preserves(phi: Map, region: frozenset[int]) -> bool:
    return all(phi[a] in region for a in region)


def uniform_class(size: int, family: Sequence[frozenset[int]]) -> tuple[Map, ...]:
    """`Phi(F)` by enumeration: the maps preserving every region in the family."""
    return tuple(phi for phi in all_maps(size)
                 if all(preserves(phi, region) for region in family))


def core(size: int, family: Sequence[frozenset[int]], action: int) -> frozenset[int]:
    """The intersection of every region containing `action`.

    Where no region contains it, the action is unconstrained and the core is the
    whole space — which is the honest reading: a response the constraint never
    admits places no requirement on a transformation.
    """
    containing = [region for region in family if action in region]
    if not containing:
        return frozenset(range(size))
    result = frozenset(range(size))
    for region in containing:
        result &= region
    return result


def predicted_size(size: int, family: Sequence[frozenset[int]]) -> int:
    """The product formula for `|Phi(F)|`."""
    total = 1
    for action in range(size):
        total *= len(core(size, family, action))
    return total


def collapses(size: int, family: Sequence[frozenset[int]]) -> bool:
    """Whether `Phi(F)` is the identity alone.

    Exactly when every action's core is that action: the family pins down each of
    its own elements.  A trajectory whose admissible sets separate points in this
    sense admits no non-trivial legitimacy-preserving comparator at all.
    """
    return all(core(size, family, a) == frozenset({a}) for a in range(size))


@dataclass(frozen=True)
class ComparatorReport:
    size: int
    family: tuple[frozenset[int], ...]
    enumerated: int
    predicted: int
    collapsed: bool
    constant_image: bool

    @property
    def agrees(self) -> bool:
        return self.enumerated == self.predicted


def analyse(size: int, family: Sequence[frozenset[int]]) -> ComparatorReport:
    regions = tuple(family)
    return ComparatorReport(
        size=size,
        family=regions,
        enumerated=len(uniform_class(size, regions)),
        predicted=predicted_size(size, regions),
        collapsed=collapses(size, regions),
        constant_image=len(set(regions)) <= 1,
    )


# --------------------------------------------------------------------------
# Declared families
# --------------------------------------------------------------------------

RESPONSES = ("concede", "contest", "toll", "refer")

#: A constraint that never moves: every response admissible at every date.
CONSTANT_FAMILY = (frozenset({0, 1, 2, 3}),) * 4

#: A constraint whose admissible set moves with the record, in the smallest way
#: that separates every response from every other.
SEPARATING_FAMILY = (frozenset({0, 1}), frozenset({1, 2}),
                     frozenset({2, 3}), frozenset({0, 3}))

#: Between the two: the admissible set moves, and two responses stay tied.
PARTIAL_FAMILY = (frozenset({0, 1, 2}), frozenset({0, 1, 3}))


def exhaustive_formula_check(size: int = 3, length: int = 3) -> tuple[int, int]:
    """Check the product formula against enumeration over every short family.

    Returns the number of families checked and the number of disagreements.  The
    scope is stated rather than sampled: all families of exactly `length` regions
    drawn from all `2**size` subsets.
    """
    subsets = [frozenset(bits) for bits in _powerset(range(size))]
    checked = 0
    disagreements = 0
    for family in product(subsets, repeat=length):
        checked += 1
        if len(uniform_class(size, family)) != predicted_size(size, family):
            disagreements += 1
    return checked, disagreements


def _powerset(items: Iterable[int]) -> Iterable[tuple[int, ...]]:
    pool = tuple(items)
    for mask in range(1 << len(pool)):
        yield tuple(pool[i] for i in range(len(pool)) if mask >> i & 1)
