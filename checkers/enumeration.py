"""The enumeration checker.

**What a passing verdict means.** The checker generated a finite domain **itself**
from the supplied parameters, evaluated the named property at every point of it
with exact arithmetic, and found no failure. The domain size it visited is
reported.

**What it does not mean.** Nothing about any point outside the generated domain,
and nothing about the domain being the right one. A finite universal claim
verified here is verified over exactly the domain the parameters describe.

**Why the checker generates the domain.** If a contributor supplied the
enumeration, a contributor would be certifying the claim — the enumeration is the
proof. Contributors supply parameters; the judge builds the domain.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
from typing import Any, Callable, Iterator, Mapping

from checkers.witness import PROPERTIES, _rational

MAX_POINTS = 200_000  # budget; see AGENTS.md. Exceeding it fails rather than hangs.


def _grid(params: Mapping[str, Any]) -> Iterator[tuple[Q, ...]]:
    """Rational grid: each coordinate runs over `numerator/denominator` for
    numerator in [low, high]. Finite and exactly enumerable by construction."""
    denominator = int(params["denominator"])
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    axes = []
    for axis in params["axes"]:
        low, high = int(axis["low"]), int(axis["high"])
        if high < low:
            raise ValueError("axis high is below its low")
        axes.append([Q(n, denominator) for n in range(low, high + 1)])
    return product(*axes)


def _simplex(params: Mapping[str, Any]) -> Iterator[tuple[Q, ...]]:
    """Rational points of the probability simplex at a declared denominator:
    every nonnegative integer vector summing to the denominator, scaled."""
    denominator = int(params["denominator"])
    dimension = int(params["dimension"])
    if denominator <= 0 or dimension <= 0:
        raise ValueError("denominator and dimension must be positive")

    def parts(total: int, slots: int) -> Iterator[tuple[int, ...]]:
        if slots == 1:
            yield (total,)
            return
        for first in range(total + 1):
            for rest in parts(total - first, slots - 1):
                yield (first,) + rest

    for combination in parts(denominator, dimension):
        yield tuple(Q(c, denominator) for c in combination)


DOMAINS: Mapping[str, Callable[..., Iterator[tuple[Q, ...]]]] = {
    "rational-grid": _grid,
    "rational-simplex": _simplex,
}


def check(params: Mapping[str, Any]) -> tuple[bool, str]:
    """Generate the declared domain and check the property at every point."""
    kind = params.get("domain")
    if kind not in DOMAINS:
        return False, (f"unknown domain {kind!r}; registered: {sorted(DOMAINS)}. "
                       "A new one is a maintainer act.")
    name = params.get("property")
    if name not in PROPERTIES:
        return False, f"unknown property {name!r}; registered: {sorted(PROPERTIES)}"
    predicate = PROPERTIES[name]
    visited = 0
    try:
        for point in DOMAINS[kind](params):
            visited += 1
            if visited > MAX_POINTS:
                return False, (f"domain exceeds the budget of {MAX_POINTS} points; "
                               "a larger domain is a conversation, not an override")
            ok, detail = predicate({"point": point}, params)
            if not ok:
                return False, f"failed at {tuple(str(c) for c in point)}: {detail}"
    except (KeyError, TypeError, ValueError, ZeroDivisionError) as error:
        return False, f"{type(error).__name__}: {error}"
    if visited == 0:
        return False, "the declared domain is empty; a vacuous pass is not a pass"
    return True, f"property held at all {visited} points of the generated domain"
