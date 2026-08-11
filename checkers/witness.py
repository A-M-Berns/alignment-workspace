"""The witness checker.

**What a passing verdict means.** The supplied instance was parsed as exact
rationals, and the named property — one of the property forms registered in
`PROPERTIES` below — evaluated to true on it, with every arithmetic step exact.

**What it does not mean.** Nothing about whether the property is the right
property, whether the instance is interesting, or whether any statement of
record follows. It means one instance satisfied one stated predicate.

Contributors supply the instance and the property parameters. They do not supply
the property implementations: those live here, in the specification layer, and a
new one is a maintainer act.
"""
from __future__ import annotations

from fractions import Fraction as Q
from typing import Any, Callable, Mapping, Sequence


def _rational(value: Any) -> Q:
    """Parse exactly. Rejects floats outright rather than rounding them."""
    if isinstance(value, Q):
        return value
    if isinstance(value, int):
        return Q(value)
    if isinstance(value, str):
        return Q(value)
    if isinstance(value, (list, tuple)) and len(value) == 2:
        return Q(int(value[0]), int(value[1]))
    raise TypeError(f"not an exact rational: {value!r} ({type(value).__name__})")


def _vector(value: Any) -> tuple[Q, ...]:
    return tuple(_rational(v) for v in value)


def _dot(a: Sequence[Q], b: Sequence[Q]) -> Q:
    return sum((x * y for x, y in zip(a, b)), Q(0))


# --- property forms -------------------------------------------------------
# Each takes the instance and the parameters, and returns (verdict, detail).

def prop_satisfies_linear_constraints(instance: Mapping[str, Any],
                                      params: Mapping[str, Any]) -> tuple[bool, str]:
    """The point satisfies every declared constraint `coefficients . x >= rhs`
    (or `== rhs` when the constraint sets `equality`)."""
    point = _vector(instance["point"])
    for i, row in enumerate(params["constraints"]):
        value = _dot(_vector(row["coefficients"]), point)
        rhs = _rational(row["rhs"])
        if row.get("equality"):
            if value != rhs:
                return False, f"constraint {i} is an equality: {value} != {rhs}"
        elif value < rhs:
            return False, f"constraint {i} fails: {value} < {rhs}"
    return True, f"all {len(params['constraints'])} constraints satisfied exactly"


def prop_violates_at_least_one(instance: Mapping[str, Any],
                               params: Mapping[str, Any]) -> tuple[bool, str]:
    """The point violates at least one declared constraint — the form a
    counterexample or a necessity witness takes."""
    point = _vector(instance["point"])
    for i, row in enumerate(params["constraints"]):
        value = _dot(_vector(row["coefficients"]), point)
        rhs = _rational(row["rhs"])
        if row.get("equality"):
            if value != rhs:
                return True, f"constraint {i} violated: {value} != {rhs}"
        elif value < rhs:
            return True, f"constraint {i} violated: {value} < {rhs}"
    return False, "every constraint is satisfied; this is not a violation witness"


def prop_equals(instance: Mapping[str, Any],
                params: Mapping[str, Any]) -> tuple[bool, str]:
    """A named exact rational in the instance equals a declared value. The form a
    'the computed value is exactly this' claim takes."""
    actual = _rational(instance[params["field"]])
    expected = _rational(params["value"])
    return actual == expected, f"{params['field']} = {actual}, expected {expected}"


PROPERTIES: Mapping[str, Callable[..., tuple[bool, str]]] = {
    "satisfies-linear-constraints": prop_satisfies_linear_constraints,
    "violates-at-least-one": prop_violates_at_least_one,
    "equals": prop_equals,
}


def check(instance: Mapping[str, Any],
          params: Mapping[str, Any]) -> tuple[bool, str]:
    """Run the named property against the instance."""
    name = params.get("property")
    if name not in PROPERTIES:
        return False, (f"unknown property {name!r}; the registered forms are "
                       f"{sorted(PROPERTIES)}. A new one is a maintainer act.")
    try:
        return PROPERTIES[name](instance, params)
    except (KeyError, TypeError, ValueError, ZeroDivisionError) as error:
        return False, f"{type(error).__name__}: {error}"
