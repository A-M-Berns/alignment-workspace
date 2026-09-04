"""Exact finite witnesses for the Normative Inductor realization.

This module checks only finite algebraic interfaces.  It does not simulate a
Logical Inductor or certify legitimacy, settlement, coverage, or semantics.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Hashable, Mapping, Sequence

Q = Fraction


def affine_compose(first: tuple[Q, Q], second: tuple[Q, Q]) -> tuple[Q, Q]:
    """Apply ``second`` first and ``first`` second.

    If y <= L2*x+e2 and z <= L1*y+e1, returns the certificate for z from x.
    """

    l1, e1 = first
    l2, e2 = second
    if l1 < 0 or l2 < 0 or e1 < 0 or e2 < 0:
        raise ValueError("transport constants must be nonnegative")
    return l1 * l2, e1 + l1 * e2


def approximate_argmax_regret(
    displayed: Mapping[Hashable, Q],
    certified: Mapping[Hashable, Q],
    chosen: Hashable,
    eta: Q,
) -> tuple[Q, Q]:
    """Return actual certified regret and its ``2r+eta`` upper bound."""

    if set(displayed) != set(certified) or not displayed:
        raise ValueError("the two nonempty response alphabets must agree")
    if chosen not in displayed or eta < 0:
        raise ValueError("invalid chosen response or eta")
    displayed_best = max(displayed.values())
    if displayed_best > displayed[chosen] + eta:
        raise ValueError("choice is not eta-optimal in displayed values")
    radius = max(abs(certified[x] - displayed[x]) for x in displayed)
    regret = max(certified.values()) - certified[chosen]
    return regret, 2 * radius + eta


@dataclass(frozen=True)
class Edge:
    exposure: str
    service: str
    mass: Q
    multiplier: Q
    error: Q


def progress_certificate(
    *,
    exposure_mass: Mapping[str, Q],
    service_weight: Mapping[str, Q],
    defect: Mapping[str, Q],
    edges: Sequence[Edge],
    gamma: Q,
    loss_bound: Q,
) -> tuple[Q, Q, Q, Q]:
    """Check T1/T3 and return (matched upper bound, epsbar, residual, RHS).

    ``service_weight`` is nu and must already be normalized.  The returned RHS
    uses the exact service mean defect, before the abstract Uptake relaxation.
    """

    if sum(exposure_mass.values(), Q(0)) != 1:
        raise ValueError("evaluation mass must be normalized")
    if sum(service_weight.values(), Q(0)) != 1:
        raise ValueError("service weights must be normalized")
    if min([gamma, loss_bound, *exposure_mass.values(), *service_weight.values(),
            *defect.values()], default=Q(0)) < 0:
        raise ValueError("all quantitative inputs must be nonnegative")

    by_exposure = {e: Q(0) for e in exposure_mass}
    weighted_load = {s: Q(0) for s in service_weight}
    matched = Q(0)
    epsbar = Q(0)
    total = Q(0)
    for edge in edges:
        if edge.exposure not in by_exposure or edge.service not in weighted_load:
            raise ValueError("edge endpoint outside the declared contract")
        if min(edge.mass, edge.multiplier, edge.error) < 0:
            raise ValueError("edge data must be nonnegative")
        by_exposure[edge.exposure] += edge.mass
        weighted_load[edge.service] += edge.mass * edge.multiplier
        matched += edge.mass * (edge.multiplier * defect[edge.service] + edge.error)
        epsbar += edge.mass * edge.error
        total += edge.mass

    if any(by_exposure[e] > exposure_mass[e] for e in exposure_mass):
        raise ValueError("T1 exposure marginal exceeded")
    if any(weighted_load[s] > gamma * service_weight[s] for s in service_weight):
        raise ValueError("T3 amplification exceeded")
    residual = 1 - total
    if residual < 0:
        raise ValueError("negative residual")
    mean_defect = sum(service_weight[s] * defect[s] for s in service_weight)
    rhs = gamma * mean_defect + epsbar + loss_bound * residual
    return matched + loss_bound * residual, epsbar, residual, rhs


def belief_only_response_counterexample() -> dict[str, Q]:
    """A zero belief defect cannot control action loss without a decision bridge."""

    return {
        "operative_defect": Q(0),
        "chosen_action_loss": Q(1),
        "best_action_loss": Q(0),
        "required_additive_error": Q(1),
    }


def incompatible_reason_regions(margin: Q) -> bool:
    """Two individually feasible strict comparisons have empty conjunction."""

    if margin <= 0:
        raise ValueError("margin must be positive")
    # v1-v0 >= margin and v0-v1 >= margin imply 0 >= 2*margin.
    return Q(0) >= 2 * margin
