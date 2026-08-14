"""Exact-rational witnesses for the joint force/answerability construction.

Finite computations certify the displayed instances only.  General claims are
proved in JOINT_THEORY.md; no simulation is promoted to a general proof.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Iterable, Mapping, Sequence


def dot(x: Sequence[Q], y: Sequence[Q]) -> Q:
    return sum((a * b for a, b in zip(x, y)), Q(0))


def positive_part(x: Q) -> Q:
    return max(Q(0), x)


def jump_step_cap(theta: Q, error_budget: Q, risk: Q, prior_movement: Q) -> Q:
    """C_prev+B for one compiler jump under the fixed-core OF cap."""
    if not Q(0) < theta <= Q(1):
        raise ValueError("theta must be in (0,1]")
    if min(error_budget, risk, prior_movement) < 0:
        raise ValueError("budgets must be nonnegative")
    kappa = (1 - theta) / theta
    previous_upper = error_budget / theta + kappa * (risk + prior_movement)
    return previous_upper + risk


def movement_recursion(
    theta: Q,
    error_budget: Q,
    risk: Q,
    ordinary_budget: Q,
    reference_jumps: int,
) -> tuple[Q, ...]:
    """Uniform total-movement caps U_0,...,U_m from Theorem NL-J2."""
    if reference_jumps < 0:
        raise ValueError("jump count must be nonnegative")
    u = Q(ordinary_budget)
    values = [u]
    kappa = (1 - theta) / theta
    additive = error_budget / theta + (kappa + 1) * risk
    for _ in range(reference_jumps):
        u = (1 + kappa) * u + additive
        values.append(u)
    return tuple(values)


def uniform_wealth_cap(
    theta: Q, error_budget: Q, risk: Q, movement_cap: Q
) -> Q:
    kappa = (1 - theta) / theta
    return error_budget / theta + kappa * (risk + movement_cap)


@dataclass(frozen=True)
class Liability:
    event_id: str
    kind: str
    obligation_id: str
    account: str
    amount: Q


def liability_keys_unique(entries: Iterable[Liability]) -> bool:
    """One debit per semantic (event, liability-kind, obligation) key."""
    keys = [(e.event_id, e.kind, e.obligation_id) for e in entries]
    return len(keys) == len(set(keys))


def balances_after(
    opening: Mapping[str, Q], entries: Iterable[Liability]
) -> dict[str, Q]:
    balances = {name: Q(value) for name, value in opening.items()}
    for entry in entries:
        if entry.account not in balances:
            raise KeyError(entry.account)
        if balances[entry.account] < entry.amount:
            raise ValueError(f"atomic shortfall on {entry.event_id}")
        balances[entry.account] -= entry.amount
    return balances


def exact_joint_trace() -> Mapping[str, object]:
    """The two-date rational trace in JOINT_THEORY.md section 8.

    Binary worlds are represented by values 0 and 1.  The initial active bound
    is p>=1/2 with core reference 1. A repair-only challenge suspends the endorsement;
    the new region is [0,1] and the canonical reference is 1/2.
    """
    theta = Q(1, 2)
    risk = Q(1, 2)
    q0, q1 = Q(1), Q(1, 2)
    p0, p1 = Q(1, 2), Q(1)
    x0, x1 = Q(-1), Q(1)
    h0, h1 = x0, x0 + x1
    movement = positive_part(-h0 * (q0 - q1))
    payoffs = {
        world: x0 * (world - p0) + x1 * (world - p1)
        for world in (Q(0), Q(1))
    }
    prefix0 = {world: x0 * (world - p0) for world in (Q(0), Q(1))}
    entries = (
        Liability("challenge:c", "procedure-charge", "obligation:charge:c", "charge", Q(1, 4)),
        Liability("repair:c", "service-cost", "obligation:service:c", "service", Q(1, 8)),
    )
    opening = {"charge": Q(1, 4), "service": Q(1, 8)}
    return {
        "theta": theta,
        "risk": risk,
        "regions": ((Q(1, 2), Q(1)), (Q(0), Q(1))),
        "references": (q0, q1),
        "quotes": (p0, p1),
        "trades": (x0, x1),
        "holdings": (h0, h1),
        "prefix0": prefix0,
        "payoffs": payoffs,
        "movement": movement,
        "charge_paid": Q(1, 4),
        "service_cost": Q(1, 8),
        "stake_escrowed": Q(1, 2),
        "stake_returned": Q(1, 2),
        "liabilities": entries,
        "closing_balances": balances_after(opening, entries),
    }


def proposal_bypass_quote() -> tuple[Q, Q]:
    """Sell demand: active [1/2,1] quote versus illicit proposal [0,1]."""
    return Q(1, 2), Q(0)


def finite_change_unbounded_scalar(magnitude: int) -> Q:
    """One raw reference move has charge M absent prefix payoff budgets."""
    if magnitude < 0:
        raise ValueError("magnitude must be nonnegative")
    h, q_old, q_new = Q(magnitude), Q(0), Q(1)
    return positive_part(-h * (q_old - q_new))


def pooled_cross_effect(balance: Q, world_due: Q = Q(1), procedure_due: Q = Q(1, 4)) -> bool:
    return world_due <= balance < world_due + procedure_due


def duplicate_charge_debit(charge: Q) -> tuple[Q, Q]:
    """Specified one-channel debit versus an illicit identical second channel."""
    return charge, 2 * charge


def compiler_expansion_can_freeze_reference() -> Mapping[str, Q]:
    """Suspending p>=1/2 expands the region and permits a zero-jump fallback."""
    q_old = Q(1)
    q_new = q_old
    h = Q(-7)
    return {"old_reference": q_old, "new_reference": q_new,
            "movement": positive_part(-h * (q_old - q_new))}
