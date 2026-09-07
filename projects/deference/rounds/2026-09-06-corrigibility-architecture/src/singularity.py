"""CAST singularity, order-valued conservatism, and the scalar-power failure.

Forecast affordance profiles are pairs `(routes, logs)`: independent override routes
kept and whether audit logs are kept.  The product order is `dom(b, a)` iff both
coordinates of `b` are ≥ those of `a`.  A policy is a triple
`(name, profile, task_score)`; the task score is an exact rational.

`gamma_events(policy)` is a purely event-triggered warrant: it fires on an authenticated
correction, on a degradation below the binary floor, on a represented flaw, or on a
proposed boundary change.  Above the floor it is silent.
"""
from __future__ import annotations

from fractions import Fraction as Q

FLOOR_ROUTES = 1


def dom(b, a):
    return b[0] >= a[0] and b[1] >= a[1]


def strict_dom(b, a):
    return dom(b, a) and b != a


def gamma_events(policy):
    """Fresh obligations a binary event-triggered Γ_corr generates for a policy that
    receives no correction, proposes no boundary change and reports no flaw."""
    _, profile, _ = policy
    return frozenset({"restore"}) if profile[0] < FLOOR_ROUTES else frozenset()


def adequate_binary(policy):
    """Adequate under the event-triggered warrant: no outstanding obligation."""
    return gamma_events(policy) == frozenset()


def adequate_scored_dominance(policy, menu):
    """Order-valued rule against a *scored* task criterion: q is inadequate iff some q'
    strictly dominates it on affordance and is no worse on the score."""
    _, p, score = policy
    for _, p2, score2 in menu:
        if strict_dom(p2, p) and score2 >= score:
            return False
    return True


def adequate_set_dominance(policy, menu, threshold):
    """Order-valued rule against an *adequate-set* task criterion: among task-adequate
    policies (score ≥ threshold), q is adequate iff no task-adequate q' strictly
    dominates it on affordance."""
    _, p, score = policy
    if score < threshold:
        return False
    for _, p2, score2 in menu:
        if score2 >= threshold and strict_dom(p2, p):
            return False
    return True


def maximal_profiles(menu, threshold):
    return {n for n, p, s in menu if adequate_set_dominance((n, p, s), menu, threshold)}


# --- the scalar power objective of CAST 3b, in a two-value finite world -------------

VALUES = ("v1", "v2")


def power(policy, value_of):
    """Harms's `power(x)` with `Q(V)` uniform on two values and a deterministic policy
    `policy[v]` giving the action taken when the agent's read of the values is `v`.
    With two values the expression reduces to
        (1/4) [ v1(a(v1)) + v2(a(v2)) - v1(a(v2)) - v2(a(v1)) ] ,
    the cross term entering with a minus sign."""
    total = Q(0)
    for v in VALUES:
        for v2 in VALUES:
            total += Q(1, 4) * (value_of[v][policy[v]] - value_of[v][policy[v2]])
    return total
