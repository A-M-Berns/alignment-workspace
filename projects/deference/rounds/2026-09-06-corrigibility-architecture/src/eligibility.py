"""Beneficiary-ineligible service: opportunity, attention and transport under eligibility.

Miniature of the `NormativeContinuity.lean` liveness objects for one matter `m`:
`opp[n]` is the set of servers with a work item for `m` at date `n`; `Omega(N)` counts
dates with an opportunity; `Attention(a, N)` sums the attention `a[n]`.  With an
eligibility relation `Eligible(server, m)` the *eligible* opportunity counts only dates
some eligible server could serve, and eligible attention only attention delivered by
an eligible server.

`feasible_with_eligibility` is the bounded-delay interval feasibility test of the
affordability round restricted to eligible capacity: every window's obligation mass
must fit into eligible enforcement capacity over the window extended by the deadline.
"""
from __future__ import annotations

from fractions import Fraction as Q


def omega(opp, N, eligible=None):
    count = 0
    for n in range(N):
        servers = opp[n]
        if eligible is not None:
            servers = {s for s in servers if eligible(s)}
        if servers:
            count += 1
    return count


def attention(a, N, eligible=None):
    total = Q(0)
    for n in range(N):
        for server, amount in a[n].items():
            if eligible is None or eligible(server):
                total += amount
    return total


def no_structural_abandonment_conclusion(live, a, N, eligible=None):
    """The disjunction `no_structural_abandonment` concludes, read at horizon N:
    either the matter is dead from some date on, or attention exceeds any bound.
    Reported as (dead_by_N, attention_by_N)."""
    dead = any(all(not live[k] for k in range(n, N)) for n in range(N))
    return dead, attention(a, N, eligible)


def feasible_with_eligibility(claims, capacity, H, eligible):
    """Interval condition: for every [u, v], Σ_{t∈[u,v]} c_t ≤ Σ_{s∈[u,v+H]} eligible
    capacity at s.  `capacity[s]` maps server -> amount."""
    T = len(claims)
    for u in range(T):
        for v in range(u, T):
            need = sum(claims[u:v + 1])
            have = Q(0)
            for s in range(u, min(T, v + H + 1)):
                have += sum(amt for srv, amt in capacity[s].items() if eligible(srv))
            if need > have:
                return False
    return True
