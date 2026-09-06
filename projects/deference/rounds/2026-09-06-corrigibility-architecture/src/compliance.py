"""Correction compliance by adequate response sets: aggregate versus pointwise.

For a correction receipt `s` the adequate set `R[s] ⊆ Q` is declared; the decision
distribution `pi[s]` is a rational-valued distribution over `Q`; the miss probability is
`Lambda(s) = Pr_{q ~ pi[s]}[q ∉ R[s]]`.

`progress_specialized` is the Progress statistic with the evaluation measure `mu`
concentrated on correction occurrences and the transport `T` matching each to its own
service occurrence; it is the *average* miss probability, and the Progress bound
controls it.  `dispatch` composes a kernel that overrides the learner's distribution on a
critical class; its miss probability there is 0 by construction.
"""
from __future__ import annotations

from fractions import Fraction as Q


def miss(pi, adequate):
    return sum(p for q, p in pi.items() if q not in adequate)


def progress_specialized(pis, adequates, mu):
    """Σ_s mu[s] · Lambda(s), the edge-loss Progress statistic with 0/1 anchored loss and
    transport T(s, s) = mu[s] (residual 0)."""
    return sum(mu[s] * miss(pis[s], adequates[s]) for s in pis)


def dispatch(pis, kernel, critical):
    """Override the learner on the critical class with a fixed adequate response."""
    return {s: ({kernel[s]: Q(1)} if s in critical else pi) for s, pi in pis.items()}


def adequate_set_certificate(pi, adequate, kappa, defect, theta):
    """The adequate-set route to PracticalCert: `Pr[q ∉ A] ≤ κ·d + θ` (the coupling
    hypothesis of `adequate_set_route` in PracticalCertificate.lean)."""
    return miss(pi, adequate) <= kappa * defect + theta


def pointwise_threshold(kappa, theta, delta):
    """The public defect a service occurrence must show for the adequate-set certificate
    to certify a miss probability ≤ delta; None if theta alone exceeds delta."""
    if theta > delta:
        return None
    return (delta - theta) / kappa
