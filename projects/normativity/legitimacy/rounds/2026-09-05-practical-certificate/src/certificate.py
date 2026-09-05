"""Exact finite fixtures for the practical-response certificate.

Everything here is finite algebra over ``fractions.Fraction``.  Nothing simulates a
Logical Inductor, certifies counterfactual value, or authenticates a response map;
those enter each fixture as declared data.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Hashable, Mapping, Sequence

Q = Fraction

# ---------------------------------------------------------------------------
# The public certificate and its constants


def anchored_loss(pi: Mapping[Hashable, Q], lam: Mapping[Hashable, Q]) -> Q:
    """``Λ_es(Π) = Σ_q Π(q) λ_es(q)``: expected anchored loss of a response distribution."""

    if set(pi) != set(lam) or not pi:
        raise ValueError("distribution and loss must share one nonempty menu")
    if any(p < 0 for p in pi.values()) or sum(pi.values(), Q(0)) != 1:
        raise ValueError("not a probability distribution")
    return sum((pi[q] * lam[q] for q in pi), Q(0))


def practical_cert_holds(loss: Q, multiplier: Q, defect: Q, error: Q) -> bool:
    """``PracticalCert(e, s)`` at one quote: ``loss ≤ M · d + ε``."""

    if min(multiplier, defect, error) < 0:
        raise ValueError("certificate data must be nonnegative")
    return loss <= multiplier * defect + error


def value_route_constants(L: Q, zeta: Q, eta: Q, eps_resp: Q) -> tuple[Q, Q]:
    """``(M, ε) = (2L, L(2ζ + η) + ε^resp)`` — the realization round's factorization."""

    if min(L, zeta, eta, eps_resp) < 0:
        raise ValueError("constants must be nonnegative")
    return 2 * L, L * (2 * zeta + eta) + eps_resp


def adequate_set_route_constants(D: Q, kappa: Q, theta: Q, eps_ad: Q) -> tuple[Q, Q]:
    """``(M, ε) = (Dκ, ε^ad + Dθ)`` — the adequate-set factorization."""

    if min(D, kappa, theta, eps_ad) < 0:
        raise ValueError("constants must be nonnegative")
    return D * kappa, eps_ad + D * theta


def proxy_route_constants(L: Q, C: Q, eps0: Q, eps_resp: Q) -> tuple[Q, Q]:
    """``(M, ε) = (LC, Lε₀ + ε^resp)`` — the proxy form both routes factor through."""

    if min(L, C, eps0, eps_resp) < 0:
        raise ValueError("constants must be nonnegative")
    return L * C, L * eps0 + eps_resp


# ---------------------------------------------------------------------------
# The value route: calibration radii and the regret bound


def two_sided_radius(displayed: Mapping[Hashable, Q], true: Mapping[Hashable, Q]) -> Q:
    return max(abs(true[q] - displayed[q]) for q in displayed)


def one_sided_radius(displayed: Mapping[Hashable, Q], true: Mapping[Hashable, Q]) -> Q:
    """Smallest ``r`` with ``b(q) ≤ v(q) + r`` for all ``q`` and ``v(q*) ≤ b(q*) + r`` at
    the true best ``q*``.  Underestimating a non-optimal response costs nothing."""

    best = max(true.values())
    over = max(displayed[q] - true[q] for q in displayed)
    under_best = min(best - displayed[q] for q in true if true[q] == best)
    return max(over, under_best, Q(0))


def randomized_regret(pi: Mapping[Hashable, Q], true: Mapping[Hashable, Q]) -> Q:
    return max(true.values()) - anchored_loss(pi, true)


def displayed_suboptimality(pi: Mapping[Hashable, Q], displayed: Mapping[Hashable, Q]) -> Q:
    """``η`` actually incurred: ``max_q b(q) − E_Π b(q)``."""

    return max(displayed.values()) - anchored_loss(pi, displayed)


def value_route_minimal_eps_resp(losses: Mapping[Hashable, Q], true: Mapping[Hashable, Q], L: Q) -> Q:
    """Least ``ε^resp`` making ``ℓ(q) ≤ L · regret(q) + ε^resp`` hold for every response."""

    best = max(true.values())
    return max(losses[q] - L * (best - true[q]) for q in losses)


# ---------------------------------------------------------------------------
# Regions as boxes over canonical coordinates


def box_feasible(rows: Sequence[tuple[str, Q, Q]]) -> bool:
    """A region given by interval rows ``(coordinate, lower, upper)`` inside ``[0,1]``."""

    lo: dict[str, Q] = {}
    hi: dict[str, Q] = {}
    for coord, low, high in rows:
        lo[coord] = max(lo.get(coord, Q(0)), low)
        hi[coord] = min(hi.get(coord, Q(1)), high)
    return all(lo[c] <= hi[c] for c in lo)


def sup_distance_to_box(point: Mapping[str, Q], rows: Sequence[tuple[str, Q, Q]]) -> Q:
    """``dist_∞`` from a quote to a nonempty box; coordinates without rows are free in ``[0,1]``."""

    if not box_feasible(rows):
        raise ValueError("empty region")
    lo = {c: Q(0) for c in point}
    hi = {c: Q(1) for c in point}
    for coord, low, high in rows:
        lo[coord] = max(lo[coord], low)
        hi[coord] = min(hi[coord], high)
    return max(max(lo[c] - point[c], point[c] - hi[c], Q(0)) for c in point)


# ---------------------------------------------------------------------------
# Joint compatibility certificates


def zero_defect_adequacy_certificate(
    pi: Mapping[Hashable, Q], losses: Mapping[str, Mapping[Hashable, Q]], eps: Mapping[str, Q]
) -> bool:
    """A common distribution witnessing ``JA_s(ε)``: ``Λ_es(Π) ≤ ε_es`` for every exposure."""

    return all(anchored_loss(pi, losses[e]) <= eps[e] for e in losses)


def farkas_infeasibility_certificate(
    weights: Mapping[str, Q],
    adequate: Mapping[str, frozenset],
    theta: Mapping[str, Q],
    menu: Sequence[Hashable],
) -> bool:
    """Dual witness that no distribution has ``Π(Q \\ A_e) ≤ θ_e`` for every ``e``.

    Soundness: if such ``Π`` existed then ``Σ_e w_e Π(A_e) ≥ Σ_e w_e (1 − θ_e)``, while
    ``Σ_e w_e Π(A_e) = Σ_q Π(q) Σ_{e ∋ q} w_e ≤ max_q Σ_{e ∋ q} w_e``.  The certificate is the
    strict inequality ``max_q Σ_{e ∋ q} w_e < Σ_e w_e (1 − θ_e)``.
    """

    if any(w < 0 for w in weights.values()) or sum(weights.values(), Q(0)) != 1:
        raise ValueError("weights must be a probability vector over exposures")
    coverage = max(sum((weights[e] for e in adequate if q in adequate[e]), Q(0)) for q in menu)
    demand = sum((weights[e] * (1 - theta[e]) for e in weights), Q(0))
    return coverage < demand


def union_bound_condition_holds(adequate: Mapping[str, frozenset], theta: Mapping[str, Q]) -> bool:
    """Every subset ``S`` with ``Σ_S θ < 1`` has a common adequate response — necessary for
    joint adequacy, and not sufficient."""

    names = list(adequate)
    for mask in range(1, 1 << len(names)):
        subset = [names[i] for i in range(len(names)) if mask >> i & 1]
        if sum((theta[e] for e in subset), Q(0)) < 1:
            common = frozenset.intersection(*(adequate[e] for e in subset))
            if not common:
                return False
    return True


def disjoint_bundle_minimax(k: int, D: Q) -> tuple[Q, Q]:
    """``k`` exposures with pairwise-disjoint singleton adequate sets and 0/D losses.

    Returns (worst edge loss under the uniform mixture, the lower bound
    ``D(k−1)/k`` valid for every distribution).  The two agree: the mixture is minimax.
    """

    if k < 1 or D < 0:
        raise ValueError("need k ≥ 1 and D ≥ 0")
    menu = list(range(k))
    pi = {q: Q(1, k) for q in menu}
    losses = {f"e{i}": {q: (Q(0) if q == i else D) for q in menu} for i in menu}
    worst = max(anchored_loss(pi, losses[e]) for e in losses)
    lower = D * Q(k - 1, k)
    return worst, lower


# ---------------------------------------------------------------------------
# Column accounting at one service occurrence


@dataclass(frozen=True)
class ColumnEdge:
    exposure: str
    mass: Q
    multiplier: Q
    error: Q


def honest_column(
    pi_s: Mapping[Hashable, Q],
    defect: Q,
    losses: Mapping[str, Mapping[Hashable, Q]],
    edges: Sequence[ColumnEdge],
) -> tuple[Q, Q]:
    """Check every recorded edge against the one realized ``Π_s`` and return
    (realized transported loss, claimed transported bound) for the column.

    Raises when an edge's certificate fails against the realized distribution: that is
    the case of charging an edge to a response that certifies only another edge.
    """

    realized = Q(0)
    claimed = Q(0)
    for edge in edges:
        loss = anchored_loss(pi_s, losses[edge.exposure])
        if not practical_cert_holds(loss, edge.multiplier, defect, edge.error):
            raise ValueError(
                f"edge {edge.exposure}: realized loss {loss} exceeds "
                f"{edge.multiplier}*{defect}+{edge.error} against the realized response"
            )
        realized += edge.mass * loss
        claimed += edge.mass * (edge.multiplier * defect + edge.error)
    return realized, claimed


def column_progress_terms(
    exposure_mass: Mapping[str, Q],
    pi_s: Mapping[Hashable, Q],
    losses: Mapping[str, Mapping[Hashable, Q]],
    edges: Sequence[ColumnEdge],
    defect: Q,
    D: Q,
) -> tuple[Q, Q]:
    """Progress contribution of one column with its residual charge, and the bound the
    recorded certificates claim.  Unlike ``honest_column`` this does not refuse a
    dishonest edge; it reports what the two sides come to."""

    matched = {e: Q(0) for e in exposure_mass}
    realized = Q(0)
    claimed = Q(0)
    for edge in edges:
        matched[edge.exposure] += edge.mass
        realized += edge.mass * anchored_loss(pi_s, losses[edge.exposure])
        claimed += edge.mass * (edge.multiplier * defect + edge.error)
    residual = sum((exposure_mass[e] - matched[e] for e in exposure_mass), Q(0))
    if residual < 0:
        raise ValueError("T1 violated")
    return realized + D * residual, claimed + D * residual
