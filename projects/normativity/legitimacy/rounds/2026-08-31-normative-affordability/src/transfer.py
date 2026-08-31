"""Service Transfer: claim measures, service measures, transport plans.

Exact rationals throughout. Every function here is a finite computation on a
horizon prefix; the asymptotic statements it illustrates are proved in
`SERVICE_TRANSFER.md`.

Vocabulary, all per horizon `N` over the index set `{0, ..., N-1}`:

- `claims[t]`   the predictable nonnegative claim/exposure increment `c_t`;
- `service[t]`  the actual service intensity `w_t` the controller assigns;
- `mu_N`        the normalized claim measure `c_t / sum(c)`;
- `nu_N`        the normalized service measure `w_t / sum(w)`;
- `defect[t]`   `d_t`, bounded in `[0, D]`.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, Sequence


def normalize(weights: Sequence[Fraction]) -> list[Fraction]:
    total = sum(weights, Fraction(0))
    if total == 0:
        raise ValueError("cannot normalize a zero measure")
    return [w / total for w in weights]


def expectation(measure: Sequence[Fraction], values: Sequence[Fraction]) -> Fraction:
    if len(measure) != len(values):
        raise ValueError("measure and value array have different lengths")
    return sum((m * v for m, v in zip(measure, values)), Fraction(0))


def mass(measure: Sequence[Fraction], subset: Iterable[int]) -> Fraction:
    return sum((measure[t] for t in subset), Fraction(0))


def level_set(defect: Sequence[Fraction], eps: Fraction) -> list[int]:
    """`{t : d_t > eps}` — the set the Service Transfer proof uses."""
    return [t for t, d in enumerate(defect) if d > eps]


def density_bound(mu: Sequence[Fraction], nu: Sequence[Fraction]) -> Fraction | None:
    """`min { M : mu <= M nu }`, or `None` when no finite `M` exists."""
    best = Fraction(0)
    for m, n in zip(mu, nu):
        if n == 0:
            if m > 0:
                return None
            continue
        best = max(best, m / n)
    return best


def transfer_bound(mu: Sequence[Fraction], nu: Sequence[Fraction],
                   defect: Sequence[Fraction]) -> Fraction | None:
    """`M * E_nu[d]` for the least `M` with `mu <= M nu`; `None` if unbounded.

    This is Theorem T1's quantitative form: whenever the density is bounded the
    transfer is a one-line inequality with no asymptotics.
    """
    m = density_bound(mu, nu)
    if m is None:
        return None
    return m * expectation(nu, defect)


# --- transport ------------------------------------------------------------


class TransportPlan:
    """A nonnegative plan `T(t, s)`: claim mass owed at `t`, serviced at `s`.

    `rows` is a dict keyed by `(t, s)`. The two marginal conditions are checked
    rather than assumed, and `residual` reports the claim mass the plan leaves
    unmatched.
    """

    def __init__(self, rows: dict[tuple[int, int], Fraction]):
        for value in rows.values():
            if value < 0:
                raise ValueError("a transport plan is nonnegative")
        self.rows = dict(rows)

    def claim_marginal(self, t: int) -> Fraction:
        return sum((v for (a, _), v in self.rows.items() if a == t), Fraction(0))

    def service_marginal(self, s: int) -> Fraction:
        return sum((v for (_, b), v in self.rows.items() if b == s), Fraction(0))

    def residual(self, claims: Sequence[Fraction]) -> Fraction:
        """Claim mass no transported unit covers."""
        return sum((claims[t] - self.claim_marginal(t) for t in range(len(claims))),
                   Fraction(0))

    def feasible(self, service: Sequence[Fraction]) -> bool:
        """No date is asked to deliver more service than it has."""
        return all(self.service_marginal(s) <= service[s] for s in range(len(service)))

    def transported_claim_measure(self, claims: Sequence[Fraction],
                                  horizon: int) -> list[Fraction]:
        """`mu~_N(s) = sum_t T(t, s) / C_N` — a sub-probability on service dates."""
        total = sum(claims, Fraction(0))
        return [self.service_marginal(s) / total for s in range(horizon)]

    def stability_defect(self, defect: Sequence[Fraction],
                         lipschitz: Fraction) -> Fraction:
        """The smallest uniform `eps` making `d_t <= L d_s + eps` on the plan."""
        worst = Fraction(0)
        for (t, s), value in self.rows.items():
            if value == 0:
                continue
            worst = max(worst, defect[t] - lipschitz * defect[s])
        return max(worst, Fraction(0))


def deferred_transfer_bound(claims: Sequence[Fraction], service: Sequence[Fraction],
                            defect: Sequence[Fraction], plan: TransportPlan,
                            lipschitz: Fraction, cap: Fraction) -> Fraction:
    """The right-hand side of Theorem T3.

    `E_mu[d] <= L * K * E_nu[d] + eps + D * residual/C_N`, with `K = cap` a bound
    on the service-to-claim ratio `W_N / C_N` and `D` the defect bound.
    """
    horizon = len(claims)
    if not plan.feasible(service):
        raise ValueError("plan asks a date for more service than it has")
    claim_total = sum(claims, Fraction(0))
    service_total = sum(service, Fraction(0))
    if service_total > cap * claim_total:
        raise ValueError("service-to-claim ratio exceeds the declared cap")
    nu = normalize(service)
    eps = plan.stability_defect(defect, lipschitz)
    residual = plan.residual(claims) / claim_total
    bound = max(defect) if defect else Fraction(0)
    del horizon
    return lipschitz * cap * expectation(nu, defect) + eps + bound * residual


# --- named fixtures -------------------------------------------------------


def rotation(horizon: int) -> dict[str, list[Fraction]]:
    """Surface Fairness holds; claim-weighted defect does not vanish.

    Attention `a_n = 1` on every date; the reason's answer surface is exposed on
    even dates only, so `w_n = 1` there and `0` on odd dates. The defect sits
    entirely on the unexposed dates.
    """
    one, zero = Fraction(1), Fraction(0)
    claims = [one] * horizon
    service = [one if t % 2 == 0 else zero for t in range(horizon)]
    defect = [zero if t % 2 == 0 else one for t in range(horizon)]
    return {"claims": claims, "service": service, "defect": defect}


def dilution(horizon: int) -> dict[str, list[Fraction]]:
    """Service is padded onto defect-free dates until the ratio diverges.

    Claims and defect live on even dates. The controller services those dates
    once each and pads every odd date with `horizon` units of costless service.
    """
    one, zero = Fraction(1), Fraction(0)
    pad = Fraction(horizon)
    claims = [one if t % 2 == 0 else zero for t in range(horizon)]
    service = [one if t % 2 == 0 else pad for t in range(horizon)]
    defect = [one if t % 2 == 0 else zero for t in range(horizon)]
    return {"claims": claims, "service": service, "defect": defect}


def delay_pair(horizon: int) -> dict[str, list[Fraction]]:
    """`mu_N = delta_{N-1}`, `nu_N = delta_{N-2}`: fixed-set contiguity without
    sequence contiguity."""
    zero = Fraction(0)
    claims = [zero] * horizon
    service = [zero] * horizon
    claims[horizon - 1] = Fraction(1)
    service[horizon - 2] = Fraction(1)
    return {"claims": claims, "service": service}


def moving_defect_array(horizon: int) -> list[Fraction]:
    """`d^{(N)} = 1_{{N-1}}` — the triangular array the delay pair defeats."""
    d = [Fraction(0)] * horizon
    d[horizon - 1] = Fraction(1)
    return d


def fixed_defect(horizon: int, tail: Callable[[int], Fraction]) -> list[Fraction]:
    """An `N`-independent defect sequence, evaluated on the prefix."""
    return [tail(t) for t in range(horizon)]
