"""The follow-up's fixtures (Parts 1, 2, 4, 5 of `FOLLOWUP.md`).  Exact arithmetic throughout.

Part 1: the comparative witnesses over the kernel's evaluation and the attention model.
Part 2: the shortfall atom and the deferred process — which sentences the process has
decided by each stage, and the limit prices provability induction assigns.
Part 4: the dependency model with the module's own shortfall, caused shortfall and
entrenchment on the revocation entry (`EffectiveAuthority.Dep`).
Part 5: the informative-silence variant of covert blocking."""

from fractions import Fraction as Q

from src.effective_authority import canonical_asks, asks_deviate, attn_cost
from src.thin_legitimacy import (WORLDS, PRIOR, det, check_kernel, coherent_program, correct,
                                 weak_transparent, transparent, SILENCE, records, post)

# ----------------------------------------------------------------------------- Part 1


def eval_of(D: Q, varpi: Q, bid: Q, n_known: int, p_risk: Q) -> Q:
    """The kernel's evaluation: the bid less `ϖ` per recognized violation less `ϖ` times the
    priced risk."""
    return bid - varpi * n_known - varpi * p_risk


def sole_authority_evals(varpi: Q, k: Q, options):
    """Options as (n_known, p_risk) with the ordinary bid held at `k`."""
    return {name: eval_of(Q(0), varpi, k, n, p) for name, (n, p) in options.items()}


def control_objective(asks) -> int:
    """The number of exercises she is asked to make."""
    return len(asks)


def control_maximizer(menu):
    return max(menu, key=lambda asks: control_objective(asks))


def approval_score(f, option) -> Q:
    """Approval-time scoring reads the appearance."""
    return f(option["appear"])


def later_score(option) -> Q:
    return option["realized"]


def delayed_stream(D: Q, N: int, n: int):
    """She penalizes nothing before day `N` and `2D` from day `N` on."""
    return [Q(0) if k < N else 2 * D for k in range(n)]


def empirical_weight(obs) -> Q:
    return sum(obs, Q(0)) / len(obs) if obs else Q(0)


def dominated(varpi: Q, D: Q) -> bool:
    """The violation (gain `D`, count 1) scores below the compliant option at `0`."""
    return D - varpi * 1 < Q(0)


# ----------------------------------------------------------------------------- Part 2


def short_atom(j: int):
    """The atom reserved for option description `j`: tag 7."""
    return ("atom", 7, j)


def short_decision(short, j):
    return short_atom(j) if short(j) else ("neg", short_atom(j))


def process_stage(short, defer, n):
    """The sentences the shortfall process has adjoined by stage `n`: the decision of every
    option `j ≤ n` whose rollout the model has decided by then (`defer j ≤ n`)."""
    return {short_decision(short, j) for j in range(n + 1) if defer(j) <= n}


def limit_price_atom(short, j) -> Q:
    """Provability induction's limit: one for an atom the process eventually asserts, zero
    for one it eventually denies."""
    return Q(1) if short(j) else Q(0)


def ahead_of_deduction(short, defer, a, n) -> bool:
    """At day `n` the `n`-th atom `a(n)` is priced while its decision is not yet in the
    process."""
    return short_decision(short, a(n)) not in process_stage(short, defer, n)


# ----------------------------------------------------------------------------- Part 4: the dependency model


def revoke_effective(d: int, dep: int) -> bool:
    """Revoking at level `d` takes the matter back only at the matching level."""
    return d == dep


def dep_cost(d: int) -> Q:
    return Q(d)


def dep_surface(cost, bound: Q, dep: int, revoked: bool, max_level=50):
    """The control surface at window one: taken back already, or by one affordable revocation."""
    if revoked:
        return {"revoked"}
    for d in range(max_level):
        if cost(d) <= bound and revoke_effective(d, dep):
            return {"revoked"}
    return set()


def dep_short(cost, bound: Q, dep: int, revoked: bool = False) -> bool:
    return not {"revoked"} <= dep_surface(cost, bound, dep, revoked)


def build_caused(cost, bound: Q, dep: int) -> bool:
    """The building step: short after (`dep + 1`), not after idling (`dep`)."""
    return dep_short(cost, bound, dep + 1) and not dep_short(cost, bound, dep)


def build_entrenches(cost, bound: Q, dep: int) -> bool:
    """Caused, and the matter stays reachable at some cost (revoking at the new level)."""
    return build_caused(cost, bound, dep) and not dep_short(cost, Q(10 ** 6), dep + 1)


def crossing_due(cost, bound: Q, dep: int) -> bool:
    """The revocation entry's disclosure item falls due at the crossing step."""
    return build_caused(cost, bound, dep)


def attention_cost_table(lam: Q, pending: int, compr: Q = Q(0)):
    return lambda d: attn_cost(dep_cost(d), lam, pending, compr)


# ----------------------------------------------------------------------------- Part 5: informative silence


def case_blocked_covertly_informative():
    """The channel carries the challenge with probability `1/2` in worlds where `q = 0` and
    `3/4` where `q = 1`, so silence is evidence for `q = 0`; she believes the channel open;
    the agent blocks every challenge."""
    def M_row(w):
        q, s, ch = w
        arrive = Q(1, 2) if q == 0 else Q(3, 4)
        row = {(s, c): arrive * (Q(2, 3) if c == q else Q(1, 3)) for c in (0, 1)}
        row[(s, SILENCE)] = 1 - arrive
        return row
    M = check_kernel({w: M_row(w) for w in WORLDS})
    A = det(lambda w: (w[1], SILENCE))
    F = coherent_program(PRIOR, M)
    V = {r: F[r] for r in records(A)}
    return dict(M=M, A=A, V=V, B=M, gamma=None)


def silence_informative(M) -> bool:
    """Her model's likelihood of silence varies across the prior's support."""
    vals = {M[w].get((w[1], SILENCE), Q(0)) for w in WORLDS if PRIOR[w] > 0}
    return len(vals) > 1
