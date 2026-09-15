"""The finite compilation of a mediated pair into a bounded constraint over worlds, and
the soft selector for finite menus.

A world `w` carries `c_raw, c_corr` (activations), `w_raw, w_app, w_act` (protected
values, in `[0, D]`), `delta` (structural discrepancy, in `[0, dmax]`) and
`rho = (w_app − w_act)₊`.  The five `[0,1]`-valued variables of the pair are

    U_raw = c_raw·w_raw/D        U_corr = c_corr·w_act/D
    G_δ   = both·δ/dmax          G_ρ    = both·ρ/D          G_M = c_raw·(1 − c_corr)

and the constraint is `B = U_raw − U_corr − λ·G_δ − G_ρ − G_M` with `λ = L·dmax/D`.
Every world with a sound reproduction certificate has `B ≤ 0`; hence every credence has
`E[B] ≤ 0`, and every convex combination of pair constraints with nonnegative weights
is `≤ 0` in every world.  The soft selector is the normalised ramp of each pair's score
above the menu maximum less `2δ`.
"""
from fractions import Fraction as Q


def pos(x):
    return x if x > 0 else Q(0)


def gated(c, x):
    """The gated variable: `x` where the gate holds, `0` elsewhere.  Its value equals the
    product `c·x`; as a LUV it is one variable, not a product of two."""
    return x if c else Q(0)


def luvs(w, L, D, dmax):
    both = bool(w["c_raw"]) and bool(w["c_corr"])
    rawonly = bool(w["c_raw"]) and not w["c_corr"]
    rho = pos(w["w_app"] - w["w_act"])
    return {
        "U_raw": gated(w["c_raw"], w["w_raw"] / D),
        "U_corr": gated(w["c_corr"], w["w_act"] / D),
        "G_delta": gated(both, w["delta"] / dmax),
        "G_rho": gated(both, rho / D),
        "G_M": Q(1) if rawonly else Q(0),
    }


def lam(L, D, dmax):
    return L * dmax / D


def constraint(w, L, D, dmax):
    v = luvs(w, L, D, dmax)
    return v["U_raw"] - v["U_corr"] - lam(L, D, dmax) * v["G_delta"] - v["G_rho"] - v["G_M"]


def certified(w, L):
    """The reproduction certificate, required only where both activate."""
    if w["c_raw"] and w["c_corr"]:
        return abs(w["w_raw"] - w["w_app"]) <= L * w["delta"]
    return True


def in_range(w, D, dmax):
    return all(Q(0) <= w[k] <= D for k in ("w_raw", "w_app", "w_act")) and Q(0) <= w["delta"] <= dmax


def valid_everywhere(worlds, L, D, dmax):
    return all(constraint(w, L, D, dmax) <= 0 for w in worlds)


def expectation(credence, worlds, f):
    return sum((credence[i] * f(w) for i, w in enumerate(worlds)), Q(0))


def coefficient_l1(L, D, dmax):
    """`‖B‖₁` including the (zero) trailing coefficient: `3 + λ`."""
    return Q(3) + abs(lam(L, D, dmax))


# ---------------------------------------------------------------- the soft selector


def ramp(delta, x, y):
    """`min(1, max(0, (x − y)/δ))`: an expressible feature of `x, y`."""
    return min(Q(1), max(Q(0), (x - y) / delta))


def soft_weights(scores, delta):
    """Near-argmax weights: ramp of each score above `max − 2δ`, normalised.  The
    argmax has ramp `1`, so the normaliser is at least `1` and the safe reciprocal
    `1/max(1, Σ)` is the exact reciprocal."""
    m = max(scores)
    raw = [ramp(delta, s, m - 2 * delta) for s in scores]
    Z = sum(raw, Q(0))
    assert Z >= 1
    return [r / Z for r in raw]


def aggregate(scores, weights):
    return sum((w * s for w, s in zip(weights, scores)), Q(0))


def support_near_max(scores, weights, delta):
    m = max(scores)
    return all(s > m - 2 * delta for s, w in zip(scores, weights) if w > 0)


def argmax(scores):
    return max(range(len(scores)), key=lambda i: scores[i])


def hard_selector_jump(scores_a, scores_b):
    """The hard argmax is not continuous: two score vectors, the chosen index differs,
    and the selected score changes by a fixed amount however close the vectors are.
    Returns `(sup-distance of the vectors, change of the selected pair's index)`."""
    dist = max(abs(a - b) for a, b in zip(scores_a, scores_b))
    return dist, argmax(scores_a) != argmax(scores_b)


def convex_constraint(worlds_by_pair, weights, L, D, dmax, world_index):
    """`Σ_q ŵ_q · B_q(w)` at one world, for a menu of pairs each with its own world data."""
    return sum((wq * constraint(worlds_by_pair[q][world_index], L, D, dmax)
                for q, wq in enumerate(weights)), Q(0))
