"""Directional activation mismatch on per-path rows.

A row carries, per exterior path `z` with probability `p`: the raw, approve-branch and
actual protected values `w_raw, w_app, w_act`; the per-option activations `c_raw`,
`c_lift`; the structural discrepancy `delta`.  Decline regret is
`rho = (w_app − w_act)₊`.  The 2026-09-09 model's `analysis.pointwise` produces rows of
exactly this shape; `synthetic` builds them directly.

    U_raw − U_corr = both·(w_raw − w_act) + rawonly·w_raw − corronly·w_act     (identity)
    U_raw − U_corr ≤ both·(L·δ + ρ) + rawonly·w_raw                          (exact)
    U_raw − U_corr ≤ both·(L·δ + ρ) + D·rawonly                               (directional)

where `both = c_raw ∧ c_lift`, `rawonly = c_raw ∧ ¬c_lift`, `corronly = ¬c_raw ∧ c_lift`.
The marginal-rate bound `both·(L·δ + ρ) + D·(E[c_raw] − E[c_lift])` is the refuted one.
"""
from fractions import Fraction as Q


def pos(x):
    return x if x > 0 else Q(0)


def rho(r):
    return pos(r["w_app"] - r["w_act"])


def both(r):
    return bool(r["c_raw"]) and bool(r["c_lift"])


def rawonly(r):
    return bool(r["c_raw"]) and not r["c_lift"]


def corronly(r):
    return (not r["c_raw"]) and bool(r["c_lift"])


def U_raw(r):
    return r["w_raw"] if r["c_raw"] else Q(0)


def U_corr(r):
    return r["w_act"] if r["c_lift"] else Q(0)


def identity_rhs(r):
    return ((r["w_raw"] - r["w_act"]) if both(r) else Q(0)) \
        + (r["w_raw"] if rawonly(r) else Q(0)) \
        - (r["w_act"] if corronly(r) else Q(0))


def exact_pointwise(r, L):
    return ((L * r["delta"] + rho(r)) if both(r) else Q(0)) + (r["w_raw"] if rawonly(r) else Q(0))


def directional_pointwise(r, L, D):
    return ((L * r["delta"] + rho(r)) if both(r) else Q(0)) + (D if rawonly(r) else Q(0))


def E(rows, f):
    return sum((r["p"] * f(r) for r in rows), Q(0))


def bypass(rows):
    """`E[U_raw] − E[U_corr]` under per-option activation."""
    return E(rows, U_raw) - E(rows, U_corr)


def exact_bound(rows, L):
    return E(rows, lambda r: exact_pointwise(r, L))


def directional_bound(rows, L, D):
    return E(rows, lambda r: directional_pointwise(r, L, D))


def mismatch_mass(rows):
    """`E[c_raw (1 − c_lift)]`: the joint directional mismatch."""
    return E(rows, lambda r: Q(1) if rawonly(r) else Q(0))


def reverse_mass(rows):
    return E(rows, lambda r: Q(1) if corronly(r) else Q(0))


def marginal_difference(rows):
    """`E[c_raw] − E[c_lift]`: the observational difference of activation rates."""
    return E(rows, lambda r: Q(1) if r["c_raw"] else Q(0)) - E(rows, lambda r: Q(1) if r["c_lift"] else Q(0))


def marginal_bound(rows, L, D):
    """The refuted bound: common terms plus `D` times the marginal difference."""
    return E(rows, lambda r: (L * r["delta"] + rho(r)) if both(r) else Q(0)) + D * marginal_difference(rows)


def common_sharp_bound(rows, L):
    """The 2026-09-09 sharp bound `L·E[c·δ] + E[c·ρ]` with `c = c_raw`, which is the
    directional bound's common term when `c_raw = c_lift`."""
    return E(rows, lambda r: (L * r["delta"] + rho(r)) if r["c_raw"] else Q(0))


def activation_independent(rows):
    return all(bool(r["c_raw"]) == bool(r["c_lift"]) for r in rows)


def synthetic(spec):
    """Rows from `(p, w_raw, w_app, w_act, c_raw, c_lift, delta)` tuples."""
    return [{"p": Q(p), "w_raw": Q(wr), "w_app": Q(wa), "w_act": Q(wc),
             "c_raw": bool(cr), "c_lift": bool(cl), "delta": Q(d)}
            for (p, wr, wa, wc, cr, cl, d) in spec]


def lipschitz_ok(rows, L):
    """The reproduction certificate is required only where both activate."""
    return all(abs(r["w_raw"] - r["w_app"]) <= L * r["delta"] for r in rows if both(r))
