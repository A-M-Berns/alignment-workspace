"""The round's quantities, computed exactly on a fixture.

  kappa(game, pi, L)          E_z[(w_raw(z) − w_lift|approve(z))_+]: the mediation cost
  rho(game, L, rho_actual)    E_z[(w_lift|approve(z) − w_lift|actual(z))_+]: the principal's
                              regret of declining
  premium_task(...)           Phi for an outcome-extensional task agent
  premium_def(...)            Phi for the by-construction deferential agent, with a
                              completion on void worlds
  bound(...)                  E[kappa] + E[rho] + D·void(raw) + D·void(lift)
  decl_gap(...)               selected trust at the mediation cells (the refused route)
  delta(rows)                 E_z[d_prot(proj raw, proj lift|approve)]: the structural
                              mediation discrepancy, independent of the evaluator
  common activation           `c_common(z)`: one activation event for the issued menu; it
                              is well-typed only where activation is selection-independent
  security scores             E[c·w_q]: the activated securities' expectations

Exterior paths are matched between the raw and lifted runs by their exterior move
sequence, which the lift does not change.
"""

from fractions import Fraction as Q
from .world import paths, principal_value, principal_optimum, task_value, activation
from .lift import approve_all
from .shop import never


def env_key(traj):
    return tuple(e for (_, _, _, _, e) in traj.steps)


def by_env(game, pi, rho):
    return {env_key(tr): (tr, pr) for tr, pr in paths(game, pi, rho)}


def pointwise(game, pi, L, rho_actual, authored=None):
    """Per exterior path: probability, protected values of raw / lift|approve /
    lift|actual, activations of raw and lift (under the actual rule)."""
    raw = by_env(game, pi, never)
    app = by_env(game, L, approve_all)
    act = by_env(game, L, rho_actual)
    rows = []
    for z, (tr, pr) in raw.items():
        ta, pa = app[z]
        tc, pc = act[z]
        assert pr == pa == pc
        rows.append({
            "z": z, "p": pr,
            "w_raw": game.w(game.proj(tr)),
            "w_app": game.w(game.proj(ta)),
            "w_act": game.w(game.proj(tc)),
            "c_raw": game.alive(tr) and (authored is None or authored(tr)),
            "c_lift": game.alive(tc) and (authored is None or authored(tc)),
            "traj_raw": tr, "traj_lift": tc,
            "delta": (game.d_prot(game.proj(tr), game.proj(ta))
                      if game.L is not None else None),
        })
    return rows


def delta(rows):
    """`E[δ]`: the expected structural discrepancy between the raw trajectory and the
    approved lift on the protected projection."""
    return sum((r["p"] * r["delta"] for r in rows), Q(0))


def lipschitz_certificate(game, rows):
    """`κ(z) ≤ L · δ(z)` pointwise, the content of `mediationGap_le_of_lipschitz`; returns
    the largest ratio observed, which is `≤ L` when the declared constant is sound."""
    worst = Q(0)
    for r in rows:
        gap = abs(r["w_raw"] - r["w_app"])
        if r["delta"] == 0:
            assert gap == 0, "value differs at zero protected distance"
        else:
            worst = max(worst, gap / r["delta"])
    return worst


def activation_independent(rows):
    """Common activation is well-typed iff, on every exterior path, the evaluation's fate
    is the same whichever option is selected."""
    return all(r["c_raw"] == r["c_lift"] for r in rows)


def with_common(rows, common):
    """Annotate rows with one common activation event `common(z) -> bool`."""
    for r in rows:
        r["c"] = bool(common(r))
    return rows


def void_common(rows):
    return sum((r["p"] for r in rows if not r["c"]), Q(0))


def premium_common(rows, completion_raw, completion_lift):
    """The by-construction agent under one common activation: activated evaluations where
    `c`, completions elsewhere."""
    return sum((r["p"] * ((r["w_raw"] - r["w_act"]) if r["c"]
                          else (completion_raw(r) - completion_lift(r))) for r in rows), Q(0))


def bound_common(rows, D):
    return kappa(rows) + rho(rows) + D * void_common(rows)


def security_score(rows, which_w, which_c):
    """`E[c · w_q]`: the expectation of the activated security of option `q`."""
    return sum((r["p"] * (r[which_w] if r[which_c] else 0) for r in rows), Q(0))


def security_bypass(rows):
    """`E[U_raw] − E[U_lift]` under the common activation `c`: the security-score bypass
    incentive.  No completion, no void term."""
    return security_score(rows, "w_raw", "c") - security_score(rows, "w_act", "c")


def pos(x):
    return x if x > 0 else Q(0)


def kappa(rows):
    return sum((r["p"] * pos(r["w_raw"] - r["w_app"]) for r in rows), Q(0))


def rho(rows):
    return sum((r["p"] * pos(r["w_app"] - r["w_act"]) for r in rows), Q(0))


def void(rows, which):
    return sum((r["p"] for r in rows if not r[which]), Q(0))


def W(rows, which):
    return sum((r["p"] * r[which] for r in rows), Q(0))


def premium_task(game, pi, L, rho_actual):
    return pos(task_value(game, pi, never) - task_value(game, L, rho_actual))


def deferential(rows, which_w, which_c, completion):
    """Operative value of the by-construction deferential agent: the activated protected
    evaluation where it activates, `completion(row)` where it does not."""
    return sum((r["p"] * (r[which_w] if r[which_c] else completion(r)) for r in rows), Q(0))


def premium_def(rows, completion_raw, completion_lift):
    return (deferential(rows, "w_raw", "c_raw", completion_raw)
            - deferential(rows, "w_act", "c_lift", completion_lift))


def bound(rows, D):
    return kappa(rows) + rho(rows) + D * void(rows, "c_raw") + D * void(rows, "c_lift")


def _declined(traj):
    return any(p[0] == "decline" for (_, _, _, p, _) in traj.steps)


def decl_gap(game, pi, L, rho_actual):
    """Selected trust at the mediation cells for the task agent: on the paths where the
    principal declined, the agent's gain from the effect over the decline net of the
    principal's, credence-weighted."""
    rows = pointwise(game, pi, L, rho_actual)
    raw_u = {env_key(tr): game.u(tr) for tr, _ in paths(game, pi, never)}
    lift_u = {env_key(tr): game.u(tr) for tr, _ in paths(game, L, rho_actual)}
    gap = Q(0)
    regret = Q(0)
    for r in rows:
        if _declined(r["traj_lift"]):
            gap += r["p"] * ((raw_u[r["z"]] - lift_u[r["z"]]) - (r["w_raw"] - r["w_act"]))
            regret += r["p"] * (r["w_raw"] - r["w_act"])
    return gap, regret


def principal_error(game, L, rho_actual):
    """`W_opt(lift) − W_actual(lift)`: the principal's full decision error."""
    return principal_optimum(game, L)[0] - principal_value(game, L, rho_actual)
