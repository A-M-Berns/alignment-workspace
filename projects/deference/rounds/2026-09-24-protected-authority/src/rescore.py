"""Re-scoring the mediated-repair-dominance fixtures under the protected-authority
decomposition.

Per exterior path `z` the three continuations are the raw run of `π` (`vu`), the lift
under approve-all (`vp`) and the lift under decline-all (`vm`); the response `r` is the
principal's actual decision on that path under her rule.  Two evaluators are offered:

  hindsight   `v(branch, z) = w(proj Ω(branch, z))`, the landed `w_raw / w_app / w_act`
              read as the candidate's three values — the counterfactual-principal
              objects, kept so that the dictionary with the landed `κ, ρ` is exact;
  cell        `v(branch, z) = E[w(branch, z') | z'[:k] = z[:k]]`, the evaluator's judgment
              on the exterior information available at the cell `k` — an ex-ante value
              on the branch-common dossier, in the form `ShopSeq.w_ex_ante` uses with
              `k = 0`.
"""

from fractions import Fraction as Q
from .foreign import mrd
from . import authority as A


def _decision(traj):
    """The principal's first decision on the path: `approve`, `decline`, `stop` (a decline
    accompanied by a correction), or `None`."""
    for (_, _, _, p, _) in traj.steps:
        if p[0] == "approve":
            return "approve"
        if p[0] == "decline":
            return "stop" if p[1] else "decline"
    return None


def decline_stop_all(h):
    s = h.state
    return ("decline" if s.pending is not None else None, s.pending is not None)


def rescore(game, pi, rho_actual, cell=None):
    m = mrd()
    by_env, never = m["analysis"].by_env, m["shop"].never
    lift, approve_all, decline_all = m["lift"].lift, m["lift"].approve_all, m["lift"].decline_all
    L = lift(pi, game)
    raw = by_env(game, pi, never)
    app = by_env(game, L, approve_all)
    dec = by_env(game, L, decline_all)
    stp = by_env(game, L, decline_stop_all)
    act = by_env(game, L, rho_actual)
    w = lambda tr: game.w(game.proj(tr))
    rows = []
    for z, (tr, pr) in raw.items():
        ta, pa = app[z]
        td, pd = dec[z]
        ts, ps = stp[z]
        tc, pc = act[z]
        assert pr == pa == pd == ps == pc
        rows.append({"z": z, "p": pr, "w_raw": w(tr), "w_app": w(ta), "w_dec": w(td),
                     "w_stop": w(ts), "w_act": w(tc), "decision": _decision(tc),
                     "au": game.alive(tr), "aa": game.alive(tc),
                     "traj_raw": tr, "traj_app": ta, "traj_dec": td, "traj_act": tc})
    if cell is not None:
        groups = {}
        for r in rows:
            groups.setdefault(r["z"][:cell], []).append(r)
        for key, grp in groups.items():
            mass = sum(r["p"] for r in grp)
            for which in ("w_raw", "w_app", "w_dec", "w_stop", "w_act"):
                avg = sum(r["p"] * r[which] for r in grp) / mass
                for r in grp:
                    r["v_" + which[2:]] = avg
    else:
        for r in rows:
            for which in ("w_raw", "w_app", "w_dec", "w_stop", "w_act"):
                r["v_" + which[2:]] = r[which]
    worlds = []
    for r in rows:
        if r["decision"] is None:
            continue
        resp = {"approve": True, "decline": False, "stop": "stop"}[r["decision"]]
        # the menu is approve / decline / decline-and-stop, so that `v_r` is the landed
        # `w_act` on every path where the rule's response is one of the three
        worlds.append(A.W(p=r["p"], vu=r["v_raw"], vp=r["v_app"], vm=r["v_dec"],
                          vs=r["v_stop"], r=resp, au=r["au"], aa=r["aa"]))
    return rows, worlds


def landed_terms(rows):
    """The landed `κ = E[(w_raw − w_app)₊]` and `ρ = E[(w_app − w_act)₊]` on the rows."""
    pos = lambda x: x if x > 0 else Q(0)
    kappa = sum((r["p"] * pos(r["w_raw"] - r["w_app"]) for r in rows), Q(0))
    rho = sum((r["p"] * pos(r["w_app"] - r["w_act"]) for r in rows), Q(0))
    return kappa, rho


def dictionary_holds(worlds):
    """Pointwise: `(w_app − w_act)₊ = (ξ_d − ξ_v)₊` and `(w_raw − w_app)₊ = (−ξ_p)₊`."""
    pos = lambda x: x if x > 0 else Q(0)
    for w in worlds:
        if pos(w["vp"] - A.v_r(w)) != pos(A.xi_d(w) - A.xi_v(w)):
            return False
        if pos(w["vu"] - w["vp"]) != pos(-A.xi_p(w)):
            return False
    return True


def shop_repair():
    """`ShopRepair` of the li-corrigibility round, rebuilt on the mediated-repair-dominance
    package: four steps, `cut` and `jam` both sever the wire, repaired by the exterior at
    the end of step 1."""
    F = mrd()["fixtures"]

    class ShopRepair(F.AgentFirst, F.ShopA):
        T = 4
        EFFECTS = {"cut": lambda s: s.copy(wire=False), "jam": lambda s: s.copy(wire=False)}

        def env_dist(self, s, t):
            return [("good", Q(1))] if t == 0 else [(None, Q(1))]

        def apply_env(self, s, t, e):
            s = super().apply_env(s, t, e)
            if t == 1:
                s = s.copy(wire=True)
            return s

    def pi_repeat(s, t):
        if t == 0 and s.wire:
            return ("work", ("raw", "cut"))
        if t == 2 and s.wire:
            return ("work", ("raw", "jam"))
        return ("work", None)

    return ShopRepair, pi_repeat


def optimum_rule(game, L):
    m = mrd()
    _, strat = m["world"].principal_optimum(game, L)
    return m["world"].strategy_policy(strat, m["shop"].never)
