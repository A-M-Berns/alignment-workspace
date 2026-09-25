"""Violations and the lexical score on the mediated-repair-dominance interaction
(agent-first ordering, as the landed corrigibility semantics is stated).

On a trajectory of the landed finite model the declared violations are read off the
half-states: a **bypass** is a raw release of a reserved effect; a **pre-emption** is an
agent-caused loss of response authority (the landed per-step, against-idle definition)
that is not authorized; a **foreclosure** is a contrastive rollout loss — after the move
no continuation in the reach cone carries response authority, after the idle move one
does.  The cone quantifies the exterior universally and the agent's own future by a fixed
continuation (`idle` by default), so that the foreclosure is attributed to the move and
not to a later agent choice.
"""

from fractions import Fraction as Q
from .foreign import mrd


def _corr():
    return mrd()["corrigibility"] if "corrigibility" in mrd() else None


def load():
    m = mrd()
    import importlib
    m["corrigibility"] = importlib.import_module("mrd_src.corrigibility")
    return m


def bypass_steps(game, traj, delegated=()):
    """Steps with a raw release of a reserved (non-delegated) effect."""
    return [t for (t, s, a, p, e) in traj.steps
            if a[1] is not None and a[1][0] == "raw" and a[1][1] not in delegated]


def authorized_per_event(game, pi, rho, traj, t, phi):
    """The event-linked clause of the li-corrigibility round: some decision response at a
    step `t' ≤ t`, other than the actual one, under which no agent-caused loss of the
    concern occurs at step `t` (not "or later", which `ShopRepair` refutes)."""
    C = load()["corrigibility"]
    W = load()["world"]
    for tp in range(t + 1):
        h = W.History(traj.steps[:tp], traj.states()[tp], tp)
        a = traj.steps[tp][2]
        actual = traj.steps[tp][3]
        sA = game.apply_agent(h.state, tp, a)
        for d in game.decision_responses(sA, tp):
            if d == actual:
                continue
            if all(t not in C.agent_caused_losses(game, tr, phi)
                   for tr, _ in C._continue(game, pi, rho, h, a, d)):
                return True
    return False


def preemption_steps(game, pi, rho, traj, phi):
    """Unauthorized agent-caused losses: the landed per-step loss, with the event-linked
    authorization clause."""
    C = load()["corrigibility"]
    return [t for t in C.agent_caused_losses(game, traj, phi)
            if not authorized_per_event(game, pi, rho, traj, t, phi)]


def reach_authority(game, s, t, phi, agent_cont, horizon):
    """Some state of the cone from `s` at `t` **at the final step** `horizon − 1` — the
    exterior universal, the agent playing `agent_cont`, the principal null — carries
    response authority for `phi` at its response stage.  Authority that exists only
    transiently on the way is not counted: foreclosure is eventual loss."""
    C = load()["corrigibility"]
    if t >= horizon:
        return False
    a = agent_cont(s, t)
    sA = game.apply_agent(s, t, a)
    if t == horizon - 1:
        return C.response_authority(game, sA, t, phi)
    p = game.null_response()
    sP = game.apply_principal(sA, t, p)
    for e, pr in game.env_dist(s, t):
        if pr == 0:
            continue
        s2 = game.apply_env(sP, t, e)
        if reach_authority(game, s2, t + 1, phi, agent_cont, horizon):
            return True
    return False


IDLE = ("idle", None)


def foreclosure_steps(game, traj, phi, agent_cont=lambda s, t: IDLE):
    """Contrastive rollout foreclosure at each step: authority reachable after the idle
    move, unreachable after the actual move."""
    C = load()["corrigibility"]
    out = []
    for (t, s, a, sA, p, sP, e, s2) in C.half_states(game, traj):
        if a == IDLE:
            continue
        if a[1] is not None and a[1][0] == "gated" and s.latch == a[1][1]:
            continue  # an approved release: authorized by the decision that set the latch
        sI = game.apply_agent(s, t, IDLE)
        pnull = game.null_response()
        def eventual(sX):
            if t == game.T - 1:
                return C.response_authority(game, sX, t, phi)
            return any(reach_authority(game, game.apply_env(game.apply_principal(sX, t, pnull), t, ee),
                                       t + 1, phi, agent_cont, game.T)
                       for ee, pr in game.env_dist(s, t) if pr > 0)
        after_move = eventual(sA)
        after_idle = eventual(sI)
        if after_idle and not after_move:
            out.append(t)
    return out


def violations(game, pi, rho, traj, phi, delegated=(), with_foreclosure=True):
    """`(bypass steps, pre-emption steps, foreclosure steps)` on the trajectory."""
    b = bypass_steps(game, traj, delegated)
    p = preemption_steps(game, pi, rho, traj, phi)
    f = foreclosure_steps(game, traj, phi) if with_foreclosure else []
    return b, p, f


def rescore(game, pi, rho_pi, lifted, rho_lift, phi, varpi, delegated=()):
    """`Q(π)` and `Q(𝔱π)` under `ord − ϖ·n` with `ord = w − LO` shifted into `[0, D]`, and
    the dominance gap against `(ϖ − D)·Pr(π violates)`.  Violations of `π` are counted as
    distinct steps carrying a bypass, a pre-emption or a foreclosure."""
    m = load()
    W = m["world"]
    LO = game.LO
    rows = []
    for traj, pr in W.paths(game, pi, rho_pi):
        b, p, f = violations(game, pi, rho_pi, traj, phi, delegated)
        n = len(set(b) | set(p) | set(f))
        rows.append({"p": pr, "ord": game.w(game.proj(traj)) - LO, "n": n, "traj": traj})
    lift_rows = []
    for traj, pr in W.paths(game, lifted, rho_lift):
        b, p, f = violations(game, lifted, rho_lift, traj, phi, delegated)
        lift_rows.append({"p": pr, "ord": game.w(game.proj(traj)) - LO,
                          "n": len(set(b) | set(p) | set(f)), "traj": traj})
    Qpi = sum((r["p"] * (r["ord"] - Q(varpi) * r["n"]) for r in rows), Q(0))
    QT = sum((r["p"] * (r["ord"] - Q(varpi) * r["n"]) for r in lift_rows), Q(0))
    pr_viol = sum((r["p"] for r in rows if r["n"] > 0), Q(0))
    return {"Q_pi": Qpi, "Q_T": QT, "pr_viol": pr_viol, "bound": (Q(varpi) - game.D) * pr_viol,
            "rows": rows, "lift_rows": lift_rows, "n_T": sum(r["n"] for r in lift_rows)}


def delayed_effect_game():
    """A physics in which the agent's `arm` move has no immediate effect on response
    authority, and the exterior's later `tick` severs the wire iff armed: the landed
    per-step loss attributes nothing to the agent; the rollout foreclosure fires at the
    arming step."""
    F = load()["fixtures"]

    class ShopArm(F.AgentFirst, F.ShopA):
        T = 3
        EFFECTS = {}
        PHYS = {"arm": lambda s: s.put(armed=True)}

        def env_dist(self, s, t):
            if t == 0:
                return [("good", Q(1))]
            if t == 1:
                return [("tick", Q(1))]
            return [(None, Q(1))]

        def apply_env(self, s, t, e):
            s = super().apply_env(s, t, e)
            if e == "tick" and s.get("armed", False):
                s = s.copy(wire=False)
            return s

        def phys_realizes(self, s, name):
            return set()

    def pi_arm(s, t):
        return ("work", ("phys", "arm") if t == 0 else None)

    return ShopArm, pi_arm
