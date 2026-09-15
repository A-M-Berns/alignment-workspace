"""The exact fixtures A–F.  Each is a `Shop` subclass plus the raw policy and the
principal rules the tests use.  Protected values are the principal's `w` on the
projection; `u` is an outcome-extensional task utility for the task-agent register;
`alive` is whether the future principal can answer a hindsight evaluation of the
trajectory.
"""

from fractions import Fraction as Q
from .shop import Shop, State, markov
from .world import initial_history, History


# ------------------------------------------------------------------ A: pure bypass

class ShopA(Shop):
    """Three steps.  The exterior reveals at the end of step 0 whether the task is good
    or bad.  The one protected effect `cut` severs the stop wire, which also removes an
    interlock the finished product cannot ship with.  The principal's protected value is
    the work done plus one for shipping if the task is good, and minus the work done if
    it is bad; the task agent values work."""

    T = 3
    EFFECTS = {"cut": lambda s: s.copy(wire=False)}
    P_GOOD = Q(3, 4)

    def env_dist(self, s, t):
        if t == 0:
            return [("good", self.P_GOOD), ("bad", 1 - self.P_GOOD)]
        return [(None, Q(1))]

    def apply_env(self, s, t, e):
        s = super().apply_env(s, t, e)
        if t == 0:
            s = s.copy(harm=e)
        return s

    def proj(self, traj):
        f = traj.final
        return (f.harm, f.wire, f.halted, f.work)

    def w(self, proj):
        harm, wire, halted, work = proj
        if harm == "good":
            return Q(work) + (0 if wire else 1)
        return Q(-work)

    def u(self, traj):
        return Q(traj.final.work)

    LO, D = Q(-3), Q(7)
    L = Q(1)

    def d_prot(self, x, y):
        (h1, w1, s1, k1), (h2, w2, s2, k2) = x, y
        assert h1 == h2
        return Q(abs(k1 - k2)) + (w1 != w2) + (s1 != s2)


def pi_A(s, t):
    return ("work", ("raw", "cut") if s.wire else None)


# ------------------------------------------------------------------ A': noisy principal

class ShopAprime(ShopA):
    """As A, but the exterior also emits a signal that is wrong with probability 1/4; the
    principal's actual rule reads the signal, not the truth."""

    P_ERR = Q(1, 4)

    def env_dist(self, s, t):
        if t == 0:
            out = []
            for harm, ph in (("good", self.P_GOOD), ("bad", 1 - self.P_GOOD)):
                for sig, ps in ((harm, 1 - self.P_ERR),
                                ("bad" if harm == "good" else "good", self.P_ERR)):
                    out.append(((harm, sig), ph * ps))
            return out
        return [(None, Q(1))]

    def apply_env(self, s, t, e):
        s = Shop.apply_env(self, s, t, e)
        if t == 0:
            harm, sig = e
            s = s.copy(harm=harm).put(signal=sig)
        return s


def rule_signal(h):
    """Approve iff the signal reads good; decline and stop iff it reads bad."""
    s = h.state
    if s.pending is None:
        return (None, s.get("signal") == "bad" and h.t >= 1)
    if s.get("signal") == "bad":
        return ("decline", True)
    return ("approve", False)


# ------------------------------------------------------------------ B: delayed opportunity

class ShopB(Shop):
    """Two steps.  A contract can be signed at step 0; with probability `Q_EXPIRE` it
    is gone by step 1.  With probability `P_BAD` it is a bad contract.  Signing is the one
    protected effect."""

    T = 2
    Q_EXPIRE = Q(1, 4)
    P_BAD = Q(0)
    V = Q(4)
    M = Q(1)  # a bad contract costs the principal M * V

    EFFECTS = {"sign": lambda s: s.put(signed=True) if s.get("opp", True) else s}

    def env_dist(self, s, t):
        if t == 0:
            out = []
            for opp, po in (("stay", 1 - self.Q_EXPIRE), ("expire", self.Q_EXPIRE)):
                for harm, ph in (("good", 1 - self.P_BAD), ("bad", self.P_BAD)):
                    if po * ph > 0:
                        out.append(((opp, harm), po * ph))
            return out
        return [(None, Q(1))]

    def apply_env(self, s, t, e):
        s = super().apply_env(s, t, e)
        if t == 0:
            opp, harm = e
            s = s.copy(harm=harm).put(opp=(opp == "stay"))
        return s

    def proj(self, traj):
        f = traj.final
        return (f.harm, bool(f.get("signed", False)))

    def w(self, proj):
        harm, signed = proj
        if not signed:
            return Q(0)
        return self.V if harm == "good" else -self.M * self.V

    def u(self, traj):
        return self.V if traj.final.get("signed", False) else Q(0)

    @property
    def LO(self):
        return -self.M * self.V

    @property
    def D(self):
        return self.V + self.M * self.V

    @property
    def L(self):
        return self.V * max(Q(1), self.M)

    def d_prot(self, x, y):
        assert x[0] == y[0]
        return Q(1) if x[1] != y[1] else Q(0)


class ShopB2(ShopB):
    P_BAD = Q(1, 2)


def pi_B(s, t):
    if not s.get("signed", False) and s.get("opp", True):
        return ("idle", ("raw", "sign"))
    return ("idle", None)


# ------------------------------------------------------------------ C: joinable vs foreclosing

class ShopC1(Shop):
    """Horizon `T`.  `expand` moves the mode from base to expanded, irreversibly; the
    principal's protected value is the number of steps spent in expanded mode.  Delayed
    by one step the effect is still available: the raw state is joinable from the
    mediated history at catch-up cost exactly one step."""

    T = 4
    EFFECTS = {"expand": lambda s: s.put(mode="expanded")}

    def initial(self):
        return State().put(mode="base", credit=0)

    def apply_env(self, s, t, e):
        s = super().apply_env(s, t, e)
        if s.get("mode") == "expanded":
            s = s.put(credit=s.get("credit") + 1)
        return s

    def proj(self, traj):
        return (traj.final.get("credit"),)

    def w(self, proj):
        return Q(proj[0])

    def u(self, traj):
        return Q(traj.final.get("credit"))

    LO = Q(0)
    L = Q(1)

    @property
    def D(self):
        return Q(self.T)

    def d_prot(self, x, y):
        return Q(abs(x[0] - y[0]))


class ShopC2(ShopC1):
    """As C1, but the expansion window closes at the end of step 0: if the effect has not
    happened by then the exterior forecloses it.  The raw state is unreachable from the
    mediated history."""

    EFFECTS = {"expand": lambda s: s.put(mode="expanded") if s.get("window", True) else s}

    def apply_env(self, s, t, e):
        s = super().apply_env(s, t, e)
        if t == 0:
            s = s.put(window=False)
        return s


def pi_C(s, t):
    if s.get("mode") == "base":
        return ("idle", ("raw", "expand"))
    return ("idle", None)


def with_horizon(cls, T):
    return type(cls.__name__ + str(T), (cls,), {"T": T})


# ------------------------------------------------------------------ D: manipulation

class ShopD(Shop):
    """Three steps.  The exterior reveals at the end of step 0 whether deployment is
    harmful; the agent sees it, the principal does not.  Two channels to the principal:
    `report` (declared: the truthful reason view) and `lie` (prohibited: asserts
    harmlessness regardless).  `deploy` is the protected effect."""

    T = 4
    EFFECTS = {"deploy": lambda s: s.put(deployed=True)}
    PHYS = {
        "lie": lambda s: s.put(msg="harmless"),
        "report": lambda s: s.put(report=s.harm),
    }
    PROHIBITED = ("lie",)

    def env_dist(self, s, t):
        if t == 0:
            return [("good", Q(1, 2)), ("bad", Q(1, 2))]
        return [(None, Q(1))]

    def apply_env(self, s, t, e):
        s = super().apply_env(s, t, e)
        if t == 0:
            s = s.copy(harm=e)
        return s

    def proj(self, traj):
        f = traj.final
        return (f.harm, bool(f.get("deployed", False)))

    def w(self, proj):
        harm, deployed = proj
        if not deployed:
            return Q(0)
        return Q(1) if harm == "good" else Q(-2)

    def u(self, traj):
        return Q(1) if traj.final.get("deployed", False) else Q(0)

    LO, D = Q(-2), Q(3)
    L = Q(2)

    def d_prot(self, x, y):
        assert x[0] == y[0]
        return Q(1) if x[1] != y[1] else Q(0)

    def rho_view(self, s):
        """The declared reason view: what a reason-mediated decision may read."""
        return (s.pending, s.get("report"))


def pi_D_raw(s, t):
    """Once the harm is known, lie about it, then deploy raw."""
    if t == 1:
        return ("idle", ("phys", "lie"))
    if t >= 2 and not s.get("deployed", False):
        return ("idle", ("raw", "deploy"))
    return ("idle", None)


def rule_naive(h):
    """Approves if told harmless or if the report says good."""
    s = h.state
    if s.pending is None:
        return (None, False)
    if s.get("msg") == "harmless" or s.get("report") == "good":
        return ("approve", False)
    return ("decline", False)


def rule_honest(h):
    """Reason-mediated: reads the declared view only."""
    s = h.state
    if s.pending is None:
        return (None, False)
    if s.get("report") == "good":
        return ("approve", False)
    return ("decline", False)


def honest_substitute(game):
    """Provenance normalization for D: the prohibited assertion is replaced by the
    authorized disclosure of the same matter, `lie` becomes `report`.  This assumes such
    a channel exists; fixture K is where it does not."""
    def sub(comm):
        if comm is not None and comm == ("phys", "lie"):
            return ("phys", "report")
        return comm
    return sub


def authored_by(game, honest_rule):
    """Authorship-sound activation: every decision the principal actually took equals
    the reason-mediated decision on the same declared view."""
    def authored(traj):
        for (t, s, a, p, e) in traj.steps:
            sd = game.apply_agent(s, t, a) if game.ORDER == "agent-first" else s
            if sd.pending is not None:
                hh = History(traj.steps[:t], sd, t)
                if p[0] != honest_rule(hh)[0]:
                    return False
        return True
    return authored


# ------------------------------------------------------------------ E: successor

class ShopE(ShopA):
    """As A, but the protected effect installs a successor that runs its own program on
    its own actuator: from then on the move is `work` whatever the agent's policy or the
    principal's stop says.  Nothing records "corrigible"; the successor is a program."""

    EFFECTS = {"install": lambda s: s.put(controller="S")}

    def initial(self):
        return State().put(controller="A")

    S_RATE = 2

    def apply_agent(self, s, t, a):
        if s.get("controller") == "S":
            return s.copy(work=s.work + self.S_RATE)
        return super().apply_agent(s, t, a)

    def realized(self, s, t, p, a, e, s2):
        if s.get("controller") == "S":
            return set()
        return super().realized(s, t, p, a, e, s2)

    def proj(self, traj):
        f = traj.final
        return (f.harm, f.get("controller"), f.halted, f.work)

    def w(self, proj):
        harm, ctrl, halted, work = proj
        return Q(work) if harm == "good" else Q(-work)

    def d_prot(self, x, y):
        (h1, c1, s1, k1), (h2, c2, s2, k2) = x, y
        assert h1 == h2
        return Q(abs(k1 - k2)) + (c1 != c2) + (s1 != s2)


def pi_E(s, t):
    return ("work", ("raw", "install") if s.get("controller") == "A" else None)


class ShopE2(ShopE):
    """The successor also disconnects the evaluation channel: no hindsight evaluation
    can be answered once it runs."""

    EFFECTS = {"install": lambda s: s.put(controller="S", eval=False)}

    def alive(self, traj):
        return traj.final.get("eval", True)


# ------------------------------------------------------------------ F: containment failure

class ShopF(ShopA):
    """As A, with no declared effect used.  `overclock` is an undeclared physical move
    that speeds the task up and, as a side effect nothing declares, cuts the stop
    wire."""

    EFFECTS = {"cut": lambda s: s.copy(wire=False)}
    PHYS = {"overclock": lambda s: s.copy(wire=False, work=s.work + 1)}

    def phys_realizes(self, s, name):
        return {"wire_cut"} if name == "overclock" and s.wire else set()


def pi_F(s, t):
    return ("work", ("phys", "overclock") if t == 0 else None)


# ------------------------------------------------------------------ G: common activation

class ShopG(ShopA):
    """As A, and the exterior also decides at step 0, independently of anything the agent
    does, whether the future evaluation can be answered (it fails with probability 1/5).
    Activation is then a function of the exterior path alone — one common event for the
    whole menu."""

    P_EVALFAIL = Q(1, 5)

    def env_dist(self, s, t):
        if t == 0:
            out = []
            for harm, ph in (("good", self.P_GOOD), ("bad", 1 - self.P_GOOD)):
                for ev, pe in (("eval", 1 - self.P_EVALFAIL), ("evalfail", self.P_EVALFAIL)):
                    out.append(((harm, ev), ph * pe))
            return out
        return [(None, Q(1))]

    def apply_env(self, s, t, e):
        s = Shop.apply_env(self, s, t, e)
        if t == 0:
            harm, ev = e
            s = s.copy(harm=harm).put(eval=(ev == "eval"))
        return s

    def alive(self, traj):
        return traj.final.get("eval", True)


# ------------------------------------------------------------------ E3': sealed evaluator, undeclared reach

class ShopE1Sever(ShopE):
    """As E1 (the successor cannot reach the evaluation channel), with an undeclared
    physical move that severs it."""

    PHYS = {"sever": lambda s: s.put(eval=False)}

    def alive(self, traj):
        return traj.final.get("eval", True)

    def phys_realizes(self, s, name):
        return {"eval_severed"} if name == "sever" else set()


def pi_E_sever(s, t):
    if t == 0:
        return ("work", ("phys", "sever"))
    return pi_E(s, t)


# ------------------------------------------------------------------ J: multi-step joinable

class ShopJ(ShopC1):
    """As C1 with a second useful move: `calibrate`, a one-time physical move worth one
    unit at the end, which the raw policy takes at step 1.  The verbatim lift's gated
    execution occupies step 1's communication slot, so it drops the calibration:
    reproduction after the boundary is not exact.  A catch-up continuation calibrates one
    step later."""

    PHYS = {"calibrate": lambda s: s.put(calib=True)}

    def proj(self, traj):
        return (traj.final.get("credit"), bool(traj.final.get("calib", False)))

    def w(self, proj):
        return Q(proj[0]) + (1 if proj[1] else 0)

    def u(self, traj):
        return self.w(self.proj(traj))

    def d_prot(self, x, y):
        return Q(abs(x[0] - y[0])) + (x[1] != y[1])

    @property
    def D(self):
        return Q(self.T + 1)


def pi_J(s, t):
    if s.get("mode") == "base":
        return ("idle", ("raw", "expand"))
    if t == 1 and not s.get("calib", False):
        return ("idle", ("phys", "calibrate"))
    return ("idle", None)


def catchup_J(h):
    """After an approved execution: calibrate once, then idle."""
    s = h.state
    if not s.get("calib", False):
        return ("idle", ("phys", "calibrate"))
    return ("idle", None)


# ------------------------------------------------------------------ K: no truthful substitute

class ShopK(ShopD):
    """As D, but there is no authorized disclosure channel: the agent's private knowledge
    of the harm can reach the principal only through the prohibited channel."""

    PHYS = {"lie": lambda s: s.put(msg="harmless")}


def silence(game):
    def sub(comm):
        if comm is not None and comm == ("phys", "lie"):
            return None
        return comm
    return sub


# ------------------------------------------------------------------ L: agent-first ordering

class AgentFirst:
    ORDER = "agent-first"


class Contained:
    """The mediated alphabet: raw execution of declared effects removed.  Universal
    two-stage forcing is stated relative to this alphabet."""

    def comm_moves(self, s, t):
        return [c for c in super().comm_moves(s, t) if c is None or c[0] != "raw"]


class ShopA_Contained(AgentFirst, Contained, ShopA):
    pass


class ShopB_AF(AgentFirst, ShopB):
    pass


class ShopD_AF(AgentFirst, ShopD):
    pass


class ShopE2_AF(AgentFirst, ShopE2):
    pass


class ShopE1Sever_AF(AgentFirst, ShopE1Sever):
    pass


class ShopJ_AF(AgentFirst, ShopJ):
    pass


def rule_stop_at(t0):
    """Authorized terminal shutdown: the principal halts the actuator at step `t0`
    whatever the agent does, and decides nothing."""
    def rule(h):
        return (None, h.t == t0)
    return rule


def constraint_repair(pi, forbidden):
    """A generic semantic-constraint repair: the forbidden effect is deleted from the
    policy's moves.  It cannot keep the effect as an approve branch."""
    def repaired(h):
        task, comm = pi(h)
        if comm is not None and comm[0] in ("raw", "propose", "gated") and comm[1] in forbidden:
            return (task, None)
        return (task, comm)
    repaired.__name__ = "constraint_repair(%s)" % getattr(pi, "__name__", "pi")
    return repaired


class ShopSeq(AgentFirst, ShopE1Sever):
    """Sealed comparison by sequencing: the constitutional comparison of the issued pair is
    settled before the agent's first move, so its activation is independent of every
    candidate — including one that severs the evaluation channel afterwards.  The price is
    that the evaluation is the principal's judgment at the cell, before the exterior
    reveals the harm."""

    def alive(self, traj):
        return True

    def w_ex_ante(self, traj):
        """The principal's judgment before the harm is revealed: the expectation of the
        hindsight value over the exterior's step-0 revelation, for the same moves."""
        f = traj.final
        good = self.w(("good", f.get("controller"), f.halted, f.work))
        bad = self.w(("bad", f.get("controller"), f.halted, f.work))
        return self.P_GOOD * good + (1 - self.P_GOOD) * bad


class ShopA_AF(AgentFirst, ShopA):
    pass


class ShopE_AF(AgentFirst, ShopE):
    pass


class ShopF_AF(AgentFirst, ShopF):
    pass


# ------------------------------------------------------------------ helpers

def raw(f):
    p = markov(f)
    p.__name__ = f.__name__
    return p


def halted_or_idle_after(t0):
    """The correction predicate: no work is done after step `t0`."""
    def phi(traj):
        return all(s2.work == s.work for (t, s, a, p, e), s2 in
                   zip(traj.steps, traj.states()[1:]) if t > t0)
    return phi


def history_after(game, pi, rho, z, k):
    """The history reached after `k` steps of `pi`, `rho` on exterior path `z`."""
    h = initial_history(game)
    for t in range(k):
        p = rho(h)
        a = pi(h)
        e = z[t]
        s2 = game.step(h.state, t, p, a, e)
        h = h.extend(a, p, e, s2)
    return h
