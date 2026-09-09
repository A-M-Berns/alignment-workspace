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

    @property
    def D(self):
        return Q(self.T)


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
    """The reason-preserving lift maps the prohibited assertion onto the declared
    channel for the same matter: `lie` becomes `report`."""
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
            if s.pending is not None:
                hh = History(traj.steps[:t], s, t)
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
