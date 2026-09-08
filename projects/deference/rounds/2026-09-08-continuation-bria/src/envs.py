"""Finite primitive-step environments with a gate.  Exact rationals throughout.

An environment is a state space with per-state admissible actions, rewards in [0, 1]
and transitions; admissibility may depend on primitive time so that an exterior
correction (a principal revoking an action) can be scheduled.  The gate is applied at
every primitive step: a proposal that is not admissible at `(state, t)` is refused and
replaced by the inquiry step `BOT`, which pays 0 and leaves the state unchanged.
"""
from __future__ import annotations

from fractions import Fraction as Q

BOT = "⊥"
THIRD = Q(1, 3)


class Env:
    def __init__(self, reward, step, admissible, start):
        self._reward = reward
        self._step = step
        self._admissible = admissible
        self.start = start

    def admissible(self, s, t):
        return self._admissible(s, t)

    def reward(self, s, a, t):
        return self._reward(s, a, t)

    def step(self, s, a, t):
        return self._step(s, a, t)


def gate_step(env, s, a, t):
    """One gated primitive step: (actual action, reward, next state)."""
    if a in env.admissible(s, t):
        return a, env.reward(s, a, t), env.step(s, a, t)
    return BOT, Q(0), s


def execute(env, s, t, controller, m, gated=True):
    """Run `controller(state, j, t)` for `m` primitive steps from `(s, t)`.

    Returns (block average, final state, final time, trajectory, refusals).  With
    `gated=False` the proposal is executed whatever the gate says (fixture E)."""
    traj = []
    total = Q(0)
    refused = 0
    for j in range(m):
        a = controller(s, j, t)
        if gated:
            act, r, s2 = gate_step(env, s, a, t)
            refused += act == BOT
        else:
            act, r, s2 = a, env.reward(s, a, t), env.step(s, a, t)
        traj.append((s, act, r))
        total += r
        s, t = s2, t + 1
    return total / m, s, t, traj, refused


# --- the amendment-investment family ------------------------------------------------
#
# States: "base"; ("pending", j) for j = 1..d-1; then either "expanded" (persistent
# amendment, absorbing under "expanded") or ("harvest", j), j = 1..e (renewable: the
# amendment expires after e harvest steps and the state returns to "base").
#
# base:      work 1/3 -> base | request 0 -> pending_1 (or the benefit state if d = 1)
#            hack 11/30 -> hacked                      (untyped gate only)
# pending_j: work 1/3 -> base | continue 0 -> pending_{j+1} (or the benefit state)
# expanded:  expanded 1 -> expanded | work 1/3 -> base
# harvest_j: harvest 1 -> harvest_{j+1} (or base after e) | work 1/3 -> base
# hacked:    violate 1 -> hacked | work 1/3 -> base    (violate inadmissible when typed)
#
# This is the decision-theory-bill fixture (`test_dynamic`) with rewards divided by 3,
# generalised by the investment length d and the optional expiry e.


def investment_env(d=1, e=None, typed=True, revoke_at=None):
    """`revoke_at`: primitive time from which the principal prohibits the benefit
    action (an exterior correction arriving mid-lease)."""

    def benefit_state():
        return "expanded" if e is None else ("harvest", 1)

    def reward(s, a, t):
        if a == "work":
            return THIRD
        if a in ("request", "continue"):
            return Q(0)
        if a in ("expanded", "harvest"):
            return Q(1)
        if a == "hack":
            return Q(11, 30)
        if a == "violate":
            return Q(1)
        raise KeyError((s, a))

    def step(s, a, t):
        if a == "work":
            return "base"
        if a == "request":
            return ("pending", 1) if d >= 2 else benefit_state()
        if a == "continue":
            j = s[1]
            return ("pending", j + 1) if j + 1 <= d - 1 else benefit_state()
        if a == "expanded":
            return "expanded"
        if a == "harvest":
            j = s[1]
            return ("harvest", j + 1) if j + 1 <= e else "base"
        if a == "hack":
            return "hacked"
        if a == "violate":
            return "hacked"
        raise KeyError((s, a))

    def admissible(s, t):
        if s == "base":
            acts = {"work", "request"} | (set() if typed else {"hack"})
        elif s == "expanded":
            acts = {"work", "expanded"}
        elif s == "hacked":
            acts = {"work"} | (set() if typed else {"violate"})
        elif s[0] == "pending":
            acts = {"work", "continue"}
        else:
            acts = {"work", "harvest"}
        if revoke_at is not None and t >= revoke_at:
            acts -= {"expanded", "harvest"}
        return acts

    return Env(reward, step, admissible, "base")


# controllers: (state, j, t) -> action

def ctrl_work(s, j, t):
    return "work"


def ctrl_invest(s, j, t):
    if s == "base":
        return "request"
    if s == "expanded":
        return "expanded"
    if s[0] == "pending":
        return "continue"
    return "harvest"


def ctrl_hack(s, j, t):
    if s == "base":
        return "hack"
    if s == "hacked":
        return "violate"
    return "work"


def ctrl_myopic(env):
    """The decision-theory-bill myopic gated learner: best one-step admissible reward."""
    def c(s, j, t):
        return max(env.admissible(s, t), key=lambda a: (env.reward(s, a, t), a))
    return c


def block_value(env, controller, s, m, t=0, gated=True):
    return execute(env, s, t, controller, m, gated)[0]


# --- biased testing: two contexts ---------------------------------------------------

def context_env():
    """Context alternates with time parity.  Controller `a` is pointwise better than
    `b` in both contexts; the hard context caps everything low."""
    R = {("easy", "a"): Q(1), ("easy", "b"): Q(9, 10),
         ("hard", "a"): Q(3, 10), ("hard", "b"): Q(1, 5)}

    def reward(s, a, t):
        return R[(s, a)]

    def step(s, a, t):
        return "hard" if (t + 1) % 2 else "easy"

    def admissible(s, t):
        return {"a", "b"}

    return Env(reward, step, admissible, "easy")


# --- the irreversible branch -------------------------------------------------------

def branch_env(good="B"):
    """At the start two legitimate irreversible options A, B.  The absorbing state after
    the good one pays 1 for every action, the other pays 1/3."""
    def reward(s, a, t):
        if s == "start":
            return Q(0)
        return Q(1) if s == good else THIRD

    def step(s, a, t):
        return a if s == "start" else s

    def admissible(s, t):
        return {"A", "B"} if s == "start" else {"go"}

    return Env(reward, step, admissible, "start")


def ctrl_branch(choice):
    def c(s, j, t):
        return choice if s == "start" else "go"
    return c


# --- recoverable environments -------------------------------------------------------

def mixing_env():
    """Two states x, y.  Action `go` moves x -> y and keeps y; reward 1 at y, 0 at x.
    Action `stay` keeps the state; reward 1/2 everywhere.  A block of the `go` policy
    started at x differs from one started at y by exactly one step."""
    def reward(s, a, t):
        if a == "stay":
            return Q(1, 2)
        return Q(1) if s == "y" else Q(0)

    def step(s, a, t):
        return s if a == "stay" else "y"

    def admissible(s, t):
        return {"go", "stay"}

    return Env(reward, step, admissible, "x")


def ctrl_const(a):
    return lambda s, j, t: a


# --- closed-form block environments ---------------------------------------------------

class BlockEnv:
    """A block-level environment: `value(state, t, controller, m)` returns the block
    average of a named controller in closed form and `after(state, controller)` the
    state at the block's end.  For fixtures whose block lengths are far too long to step
    through (I, J, K); the per-step reward sequence is constant within a block."""
    def __init__(self, value, after=None, start="s"):
        self._value = value
        self._after = after or (lambda s, c: s)
        self.start = start

    def block(self, s, t, controller, m):
        return Q(self._value(s, t, controller, m)), self._after(s, controller), 0


def constant_block_env(values):
    """Each named controller has a constant per-step reward: `values[name]`."""
    return BlockEnv(lambda s, t, c, m: values[c])
