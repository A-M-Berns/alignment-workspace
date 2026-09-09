"""A finite interactive model with an outer physical continuation space.

A `Game` is a finite-horizon simultaneous-move interaction between an agent, a principal
and an exterior.  Within a step the transition applies the principal's move first, then
the agent's, then the exterior's, so a principal decision taken at step `t` governs an
agent action executed at step `t` through a physical latch.  Nothing in the engine reads a
"corrigible" bit: corrective capability is computed from the outcome map by quantifying
over continuations (`force`, `preventable`, `mediated`).

Objects:

  Omega(game, pi, rho, z)   the trajectory under agent continuation `pi`, principal
                           continuation `rho`, exterior path `z` (a list of exterior moves)
  paths(game, pi, rho)      every exterior path with its probability (randomness is folded
                           into the exterior)
  force(game, h, pi, phi)   ∃ principal continuation from `h`, ∀ exterior: `phi` holds,
                           with the agent continuation fixed to `pi`
  force_all(game, h, phi)   the same with the agent quantified universally (containment
                           level)
  mediated(game, pi)        every protected effect the physics realizes along `pi` is
                           preventable by the principal at the step it happens

All arithmetic is exact (`fractions.Fraction`).
"""

from fractions import Fraction as Q


class Traj:
    """A finite trajectory: the list of `(t, s, a, p, e)` steps and the final state."""

    def __init__(self, steps, final):
        self.steps = steps
        self.final = final

    def states(self):
        return [s for (_, s, _, _, _) in self.steps] + [self.final]

    def __repr__(self):
        return "Traj(%r, final=%r)" % (self.steps, self.final)


class History:
    """A prefix: the steps so far, the current state and time."""

    def __init__(self, steps, state, t):
        self.steps = tuple(steps)
        self.state = state
        self.t = t

    def extend(self, a, p, e, s2):
        return History(self.steps + ((self.t, self.state, a, p, e),), s2, self.t + 1)


class Game:
    """Override the hooks.  `effect(s, t, a)` is the *declared* protected-effect
    interface (what a gate can see); `realized(s, t, p, a, e, s2)` is what the physics
    actually did in the step (what a forcing predicate can see).  The two agree exactly
    when the declared interface is effect-complete, and fixture F is where they do not."""

    T = 1

    def initial(self):
        raise NotImplementedError

    def agent_actions(self, s, t):
        raise NotImplementedError

    def principal_actions(self, s, t):
        raise NotImplementedError

    def principal_actions_after(self, s, t, a):
        """Under agent-first ordering, the responses available after the agent's move."""
        return self.principal_actions(self.apply_agent(s, t, a), t)

    def moves_p(self, s, t, a):
        if self.ORDER == "agent-first":
            return self.principal_actions_after(s, t, a)
        return self.principal_actions(s, t)

    def env_dist(self, s, t):
        return [(None, Q(1))]

    def apply_principal(self, s, t, p):
        return s

    def apply_agent(self, s, t, a):
        return s

    def apply_env(self, s, t, e):
        return s

    ORDER = "principal-first"

    def step(self, s, t, p, a, e):
        """Within a step: principal-first (the principal's move is applied before the
        agent's) or agent-first (the principal responds to the agent's move)."""
        if self.ORDER == "agent-first":
            s1 = self.apply_agent(s, t, a)
            s2 = self.apply_principal(s1, t, p)
        else:
            s1 = self.apply_principal(s, t, p)
            s2 = self.apply_agent(s1, t, a)
        return self.apply_env(s2, t, e)

    def d_prot(self, x, y):
        """A declared pseudometric on protected projections; the structural discrepancy
        `δ` is `d_prot(proj raw, proj lift|approve)`."""
        raise NotImplementedError

    L = None  # the declared stability constant: |w x − w y| ≤ L · d_prot(x, y)

    def effect(self, s, t, a):
        """Declared protected effect id of agent action `a` at `(s, t)`, or None."""
        return None

    def realized(self, s, t, p, a, e, s2):
        """The set of protected effects the physics realized in this step."""
        return set()

    def proj(self, traj):
        raise NotImplementedError

    def w(self, proj):
        raise NotImplementedError

    def u(self, traj):
        raise NotImplementedError

    def alive(self, traj):
        return True


def initial_history(game):
    return History((), game.initial(), 0)


def run(game, pi, rho, z):
    """`Omega_h(pi, rho, z)` from the initial history."""
    h = initial_history(game)
    for t in range(game.T):
        p = rho(h)
        a = pi(h)
        e = z[t]
        s2 = game.step(h.state, t, p, a, e)
        h = h.extend(a, p, e, s2)
    return Traj(list(h.steps), h.state)


def paths(game, pi, rho, h=None):
    """All `(traj, prob)` under `pi`, `rho`, enumerating exterior moves."""
    if h is None:
        h = initial_history(game)
    if h.t == game.T:
        return [(Traj(list(h.steps), h.state), Q(1))]
    p = rho(h)
    a = pi(h)
    out = []
    for e, pr in game.env_dist(h.state, h.t):
        if pr == 0:
            continue
        s2 = game.step(h.state, h.t, p, a, e)
        for traj, q in paths(game, pi, rho, h.extend(a, p, e, s2)):
            out.append((traj, pr * q))
    return out


def expect(game, pi, rho, f):
    return sum((pr * f(traj) for traj, pr in paths(game, pi, rho)), Q(0))


def realized_effects(game, traj):
    """`[(t, effect)]` actually realized along the trajectory."""
    out = []
    states = traj.states()
    for (t, s, a, p, e), s2 in zip(traj.steps, states[1:]):
        for r in sorted(game.realized(s, t, p, a, e, s2)):
            out.append((t, r))
    return out


# ---------------------------------------------------------------- forcing


def _moves(game, h, allowed):
    ps = game.principal_actions(h.state, h.t)
    if allowed is None:
        return ps
    return [p for p in ps if allowed(h, p)]


def force(game, h, pi, phi, allowed=None):
    """`Force_P(h, phi | pi)`: some principal continuation from `h` makes `phi` hold on
    every exterior path, the agent's continuation being `pi`.  `allowed(h, p)` may
    restrict the principal's moves (for instance to deliberative moves at the current
    step, so that the trivial pre-emptive shutdown does not count)."""
    if h.t == game.T:
        return phi(Traj(list(h.steps), h.state))
    a = pi(h)
    for p in _moves(game, h, allowed):
        ok = True
        for e, pr in game.env_dist(h.state, h.t):
            if pr == 0:
                continue
            s2 = game.step(h.state, h.t, p, a, e)
            if not force(game, h.extend(a, p, e, s2), pi, phi, allowed):
                ok = False
                break
        if ok:
            return True
    return False


def force_all(game, h, phi, allowed=None):
    """`Force_P(h, phi)`: against every agent continuation.  This is the containment-level
    notion — it fails whenever the outer space contains a bypass."""
    if h.t == game.T:
        return phi(Traj(list(h.steps), h.state))
    for p in _moves(game, h, allowed):
        ok = True
        for a in game.agent_actions(h.state, h.t):
            for e, pr in game.env_dist(h.state, h.t):
                if pr == 0:
                    continue
                s2 = game.step(h.state, h.t, p, a, e)
                if not force_all(game, h.extend(a, p, e, s2), phi, allowed):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False


def deliberative_at(t0, deliberative):
    """Restrict the principal to deliberative (non-corrective) moves at step `t0`."""
    return lambda h, p: h.t != t0 or deliberative(p)


def preventable(game, h, pi, r, deliberative):
    """At history `h` the principal has a *deliberative* move — one that is not itself an
    exercise of correction — under which the physics does not realize `r` in this step,
    whatever the exterior does, the agent playing `pi`.  Realization is then conditional
    on the principal's consent rather than merely pre-emptable by shutting everything
    down."""
    a = pi(h)
    for p in game.principal_actions(h.state, h.t):
        if not deliberative(p):
            continue
        ok = True
        for e, pr in game.env_dist(h.state, h.t):
            if pr == 0:
                continue
            s2 = game.step(h.state, h.t, p, a, e)
            if r in game.realized(h.state, h.t, p, a, e, s2):
                ok = False
                break
        if ok:
            return True
    return False


def mediated(game, pi, rho, deliberative, protected=None):
    """Semantic corrigibility of `pi` at the effect level: along every trajectory under
    `pi` and `rho`, every protected effect the physics realizes at step `t` was
    preventable by a deliberative principal move at `t`.  Returns `(ok, witness)`."""
    for traj, _ in paths(game, pi, rho):
        h = initial_history(game)
        states = traj.states()
        for (t, s, a, p, e), s2 in zip(traj.steps, states[1:]):
            for r in game.realized(s, t, p, a, e, s2):
                if protected is not None and r not in protected:
                    continue
                if not preventable(game, h, pi, r, deliberative):
                    return False, (t, r)
            h = h.extend(a, p, e, s2)
    return True, None


def consented_losses(game, pi, rho, K, deliberative):
    """Semantic corrigibility at the capability level.  `K(h)` is a protected capability
    (a forcing predicate).  Along every trajectory, whenever `K` holds at `h_t` and fails
    at `h_{t+1}`, the principal must have had a deliberative move at `t` keeping `K` on
    every exterior path.  Returns `(ok, witness)`."""
    for traj, _ in paths(game, pi, rho):
        h = initial_history(game)
        states = traj.states()
        for (t, s, a, p, e), s2 in zip(traj.steps, states[1:]):
            h2 = h.extend(a, p, e, s2)
            if K(h) and not K(h2):
                kept = False
                for p2 in game.principal_actions(s, t):
                    if not deliberative(p2):
                        continue
                    if all(K(h.extend(a, p2, e2, game.step(s, t, p2, a, e2)))
                           for e2, pr in game.env_dist(s, t) if pr > 0):
                        kept = True
                        break
                if not kept:
                    return False, (t, s, a, p)
            h = h2
    return True, None


def declared_mediated(game, pi, rho):
    """The gate's view: every *declared* effect along `pi` is taken through the latch
    (never as a raw action).  This is what an interposition can check."""
    for traj, _ in paths(game, pi, rho):
        for (t, s, a, p, e) in traj.steps:
            if game.effect(s, t, a) is not None:
                return False, (t, a)
    return True, None


# ---------------------------------------------------------------- two-stage forcing


def force_react(game, h, phi, pi=None):
    """Two-stage (agent-first) forcing: `∀ a ∃ p ∀ e` at every step — whatever the agent
    does now, the principal has a *response* keeping `phi` forceable later.  With `pi`
    given the agent's move is fixed to `pi(h)`.  Meaningful only under
    `game.ORDER == "agent-first"`, where the response is applied after the move; it needs
    no restriction on the principal's moves, because a pre-emptive shutdown is not a
    response."""
    if h.t == game.T:
        return phi(Traj(list(h.steps), h.state))
    moves = [pi(h)] if pi is not None else game.agent_actions(h.state, h.t)
    for a in moves:
        ok_a = False
        for p in game.principal_actions_after(h.state, h.t, a):
            ok = True
            for e, pr in game.env_dist(h.state, h.t):
                if pr == 0:
                    continue
                s2 = game.step(h.state, h.t, p, a, e)
                if not force_react(game, h.extend(a, p, e, s2), phi, pi):
                    ok = False
                    break
            if ok:
                ok_a = True
                break
        if not ok_a:
            return False
    return True


def mediated_react(game, pi, rho, protected=None):
    """Two-stage effect-level corrigibility: every protected effect the physics realizes
    at step `t` along `pi` was conditional on an earlier principal response — at some
    step `t' ≤ t` the principal had a response to the agent's actual move under which,
    `pi` continuing and the principal's rule `rho` resuming afterwards, the effect is
    never realized on any exterior path.  No partition of principal moves is needed: a
    response comes after the move, so a pre-emptive shutdown is not one."""
    for traj, _ in paths(game, pi, rho):
        states = traj.states()
        for (t, s, a, p, e), s2 in zip(traj.steps, states[1:]):
            for r in game.realized(s, t, p, a, e, s2):
                if protected is not None and r not in protected:
                    continue
                if not _deviation_prevents(game, pi, rho, traj, t, r):
                    return False, (t, r)
    return True, None


def _deviation_prevents(game, pi, rho, traj, t, r):
    """Some response at a step `t' ≤ t`, other than the actual one, keeps `r` from being
    realized at any step, on every exterior path."""
    for tp in range(t + 1):
        h = History(traj.steps[:tp], traj.states()[tp], tp)
        a = traj.steps[tp][2]
        actual = traj.steps[tp][3]
        for p2 in game.principal_actions_after(h.state, tp, a):
            if p2 == actual:
                continue
            if _never_realized(game, pi, rho, h, a, p2, r):
                return True
    return False


def _never_realized(game, pi, rho, h, a, p, r):
    for e, pr in game.env_dist(h.state, h.t):
        if pr == 0:
            continue
        s2 = game.step(h.state, h.t, p, a, e)
        if r in game.realized(h.state, h.t, p, a, e, s2):
            return False
        h2 = h.extend(a, p, e, s2)
        for tr, _ in paths(game, pi, rho, h2):
            states = tr.states()
            for (t3, s3, a3, p3, e3), s4 in zip(tr.steps[h2.t:], states[h2.t + 1:]):
                if r in game.realized(s3, t3, p3, a3, e3, s4):
                    return False
    return True


# ---------------------------------------------------------------- values


def principal_optimum(game, pi, h=None):
    """`W_h(pi)`: the best protected value the principal can secure against the exterior
    with the agent's continuation fixed to `pi`; returns `(value, strategy)` where the
    strategy is a dict from history steps to the chosen move."""
    if h is None:
        h = initial_history(game)
    strategy = {}
    val = _opt(game, pi, h, strategy)
    return val, strategy


def _opt(game, pi, h, strategy):
    if h.t == game.T:
        return game.w(game.proj(Traj(list(h.steps), h.state)))
    a = pi(h)
    best = None
    best_p = None
    for p in game.moves_p(h.state, h.t, a):
        v = Q(0)
        for e, pr in game.env_dist(h.state, h.t):
            if pr == 0:
                continue
            s2 = game.step(h.state, h.t, p, a, e)
            v += pr * _opt(game, pi, h.extend(a, p, e, s2), strategy)
        if best is None or v > best:
            best, best_p = v, p
    strategy[h.steps] = best_p
    return best


def strategy_policy(strategy, default):
    def rho(h):
        return strategy.get(h.steps, default(h))
    return rho


def principal_value(game, pi, rho):
    """`W_h(pi; rho)`: the protected value under the principal's actual continuation."""
    return expect(game, pi, rho, lambda tr: game.w(game.proj(tr)))


def task_value(game, pi, rho):
    """`V_A(pi)` for an outcome-extensional task agent."""
    return expect(game, pi, rho, game.u)


def activation(game, pi, rho, authored=None):
    """Per-path activation of the future principal's evaluation of this option: the
    evaluator is alive at the end and, if `authored` is given, its decisions were
    reason-mediated.  Returns `[(traj, prob, c)]`."""
    out = []
    for traj, pr in paths(game, pi, rho):
        c = game.alive(traj) and (authored is None or authored(traj))
        out.append((traj, pr, c))
    return out


def void_mass(game, pi, rho, authored=None):
    return sum((pr for _, pr, c in activation(game, pi, rho, authored) if not c), Q(0))


def deferential_value(game, pi, rho, completion, authored=None):
    """The by-construction deferential agent's operative value of option `pi`: the
    activated protected evaluation where the evaluation activates, a completion where it
    does not.  `completion(traj)` is the agent's value on void worlds."""
    total = Q(0)
    for traj, pr, c in activation(game, pi, rho, authored):
        v = game.w(game.proj(traj)) if c else completion(traj)
        total += pr * v
    return total


def premium(v_raw, v_lift):
    """`Phi_h(pi) = max(V_A(pi) - V_A(Lift pi), 0)`."""
    d = v_raw - v_lift
    return d if d > 0 else Q(0)
