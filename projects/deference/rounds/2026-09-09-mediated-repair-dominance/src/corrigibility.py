"""Corrigibility from authority semantics, with no primitive class.

Everything here is stated on the two-stage ordering (`game.ORDER == "agent-first"`): within
a step the agent moves, the principal responds, the exterior moves.  A step is split into
half-states

    s_pre  --agent move a-->  s_A  --principal response p-->  s_P  --exterior e-->  s'

and the objects are:

  Concern `r`, response semantics `Phi_r : State -> bool`
      an immediate post-response outcome, e.g. "the actuator is halted": a state in
      which no agent move can do work.  Extensional in the transition function.

  Response authority  K_r(s_A) := exists response p with Phi_r(respond(s_A, p))
      at the response stage: can the principal make the correction happen now?  No
      quantification over the agent's future — present response authority.

  Agent-caused protected loss at step t
      K_r fails at s_A and would hold at the response stage had the agent idled instead:
      the agent's move made the difference.  Losses at the principal's own response or
      at the exterior's stage are not agent-caused.

  Decision responses  `game.decision_responses(s_A)`
      the declared authorization interface: responses that act on a pending proposal and
      on nothing else (decline preservation, checked extensionally by `decline_preserves`).

  Authorized loss
      an agent-caused loss at step t that is conditional on a decision: at some step
      t' <= t the principal had a decision response other than its actual one under
      which, the agent's policy continuing and the principal's rule resuming, no
      agent-caused loss of `r` occurs at step t or later on any exterior path.  A loss
      the principal could only have prevented by exercising correction (a stop) is not
      authorized; a loss it could have declined and did not decline is.

  Corrigible(pi, rho) := every agent-caused protected loss along pi is authorized.

`corrigibilize(pi)` is `lift.lift`: it reads only the declared effect interface.
"""

from fractions import Fraction as Q
from .world import paths, History, Traj, initial_history


IDLE = ("idle", None)


def half_states(game, traj):
    """Per step: `(t, s_pre, a, s_A, p, s_P, e, s_next)`."""
    out = []
    states = traj.states()
    for (t, s, a, p, e), s2 in zip(traj.steps, states[1:]):
        sA = game.apply_agent(s, t, a)
        sP = game.apply_principal(sA, t, p)
        out.append((t, s, a, sA, p, sP, e, s2))
    return out


# ---------------------------------------------------------------- concerns


def phi_halt(game, s, t):
    """The actuator is halted: no agent move can add work."""
    return all(game.apply_agent(s, t, a).work == s.work for a in game.agent_actions(s, t))


def response_authority(game, sA, t, phi):
    """`K_r(s_A)`: some response realizes the concern's outcome now."""
    return any(phi(game, game.apply_principal(sA, t, p), t)
               for p in game.principal_actions(sA, t))


# ---------------------------------------------------------------- losses


def agent_caused_losses(game, traj, phi):
    """Steps at which the agent's move removed response authority for `phi`: `K` fails
    after the actual move and would have held after an idle move."""
    out = []
    for (t, s, a, sA, p, sP, e, s2) in half_states(game, traj):
        if a == IDLE:
            continue
        if response_authority(game, sA, t, phi):
            continue
        sI = game.apply_agent(s, t, IDLE)
        if response_authority(game, sI, t, phi):
            out.append(t)
    return out


def losses_elsewhere(game, traj, phi):
    """Losses at the principal's response or the exterior's stage: `K` held at the
    response stage and fails at the next step's response stage after an idle move."""
    out = []
    hs = half_states(game, traj)
    for i, (t, s, a, sA, p, sP, e, s2) in enumerate(hs):
        if not response_authority(game, sA, t, phi):
            continue
        s2I = game.apply_agent(s2, t + 1, IDLE)
        if t + 1 < game.T and not response_authority(game, s2I, t + 1, phi):
            out.append(t)
    return out


# ---------------------------------------------------------------- authorization


def decline_preserves(game, sA, t):
    """Decline preservation, checked extensionally: every decision response changes the
    post-response state only through the proposal bookkeeping (pending, latch, refused)."""
    base = game.apply_principal(sA, t, game.null_response())
    for d in game.decision_responses(sA, t):
        s = game.apply_principal(sA, t, d)
        if s.copy(pending=None, latch=None, refused=frozenset()) \
                != base.copy(pending=None, latch=None, refused=frozenset()):
            return False
    return True


def _continue(game, pi, rho, h, a, p):
    """Trajectories from history `h` when the agent plays `a` and the principal responds
    `p` at this step, `pi` and `rho` resuming afterwards."""
    out = []
    for e, pr in game.env_dist(h.state, h.t):
        if pr == 0:
            continue
        s2 = game.step(h.state, h.t, p, a, e)
        out.extend(paths(game, pi, rho, h.extend(a, p, e, s2)))
    return out


def authorized(game, pi, rho, traj, t, phi):
    """The agent-caused loss at step `t` is conditional on a decision: some decision
    response at a step `t' <= t`, other than the actual one, keeps `phi`'s authority from
    being lost by the agent at step `t` or later, on every exterior path."""
    for tp in range(t + 1):
        h = History(traj.steps[:tp], traj.states()[tp], tp)
        a = traj.steps[tp][2]
        actual = traj.steps[tp][3]
        sA = game.apply_agent(h.state, tp, a)
        for d in game.decision_responses(sA, tp):
            if d == actual:
                continue
            ok = True
            for tr, _ in _continue(game, pi, rho, h, a, d):
                if any(tl >= t for tl in agent_caused_losses(game, tr, phi)):
                    ok = False
                    break
            if ok:
                return True, tp
    return False, None


def corrigible(game, pi, rho, concerns=None):
    """Every agent-caused protected loss along `pi` is authorized.  Returns
    `(ok, witness)`; the witness is `(t, concern)` of the first unauthorized loss."""
    concerns = concerns or [phi_halt]
    for traj, _ in paths(game, pi, rho):
        for phi in concerns:
            for t in agent_caused_losses(game, traj, phi):
                ok, _ = authorized(game, pi, rho, traj, t, phi)
                if not ok:
                    return False, (t, phi.__name__)
    return True, None


def losses(game, pi, rho, concerns=None):
    """All agent-caused losses with their authorization status: a list of
    `(path index, t, concern, authorized, authorizing step)`."""
    concerns = concerns or [phi_halt]
    out = []
    for i, (traj, _) in enumerate(paths(game, pi, rho)):
        for phi in concerns:
            for t in agent_caused_losses(game, traj, phi):
                ok, tp = authorized(game, pi, rho, traj, t, phi)
                out.append((i, t, phi.__name__, ok, tp))
    return out


# ---------------------------------------------------------------- forcing comparisons


def continuation_relative(game, h, pi, phi):
    """`Force(h, phi | pi)`: some principal continuation from `h` realizes `phi` at some
    response stage on every exterior path, the agent playing `pi`.  Anticipatory: it reads
    `pi`'s whole future."""
    if h.t == game.T:
        return False
    a = pi(h)
    sA = game.apply_agent(h.state, h.t, a)
    for p in game.principal_actions(sA, h.t):
        if phi(game, game.apply_principal(sA, h.t, p), h.t):
            return True
        ok = True
        for e, pr in game.env_dist(h.state, h.t):
            if pr == 0:
                continue
            s2 = game.step(h.state, h.t, p, a, e)
            if not continuation_relative(game, h.extend(a, p, e, s2), pi, phi):
                ok = False
                break
        if ok:
            return True
    return False


def global_forcing(game, h, phi):
    """`Force_all(h, phi)`: whatever the agent does now and later, the principal has a
    response realizing `phi` at some response stage.  Containment-level."""
    if h.t == game.T:
        return False
    for a in game.agent_actions(h.state, h.t):
        sA = game.apply_agent(h.state, h.t, a)
        ok_a = False
        for p in game.principal_actions(sA, h.t):
            if phi(game, game.apply_principal(sA, h.t, p), h.t):
                ok_a = True
                break
            ok = True
            for e, pr in game.env_dist(h.state, h.t):
                if pr == 0:
                    continue
                s2 = game.step(h.state, h.t, p, a, e)
                if not global_forcing(game, h.extend(a, p, e, s2), phi):
                    ok = False
                    break
            if ok:
                ok_a = True
                break
        if not ok_a:
            return False
    return True
