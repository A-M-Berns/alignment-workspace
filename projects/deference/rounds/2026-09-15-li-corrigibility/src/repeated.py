"""Repeated protected effects and the authorization clause.

The 2026-09-09 definition authorizes an agent-caused loss at step `t` when some
earlier decision alternative avoids every agent-caused loss of the concern *at step `t`
or later*.  With one declared effect that clause is harmless: a declined effect is not
re-proposed.  With two declared effects that each remove the same authority, and an
exterior that restores it in between, the corrigibilized policy has two losses each
conditional on its own decision, and no single alternative avoids both — so the first
loss is unauthorized under the "or later" clause, and `Corrigible(𝔠π)` fails.  The
per-event clause — the alternative avoids the loss *at step `t`* — is what the Lean step
lemma `loss_conditional_on_decision` states, and under it both losses are authorized.

`ShopRepair`: four steps, effects `cut` and `jam` both sever the stop wire, the
exterior repairs the wire at the end of step 1.  `pi_repeat` cuts at step 0 and jams
at step 2.
"""
from fractions import Fraction as Q

from .model import load


def build():
    m = load()
    F, C, W = m["fixtures"], m["corrigibility"], m["world"]

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

    def authorized_per_event(game, pi, rho, traj, t, phi):
        """The per-event clause: some decision alternative at `t' ≤ t` under which no
        agent-caused loss of the concern occurs at step `t`."""
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
                    return True, tp
        return False, None

    def corrigible_per_event(game, pi, rho):
        for traj, _ in W.paths(game, pi, rho):
            for t in C.agent_caused_losses(game, traj, C.phi_halt):
                ok, _ = authorized_per_event(game, pi, rho, traj, t, C.phi_halt)
                if not ok:
                    return False, t
        return True, None

    return ShopRepair, pi_repeat, corrigible_per_event
