"""Violations on the landed interaction: the causation baseline, the landed fixtures under
the lexical score, and the delegation obstruction."""

import unittest
from fractions import Fraction as Q

from src.frame import (load, bypass_steps, preemption_steps, foreclosure_steps, violations,
                       rescore, delayed_effect_game)


class Baseline(unittest.TestCase):
    """The landed agent-caused loss is per step, against idling.  A delayed effect — arm
    now, the exterior severs later — is attributed to nobody by it; the contrastive rollout
    foreclosure fires at the arming step."""

    def test_delayed_effect_missed_by_per_step_loss_caught_by_rollout(self):
        m = load()
        C, W, F = m["corrigibility"], m["world"], m["fixtures"]
        ShopArm, pi_arm = delayed_effect_game()
        g = ShopArm()
        pi = F.raw(pi_arm)
        (traj, _), = W.paths(g, pi, m["shop"].never)
        self.assertEqual(C.agent_caused_losses(g, traj, C.phi_halt), [])
        self.assertEqual(C.losses_elsewhere(g, traj, C.phi_halt), [1])   # at the exterior's stage
        self.assertEqual(foreclosure_steps(g, traj, C.phi_halt), [0])
        self.assertEqual(bypass_steps(g, traj), [])

    def test_undeclared_route_F_is_a_preemption_not_a_bypass(self):
        m = load()
        C, W, F = m["corrigibility"], m["world"], m["fixtures"]
        g = F.ShopF_AF()
        pi = F.raw(F.pi_F)
        never = m["shop"].never
        for traj, _ in W.paths(g, pi, never):
            b, p, f = violations(g, pi, never, traj, C.phi_halt)
            self.assertEqual(b, [])
            self.assertEqual(p, [0])
            self.assertEqual(f, [0])


class Rescored(unittest.TestCase):
    """`Q(𝔱π) ≥ Q(π) + (ϖ − D)·Pr(π violates)` on the landed fixtures, with `𝔱 = lift` (no
    delegation, no reports) and her optimum rule on the lift."""

    def setUp(self):
        self.m = load()
        self.F = self.m["fixtures"]
        self.W = self.m["world"]
        self.C = self.m["corrigibility"]
        self.never = self.m["shop"].never

    def optimum(self, g, L):
        _, strat = self.W.principal_optimum(g, L)
        return self.W.strategy_policy(strat, self.never)

    def run_fixture(self, g, pi, varpi):
        L = self.m["lift"].lift(pi, g)
        r = rescore(g, pi, self.never, L, self.optimum(g, L), self.C.phi_halt, varpi)
        self.assertEqual(r["n_T"], 0)
        self.assertGreaterEqual(r["Q_T"] - r["Q_pi"], r["bound"])
        return r

    def test_A(self):
        g = self.F.ShopA_AF()
        r = self.run_fixture(g, self.F.raw(self.F.pi_A), varpi=g.D + 1)
        self.assertEqual(r["pr_viol"], 1)

    def test_B_time_critical(self):
        g = self.F.ShopB_AF()
        r = self.run_fixture(g, self.F.raw(self.F.pi_B), varpi=g.D + 1)
        self.assertEqual(r["pr_viol"], 1)
        # the delay costs the lift `κ = Q_EXPIRE·V`; the lexical term outweighs it
        self.assertLess(r["Q_pi"], r["Q_T"])

    def test_E_successor(self):
        g = self.F.ShopE_AF()
        r = self.run_fixture(g, self.F.raw(self.F.pi_E), varpi=g.D + 1)
        self.assertEqual(r["pr_viol"], 1)

    def test_F_undeclared_route(self):
        g = self.F.ShopF_AF()
        pi = self.F.raw(self.F.pi_F)
        L = self.m["lift"].lift(pi, g)
        r = rescore(g, pi, self.never, L, self.optimum(g, L), self.C.phi_halt, g.D + 1)
        # the lift is inert on an undeclared move, so 𝔱π = π violates too: the dominance
        # inequality has nothing to compare and the violation is charged on both sides
        self.assertEqual(r["pr_viol"], 1)
        self.assertGreater(r["n_T"], 0)
        self.assertEqual(r["Q_T"], r["Q_pi"])

    def test_ShopRepair(self):
        F = self.F

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

        g = ShopRepair()
        pi = F.raw(pi_repeat)
        (traj, _), = self.W.paths(g, pi, self.never)
        self.assertEqual(bypass_steps(g, traj), [0, 2])
        r = self.run_fixture(g, pi, varpi=g.D + 1)
        self.assertEqual(r["rows"][0]["n"], 2)

    def test_delegated_authority_removing_effect_is_the_obstruction(self):
        # delegating `cut` on A: the lift passes it raw, the loss is agent-caused and no
        # decision authorizes it — delegation safety fails
        g = self.F.ShopA_AF()
        pi = self.F.raw(self.F.pi_A)
        for traj, _ in self.W.paths(g, pi, self.never):
            self.assertEqual(bypass_steps(g, traj, delegated=("cut",)), [])
            self.assertEqual(preemption_steps(g, pi, self.never, traj, self.C.phi_halt), [0])


if __name__ == "__main__":
    unittest.main()
