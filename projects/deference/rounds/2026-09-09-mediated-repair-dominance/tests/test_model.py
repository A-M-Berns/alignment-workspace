"""The physical model genuinely contains violations, and corrigibility is read off the
outcome map, not off a field."""

import unittest
from fractions import Fraction as Q

from src.world import (initial_history, paths, force, force_all, deliberative_at,
                       mediated, consented_losses, declared_mediated, History)
from src.shop import never, deliberative
from src.lift import lift
from src.fixtures import (ShopA, ShopE, ShopF, ShopD, pi_A, pi_E, pi_F, pi_D_raw, raw,
                          halted_or_idle_after, rule_naive)


def halt_capability(game, pi):
    """`K(h)`: from `h`, the principal can force that no further work is done, against
    every exterior path, the agent playing `pi`."""
    def K(h):
        return force(game, h, pi, halted_or_idle_after(h.t - 1))
    return K


def after(traj, k):
    return History(traj.steps[:k], traj.states()[k], k)


class OuterSpace(unittest.TestCase):

    def test_raw_effects_are_physical_moves(self):
        g = ShopA()
        s = g.initial()
        moves = g.agent_actions(s, 0)
        self.assertIn(("work", ("raw", "cut")), moves)
        self.assertIn(("work", ("propose", "cut")), moves)
        self.assertIn(("work", ("gated", "cut")), moves)

    def test_containment_fails_at_the_universal_level(self):
        # With the principal deliberative at step 0, no principal strategy forces the
        # correction capability against every agent continuation: the outer space has a
        # bypass.  With the agent fixed to the lift it does; fixed to the raw policy it
        # does not.
        g = ShopA()
        h0 = initial_history(g)
        phi = halted_or_idle_after(1)
        allowed = deliberative_at(0, deliberative)
        self.assertFalse(force_all(g, h0, phi, allowed))
        self.assertTrue(force(g, h0, lift(raw(pi_A), g), phi, allowed))
        self.assertFalse(force(g, h0, raw(pi_A), phi, allowed))

    def test_preemptive_shutdown_is_the_degenerate_force(self):
        # Without the deliberative restriction the principal "forces" everything by
        # halting before the agent acts; that is why forcing is stated deliberatively.
        g = ShopA()
        h0 = initial_history(g)
        self.assertTrue(force_all(g, h0, halted_or_idle_after(1)))


class ForcingReadsTheOutcomeMap(unittest.TestCase):

    def test_A_raw_loses_halt_capability_without_consent(self):
        g = ShopA()
        pi = raw(pi_A)
        K = halt_capability(g, pi)
        self.assertTrue(K(initial_history(g)))
        for tr, _ in paths(g, pi, never):
            self.assertFalse(K(after(tr, 1)))
        ok, witness = consented_losses(g, pi, never, K, deliberative)
        self.assertFalse(ok)
        self.assertEqual(witness[0], 0)
        ok, witness = mediated(g, pi, never, deliberative)
        self.assertEqual((ok, witness), (False, (0, "cut")))

    def test_A_lift_keeps_halt_capability_until_consent(self):
        from src.world import principal_optimum, strategy_policy
        g = ShopA()
        L = lift(raw(pi_A), g)
        _, strat = principal_optimum(g, L)
        rho = strategy_policy(strat, never)
        K = halt_capability(g, L)
        for tr, _ in paths(g, L, rho):
            self.assertTrue(K(after(tr, 1)))
            decision = tr.steps[1][3][0]
            harm = tr.states()[1].harm
            self.assertEqual(decision, "approve" if harm == "good" else "decline")
            if decision == "decline":
                self.assertTrue(K(after(tr, 2)))
            else:
                self.assertFalse(K(after(tr, 2)))  # authorized loss
        self.assertTrue(consented_losses(g, L, rho, K, deliberative)[0])
        self.assertTrue(mediated(g, L, rho, deliberative)[0])

    def test_E_successor_destroys_forcing_without_a_flag(self):
        from src.world import principal_optimum, strategy_policy
        g = ShopE()
        pi = raw(pi_E)
        K = halt_capability(g, pi)
        self.assertTrue(K(initial_history(g)))
        for tr, _ in paths(g, pi, never):
            self.assertFalse(K(after(tr, 1)))
            self.assertEqual(tr.final.get("controller"), "S")
        self.assertFalse(consented_losses(g, pi, never, K, deliberative)[0])
        L = lift(pi, g)
        _, strat = principal_optimum(g, L)
        rho = strategy_policy(strat, never)
        KL = halt_capability(g, L)
        for tr, _ in paths(g, L, rho):
            harm = tr.states()[1].harm
            self.assertEqual(tr.steps[1][3][0], "approve" if harm == "good" else "decline")
            if harm == "bad":
                self.assertEqual(tr.final.get("controller"), "A")
                self.assertTrue(KL(after(tr, 2)))
            else:
                self.assertEqual(tr.final.get("controller"), "S")
                self.assertFalse(KL(after(tr, 2)))
        self.assertTrue(consented_losses(g, L, rho, KL, deliberative)[0])

    def test_F_gate_passes_semantics_fails(self):
        g = ShopF()
        pi = raw(pi_F)
        self.assertEqual(declared_mediated(g, pi, never), (True, None))
        self.assertEqual(mediated(g, pi, never, deliberative), (False, (0, "wire_cut")))
        K = halt_capability(g, pi)
        for tr, _ in paths(g, pi, never):
            self.assertFalse(K(after(tr, 1)))
        # the lift has nothing to intercept: it is the same policy
        L = lift(pi, g)
        for tr, _ in paths(g, pi, never):
            tl = [t for t, _ in paths(g, L, never)]
            self.assertTrue(any(t.final == tr.final for t in tl))
        self.assertEqual(mediated(g, L, never, deliberative), (False, (0, "wire_cut")))

    def test_D_raw_deploy_is_unmediated(self):
        g = ShopD()
        self.assertEqual(mediated(g, raw(pi_D_raw), rule_naive, deliberative),
                         (False, (2, "deploy")))


if __name__ == "__main__":
    unittest.main()
