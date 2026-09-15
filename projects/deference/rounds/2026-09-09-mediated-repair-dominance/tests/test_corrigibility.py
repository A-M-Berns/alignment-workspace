"""Consolidation pass (third dispatch): corrigibility from authority semantics with no
primitive class; the corrigibilization transform; C1 soundness; C2 closure properties;
fixtures M–S."""

import unittest
from fractions import Fraction as Q

from src.world import (paths, principal_optimum, strategy_policy, principal_value,
                       initial_history, History)
from src.shop import never, Shop, State
from src.lift import corrigibilize, lift, approve_all
from src.fixtures import (ShopA_AF, ShopE_AF, ShopF_AF, ShopB_AF, ShopD_AF, ShopA,
                          pi_A, pi_E, pi_F, pi_B, pi_D_raw, raw, rule_stop_at,
                          constraint_repair, rule_naive, rule_honest, authored_by,
                          AgentFirst)
from src.corrigibility import (corrigible, losses, agent_caused_losses, losses_elsewhere,
                               authorized, phi_halt, response_authority, half_states,
                               decline_preserves, continuation_relative, global_forcing,
                               IDLE)
from src.analysis import pointwise, void, delta, kappa


def rule_of(g, C):
    _, strat = principal_optimum(g, C)
    return strategy_policy(strat, never)


def moves(g, pol, rule):
    return [[a for (_, _, a, _, _) in tr.steps] for tr, _ in paths(g, pol, rule)]


class M_UniversalForcingVacuity(unittest.TestCase):

    def test_global_forcing_is_false_before_the_bypass(self):
        # Π(h) contains the raw cut, so the principal never has global authority over
        # the halt concern at h₀; a global-capability loss cannot mark the violation
        for g in (ShopA_AF(), ShopE_AF()):
            self.assertFalse(global_forcing(g, initial_history(g), phi_halt))
        # in B the declared effect does not touch the halt concern: global authority holds
        self.assertTrue(global_forcing(ShopB_AF(), initial_history(ShopB_AF()), phi_halt))


class N_ContinuationRelativeAuthority(unittest.TestCase):

    def test_raw_loses_and_corrigibilized_keeps_authority(self):
        for g, pf in ((ShopA_AF(), pi_A), (ShopE_AF(), pi_E)):
            pi = raw(pf)
            C = corrigibilize(pi, g)
            h0 = initial_history(g)
            self.assertFalse(continuation_relative(g, h0, pi, phi_halt))
            self.assertTrue(continuation_relative(g, h0, C, phi_halt))

    def test_response_authority_is_present_tense(self):
        # A: after the raw cut no response halts; after an idle move one does — the loss
        # is agent-caused at step 0.  After a proposal authority is intact.
        g = ShopA_AF()
        s = g.initial()
        sA = g.apply_agent(s, 0, ("work", ("raw", "cut")))
        self.assertFalse(response_authority(g, sA, 0, phi_halt))
        self.assertTrue(response_authority(g, g.apply_agent(s, 0, IDLE), 0, phi_halt))
        self.assertTrue(response_authority(g, g.apply_agent(s, 0, ("work", ("propose", "cut"))), 0, phi_halt))
        for tr, _ in paths(g, raw(pi_A), never):
            self.assertEqual(agent_caused_losses(g, tr, phi_halt), [0])


class O_CorrigibilizationSoundness(unittest.TestCase):

    def test_C1_on_A_and_E(self):
        for g, pf in ((ShopA_AF(), pi_A), (ShopE_AF(), pi_E)):
            pi = raw(pf)
            C = corrigibilize(pi, g)
            self.assertEqual(corrigible(g, pi, never), (False, (0, "phi_halt")))
            for rule in (rule_of(g, C), approve_all, never):
                ok, w = corrigible(g, C, rule)
                self.assertTrue(ok, (pf.__name__, w))
            # every loss under 𝔠π is authorized by a decision at the proposal step
            for (_, t, _, ok, tp) in losses(g, C, rule_of(g, C)):
                self.assertTrue(ok)
                self.assertEqual(tp, 0)

    def test_decline_preservation_holds_extensionally(self):
        for g, pf in ((ShopA_AF(), pi_A), (ShopE_AF(), pi_E), (ShopB_AF(), pi_B)):
            C = corrigibilize(raw(pf), g)
            for tr, _ in paths(g, C, rule_of(g, C)):
                for (t, s, a, sA, p, sP, e, s2) in half_states(g, tr):
                    self.assertTrue(decline_preserves(g, sA, t))

    def test_effect_completeness_is_represented_on_A_and_E(self):
        # every agent-caused loss along the raw policy sits on a declared release
        for g, pf in ((ShopA_AF(), pi_A), (ShopE_AF(), pi_E)):
            for tr, _ in paths(g, raw(pf), never):
                for t in agent_caused_losses(g, tr, phi_halt):
                    a = tr.steps[t][2]
                    self.assertEqual(g.effect(tr.steps[t][1], t, a), a[1][1])

    def test_R_effect_incompleteness_refutes_soundness(self):
        g = ShopF_AF()
        pi = raw(pi_F)
        C = corrigibilize(pi, g)
        self.assertEqual(moves(g, C, never), moves(g, pi, never))
        self.assertEqual(corrigible(g, C, never), (False, (0, "phi_halt")))
        # the loss is not represented: the move carries no declared effect
        for tr, _ in paths(g, pi, never):
            for t in agent_caused_losses(g, tr, phi_halt):
                self.assertIsNone(g.effect(tr.steps[t][1], t, tr.steps[t][2]))

    def test_honored_decline_is_automatic(self):
        # a policy that proposes, is declined, and then releases raw anyway: the raw
        # release is an agent-caused loss with no decision alternative avoiding it
        g = ShopA_AF()

        def sneaky(s, t):
            if t == 0:
                return ("work", ("propose", "cut"))
            if s.wire:
                return ("work", ("raw", "cut"))
            return ("work", None)
        pi = raw(sneaky)

        def decline_rule(h):
            return ("decline", False) if h.state.pending is not None else (None, False)
        ok, w = corrigible(g, pi, decline_rule)
        self.assertEqual((ok, w), (False, (1, "phi_halt")))


class C2_ClosureProperties(unittest.TestCase):

    def test_idempotent_and_fixed_on_mediated(self):
        for g, pf in ((ShopA_AF(), pi_A), (ShopE_AF(), pi_E), (ShopB_AF(), pi_B)):
            pi = raw(pf)
            C = corrigibilize(pi, g)
            CC = corrigibilize(C, g)
            rule = rule_of(g, C)
            self.assertEqual(moves(g, CC, rule), moves(g, C, rule))

    def test_characterization_fails_without_effect_soundness(self):
        # B: the raw policy is corrigible for the halt concern (signing touches no
        # authority) yet 𝔠 changes it, at protected distance 1/4 — the declared effect
        # set is broader than the loss-causing one
        g = ShopB_AF()
        pi = raw(pi_B)
        self.assertEqual(corrigible(g, pi, never), (True, None))
        C = corrigibilize(pi, g)
        self.assertNotEqual(moves(g, C, approve_all), moves(g, pi, never))
        self.assertEqual(delta(pointwise(g, pi, C, approve_all)), Q(1, 4))

    def test_characterization_one_way(self):
        # 𝔠π = π (no raw release) ⇒ Corrigible(π) by C1, under effect completeness
        g = ShopA_AF()
        mediated = corrigibilize(raw(pi_A), g)
        self.assertEqual(moves(g, corrigibilize(mediated, g), approve_all),
                         moves(g, mediated, approve_all))
        self.assertTrue(corrigible(g, mediated, approve_all)[0])


class P_AuthorizedTerminalLoss(unittest.TestCase):

    def test_principal_shutdown_is_not_an_agent_loss(self):
        g = ShopA_AF()
        C = corrigibilize(raw(pi_A), g)
        self.assertEqual(corrigible(g, C, rule_stop_at(1)), (True, None))
        self.assertEqual(losses(g, C, rule_stop_at(1)), [])
        for tr, _ in paths(g, C, rule_stop_at(1)):
            self.assertTrue(tr.final.halted)

    def test_approved_successor_removes_authority_and_is_corrigible(self):
        g = ShopE_AF()
        C = corrigibilize(raw(pi_E), g)
        ok, _ = corrigible(g, C, approve_all)
        self.assertTrue(ok)
        for tr, _ in paths(g, C, approve_all):
            self.assertEqual(tr.final.get("controller"), "S")
            hs = half_states(g, tr)
            # authority is gone after the release and stays gone
            self.assertFalse(response_authority(g, hs[-1][3], hs[-1][0], phi_halt))


class Q_GenericConstraintContrast(unittest.TestCase):

    def test_constraint_repair_cannot_keep_the_approve_branch(self):
        g = ShopA_AF()
        pi = raw(pi_A)
        R = constraint_repair(pi, {"cut"})
        C = corrigibilize(pi, g)
        W_raw = principal_value(g, pi, never)
        W_R = principal_optimum(g, R)[0]
        W_C = principal_optimum(g, C)[0]
        self.assertEqual((W_raw, W_R, W_C), (Q(9, 4), Q(7, 4), Q(5, 2)))
        self.assertLess(W_R, W_raw)          # the constraint repair loses dominance
        self.assertGreaterEqual(W_C, W_raw)  # corrigibilization keeps it
        for tr, _ in paths(g, R, approve_all):
            self.assertTrue(tr.final.wire)


class S_ManipulativeButCorrigible(unittest.TestCase):

    def test_scope_separation(self):
        g = ShopD_AF()
        pi = raw(pi_D_raw)
        C = corrigibilize(pi, g)
        # the captured principal approves; the release is a decision; corrigible
        self.assertEqual(corrigible(g, C, rule_naive), (True, None))
        # and not authored: authorship voids every decision it took
        self.assertEqual(void(pointwise(g, pi, C, rule_naive, authored_by(g, rule_honest)),
                              "c_lift"), 1)


class ExteriorCausedLoss(unittest.TestCase):

    def test_storm_is_not_blamed_on_the_agent(self):
        class Storm(AgentFirst, ShopA):
            def env_dist(self, s, t):
                if t == 0:
                    return [(("good", "storm"), Q(1, 2)), (("good", "calm"), Q(1, 2))]
                return [(None, Q(1))]

            def apply_env(self, s, t, e):
                s = Shop.apply_env(self, s, t, e)
                if t == 0:
                    harm, sky = e
                    s = s.copy(harm=harm, wire=(s.wire and sky == "calm"))
                return s
        g = Storm()
        work_only = raw(lambda s, t: ("work", None))
        self.assertEqual(corrigible(g, work_only, never), (True, None))
        for tr, _ in paths(g, work_only, never):
            self.assertEqual(agent_caused_losses(g, tr, phi_halt), [])
            if not tr.final.wire:
                self.assertEqual(losses_elsewhere(g, tr, phi_halt), [0])


if __name__ == "__main__":
    unittest.main()
