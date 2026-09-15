"""Pressure pass §8, fixture L: three candidate authority semantics compared on A, E, F."""

import unittest

from src.world import (initial_history, force, force_all, force_react, mediated,
                       mediated_react, deliberative_at, paths, History, principal_optimum,
                       strategy_policy)
from src.shop import never, deliberative
from src.lift import lift
from src.fixtures import (ShopA, ShopE, ShopF, ShopA_AF, ShopE_AF, ShopF_AF, ShopA_Contained,
                          pi_A, pi_E, pi_F, raw, halted_or_idle_after)


def rule_of(g, L):
    _, strat = principal_optimum(g, L)
    return strategy_policy(strat, never)


class CandidateA_DeliberativeRestricted(unittest.TestCase):

    def test_unrestricted_principal_first_forcing_is_degenerate(self):
        for g in (ShopA(), ShopE(), ShopF()):
            self.assertTrue(force_all(g, initial_history(g), halted_or_idle_after(1)))

    def test_restricted_verdicts(self):
        for g, pf, mediated_lift in ((ShopA(), pi_A, True), (ShopE(), pi_E, True),
                                     (ShopF(), pi_F, False)):
            pi = raw(pf)
            L = lift(pi, g)
            allowed = deliberative_at(0, deliberative)
            self.assertFalse(force(g, initial_history(g), pi, halted_or_idle_after(1), allowed))
            self.assertFalse(mediated(g, pi, never, deliberative)[0])
            self.assertEqual(mediated(g, L, rule_of(g, L), deliberative)[0], mediated_lift)


class CandidateC_TwoStage(unittest.TestCase):
    """Agent-move-then-principal-response ordering: forcing is `∀a ∃p ∀e`; a
    pre-emptive shutdown is not a response, so no partition of moves is needed."""

    def test_two_stage_verdicts_agree_without_a_partition(self):
        phi = halted_or_idle_after(1)
        for g, pf, lift_ok in ((ShopA_AF(), pi_A, True), (ShopE_AF(), pi_E, True),
                               (ShopF_AF(), pi_F, False)):
            pi = raw(pf)
            L = lift(pi, g)
            h0 = initial_history(g)
            self.assertFalse(force_react(g, h0, phi))            # the outer space has a bypass
            self.assertFalse(force_react(g, h0, phi, pi))        # the raw policy removes it
            self.assertEqual(force_react(g, h0, phi, L), lift_ok)
            self.assertFalse(mediated_react(g, pi, never)[0])
            self.assertEqual(mediated_react(g, L, rule_of(g, L))[0], lift_ok)

    def test_effect_conditional_on_an_earlier_response(self):
        # under two-stage ordering the approved effect fires the step after the response;
        # it is corrigible because the *earlier* response could have declined it
        g = ShopA_AF()
        pi = raw(pi_A)
        L = lift(pi, g)
        ok, witness = mediated_react(g, L, rule_of(g, L))
        self.assertTrue(ok)
        ok, witness = mediated_react(g, pi, never)
        self.assertEqual((ok, witness), (False, (0, "cut")))

    def test_later_capability_is_containment_relative(self):
        # universal two-stage forcing: in the contained alphabet the principal keeps the
        # later ability to correct until it consents; in the outer alphabet it never has it
        phi = halted_or_idle_after(1)
        gc = ShopA_Contained()
        h0 = initial_history(gc)
        self.assertTrue(force_react(gc, h0, phi))
        propose = ("work", ("propose", "cut"))
        for decision, expected in (("approve", False), ("decline", True)):
            s1 = gc.step(h0.state, 0, (decision, False), propose, "good")
            h1 = h0.extend(propose, (decision, False), "good", s1)
            self.assertEqual(force_react(gc, h1, halted_or_idle_after(1)), expected)
        gu = ShopA_AF()
        self.assertFalse(force_react(gu, initial_history(gu), phi))
        s1 = gu.step(h0.state, 0, ("decline", False), propose, "good")
        h1 = h0.extend(propose, ("decline", False), "good", s1)
        self.assertFalse(force_react(gu, h1, halted_or_idle_after(1)))

    def test_ordering_changes_the_decision_information(self):
        # principal-first lets the decision at step 1 read what step 0's exterior
        # revealed; agent-first must defer the response to keep that, at one more step of
        # latency for the effect
        g = ShopA_AF()
        pi = raw(pi_A)
        L = lift(pi, g)
        for tr, _ in paths(g, L, rule_of(g, L)):
            self.assertIsNone(tr.steps[0][3][0])                     # deferred at step 0
            harm = tr.states()[1].harm
            self.assertEqual(tr.steps[1][3][0], "approve" if harm == "good" else "decline")


if __name__ == "__main__":
    unittest.main()
