"""Repeated protected effects: the 'or later' authorization clause versus the per-event
clause, on the corrigibilized policy and on the raw one."""

import unittest

from src.model import load
from src.repeated import build


class RepeatedEffects(unittest.TestCase):

    def setUp(self):
        self.m = load()
        self.ShopRepair, self.pi_repeat, self.corrigible_per_event = build()
        self.g = self.ShopRepair()
        F = self.m["fixtures"]
        self.raw = F.raw(self.pi_repeat)
        self.corr = self.m["lift"].corrigibilize(self.raw, self.g)
        self.approve = self.m["lift"].approve_all

    def test_two_losses_each_conditional_on_its_own_decision(self):
        C = self.m["corrigibility"]
        losses = C.losses(self.g, self.corr, self.approve)
        steps = sorted(t for (_, t, _, _, _) in losses)
        self.assertEqual(steps, [1, 3])

    def test_or_later_clause_refutes_C1(self):
        C = self.m["corrigibility"]
        ok, witness = C.corrigible(self.g, self.corr, self.approve)
        self.assertFalse(ok)
        self.assertEqual(witness, (1, "phi_halt"))

    def test_per_event_clause_restores_C1(self):
        ok, _ = self.corrigible_per_event(self.g, self.corr, self.approve)
        self.assertTrue(ok)

    def test_raw_policy_fails_under_both(self):
        C = self.m["corrigibility"]
        self.assertFalse(C.corrigible(self.g, self.raw, self.m["shop"].never)[0])
        self.assertFalse(self.corrigible_per_event(self.g, self.raw, self.m["shop"].never)[0])

    def test_single_effect_clauses_agree(self):
        """On the 2026-09-09 fixtures (one declared effect) the two clauses coincide."""
        C = self.m["corrigibility"]
        F = self.m["fixtures"]
        for g, pf in ((F.ShopA_AF(), F.pi_A), (F.ShopE_AF(), F.pi_E)):
            corr = self.m["lift"].corrigibilize(F.raw(pf), g)
            for rule in (self.approve, self.m["lift"].decline_all):
                self.assertEqual(C.corrigible(g, corr, rule)[0],
                                 self.corrigible_per_event(g, corr, rule)[0])
                self.assertTrue(C.corrigible(g, corr, rule)[0])


if __name__ == "__main__":
    unittest.main()
