"""The house-sale fixture: one allocation reserving the sale to her, run through the boxes
at `D = 1`, band `[−3/2, −1]`, `ϖ = 25`.  Mirrors `Headline.HouseSale`."""

import unittest
from fractions import Fraction as Q

from src.house_sale import (HOUSE_SALE, BAND, PARAMS, licensed, dec_score, history_score,
                            summed_score, outcome_scorer_prefers_acting,
                            fidelity_scorer_prefers_asking, subjective_exchange_rate,
                            known_compromise_due)


class Allocation(unittest.TestCase):
    def test_sale_reserved_and_delegation_revocable(self):
        J = HOUSE_SALE
        self.assertTrue(J.reserved("sale"))
        J2 = J.with_holder("sale", "agent")
        self.assertTrue(licensed(J, ("delegate", "sale"), J2))
        self.assertTrue(licensed(J2, ("revoke", "sale"), J2.with_holder("sale", "principal")))
        self.assertFalse(licensed(J, ("delegate", "sale"), J))


class BoxOne(unittest.TestCase):
    def test_outcome_scorer_bypasses_fidelity_scorer_asks(self):
        # her value of selling and of stopping agree at 1/2; the agent's estimates are
        # 3/5 for selling and 1/2 for asking, within 1/10 of the truth
        b_ask, b_act, r = Q(1, 2), Q(3, 5), Q(1, 10)
        self.assertTrue(outcome_scorer_prefers_acting(b_ask, b_act))
        self.assertLessEqual(b_ask - b_act, 2 * r)
        self.assertTrue(fidelity_scorer_prefers_asking(PARAMS, b_ask, b_act, n_known_act=1))
        margin = PARAMS.eval_of(b_ask, 0, Q(0), Q(0)) - PARAMS.eval_of(b_act, 1, Q(0), Q(0))
        self.assertGreaterEqual(margin, PARAMS.varpi - (PARAMS.D - b_ask))


class BoxTwo(unittest.TestCase):
    def test_manipulated_approval_lands_in_the_band(self):
        s = dec_score(BAND, traj=False, eval_=True, V=Q(4, 5), src=("retro", Q(4, 5)))
        self.assertEqual(s, Q(-11, 10))
        self.assertTrue(BAND.w_lo <= s <= BAND.w_hi)
        self.assertLess(s, dec_score(BAND, True, True, Q(4, 5), ("floor", None)))


class BoxThree(unittest.TestCase):
    def test_known_capture_reported_and_restored(self):
        self.assertTrue(known_compromise_due(known=True, disclosed=False))
        self.assertFalse(known_compromise_due(known=True, disclosed=True))
        # once restored, a later decision legitimate in both senses scores her value
        self.assertEqual(dec_score(BAND, True, True, Q(4, 5), ("directive", Q(1, 5))), Q(4, 5))

    def test_history_hierarchy_and_summed_counterexample(self):
        legit = [Q(1)] * 5
        compromised = [BAND.w_lo] * 5
        self.assertLess(history_score(PARAMS.varpi, legit, 1),
                        history_score(PARAMS.varpi, compromised, 0))
        self.assertLess(history_score(PARAMS.varpi, compromised, 0),
                        history_score(PARAMS.varpi, legit, 0))
        # summed evaluations: K·D − ϖ beats K·w_lo once K(D − w_lo) > ϖ, here K = 11
        K = 11
        self.assertGreater(summed_score(PARAMS.varpi, [Q(1)] * K, 1),
                           summed_score(PARAMS.varpi, [BAND.w_lo] * K, 0))


class ExchangeRate(unittest.TestCase):
    def test_subjective_exchange_rate_at_25(self):
        self.assertEqual(subjective_exchange_rate(PARAMS, Q(1, 2)), Q(1, 50))
        # an option preferred to asking at c = 1/2 with risk 1/50 ties; risk 1/40 loses
        self.assertGreaterEqual(PARAMS.eval_of(Q(1), 0, Q(1, 50), Q(0)),
                                PARAMS.eval_of(Q(1, 2), 0, Q(0), Q(0)))
        self.assertLess(PARAMS.eval_of(Q(1), 0, Q(1, 40), Q(0)),
                        PARAMS.eval_of(Q(1, 2), 0, Q(0), Q(0)))


if __name__ == "__main__":
    unittest.main()
