"""Allowance-timing fixtures (PRESSURE_PASS.md §13): the surprise-spike diagnostic under
opening and settlement timing, the reindexing equivalence, the coverage coefficient, and
the attention bound with the opening subsidy counted."""
import math
import unittest
from fractions import Fraction as Q

from src.bria import (Hyp, const_hyp, cumulative_allowance, prefix_allowance, run_auction,
                      weighted_overestimation)
from src.envs import constant_block_env
from tests.test_pressure import nasty_schedule

GOOD_LIAR = {"good": Q(3, 4), "liar": Q(0)}
SPIKES = [4 ** j for j in range(1, 6)]


def spike_liar():
    """Promises 1 exactly at the spikes, 0 elsewhere; its controller returns 0."""
    return Hyp("spike-liar", lambda ctx: ("liar", Q(1) if ctx["k"] in SPIKES else Q(0)))


class SurpriseSpike(unittest.TestCase):
    """Schedule `m_k = 1` except `m_{4^j} = ⌊S_{4^j − 1}/j⌋`: non-dominant, each spike a new
    running maximum about four times the previous one, revealed only at its own round."""

    def test_settlement_timing_never_tests_the_spike_liar(self):
        """Source-paper timing: the current `ΔM_k` is credited after block k.  At every
        spike the liar's carried wealth is at most the previous maximum plus a harmonic
        sum, its bid stays below `good`'s 3/4, it is rejected at every spike, tested at
        none, record 0 while outpromising infinitely often: coverage fails, under either
        coefficient."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        for coef in (1, 2):
            hyps = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
            rounds = run_auction(env, hyps, sched, prefix_allowance(sched, coef=coef), 1024,
                                 timing="settlement")
            liar = hyps[1]
            self.assertEqual(liar.wins, [])
            self.assertEqual(liar.record, 0)
            self.assertEqual([k for k in liar.rejections if k in SPIKES], SPIKES)
            for k in SPIKES:
                self.assertLess(rounds[k - 1].bids[1], Q(3, 4))

    def test_opening_timing_finances_the_current_spike(self):
        """Weighted timing with `coef = 2`: at spikes 64, 256, 1024 the opening capital
        covers the whole block, the liar bids 1, wins, and pays: record −320.  With
        `coef = 1` the liar wins only at 256 — after a loss it carries nothing and
        `ΔM_k = m_k − M_{k−1}` alone is short of `m_k`, which is why coverage needs
        `A_i(K) − 2 m_K → ∞`."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        hyps = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
        rounds = run_auction(env, hyps, sched, prefix_allowance(sched, coef=2), 1024)
        self.assertEqual(hyps[1].wins, [64, 256, 1024])
        self.assertEqual(hyps[1].record, -(24 + 71 + 225))
        for k in (64, 256, 1024):
            self.assertEqual(rounds[k - 1].bids[1], Q(1))
        hyps1 = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
        run_auction(env, hyps1, sched, prefix_allowance(sched, coef=1), 1024)
        self.assertEqual(hyps1[1].wins, [256])


class Reindexing(unittest.TestCase):
    def test_opening_equals_settlement_with_shifted_allowance_and_endowment(self):
        """The opening-timed auction with allowance `A` is, bid for bid, the settlement-
        timed auction with allowance `A'(k) = A(k+1)` and initial wealth `A(1, i)`.  The
        difference between the two timings is only what the funding rule may read."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        A = prefix_allowance(sched, coef=2)
        h_open = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
        r_open = run_auction(env, h_open, sched, A, 300, timing="opening")
        h_set = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
        for i, h in enumerate(h_set, 1):
            h.wealth = A(1, i)
        r_set = run_auction(env, h_set, sched, lambda k, i: A(k + 1, i), 300, timing="settlement")
        self.assertEqual([(r.winner, r.alpha_e, r.bids) for r in r_open],
                         [(r.winner, r.alpha_e, r.bids) for r in r_set])
        # settlement has additionally credited A'(300) = A(301) after the last round
        self.assertEqual([h.wealth + A(301, i) for i, h in enumerate(h_open, 1)], [h.wealth for h in h_set])


class Bounds(unittest.TestCase):
    def test_overestimation_and_attention_with_opening_subsidy(self):
        """Weighted overestimation `≤ 𝒜_K / S_K` with the allowance through K inclusive
        (Lean `overestimation_le_allowance_opening`); per hypothesis, the weighted
        shortfall on its wins is at most its allowance through K inclusive (Lean
        `chargedRecord_ge_neg_allowance`) — the current-round subsidy is counted."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        A = prefix_allowance(sched, coef=2)
        hyps = [const_hyp("good", "good", Q(3, 4)), const_hyp("liar", "liar", Q(1))]
        rounds = run_auction(env, hyps, sched, A, 512)
        S = sum(r.m for r in rounds)
        total = sum(A(k, i) for k in range(1, 513) for i in (1, 2))
        self.assertLessEqual(weighted_overestimation(rounds), total / S)
        for idx, h in enumerate(hyps, 1):
            shortfall = sum(r.m * (r.alpha_e - r.G) for r in rounds if r.winner == idx - 1)
            self.assertLessEqual(shortfall, cumulative_allowance(A, 512, idx))

    def test_capital_adequacy_with_coefficient_two(self):
        """`A_i(K) − 2 m_K` grows without bound under the coefficient-2 prefix rule on the
        spiky schedule (checked at the spikes, where it is smallest), and would not with
        coefficient 1 on a nondecreasing schedule."""
        sched = nasty_schedule()
        A2 = prefix_allowance(sched, coef=2)
        gaps = [cumulative_allowance(A2, k, 1) - 2 * sched(k) for k in SPIKES]
        self.assertTrue(all(b > a for a, b in zip(gaps, gaps[1:])))
        lin = lambda k: k
        A1 = prefix_allowance(lin, coef=1)
        self.assertLess(cumulative_allowance(A1, 400, 1) - 2 * 400, -300)
        A2l = prefix_allowance(lin, coef=2)
        self.assertGreater(cumulative_allowance(A2l, 400, 1) - 2 * 400, 5)


if __name__ == "__main__":
    unittest.main()
