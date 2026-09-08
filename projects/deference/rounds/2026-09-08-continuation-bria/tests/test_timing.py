"""Allowance-timing fixtures (PRESSURE_PASS.md §13–14): the surprise-spike diagnostic under
opening and settlement timing, the reindexing equivalence, the sharp per-rejection
record bound, and the attention bound with the opening subsidy counted."""
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
    """Claims 1 exactly at the spikes, 0 elsewhere; its continuation returns 0."""
    return Hyp("spike-liar", lambda ctx: ("liar", Q(1) if ctx["k"] in SPIKES else Q(0)))


class SurpriseSpike(unittest.TestCase):
    """Schedule `m_k = 1` except `m_{4^j} = ⌊S_{4^j − 1}/j⌋`: non-dominant, each spike a new
    running maximum about four times the previous one, revealed only at its own round."""

    def test_settlement_timing_never_tests_the_spike_liar(self):
        """Source-paper timing: the current `ΔM_k` is credited after block k.  At every
        spike the liar's carried wealth is at most the previous maximum plus a harmonic
        sum, its bid stays below `good`'s 3/4, it is rejected at every spike, tested at
        none, record 0 while outpromising infinitely often: coverage fails."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        hyps = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
        rounds = run_auction(env, hyps, sched, prefix_allowance(sched), 1024, timing="settlement")
        liar = hyps[1]
        self.assertEqual(liar.wins, [])
        self.assertEqual(liar.record, 0)
        self.assertEqual([k for k in liar.rejections if k in SPIKES], SPIKES)
        for k in SPIKES:
            self.assertLess(rounds[k - 1].bids[1], Q(3, 4))

    def test_opening_timing_makes_the_current_spike_biddable(self):
        """Weighted timing: the opening capital at a spike includes the current `ΔM_k`.
        The liar is tested at spike 256 (bid 0.93, record −71); at 1024 it carries
        nothing after that loss and bids `ΔM/m = 154/225 ≈ 0.68 < 3/4`, so it is rejected
        there — which coverage permits, since the sharp bound `ℓ_K < w_K − A_i(K)` holds
        at that rejection and `A_i(K) − m_K` grows.  Coverage asks for divergence along
        rejections, not a win at every spike."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        A = prefix_allowance(sched)
        hyps = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
        rounds = run_auction(env, hyps, sched, A, 1024)
        liar = hyps[1]
        self.assertEqual(liar.wins, [256])
        self.assertEqual(liar.record, -71)
        self.assertGreater(rounds[255].bids[1], Q(9, 10))
        self.assertGreater(rounds[1023].bids[1], Q(6, 10))
        self.assertLess(rounds[1023].bids[1], Q(3, 4))

    def test_sharp_record_bound_at_every_rejection(self):
        """At every round K at which the liar is rejected, its inclusive record satisfies
        `ℓ_K < w_K − A_i(K)` with `A_i` through K inclusive (Lean
        `record_succ_lt_of_rejected_opening`), including the round it wins while
        wealth-constrained."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        A = prefix_allowance(sched)
        hyps = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
        rounds = run_auction(env, hyps, sched, A, 1024)
        record = Q(0)
        checked = 0
        for r in rounds:
            if r.winner == 1:
                record += r.m * (r.G - r.promises[1])
            if r.promises[1] > r.alpha_e:                       # rejected at K
                self.assertLess(record, r.m - cumulative_allowance(A, r.k, 2))
                checked += 1
        self.assertEqual(checked, len(hyps[1].rejections))
        self.assertGreaterEqual(checked, 5)


class Reindexing(unittest.TestCase):
    def test_opening_equals_settlement_with_shifted_allowance_and_endowment(self):
        """The opening-timed auction with subsidy `A` is, bid for bid, the settlement-timed
        auction with allowance `A'(k) = A(k+1)` and initial wealth `A(1, i)`.  The
        difference between the two timings is only what the funding rule may read."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        A = prefix_allowance(sched)
        h_open = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
        r_open = run_auction(env, h_open, sched, A, 300, timing="opening")
        h_set = [const_hyp("good", "good", Q(3, 4)), spike_liar()]
        for i, h in enumerate(h_set, 1):
            h.wealth = A(1, i)
        r_set = run_auction(env, h_set, sched, lambda k, i: A(k + 1, i), 300, timing="settlement")
        self.assertEqual([(r.winner, r.alpha_e, r.bids) for r in r_open],
                         [(r.winner, r.alpha_e, r.bids) for r in r_set])
        self.assertEqual([h.wealth + A(301, i) for i, h in enumerate(h_open, 1)], [h.wealth for h in h_set])


class Bounds(unittest.TestCase):
    def test_overestimation_and_attention_with_opening_subsidy(self):
        """Weighted overestimation `≤ 𝒜_K / S_K` with the subsidy through K inclusive (Lean
        `overestimation_le_allowance_opening`); per hypothesis, the weighted shortfall on
        its wins is at most its subsidy through K inclusive (Lean
        `chargedRecord_ge_neg_allowance`) — the current-round subsidy is counted."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        A = prefix_allowance(sched)
        hyps = [const_hyp("good", "good", Q(3, 4)), const_hyp("liar", "liar", Q(1))]
        rounds = run_auction(env, hyps, sched, A, 512)
        S = sum(r.m for r in rounds)
        total = sum(A(k, i) for k in range(1, 513) for i in (1, 2))
        self.assertLessEqual(weighted_overestimation(rounds), total / S)
        for idx, h in enumerate(hyps, 1):
            shortfall = sum(r.m * (r.alpha_e - r.G) for r in rounds if r.winner == idx - 1)
            self.assertLessEqual(shortfall, cumulative_allowance(A, 512, idx))

    def test_capital_adequacy_at_the_spikes(self):
        """`A_i(K) − m_K` grows without bound under the prefix rule on the spiky schedule,
        checked at the spikes where it is smallest, and under the paper's own allowance
        on `m_k = k` it does not."""
        sched = nasty_schedule()
        A = prefix_allowance(sched)
        gaps = [cumulative_allowance(A, k, 1) - sched(k) for k in SPIKES]
        self.assertTrue(all(b > a for a, b in zip(gaps, gaps[1:])))
        paper = lambda k, i: Q(1, k * i * i)
        self.assertLess(cumulative_allowance(paper, 400, 1) - 400, -390)


if __name__ == "__main__":
    unittest.main()
