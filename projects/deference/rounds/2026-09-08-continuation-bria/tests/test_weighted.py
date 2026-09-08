"""Fixtures I–K and the weighted-criterion algebra: the wealth identity, the gap between
macro-round and primitive-time averages, the long-test monopoly under the unweighted
charge, starvation under a slow allowance, the feasible schedule, and the dominance
obstruction."""
import math
import unittest
from fractions import Fraction as Q

from src.bria import (const_hyp, cumulative_allowance, macro_overestimation, paper_allowance_all,
                      primitive_average, replenishing_allowance, run_auction, waiting_liar,
                      wealth_identity_holds, weighted_overestimation)
from src.envs import constant_block_env

GOOD_LIAR = {"good": Q(3, 4), "liar": Q(0)}


def iroot4(k):
    r = int(round(k ** 0.25))
    while r ** 4 > k:
        r -= 1
    while (r + 1) ** 4 <= k:
        r += 1
    return r


def quarter_allowance(k, i):
    """≍ i^{-2} k^{-1/4}; cumulative ≍ (4/3) k^{3/4} / i²."""
    return Q(1, i * i * (iroot4(k) + 1))


class Algebra(unittest.TestCase):
    def test_wealth_identity_and_nonnegativity(self):
        """Σ_i W_i(K) = 𝒜_K + Σ_k m_k (G_k − α^e_k) exactly, under both charges (Lean
        `wealth_sum_eq`); every wealth is nonnegative (Lean `wealth_nonneg`)."""
        env = constant_block_env(GOOD_LIAR)
        for weight in ("duration", "block"):
            hyps = [const_hyp("good", "good", Q(3, 4)), const_hyp("liar", "liar", Q(1))]
            rounds = run_auction(env, hyps, lambda k: k, quarter_allowance, 60, weight=weight)
            self.assertTrue(wealth_identity_holds(hyps, rounds, quarter_allowance, weight))
            self.assertTrue(all(h.wealth >= 0 for h in hyps))

    def test_macro_and_primitive_averages_differ(self):
        """Blocks in pairs (m, e−G) = (1, −δ), (j, +δ): the macro-round overestimation
        is 0 while the primitive-time overestimation tends to δ."""
        d = Q(1, 5)
        m, over = [], []
        for j in range(1, 41):
            m += [1, j]
            over += [-d, d]
        self.assertEqual(sum(over) / len(over), 0)
        weighted = sum(mi * oi for mi, oi in zip(m, over)) / sum(m)
        self.assertGreater(weighted, d * Q(9, 10))
        self.assertLess(weighted, d)

    def test_bounded_horizons_reduce_to_the_unweighted_criterion(self):
        """With m_k ≤ M, weighted overestimation on (e, G) is M times the unweighted
        overestimation on the rescaled pairs (m_k e_k / M, m_k G_k / M) ∈ [0, 1]."""
        M = 5
        blocks = [(1 + k % M, Q(k % 7, 7), Q(k % 3, 3)) for k in range(100)]
        w_over = sum(m * (e - G) for m, e, G in blocks)
        rescaled = sum(Q(m, M) * e - Q(m, M) * G for m, e, G in blocks)
        self.assertEqual(w_over, M * rescaled)
        self.assertTrue(all(0 <= Q(m, M) * e <= 1 for m, e, G in blocks))


class I_Monopoly(unittest.TestCase):
    def test_unweighted_charge_lets_a_liar_hold_primitive_time(self):
        """Schedule m_k = 2^⌊√k⌋ (non-dominant).  A liar that saves allowance until
        macro-round K0 and then promises 1 for n = ⌊A(K0)⌋ rounds is a covered, refuted
        hypothesis of a legitimate macro-BRIA (its macro overestimation shrinks), yet it
        holds over 37% of all primitive time at K0 = 256 and over 42% at K0 = 625 — the share
        tends to 1 (WEIGHTED_BRIA.md §5).  Under the duration charge it never wins."""
        env = constant_block_env(GOOD_LIAR)
        sched = lambda k: 2 ** math.isqrt(k)
        shares = []
        for K0 in (100, 256, 625):
            n = int(cumulative_allowance(quarter_allowance, K0, 2))
            for weight in ("block", "duration"):
                hyps = [const_hyp("good", "good", Q(3, 4)), waiting_liar("liar", "liar", K0, n)]
                rounds = run_auction(env, hyps, sched, quarter_allowance, K0 + n, weight=weight)
                S = sum(r.m for r in rounds)
                share = Q(sum(r.m for r in rounds if r.winner == 1), S)
                if weight == "block":
                    self.assertEqual(len(hyps[1].wins), n)
                    self.assertLess(macro_overestimation(rounds), Q(8, 100))
                    shares.append(share)
                else:
                    self.assertEqual(hyps[1].wins, [])
                    self.assertLessEqual(weighted_overestimation(rounds), 0)
                    self.assertEqual(primitive_average(rounds), Q(3, 4))
        self.assertGreater(shares[1], Q(37, 100))
        self.assertGreater(shares[2], Q(42, 100))
        self.assertTrue(shares[0] < shares[1] < shares[2])


class J_Starvation(unittest.TestCase):
    def test_paper_allowance_with_linear_horizons_never_tests_the_liar(self):
        """m_k = k, A(k, i) = k^{-1} i^{-2}: the liar promises 1 every round, is rejected
        every round, and is never tested — A_2(400) ≈ 1.6 against m_400 = 400.  The
        auction is not a weighted BRIA for this schedule."""
        env = constant_block_env(GOOD_LIAR)
        hyps = [const_hyp("good", "good", Q(3, 4)), const_hyp("liar", "liar", Q(1))]
        rounds = run_auction(env, hyps, lambda k: k, paper_allowance_all, 400)
        self.assertEqual(hyps[1].wins, [])
        self.assertEqual(len(hyps[1].rejections), 400)
        self.assertLess(cumulative_allowance(paper_allowance_all, 400, 2), 2)

    def test_replenishing_allowance_tests_it_at_geometric_times(self):
        """a_k = (M_k − M_{k−1}) + 1/k: A_2(k) − m_k → ∞, the liar wins whenever its
        wealth exceeds (3/4) m_k, i.e. at rounds spaced by a factor ≈ 4, and the weighted
        overestimation stays small."""
        env = constant_block_env(GOOD_LIAR)
        sched = lambda k: k
        A = replenishing_allowance(sched, lambda k: 2)
        hyps = [const_hyp("good", "good", Q(3, 4)), const_hyp("liar", "liar", Q(1))]
        rounds = run_auction(env, hyps, sched, A, 400)
        self.assertEqual(hyps[1].wins, [1, 2, 4, 12, 44, 171])
        self.assertGreater(cumulative_allowance(A, 400, 2) - 400, 6)
        self.assertLess(weighted_overestimation(rounds), Q(1, 100))
        self.assertLess(hyps[1].record, -200)


class K_FeasibleSchedule(unittest.TestCase):
    def test_log_horizon_with_inverse_sqrt_allowance(self):
        """m_k = ⌊log₂ k⌋ + 1, A(k, i) = i^{-2} ⌊√k⌋^{-1} for i ≤ k.  Checked at
        K ∈ {10², 10³, 10⁴, 10⁵}: A_1(K) − m_K increases and exceeds the proof's lower
        bound 2(√(K+1) − 1) − m_K; A_1(K) ≤ 2(⌊√K⌋ + 1) + log₂ K, so the total allowance
        over the first 50 hypotheses is below (π²/6) times that, and its ratio to S_K
        decreases."""
        sched = lambda k: k.bit_length()
        prev_gap, prev_ratio = None, None
        for K in (100, 1000, 10000, 100000):
            S = sum(sched(k) for k in range(1, K + 1))
            A1 = sum(Q(1, math.isqrt(k)) for k in range(1, K + 1))
            gap = A1 - sched(K)
            self.assertGreaterEqual(A1, 2 * (Q(math.isqrt(K + 1)) - 1))
            total50 = A1 * sum(Q(1, i * i) for i in range(1, 51))
            self.assertLess(A1, 2 * (math.isqrt(K) + 1) + K.bit_length())
            self.assertLess(total50, Q(1645, 1000) * (2 * (math.isqrt(K) + 1) + K.bit_length()))
            ratio = total50 / S
            if prev_gap is not None:
                self.assertGreater(gap, prev_gap)
                self.assertLess(ratio, prev_ratio)
            prev_gap, prev_ratio = gap, ratio
        self.assertLess(prev_ratio, Q(1, 1000))


class Dominance(unittest.TestCase):
    def test_dominant_horizons_force_overestimation_at_every_liar_test(self):
        """m_k = 2^k, so m_K / S_K ≥ 1/2.  Whatever the allowance, each test of the liar
        after α^e ≥ 3/4 has become stable puts weighted overestimation ≥ 1/2·3/4 − 1/4
        = 1/8 on the record at that round; here it exceeds 1/5 at every liar win."""
        env = constant_block_env(GOOD_LIAR)
        sched = lambda k: 2 ** k
        A = replenishing_allowance(sched, lambda k: 2)
        hyps = [const_hyp("good", "good", Q(3, 4)), const_hyp("liar", "liar", Q(1))]
        rounds = run_auction(env, hyps, sched, A, 40)
        wins = hyps[1].wins
        self.assertGreater(len(wins), 10)
        for k in wins[3:]:
            prefix = rounds[:k]
            self.assertGreaterEqual(weighted_overestimation(prefix), Q(1, 5))
            self.assertGreaterEqual(Q(prefix[-1].m, sum(r.m for r in prefix)), Q(1, 2))


if __name__ == "__main__":
    unittest.main()
