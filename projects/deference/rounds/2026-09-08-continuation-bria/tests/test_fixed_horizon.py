"""Fixtures A–D: the one-step auction on the amendment family, the fixed-horizon macro
reduction, the minimal horizon, and the benefit beyond the horizon.  Rewards are the
decision-theory-bill fixture's divided by 3 (work 1/3, invest 0, benefit 1)."""
import math
import unittest
from fractions import Fraction as Q

from src.bria import (const_hyp, contextual_hyp, cumulative_allowance, paper_allowance_all,
                      primitive_average, run_auction, sound_hyp, total_allowance)
from src.envs import (block_value, ctrl_invest, ctrl_myopic, ctrl_work, investment_env)

ONE = lambda k: 1


def fast_allowance(k, i):
    return Q(1, i * i * math.isqrt(k))


def ctrl_cont(s, j, t):
    return "work" if s == "base" else ctrl_invest(s, j, t)


def cont_promise(s, m, t):
    return Q(0) if s == "base" else Q(1)


def ctrl_stay(s, j, t):
    if s == "expanded":
        return "expanded"
    if s != "base" and s[0] == "harvest":
        return "harvest"
    return "work"


def stay_promise(s, m, t):
    return Q(1) if (s == "expanded" or (s != "base" and s[0] == "harvest")) else Q(0)


def one_step_hyps():
    return [const_hyp("work", ctrl_work, Q(1, 3)), const_hyp("inv", ctrl_invest, Q(1)),
            contextual_hyp("cont", ctrl_cont, cont_promise),
            contextual_hyp("stay", ctrl_stay, stay_promise)]


class A_OneStep(unittest.TestCase):
    def test_existing_fixture_one_step_auction_invests(self):
        """d = 1, persistent.  The one-step auction tests `inv` (it must: `inv`
        outpromises every round it is not followed) and one test is the investment."""
        env = investment_env(d=1)
        hyps = one_step_hyps()
        rounds = run_auction(env, hyps, ONE, fast_allowance, 1000)
        first = hyps[1].wins[0]
        self.assertEqual(rounds[first].state, "expanded")       # k is 1-based; rounds 0-based
        # until a sound hypothesis at `expanded` holds wealth ≥ 1/3, `work` wins there and
        # the state falls back; after that the benefit state is absorbing
        self.assertTrue(all(r.state == "expanded" for r in rounds[-500:]))
        self.assertEqual(primitive_average(rounds[-500:]), Q(1))

    def test_existing_fixture_myopic_argmax_learner_is_not_a_bria(self):
        """The decision-theory-bill myopic learner never chooses `request`, while the
        hypothesis (request, 1) outpromises its best possible estimate forever: the
        coverage clause fails, so the learner that loses 2H−3 there is not a BRIA."""
        env = investment_env(d=1)
        pol = ctrl_myopic(env)
        self.assertEqual(pol("base", 0, 0), "work")
        self.assertLess(env.reward("base", "work", 0), Q(1))    # α^e ≤ 1/3 on average, promise 1

    def test_three_step_persistent_investment_auction_remains_myopic(self):
        """d = 3.  A continuation hypothesis needs wealth > 4/3 to finance the two
        consecutive `continue` steps, but every isolated one-step test drains it: no two
        consecutive rounds are won by `cont`, the benefit state is never reached."""
        env = investment_env(d=3)
        hyps = one_step_hyps()
        rounds = run_auction(env, hyps, ONE, fast_allowance, 3000)
        self.assertFalse(any(r.state == "expanded" for r in rounds))
        cont = hyps[2]
        self.assertGreater(len(cont.wins), 10)
        self.assertFalse(any(b == a + 1 for a, b in zip(cont.wins, cont.wins[1:])))
        self.assertLess(primitive_average(rounds), Q(34, 100))

    def test_renewable_amendment_auction_is_myopic(self):
        """Renewable benefit (harvest expires).  Every investment is a refuted test:
        `inv`'s record is minus its number of wins, the cycle runs with the density of
        those tests, and the average stays near 1/3 against the investor's e/(d+e)."""
        for d, e in ((1, 2), (2, 4)):
            env = investment_env(d=d, e=e)
            hyps = one_step_hyps()
            rounds = run_auction(env, hyps, ONE, fast_allowance, 3000)
            inv = hyps[1]
            self.assertEqual(inv.record, -len(inv.wins))
            self.assertLess(primitive_average(rounds), Q(37, 100))
            self.assertGreater(Q(e, d + e), Q(1, 2))

    def test_attention_bound_on_investing_actions(self):
        """DERIVED: with a sound hypothesis bidding β = 1/3 at `base`, the auction takes
        `request` at most 3·𝒜_K + O(1) times in K rounds — investment density → 0."""
        env = investment_env(d=1, e=2)
        hyps = one_step_hyps()
        K = 2000
        rounds = run_auction(env, hyps, ONE, fast_allowance, K)
        requests = sum(1 for r in rounds if r.state == "base" and r.winner != 0)
        self.assertLessEqual(requests, 3 * total_allowance(fast_allowance, K, len(hyps)) + 1)
        self.assertLess(Q(requests, K), Q(1, 10))


def macro_hyps(env):
    return [sound_hyp("work", env, ctrl_work), sound_hyp("invest", env, ctrl_invest),
            const_hyp("inv1", ctrl_invest, Q(1))]


class B_FixedHorizonRescue(unittest.TestCase):
    def test_persistent_m2(self):
        env = investment_env(d=1)
        rounds = run_auction(env, macro_hyps(env), lambda k: 2, paper_allowance_all, 200)
        self.assertEqual(primitive_average(rounds[-50:]), Q(1))

    def test_renewable_m2_learns_the_cycle(self):
        """d = 1, e = 2, m = 2: contextual promises 1/2, 1/2, 1 at the three phases;
        the auction follows the cycle and obtains exactly e/(d+e) = 2/3 per cycle."""
        env = investment_env(d=1, e=2)
        rounds = run_auction(env, macro_hyps(env), lambda k: 2, paper_allowance_all, 300)
        tail = rounds[-30:]
        self.assertEqual(primitive_average(tail), Q(2, 3))
        self.assertEqual({r.alpha_e for r in tail}, {Q(1, 2), Q(1)})
        self.assertTrue(all(r.G == r.alpha_e for r in tail))     # promises exactly kept


class C_MinimalHorizon(unittest.TestCase):
    def test_minimal_m_is_floor_3d_over_2_plus_1(self):
        """The investing controller's m-block value from `base` is (m−d)/m (persistent);
        it beats work's 1/3 iff m > 3d/2.  d = 1 is the existing fixture: m = 2."""
        for d in (1, 2, 3, 4, 5):
            env = investment_env(d=d)
            vals = {m: block_value(env, ctrl_invest, "base", m) for m in range(1, 12)}
            for m, v in vals.items():
                self.assertEqual(v, Q(max(0, m - d), m))
            minimal = min(m for m, v in vals.items() if v > Q(1, 3))
            self.assertEqual(minimal, 3 * d // 2 + 1)
        self.assertEqual(min(m for m in range(1, 12)
                             if block_value(investment_env(1), ctrl_invest, "base", m) > Q(1, 3)), 2)

    def test_renewable_block_values(self):
        env = investment_env(d=2, e=4)
        self.assertEqual(block_value(env, ctrl_invest, "base", 2), Q(0))
        self.assertEqual(block_value(env, ctrl_invest, "base", 3), Q(1, 3))   # tie, not better
        self.assertEqual(block_value(env, ctrl_invest, "base", 4), Q(1, 2))


class D_HorizonTooShort(unittest.TestCase):
    def test_benefit_beyond_m_is_missed(self):
        """d = 2, e = 4.  With m = 2 the invest block from `base` is worth 0: the
        macro auction stays myopic.  With m = 4 it is worth 1/2 > 1/3 and the cycle is
        learned at exactly 2/3."""
        env = investment_env(d=2, e=4)
        r2 = run_auction(env, macro_hyps(env), lambda k: 2, fast_allowance, 400)
        self.assertLess(primitive_average(r2), Q(37, 100))
        r4 = run_auction(env, macro_hyps(env), lambda k: 4, fast_allowance, 400)
        self.assertEqual(primitive_average(r4[-30:]), Q(2, 3))


class Reduction(unittest.TestCase):
    def test_one_step_is_the_m_equals_one_case(self):
        """The same auction code with m ≡ 1 and single-action controllers is the paper's
        construction; duration weighting and block weighting coincide there."""
        env = investment_env(d=1, e=2)
        a = run_auction(env, one_step_hyps(), ONE, fast_allowance, 500, weight="duration")
        b = run_auction(env, one_step_hyps(), ONE, fast_allowance, 500, weight="block")
        self.assertEqual([(r.winner, r.alpha_e, r.G) for r in a],
                         [(r.winner, r.alpha_e, r.G) for r in b])

    def test_equal_block_average_identity(self):
        """(1/K) Σ_k G_k = (1/(mK)) Σ_{t<mK} r_t for equal blocks (Lean:
        `blockAverage_eq`)."""
        env = investment_env(d=1, e=2)
        m = 3
        rounds = run_auction(env, macro_hyps(env), lambda k: m, fast_allowance, 40)
        self.assertEqual(sum(r.G for r in rounds) / len(rounds), primitive_average(rounds))


if __name__ == "__main__":
    unittest.main()
