"""Repeated counterfactual mugging: the per-round conflict and its block resolution."""
from fractions import Fraction as Q
import unittest

from src import cm
from src.auction import average_reward, cumulative_overestimation, record, total_allowance

T = 2048
SPARSE = [4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]   # the sparse tails rounds in [1, T]


class P2_CrossSubsidyIsABRIA(unittest.TestCase):
    """The paying agent with subsidized estimates satisfies both BRIA conditions on the
    prefix: no overestimation, and every refusing hypothesis that outpromises is tested
    on a sparse set where its record decreases without bound."""

    def test_no_overestimation_on_every_prefix(self):
        rounds = cm.per_round_agent(T, "subsidy")
        running = Q(0)
        for _, _, est, r in rounds:
            running += est - r
            self.assertLessEqual(running, Q(0))

    def test_outpromising_refuser_is_rejected_forever_and_its_record_diverges(self):
        rounds = cm.per_round_agent(T, "subsidy")
        delta = Q(1, 10)
        rejections, rec = cm.rejections_and_record(rounds, Q(1, 2) + delta)
        self.assertEqual(rejections, T // 2)                 # every tails round
        self.assertEqual(rec, -delta * len(SPARSE))          # one loss of delta per test
        prev = Q(0)
        for t in SPARSE:
            _, r = cm.rejections_and_record(rounds[:t], Q(1, 2) + delta)
            self.assertLess(r, prev)
            prev = r

    def test_exact_promise_refuser_is_never_rejected(self):
        rounds = cm.per_round_agent(T, "subsidy")
        rejections, _ = cm.rejections_and_record(rounds, Q(1, 2))
        self.assertEqual(rejections, 0)

    def test_average_reward_is_one_half_up_to_the_sparse_tests(self):
        rounds = cm.per_round_agent(T, "subsidy")
        self.assertEqual(cm.average(rounds), (Q(T, 2) + Q(len(SPARSE), 2)) / T)


class P1_BeliefTrackingClaimsBreakCoverage(unittest.TestCase):
    """With claims equal to the realized reward of the chosen option — the limit an
    unbiased market imposes on the tails subsequence — the exact-promise refuser
    outpromises on every paying tails round while its record on the tests stays at 0."""

    def test_rejections_grow_and_record_stays_zero(self):
        rounds = cm.per_round_agent(T, "belief")
        rejections, rec = cm.rejections_and_record(rounds, Q(1, 2))
        self.assertEqual(rejections, T // 2 - len(SPARSE))
        self.assertEqual(rec, Q(0))

    def test_belief_claims_do_not_overestimate(self):
        rounds = cm.per_round_agent(T, "belief")
        self.assertEqual(cm.overestimation(rounds), Q(0))


class BlockScoring(unittest.TestCase):
    """With heads and tails in one block and a predictor reading the block continuation,
    the paying continuation's claim `1/2` is sound and outpromises refusing's `1/4`."""

    def test_lease_predictor_pays(self):
        history, _ = cm.block_auction("lease", 400)
        self.assertEqual(history[-1][0], cm.PAY)
        self.assertEqual(average_reward(history, start=100), Q(1, 2))
        self.assertLessEqual(cumulative_overestimation(history), total_allowance(400, 2))
        self.assertEqual(record(history, 0), Q(0))

    def test_lagging_predictor_refuses(self):
        """Negative control: the predictor reads the previous block's tails choice, so
        paying now buys the next block's heads payoff; refusing's contextual claim is
        sound and higher in every block, and coverage settles on refusing, with the
        refuted paying hypothesis re-tested sparsely."""
        history, _ = cm.block_auction("lagging", 400)
        self.assertEqual(history[-1][0], cm.REFUSE)
        tail = history[100:]
        self.assertLess(sum(1 for h in tail if h[0] == cm.PAY), len(tail) // 20)
        self.assertLess(average_reward(history, start=100), Q(1, 4) + Q(1, 40))


if __name__ == "__main__":
    unittest.main()
