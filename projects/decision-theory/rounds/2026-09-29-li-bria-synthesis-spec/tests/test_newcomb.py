"""Repeated Newcomb with realized feedback: the verdict turns on what the predictor reads
and on the scoring granularity."""
from fractions import Fraction as Q
import unittest

from src import newcomb
from src.auction import average_reward, record


class LeasePredictor(unittest.TestCase):
    def test_per_round_one_boxes(self):
        history, _ = newcomb.per_round("lease", 400)
        self.assertEqual(history[-1][0], newcomb.ONE)
        self.assertGreater(average_reward(history, start=200), Q(999, 1000) - Q(1, 40))
        self.assertLess(record(history, 1), Q(0))   # two-boxing's claim of 1 is refuted

    def test_block_one_boxes(self):
        history, _ = newcomb.block("lease", 5, 400)
        self.assertEqual(history[-1][0], newcomb.ONE)
        self.assertGreater(average_reward(history, start=200), Q(999, 1000) - Q(1, 40))


class FrequencyPredictorPerRound(unittest.TestCase):
    """Per-round scoring: two-boxing's contextual claim is sound and higher whenever
    the predictor predicts one-boxing, so coverage excludes the one-boxing agent."""

    def test_one_boxing_agent_fails_coverage(self):
        rounds = newcomb.frequency_agent(2048, newcomb.ONE)
        rejections, rec = newcomb.coverage_of(rounds, newcomb.TWO)
        self.assertGreater(rejections, 2000)
        self.assertEqual(rec, Q(0))

    def test_two_boxing_agent_covers_the_two_fixed_bidders(self):
        """Against the sound contextual one-boxer and the non-contextual one claiming
        999/1000, the two-boxing agent with sparse one-box tests is fine on the prefix."""
        rounds = newcomb.frequency_agent(2048, newcomb.TWO)
        rejections, _ = newcomb.coverage_of(rounds, newcomb.ONE)
        self.assertEqual(rejections, 0)
        tests = [r for r in rounds if r[0] == newcomb.ONE]
        self.assertEqual(sum((r[2] - Q(999, 1000) for r in tests), Q(0)),
                         -Q(999, 1000) * len(tests))
        self.assertEqual(len(tests), 10)

    def test_two_boxing_agent_with_a_fixed_schedule_is_not_a_bria(self):
        """The off-schedule attacker: promise 1 for one-boxing off the sparse schedule,
        promise 0 for two-boxing on it; never matched, record 0, outpromises on every
        off-schedule round because the agent's estimate there is 1/1000 < 1.  The
        obstruction is conditional on that estimate being below 1."""
        rounds = newcomb.frequency_agent(2048, newcomb.TWO)
        rejections, rec, tests = newcomb.coverage_of_off_schedule_attacker(rounds, newcomb.TWO)
        self.assertEqual(tests, 0)
        self.assertEqual(rec, Q(0))
        self.assertEqual(rejections, 2048 - 10)

    def test_auction_cycles_at_finite_horizon(self):
        """The paper's auction under the frequency predictor: both options win with
        positive frequency on the prefix, and the average sits between the two limits."""
        history, _ = newcomb.per_round("frequency", 400)
        ones = sum(1 for h in history if h[0] == newcomb.ONE)
        self.assertGreater(ones, 40)
        self.assertGreater(400 - ones, 40)


class FrequencyPredictorBlock(unittest.TestCase):
    def test_block_one_boxes(self):
        """Block scoring with within-block memory: the one-boxing block is worth
        `(m-1)/m * 999/1000` and the two-boxing block `1/1000`."""
        m = 5
        history, _ = newcomb.block("frequency", m, 400)
        self.assertEqual(history[-1][0], newcomb.ONE)
        self.assertGreater(average_reward(history, start=200),
                           Q(m - 1, m) * Q(999, 1000) - Q(1, 40))


if __name__ == "__main__":
    unittest.main()
