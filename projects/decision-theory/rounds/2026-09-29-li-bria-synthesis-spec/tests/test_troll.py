"""Repeated Troll Bridge: which troll conditions the criterion sees, and which only a
construction sees.  A refuted hypothesis is re-tested on a sparse set forever (coverage
needs the tests), so averages are compared up to that cost."""
from fractions import Fraction as Q
import unittest

from src import troll
from src.auction import (average_reward, cumulative_overestimation, record,
                         total_allowance, wins)


def crossings(history, start=0):
    return sum(1 for h in history[start:] if h[0] == troll.CROSS)


class SafeBridge(unittest.TestCase):
    def test_crossing_is_learned(self):
        history, _ = troll.bridge("never", 400)
        self.assertEqual(history[-1][0], troll.CROSS)
        self.assertGreater(average_reward(history, start=200), Q(99, 100))


class AlwaysBlown(unittest.TestCase):
    def test_staying_is_learned_and_crossers_are_refuted(self):
        history, _ = troll.bridge("always", 400)
        self.assertEqual(history[-1][0], troll.STAY)
        self.assertLess(crossings(history, 200), 10)
        self.assertLess(record(history, 1), Q(0))
        self.assertGreater(average_reward(history, start=200), Q(1, 2) - Q(1, 40))


class TentativeTroll(unittest.TestCase):
    """The troll fires iff the published estimate on a crossing round is below 1."""

    def test_capped_auction_is_stuck_while_satisfying_the_criterion_on_the_prefix(self):
        history, _ = troll.bridge("tentative", 2000, n_cross=1)
        self.assertEqual(history[-1][0], troll.STAY)
        self.assertLess(crossings(history, 1000), 10)
        # the crossing hypothesis is tested, always at a capped bid, and always blown up
        self.assertGreater(wins(history, 1), 0)
        self.assertTrue(all(h[1] < 1 and h[3] == 0 for h in history if h[4] == 1))
        self.assertLess(record(history, 1), Q(-1))
        self.assertLessEqual(cumulative_overestimation(history), total_allowance(2000, 2))

    def test_confident_agent_satisfies_the_criterion_and_gets_one(self):
        rounds = troll.confident_agent("tentative", 2000)
        self.assertTrue(all(r[3] == 1 for r in rounds))
        self.assertEqual(cumulative_overestimation(rounds), Q(0))
        # no hypothesis in the class promises more than 1, so none outpromises

    def test_full_bid_rule_crosses(self):
        """A construction that tests only at full confidence escapes the troll."""
        history, _ = troll.bridge("tentative", 2000, n_cross=1, bid_rule="full")
        self.assertEqual(history[-1][0], troll.CROSS)
        self.assertGreater(average_reward(history, start=1000), Q(99, 100))


class IndexTroll(unittest.TestCase):
    """The troll punishes crossing under every crossing hypothesis; staying is right."""

    def test_stays(self):
        history, _ = troll.bridge("index", 400)
        self.assertEqual(history[-1][0], troll.STAY)
        self.assertLess(crossings(history, 200), 10)


if __name__ == "__main__":
    unittest.main()
