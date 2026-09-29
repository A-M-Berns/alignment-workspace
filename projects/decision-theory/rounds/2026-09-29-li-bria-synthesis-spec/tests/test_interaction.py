"""The interaction diagnostic: a hypothesis class that reads the market reaches what a
blind class cannot, at the criterion level."""
from fractions import Fraction as Q
import unittest

from src import logic_rewards
from src.auction import average_reward


class BlindClass(unittest.TestCase):
    def test_every_blind_predictor_is_wrong_on_its_residue_class(self):
        preds = logic_rewards.blind_predictors()
        truth = logic_rewards.truth_sequence(300, preds)
        for i, p in enumerate(preds):
            past = []
            wrong_on_own = 0
            for k, v in enumerate(truth):
                if k % 3 == i and p(past) == v:
                    wrong_on_own += 1
                past.append(v)
            self.assertEqual(wrong_on_own, 0)

    def test_blind_auction_average_is_bounded_away_from_one(self):
        history, _ = logic_rewards.blind_auction(900)
        self.assertLess(average_reward(history, start=300), Q(9, 10))


class MarketReadingClass(unittest.TestCase):
    def test_market_auction_average_tends_to_one(self):
        history, _ = logic_rewards.market_auction(900, d0=30)
        self.assertGreater(average_reward(history, start=300), Q(99, 100))
        tail = history[300:]
        self.assertGreater(sum(1 for h in tail if h[4] == 3), len(tail) * 19 // 20)


if __name__ == "__main__":
    unittest.main()
