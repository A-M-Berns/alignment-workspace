"""The lock-in fixture: an option better than asking, estimated below it (the follow-up,
Part 3).  Under the clause it is never tried; without it, it is tried at the exploration
rate and the estimate corrects."""

import unittest
from fractions import Fraction as Q

from src.exploration_lockin import run, honest_exploration_term, clause_exploration_term


class LockIn(unittest.TestCase):
    def test_under_the_clause_never_tried_and_never_corrected(self):
        L, ask, under = run(above_asking=True)
        self.assertEqual(L.tried.get("under", 0), 0)
        self.assertEqual(L.estimates["under"], Q(2, 5))
        self.assertTrue(all(name == "ask" for name in L.chosen))

    def test_without_the_clause_tried_at_the_exploration_rate_and_corrected(self):
        L, ask, under = run(above_asking=False)
        # the first exploration block is block 4 (mass 1/5); the cycle reaches "under" there
        # or on the next exploration block, after which the maximizer takes it every block
        first = L.chosen.index("under")
        self.assertLessEqual(first, 9)
        self.assertEqual(L.estimates["under"], Q(4, 5))
        self.assertTrue(all(name == "under" for k, name in enumerate(L.chosen)
                            if k > first and not L.is_exploration(k)))

    def test_no_violation_under_either_rule_and_the_bounds_hold(self):
        for above in (True, False):
            L, ask, under = run(above_asking=above)
            realized_rate = Q(0)
            exchange = (L.D - Q(1, 2)) / L.varpi
            term = (clause_exploration_term(L.theta_hi, L.eps) if above
                    else honest_exploration_term(L.D, Q(-3, 2), L.varpi, L.theta_hi, L.eps))
            self.assertLessEqual(realized_rate, exchange + term)
        # the honest term is the larger one: the price of reaching what is underestimated
        self.assertGreater(honest_exploration_term(Q(1), Q(-3, 2), Q(25), Q(1, 50), Q(1, 5)),
                           clause_exploration_term(Q(1, 50), Q(1, 5)))


if __name__ == "__main__":
    unittest.main()
