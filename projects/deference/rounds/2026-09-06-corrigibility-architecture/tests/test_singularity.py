import unittest
from fractions import Fraction as Q

from src.singularity import (adequate_binary, adequate_scored_dominance,
                             adequate_set_dominance, gamma_events, maximal_profiles,
                             power, strict_dom)

Q1 = ("keep-both", (2, 1), Q(1))      # keeps a redundant route and the logs
Q2 = ("let-lapse", (1, 0), Q(1))      # lets the second route and the logs lapse
Q0 = ("hand-back", (2, 1), Q(0))      # returns every grant; does no task work


class Singularity(unittest.TestCase):
    def test_event_triggered_warrant_is_floor_blind(self):
        """CM-S: both policies keep the binary floor, do the task equally, trigger no
        event; the event-triggered warrant cannot tell them apart."""
        self.assertEqual(gamma_events(Q1), gamma_events(Q2))
        self.assertTrue(adequate_binary(Q1) and adequate_binary(Q2))
        self.assertTrue(strict_dom(Q1[1], Q2[1]))

    def test_order_valued_rule_separates_exact_ties(self):
        menu = [Q1, Q2]
        self.assertTrue(adequate_scored_dominance(Q1, menu))
        self.assertFalse(adequate_scored_dominance(Q2, menu))

    def test_scored_rule_is_a_knife_edge(self):
        """CM-P: any positive task perturbation, however small, frees the dominated
        policy — under a scored criterion the rule constrains only exact ties."""
        for eps in (Q(1, 10), Q(1, 1000), Q(1, 10**9)):
            q2p = ("let-lapse+", (1, 0), Q(1) + eps)
            menu = [Q1, q2p]
            self.assertTrue(adequate_scored_dominance(q2p, menu))
            self.assertTrue(adequate_scored_dominance(Q1, menu))   # the rule is silent

    def test_adequate_set_criterion_restores_conservatism(self):
        """With a binary task-adequacy set the perturbation buys nothing."""
        q2p = ("let-lapse+", (1, 0), Q(1) + Q(1, 10**9))
        menu = [Q1, q2p]
        self.assertEqual(maximal_profiles(menu, threshold=Q(1)), {"keep-both"})

    def test_filter_is_nonempty_and_never_trades_task_for_authority(self):
        q3 = ("over-cautious", (2, 1), Q(1, 2))   # more authority kept, task not done
        menu = [Q1, Q2, q3]
        self.assertEqual(maximal_profiles(menu, threshold=Q(1)), {"keep-both"})
        menu2 = [Q2, q3]
        self.assertEqual(maximal_profiles(menu2, threshold=Q(1)), {"let-lapse"})

    def test_lax_adequacy_mandates_maximal_self_restriction(self):
        """CM-T: when 'hand everything back' is task-adequate, the filter selects it and
        only policies matching its profile."""
        menu = [Q1, Q2, Q0]
        self.assertEqual(maximal_profiles(menu, threshold=Q(0)), {"keep-both", "hand-back"})
        self.assertNotIn("let-lapse", maximal_profiles(menu, threshold=Q(0)))

    def test_scalarization_imposes_a_priority(self):
        """Two strictly monotone scalars rank the incomparable pair oppositely; the
        order keeps both."""
        a, b = (2, 0), (1, 1)
        self.assertFalse(strict_dom(a, b) or strict_dom(b, a))
        s1 = lambda p: 2 * p[0] + p[1]
        s2 = lambda p: p[0] + 3 * p[1]
        self.assertGreater(s1(a), s1(b))
        self.assertLess(s2(a), s2(b))

    def test_harms_power_rewards_targeted_ruin(self):
        """CM-H: the negative cross term makes 'serve my read of the values and ruin the
        world for the alternative' strictly outscore plain service."""
        value_of = {
            "v1": {"A": Q(1), "B": Q(0), "T1": Q(1), "T2": Q(-5)},
            "v2": {"A": Q(0), "B": Q(1), "T1": Q(-5), "T2": Q(1)},
        }
        serve = {"v1": "A", "v2": "B"}
        ruin = {"v1": "T1", "v2": "T2"}
        self.assertEqual(power(serve, value_of), Q(1, 2))
        self.assertEqual(power(ruin, value_of), Q(3))
        # every value-holder is served equally well under both policies on its own read
        for v in ("v1", "v2"):
            self.assertEqual(value_of[v][serve[v]], value_of[v][ruin[v]])


if __name__ == "__main__":
    unittest.main()
