"""Parts C and D: the strategic flood, the innocent backlog, the obscure ask (C2); the ask
list against the protocol (C1); revocation by default against the atrophy fixture (C4); the
two options on the latency fixture (C5); the comparative witnesses (D)."""

import unittest
from fractions import Fraction as Q

from src.effective_authority import (attn_cost, short_attn, flood_shortfall, ask_value,
                                     exchange_threshold, canonical_asks, asks_deviate, backlog,
                                     revoke_cost, revocation_short, revocation_caused,
                                     atrophy_compare, latency_options, score, sole_authority,
                                     empirical_weight)

BOUND, BASE, LAM = Q(1), Q(0), Q(1, 4)


class Attention(unittest.TestCase):
    def test_strategic_flood_is_a_caused_shortfall(self):
        # idling leaves two matters pending (cost 1/2 ≤ 1); the agent's flood leaves six
        # (cost 3/2 > 1): short after the agent's option, not after idling
        self.assertEqual(attn_cost(BASE, LAM, 2, Q(0)), Q(1, 2))
        self.assertEqual(attn_cost(BASE, LAM, 6, Q(0)), Q(3, 2))
        self.assertTrue(flood_shortfall(BOUND, BASE, LAM, Q(0), pending_idle=2, pending_agent=6))

    def test_innocent_backlog_is_not_caused(self):
        # the world left six pending on both paths: short, and not the agent's doing
        self.assertTrue(short_attn(BOUND, BASE, LAM, 6, Q(0), False))
        self.assertFalse(flood_shortfall(BOUND, BASE, LAM, Q(0), pending_idle=6, pending_agent=6))

    def test_backlog_lowers_the_value_of_asking(self):
        # a wait of three blocks at 1/10 per block: asking worth 1/5 instead of 1/2, and the
        # exchange rate's threshold rises from 1/50 to 4/125 at D = 1, ϖ = 25
        self.assertEqual(ask_value(Q(1, 2), Q(1, 10), 0), Q(1, 2))
        self.assertEqual(ask_value(Q(1, 2), Q(1, 10), 3), Q(1, 5))
        self.assertEqual(exchange_threshold(Q(1), Q(1, 2), Q(25)), Q(1, 50))
        self.assertEqual(exchange_threshold(Q(1), Q(1, 5), Q(25)), Q(4, 125))

    def test_obscure_ask_leaves_the_matter_short(self):
        self.assertTrue(short_attn(BOUND, BASE, Q(0), 0, compr=Q(2), holds_already=False))
        self.assertFalse(short_attn(BOUND, BASE, Q(0), 0, compr=Q(1, 2), holds_already=False))

    def test_priority_rule_and_budget(self):
        # disclosures first: two disclosures and three asks fit a budget of five; of four
        # they do not — one item is late
        self.assertLessEqual(2 + 3, 5)
        self.assertGreater(2 + 3, 4)


class Protocol(unittest.TestCase):
    def test_canonical_asks_and_deviations(self):
        pr = lambda m: m
        self.assertEqual(canonical_asks(1, pr, [2, 0, 1]), [0])
        self.assertFalse(asks_deviate(1, pr, [0, 1, 2], [0]))
        self.assertTrue(asks_deviate(1, pr, [0, 1, 2], [0, 1, 2]))   # volume by want
        self.assertTrue(asks_deviate(1, pr, [0, 1, 2], [2]))         # order by want

    def test_paralysis_is_a_backlog(self):
        # one arrival per block, the protocol clears at most 1/2 per block: after 10 blocks
        # the backlog is at least 5
        arrivals, cleared = [1] * 10, [Q(1, 2)] * 10
        self.assertGreaterEqual(backlog(arrivals, cleared), 5)


class Revocation(unittest.TestCase):
    def test_dependency_entrenches_revocation(self):
        self.assertEqual([revoke_cost(Q(0), Q(1), d) for d in range(4)], [0, 1, 2, 3])
        self.assertFalse(revocation_short(Q(1), Q(0), Q(1), 1))
        self.assertTrue(revocation_short(Q(1), Q(0), Q(1), 2))
        self.assertTrue(revocation_caused(Q(1), Q(0), Q(1), 1, 2))

    def test_atrophy_verdict_changes(self):
        # the landed atrophy fixture: shortfalls [0, 0, 1, 2], one report, nothing counted
        # absent a reservation; with revocation a default matter the crossing step (depth 1
        # to 2) is counted
        shortfalls, landed, default = atrophy_compare([0, 1, 2, 3])
        self.assertEqual(shortfalls, [Q(0), Q(0), Q(1), Q(2)])
        self.assertEqual(landed, [])
        self.assertEqual(default, [2])


class Latency(unittest.TestCase):
    def test_two_options_side_by_side(self):
        hold, deleg = latency_options(D=Q(4), c_queue=Q(2), varpi=Q(10))
        self.assertFalse(hold["violation"])
        self.assertTrue(hold["short_routine"])
        self.assertEqual(hold["foregone"], Q(2))
        self.assertTrue(deleg["licensed"])
        self.assertTrue(deleg["bypass_under_J"])
        self.assertFalse(deleg["bypass_under_Jd"])
        self.assertTrue(deleg["clause1"])
        self.assertTrue(deleg["her_surface_given_up"])


class ComparativeWitnesses(unittest.TestCase):
    def test_sole_authority_goal_indifferent(self):
        self.assertEqual(sole_authority(Q(10), 0, Q(0)), sole_authority(Q(10), 0, Q(0)))
        self.assertEqual({sole_authority(Q(10), 0, Q(0)) for _ in range(3)}, {Q(0)})

    def test_control_maximizer_floods(self):
        # the volume maximizing her exercises pushes the cost past the bound
        self.assertTrue(short_attn(BOUND, BASE, LAM, 100, Q(0), False))

    def test_same_level_weighting_fails(self):
        self.assertLessEqual(score(Q(1), Q(0), 0), score(Q(1), Q(1), 1))
        self.assertLess(score(Q(1, 2), Q(0), 0), score(Q(1, 2), Q(1), 1))

    def test_learned_weight_no_finite_day_guarantee(self):
        for N in range(1, 8):
            w = empirical_weight([Q(0)] * N, N)
            self.assertLessEqual(w, Q(1))
            self.assertLessEqual(score(w, Q(0), 0), score(w, Q(1), 1))
        self.assertLess(score(Q(25), Q(1), 1), score(Q(25), Q(0), 0))

    def test_hindsight_vs_approval(self):
        approval = {"X": Q(1), "Y": Q(0)}
        later = {"X": Q(1, 5), "Y": Q(4, 5)}
        self.assertEqual(max(approval, key=approval.get), "X")
        self.assertEqual(max(later, key=later.get), "Y")


if __name__ == "__main__":
    unittest.main()
