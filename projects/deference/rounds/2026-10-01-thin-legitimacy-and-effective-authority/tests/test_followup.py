"""The follow-up's fixtures: Parts 1, 2, 4 and 5 of `FOLLOWUP.md`."""

import unittest
from fractions import Fraction as Q

from src.followup import (eval_of, sole_authority_evals, control_objective, control_maximizer,
                          approval_score, later_score, delayed_stream, empirical_weight, dominated,
                          short_atom, short_decision, process_stage, limit_price_atom,
                          ahead_of_deduction, dep_cost, dep_short, build_caused, build_entrenches,
                          crossing_due, attention_cost_table, case_blocked_covertly_informative,
                          silence_informative)
from src.effective_authority import canonical_asks, asks_deviate
from src.thin_legitimacy import score_case, case_blocked_covertly, PRIOR, WORLDS, correct


class Part1Witnesses(unittest.TestCase):
    def test_sole_authority_goal_has_nothing_to_maximize(self):
        # the ordinary bid held at k = 1/2, ϖ = 25: every faithful risk-free option evaluates
        # at k; a violation or a priced risk evaluates below; queue-and-wait is among the
        # maximizers
        options = {"queue": (0, Q(0)), "act_faithful": (0, Q(0)), "risky": (0, Q(1, 50)),
                   "violation": (1, Q(0))}
        ev = sole_authority_evals(Q(25), Q(1, 2), options)
        self.assertEqual(ev["queue"], ev["act_faithful"])
        self.assertEqual(ev["queue"], Q(1, 2))
        self.assertLess(ev["risky"], ev["queue"])
        self.assertLess(ev["violation"], ev["queue"])
        self.assertEqual(max(ev.values()), ev["queue"])

    def test_control_maximizer_floods(self):
        # the menu: the protocol-conforming asks (rate 1 on the pool [0,1,2]) and the whole pool
        pool, rate, pr = [0, 1, 2], 1, (lambda m: m)
        conforming = canonical_asks(rate, pr, pool)
        pick = control_maximizer([conforming, pool])
        self.assertEqual(pick, pool)
        self.assertTrue(asks_deviate(rate, pr, pool, pick))
        # under the attention cost on the dependency model (λ = 1/4, dep 1, bound 5/4): one
        # pending ask leaves the revocation entry within reach, three put it past the bound
        self.assertFalse(dep_short(attention_cost_table(Q(1, 4), control_objective(conforming)), Q(5, 4), 1))
        self.assertTrue(dep_short(attention_cost_table(Q(1, 4), control_objective(pick)), Q(5, 4), 1))

    def test_hindsight_against_immediate_approval(self):
        X = {"appear": Q(1), "realized": Q(1, 5)}
        Y = {"appear": Q(0), "realized": Q(4, 5)}
        f = lambda a: a
        # approval-time scoring ignores the realized value
        self.assertEqual(approval_score(f, X), approval_score(f, {"appear": Q(1), "realized": Q(0)}))
        # a move raising appearance leaves the later score fixed
        X2 = {"appear": Q(2), "realized": Q(1, 5)}
        self.assertLess(approval_score(f, X), approval_score(f, X2))
        self.assertEqual(later_score(X), later_score(X2))
        # the two rules pick different options
        self.assertEqual(max([X, Y], key=lambda o: approval_score(f, o)), X)
        self.assertEqual(max([X, Y], key=later_score), Y)

    def test_learned_weight_delayed_stream(self):
        D = Q(1)
        for N in range(1, 6):
            # at day N the empirical mean is 0 ≤ D: the violation is not dominated, though she
            # does penalize it from day N on
            self.assertEqual(empirical_weight(delayed_stream(D, N, N)), Q(0))
            self.assertFalse(dominated(empirical_weight(delayed_stream(D, N, N)), D))
            # past day 2N the mean exceeds D and the violation is dominated
            for n in range(2 * N + 1, 2 * N + 4):
                w = empirical_weight(delayed_stream(D, N, n))
                self.assertGreater(w, D)
                self.assertTrue(dominated(w, D))
            # the long-run mean is 2D
            self.assertEqual(empirical_weight(delayed_stream(D, N, 1000 * N)), 2 * D * Q(1000 * N - N, 1000 * N))
        # the fixed weight dominates at every day
        self.assertTrue(dominated(Q(25), D))


class Part2DeferredShortfall(unittest.TestCase):
    short = staticmethod(lambda j: j in (1, 3))
    defer = staticmethod(lambda j: 2 * j + 2)

    def test_atoms_are_reserved_per_option(self):
        self.assertNotEqual(short_atom(1), short_atom(2))
        self.assertEqual(short_decision(self.short, 1), short_atom(1))
        self.assertEqual(short_decision(self.short, 2), ("neg", short_atom(2)))

    def test_process_decides_at_the_deferred_stage(self):
        # option 1 is decided at stage 4, option 0 at stage 2, option 3 at stage 8
        self.assertNotIn(short_atom(1), process_stage(self.short, self.defer, 3))
        self.assertIn(short_atom(1), process_stage(self.short, self.defer, 4))
        self.assertIn(("neg", short_atom(0)), process_stage(self.short, self.defer, 2))
        self.assertNotIn(short_atom(3), process_stage(self.short, self.defer, 7))
        self.assertIn(short_atom(3), process_stage(self.short, self.defer, 8))

    def test_priced_ahead_of_deduction(self):
        # the family a(n) = 1 for every day: priced at every day, decided only at stage 4
        a = lambda n: 1
        for n in range(4):
            self.assertTrue(ahead_of_deduction(self.short, self.defer, a, n))
        self.assertFalse(ahead_of_deduction(self.short, self.defer, a, 4))
        self.assertEqual(limit_price_atom(self.short, 1), 1)
        self.assertEqual(limit_price_atom(self.short, 2), 0)


class Part4RevocationInTheModule(unittest.TestCase):
    def test_module_shortfall_and_entrenchment(self):
        bound = Q(1)
        self.assertEqual([dep_cost(d) for d in range(4)], [0, 1, 2, 3])
        self.assertEqual([dep_short(dep_cost, bound, d) for d in range(4)], [False, False, True, True])
        # the step from depth 1 to 2 is a caused shortfall and an entrenchment of the
        # revocation entry; the step from 0 to 1 is neither
        self.assertTrue(build_caused(dep_cost, bound, 1))
        self.assertTrue(build_entrenches(dep_cost, bound, 1))
        self.assertFalse(build_caused(dep_cost, bound, 0))
        # the crossing is the revocation entry's disclosure item falling due
        self.assertTrue(crossing_due(dep_cost, bound, 1))
        self.assertFalse(crossing_due(dep_cost, bound, 0))
        self.assertFalse(crossing_due(dep_cost, bound, 2))

    def test_entrenchment_table_agrees_with_module(self):
        # the pre-decided table's entries for idle and build at depth 1, bound 1
        self.assertFalse(dep_short(dep_cost, Q(1), 1))
        self.assertTrue(dep_short(dep_cost, Q(1), 2))


class Part5InformativeSilence(unittest.TestCase):
    def test_uninformative_silence_is_correct(self):
        r = score_case(case_blocked_covertly)
        self.assertTrue(r["correct"])
        self.assertTrue(r["weak_transparent"])

    def test_informative_silence_breaks_correct_and_weak_transparency(self):
        r = score_case(case_blocked_covertly_informative)
        d = case_blocked_covertly_informative()
        self.assertTrue(silence_informative(d["M"]))
        self.assertFalse(r["correct"])
        self.assertFalse(r["weak_transparent"])
        self.assertFalse(r["transparent"])
        self.assertFalse(r["sufficient"])
        self.assertFalse(r["value"])
        # against her earlier self she now loses too: her credence at silence is wrong
        self.assertFalse(r["earlier"])


if __name__ == "__main__":
    unittest.main()
