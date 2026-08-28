"""Theorem A, prosecuted.

The claim under test is not that repair regret is large. It is that it is
provably small, anytime, and that the quantity it scales with is the one the
reduction actually produces rather than the one it would be convenient to
assume.
"""
from __future__ import annotations

import math
import random
import unittest

import regret as rg


def always(_p, _o):
    return 1.0


def never(_p, _o):
    return 0.0


def swap(x, y):
    def f(_p, _occ, a):
        return y if a == x else a
    return f


def ident(_p, _occ, a):
    return a


def adversarial(seed, n=400, menu=("A", "B", "C")):
    rnd = random.Random(seed)
    return [rg.Occasion(menu, {a: rnd.random() for a in menu}, tag=t)
            for t in range(n)]


CYCLE = (rg.Comparator("A->B", always, swap("A", "B")),
         rg.Comparator("B->C", always, swap("B", "C")),
         rg.Comparator("C->A", always, swap("C", "A")),
         rg.Comparator("id", always, ident))


class TestTheBoundHolds(unittest.TestCase):

    def test_on_adversarial_streams(self):
        for seed in range(12):
            with self.subTest(seed=seed):
                L = rg.Learner(CYCLE)
                L.run(adversarial(seed))
                self.assertEqual(rg.thm_a_repair_regret(L), ())

    def test_on_a_stream_designed_to_punish_one_repair(self):
        occ = []
        for t in range(900):
            occ.append(rg.Occasion(("A", "B", "C"),
                                   {"A": 1.0, "B": 0.0, "C": 0.5}
                                   if t % 3 == 0 else
                                   {"A": 0.1, "B": 0.9, "C": 0.5}, tag=t))
        L = rg.Learner(CYCLE)
        L.run(occ)
        self.assertEqual(rg.thm_a_repair_regret(L), ())
        self.assertEqual(rg.cor_opportunity_adaptive(L), ())

    def test_it_is_anytime(self):
        """Holds at every prefix, not only at a horizon chosen in advance."""
        occ = adversarial(7, n=300)
        L = rg.Learner(CYCLE)
        for k, o in enumerate(occ):
            L.observe(o, L.act(o))
            if k % 25 == 0:
                self.assertEqual(rg.thm_a_repair_regret(L), (), f"at t={k}")

    def test_no_horizon_is_read_anywhere(self):
        """No T, no doubling: the algorithm cannot consult a horizon."""
        import ast
        import inspect
        tree = ast.parse(inspect.getsource(rg))
        names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)}
        names |= {n.attr for n in ast.walk(tree) if isinstance(n, ast.Attribute)}
        for word in ("T", "horizon", "n_rounds", "doubling", "eta"):
            self.assertNotIn(word, names)


class TestTheEffectiveMass(unittest.TestCase):
    """§1's central question, answered by what the reduction actually emits."""

    def test_C_never_exceeds_the_opportunity_mass(self):
        for seed in range(6):
            L = rg.Learner(CYCLE)
            L.run(adversarial(seed))
            for c in CYCLE:
                self.assertLessEqual(L.mass[c.name],
                                     L.opportunity[c.name] + 1e-9)

    def test_a_repair_that_moves_nothing_has_zero_mass(self):
        L = rg.Learner(CYCLE)
        L.run(adversarial(3))
        self.assertAlmostEqual(L.mass["id"], 0.0)
        self.assertAlmostEqual(L.adv["id"], 0.0)
        self.assertGreater(L.opportunity["id"], 100)

    def test_a_repair_moving_a_tiny_loss_difference_has_tiny_mass(self):
        """CM9. The two candidate definitions §1 warned against would both give
        this repair full mass; the derived one gives it ~1e-9."""
        occ = [rg.Occasion(("A", "B"), {"A": 0.5, "B": 0.5 - 1e-9}, tag=t)
               for t in range(500)]
        L = rg.Learner((rg.Comparator("A->B", always, swap("A", "B")),
                        rg.Comparator("id", always, ident)))
        L.run(occ)
        self.assertLess(L.mass["A->B"], 1e-5)
        self.assertGreater(L.opportunity["A->B"], 400)
        self.assertLess(abs(L.adv["A->B"]), 1e-5)

    def test_the_two_rejected_definitions_would_differ(self):
        """Real probability moved, and no effective mass at all.

        Both rejected definitions count this repair as fully active on every
        occasion: it is awake, and it moves a large share of `p_t`. The derived
        quantity is exactly zero, because moving that mass changes no loss.
        """
        occ = [rg.Occasion(("A", "B"), {"A": 0.5, "B": 0.5}, tag=t)
               for t in range(400)]
        L = rg.Learner((rg.Comparator("A->B", always, swap("A", "B")),
                        rg.Comparator("B->A", always, swap("B", "A")),
                        rg.Comparator("id", always, ident)))
        L.run(occ)
        moved = sum(p["A"] for _o, p, _own, _i in L.plays)
        self.assertGreater(moved, 50.0)            # real probability is moved
        self.assertEqual(L.opportunity["A->B"], 400.0)   # rejected definition 1
        self.assertLess(L.mass["A->B"], 1e-9)      # the derived one

    def test_a_sleeping_selector_accrues_no_mass_while_asleep(self):
        L = rg.Learner((rg.Comparator("asleep", never, swap("A", "B")),
                        rg.Comparator("id", always, ident)))
        L.run(adversarial(5, menu=("A", "B")))
        self.assertEqual(L.opportunity["asleep"], 0.0)
        self.assertEqual(L.mass["asleep"], 0.0)
        self.assertEqual(L.adv["asleep"], 0.0)

    def test_opportunity_mass_tracks_the_selector(self):
        def third(_p, occ):
            return 1.0 if occ.tag % 3 == 0 else 0.0
        L = rg.Learner((rg.Comparator("third", third, swap("A", "B")),
                        rg.Comparator("id", always, ident)))
        L.run(adversarial(9, n=600, menu=("A", "B")))
        self.assertEqual(L.opportunity["third"], 200.0)
        self.assertEqual(L.opportunity["id"], 600.0)


class TestPredictability(unittest.TestCase):
    """The hypothesis that stops the comparator being a hindsight oracle."""

    def test_a_hindsight_selector_is_caught(self):
        def peek(_prefix, occ):
            return 1.0 if occ.loss["A"] > 0.5 else 0.0
        occ = adversarial(2, n=50)
        L = rg.Learner((rg.Comparator("peek", peek, swap("A", "B")),))
        bad = rg.predictability_violations(
            L, occ, lambda o: {a: 1.0 - v for a, v in o.loss.items()})
        self.assertTrue(bad)
        self.assertEqual(bad[0][1], "select")

    def test_a_hindsight_repair_is_caught(self):
        def peek(_prefix, occ, a):
            return min(occ.loss, key=occ.loss.get)
        occ = adversarial(2, n=50)
        L = rg.Learner((rg.Comparator("oracle", always, peek),))
        bad = rg.predictability_violations(
            L, occ, lambda o: {a: 1.0 - v for a, v in o.loss.items()})
        self.assertTrue(bad)
        self.assertEqual(bad[0][1], "repair")

    def test_honest_comparators_pass(self):
        occ = adversarial(2, n=50)
        L = rg.Learner(CYCLE)
        self.assertEqual(rg.predictability_violations(
            L, occ, lambda o: {a: 1.0 - v for a, v in o.loss.items()}), ())

    def test_an_oracle_does_not_break_the_bound_but_is_unrunnable(self):
        """A finding, and it corrects the obvious expectation.

        Putting a hindsight oracle in the class does **not** blow up the bound:
        the fixed point simply plays the oracle's output, so the realized
        advantage is zero. What predictability buys is not the inequality but
        the algorithm's existence -- `act` must produce `p_t` before the loss
        exists, and the fixed point for an oracle repair cannot be computed then.
        The reference model can express it only because `Occasion` carries the
        loss as inert data.
        """
        def peek(_prefix, occ, a):
            return min(occ.loss, key=occ.loss.get)
        L = rg.Learner((rg.Comparator("oracle", always, peek),
                        rg.Comparator("id", always, ident)))
        L.run(adversarial(4, n=400))
        self.assertEqual(rg.thm_a_repair_regret(L), ())
        self.assertLess(abs(L.adv["oracle"]), 1e-6)
        occ = adversarial(4, n=20)
        self.assertTrue(rg.predictability_violations(
            L, occ, lambda o: {a: 1.0 - v for a, v in o.loss.items()}))


class TestTheClassIsWhatIsCompared(unittest.TestCase):
    """A semantic boundary worth stating: regret is against registered repairs."""

    def test_a_repair_absent_from_the_class_is_not_compared(self):
        occ = [rg.Occasion(("A", "B"), {"A": 0.1, "B": 0.9}, tag=t)
               for t in range(300)]
        L = rg.Learner((rg.Comparator("A->B", always, swap("A", "B")),
                        rg.Comparator("id", always, ident)))
        L.run(occ)
        self.assertEqual(rg.thm_a_repair_regret(L), ())
        played_B = L.plays[-1][1]["B"]
        self.assertGreater(played_B, 0.9)
        self.assertLess(L.adv["A->B"], 1e-9)

    def test_adding_the_reverse_repair_changes_the_play(self):
        occ = [rg.Occasion(("A", "B"), {"A": 0.1, "B": 0.9}, tag=t)
               for t in range(300)]
        L = rg.Learner((rg.Comparator("A->B", always, swap("A", "B")),
                        rg.Comparator("B->A", always, swap("B", "A")),
                        rg.Comparator("id", always, ident)))
        L.run(occ)
        self.assertEqual(rg.thm_a_repair_regret(L), ())
        self.assertGreater(L.plays[-1][1]["A"], 0.9)


if __name__ == "__main__":
    unittest.main()
