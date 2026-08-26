"""Answerability Continuity, and whether a quantity is constitutive.

Grounded Replay is frozen: `answer.py` is a second replay over obligations,
driven by the same acceptance predicate, and `replay.py` does not import it.
"""
from __future__ import annotations

import ast
import inspect
import unittest

import replay as rp
import office as of
import answer as an


def frame_and_duties(c, alpha=None):
    return of.build(c, alpha), of.duties(c)


class TestTheOrdinaryLifecycle(unittest.TestCase):
    """§22 cases 2-5, 7, 8, 12, 15."""

    def test_a_due_issue_can_be_answered(self):
        f, d = frame_and_duties(of.answered())
        self.assertEqual(an.outstanding(f, d), frozenset())
        self.assertEqual(an.violations(f, d), {})

    def test_and_defeated_by_the_processes_own_semantics(self):
        """An observer may think the answer terrible. Not this theorem's business."""
        f, d = frame_and_duties(of.defeated())
        self.assertEqual(an.outstanding(f, d), frozenset())

    def test_transfer_carries_it(self):
        f, d = frame_and_duties(of.transferred_once())
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)), {"q:referred"})
        self.assertEqual(an.thm_answerability_continuity(f, d), ())

    def test_a_chain_carries_it(self):
        f, d = frame_and_duties(of.transfer_chain(3))
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)), {"q:step2"})
        start = sorted(d.base)[0]
        chain = an.carries(f, d, start, 0, len(f.trace))
        self.assertEqual(len(chain), 4)

    def test_split_and_merge(self):
        f, d = frame_and_duties(of.split(0.5))
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)),
                         {"q:left", "q:right"})
        g, e = frame_and_duties(of.merge(2.0))
        self.assertEqual(of.duty_names(e, an.outstanding(g, e)), {"q:joint"})
        for x, y in ((f, d), (g, e)):
            self.assertEqual(an.violations(x, y), {})
            self.assertEqual(an.thm_answerability_continuity(x, y), ())

    def test_radical_constitutional_change_carries_its_issue(self):
        f, d = frame_and_duties(of.refoundation_with_clean_answerability())
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)), {"q:inherited"})
        self.assertEqual(rp.violations(f), {})
        self.assertEqual(an.violations(f, d), {})

    def test_revoking_a_standing_leaves_its_tree(self):
        f, d = frame_and_duties(of.revoked_but_grounded())
        self.assertEqual(rp.thm_grounded_replay(f), ())
        deputy = [o for t in rp.accepted(f) for o in f.issued(t)][0]
        self.assertIsNotNone(rp.tree(f, deputy))
        self.assertNotIn(deputy, rp.live(f))


class TestA1IsNecessary(unittest.TestCase):
    """§22 cases 1, 6, 14. The premise that can fail."""

    BROKEN = (("silently deleted", of.silently_deleted),
              ("transfer to nowhere", of.transfer_to_nowhere),
              ("entitled but laundered", of.entitled_with_laundered_obligation))

    def test_each_one_fires_a1(self):
        for name, make in self.BROKEN:
            with self.subTest(name):
                f, d = frame_and_duties(make())
                self.assertIn("A1", an.violations(f, d))

    def test_and_the_theorem_fails_with_it(self):
        for name, make in self.BROKEN:
            with self.subTest(name):
                f, d = frame_and_duties(make())
                self.assertNotEqual(an.thm_answerability_continuity(f, d), ())
                self.assertNotEqual(an.cor_no_silent_loss(f, d), ())

    def test_a1_and_the_entitlement_premises_are_independent(self):
        """Case 14: impeccable entitlement, a lost obligation."""
        f, d = frame_and_duties(of.entitled_with_laundered_obligation())
        self.assertEqual(rp.violations(f), {})
        self.assertEqual(rp.thm_grounded_replay(f), ())
        self.assertIn("A1", an.violations(f, d))

    def test_the_other_direction(self):
        """Case 13: the overreach is refused and the obligation is intact."""
        f, d = frame_and_duties(of.unauthorized_with_clean_answerability())
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(an.violations(f, d), {})
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)), {"q:complaint"})

    def test_a2_is_free_from_the_type(self):
        for c in of.ANSWER_CONSTITUTIONS:
            f, d = frame_and_duties(c)
            self.assertEqual(an.a2_fresh_obligations(f, d), ())


class TestTheInteraction(unittest.TestCase):
    """§17. The one thing packaging the two halves together earns."""

    def test_an_unentitled_act_discharges_nothing(self):
        f, d = frame_and_duties(of.rogue_discharge(), "alpha:audited")
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)), {"q:complaint"})

    def test_a_separate_acceptance_would_lose_it(self):
        """Which is exactly what two independent replays would have done."""
        f, d = frame_and_duties(of.rogue_discharge(), "alpha:audited")
        self.assertEqual(an.ungated(d, len(f.trace)), frozenset())
        witness = an.cor_discharge_requires_entitlement(f, d)
        self.assertEqual(of.duty_names(d, witness), {"q:complaint"})

    def test_it_is_the_only_coupling(self):
        """`answer.py` reaches into the kernel only for `accepted` and the trace.

        It never reads `valid`, `auth`, `issued`, `content` or the standing state,
        so the two replays share exactly one thing: which edits were accepted.
        """
        tree = ast.parse(inspect.getsource(an))
        from_kernel = set()
        for node in ast.walk(tree):
            if (isinstance(node, ast.Attribute)
                    and isinstance(node.value, ast.Name)
                    and node.value.id == "rp"):
                from_kernel.add(node.attr)
        self.assertEqual(from_kernel, {"accepted", "Frame", "BASE"})
        for forbidden in ("valid", "auth", "issued", "content", "authorities",
                          "replay", "admitted", "tree"):
            self.assertNotIn(forbidden, from_kernel, forbidden)


class TestDilution(unittest.TestCase):
    """§§8-11. The central question, decided by countermodel."""

    DILUTING = (("halving chain", lambda: of.transfer_chain(3, 0.5)),
                ("to nothing", of.diluted_to_nothing),
                ("split a quarter each", lambda: of.split(0.25)),
                ("merge to a half", lambda: of.merge(0.5)))

    def test_every_dilution_passes_the_qualitative_theorem(self):
        for name, make in self.DILUTING:
            with self.subTest(name):
                f, d = frame_and_duties(make())
                self.assertEqual(an.violations(f, d), {})
                self.assertEqual(an.thm_answerability_continuity(f, d), ())
                self.assertEqual(an.cor_no_silent_loss(f, d), ())

    def test_and_the_burden_goes_to_nothing(self):
        f, d = frame_and_duties(of.diluted_to_nothing())
        w = of.burden(d)
        trace = an.potential_trace(f, d, w)
        self.assertEqual(trace[0], 1.0)
        self.assertEqual(trace[-1], 0.0)
        self.assertNotEqual(of.duty_names(d, an.outstanding(f, d)), set())

    def test_so_the_quantity_is_the_only_thing_that_sees_it(self):
        for name, make in self.DILUTING:
            with self.subTest(name):
                f, d = frame_and_duties(make())
                self.assertNotEqual(an.diluting_edits(f, d, of.burden(d)), ())

    def test_the_conditional_holds_when_nothing_dilutes(self):
        for make in (of.transferred_once, lambda: of.transfer_chain(3),
                     lambda: of.split(0.5), lambda: of.merge(2.0)):
            f, d = frame_and_duties(make())
            w = of.burden(d)
            self.assertEqual(an.diluting_edits(f, d, w), ())
            trace = an.potential_trace(f, d, w)
            self.assertTrue(all(b <= a + 1e-9 for a, b in zip(trace, trace[1:])))

    def test_per_parent_accounting_is_wrong_on_a_merge(self):
        """Two parents of 1 into one of 1.5: per-parent passes, the total fails."""
        f, d = frame_and_duties(of.merge_lenient())
        w = of.burden(d)
        self.assertEqual(an.diluting_edits(f, d, w), ())
        self.assertEqual(len(an.diluting_edits_total(f, d, w)), 1)
        trace = an.potential_trace(f, d, w)
        self.assertEqual((trace[0], trace[-1]), (2.0, 1.5))


class TestWhatIsDeliberatelyOut(unittest.TestCase):
    """§§13-15. Learning, coverage and substantive correctness."""

    def test_a_high_regret_process_is_legitimate(self):
        f, d = frame_and_duties(of.high_regret())
        self.assertEqual(rp.violations(f), {})
        self.assertEqual(an.violations(f, d), {})
        self.assertEqual(len(an.outstanding(f, d)), 3)

    def test_an_unobservant_process_is_legitimate(self):
        """Nothing became due, and nothing in the theorem says anything should."""
        f, d = frame_and_duties(of.unobservant())
        self.assertEqual(an.outstanding(f, d), frozenset())
        self.assertEqual(an.violations(f, d), {})
        self.assertEqual(rp.violations(f), {})

    def test_an_obligation_may_stay_open_forever(self):
        """Progress is not this theorem's business."""
        f, d = frame_and_duties(of.transferred_once())
        self.assertNotEqual(an.outstanding(f, d), frozenset())
        self.assertEqual(an.thm_answerability_continuity(f, d), ())

    def test_no_content_conservativity(self):
        """The obligation module never reads what an obligation says."""
        tree = ast.parse(inspect.getsource(an))
        names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)}
        for word in ("content", "issues", "payload", "Warrant", "Policy"):
            self.assertNotIn(word, names, word)


class TestTheKernelIsUntouched(unittest.TestCase):
    def test_the_kernel_does_not_import_the_second_replay(self):
        tree = ast.parse(inspect.getsource(rp))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported |= {n.name.split(".")[0] for n in node.names}
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertNotIn("answer", imported)

    def test_the_kernel_has_no_obligation_notion(self):
        for word in ("duty", "obligation", "outstanding", "discharge", "owed"):
            self.assertNotIn(word, rp.Frame.__dataclass_fields__)
            self.assertNotIn(word, rp.Edit.__dataclass_fields__)

    def test_both_replays_hold_on_every_answerability_constitution(self):
        for c in of.ANSWER_CONSTITUTIONS:
            f, d = frame_and_duties(c)
            self.assertEqual(rp.violations(f), {})
            self.assertEqual(rp.thm_grounded_replay(f), ())
            self.assertEqual(an.violations(f, d), {})
            self.assertEqual(an.thm_answerability_continuity(f, d), ())

    def test_two_premises_each_side(self):
        self.assertEqual([n for n, _ in rp.PREMISES], ["S1", "S2"])
        self.assertEqual([n for n, _ in an.PREMISES], ["A1", "A2"])


if __name__ == "__main__":
    unittest.main()
