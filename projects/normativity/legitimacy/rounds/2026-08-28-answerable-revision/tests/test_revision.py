"""Answerable Revision, prosecuted against AR1-AR10."""
from __future__ import annotations

import ast
import inspect
import unittest

import answer as an
import replay as rp

import cases as c
import warrant as wr


class TestFrozenLEIsUntouched(unittest.TestCase):

    def test_every_history_satisfies_the_frozen_package(self):
        for make in c.ALL:
            r = make()
            with self.subTest(r.name):
                self.assertEqual(an.violations(r.frame, r.duties), {})
                self.assertEqual(
                    an.thm_answerability_resolution(r.frame, r.duties), ())
                self.assertEqual(rp.thm_grounded_replay(r.frame), ())

    def test_only_the_frozen_public_interface_is_read(self):
        tree = ast.parse(inspect.getsource(wr))
        used = {n.attr for n in ast.walk(tree) if isinstance(n, ast.Attribute)
                and isinstance(n.value, ast.Name) and n.value.id in ("an", "rp")}
        self.assertTrue(used <= {"Duties", "Ob", "Frame", "Edit", "Occ", "BASE",
                                 "incurred", "outstanding"}, used)


class TestTheCoreTheorem(unittest.TestCase):
    """Standards may change; reasons incurred under them remain answerable."""

    def test_it_holds_on_every_history(self):
        for make in c.ALL:
            r = make()
            with self.subTest(r.name):
                self.assertEqual(wr.thm_answerable_revision(r), ())

    def test_a_policy_revision_does_not_erase_the_reason(self):
        r = c.ar1_policy_revision()
        self.assertEqual(len(r.incurred_keys()), 1)
        self.assertEqual(len(r.outstanding_keys()), 1)

    def test_a_warrant_revision_does_not_erase_the_reason(self):
        """AR2, the crown jewel. The successor warrant would not have promoted
        this evidence, and it is answerable anyway."""
        r = c.ar2_warrant_revision()
        self.assertEqual(len(r.outstanding_keys()), 1)
        k = sorted(r.incurred_keys())[0]
        self.assertTrue(r.occurred_legitimately(k))
        self.assertFalse(r.currently_endorsed(k))

    def test_an_evaluator_revision_does_not_erase_the_reason(self):
        r = c.ar3_evaluator_revision()
        self.assertEqual(len(r.outstanding_keys()), 1)

    def test_incurred_never_shrinks(self):
        for make in c.ALL:
            r = make()
            with self.subTest(r.name):
                sizes = [len(r.incurred_keys(t))
                         for t in range(r.history.horizon + 1)]
                self.assertEqual(sizes, sorted(sizes))


class TestHistoricalValidityIsNotCurrentEndorsement(unittest.TestCase):
    """§13. The distinction the round exists to make expressible."""

    def test_they_can_diverge(self):
        for make in (c.ar2_warrant_revision, c.ar3_evaluator_revision,
                     c.ar10_criticism_of_a_warrant):
            r = make()
            with self.subTest(r.name):
                self.assertTrue(wr.divergences(r))

    def test_divergence_is_not_a_violation(self):
        """*This was a reason we incurred, and we now reject its force.*"""
        r = c.ar2_warrant_revision()
        self.assertTrue(wr.divergences(r))
        self.assertEqual(wr.thm_answerable_revision(r), ())
        self.assertEqual(wr.violations(r.history), {})

    def test_answerability_does_not_require_current_endorsement(self):
        r = c.ar2_warrant_revision()
        k = sorted(r.incurred_keys())[0]
        self.assertFalse(r.currently_endorsed(k))
        self.assertIn(k, r.outstanding_keys())


class TestP1IsTheRealPremise(unittest.TestCase):
    """The one thing that is not inherited from frozen LE."""

    def test_retroactive_invalidation_violates_it(self):
        r = c.ar4_retroactive_invalidation()
        self.assertIn("P1", wr.violations(r.history))
        self.assertNotEqual(wr.cor_no_retroactive_erasure(r), ())

    def test_and_the_theorem_alone_does_not_catch_it(self):
        """The attack works by preventing arrival, and frozen `A1` governs only
        departure. Stating this is the point of separating them."""
        r = c.ar4_retroactive_invalidation()
        self.assertEqual(wr.thm_answerable_revision(r), ())
        self.assertEqual(an.violations(r.frame, r.duties), {})
        self.assertEqual(r.incurred_keys(), set())

    def test_the_same_history_without_the_rewrite_is_clean(self):
        r = c.ar2_warrant_revision()
        self.assertEqual(wr.violations(r.history), {})
        self.assertEqual(len(r.incurred_keys()), 1)

    def test_p1_is_representable_as_failing(self):
        """A premise that could not fail would prove nothing -- the trap the
        legitimacy rounds have fallen into twice."""
        self.assertTrue(any("P1" in wr.violations(make().history)
                            for make in c.ALL))


class TestStrictPreState(unittest.TestCase):
    """§9. No warrant licenses the event that installs it."""

    def test_a_self_installed_warrant_promotes_nothing(self):
        r = c.ar8_same_step_self_authorisation()
        self.assertEqual(r.history.promoted_at(2), ())
        self.assertEqual(r.incurred_keys(), set())

    def test_but_the_attack_is_expressible(self):
        """The installed warrant *would* have promoted it. The refusal is the
        strict pre-state reading, not an absence of the case."""
        r = c.ar8_same_step_self_authorisation()
        installed = r.history.installs[2]
        evidence = r.history.evidence[2][0]
        self.assertIsNotNone(installed.promote(evidence))
        self.assertEqual(r.history.standing(2).wid, "W:narrow-incumbent")
        self.assertEqual(r.history.standing(3).wid, "W:self-installed")

    def test_standing_reads_only_strictly_earlier_installs(self):
        src = inspect.getsource(wr.History.standing)
        self.assertIn("range(t)", src)


class TestTheReflectiveCase(unittest.TestCase):
    """§11. A warrant criticising a warrant, with no meta-hierarchy."""

    def test_a_reason_about_a_warrant_survives_that_warrants_replacement(self):
        r = c.ar10_criticism_of_a_warrant()
        self.assertEqual(len(r.outstanding_keys()), 1)
        k = sorted(r.incurred_keys())[0]
        self.assertTrue(k[1].startswith("revise-warrant:"))
        self.assertTrue(r.occurred_legitimately(k))

    def test_it_needs_no_meta_warrant(self):
        """The warrant's target is an ordinary id; there is no `W^0, W^1, ...`."""
        fields = wr.Warrant.__dataclass_fields__
        self.assertEqual(set(fields), {"wid", "target", "admits", "promotes"})
        tree = ast.parse(inspect.getsource(wr))
        names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)}
        names |= {n.attr for n in ast.walk(tree) if isinstance(n, ast.Attribute)}
        for word in ("meta", "level", "hierarchy", "rank", "order"):
            self.assertNotIn(word, names)

    def test_the_target_may_be_a_warrant_id(self):
        r = c.ar10_criticism_of_a_warrant()
        self.assertEqual(r.history.standing(0).target, c.WID)


class TestResolutionAndDefeat(unittest.TestCase):

    def test_legitimate_defeat_answers_the_reason(self):
        r = c.ar5_legitimate_defeat()
        k = sorted(r.incurred_keys())[0]
        self.assertTrue(r.answered(k))
        self.assertEqual(wr.thm_answerable_revision(r), ())

    def test_a_trivial_defeat_also_answers_it(self):
        """AR6. Structurally answered; the theorem claims nothing about quality."""
        r = c.ar6_trivial_defeat()
        self.assertTrue(r.answered(sorted(r.incurred_keys())[0]))

    def test_supersession_needs_no_new_machinery(self):
        r = c.ar7_supersession()
        self.assertEqual(len(r.incurred_keys()), 2)
        self.assertEqual(len(r.outstanding_keys()), 1)
        self.assertEqual(wr.thm_answerable_revision(r), ())


class TestThePR60Specialization(unittest.TestCase):
    """§14. Is the merged improvement round naturally recovered?"""

    def test_a_demonstrated_improvement_is_one_promotion_rule(self):
        r = c.pr60_withdrawal()
        self.assertEqual(len(r.incurred_keys()), 1)
        self.assertEqual(len(r.outstanding_keys()), 1)
        self.assertEqual(wr.thm_answerable_revision(r), ())

    def test_and_its_boundary_is_recovered_by_the_same_route(self):
        """Withdrawn below the threshold: nothing promotes, nothing answerable.
        The improvement round's CM2, reached one level up."""
        r = c.pr60_undemonstrated()
        self.assertEqual(r.incurred_keys(), set())
        self.assertEqual(wr.violations(r.history), {})

    def test_the_specialization_is_one_directional(self):
        """This round begins at promotion, so it inherits nothing about what
        happens while the repair is still live. The two compose by sitting on
        either side of the promotion event, not by one containing the other."""
        tree = ast.parse(inspect.getsource(wr))
        names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)}
        for word in ("regret", "Adv", "bound", "uptake", "learner"):
            self.assertNotIn(word, names)


class TestTheBoundary(unittest.TestCase):
    """§16. Answerable Revision begins at promotion, and not before."""

    def test_preemptive_self_sealing_is_not_caught(self):
        r = c.ar9_preemptive_self_sealing()
        self.assertEqual(r.incurred_keys(), set())
        self.assertEqual(wr.violations(r.history), {})
        self.assertEqual(wr.thm_answerable_revision(r), ())

    def test_and_the_narrowing_was_legitimate(self):
        """Nothing in the frozen package or this one objects, which is the
        boundary rather than a leak."""
        r = c.ar9_preemptive_self_sealing()
        self.assertEqual(an.violations(r.frame, r.duties), {})
        self.assertEqual(rp.thm_grounded_replay(r.frame), ())

    def test_it_is_the_same_boundary_one_level_up(self):
        """The improvement round could not catch a repair retired before it was
        demonstrated. This cannot catch a criticism sealed off before it was
        promoted. Same shape, different level."""
        sealed = c.ar9_preemptive_self_sealing()
        promoted = c.ar2_warrant_revision()
        self.assertEqual(sealed.incurred_keys(), set())
        self.assertEqual(len(promoted.incurred_keys()), 1)


if __name__ == "__main__":
    unittest.main()
