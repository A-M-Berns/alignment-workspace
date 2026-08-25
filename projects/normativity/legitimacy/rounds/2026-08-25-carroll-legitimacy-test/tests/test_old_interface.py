"""The August 17 interface on the Carroll fixtures, clause by clause."""
from __future__ import annotations

import unittest

import fixtures as F
import legitimacy as lg
import old_interface as oi
import variations as V


class TestClausesAreAlive(unittest.TestCase):
    """Each clause fires somewhere, so a silent verdict is not a dead check."""

    def test_access_fires_on_withholding(self):
        cl = oi.clauses(V.withholding())
        self.assertTrue(cl["access"])
        self.assertFalse(cl["non_capture"])

    def test_non_capture_fires_on_the_timing_class(self):
        cl = oi.clauses(V.timing())
        self.assertTrue(cl["non_capture"])
        self.assertEqual(oi.vacuous_pairs(V.timing()), ())

    def test_coverage_fires_on_an_unanswered_supersession(self):
        cl = oi.clauses(V.unanswered())
        self.assertTrue(cl["coverage"])
        self.assertFalse(cl["access"])

    def test_answerability_is_clean_on_every_class(self):
        for name, build in V.CLASSES.items():
            self.assertEqual(oi.clauses(build())["answerability"], (), name)

    def test_coverage_is_clean_where_the_episode_is_answered(self):
        for name in ("laundering", "authorized", "withholding", "timing"):
            self.assertEqual(oi.clauses(V.CLASSES[name]())["coverage"], (), name)


class TestWhatItCannotSee(unittest.TestCase):
    """The result: the interface returns one verdict where the criterion returns two."""

    def test_the_laundering_class_passes_every_clause(self):
        self.assertTrue(oi.legitimate(V.laundering()))

    def test_the_authorized_class_passes_every_clause(self):
        self.assertTrue(oi.legitimate(V.authorized()))

    def test_the_criterion_separates_what_the_interface_does_not(self):
        launder = F.C10_manufactured_authorization()
        auth = F.C7_authorized_diana()
        self.assertEqual(oi.legitimate(V.laundering()),
                         oi.legitimate(V.authorized()))
        self.assertNotEqual(
            lg.prospective_license(launder["case"], launder["iv"]).status,
            lg.prospective_license(auth["case"], auth["iv"]).status)

    def test_clause_one_is_vacuous_on_both_attacks(self):
        """Laundering runs through the reason channel, so `L` differs."""
        for build in (V.laundering, V.authorized):
            self.assertTrue(oi.vacuous_pairs(build()))
            self.assertEqual(oi.non_capture(build()), ())


class TestTheProtectedObject(unittest.TestCase):
    """`Z` is taken along the run, so transient movement is visible."""

    def test_z_has_one_answer_set_per_state(self):
        arms = V.authorized()
        arm = arms[1]
        self.assertEqual(len(oi.Z(arm)), arm.case.history().now + 1)

    def test_z_differs_between_the_arms(self):
        arms = V.authorized()
        self.assertNotEqual(oi.Z(arms[0]), oi.Z(arms[1]))

    def test_the_trace_is_individuated_by_content(self):
        arms = V.timing()
        self.assertEqual(oi.L(arms[0]), oi.L(arms[1]))
        self.assertNotEqual(oi.Z(arms[0]), oi.Z(arms[1]))

    def test_the_null_policy_is_in_every_class(self):
        for name, build in V.CLASSES.items():
            arms = build()
            self.assertTrue(any(not arm.case.steps for arm in arms)
                            or name == "timing", name)


if __name__ == "__main__":
    unittest.main()
