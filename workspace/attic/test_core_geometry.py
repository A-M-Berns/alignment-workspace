"""WP-3: the two readings of the core condition, and transport under pins."""

from __future__ import annotations

import unittest
from fractions import Fraction as Q

from src.core_geometry import (
    QUARANTINE_OF_FORCE,
    accumulate_pins,
    ambient_core_holds,
    ambient_vertices,
    ambient_voids_nondegenerate,
    ambient_voids_witness,
    clipping_adapter_admits,
    core_admissible_reference,
    core_admission,
    core_upper_bound,
    dependent_pin_failure,
    endorsement_rows,
    max_core_coefficient,
    pin_effect,
    pin_is_independent,
    relative_core_holds,
    relative_vertices,
    single_row_core_coefficient,
    small_instance_search,
    transport_lemma,
)
from src.leverage_interval import Book, Endorsement, Language, SettledFact


class AmbientReadingTests(unittest.TestCase):
    """The ambient reading voids on the first exact pin."""

    def test_the_two_sentence_witness_voids_at_every_coefficient(self):
        witness = ambient_voids_witness()
        self.assertEqual(len(witness["language"].truth), 2, "two sentences")
        self.assertEqual(len(witness["settled"]), 1, "one exact pin")
        for coefficient, holds in witness["ambient"]:
            with self.subTest(coefficient=coefficient):
                self.assertFalse(holds)
        for coefficient, holds in witness["relative"]:
            with self.subTest(coefficient=coefficient):
                self.assertTrue(holds)

    def test_the_voiding_is_not_an_artifact_of_a_collapsed_region(self):
        """A three-world instance whose post-pin region is still a segment."""
        witness = ambient_voids_nondegenerate()
        self.assertEqual(witness["region_dimension"], 1)
        self.assertGreater(len(relative_vertices(witness["language"],
                                                 witness["settled"])), 1)
        self.assertTrue(all(not holds for _, holds in witness["ambient"]))
        self.assertTrue(all(holds for _, holds in witness["relative"]))

    def test_the_dimension_count_is_what_drives_it(self):
        """The homothet keeps the ambient dimension; a pinned region loses one."""
        language = Language(("w1", "w2", "w3"), {"A": ("w1", "w2"), "B": ("w2",)})
        self.assertEqual(len(ambient_vertices(3)), 3)
        pinned = relative_vertices(language, (SettledFact("A", Q(1, 2)),))
        self.assertLess(len(pinned), len(ambient_vertices(3)))

    def test_an_unpinned_region_does_not_void(self):
        """Without a pin the ambient reading is satisfiable, so the pin is the cause."""
        language = Language(("w1", "w2"), {"A": ("w1",), "B": ("w2",)})
        book = Book(1, ())
        self.assertTrue(
            ambient_core_holds(language, book, (), (Q(1, 2), Q(1, 2)), Q(1)))


class ClosedFormTests(unittest.TestCase):

    def test_the_single_row_coefficient_is_the_closed_form(self):
        self.assertEqual(single_row_core_coefficient(Q(0), Q(1, 2), Q(1)), Q(1, 2))
        self.assertEqual(single_row_core_coefficient(Q(0), Q(1, 4), Q(1)), Q(3, 4))
        self.assertEqual(single_row_core_coefficient(Q(0), Q(1), Q(1)), Q(0))

    def test_the_closed_form_agrees_with_the_search(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),))
        bound = max_core_coefficient(language, book, ())
        self.assertTrue(bound.exact)
        self.assertEqual(bound.working, Q(1, 2))
        self.assertEqual(bound.upper_bound, Q(1, 2))
        self.assertEqual(bound.witness, (Q(1), Q(0), Q(0)))

    def test_the_per_row_bound_caps_the_joint_problem(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),
                        Endorsement("e:B", (Q(0), Q(1), Q(0)), Q(1, 4))))
        vertices = relative_vertices(language, ())
        bound = max_core_coefficient(language, book, ())
        self.assertLessEqual(bound.working,
                             core_upper_bound(vertices, endorsement_rows(language,
                                                                         book)))

    def test_both_bracket_endpoints_are_verified(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),
                        Endorsement("e:B", (Q(0), Q(1), Q(0)), Q(1, 4))))
        bound = max_core_coefficient(language, book, ())
        self.assertTrue(clipping_adapter_admits(language, book, (), bound.working))
        if bound.failing is not None:
            self.assertFalse(
                clipping_adapter_admits(language, book, (), bound.failing))


class ClippingAdapterTests(unittest.TestCase):
    """P1 as a program with a declared branch."""

    def test_an_admissible_reference_really_admits_the_coefficient(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),))
        reference = core_admissible_reference(language, book, (), Q(1, 4))
        self.assertIsNotNone(reference)
        self.assertTrue(relative_core_holds(language, book, (), reference, Q(1, 4)))

    def test_emptiness_is_a_declared_branch_not_a_silent_failure(self):
        language = Language(("w1", "w2"), {"A": ("w1",)})
        book = Book(1, (Endorsement("e", (Q(1), Q(0)), Q(1, 2)),))
        admission = core_admission(language, book, (), Q(9, 10), date=0)
        self.assertFalse(admission.admitted)
        self.assertEqual(admission.consequence, QUARANTINE_OF_FORCE)

    def test_the_adapter_never_quietly_lowers_the_declared_minimum(self):
        language = Language(("w1", "w2"), {"A": ("w1",)})
        book = Book(1, (Endorsement("e", (Q(1), Q(0)), Q(1, 2)),))
        admission = core_admission(language, book, (), Q(9, 10))
        self.assertEqual(admission.theta_minimum, Q(9, 10))
        self.assertIsNone(admission.reference)


class TransportTests(unittest.TestCase):
    """The relative reading transports across an independent pin."""

    def setUp(self):
        witness = dependent_pin_failure()
        self.language = witness["language"]
        self.book = witness["book"]
        self.reference = witness["reference"]
        self.dependent = witness["dependent"]
        self.independent = witness["independent"]

    def test_independence_is_the_incumbent_confirming_the_pin(self):
        self.assertTrue(pin_is_independent(self.language, self.reference,
                                           self.independent))
        self.assertFalse(pin_is_independent(self.language, self.reference,
                                            self.dependent))

    def test_transport_holds_across_the_independent_pin(self):
        self.assertTrue(relative_core_holds(self.language, self.book, (),
                                            self.reference, Q(1, 2)))
        self.assertTrue(transport_lemma(self.language, self.book, (),
                                        self.reference, Q(1, 2), self.independent))

    def test_transport_is_stated_only_for_confirmed_pins(self):
        with self.assertRaises(ValueError):
            transport_lemma(self.language, self.book, (), self.reference, Q(1, 2),
                            self.dependent)

    def test_the_dependent_pin_destroys_what_the_independent_one_keeps(self):
        before = max_core_coefficient(self.language, self.book, ())
        after_dependent = max_core_coefficient(self.language, self.book,
                                               (self.dependent,))
        after_independent = max_core_coefficient(self.language, self.book,
                                                 (self.independent,))
        self.assertEqual(before.working, Q(1, 2))
        self.assertEqual(after_independent.working, Q(1, 2))
        self.assertEqual(after_dependent.working, Q(0))
        self.assertTrue(after_dependent.exact,
                        "every positive coefficient fails, exactly")

    def test_the_effect_of_one_pin_is_classified(self):
        effect = pin_effect(self.language, self.book, (), self.reference, Q(1, 2),
                            self.dependent)
        self.assertFalse(effect.independent)
        self.assertTrue(effect.collapsed)
        self.assertIsNone(effect.transported)


class SearchTests(unittest.TestCase):
    """Exact-rational sweep over small instances."""

    def test_every_independent_pin_transports(self):
        report = small_instance_search()
        self.assertGreater(report["independent_total"], 0)
        self.assertEqual(report["independent_transport"], report["independent_total"])

    def test_dependent_pins_are_where_the_coefficient_is_lost(self):
        report = small_instance_search()
        self.assertGreater(report["dependent_total"], 0)
        self.assertTrue(report["dependent_collapsed"],
                        "some dependent pin voids the coefficient outright")
        self.assertTrue(report["dependent_reduced"],
                        "some dependent pin lowers it without voiding it")
        for _, _, _, before, after in report["dependent_reduced"]:
            self.assertLess(after, before)


class TrajectoryTests(unittest.TestCase):
    """The coefficient as pins accumulate.  Finite-instance evidence only."""

    def test_a_declared_minimum_can_survive_a_trajectory(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 4)),))
        report = accumulate_pins(language, book,
                                 (SettledFact("B", Q(0)), SettledFact("C", Q(0))),
                                 Q(1, 8))
        self.assertTrue(report.survives)
        self.assertGreaterEqual(report.minimum, Q(1, 8))
        self.assertEqual(len(report.coefficients), 3)

    def test_a_declared_minimum_can_fail_on_a_trajectory(self):
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 2)),))
        report = accumulate_pins(language, book, (SettledFact("B", Q(1, 2)),),
                                 Q(1, 8))
        self.assertFalse(report.survives)
        self.assertEqual(report.minimum, Q(0))

    def test_the_report_makes_no_asymptotic_claim(self):
        """The recorded minimum is over the searched trajectory, and finite."""
        language = Language(("w1", "w2", "w3"),
                            {"A": ("w1",), "B": ("w2",), "C": ("w3",)})
        book = Book(1, (Endorsement("e:A", (Q(1), Q(0), Q(0)), Q(1, 4)),))
        pins = (SettledFact("B", Q(0)),)
        report = accumulate_pins(language, book, pins, Q(1, 8))
        self.assertEqual(len(report.stages), len(pins))
        self.assertEqual(report.minimum, min(report.coefficients))


if __name__ == "__main__":
    unittest.main()
