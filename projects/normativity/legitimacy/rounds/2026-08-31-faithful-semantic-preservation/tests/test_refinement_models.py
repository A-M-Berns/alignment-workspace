import unittest

from refinement_models import (
    Admission,
    Allocation,
    SemanticBatch,
    SliceSemantics,
    activated_due,
    bridges_compose,
    powerset,
)


A = frozenset({"a"})
B = frozenset({"b"})
AB = A | B
EMPTY = frozenset()


class HostileRefinementCases(unittest.TestCase):
    def test_01_live_issue_silently_loses_load(self):
        before = Allocation(frozenset({"q"}), {"q": A})
        after = Allocation(frozenset({"q"}), {"q": EMPTY})
        batch = SemanticBatch(before, after, frozenset(), frozenset())
        self.assertFalse(batch.valid())

    def test_02_live_issue_silently_changes_a_to_b(self):
        before = Allocation(frozenset({"q"}), {"q": A})
        after = Allocation(frozenset({"q"}), {"q": B})
        batch = SemanticBatch(before, after, frozenset(), frozenset())
        self.assertFalse(batch.valid())

    def test_03_in_place_exact_translation(self):
        before = Allocation(frozenset({"q"}), {"q": A})
        after = Allocation(frozenset({"q"}), {"q": A})
        batch = SemanticBatch(before, after, frozenset({"q"}), frozenset({"q"}))
        self.assertTrue(batch.valid())

    def test_04_in_place_weakening_with_disposition(self):
        before = Allocation(frozenset({"q"}), {"q": AB})
        after = Allocation(frozenset({"q"}), {"q": A})
        batch = SemanticBatch(
            before, after, frozenset({"q"}), frozenset({"q"}),
            disposed=B, disposition_authorized=True,
        )
        self.assertTrue(batch.valid())

    def test_05_in_place_strengthening_uses_fresh_slice(self):
        old = SemanticBatch(
            Allocation(frozenset({"q"}), {"q": A}),
            Allocation(frozenset({"q"}), {"q": A}),
            frozenset({"q"}), frozenset({"q"}),
        )
        increment = Admission(True, frozenset({"rule"}), frozenset({"rule"}), True)
        self.assertTrue(old.valid() and increment.valid())

    def test_06_join_map_hides_strengthening(self):
        sem = SliceSemantics({"a": A, "b": EMPTY}, frozenset({"a", "b"}), powerset(("a", "b")))
        self.assertTrue(sem.join_preserving())
        self.assertEqual(sem.anchor(A), sem.anchor(AB))
        self.assertFalse(sem.adequate())

    def test_07_lossy_map_hides_weakening(self):
        sem = SliceSemantics({"a": A, "b": EMPTY}, frozenset({"a", "b"}), powerset(("a", "b")))
        self.assertEqual(sem.anchor(AB), sem.anchor(A))
        self.assertFalse(sem.order_reflecting())

    def test_08_noninjective_but_slice_faithful(self):
        sem = SliceSemantics(
            {"a": A, "cosmetic-red": EMPTY, "cosmetic-blue": EMPTY},
            frozenset({"a"}), powerset(("a", "cosmetic-red", "cosmetic-blue")),
        )
        self.assertEqual(sem.anchor(frozenset({"cosmetic-red"})), EMPTY)
        self.assertEqual(sem.anchor(frozenset({"cosmetic-blue"})), EMPTY)
        self.assertTrue(sem.adequate())

    def test_09_sound_but_vacuous_constant_observation(self):
        sem = SliceSemantics({"a": EMPTY, "b": EMPTY}, frozenset({"a", "b"}), powerset(("a", "b")))
        self.assertTrue(sem.join_preserving())
        self.assertFalse(sem.equality_reflecting())

    def test_10_order_preserving_not_order_reflecting(self):
        sem = SliceSemantics({"a": A, "b": EMPTY}, frozenset({"a", "b"}), powerset(("a", "b")))
        self.assertTrue(sem.join_preserving())
        self.assertFalse(sem.order_reflecting())

    def test_11_quotient_relative_faithful_map(self):
        sem = SliceSemantics(
            {"claim": A, "font1": EMPTY, "font2": EMPTY},
            frozenset({"claim"}), powerset(("claim", "font1", "font2")),
        )
        self.assertTrue(sem.adequate())

    def test_12_faithful_bridges_compose(self):
        one = SliceSemantics({"a": A}, frozenset({"a"}), powerset(("a",)))
        two = SliceSemantics({"a": A}, frozenset({"a"}), powerset(("a",)))
        self.assertTrue(bridges_compose(one, two, (EMPTY, A)))

    def test_13_quotient_mismatch_breaks_composition(self):
        one = SliceSemantics({"a": A}, frozenset({"a"}), powerset(("a",)))
        two = SliceSemantics({"a": A}, frozenset({"a"}), powerset(("a",)))
        self.assertFalse(bridges_compose(one, two, (EMPTY, A), quotient_compatible=False))

    def test_14_many_era_erosion_is_caught(self):
        eras = [
            SliceSemantics({"a": A, "b": B}, frozenset({"a", "b"}), powerset(("a", "b"))),
            SliceSemantics({"a": A, "b": B}, frozenset({"a", "b"}), powerset(("a", "b"))),
            SliceSemantics({"a": A, "b": EMPTY}, frozenset({"a", "b"}), powerset(("a", "b"))),
        ]
        self.assertTrue(eras[0].adequate() and eras[1].adequate())
        self.assertFalse(eras[2].adequate())

    def test_15_semantics_valid_admission_ungrounded(self):
        self.assertFalse(Admission(True, frozenset(), frozenset({"rule"}), True).valid())

    def test_16_grounded_admission_malformed_semantics(self):
        self.assertFalse(Admission(False, frozenset({"rule"}), frozenset({"rule"}), True).valid())

    def test_17_new_fact_activates_grounded_due(self):
        admission = activated_due(False, True, True, "conditional-rule", frozenset({"conditional-rule"}), True)
        self.assertTrue(admission.valid())

    def test_18_evaluator_invents_convenient_slice(self):
        self.assertFalse(Admission(True, frozenset({"evaluator"}), frozenset(), True).valid())

    def test_19_coverage_weakening_hidden_by_coarse_semantics(self):
        sem = SliceSemantics(
            {"target": A, "applicability": EMPTY},
            frozenset({"target", "applicability"}),
            powerset(("target", "applicability")),
        )
        self.assertFalse(sem.adequate())

    def test_20_reason_answer_mode_laundering(self):
        sem = SliceSemantics(
            {"claim": A, "supply-evidence": EMPTY, "acknowledge": EMPTY},
            frozenset({"claim", "supply-evidence", "acknowledge"}),
            powerset(("claim", "supply-evidence", "acknowledge")),
        )
        self.assertFalse(sem.equality_reflecting())

    def test_21_global_injectivity_is_too_strong(self):
        sem = SliceSemantics(
            {"claim": A, "irrelevant1": EMPTY, "irrelevant2": EMPTY},
            frozenset({"claim"}), powerset(("claim", "irrelevant1", "irrelevant2")),
        )
        self.assertTrue(sem.adequate())
        self.assertEqual(sem.anchor(frozenset({"irrelevant1"})), sem.anchor(frozenset({"irrelevant2"})))

    def test_22_order_reflection_is_necessary_for_classification(self):
        sem = SliceSemantics({"a": A, "b": EMPTY}, frozenset({"a", "b"}), powerset(("a", "b")))
        self.assertEqual(sem.anchor(AB), sem.anchor(A))
        self.assertFalse(sem.order_reflecting())


if __name__ == "__main__":
    unittest.main()
