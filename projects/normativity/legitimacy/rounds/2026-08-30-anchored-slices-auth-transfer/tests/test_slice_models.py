import unittest

from slice_models import (
    ClaimedTransfer,
    Interpretation,
    LocalEra,
    M3,
    RevisionAccount,
    Slice,
    SliceState,
    admit,
    commuting_transport,
    compose,
    growing_anchor_indistinguishable,
    late_accretion_on_frontier,
)


class SliceAuthenticationHostileCases(unittest.TestCase):
    def test_01_same_matter_gets_new_criticism_later(self):
        a = Slice("a", "m", 3, frozenset({"crit-a"}))
        b = Slice("b", "m", 20, frozenset({"crit-b"}))
        self.assertTrue(admit(a, 3, frozenset({"q"}), {"q": a.anchor}).valid())
        self.assertTrue(admit(b, 20, frozenset({"q"}), {"q": b.anchor}).valid())

    def test_02_new_criticism_is_not_translation(self):
        old = Interpretation("old", "p", {"c": frozenset({"a"})})
        new = Interpretation("new", "p", {"c2": frozenset({"a", "b"})})
        claim = ClaimedTransfer(("c",), ("c2",), frozenset({"a"}), {"c2": frozenset({"a"})})
        self.assertTrue(claim.accounting_valid())
        self.assertFalse(claim.authenticated(old, new))

    def test_03_weakening_requires_disposition(self):
        bad = RevisionAccount(frozenset({"a", "b"}), frozenset({"a"}), frozenset({"a"}))
        good = RevisionAccount(
            frozenset({"a", "b"}), frozenset({"a"}), frozenset({"a"}),
            frozenset({"b"}), True,
        )
        self.assertFalse(bad.valid())
        self.assertTrue(good.valid())

    def test_04_strengthening_requires_fresh_slice(self):
        bad = RevisionAccount(
            frozenset({"a"}), frozenset({"a", "b"}), frozenset({"a"}),
            increment=frozenset({"b"}),
        )
        increment = Slice("inc", "m", 7, frozenset({"b"}))
        good = RevisionAccount(
            bad.old, bad.successor, bad.retained,
            increment=frozenset({"b"}), fresh_slice=increment,
        )
        self.assertFalse(bad.valid())
        self.assertTrue(good.valid())

    def test_05_exact_semantic_translation(self):
        old = Interpretation("old", "p", {"x": frozenset({"a"})})
        new = Interpretation("new", "p", {"y": frozenset({"a"})})
        t = ClaimedTransfer(("x",), ("y",), frozenset({"a"}), {"y": frozenset({"a"})})
        self.assertTrue(t.authenticated(old, new))

    def test_06_split_translation_preserves_joint_meaning(self):
        old = Interpretation("old", "p", {"x": frozenset({"a", "b"})})
        new = Interpretation("new", "p", {"ya": frozenset({"a"}), "yb": frozenset({"b"})})
        t = ClaimedTransfer(
            ("x",), ("ya", "yb"), old.meanings["x"],
            {"ya": new.meanings["ya"], "yb": new.meanings["yb"]},
        )
        self.assertTrue(t.authenticated(old, new))

    def test_07_merge_translation_preserves_parent_meanings(self):
        old = Interpretation("old", "p", {"xa": frozenset({"a"}), "xb": frozenset({"b"})})
        new = Interpretation("new", "p", {"y": frozenset({"a", "b"})})
        t = ClaimedTransfer(("xa", "xb"), ("y",), frozenset({"a", "b"}), {"y": new.meanings["y"]})
        self.assertTrue(t.authenticated(old, new))

    def test_08_locally_valid_looking_translations_do_not_compose(self):
        e0 = Interpretation("e0", "p0", {"x": frozenset({"a"})})
        e1a = Interpretation("e1a", "p1", {"y": frozenset({"a"})})
        e1b = Interpretation("e1b", "p2", {"y": frozenset({"b"})})
        e2 = Interpretation("e2", "p2", {"z": frozenset({"b"})})
        t1 = ClaimedTransfer(("x",), ("y",), frozenset({"a"}), {"y": frozenset({"a"})})
        t2 = ClaimedTransfer(("y",), ("z",), frozenset({"b"}), {"z": frozenset({"b"})})
        self.assertTrue(t1.authenticated(e0, e1a))
        self.assertTrue(t2.authenticated(e1b, e2))
        self.assertIsNone(compose(t1, t2, e0, e1a, e1b, e2))

    def test_09_accounting_valid_but_semantically_bogus(self):
        old = Interpretation("old", "p", {"x": frozenset({"a"})})
        new = Interpretation("new", "p", {"y": frozenset({"b"})})
        t = ClaimedTransfer(("x",), ("y",), frozenset({"a"}), {"y": frozenset({"a"})})
        self.assertTrue(t.accounting_valid())
        self.assertFalse(t.authenticated(old, new))

    def test_10_coverage_target_same_applicability_weakened(self):
        old = Interpretation("old", "coverage", {"c": frozenset({"target:T", "applies:A+B"})})
        new = Interpretation("new", "coverage", {"c2": frozenset({"target:T", "applies:A"})})
        t = ClaimedTransfer(("c",), ("c2",), old.meanings["c"], {"c2": old.meanings["c"]})
        self.assertFalse(t.authenticated(old, new))

    def test_11_coverage_applicability_same_target_changed(self):
        old = Interpretation("old", "coverage", {"c": frozenset({"target:T", "applies:A"})})
        new = Interpretation("new", "coverage", {"c2": frozenset({"target:U", "applies:A"})})
        t = ClaimedTransfer(("c",), ("c2",), old.meanings["c"], {"c2": old.meanings["c"]})
        self.assertFalse(t.authenticated(old, new))

    def test_12_reason_content_same_answer_mode_changed(self):
        old = Interpretation("old", "reason", {"r": frozenset({"claim:C", "mode:answer"})})
        new = Interpretation("new", "reason", {"r2": frozenset({"claim:C", "mode:ignore"})})
        t = ClaimedTransfer(("r",), ("r2",), old.meanings["r"], {"r2": old.meanings["r"]})
        self.assertFalse(t.authenticated(old, new))

    def test_13_answerability_preserved_without_progress_comparability(self):
        old = Interpretation("old", "reason", {"r": frozenset({"claim:C", "mode:repair"})})
        new = Interpretation("new", "reason", {"r2": old.meanings["r"]})
        t = ClaimedTransfer(("r",), ("r2",), old.meanings["r"], {"r2": new.meanings["r2"]})
        self.assertTrue(t.authenticated(old, new))
        old_margin, new_margin = "1/3", "unknown"
        self.assertNotEqual(old_margin, new_margin)

    def test_14_ontology_change_commutes_to_anchor(self):
        old = LocalEra("old", {"x": frozenset({"red"})}, {"red": frozenset({"risk"})})
        new = LocalEra("new", {"y": frozenset({"rouge"})}, {"rouge": frozenset({"risk"})})
        self.assertTrue(commuting_transport(old, "x", new, "y"))

    def test_15_ontology_change_without_transport_fails(self):
        old = LocalEra("old", {"x": frozenset({"red"})}, {"red": frozenset({"risk"})})
        new = LocalEra("new", {"y": frozenset({"rouge"})}, {"rouge": frozenset({"reward"})})
        self.assertFalse(commuting_transport(old, "x", new, "y"))

    def test_16_external_fact_changes_applicability_via_disposition(self):
        account = RevisionAccount(
            frozenset({"applies"}), frozenset(), frozenset(),
            disposed=frozenset({"applies"}), disposition_authorized=True,
        )
        self.assertTrue(account.valid())

    def test_17_evaluator_revision_is_not_factual_change(self):
        account = RevisionAccount(frozenset({"applies"}), frozenset(), frozenset())
        self.assertFalse(account.valid())

    def test_18_late_accretion_on_split_frontier(self):
        a = Slice("a", "m", 3, frozenset({"a1", "a2"}))
        old = SliceState(a, 20, frozenset({"q1", "q2"}), {"q1": frozenset({"a1"}), "q2": frozenset({"a2"})})
        b = Slice("b", "m", 20, frozenset({"b"}))
        old2, new = late_accretion_on_frontier(old, b, 20, "q2")
        self.assertTrue(old2.valid() and new.valid())

    def test_19_late_accretion_on_merged_multi_matter_issue(self):
        a = Slice("a", "m1", 1, frozenset({"a"}))
        b = Slice("b", "m2", 1, frozenset({"b"}))
        c = Slice("c", "m1", 9, frozenset({"c"}))
        live = frozenset({"merged"})
        self.assertTrue(admit(a, 9, live, {"merged": a.anchor}).valid())
        self.assertTrue(admit(b, 9, live, {"merged": b.anchor}).valid())
        self.assertTrue(admit(c, 9, live, {"merged": c.anchor}).valid())

    def test_20_growing_anchor_without_deltas_loses_origin(self):
        self.assertTrue(growing_anchor_indistinguishable())
        late = Slice("b", "m", 20, frozenset({"b"}))
        early = Slice("b", "m", 3, frozenset({"b"}))
        self.assertNotEqual(late.born, early.born)

    def test_join_semilattice_needs_no_distributivity_or_atoms(self):
        self.assertEqual(M3.join("a", "b"), M3.ONE)
        self.assertEqual(M3.join(M3.join("a", "b"), "c"), M3.ONE)
        relational = Slice("rel", "m", 1, frozenset({"answer-a-in-light-of-b"}))
        self.assertTrue(admit(relational, 1, frozenset({"q"}), {"q": relational.anchor}).valid())


if __name__ == "__main__":
    unittest.main()
