"""Part I fixtures: repairs to the PR #48 reason-state representation."""
from __future__ import annotations

import dataclasses
import unittest

from reason_state import (
    App,
    Atom,
    Incomp,
    Inst,
    Neg,
    ReasonState,
    Receipt,
    case_view,
    conflict,
    criticizable,
    enabled,
    incompatible,
    joint_conflicts,
    neg,
    reasons,
    rebuts,
)


class TestCanonicalNegation(unittest.TestCase):
    """Part I.3: the involution holds by construction, not by convention."""

    def test_double_negation_is_unconstructible(self):
        with self.assertRaises(TypeError):
            Neg(Neg(Atom("p")))

    def test_neg_is_involutive(self):
        p = Atom("p")
        self.assertEqual(neg(neg(p)), p)
        a = App("sigma", "c", 3)
        self.assertEqual(neg(neg(a)), a)

    def test_floor_contradiction_is_stance_independent(self):
        p = Atom("p")
        self.assertTrue(conflict(frozenset({p, neg(p)}), frozenset()))


class TestNaryConflict(unittest.TestCase):
    """Part I.1 and dispatch fixtures 1 and 13: Incomp(S) binds the set, not
    its pairs."""

    def setUp(self):
        self.a, self.b, self.c = Atom("a"), Atom("b"), Atom("c")
        self.triple = Incomp(frozenset({self.a, self.b, self.c}))
        self.stance = frozenset({self.triple})

    def test_incomp_needs_two_members(self):
        with self.assertRaises(ValueError):
            Incomp(frozenset({Atom("a")}))

    def test_ternary_conflict_with_pairwise_compatibility(self):
        self.assertTrue(conflict(frozenset({self.a, self.b, self.c}), self.stance))
        self.assertFalse(incompatible(self.a, self.b, self.stance))
        self.assertFalse(incompatible(self.a, self.c, self.stance))
        self.assertFalse(incompatible(self.b, self.c, self.stance))

    def test_overlapping_conflict_sets(self):
        d = Atom("d")
        stance = frozenset(
            {Incomp(frozenset({self.a, self.b})), Incomp(frozenset({self.b, self.c, d}))}
        )
        self.assertTrue(conflict(frozenset({self.a, self.b}), stance))
        self.assertFalse(conflict(frozenset({self.b, self.c}), stance))
        self.assertTrue(conflict(frozenset({self.b, self.c, d}), stance))
        self.assertTrue(conflict(frozenset({self.a, self.b, self.c, d}), stance))

    def test_learned_incompatibility_later_defeated(self):
        members = frozenset({self.a, self.b, self.c})
        self.assertTrue(conflict(members, self.stance))
        self.assertFalse(conflict(members, frozenset()))

    def test_violating_stance_is_representable_but_criticizable(self):
        stance = frozenset({self.a, self.b, self.c, self.triple})
        self.assertTrue(criticizable(stance))
        state = ReasonState()
        state.mint("e", {self.a}, Atom("z"), at=0)
        self.assertTrue(enabled(state, "e", stance, frozenset()))

    def test_practical_nary_conflict_exposed_only_jointly(self):
        state = ReasonState()
        targets = [Atom(f"respond:m{i}") for i in range(3)]
        for i, t in enumerate(targets):
            state.mint(f"r{i}", {Atom(f"invited-m{i}")}, t, at=0)
        stance = frozenset(
            {Atom("invited-m0"), Atom("invited-m1"), Atom("invited-m2"),
             Incomp(frozenset(targets))}
        )
        self.assertTrue(joint_conflicts(state, ("r0", "r1", "r2"), stance, frozenset()))
        self.assertFalse(rebuts(state, "r0", "r1", stance, frozenset()))
        self.assertFalse(rebuts(state, "r1", "r2", stance, frozenset()))


class TestCaseViews(unittest.TestCase):
    """Part I.2 and dispatch fixtures 2 and 3: staged views are determined by
    the case-restricted arrival prefix."""

    def setUp(self):
        self.arrivals = {"r1": 1, "r2": 9}
        self.provenance = frozenset({("c", "r1"), ("c", "r2"), ("c2", "r1")})

    def test_views_are_prefix_determined_and_monotone(self):
        self.assertEqual(case_view("c", 2, self.arrivals, self.provenance), frozenset({"r1"}))
        self.assertEqual(
            case_view("c", 9, self.arrivals, self.provenance), frozenset({"r1", "r2"})
        )

    def test_equal_case_restriction_gives_equal_views(self):
        # A different global history — extra receipts on other cases — with
        # the same c-restricted prefix induces the same c@n view.
        other_arrivals = {"r1": 1, "r2": 9, "r3": 1}
        other_provenance = self.provenance | {("c2", "r3")}
        self.assertEqual(
            case_view("c", 2, self.arrivals, self.provenance),
            case_view("c", 2, other_arrivals, other_provenance),
        )

    def test_delayed_receipt_grounds_correction_without_view_rewrite(self):
        # r2 arrives at stage 9 bearing on how things stood at stage 2. The
        # stage-2 view is unchanged; the correction is an ordinary reason
        # against the old staged claim.
        self.assertNotIn("r2", case_view("c", 2, self.arrivals, self.provenance))
        state = ReasonState()
        state.mint(
            "correct",
            {Receipt("r2"), App("late-evidence-defeat", "c", 9)},
            neg(App("sigma", "c", 2)),
            at=9,
            applied_as={("late-evidence-defeat", "c", 9)},
        )
        stance = frozenset({App("late-evidence-defeat", "c", 9)})
        self.assertEqual(
            reasons(state, neg(App("sigma", "c", 2)), stance, frozenset({"r2"})),
            ("correct",),
        )

    def test_corrected_belief_versus_changed_situation(self):
        early, late = App("sigma", "c", 3), App("sigma", "c", 4)
        self.assertFalse(conflict(frozenset({early, neg(late)}), frozenset()))
        self.assertTrue(conflict(frozenset({early, neg(early)}), frozenset()))


class TestApplicabilityInSource(unittest.TestCase):
    """Part I.4: the convention becomes enforced well-formedness over
    constitutive instantiation declarations."""

    def test_declared_instantiation_requires_the_app_source(self):
        state = ReasonState()
        with self.assertRaises(ValueError):
            state.mint(
                "e",
                {Atom("bird")},
                Atom("flies"),
                at=1,
                applied_as={("sigma", "c", 1)},
            )
        state.mint(
            "e",
            {Atom("bird"), App("sigma", "c", 1)},
            Atom("flies"),
            at=1,
            applied_as={("sigma", "c", 1)},
        )

    def test_multiple_schemas_declare_multiple_apps(self):
        state = ReasonState()
        occ = state.mint(
            "e",
            {Atom("p"), App("sigma", "c", 1), App("tau", "c", 1)},
            Atom("q"),
            at=1,
            applied_as={("sigma", "c", 1), ("tau", "c", 1)},
        )
        # A joint application depends on both applicability judgments;
        # independence requires minting separate occurrences.
        stance = frozenset({Atom("p"), App("sigma", "c", 1)})
        self.assertFalse(enabled(state, "e", stance, frozenset()))
        self.assertEqual(len(occ.applied_as), 2)

    def test_undeclared_occurrences_are_permitted(self):
        # A seed or brute reason instantiates nothing; requiring declaration
        # everywhere would be too strong. Whether a cited basis may contain
        # undeclared occurrences is record-side policy.
        state = ReasonState()
        state.mint("seed-reason", {Atom("induction")}, Atom("q"), at=0)

    def test_persistence_schema_declares_its_own_applicability(self):
        state = ReasonState()
        state.mint(
            "persist",
            {App("sigma", "c", 3), App("persistence", "c", 4)},
            App("sigma", "c", 4),
            at=4,
            applied_as={("persistence", "c", 4)},
        )
        stance = frozenset({App("sigma", "c", 3), App("persistence", "c", 4)})
        self.assertEqual(reasons(state, App("sigma", "c", 4), stance, frozenset()), ("persist",))

    def test_persistence_justified_in_one_case_not_another(self):
        # Dispatch fixture 14: the same persistence schema carries sigma
        # forward at c1, where the learner adopts its applicability, and not
        # at c2, where the learner declines. No reason against App at c2
        # appears; the carry simply is not licensed there.
        state = ReasonState()
        for case in ("c1", "c2"):
            state.mint(
                f"persist-{case}",
                {App("sigma", case, 0), App("persistence", case, 1)},
                App("sigma", case, 1),
                at=1,
                applied_as={("persistence", case, 1)},
            )
        stance = frozenset(
            {App("sigma", "c1", 0), App("sigma", "c2", 0), App("persistence", "c1", 1)}
        )
        self.assertEqual(reasons(state, App("sigma", "c1", 1), stance, frozenset()), ("persist-c1",))
        self.assertEqual(reasons(state, App("sigma", "c2", 1), stance, frozenset()), ())
        self.assertEqual(reasons(state, neg(App("sigma", "c2", 1)), stance, frozenset()), ())

    def test_reclassification_cannot_rewrite_declarations(self):
        state = ReasonState()
        occ = state.mint(
            "e",
            {Atom("p"), App("sigma", "c", 1)},
            Atom("q"),
            at=1,
            applied_as={("sigma", "c", 1)},
        )
        with self.assertRaises(dataclasses.FrozenInstanceError):
            occ.applied_as = frozenset({("tau", "c", 1)})
        with self.assertRaises(dataclasses.FrozenInstanceError):
            occ.sources = frozenset()

    def test_cross_cutting_organization_claims_coexist(self):
        # Dispatch fixture 9: Inst claims for several schemas stand together
        # and never touch enabledness.
        state = ReasonState()
        occ = state.mint(
            "e",
            {Atom("p"), App("sigma", "c", 1)},
            Atom("q"),
            at=1,
            applied_as={("sigma", "c", 1)},
        )
        stance = frozenset(
            {Atom("p"), App("sigma", "c", 1), Inst("e", "sigma"), Inst("e", "tau")}
        )
        self.assertTrue(enabled(state, "e", stance, frozenset()))
        without = stance - {Inst("e", "sigma"), Inst("e", "tau")}
        self.assertTrue(enabled(state, "e", without, frozenset()))
        self.assertEqual(occ.applied_as, frozenset({("sigma", "c", 1)}))


if __name__ == "__main__":
    unittest.main()
