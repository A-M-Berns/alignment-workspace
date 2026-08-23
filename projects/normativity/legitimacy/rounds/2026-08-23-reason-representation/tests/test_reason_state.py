"""Adversarial prosecution of the reason-state narrow waist.

Each test class runs one investigation from the round prompt against the
finite reference model. The suite is written to fail if identical occurrences
collapse, schemas partition, undercutting implies the opposite conclusion, the
substrate resolves conflict, history is overwritten, case and docket collapse,
procedural provenance is treated as evidence, or staging cannot distinguish
changing-world from corrected-belief histories.
"""
from __future__ import annotations

import unittest

from reason_state import (
    App,
    Atom,
    Incomp,
    Inst,
    Practice,
    ReasonState,
    Receipt,
    Reliance,
    bearing,
    dependents,
    enabled,
    incompatible,
    labels_by_enumeration,
    labels_by_propagation,
    lost_basis,
    neg,
    nogoods,
    reasons,
    rebuts,
    support_closure,
    undercuts,
)


class TestStructuralIdentity(unittest.TestCase):
    """Example 9 and the append-only discipline."""

    def test_equal_source_and_target_do_not_identify_occurrences(self):
        state = ReasonState()
        src = frozenset({Atom("testimony"), App("sigma", "c1", 0)})
        tgt = Atom("liable")
        e1 = state.mint("e1", src, tgt)
        e2 = state.mint("e2", src, tgt)
        self.assertNotEqual(e1.ident, e2.ident)
        self.assertEqual(len(state.occurrences()), 2)
        stance = frozenset(src)
        self.assertEqual(set(reasons(state, tgt, stance, frozenset())), {"e1", "e2"})

    def test_identifier_reuse_is_refused(self):
        state = ReasonState()
        state.mint("e1", {Atom("p")}, Atom("q"))
        with self.assertRaises(ValueError):
            state.mint("e1", {Atom("p")}, Atom("q"))

    def test_receipts_cannot_be_targets(self):
        state = ReasonState()
        with self.assertRaises(TypeError):
            state.mint("e1", {Atom("p")}, Receipt("r1"))

    def test_receipt_sources_gate_on_transcript_not_stance(self):
        state = ReasonState()
        state.mint("e1", {Receipt("r1"), Atom("reading-indicates-fault")}, Atom("fault"))
        stance = frozenset({Atom("reading-indicates-fault")})
        self.assertFalse(enabled(state, "e1", stance, frozenset()))
        self.assertTrue(enabled(state, "e1", stance, frozenset({"r1"})))


class TestOrdinarySchemaApplication(unittest.TestCase):
    """Example 1: historical instances support applicability to a new case."""

    def setUp(self):
        self.state = ReasonState()
        self.state.add_schema("sigma")
        # Historical occurrences in settled cases, recorded as instances.
        self.state.mint("h1", {Atom("bird:c1"), App("sigma", "c1", 0)}, Atom("flies:c1"))
        self.state.mint("h2", {Atom("bird:c2"), App("sigma", "c2", 0)}, Atom("flies:c2"))
        # A schema-level reason: the historical classification supports
        # applicability to the new case. Its sources are Inst claims — schema
        # organization is ordinary content.
        self.state.mint(
            "gen",
            {Inst("h1", "sigma"), Inst("h2", "sigma"), Atom("bird:c3")},
            App("sigma", "c3", 5),
        )
        # The new application, carrying its own applicability in its sources.
        self.state.mint(
            "a3", {Atom("bird:c3"), App("sigma", "c3", 5)}, Atom("flies:c3")
        )

    def test_application_bears_once_applicability_is_adopted(self):
        stance = frozenset(
            {Inst("h1", "sigma"), Inst("h2", "sigma"), Atom("bird:c3")}
        )
        self.assertEqual(reasons(self.state, App("sigma", "c3", 5), stance, frozenset()), ("gen",))
        self.assertEqual(reasons(self.state, Atom("flies:c3"), stance, frozenset()), ())
        adopted = stance | {App("sigma", "c3", 5)}
        self.assertEqual(reasons(self.state, Atom("flies:c3"), adopted, frozenset()), ("a3",))

    def test_adoption_is_the_learner_move_not_the_substrate(self):
        stance = frozenset(
            {Inst("h1", "sigma"), Inst("h2", "sigma"), Atom("bird:c3")}
        )
        borne = bearing(self.state, stance, frozenset())
        self.assertIn(App("sigma", "c3", 5), borne)
        self.assertNotIn(App("sigma", "c3", 5), stance)


class TestUndercutting(unittest.TestCase):
    """Examples 2 and 3: reified applicability closes under nested attack."""

    def setUp(self):
        self.state = ReasonState()
        # Base application at case c, stage 4.
        self.state.mint(
            "base", {Atom("promised"), App("keep", "c", 4)}, Atom("do:keep-promise")
        )
        # Undercutter: an ordinary reason for not-App(keep, c@4), itself an
        # application of an emergency schema at its own case view.
        self.state.mint(
            "cut",
            {Atom("emergency"), App("emergency-defeat", "c", 4)},
            neg(App("keep", "c", 4)),
        )
        # Undercutter of the undercutter: the emergency report was staged.
        self.state.mint(
            "cutcut",
            {Atom("report-staged"), App("staged-report-defeat", "c", 4)},
            neg(App("emergency-defeat", "c", 4)),
        )

    def test_undercut_disables_without_supporting_the_opposite(self):
        relied = frozenset({Atom("promised"), App("keep", "c", 4)})
        self.assertTrue(enabled(self.state, "base", relied, frozenset()))
        # The learner registers the undercut by withdrawing the applicability
        # claim; the substrate then reports the base reason disabled.
        revised = frozenset({Atom("promised"), Atom("emergency"), App("emergency-defeat", "c", 4)})
        self.assertFalse(enabled(self.state, "base", revised, frozenset()))
        # No reason for the opposite conclusion appears.
        self.assertEqual(reasons(self.state, neg(Atom("do:keep-promise")), revised, frozenset()), ())

    def test_derived_undercuts_relation(self):
        stance = frozenset({Atom("emergency"), App("emergency-defeat", "c", 4)})
        self.assertTrue(undercuts(self.state, "cut", "base", stance, frozenset()))
        # An undercutter never rebuts: its target is not incompatible with the
        # victim's target.
        self.assertFalse(rebuts(self.state, "cut", "base", stance | {Atom("promised"), App("keep", "c", 4)}, frozenset()))

    def test_nested_reflection_closes_with_ordinary_structure(self):
        stance = frozenset({Atom("report-staged"), App("staged-report-defeat", "c", 4)})
        self.assertTrue(undercuts(self.state, "cutcut", "cut", stance, frozenset()))
        # After the learner withdraws the undercutter's applicability, the
        # undercutter is disabled and the base reason can stand again.
        restored = frozenset(
            {Atom("promised"), App("keep", "c", 4), Atom("emergency"), Atom("report-staged")}
        )
        self.assertFalse(enabled(self.state, "cut", restored, frozenset()))
        self.assertTrue(enabled(self.state, "base", restored, frozenset()))


class TestRebuttalAndConflict(unittest.TestCase):
    """Examples 4 and the incompatibility investigation."""

    def setUp(self):
        self.state = ReasonState()
        self.p = Atom("guilty")
        self.state.mint("for", {Atom("witness-a"), App("testimony", "c", 1)}, self.p)
        self.state.mint("against", {Atom("witness-b"), App("testimony2", "c", 1)}, neg(self.p))
        self.full = frozenset(
            {Atom("witness-a"), Atom("witness-b"), App("testimony", "c", 1), App("testimony2", "c", 1)}
        )

    def test_substrate_exposes_both_sides_and_resolves_nothing(self):
        self.assertEqual(reasons(self.state, self.p, self.full, frozenset()), ("for",))
        self.assertEqual(reasons(self.state, neg(self.p), self.full, frozenset()), ("against",))
        borne = bearing(self.state, self.full, frozenset())
        self.assertIn(self.p, borne)
        self.assertIn(neg(self.p), borne)

    def test_rebuttal_is_derived_from_the_contradiction_floor(self):
        self.assertTrue(rebuts(self.state, "for", "against", self.full, frozenset()))

    def test_substantive_incompatibility_is_adopted_content(self):
        state = ReasonState()
        a = Atom("respond:attend-m1")
        b = Atom("respond:attend-m2")
        state.mint("ra", {Atom("invited-m1")}, a)
        state.mint("rb", {Atom("invited-m2")}, b)
        base = frozenset({Atom("invited-m1"), Atom("invited-m2")})
        # Without the adopted incompatibility, the practical targets do not rebut.
        self.assertFalse(rebuts(state, "ra", "rb", base, frozenset()))
        clash = Incomp(frozenset({a, b}))
        adopted = base | {clash}
        self.assertTrue(rebuts(state, "ra", "rb", adopted, frozenset()))

    def test_a_stance_violating_an_adopted_incompatibility_is_representable(self):
        # Respecting incompatibility is normative response, not substrate
        # grammar: the queries stay total on the criticizable stance.
        a, b = Atom("x"), Atom("y")
        stance = frozenset({a, b, Incomp(frozenset({a, b}))})
        state = ReasonState()
        state.mint("e", {a, b}, Atom("z"))
        self.assertTrue(enabled(state, "e", stance, frozenset()))
        self.assertTrue(incompatible(a, b, stance))


class TestSchemaLearning(unittest.TestCase):
    """Examples 5, 6, 7, 8, 15: organization as ordinary content."""

    def test_cross_cutting_schemas_are_not_a_partition(self):
        state = ReasonState()
        state.add_schema("sigma")
        state.add_schema("tau")
        state.mint("e", {Atom("p"), App("sigma", "c", 0)}, Atom("q"))
        stance = frozenset({Inst("e", "sigma"), Inst("e", "tau")})
        # Both classification claims can stand at once; nothing forces a choice.
        self.assertTrue(incompatible(Inst("e", "sigma"), neg(Inst("e", "sigma")), stance))
        self.assertFalse(incompatible(Inst("e", "sigma"), Inst("e", "tau"), stance))

    def test_reclassification_revises_claims_not_constitutive_sources(self):
        state = ReasonState()
        state.add_schema("sigma")
        state.add_schema("tau")
        occ = state.mint("e", {Atom("p"), App("sigma", "c", 0)}, Atom("q"))
        state.mint(
            "reclass",
            {Atom("expert-review"), App("classification-review", "c2", 7)},
            neg(Inst("e", "sigma")),
        )
        stance = frozenset({Atom("expert-review"), App("classification-review", "c2", 7)})
        self.assertEqual(reasons(state, neg(Inst("e", "sigma")), stance, frozenset()), ("reclass",))
        # The occurrence's constitutive dependence is untouched: it still
        # cites App(sigma, c@0), and only that claim's standing disables it.
        self.assertEqual(occ.claim_sources(), frozenset({Atom("p"), App("sigma", "c", 0)}))

    def test_split_and_merge_are_new_identities_plus_claims(self):
        state = ReasonState()
        for s in ("sigma", "tau1", "tau2"):
            state.add_schema(s)
        state.mint("h1", {Atom("p1"), App("sigma", "c1", 0)}, Atom("q1"))
        state.mint("h2", {Atom("p2"), App("sigma", "c2", 0)}, Atom("q2"))
        # A split is reasons for reclassification into the successors; the old
        # identities and occurrences persist.
        state.mint(
            "split1", {Atom("distinguishing-feature")}, Inst("h1", "tau1")
        )
        state.mint(
            "split2", {Atom("distinguishing-feature")}, Inst("h2", "tau2")
        )
        stance = frozenset({Atom("distinguishing-feature")})
        self.assertEqual(reasons(state, Inst("h1", "tau1"), stance, frozenset()), ("split1",))
        self.assertEqual(reasons(state, Inst("h2", "tau2"), stance, frozenset()), ("split2",))
        self.assertIn("sigma", state.schemas())

    def test_reasons_about_organization_are_ordinary_reasons(self):
        state = ReasonState()
        state.add_schema("sigma")
        state.mint("h1", {Atom("p"), App("sigma", "c1", 0)}, Atom("q"))
        state.mint(
            "org",
            {Atom("statistical-evidence"), App("cluster-analysis", "c9", 3)},
            Inst("h1", "sigma"),
        )
        stance = frozenset({Atom("statistical-evidence"), App("cluster-analysis", "c9", 3)})
        self.assertEqual(reasons(state, Inst("h1", "sigma"), stance, frozenset()), ("org",))


class TestCaseDocketTranscript(unittest.TestCase):
    """Examples 10, 11, 14: provenance is not evidence."""

    def setUp(self):
        self.practice = Practice(
            cases=frozenset({"c1", "c2"}),
            docket_about={"d1": "c1", "d2": "c1", "d3": "c2"},
            open_docket=frozenset({"d1", "d2", "d3"}),
            transcript=frozenset({"r1"}),
            provenance=frozenset({("c1", "r1"), ("c2", "r1")}),
        )
        self.state = ReasonState()

    def test_one_case_several_docket_items(self):
        about_c1 = {d for d, c in self.practice.docket_about.items() if c == "c1"}
        self.assertEqual(about_c1, {"d1", "d2"})

    def test_case_outlives_its_docket(self):
        closed = Practice(
            cases=self.practice.cases,
            docket_about=self.practice.docket_about,
            open_docket=frozenset(),
            transcript=self.practice.transcript,
            provenance=self.practice.provenance,
        )
        self.assertIn("c1", closed.cases)

    def test_one_receipt_two_cases(self):
        touching = {c for c, r in self.practice.provenance if r == "r1"}
        self.assertEqual(touching, {"c1", "c2"})

    def test_procedural_provenance_generates_no_reasons(self):
        # r1 is in the transcript and tied to both cases, yet with no minted
        # occurrence there is nothing it bears on, under any stance.
        every_stance = frozenset({Atom("anything")})
        self.assertEqual(bearing(self.state, every_stance, self.practice.transcript), frozenset())

    def test_uninterpreted_evidence_changes_nothing(self):
        # Example 14: a new receipt arrives, provenance is recorded, and until
        # an occurrence cites it the reason state is silent about it.
        grown = self.practice.transcript | {"r2"}
        self.assertEqual(bearing(self.state, frozenset(), grown), frozenset())


class TestStagedApplicability(unittest.TestCase):
    """Example 12 and the persistence discipline."""

    def test_corrected_belief_versus_changed_world(self):
        early, late = App("sigma", "c", 3), App("sigma", "c", 4)
        # Changed world: applicability held at 3 and lapsed at 4 — jointly
        # coherent.
        changed_world = frozenset({early, neg(late)})
        self.assertFalse(incompatible(early, neg(late), changed_world))
        # Corrected belief: the practice learns it never applied at 3 — this
        # contradicts the earlier staged claim itself.
        self.assertTrue(incompatible(early, neg(early), frozenset()))

    def test_unstaged_applicability_would_collapse_the_two(self):
        # The staged claims are distinct objects; identifying stages
        # identifies them, which is exactly the collapse.
        self.assertNotEqual(App("sigma", "c", 3), App("sigma", "c", 4))

    def test_persistence_is_an_ordinary_defeasible_schema(self):
        state = ReasonState()
        state.mint(
            "persist",
            {App("sigma", "c", 3), App("persistence", "c", 4)},
            App("sigma", "c", 4),
        )
        stance = frozenset({App("sigma", "c", 3), App("persistence", "c", 4)})
        self.assertEqual(reasons(state, App("sigma", "c", 4), stance, frozenset()), ("persist",))
        # Persistence is itself undercuttable: withdrawing its applicability
        # disables the carry, without any reason against App(sigma, c@4).
        volatile = frozenset({App("sigma", "c", 3)})
        self.assertEqual(reasons(state, App("sigma", "c", 4), volatile, frozenset()), ())
        self.assertEqual(reasons(state, neg(App("sigma", "c", 4)), volatile, frozenset()), ())


class TestBasisLossAndReliance(unittest.TestCase):
    """Example 13: reliance is record history, never rewritten."""

    def setUp(self):
        self.state = ReasonState()
        self.state.mint(
            "e", {Atom("witness"), App("testimony", "c", 2), Receipt("r1")}, Atom("liable")
        )
        self.log = (Reliance("undertake-77", "e", 2),)
        self.transcript = frozenset({"r1"})

    def test_undercut_reliance_is_reported(self):
        stance = frozenset({Atom("witness")})  # applicability withdrawn
        self.assertEqual(lost_basis(self.state, self.log, stance, self.transcript), self.log)

    def test_alternative_support_does_not_overwrite_history(self):
        # A fresh, currently valid reason for the same conclusion appears.
        self.state.mint("e2", {Atom("forensics"), App("forensic", "c", 9)}, Atom("liable"))
        stance = frozenset({Atom("witness"), Atom("forensics"), App("forensic", "c", 9)})
        self.assertEqual(reasons(self.state, Atom("liable"), stance, self.transcript), ("e2",))
        # The historical reliance on e still reads as basis-lost: the record
        # relied on e, not on e2.
        self.assertEqual(lost_basis(self.state, self.log, stance, self.transcript), self.log)

    def test_only_the_relied_on_occurrence_is_reported(self):
        self.state.mint(
            "twin", {Atom("witness"), App("testimony", "c", 2), Receipt("r1")}, Atom("liable")
        )
        stance = frozenset({Atom("witness")})
        lost = lost_basis(self.state, self.log, stance, self.transcript)
        self.assertEqual([entry.occurrence for entry in lost], ["e"])


class TestSubstrateNeutrality(unittest.TestCase):
    """Investigation 4: totality, locality, and no hidden adjudication."""

    def test_self_undercutter_is_total_not_a_crash(self):
        state = ReasonState()
        a = App("sigma", "c", 0)
        state.mint("odd", {a}, neg(a))
        # Doyle's odd loop: with the applicability adopted, the occurrence is
        # live and bears against its own enabling claim. The substrate reports
        # exactly that and nothing else.
        stance = frozenset({a})
        self.assertTrue(enabled(state, "odd", stance, frozenset()))
        self.assertEqual(reasons(state, neg(a), stance, frozenset()), ("odd",))
        # Under the stance without the applicability, it is simply disabled.
        self.assertFalse(enabled(state, "odd", frozenset(), frozenset()))

    def test_enabledness_is_local_to_declared_sources(self):
        state = ReasonState()
        state.mint("e", {Atom("p"), Receipt("r")}, Atom("q"))
        big = frozenset({Atom("p"), Atom("noise1"), Atom("noise2")})
        small = frozenset({Atom("p")})
        self.assertEqual(
            enabled(state, "e", big, frozenset({"r", "other"})),
            enabled(state, "e", small, frozenset({"r"})),
        )

    def test_hypothetical_query_is_the_same_function(self):
        state = ReasonState()
        state.mint("e", {Atom("p")}, Atom("q"))
        actual = frozenset()
        proposed = frozenset({Atom("p")})
        before = state.occurrences()
        self.assertFalse(enabled(state, "e", actual, frozenset()))
        self.assertTrue(enabled(state, "e", proposed, frozenset()))
        self.assertEqual(state.occurrences(), before)

    def test_dependents_answers_the_withdrawal_question(self):
        state = ReasonState()
        a = App("sigma", "c", 1)
        state.mint("e1", {Atom("p"), a}, Atom("q"))
        state.mint("e2", {Atom("p")}, Atom("q2"))
        self.assertEqual(dependents(state, a), ("e1",))


class TestPolicyLayerNotSubstrate(unittest.TestCase):
    """Investigation 3: JTMS/ATMS functionality is policy plus caching."""

    def setUp(self):
        self.state = ReasonState()
        self.a, self.b = Atom("a"), Atom("b")
        self.state.mint("e1", {self.a}, Atom("m"))
        self.state.mint("e2", {self.b}, Atom("m"))
        self.state.mint("e3", {Atom("m"), self.b}, Atom("n"))
        self.universe = frozenset({self.a, self.b})

    def test_closure_is_the_named_policy_not_a_query(self):
        # The substrate reports a live reason for m without adopting m; the
        # closure policy adopts it. The two answers differ, which is the point.
        stance = frozenset({self.a})
        self.assertNotIn(Atom("m"), stance)
        self.assertIn(Atom("m"), support_closure(self.state, stance, frozenset()))

    def test_label_backends_agree_extensionally(self):
        by_prop = labels_by_propagation(self.state, self.universe, frozenset())
        for target in (Atom("m"), Atom("n"), self.a, self.b):
            by_enum = labels_by_enumeration(self.state, self.universe, frozenset(), target)
            self.assertEqual(by_prop.get(target, frozenset()), by_enum, target)

    def test_minimal_environments_match_atms_expectations(self):
        by_enum = labels_by_enumeration(self.state, self.universe, frozenset(), Atom("m"))
        self.assertEqual(by_enum, frozenset({frozenset({self.a}), frozenset({self.b})}))
        by_enum_n = labels_by_enumeration(self.state, self.universe, frozenset(), Atom("n"))
        self.assertEqual(by_enum_n, frozenset({frozenset({self.b})}))

    def test_nogoodhood_is_policy_relative(self):
        # A derived incompatibility: adopting both a and b supports a clash.
        clash = Incomp(frozenset({Atom("m"), Atom("n")}))
        self.state.mint("learned-incomp", {self.a, self.b}, clash)
        credulous = nogoods(self.state, self.universe, frozenset(), support_closure)

        def skeptical(state, assumptions, transcript):
            # A learner that refuses to adopt incompatibility claims: same
            # structure, different policy, different nogoods.
            stance = support_closure(state, assumptions, transcript)
            return frozenset(c for c in stance if not isinstance(c, Incomp))

        skeptical_bad = nogoods(self.state, self.universe, frozenset(), skeptical)
        self.assertIn(frozenset({self.a, self.b}), credulous)
        self.assertNotIn(frozenset({self.a, self.b}), skeptical_bad)

    def test_learned_incompatibility_invalidates_cached_nogoods(self):
        before = nogoods(self.state, self.universe, frozenset(), support_closure)
        self.assertEqual(before, frozenset())
        clash = Incomp(frozenset({Atom("m"), Atom("n")}))
        self.state.mint("learned-incomp", {self.a, self.b}, clash)
        after = nogoods(self.state, self.universe, frozenset(), support_closure)
        self.assertIn(frozenset({self.a, self.b}), after)


if __name__ == "__main__":
    unittest.main()
