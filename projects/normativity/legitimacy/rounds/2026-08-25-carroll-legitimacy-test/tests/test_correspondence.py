"""Each criterion-defining phrase, against what the code does.

Three of this round's six prosecuted failures lived in the gap between a document
and an implementation: `ancestry` was described as a closure over settlement
references and walked episodes; `Unresolved` was described as "the record does
not say" and was returned as `Refused`; `relabel_case` was described as renaming
the alphabets and silently dropped the settled-fact map. None of the three would
have been found by running the adversarial suite, because the suite asserts
verdicts and those defects preserved the verdicts it asserted.

This file asserts the *definitions* instead. Each case names a phrase that
appears in `CRITERION.md` or `LEGITIMACY_LANGUAGE.md` and checks the behaviour
that phrase claims. It is deliberately redundant with the suite: the suite would
stay green through a redefinition, and this would not.
"""
from __future__ import annotations

import unittest

import carroll_cases as cc
import enrichment as en
import fixtures as F
import legitimacy as lg


class TestAncestry(unittest.TestCase):
    """"the transitive predecessor closure ... projected to episodes\""""

    def setUp(self):
        self.case = F.C27_unlabelled_intermediate()["case"]

    def test_the_closure_is_transitive_through_unlabelled_settlements(self):
        self.assertEqual(en.settlement_ancestors(self.case, {"s2"}),
                         frozenset({"s2", "s_mid", "s1"}))

    def test_references_point_at_predecessors(self):
        """The closure walks backwards, and `WFStep(Settle)` is why it can."""
        self.assertNotIn("s2", en.settlement_ancestors(self.case, {"s1"}))

    def test_the_projection_happens_after_the_closure(self):
        self.assertEqual(en.ancestry(self.case, "E2"), frozenset({"E1", "E2"}))

    def test_an_episodeless_intervention_has_an_empty_class(self):
        self.assertEqual(en.ancestry(self.case, None), frozenset())

    def test_the_class_contains_its_own_episode(self):
        self.assertIn("E2", en.ancestry(self.case, "E2"))


class TestExcise(unittest.TestCase):
    """"only the ancestry class's settlements are removed by declaration\""""

    def setUp(self):
        self.case = F.C10_manufactured_authorization()["case"]
        self.after = en.excise(self.case, ["E"])

    def test_the_declared_removal_is_settlements_and_nothing_else(self):
        self.assertEqual(self.case.episode_seeds("E"),
                         frozenset({"s:t0-manipulation"}))

    def test_everything_else_falls_by_admission(self):
        self.assertEqual([e.id for e in self.after.reasons()], [])
        self.assertEqual([a.id for a in self.after.norm_events()], [])

    def test_positions_are_preserved(self):
        self.assertEqual(self.after.now, self.case.history().now)

    def test_the_result_is_itself_an_admissible_record(self):
        self.assertTrue(self.after.good())


class TestIndependent(unittest.TestCase):
    """"the same id, the same payload and Active ... and its condition discharged\""""

    def test_a_seed_basis_survives(self):
        d = F.C7_authorized_diana()
        self.assertTrue(lg.independent(d["case"], "proto.designated", "E", 1))

    def test_the_condition_is_inside_the_counterfactual(self):
        d = F.C26_manufactured_condition(inside=True)
        self.assertFalse(
            lg.independent(d["case"], "proto.designated", "E", d["iv"].tau,
                           frozenset({F.WINDOW}), d["iv"]))

    def test_an_intervention_with_no_episode_is_not_penalised(self):
        d = F.C7_authorized_diana()
        self.assertTrue(lg.independent(d["case"], "proto.designated", None, 1))

    def test_independence_applies_to_both_polarities(self):
        d = F.C7_authorized_diana()
        std = d["case"].history().std(0)
        for polarity in ("permit", "forbid"):
            live, _ = lg.admissible_independent(d["case"], d["iv"], std, polarity)
            self.assertIsInstance(live, tuple)


class TestProspectiveLicense(unittest.TestCase):
    """"three values, and a ground the status is a function of\""""

    def setUp(self):
        self.grounds = {name: lg.prospective_license(d["case"], d["iv"])
                        for name, d in F.C29_verdict_grounds().items()}

    def test_every_ground_is_reachable(self):
        self.assertEqual({v.ground for v in self.grounds.values()},
                         set(lg.STATUS_OF_GROUND))

    def test_refused_comes_only_from_a_prohibition(self):
        refused = {v.ground for v in self.grounds.values()
                   if v.status == lg.REFUSED}
        self.assertEqual(refused, {lg.PROHIBITION})

    def test_the_status_is_determined_by_the_ground(self):
        for v in self.grounds.values():
            self.assertEqual(v.status, lg.STATUS_OF_GROUND[v.ground])

    def test_a_licensed_verdict_names_the_basis_it_read(self):
        d = F.C7_authorized_diana()
        self.assertEqual(lg.prospective_license(d["case"], d["iv"]).bases,
                         ("proto.designated",))


class TestSuccession(unittest.TestCase):
    """"three clauses, and the second is not implied by the third\""""

    def test_survival_does_not_imply_independence(self):
        d = F.C28_prestate_reading_schema(prestate_reading=True)
        self.assertTrue(lg.survives_excision(d["case"], d["event"], d["episode"]))
        self.assertEqual(
            lg.legitimate_succession(d["case"], d["event"], d["episode"]).status,
            lg.UNRESOLVED)

    def test_independence_does_not_imply_survival(self):
        d = F.C11_same_endpoint()
        self.assertEqual(
            lg.authority_only_succession(d["manipulated"], "a:uptake", "E").status,
            lg.LICENSED)
        self.assertEqual(
            lg.legitimate_succession(d["manipulated"], "a:uptake", "E").status,
            lg.UNRESOLVED)

    def test_an_episodeless_challenge_is_vacuous(self):
        d = F.C28_prestate_reading_schema(prestate_reading=True)
        self.assertTrue(lg.survives_excision(d["case"], d["event"], None))


class TestStanding(unittest.TestCase):
    """"the value specifications in force in the record. Not theta.\""""

    def test_no_event_means_no_standing(self):
        d = F.C6_bare_diana()
        self.assertEqual(lg.current_standing(d["case"]), frozenset())

    def test_the_parameterization_is_in_the_dr_mdp_and_not_in_the_standing(self):
        d = F.C6_bare_diana()
        self.assertEqual(d["case"].dr_mdp.theta0, cc.TH_TIRED)
        self.assertFalse(lg.theta_has_standing(d["case"], cc.TH_TIRED,
                                               F.bridge(d["case"].dr_mdp)))

    def test_relabelling_carries_the_settled_facts(self):
        """The defect that made `C3`'s invariance true and untested."""
        d = F.C30_applicability_boundary("outside")
        m = d["case"].dr_mdp
        renamed = en.relabel_case(
            d["case"], {s: f"x::{s}" for s in m.states},
            {t: f"x::{t}" for t in m.thetas}, {a: f"x::{a}" for a in m.actions})
        self.assertEqual(renamed.fact_settlements, d["case"].fact_settlements)


if __name__ == "__main__":
    unittest.main()
