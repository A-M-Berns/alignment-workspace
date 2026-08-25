"""Gates C, D and E: what the projection forgets, and what survives it."""
from __future__ import annotations

import unittest

import carroll_cases as cc
import drmdp
import enrichment as en
import fixtures as F
import legitimacy as lg


class TestConservativity(unittest.TestCase):
    """Gate C: adding history changes nothing about `S, Theta, A, T, R`."""

    def test_the_projection_returns_the_field(self):
        d = F.C7_authorized_diana()
        self.assertIs(en.Q_DR(d["case"]), d["case"].dr_mdp)

    def test_two_enriched_cases_share_one_dr_mdp_value(self):
        bare = F.C6_bare_diana()["case"]
        rich = F.C7_authorized_diana()["case"]
        self.assertEqual(en.Q_DR(bare), en.Q_DR(rich))
        self.assertEqual(en.Q_DR(rich), cc.ai_personal_trainer())

    def test_enrichment_cannot_write_the_dr_mdp(self):
        """No operation of the enrichment layer takes a `DRMDP` and returns one.

        Except `relabel_case`, which is the relabelling test's own instrument
        and is checked separately to be an isomorphism.
        """
        before = cc.conspiracy_influence()
        b = en.CaseBuilder(before, F.seed(), F.narrative("x", "y"))
        b.settle("s:1")
        b.reason("r:1", s_L={"s:1"}, target="t")
        self.assertEqual(b.build().dr_mdp, before)

    def test_the_record_is_untouched_by_relabelling(self):
        d = F.C3_relabelling()
        self.assertEqual(d["case"].steps, d["original"]["case"].steps)
        self.assertNotEqual(d["case"].dr_mdp, d["original"]["case"].dr_mdp)


class TestNonFactorisation(unittest.TestCase):
    """Gate E: a legitimacy-relevant property that `Q_DR` does not determine."""

    def test_same_projection_different_prior_authorization(self):
        bob = F.bare("ConspiracyInfluence", "B")
        diana = F.C7_authorized_diana()
        # The projections are isomorphic under the canonical relabelling.
        self.assertEqual(drmdp.canonical(en.Q_DR(bob["case"])),
                         drmdp.canonical(en.Q_DR(diana["case"])))
        self.assertFalse(
            lg.prior_independent_authorization(bob["case"], bob["iv"]))
        self.assertTrue(
            lg.prior_independent_authorization(diana["case"], diana["iv"]))

    def test_same_projection_literally_equal(self):
        """The sharper form: one `DRMDP` value, two records, two answers."""
        m = cc.ai_personal_trainer()
        bare = F.bare("AIPersonalTrainer", "D")
        rich = F.C7_authorized_diana()
        self.assertEqual(en.Q_DR(bare["case"]), en.Q_DR(rich["case"]))
        self.assertEqual(en.Q_DR(rich["case"]), m)
        self.assertNotEqual(
            lg.prior_independent_authorization(bare["case"], bare["iv"]),
            lg.prior_independent_authorization(rich["case"], rich["iv"]))


class TestBareNegativeControl(unittest.TestCase):
    """Gate D: with no enriched difference, no verdict difference."""

    def test_bare_bob_and_bare_diana_agree(self):
        d = F.C2_bare_negative_control()
        vb = lg.prospective_license(d["bob"]["case"], d["bob"]["iv"])
        vd = lg.prospective_license(d["diana"]["case"], d["diana"]["iv"])
        self.assertEqual((vb.status, vb.reason), (vd.status, vd.reason))
        self.assertEqual(vb.status, lg.UNRESOLVED)

    def test_bare_verdicts_are_not_permission(self):
        d = F.C2_bare_negative_control()
        for side in ("bob", "diana"):
            v = lg.prospective_license(d[side]["case"], d[side]["iv"])
            self.assertNotEqual(v.status, lg.LICENSED)

    def test_a_verdict_is_never_a_silent_boolean(self):
        d = F.C6_bare_diana()
        with self.assertRaises(TypeError):
            bool(lg.prospective_license(d["case"], d["iv"]))

    def test_relabelling_changes_nothing(self):
        d = F.C3_relabelling()
        before = lg.prospective_license(d["original"]["case"],
                                        d["original"]["iv"])
        after = lg.prospective_license(d["case"], d["iv"])
        self.assertEqual((before.status, before.reason, before.bases),
                         (after.status, after.reason, after.bases))

    def test_protocols_carry_no_label(self):
        """A protocol covers index triples, so it cannot name a narrative."""
        d = F.C7_authorized_diana()
        std = d["case"].history().std()
        for _, p in en.active_protocols(std):
            for cls in p.covers:
                self.assertTrue(all(isinstance(i, int) for i in cls))

    def test_the_class_token_is_the_same_for_both_narratives(self):
        bob = F.C9_content_neutrality()
        diana = bob["diana"]
        self.assertEqual(
            en.intervention_class(bob["case"].dr_mdp, bob["iv"]),
            en.intervention_class(diana["case"].dr_mdp, diana["iv"]))


if __name__ == "__main__":
    unittest.main()
