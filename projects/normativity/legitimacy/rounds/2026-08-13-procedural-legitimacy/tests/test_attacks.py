"""The whole-architecture prosecution, and the independence matrix.

Each test names the attack, the verdict of the conjunction, and the verdict of
the independent target.  The tests that matter most are the ones where the
conjunction holds and the target fails.
"""

from __future__ import annotations

import unittest

import attacks as A
from conditions import evaluate, project
from environment import (L_CONFRONTATION, L_LICENSING, L_NON_MANUFACTURE,
                         L_SUBSTANCE, lstar)


def verdicts(builder, **kwargs):
    trajectory, environment = builder()
    report = evaluate(trajectory, **kwargs)
    uses, discharges, confrontations = project(trajectory)
    return report, lstar(environment, uses, discharges, confrontations)


class DefeatedAttacks(unittest.TestCase):
    """Attacks the conjunction stops."""

    def test_a_long_chain_amplification_is_refused(self):
        report, _ = verdicts(A.long_chain)
        self.assertFalse(report.four)
        self.assertIn("provenance.scope_amplified", report.p.codes)

    def test_a_ordinary_derivation_is_not_refused(self):
        """Necessity: without the amplifying link the same chain passes, so the
        condition is refusing the amplification and not the derivation."""
        report, target = verdicts(lambda: A.long_chain(amplify_at=None))
        self.assertTrue(report.four)
        self.assertTrue(target.legitimate)

    def test_b_circular_authorization_is_refused(self):
        report, _ = verdicts(A.circular)
        self.assertFalse(report.four)
        self.assertIn("provenance.cyclic_basis", report.p.codes)

    def test_d_entitlement_laundering_is_refused(self):
        report, _ = verdicts(A.entitlement_laundering)
        self.assertFalse(report.four)
        self.assertIn("inquiry.entitled_unserviced", report.i.codes)

    def test_d_is_refused_only_by_the_prospective_reading(self):
        """The clause doing the work: read entitlement at service time instead of
        at generation and the same trajectory passes."""
        report, _ = verdicts(A.entitlement_laundering,
                             prospective_entitlement=False)
        self.assertTrue(report.four)

    def test_f_flooding_is_self_defeating(self):
        """The flooder breaks its own condition rather than evading it."""
        report, target = verdicts(A.flooding)
        self.assertFalse(report.four)
        self.assertIn("inquiry.entitled_unserviced", report.i.codes)
        self.assertTrue(target.legitimate)


class SurvivingAttacks(unittest.TestCase):
    """Trajectories satisfying all four conditions that the target refuses.

    Six of them, in three families: the reasoner's inquiry machinery drifts from
    what arises (C, E), its bearing relation drifts from what bears (G), and its
    adequacy relation drifts from what settles (H, I, L).
    """

    def test_c_preemptive_generation(self):
        report, target = verdicts(A.preemptive_generation)
        self.assertTrue(report.four)
        self.assertFalse(target.legitimate)
        self.assertEqual(target.clauses(), (L_CONFRONTATION,))

    def test_e_narrow_formulation(self):
        report, target = verdicts(A.narrow_formulation)
        self.assertTrue(report.four)
        self.assertFalse(target.legitimate)
        self.assertEqual(target.clauses(), (L_CONFRONTATION,))

    def test_g_derived_defeaters(self):
        report, target = verdicts(A.derived_defeaters)
        self.assertTrue(report.four)
        self.assertFalse(target.legitimate)
        self.assertEqual(target.clauses(), (L_LICENSING,))

    def test_h_branch_selective_answerability(self):
        report, target = verdicts(A.branch_selective)
        self.assertTrue(report.four)
        self.assertFalse(target.legitimate)
        self.assertEqual(target.clauses(), (L_SUBSTANCE,))

    def test_i_authorized_distinction_collapse(self):
        report, target = verdicts(A.distinction_collapse)
        self.assertTrue(report.four)
        self.assertFalse(target.legitimate)
        self.assertEqual(target.clauses(), (L_SUBSTANCE,))

    def test_l_adequacy_narrowing_both_variants(self):
        """The headline counterexample, retroactive and prospective."""
        for variant in (False, True):
            report, target = verdicts(lambda v=variant: A.adequacy_narrowing(v))
            self.assertTrue(report.four)
            self.assertFalse(target.legitimate)
            self.assertEqual(target.clauses(), (L_SUBSTANCE,))


class PositiveControl(unittest.TestCase):
    """K — the architecture must not forbid legitimate transformation."""

    def test_k_radical_transformation_is_permitted(self):
        report, target = verdicts(A.radical_transformation)
        self.assertTrue(report.four)
        self.assertTrue(target.legitimate)


class FifthConditionTests(unittest.TestCase):
    """Prospectivity blocks the positive control; disclosure does not."""

    def test_prospectivity_refuses_legitimate_transformation(self):
        report, target = verdicts(A.radical_transformation)
        self.assertTrue(target.legitimate)
        self.assertFalse(report.x.holds)

    def test_prospectivity_and_disclosure_both_catch_the_retroactive_variant(self):
        report, _ = verdicts(lambda: A.adequacy_narrowing(False))
        self.assertFalse(report.x.holds)
        self.assertFalse(report.d.holds)

    def test_neither_catches_the_prospective_variant(self):
        report, target = verdicts(lambda: A.adequacy_narrowing(True))
        self.assertFalse(target.legitimate)
        self.assertTrue(report.x.holds)
        self.assertTrue(report.d.holds)

    def test_disclosure_separates_what_prospectivity_conflates(self):
        """Disclosure admits the positive control and refuses the retroactive
        attack; prospectivity refuses both.  So disclosure is strictly the better
        of the two, and still not sufficient."""
        good, _ = verdicts(A.radical_transformation)
        bad, _ = verdicts(lambda: A.adequacy_narrowing(False))
        self.assertEqual((good.x.holds, bad.x.holds), (False, False))
        self.assertEqual((good.d.holds, bad.d.holds), (True, False))


class CostTests(unittest.TestCase):
    """J — the type mismatch, made explicit."""

    def test_both_cost_arms_are_licensed(self):
        (quick, slow), environment = A.cost_pair()
        for trajectory in (quick, slow):
            report = evaluate(trajectory)
            uses, discharges, confrontations = project(trajectory)
            self.assertTrue(report.four)
            self.assertTrue(lstar(environment, uses, discharges,
                                  confrontations).legitimate)

    def test_the_conditions_cannot_see_a_selection(self):
        """Both arms pass, so no predicate of either arm distinguishes a policy
        that chose the cheaper one from a policy that chose it for other reasons.
        Selection is a fact about counterfactuals, not about a trajectory."""
        (quick, slow), _ = A.cost_pair()
        self.assertNotEqual(len(quick.edits), len(slow.edits))
        self.assertEqual(evaluate(quick).four, evaluate(slow).four)


class RecordEquivalenceTests(unittest.TestCase):
    """One record, two environments: the boundary this round cannot cross."""

    def test_one_trajectory_two_verdicts(self):
        trajectory, faithful, unfaithful = A.record_equivalent_pair()
        uses, discharges, confrontations = project(trajectory)
        report = evaluate(trajectory)
        self.assertTrue(report.four)
        self.assertTrue(lstar(faithful, uses, discharges,
                              confrontations).legitimate)
        self.assertFalse(lstar(unfaithful, uses, discharges,
                               confrontations).legitimate)

    def test_no_function_of_the_trajectory_separates_them(self):
        """There is one trajectory, so every predicate of it takes one value
        while the target takes two.  That is the whole argument, and it is why no
        strengthening of the four conditions closes the surviving attacks."""
        trajectory, faithful, unfaithful = A.record_equivalent_pair()
        uses, discharges, confrontations = project(trajectory)
        for predicate in (lambda t: evaluate(t).four,
                          lambda t: evaluate(t).x.holds,
                          lambda t: evaluate(t).d.holds,
                          lambda t: len(t.edits)):
            self.assertEqual(predicate(trajectory), predicate(trajectory))
        self.assertNotEqual(
            lstar(faithful, uses, discharges, confrontations).legitimate,
            lstar(unfaithful, uses, discharges, confrontations).legitimate)


class IndependenceTests(unittest.TestCase):
    """Whether the four are genuinely distinct restrictions."""

    def test_provenance_without_inquiry(self):
        report, _ = verdicts(A.entitlement_laundering)
        self.assertTrue(report.p.holds)
        self.assertFalse(report.i.holds)

    def test_inquiry_without_provenance(self):
        report, _ = verdicts(A.circular)
        self.assertTrue(report.i.holds)
        self.assertFalse(report.p.holds)

    def test_responsiveness_and_answerability_without_provenance(self):
        report, _ = verdicts(A.circular)
        self.assertTrue(report.rr.holds and report.da.holds)
        self.assertFalse(report.p.holds)

    def test_provenance_responsiveness_answerability_without_inquiry(self):
        report, _ = verdicts(A.flooding)
        self.assertTrue(report.p.holds and report.rr.holds and report.da.holds)
        self.assertFalse(report.i.holds)

    def test_provenance_inquiry_answerability_without_responsiveness(self):
        report, _ = verdicts(A.unlicensed_move)
        self.assertTrue(report.p.holds and report.i.holds and report.da.holds)
        self.assertFalse(report.rr.holds)

    def test_provenance_inquiry_responsiveness_without_answerability(self):
        report, _ = verdicts(A.unbacked_discharge)
        self.assertTrue(report.p.holds and report.i.holds and report.rr.holds)
        self.assertFalse(report.da.holds)


if __name__ == "__main__":
    unittest.main()
