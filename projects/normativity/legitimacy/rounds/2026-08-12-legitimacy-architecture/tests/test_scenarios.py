"""The adversarial prosecution and the independence matrix.

Each test names the attack it runs and records the verdict, including the
verdicts that go against the architecture under test.
"""

from __future__ import annotations

import unittest
from fractions import Fraction as Q

from abstract import (CARRY, DISCHARGE, ENDOGENOUS, EXOGENOUS, FATE_DISCHARGED,
                      FATE_LIVE, FATE_LOST, LOSE, REFINE, constrain,
                      diachronically_answerable, fate, legitimate,
                      reasons_responsive, record)
from scenarios import (AGENDA_DEMANDS, FAITHFUL, NAIVE, REFLEXIVE, STEERED, TOLLED,
                       agenda, base_reasons, base_state, charge,
                       cheap_and_unanswerable, cheap_and_unlicensed,
                       coupled_trajectory, coverage, da_without_rr,
                       defeater_laundering, endpoint_admissible_from_start,
                       filing_extension, maximal_charge, ontology_migration,
                       prompt_answer, repeated_tolling, rr_without_da,
                       standard_laundering, composite_of,
                       transformative)


class StandardLaunderingTests(unittest.TestCase):
    """A — the reasoner moves the standard that judges it."""

    def test_naive_condition_admits_it(self):
        """With the reasoner's machinery outside the coordinate structure, the
        laundering trajectory is fully legitimate.  This is the failure the
        stated condition exists to prevent, exhibited rather than asserted."""
        trajectory = standard_laundering()
        self.assertTrue(legitimate(trajectory, NAIVE).legitimate)
        self.assertEqual(fate(trajectory, "L1").kind, FATE_DISCHARGED)

    def test_reflexive_condition_refuses_the_uncited_move(self):
        report = reasons_responsive(standard_laundering(), REFLEXIVE)
        self.assertFalse(report.responsive)
        self.assertIn("constraint.out_of_scope", report.codes())

    def test_a_self_filed_ground_restores_the_laundering(self):
        """The controlling residue: with an authority ground the reasoner itself
        filed, every local check passes and the objection is discharged.

        Neither condition reads a ground's provenance, so neither can tell this
        from the same move backed by the world.
        """
        trajectory = standard_laundering(policy_ground_source=ENDOGENOUS)
        self.assertTrue(legitimate(trajectory, REFLEXIVE).legitimate)
        self.assertEqual(fate(trajectory, "L1").kind, FATE_DISCHARGED)

    def test_provenance_is_the_only_difference(self):
        """The exogenous and endogenous versions differ in no check's input."""
        endogenous = standard_laundering(policy_ground_source=ENDOGENOUS)
        exogenous = standard_laundering(policy_ground_source=EXOGENOUS)
        self.assertEqual(legitimate(endogenous, REFLEXIVE).legitimate,
                         legitimate(exogenous, REFLEXIVE).legitimate)


class OntologyLaunderingTests(unittest.TestCase):
    """B — the vocabulary the demand was stated in is retired."""

    def test_carrying_survives_the_vocabulary_change(self):
        """Identity is opaque, so the demand survives without any word surviving."""
        trajectory = ontology_migration(CARRY)
        self.assertTrue(legitimate(trajectory, REFLEXIVE).legitimate)
        self.assertEqual(fate(trajectory, "L1").kind, FATE_LIVE)
        self.assertNotIn("harm", trajectory.final().vocabulary)

    def test_refinement_names_descendants(self):
        outcome = fate(ontology_migration(REFINE), "L1")
        self.assertEqual(outcome.kind, FATE_LIVE)
        self.assertEqual(outcome.descendants, ("L1a", "L1b"))

    def test_removal_requires_authorization_and_disclosure(self):
        self.assertIn("da.loss_without_authorization",
                      diachronically_answerable(
                          ontology_migration(LOSE, backed=False)).codes())
        self.assertIn("da.undisclosed_loss",
                      diachronically_answerable(
                          ontology_migration(LOSE, disclosed=False)).codes())

    def test_an_authorized_disclosed_loss_is_answerable(self):
        trajectory = ontology_migration(LOSE)
        self.assertTrue(diachronically_answerable(trajectory).answerable)
        outcome = fate(trajectory, "L1")
        self.assertEqual(outcome.kind, FATE_LOST)
        self.assertEqual(outcome.backing, "auth-1")


class DefeaterLaunderingTests(unittest.TestCase):
    """C — a defeater is produced for every reason that tells against."""

    def test_universal_defeat_passes_both_conditions(self):
        trajectory = defeater_laundering(rounds=3)
        self.assertTrue(legitimate(trajectory, REFLEXIVE).legitimate)
        for index in range(3):
            self.assertEqual(fate(trajectory, f"O{index}").kind, FATE_DISCHARGED)

    def test_the_repair_leaves_the_defences_outstanding(self):
        """Making a defeat file its own liability turns the laundering trajectory
        into one that ends owing an answer for every defeat."""
        trajectory = defeater_laundering(rounds=3, defeat_files_liability=True)
        final = trajectory.final()
        outstanding = [name for name in final.open_live() if name.startswith("D")]
        self.assertEqual(len(outstanding), 3)

    def test_the_repair_does_not_by_itself_reject(self):
        """Honest limit: the repair changes what is owed, not what is refused.

        The trajectory is still legitimate; what it is not is finished.  Turning
        that into a refusal needs the coverage condition, not a further check on
        the transitions.
        """
        trajectory = defeater_laundering(rounds=3, defeat_files_liability=True)
        self.assertTrue(legitimate(trajectory, REFLEXIVE).legitimate)


class AgendaTests(unittest.TestCase):
    """D — the advisor controls which demands are ever docketed."""

    def test_both_agendas_are_legitimate(self):
        for file_second in (True, False):
            self.assertTrue(legitimate(agenda(file_second), REFLEXIVE).legitimate)

    def test_only_coverage_separates_them(self):
        self.assertEqual(coverage(agenda(True), AGENDA_DEMANDS), ())
        self.assertEqual(coverage(agenda(False), AGENDA_DEMANDS), ("L2",))


class LatentPairTests(unittest.TestCase):
    """E — the self-certifying transformation, and the limit it marks.

    The pair is the deference line's kernel-checked non-recoverability pair
    (`projects/deference/note-dump-2026-08-11/deference-trust-lab/run3/work/
    trace-nonrecoverability/`), re-instantiated so that both runs write a
    normative record.  Nothing here re-proves that result; what is checked is
    that the two conditions are functions of the record, so the verdict cannot
    separate the pair.
    """

    def test_the_records_are_identical(self):
        self.assertEqual(record(coupled_trajectory(FAITHFUL)),
                         record(coupled_trajectory(STEERED)))

    def test_the_runs_genuinely_differ(self):
        """The null input for the pair: if the two runs were the same object, or
        the influence map were inert, the equality above would show nothing."""
        self.assertNotEqual(FAITHFUL.autonomous, STEERED.autonomous)
        self.assertNotEqual(FAITHFUL.influence, STEERED.influence)
        self.assertNotEqual(FAITHFUL.advisor_free().realized(),
                            STEERED.advisor_free().realized())
        deleted = STEERED.advisor_free()
        self.assertNotEqual(record(coupled_trajectory(deleted)),
                            record(coupled_trajectory(STEERED)))

    def test_both_runs_are_legitimate(self):
        for run in (FAITHFUL, STEERED):
            self.assertTrue(legitimate(coupled_trajectory(run), REFLEXIVE).legitimate)

    def test_the_influence_defects_differ_exactly(self):
        self.assertEqual(FAITHFUL.defect(), Q(0))
        self.assertEqual(STEERED.defect(), Q(1, 2))

    def test_no_record_predicate_separates_the_pair(self):
        """Any function of the record — the two conditions included — takes the
        same value on both, while the counterfactual quantity does not."""
        for predicate in (lambda t: legitimate(t, REFLEXIVE).legitimate,
                          lambda t: reasons_responsive(t, REFLEXIVE).responsive,
                          lambda t: diachronically_answerable(t).answerable,
                          lambda t: fate(t, "L1").kind,
                          lambda t: len(t.steps)):
            self.assertEqual(predicate(coupled_trajectory(FAITHFUL)),
                             predicate(coupled_trajectory(STEERED)))
        self.assertNotEqual(FAITHFUL.defect(), STEERED.defect())


class TransformativeTests(unittest.TestCase):
    """F — the framework must permit conceptual change it could not have
    licensed at the start."""

    def test_the_transformation_is_legitimate(self):
        self.assertTrue(legitimate(transformative(), REFLEXIVE).legitimate)

    def test_the_endpoint_is_not_admissible_from_the_start(self):
        self.assertFalse(endpoint_admissible_from_start())

    def test_the_initial_demand_still_has_a_traceable_fate(self):
        outcome = fate(transformative(), "L1")
        self.assertEqual(outcome.kind, FATE_DISCHARGED)
        self.assertEqual(outcome.backing, "w-welfare")


class FilingGapTests(unittest.TestCase):
    """The single gap behind A, C and D: nothing constrains what may be filed."""

    def test_one_filing_converts_a_refusal_into_an_admission(self):
        before, after = filing_extension()
        self.assertFalse(reasons_responsive(before, REFLEXIVE).responsive)
        self.assertTrue(legitimate(after, REFLEXIVE).legitimate)

    def test_the_filing_is_itself_unconstrained(self):
        """The filed ground is the reasoner's own and no check reads that."""
        _, after = filing_extension()
        filed = [g for g in after.steps[0].reasons.grounds if g.ground_id == "g-filed"]
        self.assertEqual(filed[0].source, ENDOGENOUS)
        self.assertTrue(legitimate(after, REFLEXIVE).legitimate)


class ConstraintCompositionTests(unittest.TestCase):
    """Whether a sequence of admitted steps composes to an admitted step."""

    def test_the_allowance_is_not_consumed_across_dates(self):
        """Every step is admitted against the same declared allowance, and the
        cumulative movement is the number of dates times that allowance."""
        trajectory = repeated_tolling(steps=4, per_step=Q(2), allowance=Q(2))
        self.assertTrue(reasons_responsive(trajectory, REFLEXIVE).responsive)
        self.assertEqual(trajectory.final().commitments[TOLLED], Q(8))

    def test_the_composite_of_admitted_steps_is_not_admitted(self):
        """The counterexample to composing the constraint: two steps the
        constraint admits carry the state somewhere it refuses to go in one."""
        trajectory = repeated_tolling(steps=2, per_step=Q(2), allowance=Q(2))
        composite = composite_of(trajectory)
        verdict = constrain(trajectory.initial, trajectory.steps[0].reasons,
                            composite, REFLEXIVE)
        self.assertEqual(verdict.kind, "unresolved")
        self.assertEqual(verdict.code, "constraint.magnitude_unresolved")

    def test_a_single_movement_composes(self):
        """Necessity of the repetition: with the movement made once, the
        composite is admitted, so the failure is the repeated citation and not
        the composite construction."""
        trajectory = repeated_tolling(steps=1, per_step=Q(2), allowance=Q(2))
        composite = composite_of(trajectory)
        self.assertTrue(constrain(trajectory.initial, trajectory.steps[0].reasons,
                                  composite, REFLEXIVE).admitted)

    def test_the_transformative_endpoint_is_the_other_failure(self):
        """The second way composition fails: the later step is licensed by
        standards the earlier step installed."""
        trajectory = transformative()
        composite = composite_of(trajectory)
        verdict = constrain(trajectory.initial, trajectory.steps[0].reasons,
                            composite, REFLEXIVE)
        self.assertFalse(verdict.admitted)


class IndependenceTests(unittest.TestCase):
    """Whether the components are distinct, witness by witness."""

    def test_rr_without_da(self):
        trajectory = rr_without_da()
        self.assertTrue(reasons_responsive(trajectory, REFLEXIVE).responsive)
        self.assertFalse(diachronically_answerable(trajectory).answerable)
        self.assertIn("da.discharge_without_witness",
                      diachronically_answerable(trajectory).codes())

    def test_da_without_rr(self):
        trajectory = da_without_rr()
        self.assertTrue(diachronically_answerable(trajectory).answerable)
        self.assertFalse(reasons_responsive(trajectory, REFLEXIVE).responsive)

    def test_legitimacy_without_coverage(self):
        trajectory = agenda(file_second=False)
        self.assertTrue(legitimate(trajectory, REFLEXIVE).legitimate)
        self.assertEqual(coverage(trajectory, AGENDA_DEMANDS), ("L2",))

    def test_legitimacy_and_coverage_without_performance(self):
        """Legitimate, covering, and strictly worse than an available legitimate
        alternative at every horizon."""
        slow, fast = maximal_charge(), prompt_answer()
        self.assertTrue(legitimate(slow, REFLEXIVE).legitimate)
        self.assertTrue(legitimate(fast, REFLEXIVE).legitimate)
        self.assertEqual(coverage(slow, (AGENDA_DEMANDS[0],)), ())
        self.assertEqual(charge(slow), Q(4))
        self.assertEqual(charge(fast), Q(1))
        self.assertEqual(charge(slow) - charge(fast), Q(3))

    def test_performance_without_rr(self):
        """The illegitimate route attains the same charge as the best legitimate
        one, so the performance criterion does not discriminate at its optimum."""
        cheap = cheap_and_unlicensed()
        self.assertLess(charge(cheap), charge(maximal_charge()))
        self.assertEqual(charge(cheap), charge(prompt_answer()))
        self.assertFalse(reasons_responsive(cheap, REFLEXIVE).responsive)
        self.assertTrue(reasons_responsive(prompt_answer(), REFLEXIVE).responsive)

    def test_performance_without_da(self):
        cheap = cheap_and_unanswerable()
        self.assertLess(charge(cheap), charge(maximal_charge()))
        self.assertEqual(charge(cheap), charge(prompt_answer()))
        self.assertFalse(diachronically_answerable(cheap).answerable)
        self.assertTrue(diachronically_answerable(prompt_answer()).answerable)

    def test_laundering_pays(self):
        """The charge model prices erasure, which is what makes the answerability
        condition testable rather than decorative."""
        self.assertLess(charge(cheap_and_unanswerable()), charge(maximal_charge()))


if __name__ == "__main__":
    unittest.main()
