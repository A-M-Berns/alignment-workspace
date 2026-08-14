"""WP-5: two engines, one mechanism, and the three multi-engine witnesses."""

from __future__ import annotations

import unittest
from dataclasses import replace
from fractions import Fraction as Q

from src.case_stream import Transfer, crosses_fence
from src.coherence import ToleranceSchedule
from src.settlement_interface import (
    EMPIRICAL,
    LOGICAL,
    DeclaredHypothesis,
    evaluate_interface,
)
from src.two_engines import (
    CROSSING_TRANSFER,
    EMPIRICAL_ACCOUNT,
    EMPIRICAL_FENCE,
    EMPIRICAL_OWNER,
    EMPIRICAL_RESERVE,
    FENCED_TRANSFER,
    LOGICAL_ACCOUNT,
    LOGICAL_FENCE,
    LOGICAL_OWNER,
    LookupProver,
    breach_isolation_witness,
    compose_purse,
    disagreement_witness,
    empirical_engine,
    jurisdictions_disjoint,
    quarantine,
    two_engine_instance,
)

INSTANCE = two_engine_instance()


class JurisdictionTests(unittest.TestCase):

    def test_the_two_engines_declare_disjoint_jurisdictions(self):
        self.assertEqual(INSTANCE["disjoint"], ())

    def test_an_overlap_is_caught(self):
        logical = INSTANCE["logical"]
        clashing = replace(INSTANCE["empirical"], procedures=logical.procedures)
        obstructions = jurisdictions_disjoint((logical, clashing))
        self.assertTrue(obstructions)
        self.assertIn("claimed by both", " ".join(obstructions))

    def test_a_procedure_naming_a_foreign_owner_is_caught(self):
        empirical = INSTANCE["empirical"]
        borrowed = replace(empirical, procedures=tuple(
            replace(p, owner=LOGICAL_OWNER) for p in empirical.procedures))
        self.assertTrue(jurisdictions_disjoint((borrowed,)))

    def test_each_engine_owns_only_its_own_channel(self):
        for procedure in INSTANCE["logical"].procedures:
            self.assertEqual(procedure.channel, LOGICAL)
            self.assertEqual(procedure.owner, LOGICAL_OWNER)
        for procedure in INSTANCE["empirical"].procedures:
            self.assertEqual(procedure.channel, EMPIRICAL)
            self.assertEqual(procedure.owner, EMPIRICAL_OWNER)

    def test_the_deductive_engine_satisfies_the_checkable_clauses(self):
        report = evaluate_interface(INSTANCE["logical"], INSTANCE["record"])
        self.assertTrue(report.checkable_hold, report.obstructions)

    def test_every_logical_pin_ships_a_derivation(self):
        for pin in LookupProver().pins(1):
            self.assertTrue(pin.derivation)


class DisagreementWitnessTests(unittest.TestCase):
    """Two thermometers, one world claim, and no conflict in the record."""

    def setUp(self):
        self.witness = disagreement_witness()

    def test_the_two_procedures_write_distinct_report_variables(self):
        self.assertTrue(self.witness.distinct_variables)
        self.assertEqual(len(self.witness.pins), 2)
        self.assertNotEqual(self.witness.pins[0].variable_id,
                            self.witness.pins[1].variable_id)

    def test_there_is_no_pin_conflict_anywhere(self):
        """Write-once is about a variable, so redundancy cannot breach it."""
        self.assertFalse(self.witness.pin_conflict)

    def test_the_two_pins_really_do_disagree_about_the_world(self):
        self.assertNotEqual(self.witness.pins[0].value, self.witness.pins[1].value)
        claims = {w.world_claim for w in self.witness.warrants}
        self.assertEqual(len(claims), 1, "one world claim, two bridges")
        directions = {w.direction for w in self.witness.warrants}
        self.assertEqual(directions, {"supports", "undercuts"})

    def test_the_disagreement_surfaces_in_the_answerable_layer(self):
        self.assertTrue(self.witness.region_infeasible)
        self.assertIsNotNone(self.witness.answerable_grounds)
        self.assertIn("farkas", self.witness.answerable_grounds.payload)

    def test_the_objection_is_against_the_book_not_against_an_engine(self):
        """Both bridges are endorsed book content; the pens are untouched."""
        self.assertTrue(all(w.endorsed for w in self.witness.warrants))
        payload = self.witness.answerable_grounds.payload
        self.assertIn("book_version", payload)


class BreachIsolationTests(unittest.TestCase):

    def setUp(self):
        self.witness = breach_isolation_witness()

    def test_the_breached_channel_is_quarantined(self):
        self.assertTrue(self.witness.empirical_frozen)

    def test_the_other_channel_is_not_frozen_by_it(self):
        self.assertFalse(self.witness.logical_frozen)
        self.assertFalse(self.witness.logical_tolled_by_breach)
        self.assertTrue(self.witness.logical_still_running)

    def test_the_two_tolling_causes_are_reported_separately(self):
        """The logical channel is tolled for its own reason, not the breach's.

        Reporting one flag would let the ripeness clause's standing tolling
        masquerade as a failure of isolation.
        """
        logical = [c for c in self.witness.clocks if c.channel == LOGICAL]
        self.assertTrue(logical)
        for clock in logical:
            self.assertTrue(clock.tolled_rateless)
            self.assertFalse(clock.tolled_by_breach)
            self.assertTrue(clock.tolled)

    def test_quarantining_the_logical_channel_leaves_the_empirical_one_running(self):
        clocks = quarantine(LOGICAL, (("q:warm", EMPIRICAL), ("q:phi", LOGICAL)))
        empirical = [c for c in clocks if c.channel == EMPIRICAL]
        self.assertTrue(all(not c.frozen and not c.tolled for c in empirical))


class ComposedPurseTests(unittest.TestCase):

    def setUp(self):
        self.engines = (INSTANCE["logical"], INSTANCE["empirical"])
        self.exposures = {LOGICAL_OWNER: Q(0), EMPIRICAL_OWNER: Q(2)}

    def test_each_engine_declares_its_own_limit(self):
        purse = compose_purse(self.engines, self.exposures)
        self.assertEqual(dict(purse.limits),
                         {LOGICAL_OWNER: Q(0), EMPIRICAL_OWNER: Q(2)})

    def test_exposure_is_bounded_by_the_fenced_sum(self):
        purse = compose_purse(self.engines, self.exposures)
        self.assertEqual(purse.fenced_sum, Q(2))
        self.assertTrue(purse.within_limits)
        self.assertLessEqual(sum(v for _, v in purse.exposures), purse.fenced_sum)

    def test_exposure_beyond_one_engine_s_own_limit_is_caught(self):
        purse = compose_purse(self.engines, {LOGICAL_OWNER: Q(1),
                                             EMPIRICAL_OWNER: Q(0)})
        self.assertFalse(purse.within_limits,
                         "the refusing purse's limit is zero, so any loss breaches it")

    def test_a_transfer_between_provenances_fires_the_cross_subsidy_objection(self):
        purse = compose_purse(self.engines, self.exposures, (CROSSING_TRANSFER,))
        self.assertIsNotNone(purse.crossing)
        self.assertIn("fence_id", purse.crossing.payload)

    def test_a_transfer_inside_one_provenance_does_not(self):
        purse = compose_purse(self.engines, self.exposures, (FENCED_TRANSFER,))
        self.assertIsNone(purse.crossing)

    def test_the_fences_are_declared_and_enclose_their_own_families(self):
        self.assertTrue(LOGICAL_FENCE.declared and EMPIRICAL_FENCE.declared)
        self.assertIn(EMPIRICAL_ACCOUNT, EMPIRICAL_FENCE.inside_accounts)
        self.assertIn(EMPIRICAL_RESERVE, EMPIRICAL_FENCE.inside_accounts)
        self.assertFalse(crosses_fence(FENCED_TRANSFER, EMPIRICAL_FENCE))
        self.assertTrue(crosses_fence(CROSSING_TRANSFER, EMPIRICAL_FENCE))

    def test_a_pooled_system_declares_no_fence_and_nothing_crosses(self):
        from src.case_stream import POOLED

        self.assertFalse(crosses_fence(CROSSING_TRANSFER, POOLED))


class DocketInvariantTests(unittest.TestCase):
    """The multi-engine instance breaks no existing invariant."""

    def test_the_shared_docket_still_satisfies_the_clock_clauses(self):
        logical = INSTANCE["logical"]
        report = evaluate_interface(logical, INSTANCE["record"],
                                    clauses=("C2", "C3"))
        self.assertTrue(all(v.holds for v in report.verdicts), report.obstructions)

    def test_a_tolerance_schedule_is_carried_per_engine(self):
        loose = empirical_engine(ToleranceSchedule("t:loose", {}, Q(1, 2)))
        self.assertEqual(loose.tolerance.at(0), Q(1, 2))
        self.assertEqual(INSTANCE["logical"].tolerance.at(0), Q(0))


if __name__ == "__main__":
    unittest.main()
