"""The settlement ledger as a source for the LI epistemic substrate.

`DeductiveProcess` asks for two things and nothing else — finite stages and
monotonicity — so what `sem_L` must satisfy to feed it is decidable by reading
the type. These are those obligations, plus the failure cases.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import li
import variants as v
from epistemic import (RawOutcome, SettlementReading, SettlementSemantics,
                       Stage, conflicting_sources, deductive_entries,
                       pc_worlds, stage_satisfiable)
from toy import Trajectory


class SigmaIsALegalDeductiveProcess(unittest.TestCase):
    """The two fields of `structure DeductiveProcess`, checked along a run."""

    def test_every_stage_is_finite(self):
        traj = Trajectory().stage_a().stage_b().stage_c()
        for t in range(traj.history.now + 1):
            self.assertIsInstance(traj.stage(t).entries, tuple)

    def test_the_stages_are_nondecreasing(self):
        traj = Trajectory().stage_a().stage_b().stage_c()
        stages = [traj.stage(t) for t in range(traj.history.now + 1)]
        for earlier, later in zip(stages, stages[1:]):
            self.assertTrue(later.extends(earlier))

    def test_monotonicity_comes_from_the_ledger_being_append_only(self):
        """Retraction is what would break it, and the ledger has no retraction.

        `ri_core.History` exposes `settle` and no removal, so the settled part
        of the stage can only grow. This states the property the type needs
        rather than the absence of an API.
        """
        traj = Trajectory().stage_a()
        before = set(traj.stage().sentences())
        traj.stage_b()
        after = set(traj.stage().sentences())
        self.assertTrue(before <= after)
        self.assertTrue(after - before)


class SemLIsTotalAndRigid(unittest.TestCase):
    """E1 and E2."""

    def test_an_unread_settlement_denotes_the_empty_set(self):
        sem = SettlementSemantics()
        self.assertEqual(sem.sem("never-admitted"), ())

    def test_a_denotation_is_write_once(self):
        self.assertIsInstance(v.rewriting_a_settlement(), ValueError)

    def test_an_old_denotation_survives_language_growth(self):
        early, later = v.old_settlement_stays_rigid()
        self.assertEqual(early, later)

    def test_sem_reads_only_the_settlement(self):
        """The signature is the argument: nothing normative is in scope.

        `SettlementSemantics.sem` takes a settlement id. There is no parameter
        through which a reason, a standing or a normative event could reach it,
        so normative interpretation cannot enter the world semantics.
        """
        import inspect
        params = list(inspect.signature(SettlementSemantics.sem).parameters)
        self.assertEqual(params, ["self", "settle_id"])


class RawOutcomeIsNotASettlement(unittest.TestCase):
    """An ambiguous observation eliminates no world."""

    def test_an_uninterpreted_reading_exposes_nothing(self):
        out = v.uninterpreted_outcome()
        self.assertFalse(out["reading"].exposes)
        self.assertEqual(out["reading"].sentences, ())

    def test_and_therefore_removes_no_world(self):
        out = v.uninterpreted_outcome()
        self.assertEqual(len(pc_worlds(out["stage"], ())),
                         len(pc_worlds(out["baseline"], ())))

    def test_the_provenance_of_the_outcome_is_still_recorded(self):
        out = v.uninterpreted_outcome()
        self.assertEqual(out["reading"].of_outcome, out["outcome"].id)
        self.assertIn("no exact account", out["reading"].note)


class ContradictionIsReportedNotRepaired(unittest.TestCase):

    def test_two_settlements_that_conflict_empty_the_world_set(self):
        run, stage = v.unsatisfiable_stage()
        self.assertFalse(stage_satisfiable(stage))
        self.assertEqual(run.conflict.state, "D-stage-unsatisfiable")

    def test_the_conflicting_sources_are_attributable(self):
        _, stage = v.unsatisfiable_stage()
        sources = conflicting_sources(stage)
        self.assertTrue(sources)
        flat = {s for group in sources for s in group}
        self.assertTrue({"l:up", "l:down"} <= flat)

    def test_settlement_against_deduction_names_both_channels(self):
        _, stage = v.settlement_against_deduction()
        self.assertFalse(stage_satisfiable(stage))
        flat = {s for group in conflicting_sources(stage) for s in group}
        self.assertIn("l:bad", flat)
        self.assertIn("deductive", flat)

    def test_neither_channel_is_dropped_to_restore_consistency(self):
        _, stage = v.settlement_against_deduction()
        self.assertTrue(stage.by_source("deductive"))
        self.assertTrue(stage.by_source("l:bad"))


class AnEmptyWorldSetSilencesRatherThanBreaks(unittest.TestCase):
    """The guarantee that would be quoted over an unsatisfiable stage is vacuous.

    `isLogicalInductor_of_stage_unsatisfiable` in the pinned dependency makes
    the criterion hold over a process with an unsatisfiable stage, because every
    quantifier in it ranges over consistent worlds. So admissibility is
    vacuously true and the exclusion depth is vacuously zero, and an
    architecture that read those numbers without checking satisfiability would
    read maximal safety off a contradiction.
    """

    def test_admissibility_would_be_vacuous(self):
        _, stage = v.unsatisfiable_stage()
        self.assertEqual(pc_worlds(stage, ()), [])

    def test_the_pipeline_reports_the_state_before_reaching_the_obligations(self):
        run, _ = v.unsatisfiable_stage()
        self.assertEqual(run.conflict.state, "D-stage-unsatisfiable")
        self.assertEqual(run.obligations, (),
                         "no obligation is reported as passing over an empty "
                         "world set")


class UnrelatedGrowthChangesNothing(unittest.TestCase):
    """Item 6: conservative extension of the language and the stage."""

    def test_coordinates_rows_regions_and_depth_are_unchanged(self):
        before, after = v.unrelated_language_extension()
        self.assertEqual(before.coords, after.coords)
        self.assertEqual(before.deductive_vertices, after.deductive_vertices)
        self.assertEqual(before.region_vertices, after.region_vertices)
        self.assertEqual(before.exclusion_depth, after.exclusion_depth)

    def test_the_grown_stage_really_is_larger(self):
        before, after = v.unrelated_language_extension()
        self.assertLess(len(before.stage.entries), len(after.stage.entries))


class TheStageChainMustCoverEveryDayGrid(unittest.TestCase):
    """A threshold the chain misses is an unconstrained atom.

    This is a requirement on how `Sigma` is built that the day-indexed
    expectation forces and that nothing else in the architecture states.
    """

    def test_a_missing_threshold_admits_an_incoherent_world(self):
        X = v.x0()
        short = Stage.of(deductive_entries(
            li.threshold_chain(X.luv, (Q(0), Q(1, 2))), note="days 0-1 only"))
        coords = X.luv.expect_affine(3).sentences()
        bad = [w for w in pc_worlds(short, coords)
               if li.holds(w, X.luv.gt(Q(2, 3)))
               and not li.holds(w, X.luv.gt(Q(1, 3)))]
        self.assertTrue(bad, "an incoherent reading of X is admitted")

    def test_the_merged_grid_excludes_them(self):
        X = v.x0()
        full = Stage.of(deductive_entries(
            li.threshold_chain(X.luv, li.merged_grid((0, 1, 2)))))
        coords = X.luv.expect_affine(3).sentences()
        bad = [w for w in pc_worlds(full, coords)
               if li.holds(w, X.luv.gt(Q(2, 3)))
               and not li.holds(w, X.luv.gt(Q(1, 3)))]
        self.assertEqual(bad, [])


if __name__ == "__main__":
    unittest.main()
