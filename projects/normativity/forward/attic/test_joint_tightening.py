from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from src.joint import movement_recursion
from src.joint_tightening import (
    UNIT_INTERVAL_VERTICES, BookChange, HalfSpace, RecordedChange, Region,
    attained_sequence, attained_stage_factor, core_vertices, looseness,
    recursion_stage_factor, reference_jump, retains_core_certificate,
    tightened_cap, tightening_count, zero_jump)

THETA = Q(1, 10)
BOUND = HalfSpace("e:bound", (Q(1),), Q(1, 2))          # x >= 1/2
TIGHT = HalfSpace("e:tight", (Q(1),), Q(4, 5))          # x >= 4/5
CUT = HalfSpace("e:cut", (Q(1),), Q(3, 5))              # x >= 3/5, exactly at q
MILD = HalfSpace("e:mild", (Q(1),), Q(1, 2))            # x >= 1/2, re-endorsed
BASE = Region((BOUND,))
REFERENCE = (Q(3, 5),)
HOLDINGS = (Q(2),)   # positive: a reference forced UP is the adverse direction.

DEACTIVATION = BookChange("c:deactivate", "deactivation", BASE, BASE.without("e:bound"))
SUSPENSION = BookChange("c:suspend", "suspension", BASE, Region(()))
TIGHTENING = BookChange("c:tighten", "activation", BASE, BASE.with_added(TIGHT))
POINT_SURVIVES = BookChange("c:cut", "activation", BASE, BASE.with_added(CUT))
MILD_CHANGE = BookChange("c:mild", "activation", BASE, BASE.with_added(MILD))


def _step(change, incumbent=REFERENCE):
    return RecordedChange(change, tuple(incumbent))


class JointTighteningTests(unittest.TestCase):
    def test_tightening_ledger_rows_exist(self):
        ledger = (Path(__file__).resolve().parents[1] / "LEDGER.md").read_text()
        self.assertTrue(re.search(r"^\| NL-J2. ", ledger, re.MULTILINE))
        self.assertTrue(re.search(r"^\| NL-N-J2a ", ledger, re.MULTILINE))

    def test_frozen_joint_module_is_imported_not_redefined(self):
        source = (Path(__file__).resolve().parents[1]
                  / "src" / "joint_tightening.py").read_text()
        self.assertIn("from src.joint import movement_recursion", source)
        self.assertNotIn("def movement_recursion", source)

    def test_everything_is_exact_rational(self):
        cap, coarse, _, _ = tightened_cap(THETA, Q(1, 100), Q(1, 10), Q(1, 5),
                                          (_step(DEACTIVATION), _step(TIGHTENING)))
        self.assertIsInstance(cap, Q)
        self.assertIsInstance(coarse, Q)
        for point in core_vertices(REFERENCE, THETA, UNIT_INTERVAL_VERTICES):
            self.assertIsInstance(point[0], Q)

    # F1: the core, not the bare point.
    def test_the_core_is_the_shrunk_simplex_not_the_point(self):
        core = core_vertices(REFERENCE, THETA, UNIT_INTERVAL_VERTICES)
        self.assertEqual(core, ((Q(27, 50),), (Q(32, 50),)))
        # q(1-theta) and q(1-theta)+theta.
        self.assertEqual(core[0][0], REFERENCE[0] * (1 - THETA))
        self.assertEqual(core[1][0], REFERENCE[0] * (1 - THETA) + THETA)

    # F3 / NL-N-J2a: the necessity witness.
    def test_point_survives_but_core_dies_forcing_a_nonzero_jump(self):
        """Dropping the core condition admits a zero-charged change that forces
        a nonzero jump.  This is why bare-point admission is not the certificate."""
        # The bare incumbent is admitted exactly, so a point test says "retained".
        self.assertTrue(POINT_SURVIVES.after.admits(REFERENCE))
        # The core is not: its lower end 27/50 falls below the new bound 3/5.
        self.assertFalse(retains_core_certificate(POINT_SURVIVES, REFERENCE, THETA))
        self.assertLess(Q(27, 50), Q(3, 5))
        # So the corrected predicate refuses to certify a zero charge...
        with self.assertRaises(ValueError):
            zero_jump(POINT_SURVIVES, REFERENCE, HOLDINGS, THETA)
        # ...and the real charge is nonzero: a compiler honoring the fixed-core
        # hypothesis is forced to q' >= q/(1-theta) = 2/3.
        forced = REFERENCE[0] / (1 - THETA)
        self.assertEqual(forced, Q(2, 3))
        self.assertTrue(retains_core_certificate(
            POINT_SURVIVES, (forced,), THETA))
        self.assertEqual(reference_jump(HOLDINGS, REFERENCE, (forced,)), Q(2, 15))
        # And it counts toward m*, where a point test would have missed it.
        self.assertEqual(tightening_count((_step(POINT_SURVIVES),), THETA), 1)

    # F1: NL-X6 as a test, not a remark.
    def test_deactivation_and_suspension_retain_the_core(self):
        """S subset S' preserves inclusion — the work NL-X6 was cited for."""
        for change in (DEACTIVATION, SUSPENSION):
            self.assertTrue(change.expands(), change.change_id)
            self.assertTrue(retains_core_certificate(change, REFERENCE, THETA),
                            change.change_id)
            self.assertEqual(zero_jump(change, REFERENCE, HOLDINGS, THETA), Q(0))
        # Removing constraints cannot exclude a point the larger set admitted.
        core = core_vertices(REFERENCE, THETA, UNIT_INTERVAL_VERTICES)
        for point in core:
            self.assertTrue(BASE.admits(point))
            self.assertTrue(DEACTIVATION.after.admits(point))

    def test_a_change_excluding_even_the_bare_point_invalidates_the_core(self):
        self.assertFalse(TIGHTENING.after.admits(REFERENCE))
        self.assertFalse(retains_core_certificate(TIGHTENING, REFERENCE, THETA))
        with self.assertRaises(ValueError):
            zero_jump(TIGHTENING, REFERENCE, HOLDINGS, THETA)
        self.assertEqual(reference_jump(HOLDINGS, REFERENCE, (Q(4, 5),)), Q(2, 5))
        # The favorable direction charges nothing: the cap is one-sided.
        self.assertEqual(reference_jump((Q(-2),), REFERENCE, (Q(4, 5),)), Q(0))

    # F4: retention is theta-relative, not a shape property.
    def test_the_same_change_retains_or_invalidates_depending_on_theta(self):
        # Core lower end is q(1-theta) = (3/5)(1-theta); the bound is 1/2.
        self.assertTrue(retains_core_certificate(MILD_CHANGE, REFERENCE, Q(1, 10)))
        self.assertFalse(retains_core_certificate(MILD_CHANGE, REFERENCE, Q(1, 2)))
        # The crossover is exact at theta = 1/6, where the core lower end is 1/2.
        self.assertEqual(REFERENCE[0] * (1 - Q(1, 6)), Q(1, 2))
        self.assertTrue(retains_core_certificate(MILD_CHANGE, REFERENCE, Q(1, 6)))
        self.assertFalse(retains_core_certificate(
            MILD_CHANGE, REFERENCE, Q(1, 6) + Q(1, 1000)))
        # It is constraint-adding at every theta: the shape never changes.
        self.assertFalse(MILD_CHANGE.expands())

    # F2: counting against the recorded trajectory.
    def test_the_count_uses_the_pre_change_incumbent_not_the_initial_one(self):
        # After the forced move the same cut is core-retaining, so a history that
        # records the move counts it once, not twice.
        moved = (Q(2, 3),)
        repeat = BookChange("c:cut-again", "activation",
                            BASE.with_added(CUT), BASE.with_added(CUT))
        trajectory = (_step(POINT_SURVIVES, REFERENCE), _step(repeat, moved))
        self.assertEqual(tightening_count(trajectory, THETA), 1)
        # Judged against the initial reference throughout, the second change
        # would also be counted -- the old behaviour, and wrong.
        naive = tightening_count((_step(POINT_SURVIVES), _step(repeat, REFERENCE)),
                                 THETA)
        self.assertEqual(naive, 2)
        self.assertNotEqual(naive, tightening_count(trajectory, THETA))

    def test_the_count_is_monotone_in_the_history(self):
        history = (_step(DEACTIVATION), _step(TIGHTENING), _step(SUSPENSION))
        counts = [tightening_count(history[:n], THETA) for n in range(len(history) + 1)]
        self.assertEqual(counts, [0, 0, 1, 1])
        for earlier, later in zip(counts, counts[1:]):
            self.assertLessEqual(earlier, later)

    # F5: the showcase numbers, re-verified under the corrected predicate.
    def test_the_showcase_classification_and_constants_are_unchanged(self):
        theta, error, risk, ordinary = THETA, Q(1, 100), Q(1, 10), Q(1, 5)
        history = (_step(DEACTIVATION), _step(TIGHTENING))
        cap, coarse, tightened, naive = tightened_cap(
            theta, error, risk, ordinary, history)
        self.assertEqual((tightened, naive), (1, 2))
        caps = movement_recursion(theta, error, risk, ordinary, 2)
        self.assertEqual((cap, coarse), (caps[1], caps[2]))
        self.assertEqual(cap, Q(31, 10))
        self.assertEqual(coarse, Q(321, 10))
        self.assertLess(cap, coarse)

    def test_with_no_core_retaining_change_the_cap_is_unchanged(self):
        theta, error, risk, ordinary = THETA, Q(1, 100), Q(1, 10), Q(1, 5)
        cap, coarse, tightened, naive = tightened_cap(
            theta, error, risk, ordinary, (_step(TIGHTENING),))
        self.assertEqual((tightened, naive), (1, 1))
        self.assertEqual(cap, coarse)

    # (b) The attained optimum -- untouched by this repair (pure theta arithmetic).
    def test_the_recursion_overcharges_exactly_one_per_stage(self):
        for theta in (Q(1, 10), Q(1, 4), Q(1, 3), Q(1, 2), Q(2, 3), Q(3, 4), Q(1)):
            self.assertEqual(recursion_stage_factor(theta),
                             attained_stage_factor(theta) + Q(1))

    def test_the_cap_is_qualitatively_loose_for_theta_at_least_one_half(self):
        for theta in (Q(1, 2), Q(2, 3), Q(3, 4)):
            self.assertLessEqual(attained_stage_factor(theta), Q(1))
            self.assertGreater(recursion_stage_factor(theta), Q(1))
            self.assertEqual(recursion_stage_factor(theta), Q(1) / theta)
        self.assertEqual(attained_stage_factor(Q(1)), Q(0))
        self.assertEqual(recursion_stage_factor(Q(1)), Q(1))
        flat = attained_sequence(Q(1, 2), Q(1), 4)
        self.assertEqual(flat, (Q(1), Q(1), Q(1), Q(1), Q(1)))
        bound = movement_recursion(Q(1, 2), Q(0), Q(0), Q(1), 4)
        self.assertEqual(bound, (Q(1), Q(2), Q(4), Q(8), Q(16)))
        self.assertEqual(looseness(Q(1, 2), Q(1), 4), (Q(1), Q(2), Q(4), Q(8), Q(16)))

    def test_below_one_half_both_grow_but_the_gap_persists(self):
        theta = Q(1, 4)
        self.assertEqual(attained_stage_factor(theta), Q(3))
        self.assertEqual(recursion_stage_factor(theta), Q(4))
        ratios = looseness(theta, Q(1), 3)
        self.assertEqual(ratios[0], Q(1))
        for earlier, later in zip(ratios, ratios[1:]):
            self.assertGreater(later, earlier)


if __name__ == "__main__":
    unittest.main()
