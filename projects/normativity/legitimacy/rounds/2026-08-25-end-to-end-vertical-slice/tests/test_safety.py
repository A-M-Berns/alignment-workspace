"""The charged branch: the quantity, the three claims, and the trajectories.

The quantity billed for a normative force request is the canonical safety
layer's sharp live-world deficit

    D_t = max over omega live of sum_j d_{t,j}(omega)

and these tests pin that it is that one — computed by the canonical
implementation, not reproduced here — and that the slice never substitutes a
different aggregate for it.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import safety
import trajectories as T
import variants as v
from deduction import world_deficit
from outflow import LiveDeficitCertificate, OutflowAccount, charge
from pipeline import run_day


class TheSliceUsesTheCanonicalQuantity(unittest.TestCase):
    """The charge comes from the safety layer's own objects, not a clone."""

    def run_case(self):
        """A two-row request, so the two aggregates can differ at all.

        With one row every aggregate collapses to the same number; the
        confusion this class exists to pin needs a request whose rows are worst
        at different worlds.
        """
        X = v.x0()
        return run_day(1, v.base_stage(X), v._std([("s", v.j0(X))]))

    def test_the_certificate_is_the_canonical_type(self):
        run = self.run_case()
        self.assertIsInstance(run.charged.certificate, LiveDeficitCertificate)
        self.assertTrue(run.charged.certificate.verified)

    def test_the_billed_aggregate_is_the_sharp_one(self):
        run = self.run_case()
        self.assertEqual(run.sharp_deficit, run.charged.certificate.aggregate)

    def test_the_sharp_aggregate_is_a_max_of_row_sums(self):
        """Recomputed from `world_deficit`, which is the canonical per-row map."""
        run = self.run_case()
        region = safety.region_of(run.compiled)
        expected = max(sum(world_deficit(region, w), Q(0))
                       for w in run.live_worlds)
        self.assertEqual(run.sharp_deficit, expected)

    def test_it_is_not_the_sum_over_worlds_of_the_per_row_worst(self):
        """The two aggregates are different, and the slice bills the right one.

        This is the specific confusion the round had to repair: summing each
        world's worst row over the worlds is neither the sharp aggregate nor the
        conservative one, and it is not a quantity the safety theorem mentions.
        """
        run = self.run_case()
        region = safety.region_of(run.compiled)
        wrong = sum((max(world_deficit(region, w)) for w in run.live_worlds),
                    Q(0))
        self.assertNotEqual(run.sharp_deficit, wrong)

    def test_the_charge_is_the_canonical_formula(self):
        run = self.run_case()
        c = run.charged
        self.assertEqual(
            c.charge, charge(c.slack, c.volume, c.tolerance, c.certificate))
        self.assertEqual(
            c.charge, (c.slack + c.volume) * c.sharp / c.tolerance)

    def test_the_region_conversion_preserves_violations(self):
        """`region_of` is a change of type, checked against the compiled rows."""
        run = self.run_case()
        region = safety.region_of(run.compiled)
        for point in list(run.live_worlds) + list(run.region_vertices):
            self.assertEqual(tuple(world_deficit(region, point)),
                             tuple(r.violation(point)
                                   for r in run.compiled.rows))

    def test_the_certificate_binds_to_this_request(self):
        run = self.run_case()
        region = safety.region_of(run.compiled)
        self.assertIsNone(run.charged.certificate.binds(
            run.day, region, safety.support_of(run.compiled), run.live_worlds))


class FixedRequestMonotonicity(unittest.TestCase):
    """Claim A, and only claim A: one request, two nested assessments."""

    def test_a_narrower_assessment_never_raises_the_deficit(self):
        compiled, wide, narrow = T.fixed_request_two_assessments()
        self.assertTrue(set(narrow) <= set(wide))
        big = safety.certify(compiled, wide, 2).aggregate
        small = safety.certify(compiled, narrow, 2).aggregate
        self.assertLessEqual(small, big)

    def test_the_reason_is_that_D_is_a_maximum(self):
        """Removing a world removes one term from a max, so it cannot rise."""
        compiled, wide, _ = T.fixed_request_two_assessments()
        full = safety.certify(compiled, wide, 2).aggregate
        for drop in range(len(wide)):
            fewer = wide[:drop] + wide[drop + 1:]
            self.assertLessEqual(safety.certify(compiled, fewer, 2).aggregate,
                                 full)

    def test_an_empty_assessment_gives_zero(self):
        compiled, _, _ = T.fixed_request_two_assessments()
        self.assertEqual(safety.certify(compiled, (), 2).aggregate, Q(0))


class CrossDayMonotonicityIsFalse(unittest.TestCase):
    """Claim B. The mesh moves, so claim A does not transfer across days."""

    def test_the_deficit_rises_on_a_fixed_injunction_and_a_fixed_stage(self):
        _, _, runs = T.mesh_counterexample()
        self.assertEqual(runs[1].sharp_deficit, Q(0))
        self.assertEqual(runs[2].sharp_deficit, Q(1, 6))
        self.assertGreater(runs[2].sharp_deficit, runs[1].sharp_deficit)

    def test_it_rises_even_when_the_stage_strictly_grows(self):
        _, _, runs = T.mesh_counterexample_with_growth()
        self.assertLess(len(runs[1].stage.entries), len(runs[2].stage.entries))
        self.assertGreater(runs[2].sharp_deficit, runs[1].sharp_deficit)

    def test_the_injunction_is_the_same_object_on_both_days(self):
        _, J, runs = T.mesh_counterexample()
        for run in runs.values():
            self.assertEqual(run.projection[0][1], J)

    def test_the_two_days_price_different_fragments(self):
        """So "the live worlds shrank" is not even well-formed across days."""
        _, _, runs = T.mesh_counterexample()
        self.assertNotEqual(runs[1].coords, runs[2].coords)
        self.assertNotEqual(len(runs[1].coords), len(runs[2].coords))

    def test_a_free_day_becomes_a_charged_day(self):
        _, _, runs = T.mesh_counterexample()
        self.assertEqual(runs[1].charge, Q(0))
        self.assertGreater(runs[2].charge, Q(0))


class TheChargeIsNotTheDeficit(unittest.TestCase):
    """Claim C. `D_t` falling does not make `q_t` fall."""

    def test_a_falling_deficit_with_a_rising_charge(self):
        compiled, wide, narrow = T.fixed_request_two_assessments()
        loose = safety.certify(compiled, wide, 2)
        tight = safety.certify(compiled, narrow, 2)
        self.assertLessEqual(tight.aggregate, loose.aggregate)
        big = charge(Q(1, 100), Q(1), Q(1, 2), loose)
        small = charge(Q(1, 100), Q(1), Q(1, 1000), tight)
        if tight.aggregate > Q(0):
            self.assertGreater(small, big,
                               "a tighter tolerance raises the charge")

    def test_the_tolerance_route_stops_at_its_ceiling(self):
        out = T.tolerance_route()
        charges = [c.charge for c in out["charges"]]
        tolerances = [c.tolerance for c in out["charges"]]
        self.assertEqual(max(tolerances), Q(1))
        tail = [q for q, d in zip(charges, tolerances) if d == Q(1)]
        self.assertGreater(len(tail), 1)
        self.assertEqual(len(set(tail)), 1,
                         "once delta is capped the charge is constant")
        self.assertGreater(tail[0], Q(0), "and the constant is positive")


class ChargedTrajectories(unittest.TestCase):
    """The mechanics run from standing to a cumulative account, both ways."""

    def test_settlement_can_drive_the_tail_to_zero(self):
        out = T.settlement_closes_the_gap()
        charges = [c.charge for c in out["charges"]]
        self.assertGreater(charges[0], Q(0))
        self.assertEqual(charges[-1], Q(0))
        sums = T.partial_sums(out["charges"])
        self.assertEqual(sums[-1], sums[-2], "the tail adds nothing")

    def test_decaying_pressure_gives_a_summable_charge(self):
        out = T.pressure_decays()
        charges = [c.charge for c in out["charges"]]
        self.assertTrue(all(c.sharp > Q(0) for c in out["charges"]),
                        "a live world is excluded at every date")
        self.assertEqual(charges, [Q(1, 2 ** (i + 1))
                                   for i in range(len(charges))])
        self.assertLess(T.partial_sums(out["charges"])[-1], Q(1))

    def test_a_constant_charge_exhausts_the_account_and_withholds_force(self):
        out = T.nothing_decays()
        emitted = [c.emitted for c in out["charges"]]
        self.assertIn(True, emitted)
        self.assertIn(False, emitted)
        self.assertEqual(emitted, sorted(emitted, reverse=True),
                         "once exhausted it stays exhausted")
        for run, c in zip(out["runs"], out["charges"]):
            if not c.emitted:
                self.assertEqual(run.prices, (),
                                 "no price is produced for unfunded force")
                self.assertEqual(
                    run.obligation("bounded_liability").verdict, "fail")

    def test_the_account_never_goes_negative(self):
        for name in ("settlement_closes_the_gap", "pressure_decays",
                     "nothing_decays", "tolerance_route"):
            out = getattr(T, name)()
            self.assertGreaterEqual(out["account"].remaining, Q(0), name)

    def test_a_funded_day_debits_exactly_the_charge(self):
        out = T.pressure_decays()
        spent = out["account"].capital - out["account"].remaining
        self.assertEqual(spent, T.partial_sums(out["charges"])[-1])


class TheUnconditionalBranchIsStillFree(unittest.TestCase):
    """An inert injunction is charged nothing, through the same path."""

    def test_zero_deficit_gives_zero_charge_and_still_emits(self):
        run = v.inert_injunction()
        self.assertEqual(run.sharp_deficit, Q(0))
        self.assertEqual(run.charge, Q(0))
        self.assertTrue(run.charged.emitted)
        self.assertTrue(run.charged.zero_liability)


if __name__ == "__main__":
    unittest.main()
