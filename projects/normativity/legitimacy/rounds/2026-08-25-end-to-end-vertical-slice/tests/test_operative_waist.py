"""The operative waist: what the payload admits, and what the projection does.

Invariant package items 7, 8, 10, 11.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import variants as v
from pipeline import operative_projection
from ri_core import ACTIVE, SUSPENDED, PAuth, PCmt, PForce, StandingState
from standing import PValue, values_projection
from toy import PHI, Trajectory, j0, x0
from waist import (Expect, Ineq, Injunction, MalformedInjunction, Prob, kappa)


class MalformedPayloadsAreRefusedAtTheWaist(unittest.TestCase):
    """Conflict state A, first form: refused before any compilation."""

    def refuse(self, J, needle):
        with self.assertRaises(MalformedInjunction) as ctx:
            J.check_wellformed()
        self.assertIn(needle, str(ctx.exception))

    def test_no_inequality(self):
        self.refuse(v.empty_injunction(), "no inequality")

    def test_constant_false(self):
        self.refuse(v.constant_false_injunction(), "constant-false")

    def test_constant_true(self):
        self.refuse(v.constant_true_injunction(), "constant-true")

    def test_inexact_coefficient(self):
        self.refuse(v.float_coefficient_injunction(), "not an exact rational")

    def test_a_non_quantity_operand(self):
        J = Injunction("Jbad", (Ineq((((Q(1)), "not a quantity"),), rhs=Q(0)),))
        self.refuse(J, "not a cognitive")

    def test_an_uncertified_luv(self):
        from li import LUV
        from waist import CertifiedLUV
        bad = CertifiedLUV(LUV("Y"), "none", (("w", Q(2)),))
        J = Injunction("Jy", (Ineq(((Q(1), Expect(bad)),), rhs=Q(1)),))
        self.refuse(J, "certified as a [0,1] LUV")

    def test_a_well_formed_payload_is_accepted(self):
        j0(x0()).check_wellformed()


class ProjectionExactness(unittest.TestCase):
    """Item 7. `O_n` is every active injunction standing and only those."""

    def view(self):
        J = j0(x0())
        return {
            "active": StandingState(ACTIVE, frozenset(),
                                    PForce("c", "s", J)),
            "suspended": StandingState(SUSPENDED, frozenset(),
                                       PForce("c", "s", J)),
            "terminated": StandingState(("Terminated", "a1"), frozenset(),
                                        PForce("c", "s", J)),
            "value": StandingState(ACTIVE, frozenset(), PValue("v0")),
            "commitment": StandingState(ACTIVE, frozenset(),
                                        PCmt("StanceBearing", "c")),
            "authority": StandingState(ACTIVE, frozenset(), PAuth(None)),
        }

    def test_only_active_injunction_standing_is_projected(self):
        out = operative_projection(self.view())
        self.assertEqual([sid for sid, _ in out], ["active"])

    def test_the_projection_keeps_the_standing_identity(self):
        J = j0(x0())
        view = {
            "one": StandingState(ACTIVE, frozenset(), PForce("c", "s", J)),
            "two": StandingState(ACTIVE, frozenset(), PForce("c", "s", J)),
        }
        out = operative_projection(view)
        self.assertEqual(len(out), 2,
                         "two standings carrying equal payloads are two items")
        self.assertEqual({sid for sid, _ in out}, {"one", "two"})

    def test_value_standing_projects_separately(self):
        out = values_projection(self.view())
        self.assertEqual(out, (("value", "v0"),))


class NoInvisibleForceOrWeakening(unittest.TestCase):
    """Items 10 and 11. Every row has a source; no row is dropped or relaxed."""

    def test_every_compiled_row_names_a_standing_and_an_index(self):
        traj = Trajectory().stage_a()
        run = traj.day(1)
        self.assertTrue(run.compiled.rows)
        for row in run.compiled.rows:
            self.assertIn(row.standing_id,
                          {sid for sid, _ in run.projection})
            J = dict(run.projection)[row.standing_id]
            self.assertEqual(row.label, J.ineqs[row.index].label)

    def test_the_row_count_is_the_inequality_count(self):
        traj = Trajectory().stage_a()
        run = traj.day(1)
        expected = sum(len(J.ineqs) for _, J in run.projection)
        self.assertEqual(len(run.compiled.rows), expected)

    def test_an_infeasible_projection_is_reported_not_relaxed(self):
        run = v.empty_intersection()
        self.assertEqual(run.conflict.state, "B-empty-intersection")
        self.assertFalse(run.region_vertices,
                         "no region is emitted for an empty demand")

    def test_adding_an_injunction_never_enlarges_the_region(self):
        X = x0()
        loose = Injunction("Jloose", (
            Ineq(((Q(1), Expect(X)),), rhs=Q(3, 4)),))
        tight = Injunction("Jtight", (
            Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2)),))
        stage = v.base_stage(X)
        from pipeline import run_day
        one = run_day(2, stage, v._std([("a", loose)]))
        two = run_day(2, stage, v._std([("a", loose), ("b", tight)]))
        from geometry import in_hull
        for point in two.region_vertices:
            self.assertTrue(in_hull(point, one.region_vertices))


class ProvenanceRunsBackToTheIssuingEvent(unittest.TestCase):
    """Item 8 and item 14's upper half, on the canonical trajectory."""

    def test_a_row_resolves_to_the_event_that_created_its_standing(self):
        traj = Trajectory().stage_a()
        run = traj.day(1)
        row = run.compiled.rows[0]
        self.assertIn(row.standing_id, traj.history.std())
        # The allocator is the link: `standing_tag(tau, i)` stamps the tau of
        # the event that minted the standing, and tau is injective on the
        # trajectory, so the id resolves to exactly one normative event.
        self.assertTrue(row.standing_id.startswith("@s"))
        tau = int(row.standing_id[2:].split(".")[0])
        events = [a for a in traj.history.norm_events() if a.tau == tau]
        self.assertEqual(len(events), 1)
        self.assertEqual(events[0].id, "a:force")

    def test_the_payload_carries_no_justification_the_compiler_reads(self):
        """`PForce`'s reference fields are inert for compilation."""
        X = x0()
        J = j0(X)
        a = kappa([("s", J)], 1)
        view_other = {"s": StandingState(
            ACTIVE, frozenset(), PForce("elsewhere", "elsewhere", J))}
        b = kappa(operative_projection(view_other), 1)
        self.assertEqual([r.coefficients for r in a.rows],
                         [r.coefficients for r in b.rows])
        self.assertEqual([r.rhs for r in a.rows], [r.rhs for r in b.rows])


if __name__ == "__main__":
    unittest.main()
