"""Composition of the two channels, and the inertness dichotomy.

Invariant package items 13 and 15, and the round's central negative result.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import variants as v
from epistemic import pc_worlds
from geometry import in_hull
from li import payout
from pipeline import deductively_inert, run_day
from waist import Expect, Ineq, Injunction


class TheChannelsAreIndependent(unittest.TestCase):
    """Item 13. Deduction never reads an injunction; the compiler never reads a
    world."""

    def test_the_deductive_region_does_not_depend_on_the_injunction(self):
        X = v.x0()
        stage = v.base_stage(X)
        loose = Injunction("Jl", (Ineq(((Q(1), Expect(X)),), rhs=Q(9, 10)),))
        tight = Injunction("Jt", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 10)),))
        a = run_day(2, stage, v._std([("s", loose)]))
        b = run_day(2, stage, v._std([("s", tight)]))
        self.assertEqual(a.coords, b.coords)
        self.assertEqual(a.deductive_vertices, b.deductive_vertices)

    def test_the_compiled_rows_do_not_depend_on_the_stage(self):
        X = v.x0()
        J = v.j0(X)
        view = v._std([("s", J)])
        plain = run_day(1, v.base_stage(X), view)
        from epistemic import SettlementReading, SettlementSemantics, Stage
        sem = SettlementSemantics()
        sem.admit(SettlementReading("l", "o", (X.luv.gt(Q(1, 3)),), ""))
        settled = Stage.of(v._chain(X), sem.entries(["l"]))
        other = run_day(1, settled, view)
        self.assertEqual(plain.coords, other.coords)
        self.assertEqual([r.coefficients for r in plain.compiled.rows],
                         [r.coefficients for r in other.compiled.rows])
        self.assertEqual([r.rhs for r in plain.compiled.rows],
                         [r.rhs for r in other.compiled.rows])
        self.assertNotEqual(plain.deductive_vertices, other.deductive_vertices)


class TheCompositionIsAnIntersection(unittest.TestCase):

    def test_every_enforced_point_is_in_both(self):
        run = v.syntactically_fine_but_inadmissible()
        for point in run.region_vertices:
            self.assertTrue(in_hull(point, run.deductive_vertices),
                            "the enforced region lies inside K^D")
            self.assertTrue(run.compiled.satisfied_by(point),
                            "the enforced region satisfies every row")

    def test_a_deductive_vertex_satisfying_every_row_survives(self):
        run = v.syntactically_fine_but_inadmissible()
        for vertex in run.deductive_vertices:
            if run.compiled.satisfied_by(vertex):
                self.assertTrue(in_hull(vertex, run.region_vertices))


class TheInertnessDichotomy(unittest.TestCase):
    """An injunction is admissible exactly when it changes nothing.

    `hadm` — the admissibility hypothesis of the unconditional traderization
    theorem — says every stage-consistent world satisfies the region. `K^N` is
    an intersection of half-spaces and so convex, so that containment of the
    vertices gives `K^D subset K^N`, hence `K = K^D`.

    The consequence is the round's headline: no injunction that moves the price
    region is inside that theorem's hypothesis.
    """

    def test_an_inert_injunction_is_admissible_and_leaves_K_equal_to_KD(self):
        run = v.inert_injunction()
        self.assertTrue(deductively_inert(run))
        self.assertEqual(run.obligation("admissibility").verdict, "pass")
        self.assertEqual(run.excluded_worlds, ())
        self.assertEqual(set(run.region_vertices), set(run.deductive_vertices))

    def test_an_ordinary_injunction_is_inadmissible_and_moves_the_region(self):
        run = v.syntactically_fine_but_inadmissible()
        self.assertFalse(deductively_inert(run))
        self.assertEqual(run.obligation("admissibility").verdict, "fail")
        self.assertTrue(run.excluded_worlds)
        self.assertNotEqual(set(run.region_vertices),
                            set(run.deductive_vertices))

    def test_the_two_conditions_coincide_on_every_case_in_the_suite(self):
        cases = [
            v.inert_injunction(),
            v.syntactically_fine_but_inadmissible(),
            v.reflective_injunction(),
        ] + list(v.frozen_injunction_across_days(days=(0, 1, 2))[2].values())
        for run in cases:
            if run.conflict.blocking:
                continue
            admissible = run.obligation("admissibility").verdict == "pass"
            self.assertEqual(admissible, deductively_inert(run))
            if admissible:
                self.assertEqual(set(run.region_vertices),
                                 set(run.deductive_vertices))

    def test_inertness_is_containment_of_the_deductive_hull(self):
        run = v.inert_injunction()
        for vertex in run.deductive_vertices:
            self.assertTrue(run.compiled.satisfied_by(vertex))

    def test_exclusion_depth_is_zero_exactly_when_admissible(self):
        for run in (v.inert_injunction(),
                    v.syntactically_fine_but_inadmissible()):
            admissible = run.obligation("admissibility").verdict == "pass"
            self.assertEqual(admissible, run.exclusion_depth == Q(0))
            self.assertEqual(admissible, run.charge is None)


class SettlementConvertsCostIntoFreedom(unittest.TestCase):
    """Settling the quantity lowers what the same injunction costs to enforce.

    The exclusion depth is measured over the stage-consistent worlds, and
    settling removes worlds. So the same frozen payload becomes cheaper as the
    record settles, and would become free at the point where what it demands is
    already settled.
    """

    def test_depth_does_not_rise_when_the_stage_grows(self):
        from epistemic import SettlementReading, SettlementSemantics, Stage
        X = v.x0()
        J = Injunction("Jcap", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2)),))
        view = v._std([("s", J)])
        plain = run_day(2, v.base_stage(X), view)
        sem = SettlementSemantics()
        sem.admit(SettlementReading(
            "l", "o", (li_neg(X.luv.gt(Q(1, 3))),), "settled low"))
        settled = Stage.of(v._chain(X), sem.entries(["l"]))
        after = run_day(2, settled, view)
        self.assertLessEqual(after.exclusion_depth, plain.exclusion_depth)

    def test_a_settlement_that_decides_the_demand_makes_it_free(self):
        from epistemic import SettlementReading, SettlementSemantics, Stage
        import li
        X = v.x0()
        J = Injunction("Jcap", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2)),))
        sem = SettlementSemantics()
        sem.admit(SettlementReading(
            "l", "o", li.valued_at(X.luv, Q(0), 3), "settled at zero"))
        stage = Stage.of(v._chain(X), sem.entries(["l"]))
        run = run_day(2, stage, v._std([("s", J)]))
        self.assertEqual(run.exclusion_depth, Q(0))
        self.assertEqual(run.obligation("admissibility").verdict, "pass")
        self.assertTrue(deductively_inert(run))


def li_neg(phi):
    import li
    return li.Neg(phi)


if __name__ == "__main__":
    unittest.main()
