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

    def test_the_sharp_deficit_is_zero_exactly_when_admissible(self):
        for run in (v.inert_injunction(),
                    v.syntactically_fine_but_inadmissible()):
            admissible = run.obligation("admissibility").verdict == "pass"
            self.assertEqual(admissible, run.sharp_deficit == Q(0))
            self.assertEqual(admissible, run.charge == Q(0))


class SettlementAtAFixedDay(unittest.TestCase):
    """What settling buys, stated only where it holds: at one fixed day.

    `D_t` is a maximum over the live worlds of a *fixed* row system, so removing
    worlds cannot raise it. That is the whole of the monotonicity available, and
    it is a claim about one day. `test_safety.py` shows the cross-day version is
    false.
    """

    def test_at_a_fixed_day_a_growing_stage_does_not_raise_the_deficit(self):
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
        self.assertLessEqual(after.sharp_deficit, plain.sharp_deficit)

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
        self.assertEqual(run.sharp_deficit, Q(0))
        self.assertEqual(run.obligation("admissibility").verdict, "pass")
        self.assertTrue(deductively_inert(run))


class TheDichotomysEdges(unittest.TestCase):
    """Where the biconditional holds, and what is blocked before it applies.

    The statement is: *given* a nonempty live-world set and a well-formed,
    jointly satisfiable demand, admissibility holds iff the enforced region is
    `K^D`. Both degenerate cases are refused earlier, and that ordering is what
    keeps a vacuous admissibility from reading as success.
    """

    def test_the_converse_direction(self):
        """`K = K^D` implies every live pattern satisfies every row.

        `K^D` is the hull of the live patterns, so if the intersection is all of
        it then each pattern is in `K^N`, which is admissibility. Checked on
        the inert case, where the antecedent holds.
        """
        run = v.inert_injunction()
        self.assertEqual(set(run.region_vertices), set(run.deductive_vertices))
        for pattern in run.live_worlds:
            self.assertTrue(run.compiled.satisfied_by(pattern))

    def test_an_unsatisfiable_stage_is_blocked_before_admissibility(self):
        """Otherwise a contradiction would report as maximal safety."""
        run, _ = v.unsatisfiable_stage()
        self.assertEqual(run.conflict.state, "D-stage-unsatisfiable")
        self.assertEqual(run.obligations, ())
        self.assertIsNone(run.charged)

    def test_an_empty_demand_is_blocked_before_admissibility(self):
        run = v.empty_intersection()
        self.assertEqual(run.conflict.state, "B-empty-intersection")
        self.assertEqual(run.obligations, ())

    def test_a_redundant_row_changes_the_region_by_nothing(self):
        X = v.x0()
        one, twice = self.one_and_twice(X)
        stage = v.base_stage(X)
        a = run_day(2, stage, v._std([("s", one)]))
        b = run_day(2, stage, v._std([("s", twice)]))
        self.assertEqual(set(a.region_vertices), set(b.region_vertices))
        self.assertEqual(deductively_inert(a), deductively_inert(b))
        self.assertEqual(a.obligation("admissibility").verdict,
                         b.obligation("admissibility").verdict)

    def test_but_it_doubles_the_charge(self):
        """The charge is a function of the presentation, not of the region.

        `D_t` sums the deficits *across rows* before maximising over worlds, so
        stating one demand twice doubles what it costs while enforcing exactly
        the same set of prices. This is not a defect in the certificate — the
        trader really does hold two positions — but it means a summability
        question is a question about a schedule of *presentations*, and a
        source can make its own force arbitrarily expensive by restating it.
        """
        X = v.x0()
        one, twice = self.one_and_twice(X)
        stage = v.base_stage(X)
        a = run_day(2, stage, v._std([("s", one)]))
        b = run_day(2, stage, v._std([("s", twice)]))
        self.assertEqual(b.sharp_deficit, 2 * a.sharp_deficit)
        self.assertEqual(b.charge, 2 * a.charge)

    @staticmethod
    def one_and_twice(X):
        row = Ineq(((Q(1), Expect(X)),), rhs=Q(1, 2))
        return Injunction("J1", (row,)), Injunction("J2", (row, row))


def li_neg(phi):
    import li
    return li.Neg(phi)


if __name__ == "__main__":
    unittest.main()
