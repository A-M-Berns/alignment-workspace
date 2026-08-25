"""The canonical trajectory's two end-to-end theorems, and its replayability.

Invariant package items 16, 17, 18.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import toy
import trace as trace_module
from pipeline import operative_projection
from standing import PValue, values_projection
from toy import J0_STANDING, J1_STANDING, V0_STANDING, V1_STANDING, Trajectory


class TheRecordStaysGood(unittest.TestCase):
    """Reflective Integrity holds at every state of the trajectory."""

    def test_GC_and_AC_hold_throughout(self):
        traj = Trajectory().stage_a().stage_b().stage_c()
        for t in range(traj.history.now + 1):
            self.assertTrue(traj.history.good(t), f"state {t}")

    def test_nothing_in_the_slice_wrote_to_the_record(self):
        """The pipeline reads standing; it appends no step."""
        traj = Trajectory().stage_a()
        before = traj.history.now
        traj.day(0)
        traj.day(1)
        self.assertEqual(traj.history.now, before)


class ValueRevisionIsNotOperativeRevision(unittest.TestCase):
    """Item 16, as a state-transition fact rather than a sentence."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.a_std = self.traj.history.std()
        self.traj.stage_b()
        self.b_std = self.traj.history.std()

    def test_the_active_value_specification_changed(self):
        self.assertEqual(values_projection(self.a_std), ((V0_STANDING, "v0"),))
        self.assertEqual(values_projection(self.b_std), ((V1_STANDING, "v1"),))

    def test_the_old_value_standing_is_terminated_by_an_event(self):
        self.assertEqual(self.b_std[V0_STANDING].kind, "Terminated")
        self.assertEqual(self.b_std[V0_STANDING].status[1], "a:revalue")

    def test_the_operative_projection_did_not_change(self):
        self.assertEqual(
            [(sid, J.injunction_id) for sid, J in operative_projection(self.a_std)],
            [(sid, J.injunction_id) for sid, J in operative_projection(self.b_std)])

    def test_the_injunction_standing_is_untouched(self):
        self.assertEqual(self.a_std[J0_STANDING], self.b_std[J0_STANDING])

    def test_the_compiled_fragment_still_names_the_superseded_quantity(self):
        run = self.traj.day(1)
        self.assertTrue(all("X[v0:q]" in repr(c) or repr(c) == "phi"
                            for c in run.coords))
        self.assertFalse(any("X[v1:q]" in repr(c) for c in run.coords))

    def test_the_compiled_rows_are_the_same_condition_before_and_after(self):
        """The settlement moved the region; it did not move the demand."""
        traj = Trajectory().stage_a()
        before = traj.day(1)
        traj.stage_b()
        after = traj.day(1)
        self.assertEqual(before.coords, after.coords)
        self.assertEqual([r.coefficients for r in before.compiled.rows],
                         [r.coefficients for r in after.compiled.rows])
        self.assertNotEqual(before.deductive_vertices, after.deductive_vertices)


class ExplicitOperativeRevision(unittest.TestCase):
    """Item 17. Force moves only on a normative event that moves it."""

    def setUp(self):
        self.traj = Trajectory().stage_a().stage_b()
        self.b_std = self.traj.history.std()
        self.traj.stage_c()
        self.c_std = self.traj.history.std()

    def test_the_projection_changed_only_at_stage_C(self):
        self.assertEqual([sid for sid, _ in operative_projection(self.b_std)],
                         [J0_STANDING])
        self.assertEqual([sid for sid, _ in operative_projection(self.c_std)],
                         [J1_STANDING])

    def test_the_old_injunction_was_terminated_by_a_named_event(self):
        self.assertEqual(self.c_std[J0_STANDING].kind, "Terminated")
        self.assertEqual(self.c_std[J0_STANDING].status[1], "a:reforce")

    def test_the_new_standing_records_its_predecessor(self):
        self.assertEqual(self.c_std[J1_STANDING].pred, frozenset([J0_STANDING]))

    def test_the_fragment_moves_to_the_new_quantity(self):
        run = self.traj.day(2)
        self.assertTrue(all("X[v1:q]" in repr(c) for c in run.coords))

    def test_the_full_provenance_chain_resolves(self):
        """trade <- region <- row <- injunction standing <- event <- reason."""
        run = self.traj.day(2)
        row = run.compiled.rows[0]
        self.assertEqual(row.standing_id, J1_STANDING)
        tau = int(row.standing_id[2:].split(".")[0])
        event = [a for a in self.traj.history.norm_events() if a.tau == tau]
        self.assertEqual(len(event), 1)
        self.assertEqual(event[0].id, "a:reforce")
        basis = self.traj.history.basis(event[0])
        self.assertIn("e:reforce", basis)
        reason = [e for e in self.traj.history.reasons()
                  if e.id == "e:reforce"][0]
        self.assertEqual(reason.s_L, frozenset(["l:trial"]))
        self.assertIn("l:trial",
                      [s.id for s in self.traj.history.settlements()])


class TheTrajectoryReplays(unittest.TestCase):
    """Item 18. Two runs of the same code give the same objects and the same text."""

    def test_two_runs_agree_on_every_stage(self):
        one, two = toy.canonical(), toy.canonical()
        for key in ("A", "B", "C"):
            a, b = one[key], two[key]
            self.assertEqual(a.coords, b.coords)
            self.assertEqual(a.deductive_vertices, b.deductive_vertices)
            self.assertEqual(a.region_vertices, b.region_vertices)
            self.assertEqual(a.prices, b.prices)
            self.assertEqual(a.readings, b.readings)
            self.assertEqual(a.sharp_deficit, b.sharp_deficit)
            self.assertEqual(a.charge, b.charge)

    def test_the_rendered_trace_is_stable(self):
        self.assertEqual(trace_module.render(), trace_module.render())

    def test_the_committed_trace_matches_the_code(self):
        import pathlib
        path = pathlib.Path(__file__).resolve().parents[1] / "TRACE.txt"
        self.assertTrue(path.exists(), "TRACE.txt is committed")
        self.assertEqual(path.read_text(), trace_module.render(),
                         "regenerate with `python3 src/trace.py TRACE.txt`")


class TheReadingsAreExact(unittest.TestCase):
    """The displayed numbers, recomputed from the prices independently."""

    def test_stage_A(self):
        run = toy.canonical()["A"]
        self.assertEqual(run.prices, (Q(1, 2), Q(1, 2)))
        self.assertEqual(dict(run.readings)["Expect(X[v0:q])"], Q(1, 2))
        self.assertEqual(dict(run.readings)["Prob(phi)"], Q(1, 2))

    def test_stage_B_settlement_pins_the_first_threshold(self):
        run = toy.canonical()["B"]
        self.assertEqual(run.prices, (Q(1), Q(0), Q(1, 2)))
        self.assertEqual(dict(run.readings)["Expect(X[v0:q])"], Q(1, 2))

    def test_stage_C(self):
        run = toy.canonical()["C"]
        self.assertEqual(dict(run.readings)["Expect(X[v1:q])"], Q(1, 2))

    def test_every_ceiling_is_respected_by_the_resulting_prices(self):
        scene = toy.canonical()
        for key in ("A", "B", "C"):
            run = scene[key]
            self.assertTrue(run.compiled.satisfied_by(run.prices))


if __name__ == "__main__":
    unittest.main()
