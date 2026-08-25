"""The Level-I accounting theorem, its lemma, and the necessity of its laws.

    quantitative answerability invariants  =>  sum_t c_t < infinity

is checked here as: the one-step potential inequality holds on driven runs, it
telescopes, and removing either of the two structural laws breaks it with an
explicit divergent witness.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import answerability as A
import safety
import trajectories as T
import variants as v
from answerability import (AllowanceLedger, LaunderingLedger,
                           LiabilityViolation, SilentCreationLedger)
from deduction import world_deficit
from pipeline import run_day
from waist import Expect, Ineq, Injunction


class TheAllocationLemma(unittest.TestCase):
    """`D` is subadditive over a partition of the rows, so allocation covers."""

    def two_standings(self, day: int = 2):
        X = v.x0()
        a = Injunction("JA", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 4)),))
        b = Injunction("JB", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 3)),))
        return run_day(day, v.base_stage(X), v._std([("sA", a), ("sB", b)]))

    def test_the_allocation_covers_the_joint_charge(self):
        run = self.two_standings()
        alloc = A.allocate(run.compiled, run.live_worlds, run.day,
                           Q(1, 100), Q(1), Q(1, 10))
        self.assertGreaterEqual(A.subadditivity_gap(run.charge, alloc), Q(0))

    def test_it_covers_on_every_non_blocking_case_in_the_suite(self):
        cases = [self.two_standings(),
                 v.syntactically_fine_but_inadmissible(),
                 v.inert_injunction()]
        cases += [r for r in T.mesh_counterexample()[2].values()]
        for run in cases:
            if run.conflict.blocking:
                continue
            alloc = A.allocate(run.compiled, run.live_worlds, run.day,
                               run.charged.slack, run.charged.volume,
                               run.charged.tolerance)
            self.assertGreaterEqual(
                A.subadditivity_gap(run.charge, alloc), Q(0), repr(run.day))

    def test_the_lemma_is_max_of_sum_against_sum_of_max(self):
        """Recomputed from `world_deficit` so the inequality is visible."""
        run = self.two_standings()
        region = safety.region_of(run.compiled)
        joint = max(sum(world_deficit(region, w), Q(0)) for w in run.live_worlds)
        groups = {}
        for row in run.compiled.rows:
            groups.setdefault(row.standing_id, []).append(row)
        solo = Q(0)
        for rows in groups.values():
            sub = A._SubPresentation(run.compiled.coords, tuple(rows))
            solo += max(sum(world_deficit(safety.region_of(sub), w), Q(0))
                        for w in run.live_worlds)
        self.assertLessEqual(joint, solo)

    def test_each_group_is_a_real_request_over_the_joint_support(self):
        run = self.two_standings()
        alloc = A.allocate(run.compiled, run.live_worlds, run.day,
                           Q(1, 100), Q(1), Q(1, 10))
        self.assertEqual(set(alloc), {"sA", "sB"})
        for amount in alloc.values():
            self.assertGreaterEqual(amount, Q(0))


class TheLedgerLaws(unittest.TestCase):
    """Each transition, and what it refuses."""

    def test_capacity_enters_only_through_a_counted_grant(self):
        led = AllowanceLedger()
        self.assertEqual(led.potential(), Q(0))
        led.grant("q1", Q(5), "constitution")
        self.assertEqual(led.potential(), Q(5))
        self.assertEqual(led.granted, Q(5))

    def test_a_negative_grant_or_charge_is_refused(self):
        led = AllowanceLedger()
        with self.assertRaises(LiabilityViolation):
            led.grant("q1", Q(-1), "x")
        with self.assertRaises(LiabilityViolation):
            led.spend("q1", Q(-1))

    def test_an_unaffordable_charge_spends_nothing(self):
        led = AllowanceLedger()
        led.grant("q1", Q(1), "c")
        self.assertFalse(led.spend("q1", Q(2)))
        self.assertEqual(led.potential(), Q(1))
        self.assertEqual(led.charged, Q(0))

    def test_succession_carries_and_never_grows(self):
        led = AllowanceLedger()
        led.grant("q1", Q(6), "c")
        led.succeed("q1", ["q2", "q3"])
        self.assertEqual(led.potential(), Q(6))
        self.assertEqual(led.balances["q2"], Q(3))
        self.assertEqual(led.balances["q3"], Q(3))

    def test_merging_predecessors_accumulates_without_growing(self):
        led = AllowanceLedger()
        led.grant("q1", Q(2), "c")
        led.grant("q2", Q(3), "c")
        before = led.potential()
        led.succeed("q1", ["q3"])
        led.succeed("q2", ["q3"])
        self.assertEqual(led.potential(), before)
        self.assertEqual(led.balances["q3"], Q(5))

    def test_transfer_is_conservation_under_relabelling(self):
        led = AllowanceLedger()
        led.grant("q1", Q(4), "c")
        led.transfer("q1", "q2")
        self.assertEqual(led.potential(), Q(4))
        self.assertEqual(led.balances["q2"], Q(4))

    def test_retiring_an_episode_discharges_its_allowance(self):
        led = AllowanceLedger()
        led.grant("q1", Q(4), "c")
        self.assertEqual(led.retire("q1"), Q(4))
        self.assertEqual(led.potential(), Q(0))
        self.assertIn("discharge", [e[0] for e in led.log])

    def test_a_grant_at_succession_is_counted_as_a_grant(self):
        led = AllowanceLedger()
        led.grant("q1", Q(1), "c")
        led.succeed("q1", ["q2"], grants={"q2": Q(3)})
        self.assertEqual(led.granted, Q(4))
        self.assertEqual(led.potential(), Q(4))


class TheOneStepInequality(unittest.TestCase):
    """`c_t + Phi_{t+1} <= Phi_t + eta_t` on a driven run."""

    def driven(self, capital=Q(40), days=(0, 1, 2)):
        X = v.x0()
        J = T.ceiling(X)
        view = v._std([("s", J)])
        led = AllowanceLedger()
        led.grant("q:s", Q(capital), "constitution")
        steps = A.run_accounted(
            days, lambda n: T.stage_with(X, days), lambda n: view, led,
            lambda sid: "q:s")
        return led, steps

    def test_every_step_satisfies_the_inequality(self):
        _, steps = self.driven()
        for s in steps:
            self.assertTrue(s.holds, f"day {s.date}")

    def test_the_run_telescopes(self):
        _, steps = self.driven()
        self.assertTrue(A.telescopes(steps))

    def test_the_cumulative_charge_is_under_the_bound(self):
        _, steps = self.driven()
        total = sum((s.charge for s in steps), Q(0))
        self.assertLessEqual(total, A.bound(steps))

    def test_with_no_grants_the_bound_is_the_initial_potential(self):
        led, steps = self.driven()
        self.assertEqual(sum((s.granted for s in steps), Q(0)), Q(0),
                         "the grant happened before the run")
        self.assertEqual(A.bound(steps), steps[0].potential_before)

    def test_exhaustion_withholds_rather_than_overspending(self):
        led, steps = self.driven(capital=Q(6))
        self.assertTrue(any(s.withheld for s in steps))
        self.assertGreaterEqual(led.potential(), Q(0))
        for s in steps:
            self.assertTrue(s.holds)

    def test_a_withheld_date_contributes_no_charge(self):
        _, steps = self.driven(capital=Q(6))
        for s in steps:
            if s.withheld:
                self.assertEqual(s.charge, Q(0))


class TheLawsAreNecessary(unittest.TestCase):
    """Remove one and the cumulative charge escapes the bound."""

    def repeated_supersession(self, ledger, dates=8):
        """One force superseded by an equivalent successor at every date.

        Semantically nothing changes — the same demand is in force throughout —
        so any accounting under which this is free is one that lets a source
        launder its liability by renaming itself.
        """
        X = v.x0()
        J = T.ceiling(X)
        view = v._std([("s", J)])
        stage = T.stage_with(X, (2,))
        run = run_day(2, stage, view)
        alloc = A.allocate(run.compiled, run.live_worlds, 2, Q(1, 100), Q(1),
                           Q(1, 10))
        per_date = sum(alloc.values(), Q(0))
        total = Q(0)
        episode = "q:0"
        for i in range(dates):
            if ledger.spend(episode, per_date):
                total += per_date
            successor = f"q:{i + 1}"
            ledger.succeed(episode, [successor])
            episode = successor
        return total, per_date

    def test_with_L2_the_total_is_bounded_by_the_initial_allowance(self):
        led = AllowanceLedger()
        led.grant("q:0", Q(10), "constitution")
        total, per_date = self.repeated_supersession(led)
        self.assertLessEqual(total, Q(10))
        self.assertLess(total, per_date * 8)

    def test_without_L2_it_grows_without_bound(self):
        led = LaunderingLedger(refresh=Q(10))
        led.grant("q:0", Q(10), "constitution")
        total, per_date = self.repeated_supersession(led)
        self.assertEqual(total, per_date * 8)
        self.assertGreater(total, Q(10))

    def test_and_the_gap_grows_with_the_number_of_supersessions(self):
        short = LaunderingLedger(refresh=Q(10))
        short.grant("q:0", Q(10), "c")
        long_ = LaunderingLedger(refresh=Q(10))
        long_.grant("q:0", Q(10), "c")
        a, _ = self.repeated_supersession(short, dates=4)
        b, _ = self.repeated_supersession(long_, dates=16)
        self.assertEqual(b, 4 * a)

    def test_without_L3_a_fresh_episode_funds_itself(self):
        led = SilentCreationLedger(default=Q(10))
        total = Q(0)
        for i in range(8):
            if led.spend(f"q:new{i}", Q(5)):
                total += Q(5)
        self.assertEqual(total, Q(40))
        self.assertEqual(led.granted, Q(0),
                         "capacity appeared with no grant recorded")

    def test_the_honest_ledger_records_every_unit_of_capacity(self):
        led = AllowanceLedger()
        led.grant("q1", Q(3), "c")
        led.succeed("q1", ["q2", "q3"])
        led.transfer("q2", "q4")
        self.assertEqual(led.granted, Q(3))
        self.assertLessEqual(led.potential() + led.charged, led.granted)


class WhatTheTheoremDoesNotAssume(unittest.TestCase):
    """The route deliberately avoids the refuted premise."""

    def test_it_does_not_need_the_deficit_to_fall(self):
        """The mesh counterexample is accounted for without complaint."""
        X = v.x0()
        J = T.ceiling(X)
        view = v._std([("s", J)])
        stage = T.stage_with(X, (1, 2), settled=T._at_most_half(X))
        led = AllowanceLedger()
        led.grant("q:s", Q(40), "constitution")
        steps = A.run_accounted((1, 2), lambda n: stage, lambda n: view, led,
                                lambda sid: "q:s")
        self.assertEqual(steps[0].charge, Q(0))
        self.assertGreater(steps[1].charge, Q(0),
                           "the deficit rose, as the counterexample says")
        for s in steps:
            self.assertTrue(s.holds)
        self.assertTrue(A.telescopes(steps))


if __name__ == "__main__":
    unittest.main()
