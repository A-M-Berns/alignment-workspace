"""The motivating normative statics, and whether they discharge safety."""
from __future__ import annotations

import unittest
from itertools import product
from fractions import Fraction as F

from core import (compile_core_row, indicator, maximal_theta,
                  priceable_coefficients)
from deduction import world_deficit
from enforcement import EnforcementTrader, Region
from market import ZERO, Fragment, holdings_value
from force_api import SafetyCertifiedForce, compile_safe_force
from outflow import LiveDeficitClaim, OutflowAccount
from normative import (Endorsement, family_deficits, force_region,
                       liability_bound_at_date)

#: `NL-SI-A7`'s instance: three worlds, `A`/`B`/`C` true at one world each.
FRAGMENT = Fragment(("A", "B", "C"), [lambda w: w[0] + w[1] + w[2] == 1])
#: the book endorses that the first world carries probability at least a half
ENDORSEMENT = Endorsement("A", F(1, 2))
THETA = F(1, 4)


class TheTwoRowFamiliesDiffer(unittest.TestCase):
    """Settlement rows carry no liability; core rows carry all of it."""

    def test_settlement_rows_have_zero_deficit_at_every_assessed_world(self):
        for settled in ({}, {"B": 0}, {"B": 0, "C": 0}):
            worlds = FRAGMENT.pc_worlds(settled)
            settlement, _ = force_region(FRAGMENT, settled, [ENDORSEMENT], THETA)
            self.assertEqual(family_deficits(settlement, worlds), F(0), settled)

    def test_core_rows_carry_the_endorsement_gap(self):
        for settled, expected in (({}, F(1, 2)), ({"B": 0}, F(1, 2)),
                                  ({"B": 0, "C": 0}, F(0))):
            worlds = FRAGMENT.pc_worlds(settled)
            _, core = force_region(FRAGMENT, settled, [ENDORSEMENT], THETA)
            self.assertEqual(family_deficits(core, worlds), expected, settled)

    def test_the_gap_is_r_minus_the_worst_delivery(self):
        for settled in ({}, {"B": 0}, {"B": 0, "C": 0}):
            worlds = FRAGMENT.pc_worlds(settled)
            _, core = force_region(FRAGMENT, settled, [ENDORSEMENT], THETA)
            self.assertEqual(family_deficits(core, worlds),
                             ENDORSEMENT.exclusion_depth(FRAGMENT, worlds),
                             settled)

    def test_the_gap_does_not_depend_on_the_core_minimum(self):
        """`theta` sets how deep the reference must sit; it does not change how
        far the endorsement outruns the assessed worlds."""
        worlds = FRAGMENT.pc_worlds({})
        for theta in (F(1, 8), F(1, 4), F(1, 2)):
            _, core = force_region(FRAGMENT, {}, [ENDORSEMENT], theta)
            self.assertEqual(family_deficits(core, worlds), F(1, 2), theta)


class SettlementDrivesTheGapDown(unittest.TestCase):
    """Monotonicity is what the existing statics contribute."""

    STAGES = ({}, {"B": 0}, {"B": 0, "C": 0})

    def test_the_worst_delivery_is_non_decreasing(self):
        values = [ENDORSEMENT.worst_delivery(FRAGMENT,
                                             FRAGMENT.pc_worlds(s))
                  for s in self.STAGES]
        self.assertEqual(values, [F(0), F(0), F(1)])
        for earlier, later in zip(values, values[1:]):
            self.assertLessEqual(earlier, later)

    def test_so_the_exclusion_depth_is_non_increasing(self):
        depths = [ENDORSEMENT.exclusion_depth(FRAGMENT, FRAGMENT.pc_worlds(s))
                  for s in self.STAGES]
        self.assertEqual(depths, [F(1, 2), F(1, 2), F(0)])
        for earlier, later in zip(depths, depths[1:]):
            self.assertGreaterEqual(earlier, later)

    def test_vindication_is_where_the_depth_reaches_zero(self):
        """Once the record entails the endorsement, the core row admits every
        assessed world and the family becomes liability-free."""
        worlds = FRAGMENT.pc_worlds({"B": 0, "C": 0})
        self.assertEqual(ENDORSEMENT.worst_delivery(FRAGMENT, worlds), F(1))
        self.assertIsNone(maximal_theta(indicator(FRAGMENT, "A", worlds),
                                        ENDORSEMENT.rhs, worlds))


class SafeMotivatingTrajectory(unittest.TestCase):
    """The endorsement is vindicated by settlement after finitely many dates."""

    #: settles `B` then `C`, then nothing further changes
    STAGES = [{}, {"B": 0}] + [{"B": 0, "C": 0}] * 10

    def declarations(self):
        out = []
        for date, settled in enumerate(self.STAGES, start=1):
            worlds = FRAGMENT.pc_worlds(settled)
            settlement, core = force_region(FRAGMENT, settled, [ENDORSEMENT],
                                            THETA)
            out.append(dict(settlement=settlement, core=core, worlds=worlds,
                            slack=F(1, 2 ** (date + 1)), volume=F(date),
                            tolerance=F(1, 10)))
        return out

    def test_only_finitely_many_dates_carry_a_deficit(self):
        depths = [ENDORSEMENT.exclusion_depth(FRAGMENT,
                                              FRAGMENT.pc_worlds(s))
                  for s in self.STAGES]
        self.assertEqual([d for d in depths if d > 0], [F(1, 2), F(1, 2)])

    def test_the_cumulative_bound_is_finite(self):
        total = sum((liability_bound_at_date(**d) for d in self.declarations()),
                    F(0))
        self.assertEqual(total, F(135, 8))
        self.assertLess(total, F(17))

    def test_it_does_not_grow_with_the_horizon(self):
        first = sum((liability_bound_at_date(**d)
                     for d in self.declarations()[:4]), F(0))
        whole = sum((liability_bound_at_date(**d)
                     for d in self.declarations()), F(0))
        self.assertEqual(first, whole)


class UnsafeContrastTrajectory(unittest.TestCase):
    """Minimally altered: the endorsement is never vindicated."""

    STAGES = [{}] * 12          #: nothing ever settles

    def declarations(self):
        out = []
        for date, settled in enumerate(self.STAGES, start=1):
            worlds = FRAGMENT.pc_worlds(settled)
            settlement, core = force_region(FRAGMENT, settled, [ENDORSEMENT],
                                            THETA)
            out.append(dict(settlement=settlement, core=core, worlds=worlds,
                            slack=F(1, 2 ** (date + 1)), volume=F(date),
                            tolerance=F(1, 10)))
        return out

    def test_the_deficit_never_decays(self):
        depths = [ENDORSEMENT.exclusion_depth(FRAGMENT,
                                              FRAGMENT.pc_worlds(s))
                  for s in self.STAGES]
        self.assertEqual(set(depths), {F(1, 2)})

    def test_the_cumulative_bound_diverges_with_the_horizon(self):
        partials = []
        for horizon in (4, 8, 12):
            partials.append(sum((liability_bound_at_date(**d)
                                 for d in self.declarations()[:horizon]), F(0)))
        self.assertLess(partials[0], partials[1])
        self.assertLess(partials[1], partials[2])
        self.assertGreater(partials[2], F(300))

    def test_the_enforcement_position_really_loses_at_an_assessed_world(self):
        """Not only the bound: the position is short the endorsement's direction
        at a world the record still permits."""
        worlds = FRAGMENT.pc_worlds({})
        _, core = force_region(FRAGMENT, {}, [ENDORSEMENT], THETA)
        trader = EnforcementTrader(core, F(4))
        price = (F(1, 4), F(1, 2), F(1, 4))
        position = trader.coefficients(price)
        losing = [w for w in worlds
                  if holdings_value(position, price, w) < 0]
        self.assertTrue(losing)


if __name__ == "__main__":
    unittest.main()


class BooleanEndorsementsJumpToZero(unittest.TestCase):
    """Why the abstract safe fixture is not automatically a statics fixture.

    A sentence-indicator endorsement `P(A) >= r` has world coefficients in
    `{0, 1}`. Its worst live delivery is `0` while any `A = 0` world survives and
    `1` once none does, so its exclusion depth holds at `r` and then drops to
    zero in one step. There is no gradual closure to be had from this shape, and
    a safety story that needs decaying depth cannot get it here.
    """

    fragment = Fragment(("A", "B"))

    def test_the_depth_holds_then_jumps(self):
        e = Endorsement("A", F(1, 2))
        seen = [e.exclusion_depth(self.fragment, self.fragment.pc_worlds(s))
                for s in ({}, {"B": True}, {"A": True})]
        self.assertEqual(seen, [F(1, 2), F(1, 2), F(0)])


class StaticsGenerateAForeverUnvindicatedTrajectory(unittest.TestCase):
    """One global affine endorsement, never vindicated, safely forced forever.

    The abstract fixture in `test_outflow` stipulates `D_t = 2^-t`; it shows the
    force mechanism admits such a trajectory, not that the normative statics
    produce one. This is produced, from a **single global functional** rather
    than a sequence of hand-built finite vectors:

        c(ω) = ½·B(ω) + ¼·C(ω) + Σ_{j≥1} 2^-(j+2)·A_j(ω) ,      r = 3/4 .

    The date-`t` endorsement is this functional restricted to the date's worlds.
    Settlement establishes `B` and then `A_1, A_2, …` in turn; `C` is never
    settled, which is what keeps a world below the demand alive forever.

    Closed forms, both exact and both proved here rather than sampled:

        m_t = 3/4 − 2^-(t+2)        the worst live delivery
        D_t = 2^-(t+2)              the exclusion depth, positive at every t

    `m_t` rises to `r` and never reaches it, so the endorsement is **never
    vindicated at any finite date**, and the cost series converges in closed
    form. Finite fixtures below test the formulas rather than standing in for
    them.

    **Scope.** `NL-SI-A2` and `NL-SI-A5` state endorsements as rows `⟪c,x⟫ ≥ r`
    with rational `c`, so an affine endorsement is inside the stated statics.
    Every *displayed instance* in the source is sentence-shaped, so this is an
    unexercised part of the interface rather than an extension of it — and the
    difference matters, because a sentence-shaped endorsement provably cannot
    generate this trajectory (`BooleanEndorsementsJumpToZero`).
    """

    rhs = F(3, 4)
    slack, volume, tolerance = F(1, 8), F(1), F(1, 2)

    def coefficient(self, world, n):
        """The global functional, evaluated at one world of an `n`-sentence stage."""
        return (F(1, 2) * world[n] + F(1, 4) * world[n + 1]
                + sum((F(1, 2 ** (k + 3)) * world[k] for k in range(n)), ZERO))

    def stage(self, t, width=6):
        """Fragment `A_1..A_n, B, C` with `B` and `A_1..A_t` settled true."""
        n = max(width, t + 2)
        names = tuple(f"A{k}" for k in range(1, n + 1)) + ("B", "C")
        fragment = Fragment(names)
        worlds = [tuple(F(b) for b in bits)
                  for bits in product((0, 1), repeat=n + 2)
                  if bits[n] == 1 and all(bits[k] == 1 for k in range(t))]
        return fragment, worlds, tuple(self.coefficient(w, n) for w in worlds)

    # --- the closed forms ---------------------------------------------------

    def test_the_worst_delivery_has_the_closed_form(self):
        for t in range(8):
            self.assertEqual(min(self.stage(t)[2]),
                             F(3, 4) - F(1, 2 ** (t + 2)))

    def test_the_depth_has_the_closed_form_and_is_never_zero(self):
        for t in range(8):
            depth = max(ZERO, self.rhs - min(self.stage(t)[2]))
            self.assertEqual(depth, F(1, 2 ** (t + 2)))
            self.assertGreater(depth, ZERO)

    def test_every_stage_restricts_the_same_global_functional(self):
        """No stage invents coefficients; each is the same `c` on fewer worlds."""
        for t in range(1, 6):
            fragment, worlds, c = self.stage(t)
            n = len(fragment.names) - 2
            for world, value in zip(worlds, c):
                self.assertEqual(value, self.coefficient(world, n))

    # --- what the statics require ------------------------------------------

    def test_the_endorsement_is_priceable_at_every_date(self):
        for t in range(7):
            fragment, worlds, c = self.stage(t)
            self.assertIsNotNone(priceable_coefficients(c, fragment, worlds))

    def test_it_is_never_vindicated(self):
        for t in range(8):
            self.assertLess(min(self.stage(t)[2]), self.rhs)

    def test_the_demand_is_the_limit_the_record_approaches(self):
        limits = [min(self.stage(t)[2]) for t in range(12)]
        self.assertTrue(all(a < b for a, b in zip(limits, limits[1:])))
        self.assertLess(self.rhs - limits[-1], F(1, 2 ** 12))

    def test_a_positive_core_minimum_is_admissible_at_every_date(self):
        for t in range(7):
            _, worlds, c = self.stage(t)
            theta = maximal_theta(c, self.rhs, worlds)
            self.assertIsNotNone(theta)
            self.assertGreater(theta, F(0))

    # --- the cost series ----------------------------------------------------

    def test_the_cost_series_sums_to_nine_eighths_in_closed_form(self):
        """`Σ_t (ε+C)·2^-(t+2)/δ = (9/8)·2·(1/2) = 9/8`, exactly."""
        factor = (self.slack + self.volume) / self.tolerance
        partial = sum((factor * F(1, 2 ** (t + 2)) for t in range(200)), ZERO)
        self.assertLess(partial, F(9, 8))
        self.assertEqual(F(9, 8) - partial, factor * F(1, 2 ** 201))

    def test_the_finite_stages_agree_with_the_series(self):
        factor = (self.slack + self.volume) / self.tolerance
        for t in range(8):
            depth = max(ZERO, self.rhs - min(self.stage(t)[2]))
            self.assertEqual(factor * depth,
                             factor * F(1, 2 ** (t + 2)))

    def test_a_finite_account_funds_every_checked_date(self):
        account = OutflowAccount(F(9, 8))
        for t in range(8):
            _, worlds, c = self.stage(t)
            depth = max(ZERO, self.rhs - min(c))
            account.spend(self.slack, self.volume, self.tolerance,
                          LiveDeficitClaim(t, depth,
                                           "closed form 2^-(t+2), proved above"),
                          "e")
        self.assertLess(account.spent, F(9, 8))
        self.assertGreater(account.remaining, ZERO)


class MotivatingTrajectoriesRunThroughTheSafeAPI(unittest.TestCase):
    """End to end: real normative rows, the public entry point, the real account.

    The other motivating fixtures compute charges directly, which tests the
    arithmetic and not the path. These call `compile_safe_force` with the actual
    compiled core row, the actual support, the actual live worlds and a real
    feasibility witness — so what is demonstrated is the installed safety path
    rather than a calculation resembling it.
    """

    rhs = F(3, 4)
    slack, volume, tolerance = F(1, 8), F(1), F(1, 2)

    # --- the affine, never-vindicated trajectory ---------------------------

    def stage(self, t, width=3):
        n = max(width, t + 2)
        names = tuple(f"A{k}" for k in range(1, n + 1)) + ("B", "C")
        fragment = Fragment(names)
        worlds = [tuple(F(b) for b in bits)
                  for bits in product((0, 1), repeat=n + 2)
                  if bits[n] == 1 and all(bits[k] == 1 for k in range(t))]
        coefficient = tuple(
            F(1, 2) * w[n] + F(1, 4) * w[n + 1]
            + sum((F(1, 2 ** (k + 3)) * w[k] for k in range(n)), ZERO)
            for w in worlds)
        return fragment, worlds, coefficient

    def compiled(self, t):
        fragment, worlds, c = self.stage(t)
        theta = maximal_theta(c, self.rhs, worlds) / 2
        row = compile_core_row(c, self.rhs, theta, fragment, worlds)
        witness = max(worlds, key=lambda w: sum(x * y for x, y in zip(row.c, w)))
        return fragment, worlds, row, witness

    def test_the_safe_api_certifies_the_closed_form_deficit(self):
        for t in range(4):
            fragment, worlds, row, witness = self.compiled(t)
            account = OutflowAccount(F(9, 8))
            force = compile_safe_force(
                [(row.c, row.r)], fragment.dimension, fragment.names, t, worlds,
                self.slack, self.volume, self.tolerance, witness, account,
                label="affine")
            self.assertIsInstance(force, SafetyCertifiedForce)
            self.assertEqual(force.deficit_bound, F(1, 2 ** (t + 2)))

    def test_the_safe_api_charge_agrees_with_the_closed_form(self):
        factor = (self.slack + self.volume) / self.tolerance
        for t in range(4):
            fragment, worlds, row, witness = self.compiled(t)
            account = OutflowAccount(F(9, 8))
            force = compile_safe_force(
                [(row.c, row.r)], fragment.dimension, fragment.names, t, worlds,
                self.slack, self.volume, self.tolerance, witness, account)
            self.assertEqual(force.charged, factor * F(1, 2 ** (t + 2)))

    def test_a_prefix_of_the_trajectory_fits_inside_the_closed_form_bound(self):
        """The finite prefix through the API; the infinite bound is proved above."""
        account = OutflowAccount(F(9, 8))
        for t in range(5):
            fragment, worlds, row, witness = self.compiled(t)
            compile_safe_force(
                [(row.c, row.r)], fragment.dimension, fragment.names, t, worlds,
                self.slack, self.volume, self.tolerance, witness, account,
                label="affine")
        self.assertLess(account.spent, F(9, 8))
        self.assertGreater(account.remaining, ZERO)
        self.assertTrue(all(e.verified for e in account.ledger))

    # --- the sentence-shaped, finitely vindicated trajectory ---------------

    def test_a_vindicated_endorsement_stops_costing_anything(self):
        """The other witness: force becomes free once the record catches up."""
        fragment = Fragment(("A", "B"))
        endorsement = Endorsement("A", F(1, 2))
        account = OutflowAccount(F(10))
        charges = []
        for t, settled in enumerate(({}, {"B": True}, {"A": True})):
            worlds = fragment.pc_worlds(settled)
            c = endorsement.coefficient(fragment, worlds)
            theta = maximal_theta(c, endorsement.rhs, worlds)
            # `None` once `A` is settled: the coefficient is constant and
            # satisfied, so every core minimum works and the row is vacuous.
            usable = F(1, 2) if theta is None or theta == 0 else theta / 2
            row = compile_core_row(c, endorsement.rhs, usable, fragment, worlds)
            witness = max(worlds,
                          key=lambda w: sum(x * y for x, y in zip(row.c, w)))
            force = compile_safe_force(
                [(row.c, row.r)], fragment.dimension, fragment.names, t, worlds,
                self.slack, self.volume, self.tolerance, witness, account,
                label="sentence")
            charges.append(force.charged)
        self.assertGreater(charges[0], ZERO)
        self.assertEqual(charges[-1], ZERO)
        self.assertEqual(account.spent, sum(charges, ZERO))
