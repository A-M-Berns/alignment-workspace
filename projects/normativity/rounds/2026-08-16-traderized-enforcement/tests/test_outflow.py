"""The outflow account, prosecuted before it is believed."""
import unittest
from fractions import Fraction as F
from itertools import permutations

from contract import declared_liability_bound
from enforcement import EnforcementTrader, Region, Row
from market import ONE, ZERO, dot, holdings_value
from contract import ForceDeclaration, certified_intensity
from deduction import world_deficit
from force_api import compile_force, compile_funded_force, compile_safe_force
from force_api import compile_safe_force
from outflow import (Insufficient, LiveDeficitCertificate, LiveDeficitClaim,
                     OutflowAccount, affordable_tolerance,
                     automatically_satisfied, charge, charge_is_conservative,
                     cumulative_certificate, is_nonvacuous, maximum_violation,
                     meaningful_dates_are_finite, positive_floor_dates,
                     presentation_key, proportional, quarantine, raw_charge,
                     relax, support_key)


def cert(total, date=0):
    """A claimed aggregate, for tests about the account's arithmetic alone."""
    return LiveDeficitClaim(date, F(total), "fixture")


def verified(region, worlds, support=("A",), date=0):
    return LiveDeficitCertificate.by_enumeration(date, region, support, worlds)


class PerEndorsementCapsDoNotAggregate(unittest.TestCase):
    """The counterexample that forces the account to be global.

    Every endorsement obeys a finite lifetime cap; exactly one is live at each
    date, so finite gating is obeyed everywhere; and the aggregate diverges.
    `for all e, B_e < infinity` does not give `sum_e B_e < infinity`, and the
    gap is walkable by a source that retires each endorsement as it admits the
    next.
    """

    def dates(self, n):
        return [dict(slack=F(1, 8), volume=F(7, 8), tolerance=F(1, 2),
                     certificate=cert(F(1))) for _ in range(n)]

    def test_each_endorsement_spends_a_finite_amount(self):
        # endorsement e is live only at date e, and spends this much, ever
        per_endorsement = charge(F(1, 8), F(7, 8), F(1, 2), cert(F(1)))
        self.assertEqual(per_endorsement, F(2))

    def test_finite_gating_is_obeyed(self):
        for d in self.dates(20):
            self.assertEqual(d["certificate"].aggregate, F(1))

    def test_the_aggregate_diverges(self):
        for n in (4, 40, 400):
            self.assertEqual(cumulative_certificate(self.dates(n)), 2 * n)

    def test_the_account_stops_it(self):
        """Global capital converts divergence into finitely many admissions."""
        account = OutflowAccount(F(9))
        admitted = 0
        for e in range(400):
            try:
                account.cap(f"e{e}", F(2))
                account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)), f"e{e}")
                admitted += 1
            except Insufficient:
                break
        self.assertEqual(admitted, 4)
        self.assertLessEqual(account.spent, account.capital)


class GatingIsNotALifetimeBound(unittest.TestCase):
    """Named regression: finite gating does not bound lifetime outflow.

    Gating bounds how many rows are live *per date*. Nothing in it bounds the
    number of dates, so a constitutional clause that cites gating for safety is
    claiming more than gating gives.
    """

    def test_bounded_rows_per_date_unbounded_total(self):
        rows_per_date = 3
        dates = [dict(slack=F(1, 8), volume=F(7, 8), tolerance=F(1, 2),
                      certificate=cert(F(rows_per_date))) for _ in range(100)]
        self.assertTrue(all(d["certificate"].aggregate <= rows_per_date
                            for d in dates))
        self.assertEqual(cumulative_certificate(dates), 600)


class SummableAllocationsGiveAFiniteCertificate(unittest.TestCase):

    def test_geometric_allocation_fits_inside_capital(self):
        account = OutflowAccount(F(1))
        for e in range(12):
            account.cap(f"e{e}", F(1, 2 ** (e + 1)))
        self.assertEqual(sum(account.allocations.values(), ZERO),
                         F(1) - F(1, 2 ** 12))

    def test_a_nonsummable_allocation_is_refused_at_admission(self):
        account = OutflowAccount(F(1))
        with self.assertRaises(Insufficient):
            for e in range(100):
                account.cap(f"e{e}", F(1, 10))

    def test_the_account_cannot_be_overspent(self):
        account = OutflowAccount(F(5))
        account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(2)))     # costs 4
        self.assertEqual(account.remaining, F(1))
        with self.assertRaises(Insufficient):
            account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)))  # would cost 2
        self.assertEqual(account.remaining, F(1))              # and did not


class AffordableTolerance(unittest.TestCase):
    """The force/safety tradeoff, as an equation rather than a warning."""

    def test_the_policy_inverts_the_charge_exactly(self):
        slack, volume, deficits, allowance = F(1, 8), F(7, 8), (F(3),), F(6)
        delta = affordable_tolerance(slack, volume, deficits, allowance)
        self.assertEqual(delta, F(1, 2))
        self.assertEqual(raw_charge(slack, volume, delta, deficits), allowance)

    def test_tighter_tolerance_costs_more(self):
        args = (F(1, 8), F(7, 8), (F(1),))
        self.assertGreater(raw_charge(*args[:2], F(1, 100), args[2]),
                           raw_charge(*args[:2], F(1, 2), args[2]))

    def test_a_free_date_is_reported_as_free_not_as_zero_tolerance(self):
        self.assertIsNone(affordable_tolerance(F(1, 8), F(7, 8), (ZERO,), F(1)))

    def test_an_unaffordable_date_needs_a_vacuous_promise(self):
        """`delta > 1` is unaffordable, not a tolerance to round down to 1."""
        needed = affordable_tolerance(F(1, 8), F(7, 8), (F(4),), F(1, 2))
        self.assertEqual(needed, F(8))
        self.assertGreater(needed, ONE)
        self.assertIsNone(relax(OutflowAccount(F(100)), F(1, 8), F(7, 8),
                                cert(F(4)), F(1, 1000), ceiling=ONE,
                                allowance=F(1, 2)))


class ExhaustionBehaviour(unittest.TestCase):

    def test_quarantine_withholds_force_and_spends_nothing(self):
        account = OutflowAccount(F(1))
        self.assertIsNone(
            quarantine(account, F(1, 8), F(7, 8), F(1, 2), cert(F(1))))
        self.assertEqual(account.spent, ZERO)

    def test_relaxation_buys_the_tightest_affordable_promise(self):
        account = OutflowAccount(F(4))
        granted = relax(account, F(1, 8), F(7, 8), cert(F(1)), F(1, 100), ceiling=ONE)
        self.assertEqual(granted, F(1, 4))
        self.assertEqual(account.remaining, ZERO)

    def test_weakening_the_core_minimum_does_not_reduce_the_charge(self):
        """The exhaustion behaviour that looks helpful and is not.

        The worst endorsement deficit is `max(0, r - m_c)`, which the declared
        core minimum does not appear in. Lowering `theta` weakens the demand on
        the reference and leaves the charge exactly where it was, so a protocol
        that answers exhaustion by weakening the core has not paid for anything.
        """
        from core import compile_core_row
        from deduction import world_deficit
        from market import Fragment
        fragment = Fragment(("A", "B"))
        worlds = [(F(0), F(0)), (F(1), F(0)), (F(0), F(1)), (F(1), F(1))]
        c = tuple(w[0] for w in worlds)
        charges = set()
        for theta in (F(1, 4), F(1, 2), F(3, 4)):
            row = compile_core_row(c, F(1, 2), theta, fragment, worlds)
            region = Region(2, [row])
            worst = max(sum(world_deficit(region, w), ZERO) for w in worlds)
            charges.add(raw_charge(F(1, 8), F(7, 8), F(1, 2), (worst,)))
        self.assertEqual(len(charges), 1)


class ProportionalSpendingNeverExhausts(unittest.TestCase):
    """The policy that needs no pre-declared schedule.

    Against a deficit that never decays and volume that grows without bound,
    the account still funds force at every date, forever, because each date
    takes a share of what is left. Force is never refused; it is progressively
    weakened. That is the substantive content of the tradeoff.
    """

    def test_the_capital_never_runs_out(self):
        account = OutflowAccount(F(1))
        for t in range(60):
            proportional(account, F(1, 8), F(t + 1), cert(F(1, 2)), F(1, 10 ** 9),
                         share=F(1, 2), ceiling=F(10 ** 9))
        self.assertLess(account.spent, F(1))
        self.assertGreater(account.remaining, ZERO)

    def test_but_the_promise_it_buys_goes_vacuous_anyway(self):
        """Never exhausting is not the same as keeping force available."""
        account = OutflowAccount(F(1))
        granted = [proportional(account, F(1, 8), F(t + 1), cert(F(1, 2)), F(1, 10 ** 9),
                                share=F(1, 2), ceiling=ONE) for t in range(30)]
        # with capital 1 against this deficit, not even date 0 is affordable
        self.assertEqual([t for t, g in enumerate(granted) if g is not None], [])

    def test_the_promise_it_buys_degrades(self):
        account = OutflowAccount(F(1))
        granted = [proportional(account, F(1, 8), F(t + 1), cert(F(1, 2)), F(1, 10 ** 9),
                                share=F(1, 2), ceiling=F(10 ** 9))
                   for t in range(20)]
        self.assertLess(granted[0], granted[10])
        self.assertLess(granted[10], granted[19])
        self.assertGreater(granted[0], ONE)       # vacuous from the first date

    def test_remaining_capital_decays_geometrically(self):
        account = OutflowAccount(F(1))
        for t in range(8):
            proportional(account, F(1, 8), F(t + 1), cert(F(1, 2)), F(1, 10 ** 9),
                         share=F(1, 2), ceiling=F(10 ** 6))
        self.assertEqual(account.remaining, F(1, 256))


class DepthOnlyImpossibilityIsWithdrawn(unittest.TestCase):
    """The theorem this round asserted and had to withdraw.

    It read: a date whose promise says anything needs `delta <= 1`, so it costs
    at least the exclusion deficit; hence a deficit bounded away from zero
    exhausts any finite account. The step is wrong. The charge is

        q_t = (eps_t + C_t) * D_t / delta_t ,

    and `delta_t <= 1` gives only `q_t >= (eps_t + C_t) * D_t`. The dropped
    factor is not bounded below, so persistent positive depth is affordable
    forever whenever ordinary aggregate pressure decays.
    """

    def test_the_counterexample_sums_to_less_than_one(self):
        """`D_t = 1/2`, `delta_t = 1`, `eps_t + C_t = 2^-t`, forever."""
        total = ZERO
        for t in range(200):
            total += charge(ZERO, F(1, 2 ** t), ONE, cert(F(1, 2)))
        self.assertLess(total, ONE)
        self.assertGreater(total, F(99, 100))

    def test_the_normative_distance_never_closes_in_it(self):
        for t in range(200):
            self.assertEqual(cert(F(1, 2)).aggregate, F(1, 2))

    def test_a_finite_account_funds_it_forever(self):
        account = OutflowAccount(ONE)
        for t in range(200):
            account.spend(ZERO, F(1, 2 ** t), ONE, cert(F(1, 2)))
        self.assertGreater(account.remaining, ZERO)

    def test_the_withdrawn_function_refuses_to_answer(self):
        with self.assertRaises(NotImplementedError):
            meaningful_dates_are_finite(F(1), F(1, 2))


class PositiveFloorsOnTwoFactorsDoBound(unittest.TestCase):
    """The corrected limitative theorem. All three hypotheses are load-bearing.

    A floor on the depth, a floor on the ordinary aggregate pressure, and a
    ceiling on the tolerance together put a positive floor `c*d/delta_bar` under
    every date's charge, and finitely many of those fit in finite capital. Drop
    any one and the bound is gone.
    """

    def test_the_count_is_capital_times_ceiling_over_the_product(self):
        self.assertEqual(positive_floor_dates(F(100), F(1, 2), ONE, ONE), 200)
        self.assertEqual(positive_floor_dates(F(100), F(1, 2), ONE, F(2)), 400)

    def test_it_agrees_with_a_realized_run(self):
        account, funded = OutflowAccount(F(9)), 0
        while True:
            try:
                account.spend(F(1, 8), F(7, 8), ONE, cert(F(1, 2)))
                funded += 1
            except Insufficient:
                break
        self.assertLessEqual(funded,
                             positive_floor_dates(F(9), F(1, 2), ONE, ONE))

    def test_dropping_the_pressure_floor_breaks_it(self):
        with self.assertRaises(ValueError):
            positive_floor_dates(F(1), F(1, 2), ZERO, ONE)

    def test_dropping_the_depth_floor_breaks_it(self):
        with self.assertRaises(ValueError):
            positive_floor_dates(F(1), ZERO, ONE, ONE)

    def test_a_looser_tolerance_ceiling_buys_proportionally_more_dates(self):
        self.assertEqual(positive_floor_dates(F(100), F(1, 2), ONE, F(10)),
                         10 * positive_floor_dates(F(100), F(1, 2), ONE, ONE))


class PersistentDepthAgainstDecayingPressure(unittest.TestCase):
    """The third route to indefinite affordability, and the one that was missed.

    Normative distance stays exactly where it is, forever. The tolerance stays
    at its tightest meaningful value, forever. And the account holds, because
    ordinary aggregate pressure decays. Named regression against the withdrawn
    depth-only theorem.
    """

    def dates(self, n):
        return [dict(slack=ZERO, volume=F(1, 2 ** t), tolerance=ONE,
                     certificate=cert(F(1, 2))) for t in range(n)]

    def test_depth_and_tolerance_are_both_pinned(self):
        for d in self.dates(50):
            self.assertEqual(d["certificate"].aggregate, F(1, 2))
            self.assertEqual(d["tolerance"], ONE)

    def test_the_certificate_stays_under_one_at_every_horizon(self):
        for n in (10, 100, 400):
            self.assertLess(cumulative_certificate(self.dates(n)), ONE)


class ForeverUnvindicatedAndSafe(unittest.TestCase):
    """An **abstract force-source witness**: the deficit schedule is stipulated.

    What it establishes is that the force/safety mechanism admits a trajectory
    with indefinite nonvacuous force and finite cost. It does **not** establish
    that the motivating settlement/core statics generate one — that is a separate
    question, answered affirmatively by
    `test_normative.StaticsGenerateAForeverUnvindicatedTrajectory`, and answered
    negatively for sentence-indicator endorsements by
    `test_normative.BooleanEndorsementsJumpToZero`.

    The fixture that separates safety from deductive resolution.

    The endorsement is never vindicated: its exclusion deficit is positive at
    every date, forever. It receives force at a fixed nonvacuous tolerance,
    forever. Ordinary volume grows without bound. And the account holds, because
    the deficit decays geometrically against a linearly growing volume.

    So the safety story is not "everything normative must eventually settle". It
    is "unresolved disagreement must be resisted with summably decreasing
    force", which is a different and much weaker demand.
    """

    def dates(self, n):
        return [dict(slack=F(1, 8), volume=F(t + 1), tolerance=F(1, 2),
                     certificate=cert(F(1, 2 ** t))) for t in range(n)]

    def test_the_deficit_never_reaches_zero(self):
        self.assertTrue(all(d["certificate"].aggregate > 0 for d in self.dates(50)))

    def test_the_tolerance_is_nonvacuous_and_constant(self):
        self.assertTrue(all(d["tolerance"] == F(1, 2) for d in self.dates(50)))

    def test_the_certificate_is_bounded_by_the_closed_form(self):
        # sum_t 2 (t + 9/8) 2^-t  =  17/2
        for n in (10, 40, 120):
            self.assertLess(cumulative_certificate(self.dates(n)), F(17, 2))
        self.assertGreater(cumulative_certificate(self.dates(120)), F(8))

    def test_a_finite_account_funds_it_forever(self):
        account = OutflowAccount(F(17, 2))
        for t, d in enumerate(self.dates(120)):
            account.spend(**d, label=f"t{t}")
        self.assertGreater(account.remaining, ZERO)


class PersistentDeficitDefeatsTheCertificate(unittest.TestCase):
    """The contrast: a deficit that does not decay is unaffordable at any capital.

    Level-A *and* level-B. The declared certificate diverges, and so does the
    realized cumulative loss at a single world followed across dates, against
    prices that satisfy the market maker's contract at every date.
    """

    def setUp(self):
        self.region = Region(1, [Row([F(1)], F(1, 2))])
        self.world = (ZERO,)                       # excluded, and assessed
        self.price = (F(1, 4),)                    # a violating price

    def test_the_certificate_diverges(self):
        dates = [dict(slack=F(1, 8), volume=F(t + 1), tolerance=F(1, 2),
                      certificate=cert(F(1, 2))) for t in range(60)]
        totals = [cumulative_certificate(dates[:n]) for n in (10, 20, 40)]
        self.assertLess(totals[0], totals[1])
        self.assertLess(totals[1], totals[2])
        self.assertGreater(totals[2], 800)

    def test_the_realized_loss_at_one_followed_world_diverges(self):
        """Not merely a failure to certify: an actual divergent trajectory."""
        running, seen = ZERO, []
        for t in range(40):
            beta = (F(1, 8) + F(t + 1)) / F(1, 2) ** 2
            position = EnforcementTrader(self.region, beta).coefficients(self.price)
            running += holdings_value(position, self.price, self.world)
            seen.append(running)
        self.assertLess(seen[0], ZERO)
        self.assertLess(seen[-1], seen[len(seen) // 2])
        # position ~ beta*g*c = t + 9/8, valued at -1/4 each date: quadratic
        self.assertEqual(seen[-1], F(-825, 4))
        self.assertEqual(seen[19], F(-425, 8))
        self.assertGreater(seen[19] / seen[-1], F(1, 5))   # superlinear

    def test_no_finite_account_funds_it(self):
        account = OutflowAccount(F(1000))
        with self.assertRaises(Insufficient):
            for t in range(60):
                account.spend(F(1, 8), F(t + 1), F(1, 2), cert(F(1, 2)))


class ChargeIsAdditiveOverRowsAndConservativeOverWorlds(unittest.TestCase):

    def test_the_certificate_decomposes_additively_over_rows(self):
        slack, volume, delta = F(1, 8), F(7, 8), F(1, 2)
        deficits = (F(1), F(2), F(3))
        merged = raw_charge(slack, volume, delta, deficits)
        parts = sum(raw_charge(slack, volume, delta, (d,)) for d in deficits)
        self.assertEqual(merged, parts)

    def test_settlement_rows_contribute_nothing(self):
        slack, volume, delta = F(1, 8), F(7, 8), F(1, 2)
        self.assertEqual(raw_charge(slack, volume, delta, (F(1), ZERO, ZERO)),
                         raw_charge(slack, volume, delta, (F(1),)))

    def test_the_charge_dominates_a_followed_world(self):
        dates = [dict(slack=F(1, 8), volume=F(7, 8), tolerance=F(1, 2),
                      certificate=cert(F(1, 2))) for _ in range(10)]
        region = Region(1, [Row([F(1)], F(1, 2))])
        beta = (F(1, 8) + F(7, 8)) / F(1, 2) ** 2
        price, world = (F(1, 4),), (ZERO,)
        step = holdings_value(
            EnforcementTrader(region, beta).coefficients(price), price, world)
        self.assertTrue(charge_is_conservative(dates, [step] * 10))

    def test_the_certificate_is_strictly_conservative(self):
        """It maximizes over live worlds per date; the criterion follows one."""
        dates = [dict(slack=F(1, 8), volume=F(7, 8), tolerance=F(1, 2),
                      certificate=cert(F(1, 2))) for _ in range(10)]
        region = Region(1, [Row([F(1)], F(1, 2))])
        beta = (F(1, 8) + F(7, 8)) / F(1, 2) ** 2
        price, world = (F(1, 4),), (ZERO,)
        step = holdings_value(
            EnforcementTrader(region, beta).coefficients(price), price, world)
        self.assertLess(-10 * step, cumulative_certificate(dates))


class PresentationChangesTheInstalledCompiler(unittest.TestCase):
    """What the installed `ForceDeclaration` actually does to row presentation.

    A previous version of this class claimed invariance under rescaling *and*
    duplication. It tested a compiler retuned for the occasion — dividing the
    intensity by the row count — where the installed one uses a uniform
    `beta_j = (eps + C) / delta^2` for every row. The retuning was the whole
    content of the result, so the claim was about a compiler nobody calls.

    Held to the installed compiler at a **fixed declared tolerance**, neither
    operation is neutral.
    """

    slack, volume = F(1, 8), F(7, 8)
    price, world = (F(1, 4),), (ZERO,)
    base = Row([F(1)], F(1, 2))

    def emitted(self, rows, tolerance):
        d = ForceDeclaration(Region(1, rows), self.volume, self.slack, tolerance)
        return (d.trader().coefficients(self.price)[0],
                d.liability_bound(self.price, self.world),
                raw_charge(self.slack, self.volume, tolerance,
                           world_deficit(Region(1, rows), self.world)))

    def test_duplication_scales_position_and_charge_linearly(self):
        one = self.emitted([self.base], F(1, 2))
        two = self.emitted([self.base] * 2, F(1, 2))
        four = self.emitted([self.base] * 4, F(1, 2))
        self.assertEqual(one, (F(1), F(1, 2), F(1)))
        self.assertEqual(two, (F(2), F(1), F(2)))
        self.assertEqual(four, (F(4), F(2), F(4)))

    def test_rescaling_scales_position_and_liability_quadratically(self):
        one = self.emitted([self.base], F(1, 2))
        two = self.emitted([Row([F(2)], F(1))], F(1, 2))
        self.assertEqual(one[0], F(1))
        self.assertEqual(two[0], F(4))
        self.assertEqual(two[1], 4 * one[1])

    def test_a_redundant_nonduplicate_row_also_changes_the_force(self):
        """Presentation dependence is general, not an artifact of duplication.

        `p_A >= 1/2` and `p_B >= 1/2` already imply `p_A + p_B >= 1`. Adding the
        implied row leaves the admissible set exactly where it was and triples
        the emitted position.
        """
        a = Row([F(1), F(0)], F(1, 2))
        b = Row([F(0), F(1)], F(1, 2))
        implied = Row([F(1), F(1)], F(1))
        price = (F(1, 4), F(1, 4))
        without = ForceDeclaration(Region(2, [a, b]), self.volume, self.slack,
                                   F(1, 2))
        with_ = ForceDeclaration(Region(2, [a, b, implied]), self.volume,
                                 self.slack, F(1, 2))
        self.assertEqual(without.region.contains((F(1, 2), F(1, 2))),
                         with_.region.contains((F(1, 2), F(1, 2))))
        self.assertEqual(without.trader().coefficients(price), (F(1), F(1)))
        self.assertEqual(with_.trader().coefficients(price), (F(3), F(3)))

    def test_rescaling_is_neutral_at_a_matched_actual_conformance_target(self):
        """The half that survives: rescaling is a genuine reparametrization.

        A row scaled by `lambda` measures its own violation in units `lambda`
        times finer, so declaring `lambda * eta` asks for the same actual
        conformance `eta`. At matched targets the position, the realized
        liability and the charge all agree — so a source gains nothing by
        rescaling, provided the tolerance is read in the row's own units.
        """
        plain = self.emitted([self.base], F(1, 4))
        scaled = self.emitted([Row([F(2)], F(1))], F(1, 2))
        self.assertEqual(plain, scaled)

    def test_duplication_is_not_neutral_even_at_matched_conformance(self):
        """The half that does not: duplication is redundancy and it is billed.

        `k` copies make the weighted square `k` times larger, so the actual
        conformance is `delta / sqrt(k)` — matched only at square `k`, and then
        the position and realized liability agree while the **charge** does not,
        because the certificate sums the same deficit once per copy.
        """
        one = self.emitted([self.base], F(1, 4))
        four = self.emitted([self.base] * 4, F(1, 2))
        self.assertEqual(one[0], four[0])            # position agrees
        self.assertEqual(one[1], four[1])            # realized liability agrees
        self.assertEqual(four[2], 2 * one[2])        # the charge does not
        self.assertGreaterEqual(four[2], four[1])    # still sound, just dearer


class SharpAndRowwiseAggregates(unittest.TestCase):
    """`sup_w sum_j d_j(w)` against `sum_j sup_w d_j(w)`, which differ.

    Two rows pinning a single price from opposite sides are worst at opposite
    worlds and cannot be violated together at any world. The rowwise aggregate
    charges as though they could.
    """

    region = Region(1, [Row([F(1)], F(1, 2)), Row([F(-1)], F(-1, 2))])
    worlds = [(ZERO,), (F(1),)]

    def certificate(self):
        return LiveDeficitCertificate.by_enumeration(0, self.region, ("A",), self.worlds)

    def test_the_gap_is_a_clean_factor_of_two(self):
        c = self.certificate()
        self.assertEqual(c.aggregate, F(1, 2))
        self.assertEqual(c.rowwise, F(1))

    def test_billing_rowwise_costs_twice_as_much(self):
        c = self.certificate()
        self.assertEqual(charge(F(1, 8), F(7, 8), F(1, 2), c, sharp=False),
                         2 * charge(F(1, 8), F(7, 8), F(1, 2), c, sharp=True))

    def test_enumeration_marks_the_certificate_verified(self):
        self.assertTrue(self.certificate().verified)
        self.assertIn("enumeration", self.certificate().basis)

    def test_a_claim_is_a_different_type_and_needs_an_author(self):
        self.assertFalse(LiveDeficitClaim(0, F(1), "why").verified)
        with self.assertRaises(ValueError):
            LiveDeficitClaim(0, F(1), "")


class FundedForceCannotBypassTheAccount(unittest.TestCase):
    """The integration the account was missing.

    `compile_force` promises conformance and emits an obligation. Until the
    funded entry point existed, nothing in the API made it hard to read the
    first as the second.
    """

    rows = [([F(1)], F(1, 2))]
    region = Region(1, [Row([F(1)], F(1, 2))])
    worlds = [(ZERO,), (F(1),)]

    def safe(self, account, tolerance=F(1, 2), **kw):
        return compile_safe_force(self.rows, 1, ("A",), 0, self.worlds,
                                  F(1, 8), F(7, 8), tolerance, (F(1),),
                                  account, **kw)

    def test_raw_compile_force_carries_no_charge_and_says_so(self):
        c = compile_force(self.rows, 1, F(1, 8), F(7, 8), F(1, 2), (F(1),))
        self.assertFalse(hasattr(c, "charged"))

    def test_safe_force_pays_before_it_emits(self):
        account = OutflowAccount(F(10))
        c = self.safe(account)
        self.assertEqual(c.charged, F(1))
        self.assertEqual(account.remaining, F(9))
        self.assertTrue(c.deficit_is_verified)

    def test_an_unaffordable_request_is_quarantined_by_default(self):
        account = OutflowAccount(F(1, 100))
        self.assertIsNone(self.safe(account))
        self.assertEqual(account.spent, ZERO)

    def test_refusal_is_available_on_request(self):
        account = OutflowAccount(F(1, 100))
        with self.assertRaises(Insufficient):
            self.safe(account, policy="refuse")
        self.assertEqual(account.spent, ZERO)

    def test_quarantine_returns_nothing_and_spends_nothing(self):
        account = OutflowAccount(F(1, 100))
        self.assertIsNone(self.safe(account, policy="quarantine"))
        self.assertEqual(account.spent, ZERO)

    def test_relaxation_emits_at_the_affordable_tolerance(self):
        account = OutflowAccount(F(4))
        c = self.safe(account, tolerance=F(1, 100), policy="relax")
        self.assertEqual(c.tolerance, F(1, 8))
        self.assertTrue(c.relaxed)
        self.assertEqual(account.remaining, ZERO)

    def test_the_certificate_is_computed_from_the_region_it_enforces(self):
        account = OutflowAccount(F(10))
        c = self.safe(account)
        self.assertEqual(c.presentation,
                         presentation_key(Region(1, [Row([F(1)], F(1, 2))])))
        self.assertEqual(c.support, support_key(("A",)))
        self.assertIn("enumeration", c.deficit_basis)

    def test_it_exposes_its_proof_ingredients(self):
        account = OutflowAccount(F(10))
        keys = set(self.safe(account).ingredients())
        self.assertLessEqual({"date", "support", "presentation", "assessment",
                              "deficit_bound", "deficit_basis", "slack",
                              "volume", "tolerance", "charge", "safety_bound",
                              "remaining", "policy"}, keys)

    def test_the_feasibility_witness_is_still_checked(self):
        account = OutflowAccount(F(10))
        with self.assertRaises(ValueError):
            compile_safe_force(self.rows, 1, ("A",), 0, self.worlds, F(1, 8),
                               F(7, 8), F(1, 2), (ZERO,), account)


class Subaccounts(unittest.TestCase):

    def test_an_endorsement_cannot_spend_past_its_reservation(self):
        account = OutflowAccount(F(100))
        account.cap("e1", F(4))
        account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)), "e1")
        account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)), "e1")
        with self.assertRaises(Insufficient):
            account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)), "e1")
        self.assertEqual(account.spent, F(4))

    def test_one_endorsement_cannot_spend_anothers_reservation(self):
        account = OutflowAccount(F(8))
        account.cap("e1", F(4))
        account.cap("e2", F(4))
        for _ in range(2):
            account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)), "e1")
        with self.assertRaises(Insufficient):
            account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)), "e1")
        account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)), "e2")

    def test_an_unallocated_label_spends_against_global_capital_only(self):
        account = OutflowAccount(F(4))
        account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)), "anonymous")
        self.assertEqual(account.remaining_for("anonymous"), F(2))


class Replenishment(unittest.TestCase):
    """Unbounded refilling voids the theorem, so the API does not offer it."""

    def test_the_default_account_refuses_replenishment(self):
        with self.assertRaises(Insufficient):
            OutflowAccount(F(10)).replenish(F(1))

    def test_a_declared_ceiling_bounds_total_capital(self):
        account = OutflowAccount(F(10), lifetime_ceiling=F(12))
        account.replenish(F(2))
        self.assertEqual(account.capital, F(12))
        with self.assertRaises(Insufficient):
            account.replenish(F(1))

    def test_repeated_replenishment_cannot_reach_infinity(self):
        account = OutflowAccount(F(1), lifetime_ceiling=F(2))
        for _ in range(50):
            try:
                account.replenish(F(1, 10))
            except Insufficient:
                break
        self.assertLessEqual(account.capital, F(2))

    def test_a_ceiling_below_the_initial_capital_is_refused(self):
        with self.assertRaises(ValueError):
            OutflowAccount(F(10), lifetime_ceiling=F(5))


class ZeroDisturbanceIntensity(unittest.TestCase):
    """`eps = C = 0` made the certified intensity zero, which enforces nothing."""

    def test_the_intensity_is_positive(self):
        self.assertEqual(certified_intensity(ZERO, ZERO, F(1, 2)), ONE)

    def test_it_forces_exact_conformance_rather_than_the_declared_tolerance(self):
        d = ForceDeclaration(Region(1, [Row([F(1)], F(1, 2))]), ZERO, ZERO,
                             F(1, 2))
        self.assertGreater(d.budget_consumed((F(1, 4),)), ZERO)
        self.assertEqual(d.budget_consumed((F(1, 2),)), ZERO)

    def test_a_positive_disturbance_is_unaffected(self):
        self.assertEqual(certified_intensity(F(1, 8), F(7, 8), F(1, 2)), F(4))


class CertificateSubstitution(unittest.TestCase):
    """The attack this pass exists to close, and the binding that closes it.

    Before the repair, a `verified` certificate computed for `p >= 0` — whose
    live-world aggregate is honestly zero, because nothing can violate it — could
    be paid against enforcement of `p >= 1/2`. The account was charged nothing,
    the position was emitted anyway, and it really lost at a live world. Repeat
    forever and the cumulative liability diverges while the holder quotes a
    finite `B`.
    """

    worlds = [(ZERO,), (F(1),)]
    easy = Region(1, [Row([F(1)], ZERO)])
    hard_rows = [([F(1)], F(1, 2))]
    hard = Region(1, [Row([F(1)], F(1, 2))])

    def easy_certificate(self, date=0, support=("A",)):
        return LiveDeficitCertificate.by_enumeration(date, self.easy, support,
                                                     self.worlds)

    def test_the_easy_certificate_is_honestly_zero_and_verified(self):
        c = self.easy_certificate()
        self.assertEqual(c.aggregate, ZERO)
        self.assertTrue(c.verified)

    def test_the_emitted_position_really_loses_at_a_live_world(self):
        """What made the substitution an undercharge rather than a mislabel."""
        account = OutflowAccount(F(10))
        force = compile_safe_force(self.hard_rows, 1, ("A",), 0, self.worlds,
                                   F(1, 8), F(7, 8), F(1, 2), (F(1),), account)
        price = (F(1, 4),)
        self.assertLess(holdings_value(force.position(price), price, (ZERO,)),
                        ZERO)

    def funded(self, account, certificate, worlds=None):
        return compile_funded_force(
            self.hard_rows, 1, ("A",), 0,
            self.worlds if worlds is None else worlds,
            F(1, 8), F(7, 8), F(1, 2), (F(1),), account, certificate)

    def test_a_certificate_for_another_region_cannot_fund_this_one(self):
        account = OutflowAccount(F(10))
        with self.assertRaises(ValueError) as caught:
            self.funded(account, self.easy_certificate())
        self.assertIn("presentation", str(caught.exception))
        self.assertEqual(account.spent, ZERO)

    def test_a_certificate_from_another_assessment_cannot_fund_this_request(self):
        """The fourth identity, which `binds` did not check.

        Same date, same support, same row presentation — and a different live
        set. The narrow assessment `{A = 1}` has aggregate `0` where the wide
        one has `1/2`, so substituting it funded the wide request for nothing.
        """
        narrow = LiveDeficitCertificate.by_enumeration(0, self.hard, ("A",),
                                                       [(F(1),)])
        self.assertEqual(narrow.aggregate, ZERO)
        self.assertIsNone(narrow.binds(0, self.hard, ("A",), [(F(1),)]))
        self.assertEqual(narrow.binds(0, self.hard, ("A",), self.worlds),
                         "live-world assessment state")
        account = OutflowAccount(F(10))
        with self.assertRaises(ValueError) as caught:
            self.funded(account, narrow)
        self.assertIn("assessment", str(caught.exception))
        self.assertEqual(account.spent, ZERO)

    def test_a_duplicated_presentation_cannot_fund_a_deduplicated_one(self):
        """Duplicates change the emitted force, so they change the identity."""
        account = OutflowAccount(F(100))
        doubled = Region(1, [Row([F(1)], F(1, 2))] * 2)
        c = LiveDeficitCertificate.by_enumeration(0, doubled, ("A",),
                                                  self.worlds)
        self.assertIsNone(c.binds(0, doubled, ("A",), self.worlds))
        self.assertIsNotNone(c.binds(0, self.hard, ("A",), self.worlds))
        with self.assertRaises(ValueError):
            self.funded(account, c)

    def test_row_order_is_not_operative_and_binds_across_permutations(self):
        """Corrected: permutation only permutes summands, so it is canonicalized.

        The compiled position is `Σ_j β_j g_j(P) c_j` at uniform intensity and
        the certified aggregate is `sup_ω Σ_j d_j(ω)`. Both are sums over rows.
        An earlier version bound row order and called it operative.
        """
        a, b = Row([F(1), F(0)], F(1, 2)), Row([F(0), F(1)], F(1, 4))
        forward, backward = Region(2, [a, b]), Region(2, [b, a])
        worlds = [(ZERO, ZERO), (F(1), F(1))]
        c = LiveDeficitCertificate.by_enumeration(0, forward, ("A", "B"), worlds)
        self.assertIsNone(c.binds(0, forward, ("A", "B"), worlds))
        self.assertIsNone(c.binds(0, backward, ("A", "B"), worlds))

    def test_permuting_the_support_invalidates_the_certificate(self):
        """The world vectors are unchanged; what they mean is not."""
        region = Region(2, [Row([F(1), F(0)], F(1, 2))])
        worlds = [(ZERO, F(1)), (F(1), ZERO)]
        c = LiveDeficitCertificate.by_enumeration(0, region, ("A", "B"), worlds)
        self.assertIsNone(c.binds(0, region, ("A", "B"), worlds))
        self.assertIsNotNone(c.binds(0, region, ("B", "A"), worlds))

    def test_a_later_certificate_cannot_fund_earlier_force(self):
        """Live sets shrink, so a later certificate is cheaper."""
        later = LiveDeficitCertificate.by_enumeration(5, self.hard, ("A",),
                                                      [(F(1),)])
        early = LiveDeficitCertificate.by_enumeration(0, self.hard, ("A",),
                                                      self.worlds)
        self.assertEqual(later.aggregate, ZERO)
        self.assertGreater(early.aggregate, ZERO)
        self.assertIsNotNone(later.binds(0, self.hard, ("A",), self.worlds))
        account = OutflowAccount(F(10))
        with self.assertRaises(ValueError):
            self.funded(account, later)
        self.assertEqual(account.spent, ZERO)

    def test_a_different_assessment_at_the_same_date_is_a_different_key(self):
        wide = LiveDeficitCertificate.by_enumeration(0, self.hard, ("A",),
                                                     self.worlds)
        narrow = LiveDeficitCertificate.by_enumeration(0, self.hard, ("A",),
                                                       [(F(1),)])
        self.assertNotEqual(wide.live_worlds, narrow.live_worlds)
        self.assertNotEqual(wide.aggregate, narrow.aggregate)

    def test_the_enumeration_order_of_live_worlds_is_not_operative(self):
        one = LiveDeficitCertificate.by_enumeration(0, self.hard, ("A",),
                                                    self.worlds)
        other = LiveDeficitCertificate.by_enumeration(
            0, self.hard, ("A",), list(reversed(self.worlds)))
        self.assertEqual(one.live_worlds, other.live_worlds)

    def test_verified_cannot_be_forged_by_the_ordinary_constructor(self):
        with self.assertRaises(TypeError):
            LiveDeficitCertificate(None, 0, ZERO, ZERO, (), (), (), "forged")

    def test_a_claim_cannot_produce_safety_certified_force(self):
        account = OutflowAccount(F(10))
        with self.assertRaises(TypeError):
            self.funded(account, LiveDeficitClaim(0, F(1, 1000), "my proof"))
        self.assertEqual(account.spent, ZERO)

    def test_a_claim_may_still_price_a_request(self):
        """Planning is legitimate; only certifying is not."""
        self.assertEqual(charge(F(1, 8), F(7, 8), F(1, 2),
                                LiveDeficitClaim(0, F(1), "planning")), F(2))


class RelaxOnlyLoosens(unittest.TestCase):
    """Relaxation must not strengthen force the caller did not ask for."""

    worlds = [(ZERO,), (F(1),)]
    rows = [([F(1)], F(1, 2))]

    def test_an_affordable_request_is_emitted_as_requested(self):
        account = OutflowAccount(F(100))
        c = compile_safe_force(self.rows, 1, ("A",), 0, self.worlds, F(1, 8),
                               F(7, 8), F(1, 2), (F(1),), account,
                               policy="relax")
        self.assertEqual(c.tolerance, F(1, 2))
        self.assertFalse(c.relaxed)
        self.assertEqual(c.charged, F(1))
        self.assertEqual(account.remaining, F(99))

    def test_it_does_not_spend_the_whole_allowance_on_an_affordable_request(self):
        account = OutflowAccount(F(100))
        compile_safe_force(self.rows, 1, ("A",), 0, self.worlds, F(1, 8),
                           F(7, 8), F(1, 2), (F(1),), account, policy="relax")
        self.assertGreater(account.remaining, F(98))

    def test_an_unaffordable_request_is_loosened_and_never_tightened(self):
        account = OutflowAccount(F(4))
        c = compile_safe_force(self.rows, 1, ("A",), 0, self.worlds, F(1, 8),
                               F(7, 8), F(1, 100), (F(1),), account,
                               policy="relax")
        self.assertGreater(c.tolerance, F(1, 100))
        self.assertTrue(c.relaxed)


class LedgerIsAuditable(unittest.TestCase):

    def test_entries_identify_the_force_that_consumed_the_account(self):
        account = OutflowAccount(F(10))
        compile_safe_force([([F(1)], F(1, 2))], 1, ("A",), 3,
                           [(ZERO,), (F(1),)], F(1, 8), F(7, 8), F(1, 2),
                           (F(1),), account, label="e1")
        entry, = account.ledger
        self.assertEqual(entry.label, "e1")
        self.assertEqual(entry.date, 3)
        self.assertTrue(entry.verified)
        self.assertEqual(entry.cost, F(1))
        self.assertEqual(entry.remaining, F(9))
        self.assertEqual(entry.presentation,
                         presentation_key(Region(1, [Row([F(1)], F(1, 2))])))

    def test_a_claimed_charge_is_recorded_as_claimed(self):
        account = OutflowAccount(F(10))
        account.spend(F(1, 8), F(7, 8), F(1, 2), cert(F(1)), "planning")
        self.assertFalse(account.ledger[0].verified)


class RowPermutationIsInvariant(unittest.TestCase):
    """Derived, and now canonicalized in the presentation key.

    `E(P) = Σ_j β_j g_j(P) c_j` at uniform intensity and
    `D = sup_ω Σ_j d_j(ω)` are both sums over rows, so a permutation permutes
    summands and moves neither. Multiplicity is a different matter and is kept.
    """

    rows = [Row([F(1), F(0)], F(1, 2)), Row([F(0), F(1)], F(1, 4)),
            Row([F(1), F(1)], F(1, 3))]
    price, world = (F(1, 8), F(1, 8)), (ZERO, ZERO)
    worlds = [(ZERO, ZERO), (F(1), ZERO), (ZERO, F(1)), (F(1), F(1))]

    def test_position_and_liability_are_identical_across_permutations(self):
        seen = set()
        for order in permutations(self.rows):
            d = ForceDeclaration(Region(2, list(order)), F(7, 8), F(1, 8),
                                 F(1, 2))
            seen.add((d.trader().coefficients(self.price),
                      d.budget_consumed(self.price),
                      d.liability_bound(self.price, self.world)))
        self.assertEqual(len(seen), 1)

    def test_the_certified_aggregate_is_identical_across_permutations(self):
        seen = set()
        for order in permutations(self.rows):
            c = LiveDeficitCertificate.by_enumeration(
                0, Region(2, list(order)), ("A", "B"), self.worlds)
            seen.add((c.aggregate, c.rowwise))
        self.assertEqual(len(seen), 1)

    def test_the_presentation_key_is_permutation_invariant(self):
        keys = {presentation_key(Region(2, list(order)))
                for order in permutations(self.rows)}
        self.assertEqual(len(keys), 1)

    def test_but_multiplicity_still_distinguishes(self):
        one = presentation_key(Region(1, [Row([F(1)], F(1, 2))]))
        two = presentation_key(Region(1, [Row([F(1)], F(1, 2))] * 2))
        self.assertNotEqual(one, two)

    def test_a_certificate_binds_after_a_pure_permutation(self):
        forward = Region(2, list(self.rows))
        backward = Region(2, list(reversed(self.rows)))
        c = LiveDeficitCertificate.by_enumeration(0, forward, ("A", "B"),
                                                  self.worlds)
        self.assertIsNone(c.binds(0, backward, ("A", "B"), self.worlds))


if __name__ == "__main__":
    unittest.main()


class MeaningfulForceIsScaleRelative(unittest.TestCase):
    """`delta <= 1` is not presentation-independent, so it cannot define vacuity.

    Scaling a row by `lambda` scales its violations by `lambda`. A tolerance of
    `1` against `p >= 1/2` is vacuous — no price can violate that row by more
    than `1/2` — and against `2p >= 20` it is tight. The invariant notion is
    relative to the largest violation the row can attain.
    """

    def test_the_cube_maximum_violation(self):
        self.assertEqual(maximum_violation(Region(1, [Row([F(1)], F(1, 2))])),
                         F(1, 2))
        self.assertEqual(maximum_violation(Region(1, [Row([F(2)], F(1))])), F(1))
        self.assertEqual(
            maximum_violation(Region(1, [Row([F(-1)], F(-1, 2))])), F(1, 2))

    def test_tolerance_one_is_vacuous_on_the_plain_row(self):
        self.assertFalse(is_nonvacuous(Region(1, [Row([F(1)], F(1, 2))]), ONE))

    def test_the_same_tolerance_is_meaningful_on_a_scaled_row(self):
        self.assertTrue(is_nonvacuous(Region(1, [Row([F(10)], F(5))]), ONE))

    def test_the_judgement_scales_with_the_presentation(self):
        for lam in (F(1), F(2), F(10)):
            region = Region(1, [Row([lam], lam * F(1, 2))])
            self.assertTrue(is_nonvacuous(region, lam * F(1, 8)))
            self.assertFalse(is_nonvacuous(region, lam * F(1, 2)))

    def test_an_automatically_satisfied_region_is_not_nonvacuous(self):
        """Two concepts, no longer sharing one boolean.

        `p >= 0` cannot be violated anywhere in the cube. The promise "your
        violation is at most delta" is true and empty there, so the honest
        answer is that no tolerance is meaningful and enforcement is
        unnecessary — not that every tolerance is meaningful, which is what the
        predicate used to say.
        """
        free = Region(1, [Row([F(1)], ZERO)])
        self.assertTrue(automatically_satisfied(free))
        self.assertFalse(is_nonvacuous(free, ONE))
        self.assertFalse(is_nonvacuous(free, F(1, 1000)))
        self.assertFalse(automatically_satisfied(Region(1, [Row([F(1)], F(1, 2))])))
