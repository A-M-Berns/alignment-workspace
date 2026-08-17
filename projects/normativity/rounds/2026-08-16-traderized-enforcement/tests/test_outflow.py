"""The outflow account, prosecuted before it is believed."""
import unittest
from fractions import Fraction as F

from contract import declared_liability_bound
from enforcement import EnforcementTrader, Region, Row
from market import ONE, ZERO, dot, holdings_value
from outflow import (Insufficient, OutflowAccount, affordable_tolerance,
                     charge, charge_is_conservative, cumulative_certificate,
                     meaningful_dates_are_finite, proportional, quarantine,
                     relax)


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
                     deficits=(F(1),)) for _ in range(n)]

    def test_each_endorsement_spends_a_finite_amount(self):
        # endorsement e is live only at date e, and spends this much, ever
        per_endorsement = charge(F(1, 8), F(7, 8), F(1, 2), (F(1),))
        self.assertEqual(per_endorsement, F(2))

    def test_finite_gating_is_obeyed(self):
        for d in self.dates(20):
            self.assertEqual(len(d["deficits"]), 1)

    def test_the_aggregate_diverges(self):
        for n in (4, 40, 400):
            self.assertEqual(cumulative_certificate(self.dates(n)), 2 * n)

    def test_the_account_stops_it(self):
        """Global capital converts divergence into finitely many admissions."""
        account = OutflowAccount(F(9))
        admitted = 0
        for e in range(400):
            try:
                account.allocate(f"e{e}", F(2))
                account.spend(F(1, 8), F(7, 8), F(1, 2), (F(1),), f"e{e}")
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
                      deficits=(F(1),) * rows_per_date) for _ in range(100)]
        self.assertTrue(all(len(d["deficits"]) <= rows_per_date for d in dates))
        self.assertEqual(cumulative_certificate(dates), 600)


class SummableAllocationsGiveAFiniteCertificate(unittest.TestCase):

    def test_geometric_allocation_fits_inside_capital(self):
        account = OutflowAccount(F(1))
        for e in range(12):
            account.allocate(f"e{e}", F(1, 2 ** (e + 1)))
        self.assertEqual(sum(account.allocations.values(), ZERO),
                         F(1) - F(1, 2 ** 12))

    def test_a_nonsummable_allocation_is_refused_at_admission(self):
        account = OutflowAccount(F(1))
        with self.assertRaises(Insufficient):
            for e in range(100):
                account.allocate(f"e{e}", F(1, 10))

    def test_the_account_cannot_be_overspent(self):
        account = OutflowAccount(F(5))
        account.spend(F(1, 8), F(7, 8), F(1, 2), (F(2),))     # costs 4
        self.assertEqual(account.remaining, F(1))
        with self.assertRaises(Insufficient):
            account.spend(F(1, 8), F(7, 8), F(1, 2), (F(1),))  # would cost 2
        self.assertEqual(account.remaining, F(1))              # and did not


class AffordableTolerance(unittest.TestCase):
    """The force/safety tradeoff, as an equation rather than a warning."""

    def test_the_policy_inverts_the_charge_exactly(self):
        slack, volume, deficits, allowance = F(1, 8), F(7, 8), (F(3),), F(6)
        delta = affordable_tolerance(slack, volume, deficits, allowance)
        self.assertEqual(delta, F(1, 2))
        self.assertEqual(charge(slack, volume, delta, deficits), allowance)

    def test_tighter_tolerance_costs_more(self):
        args = (F(1, 8), F(7, 8), (F(1),))
        self.assertGreater(charge(*args[:2], F(1, 100), args[2]),
                           charge(*args[:2], F(1, 2), args[2]))

    def test_a_free_date_is_reported_as_free_not_as_zero_tolerance(self):
        self.assertIsNone(affordable_tolerance(F(1, 8), F(7, 8), (ZERO,), F(1)))

    def test_an_unaffordable_date_needs_a_vacuous_promise(self):
        """`delta > 1` is unaffordable, not a tolerance to round down to 1."""
        needed = affordable_tolerance(F(1, 8), F(7, 8), (F(4),), F(1, 2))
        self.assertEqual(needed, F(8))
        self.assertGreater(needed, ONE)
        self.assertIsNone(relax(OutflowAccount(F(100)), F(1, 8), F(7, 8),
                                (F(4),), ceiling=ONE, allowance=F(1, 2)))


class ExhaustionBehaviour(unittest.TestCase):

    def test_quarantine_withholds_force_and_spends_nothing(self):
        account = OutflowAccount(F(1))
        self.assertIsNone(
            quarantine(account, F(1, 8), F(7, 8), F(1, 2), (F(1),)))
        self.assertEqual(account.spent, ZERO)

    def test_relaxation_buys_the_tightest_affordable_promise(self):
        account = OutflowAccount(F(4))
        granted = relax(account, F(1, 8), F(7, 8), (F(1),), ceiling=ONE)
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
            charges.add(charge(F(1, 8), F(7, 8), F(1, 2), (worst,)))
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
            proportional(account, F(1, 8), F(t + 1), (F(1, 2),),
                         share=F(1, 2), ceiling=F(10 ** 9))
        self.assertLess(account.spent, F(1))
        self.assertGreater(account.remaining, ZERO)

    def test_but_the_promise_it_buys_goes_vacuous_anyway(self):
        """Never exhausting is not the same as keeping force available."""
        account = OutflowAccount(F(1))
        granted = [proportional(account, F(1, 8), F(t + 1), (F(1, 2),),
                                share=F(1, 2), ceiling=ONE) for t in range(30)]
        # with capital 1 against this deficit, not even date 0 is affordable
        self.assertEqual([t for t, g in enumerate(granted) if g is not None], [])

    def test_the_promise_it_buys_degrades(self):
        account = OutflowAccount(F(1))
        granted = [proportional(account, F(1, 8), F(t + 1), (F(1, 2),),
                                share=F(1, 2), ceiling=F(10 ** 9))
                   for t in range(20)]
        self.assertLess(granted[0], granted[10])
        self.assertLess(granted[10], granted[19])
        self.assertGreater(granted[0], ONE)       # vacuous from the first date

    def test_remaining_capital_decays_geometrically(self):
        account = OutflowAccount(F(1))
        for t in range(8):
            proportional(account, F(1, 8), F(t + 1), (F(1, 2),),
                         share=F(1, 2), ceiling=F(10 ** 6))
        self.assertEqual(account.remaining, F(1, 256))


class NoAccountSubsidizesAPersistentDeficit(unittest.TestCase):
    """The limitative theorem, against every protocol rather than one policy.

    A date at which force says anything costs at least `D_t / ceiling`. If the
    exclusion deficit never decays below a positive floor, those charges are
    bounded away from zero and finitely many fit in finite capital. So the
    account does not merely fail to fund a persistent deficit under some
    particular policy — no finite account funds one under any policy.
    """

    def test_finitely_many_meaningful_dates(self):
        self.assertEqual(meaningful_dates_are_finite(F(100), F(1, 2)), 200)
        self.assertEqual(meaningful_dates_are_finite(F(10 ** 6), F(1, 1000)),
                         10 ** 9)

    def test_a_looser_ceiling_buys_proportionally_more_dates(self):
        self.assertEqual(
            meaningful_dates_are_finite(F(100), F(1, 2), ceiling=F(10)),
            10 * meaningful_dates_are_finite(F(100), F(1, 2), ceiling=ONE))

    def test_the_theorem_needs_the_deficit_to_be_bounded_away_from_zero(self):
        with self.assertRaises(ValueError):
            meaningful_dates_are_finite(F(1), ZERO)

    def test_it_agrees_with_the_realized_policy(self):
        """The bound is not vacuous: a real run stops within it."""
        account, funded = OutflowAccount(F(9)), 0
        while True:
            try:
                account.spend(F(1, 8), F(7, 8), ONE, (F(1, 2),))
                funded += 1
            except Insufficient:
                break
        self.assertLessEqual(funded, meaningful_dates_are_finite(F(9), F(1, 2)))


class ForeverUnvindicatedAndSafe(unittest.TestCase):
    """The fixture that separates safety from deductive resolution.

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
                     deficits=(F(1, 2 ** t),)) for t in range(n)]

    def test_the_deficit_never_reaches_zero(self):
        self.assertTrue(all(d["deficits"][0] > 0 for d in self.dates(50)))

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
                      deficits=(F(1, 2),)) for t in range(60)]
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
                account.spend(F(1, 8), F(t + 1), F(1, 2), (F(1, 2),))


class ChargeIsAdditiveOverRowsAndConservativeOverWorlds(unittest.TestCase):

    def test_the_certificate_decomposes_additively_over_rows(self):
        slack, volume, delta = F(1, 8), F(7, 8), F(1, 2)
        deficits = (F(1), F(2), F(3))
        merged = charge(slack, volume, delta, deficits)
        parts = sum(charge(slack, volume, delta, (d,)) for d in deficits)
        self.assertEqual(merged, parts)

    def test_settlement_rows_contribute_nothing(self):
        slack, volume, delta = F(1, 8), F(7, 8), F(1, 2)
        self.assertEqual(charge(slack, volume, delta, (F(1), ZERO, ZERO)),
                         charge(slack, volume, delta, (F(1),)))

    def test_the_charge_dominates_a_followed_world(self):
        dates = [dict(slack=F(1, 8), volume=F(7, 8), tolerance=F(1, 2),
                      deficits=(F(1, 2),)) for _ in range(10)]
        region = Region(1, [Row([F(1)], F(1, 2))])
        beta = (F(1, 8) + F(7, 8)) / F(1, 2) ** 2
        price, world = (F(1, 4),), (ZERO,)
        step = holdings_value(
            EnforcementTrader(region, beta).coefficients(price), price, world)
        self.assertTrue(charge_is_conservative(dates, [step] * 10))

    def test_the_certificate_is_strictly_conservative(self):
        """It maximizes over live worlds per date; the criterion follows one."""
        dates = [dict(slack=F(1, 8), volume=F(7, 8), tolerance=F(1, 2),
                      deficits=(F(1, 2),)) for _ in range(10)]
        region = Region(1, [Row([F(1)], F(1, 2))])
        beta = (F(1, 8) + F(7, 8)) / F(1, 2) ** 2
        price, world = (F(1, 4),), (ZERO,)
        step = holdings_value(
            EnforcementTrader(region, beta).coefficients(price), price, world)
        self.assertLess(-10 * step, cumulative_certificate(dates))


class LiabilityIsInvariantUnderRowPresentation(unittest.TestCase):
    """Rescaling and duplication do not change what force costs.

    A half-space has many presentations. Under a fixed *declared* tolerance the
    compiled position does move, because the symbol `delta` is a promise about
    the violation in the presentation's own units. Held to a fixed **actual**
    conformance target, the position and the charge are identical across
    presentations — so a source cannot buy stronger force cheaply by rescaling
    its rows, and duplicating a row is not a way to launder intensity.
    """

    slack, volume = F(1, 8), F(2)
    price, world, target = (F(1, 4),), (ZERO,), F(1, 10)

    def compiled(self, rows, scale):
        """Position and charge at a tolerance meaning `target` in base units."""
        delta = self.target * scale
        beta = (self.slack + self.volume) / delta ** 2 / len(rows)
        position = EnforcementTrader(Region(1, rows), beta).coefficients(self.price)
        cost = sum(beta * r.violation(self.price)
                   * max(ZERO, r.r - dot(r.c, self.world)) for r in rows)
        return position, cost

    def test_rescaling_changes_nothing(self):
        results = {self.compiled([Row([lam], lam * F(1, 2))], lam)
                   for lam in (F(1), F(2), F(10), F(1, 3))}
        self.assertEqual(len(results), 1)

    def test_duplication_changes_nothing(self):
        results = {self.compiled([Row([F(1)], F(1, 2))] * k, F(1))
                   for k in (1, 2, 5)}
        self.assertEqual(len(results), 1)

    def test_a_fixed_declared_tolerance_is_presentation_dependent(self):
        """The half that does move, recorded so the API can say which is which."""
        beta = (self.slack + self.volume) / F(1, 10) ** 2
        positions = {EnforcementTrader(
            Region(1, [Row([lam], lam * F(1, 2))]), beta).coefficients(self.price)
            for lam in (F(1), F(2))}
        self.assertEqual(len(positions), 2)


if __name__ == "__main__":
    unittest.main()
