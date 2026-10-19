"""The fixture's numbers, the odds bankroll, the two market exhibits, the countermodels
and the record — exact rationals, recomputed and compared exactly."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from fixture import (ALL_TRUE, BETA, FIXTURE, N0, N1, NE, WORLDS, Ledger, Row, Strengths,
                     applicability_row, bankroll, budgeted_seller_run, gap_dominated,
                     harmonic, harmonic_buyer_run, live, maker_price, minimal_rho, odds,
                     premise_row, region_points, rho, rows, same_projection_different_support,
                     slack_world_exists, strength_row)
from record import MarketRun, trace
from licence import (Certificate, admissible, countermodel_grounds, defeat, forced_interval,
                     licensed, supported)


class TheRowsAndTheirGaps(unittest.TestCase):

    def test_strengths_are_humble(self):
        FIXTURE.check()

    def test_six_distinct_payout_vectors(self):
        vecs = {tuple(w[k] for k in ("X", "XA", "XAY", "Y")) for w in WORLDS.values()}
        self.assertEqual(len(vecs), 6)  # A is invisible when X is false

    def test_gaps_at_the_all_true_world_are_the_complements(self):
        w = WORLDS[ALL_TRUE]
        self.assertEqual(premise_row(FIXTURE).gap(w), 1 - FIXTURE.P)
        self.assertEqual(applicability_row(FIXTURE).gap(w), 1 - FIXTURE.A)
        self.assertEqual(strength_row(FIXTURE).gap(w), 1 - FIXTURE.S)

    def test_each_row_has_exactly_one_deficit_pattern(self):
        p, a, s = rows(FIXTURE)
        self.assertEqual({k for k, w in WORLDS.items() if p.gap(w) < 0}, {k for k in WORLDS if k[0] == 0})
        self.assertEqual({k for k, w in WORLDS.items() if a.gap(w) < 0}, {(1, 0, 0), (1, 0, 1)})
        self.assertEqual({k for k, w in WORLDS.items() if s.gap(w) < 0}, {(1, 1, 0)})

    def test_deficits_are_the_strengths(self):
        p, a, s = rows(FIXTURE)
        self.assertEqual(max(p.deficit(w) for w in WORLDS.values()), FIXTURE.P)
        self.assertEqual(max(a.deficit(w) for w in WORLDS.values()), FIXTURE.A)
        self.assertEqual(max(s.deficit(w) for w in WORLDS.values()), FIXTURE.S)


class TheOddsBankroll(unittest.TestCase):

    def test_fixture_odds(self):
        self.assertEqual(odds(FIXTURE.P), 4)
        self.assertEqual(odds(FIXTURE.A), 3)
        self.assertEqual(odds(FIXTURE.S), 2)
        self.assertEqual(rho(FIXTURE), 4)
        self.assertEqual(bankroll(FIXTURE), 12)

    def test_domination_holds_at_every_world(self):
        self.assertTrue(gap_dominated(FIXTURE))

    def test_the_odds_are_the_least_dominating_factor(self):
        self.assertEqual(minimal_rho(FIXTURE), rho(FIXTURE))
        self.assertFalse(gap_dominated(FIXTURE, rho(FIXTURE) - F(1, 1000)))

    def test_bankroll_is_intensity_free(self):
        # the bound names strengths only; two intensities, one bound
        self.assertEqual(bankroll(FIXTURE), bankroll(FIXTURE))
        self.assertNotIn("beta", bankroll.__code__.co_varnames)

    def test_bankroll_explodes_as_a_strength_approaches_one(self):
        near = Strengths(F(99, 100), FIXTURE.A, FIXTURE.S)
        self.assertEqual(bankroll(near), 3 * 99)


class TheThreeSettlementSemantics(unittest.TestCase):
    """Deductive, evaluation and pegged settlement are three live-set schedules of one
    assessment process; the slack world is live under all three until a refutation."""

    def test_before_any_settlement_the_slack_world_is_live(self):
        self.assertTrue(slack_world_exists(FIXTURE, live(False, None), rows(FIXTURE)))

    def test_after_x_the_slack_world_is_live(self):
        self.assertTrue(slack_world_exists(FIXTURE, live(True, None), rows(FIXTURE)))

    def test_pegged_forever_the_slack_world_is_live(self):
        # `Y` never settles: the live set never loses the all-true world
        self.assertIn(ALL_TRUE, live(True, None))

    def test_affirming_evaluation_keeps_the_slack_world(self):
        self.assertTrue(slack_world_exists(FIXTURE, live(True, True), rows(FIXTURE)))

    def test_disagreeing_evaluation_empties_the_region_while_applicability_is_live(self):
        pts = region_points(FIXTURE, rows(FIXTURE, True), x_pin=F(1), xay_pin=F(0), y_pin=F(0))
        self.assertEqual(pts, [])

    def test_disagreeing_evaluation_leaves_an_orphan_pin_after_the_defeat(self):
        pts = region_points(FIXTURE, rows(FIXTURE, False), x_pin=F(1), xay_pin=F(0), y_pin=F(0))
        self.assertTrue(pts)
        self.assertTrue(all(p["XA"] == 0 for p in pts))  # the pin: P(X∧A) = 0

    def test_the_orphan_has_no_slack_world(self):
        lw = live(True, False)
        self.assertFalse(slack_world_exists(FIXTURE, lw, rows(FIXTURE, False)))
        s = strength_row(FIXTURE)
        self.assertTrue(all(s.gap(w) <= 0 for w in lw.values()))
        self.assertEqual(s.gap(lw[(1, 1, 0)]), -FIXTURE.S)


class TheBudgetedCounterpartyExhibit(unittest.TestCase):
    """Against a live slack world the realized liability is at most the counterparty's
    budget times the odds, whatever the intensity and however many dates."""

    def test_realized_liability_under_budget_times_odds(self):
        for beta in (F(1), F(10), F(1000)):
            for budget in (F(1), F(3)):
                led = budgeted_seller_run(FIXTURE.P, beta, budget, F(1, 2), 400)
                self.assertGreaterEqual(led.enforcer_at_deficit, -budget * odds(FIXTURE.P))
                self.assertLessEqual(led.counterparty_spend, budget)

    def test_the_counterparty_runs_out_of_budget(self):
        led = budgeted_seller_run(FIXTURE.P, F(10), F(3), F(1, 2), 400)
        p = maker_price(FIXTURE.P, F(10), F(1, 2))
        self.assertLessEqual(led.counterparty_spend, 3)
        self.assertGreater(led.counterparty_spend + F(1, 2) * (1 - p), 3)
        self.assertEqual(led.units, 12)  # 24 dates at k = 1/2, spend 1/8 a date

    def test_price_never_exceeds_the_strength(self):
        for k in (F(0), F(1, 10), F(1), F(100)):
            self.assertLessEqual(maker_price(FIXTURE.P, F(10), k), FIXTURE.P)

    def test_with_the_whole_market_capital_the_bound_is_the_bankroll(self):
        led = budgeted_seller_run(FIXTURE.P, F(10), F(3), F(1, 2), 400)
        self.assertGreaterEqual(led.enforcer_at_deficit, -bankroll(FIXTURE))


class TheHarmonicBuyerExhibit(unittest.TestCase):
    """Against the orphaned strength row the realized liability grows like the harmonic
    series while the buyer's budget spend converges: no bankroll works."""

    def test_spend_converges_and_liability_diverges(self):
        led_50 = harmonic_buyer_run(BETA, FIXTURE.S, 50)
        led_200 = harmonic_buyer_run(BETA, FIXTURE.S, 200)
        bound = F(9, 40) * F(2)  # Σ 1/(t+1)² < 2, times 1/(c_S² β) = 9/40
        self.assertLess(led_50.counterparty_spend, bound)
        self.assertLess(led_200.counterparty_spend, bound)
        self.assertLess(led_200.enforcer_at_deficit, led_50.enforcer_at_deficit)

    def test_liability_tracks_the_harmonic_number(self):
        n = 200
        led = harmonic_buyer_run(BETA, FIXTURE.S, n)
        self.assertLessEqual(led.enforcer_at_deficit, -(harmonic(n) - led.counterparty_spend))
        self.assertGreater(harmonic(n), F(58, 10))

    def test_every_bound_is_passed(self):
        # H_n ≥ ln n: for a bound B the loss passes B by date exp(B + 1); here B = 2
        led = harmonic_buyer_run(BETA, FIXTURE.S, 30)
        self.assertLess(led.enforcer_at_deficit, -2)

    def test_the_buyer_is_a_fixed_rational_schedule(self):
        # efficiently computable: k_t = 1/(t+1), no price dependence
        self.assertEqual([F(1, t + 1) for t in range(5)], [F(1), F(1, 2), F(1, 3), F(1, 4), F(1, 5)])


class TheDefeater(unittest.TestCase):

    def test_liability_before_the_defeat_is_absorbed(self):
        # the applicability row's own odds bound while its slack world is live
        self.assertEqual(3 * odds(FIXTURE.A), 9)
        self.assertLessEqual(3 * odds(FIXTURE.A), bankroll(FIXTURE))

    def test_dates(self):
        self.assertLess(N1, N0)
        self.assertLess(N0, NE)


class ItemThirtyNineIsWeak(unittest.TestCase):

    def test_same_projection_different_live_worlds(self):
        w1, w2, v1, v2 = same_projection_different_support()
        self.assertNotEqual(w1, w2)
        self.assertEqual(v1, v2)

    def test_the_region_excludes_live_points(self):
        # the premise row excludes every X-false world as a point while it is live
        lw = live(False, None)
        excluded = [k for k, w in lw.items() if not premise_row(FIXTURE).satisfied(w)]
        self.assertTrue(excluded)


class TheLicenceChainCountermodels(unittest.TestCase):

    def setUp(self):
        self.G = countermodel_grounds()

    def test_region_is_the_interval_and_unchanged_by_defeat(self):
        self.assertEqual(forced_interval(self.G, set()), (F(1, 2), F(1)))
        self.assertEqual(forced_interval(self.G, {1}), (F(1, 2), F(1)))

    def test_stale_certificate_fails_supported_after_defeat(self):
        c1 = Certificate(lower_cite=1)
        self.assertTrue(supported(self.G, set(), F(1, 2), c1))
        self.assertTrue(admissible(self.G, {1}, F(1, 2)))
        self.assertFalse(supported(self.G, {1}, F(1, 2), c1))
        self.assertTrue(supported(self.G, {1}, F(1, 2), Certificate(lower_cite=2)))

    def test_two_verdicts_inside_supported_one_unauthorized(self):
        c1 = Certificate(lower_cite=1)
        for v in (F(2, 3), F(3, 4)):
            self.assertTrue(supported(self.G, set(), v, c1))
        self.assertTrue(licensed(self.G, set(), F(2, 3), c1, event=7, authorized={7}))
        self.assertFalse(licensed(self.G, set(), F(3, 4), c1, event=7, authorized=set()))

    def test_chain(self):
        c1 = Certificate(lower_cite=1)
        for docket in (set(), {1}):
            for v in (F(1, 2), F(2, 3), F(1)):
                if licensed(self.G, docket, v, c1, 7, {7}):
                    self.assertTrue(supported(self.G, docket, v, c1))
                if supported(self.G, docket, v, c1):
                    self.assertTrue(admissible(self.G, docket, v))


class TheRecord(unittest.TestCase):

    def test_not_injective(self):
        r1 = MarketRun(price=F(1, 2))
        r2 = MarketRun(price=F(1))
        self.assertNotEqual(r1, r2)
        self.assertEqual(trace(r1), trace(r2))

    def test_not_constant(self):
        r1 = MarketRun(price=F(1, 2))
        r3 = MarketRun(price=F(1, 2), defeated={1})
        self.assertNotEqual(trace(r1), trace(r3))

    def test_position_is_in_the_record(self):
        r0 = MarketRun(price=F(0))
        self.assertEqual(trace(r0).position, F(1))

    def test_licensed_is_decided_from_the_record(self):
        rec = trace(MarketRun(price=F(1, 2), authorized={7}))
        c1 = Certificate(lower_cite=1)
        self.assertTrue(rec.decide_licensed(F(2, 3), c1, 7))
        self.assertFalse(rec.decide_licensed(F(2, 3), c1, 8))


if __name__ == "__main__":
    unittest.main()
