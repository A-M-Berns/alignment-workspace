"""Tier 1 gates and Tier 2 positive bounds, including the taxonomy
adjudication fixture T2(vi)."""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

from common import (
    BOTH,
    HALF,
    ONE,
    P0,
    P1,
    ZERO,
    BudgetedTrader,
    Enforcer,
    Segment,
    Box,
    buyer,
    const_schedule,
    conservation_check,
    delta_dyadic,
    delta_half,
    delta_inv,
    enforcer_coeffs,
    eps_of,
    geometric_slack,
    interval,
    lifetime_liability,
    run_market,
    seller,
    undecided,
    value_of,
)

PHI = ("phi",)


def short_attack_run(K, delta_fn, days, F=Q(1), B=Q(1)):
    adv = BudgetedTrader("adv", PHI, seller(F), B, undecided)
    enf = Enforcer(PHI, const_schedule(K, F, delta_fn))
    run_market([adv, enf], days, PHI)
    return adv, enf


class TestG2Aggregation(unittest.TestCase):
    """Tier 1, G2: what caps a distributed attack."""

    def test_floors_sum_independent_of_spread(self):
        days = 20
        K = interval(Q(2, 5), Q(3, 5))
        # Run A: one attacker with the whole war chest.
        advA = BudgetedTrader("a", PHI, seller(ONE), Q(3, 4), undecided)
        enfA = Enforcer(PHI, const_schedule(K, ONE, delta_half))
        run_market([advA, enfA], days, PHI)
        # Run B: the same total spread over two components.
        adv1 = BudgetedTrader("a1", PHI, seller(ONE), HALF, undecided)
        adv2 = BudgetedTrader("a2", PHI, seller(ONE), Q(1, 4), undecided)
        enfB = Enforcer(PHI, const_schedule(K, Q(2), delta_half))
        run_market([adv1, adv2, enfB], days, PHI)
        # Component floors hold individually at the live tables...
        for table in BOTH:
            self.assertGreaterEqual(advA.ledger.worth(table), -Q(3, 4))
            self.assertGreaterEqual(adv1.ledger.worth(table), -HALF)
            self.assertGreaterEqual(adv2.ledger.worth(table), -Q(1, 4))
            # ...and sum to the aggregate floor however the flow is spread.
            self.assertGreaterEqual(
                adv1.ledger.worth(table) + adv2.ledger.worth(table), -Q(3, 4)
            )
        # Both arrangements are held to the same geometry bound: liability
        # <= (aggregate budget) * hi/(1-hi) + slack.
        bound = Q(3, 4) * Q(3, 5) / Q(2, 5) + 7 * geometric_slack(days)
        self.assertLessEqual(lifetime_liability(enfA.ledger, BOTH), bound)
        self.assertLessEqual(lifetime_liability(enfB.ledger, BOTH), bound)

    def test_confederate_gains_cannot_relax_the_throttle(self):
        # Mechanical scaling versus accounting offset. The throttle of a
        # component reads only that component's realized ledger, so a
        # confederate's gains are invisible to it; a firm-level P&L netting
        # rule would instead let the pair evade the cap.
        prices = {"phi": Q(2, 5)}
        solo = BudgetedTrader("solo", PHI, seller(Q(10)), ONE, undecided)
        with_friend = BudgetedTrader("w", PHI, seller(Q(10)), ONE, undecided)
        friend = BudgetedTrader("c", PHI, buyer(ONE), ONE, undecided)
        # Hand the confederate a large realized gain.
        friend.ledger.execute(1, {"phi": Q(20)}, {"phi": Q(1, 10)})
        self.assertGreaterEqual(friend.ledger.worth(P1), Q(18))
        s_solo = solo.scale(2, prices)
        s_with = with_friend.scale(2, prices)
        self.assertEqual(s_solo, s_with)
        self.assertLess(s_with, ONE)  # the throttle binds
        # The deliberately wrong netted rule would relax it:
        netted_available = ONE + with_friend.ledger.worth(P1) + friend.ledger.worth(P1)
        raw_loss = -value_of({"phi": -Q(10)}, prices, PHI, P1)
        self.assertGreater(netted_available / raw_loss, s_with)


class TestT1Uncontested(unittest.TestCase):
    """Tier 2, T1: uncontested conformity is O(2^-n) tight, far inside the
    tolerance — a strengthening of skeleton Theorem 3.4's delta bound."""

    def run_and_check(self, delta_fn, days=18):
        K = interval(Q(3, 5), Q(9, 10))
        enf = Enforcer(PHI, const_schedule(K, ONE, delta_fn))
        run_market([enf], days, PHI)
        for day, e, p in enforcer_coeffs(enf):
            d2 = K.dist2((p,))
            self.assertLessEqual(d2, eps_of(day) ** 2)  # dist <= 2^-n << delta
            self.assertLessEqual(abs(e), 11 * eps_of(day))  # realized position
        for table in [(ZERO,), (ONE,)]:  # EVERY world, plausible or not
            self.assertGreaterEqual(enf.ledger.worth(table), -11 * geometric_slack(days))

    def test_wide_tolerance(self):
        self.run_and_check(delta_half)

    def test_shrinking_tolerance(self):
        self.run_and_check(delta_dyadic, days=14)


class TestT2ContestedInteriorPeg(unittest.TestCase):
    """Tier 2, T2: the load-bearing target. Liability is governed by the
    war chest and the peg geometry, not the tolerance schedule."""

    K = interval(Q(2, 5), Q(3, 5))

    def bound(self, B, days):
        # (aggregate budget) * (far-side distance / near-side margin) + slack:
        # entry prices sit below hi, the billing world is y=0 at distance
        # <= hi, and the throttling world is y=1 at distance >= 1-hi.
        return B * Q(3, 5) / Q(2, 5) + 7 * geometric_slack(days)

    def test_i_maximal_flow_short(self):
        days = 22
        adv, enf = short_attack_run(self.K, delta_half, days)
        # Prices never cross the far edge while the flow is one-sided.
        for day, e, p in enforcer_coeffs(enf):
            self.assertLessEqual(p, Q(3, 5))
            self.assertGreaterEqual(e, ZERO)
        # The fixed point converts flow, not intensity, into inventory:
        # the realized enforcement coefficient tracks the realized opposing
        # flow to within the MarketMaker allowance.
        for (day, e, p), (_, shares, _) in zip(enforcer_coeffs(enf), adv.ledger.trades):
            c = shares.get("phi", ZERO)
            self.assertLessEqual(abs(e + c), 7 * eps_of(day))
        # Budget floor at the throttling world, and the geometry bound.
        self.assertGreaterEqual(adv.ledger.worth(P1), -ONE)
        self.assertLessEqual(lifetime_liability(enf.ledger, BOTH), self.bound(ONE, days))
        conservation_check([adv, enf], PHI, BOTH, days)

    def test_ii_confederate_pair(self):
        days = 20
        adv1 = BudgetedTrader("a1", PHI, seller(ONE), HALF, undecided)
        adv2 = BudgetedTrader("a2", PHI, buyer(ONE), HALF, undecided)
        enf = Enforcer(PHI, const_schedule(self.K, Q(2), delta_half))
        run_market([adv1, adv2, enf], days, PHI)
        self.assertLessEqual(
            lifetime_liability(enf.ledger, BOTH), self.bound(ONE, days)
        )
        conservation_check([adv1, adv2, enf], PHI, BOTH, days)

    def test_iii_dispersed_swarm(self):
        days = 20
        swarm = [
            BudgetedTrader(f"s{j}", PHI, seller(ONE), Q(1, 2 ** j), undecided)
            for j in range(1, 7)
        ]
        total_budget = sum(t.budget for t in swarm)
        enf = Enforcer(PHI, const_schedule(self.K, Q(6), delta_half))
        run_market(swarm + [enf], days, PHI)
        for t in swarm:
            self.assertGreaterEqual(t.ledger.worth(P1), -t.budget)
        self.assertLessEqual(
            lifetime_liability(enf.ledger, BOTH), self.bound(total_budget, days)
        )

    def test_iv_churn_earns_the_width_as_spread(self):
        # Gentle matched round trips: sell 1/4 for two days, buy the short
        # back over the next two, repeat. Each round trip locks in a sure
        # loss of at least the region's width per share for the churner —
        # the enforcer's world-uniform spread revenue — so the war chest
        # depletes and the budgeter eventually shuts the attack down.
        days = 28
        F = Q(1, 4)
        adv = BudgetedTrader("churn", PHI, lambda d, p: {}, ONE, undecided)
        def churn(day, prices):
            position = sum(s.get("phi", ZERO) for _, s, _ in adv.ledger.trades)
            if (day - 1) % 4 < 2:
                return {"phi": -F}
            return {"phi": min(F, -position)} if position < 0 else {}
        adv.base = churn
        enf = Enforcer(PHI, const_schedule(self.K, ONE, delta_half))
        run_market([adv, enf], days, PHI)
        # The enforcer buys near the low edge and sells near the high edge:
        # a world-uniform gain at both payoff patterns.
        self.assertGreater(enf.ledger.worth(P0), ZERO)
        self.assertGreater(enf.ledger.worth(P1), ZERO)
        self.assertTrue(adv.shut_off(days + 1))
        self.assertLessEqual(
            lifetime_liability(enf.ledger, BOTH), self.bound(ONE, days)
        )

    def test_v_tolerance_independence(self):
        days = 16
        results = {}
        for name, dfn in (("half", delta_half), ("inv", delta_inv),
                          ("dyadic", delta_dyadic)):
            adv, enf = short_attack_run(self.K, dfn, days)
            results[name] = lifetime_liability(enf.ledger, BOTH)
            self.assertLessEqual(results[name], self.bound(ONE, days))
        vals = list(results.values())
        for a in vals:
            for b in vals:
                self.assertLessEqual(abs(a - b), 2 * 7 * geometric_slack(days))


class TestT2viPointPegAdjudication(unittest.TestCase):
    """The registered disagreement: core account vs margin account on
    K = {1/2}. Decision rule stated in the dispatch: flat liability across
    tolerance schedules means the margin account wins."""

    def test_center_point_peg_is_affordable_uniformly_in_delta(self):
        days = 16
        K = interval(HALF, HALF)
        results = {}
        for name, dfn in (("half", delta_half), ("inv", delta_inv),
                          ("dyadic", delta_dyadic)):
            adv, enf = short_attack_run(K, dfn, days)
            L = lifetime_liability(enf.ledger, BOTH)
            results[name] = L
            # Geometry bound with hi = 1/2: B * (1/2)/(1/2) = B.
            self.assertLessEqual(L, ONE + 7 * geometric_slack(days))
            # Mechanism: realized coefficient tracks flow, not intensity.
            for (day, e, p), (_, shares, _) in zip(
                enforcer_coeffs(enf), adv.ledger.trades
            ):
                c = shares.get("phi", ZERO)
                self.assertLessEqual(abs(e + c), 7 * eps_of(day))
        vals = list(results.values())
        for a in vals:
            for b in vals:
                self.assertLessEqual(abs(a - b), 2 * 7 * geometric_slack(days))

    def test_zero_width_earns_no_spread_against_churn(self):
        # The revenue difference between {1/2} and [2/5, 3/5]: churn against
        # the point peg produces no width for the enforcer to earn. Same
        # matched round-trip churner against both regions; the tight
        # tolerance shrinks the price-impact dips so the spread is the
        # region's own width.
        days = 20

        def make_run(region):
            adv = BudgetedTrader("c", PHI, lambda d, p: {}, ONE, undecided)
            def churn(day, prices):
                position = sum(s.get("phi", ZERO) for _, s, _ in adv.ledger.trades)
                if (day - 1) % 8 < 4:
                    return {"phi": -ONE}
                return {"phi": min(ONE, -position)} if position < 0 else {}
            adv.base = churn
            enf = Enforcer(PHI, const_schedule(region, ONE, delta_dyadic))
            run_market([adv, enf], days, PHI)
            return min(enf.ledger.worth(P0), enf.ledger.worth(P1))

        gainP = make_run(interval(HALF, HALF))
        gainI = make_run(interval(Q(2, 5), Q(3, 5)))
        slack = geometric_slack(days)
        self.assertLessEqual(gainP, slack)          # no spread revenue
        self.assertGreater(gainI, gainP + Q(1, 10))  # the interval earns width

    def test_near_vertex_point_pegs_blow_up_at_rate_one_over_margin(self):
        # Both accounts agree at the vertex: K = {eps} diverges ~ B/margin.
        # This family is simultaneously the W2 dogmatism witness.
        # A tight constant tolerance keeps the attacker's own price impact
        # well below the margin from day one, so entry cost is the margin
        # itself. (A day-indexed shrinking schedule pollutes the early days,
        # where delta_n is still wide.)
        days = 16
        B = Q(1, 4)
        tight = lambda n: Q(1, 16)
        rates = []
        for k in (2, 3, 4):
            epsK = Q(1, 2 ** k)
            adv = BudgetedTrader("buy", PHI, buyer(ONE), B, undecided)
            enf = Enforcer(PHI, const_schedule(interval(epsK, epsK), ONE, tight))
            run_market([adv, enf], days, PHI)
            L = lifetime_liability(enf.ledger, BOTH)
            # Both terms scale as 1/margin: the war-chest term B(1-eps)/eps,
            # and the MarketMaker allowance term — near a vertex the day-n
            # guarantee tolerates imbalance up to 2^-n/p, so even the slack
            # is billed at the 1/margin rate.
            predicted = B * (ONE - epsK) / epsK
            allowance = geometric_slack(days) / epsK
            self.assertGreaterEqual(L, predicted - Q(1, 4))
            self.assertLessEqual(L, predicted + allowance + Q(1, 4))
            rates.append((epsK, L))
        # Displayed rate: halving the margin roughly doubles the liability.
        (e1, L1), (e2, L2), (e3, L3) = rates
        self.assertGreater(L2, Q(3, 2) * L1)
        self.assertGreater(L3, Q(3, 2) * L2)


class TestT3MarginDefinition(unittest.TestCase):
    """Tier 2, T3: both margin clauses are necessary, separately."""

    SUPPORT = ("phi", "psi")
    DIAG = ((ZERO, ZERO), (ONE, ONE))  # live tables under phi <-> psi

    def diag_live(self, day):
        return self.DIAG

    def test_dropping_containment_lets_coherence_flow_attack_unthrottled(self):
        # K escapes the deductive region (the diagonal), so the riskless
        # coherence arbitrage — buy phi low, sell psi high — gains at every
        # live table, is never throttled, and bills the enforcer linearly.
        days = 14
        K = Box(((Q(1, 10), Q(1, 5)), (Q(4, 5), Q(9, 10))))
        base = lambda day, prices: {"phi": ONE, "psi": -ONE}
        coh = BudgetedTrader("coh", self.SUPPORT, base, ONE, self.diag_live)
        enf = Enforcer(self.SUPPORT, const_schedule(K, Q(2), delta_half))
        run_market([coh, enf], days, self.SUPPORT)
        for table in self.DIAG:
            self.assertGreater(coh.ledger.worth(table), Q(3, 10) * days)
            self.assertLess(enf.ledger.worth(table), -Q(3, 10) * days)

    def test_containment_restores_the_bound(self):
        # The same coherence flow against a region inside the deductive
        # segment: the fixed point re-prices the two coordinates together
        # and the free lunch vanishes.
        days = 14
        K = Segment((Q(1, 4), Q(1, 4)), (Q(3, 4), Q(3, 4)))
        base = lambda day, prices: {"phi": ONE, "psi": -ONE}
        coh = BudgetedTrader("coh", self.SUPPORT, base, ONE, self.diag_live)
        enf = Enforcer(self.SUPPORT, const_schedule(K, Q(2), delta_half))
        run_market([coh, enf], days, self.SUPPORT)
        slack = geometric_slack(days)
        for table in self.DIAG:
            self.assertGreaterEqual(enf.ledger.worth(table), -slack)
            self.assertLessEqual(coh.ledger.worth(table), slack)

    def test_dropping_distance_reproduces_the_blow_up(self):
        # The distance clause's necessity is the K = {eps} family above:
        # K = {eps} is inside the deductive region [0,1], yet liability goes
        # as B/margin. Cross-reference: the near-vertex family in
        # TestT2viPointPegAdjudication is the witness.
        self.assertTrue(True)


if __name__ == "__main__":
    unittest.main()
