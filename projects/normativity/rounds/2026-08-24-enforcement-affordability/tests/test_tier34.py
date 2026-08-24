"""Tier 3 divergence witnesses, the addendum's diachronic probes, and the
Tier 4 identity prosecution."""
from __future__ import annotations

import unittest
from fractions import Fraction as Q
from itertools import product

from common import (
    BOTH,
    HALF,
    ONE,
    P0,
    P1,
    ZERO,
    Box,
    BudgetedTrader,
    Enforcer,
    buyer,
    const_schedule,
    delta_half,
    enforcer_coeffs,
    eps_of,
    geometric_slack,
    interval,
    intensity,
    lifetime_liability,
    run_market,
    seller,
    settled_true,
    undecided,
)

PHI = ("phi",)


class TestW1AntiSettlement(unittest.TestCase):
    """W1: a peg excluding the settled truth bleeds linearly against flow
    that no plausible world bills. Divergence here is forced by skeleton
    Theorem 4.4's contrapositive; the fixture also exhibits the exploitation
    shape directly."""

    def test_linear_divergence_and_exploitation_shape(self):
        days = 20
        K = interval(ZERO, Q(3, 10))
        adv = BudgetedTrader("buy", PHI, buyer(ONE), ONE, settled_true)
        enf = Enforcer(PHI, const_schedule(K, ONE, delta_half))
        run_market([adv, enf], days, PHI)
        # The buyer gains at the only live table every day: never throttled,
        # never shut off, flow forever.
        self.assertFalse(adv.shut_off(days + 1))
        # Enforcer liability at the live table grows linearly.
        L = lifetime_liability(enf.ledger, [P1])
        self.assertGreaterEqual(L, Q(1, 2) * days - 2)
        # Exploitation shape at the horizon-live table: bounded below by the
        # budget floor, unboundedly above along the run.
        self.assertGreaterEqual(adv.ledger.worth(P1), Q(1, 2) * days - 2)
        self.assertGreaterEqual(adv.ledger.worth(P1), -ONE)


def adaptive_pump(adv_holder, low_era, entry_cap):
    """Half-throttle adaptive pump: buys with flow proportional to the
    current worst-case war chest during low eras, sells the accumulated
    position back during high eras. Risk per day stays below half the
    available capital, so the budgeter never fires; the growing war chest is
    the vindication-free recharge channel (realized cash)."""

    def base(day, prices):
        adv = adv_holder[0]
        position = sum(s.get("phi", ZERO) for _, s, _ in adv.ledger.trades)
        avail = adv.budget + min(adv.ledger.worth(P0), adv.ledger.worth(P1))
        if low_era(day):
            return {"phi": avail / (2 * entry_cap)}
        return {"phi": -position} if position > 0 else {}

    return base


class TestW3RevisionPump(unittest.TestCase):
    """W3: unaccounted region motion is pumped for world-uniform cash. The
    dispatched rate claim (linear in total variation) is itself prosecuted:
    it holds for throttle-pinned constant flow and is beaten by an adaptive
    pump whose realized cash recharges the war chest — the growth is
    compounding, not linear."""

    LOW = interval(Q(1, 10), Q(1, 5))
    HIGH = interval(Q(4, 5), Q(9, 10))
    ERA = 3

    def low_era(self, day):
        return ((day - 1) // self.ERA) % 2 == 0

    def run_pump(self, base_maker, days):
        holder = [None]
        adv = BudgetedTrader("pump", PHI, lambda d, p: {}, ONE, undecided)
        holder[0] = adv
        adv.base = base_maker(holder)

        def era_schedule(day):
            region = self.LOW if self.low_era(day) else self.HIGH
            # Proposition 3.1's A_n is a computable bound on the firm's day
            # strategy. For an adaptive component whose flow scales with its
            # realized war chest, the honest bound grows with that chest;
            # holding A_n fixed would understate lambda_n and let the pump's
            # own price impact eat the spread it extracts.
            avail = adv.budget + min(adv.ledger.worth(P0), adv.ledger.worth(P1))
            A = ONE + (avail if avail > 0 else ZERO) * 2
            return region, intensity(A, day, Q(1, 4))

        enf = Enforcer(PHI, era_schedule)
        run_market([adv, enf], days, PHI)
        return adv, enf

    def cycle_gains(self, adv, days):
        gains = []
        cycle = 2 * self.ERA
        for k in range(days // cycle):
            before = min(adv.ledger.worth(P0, through_day=k * cycle),
                         adv.ledger.worth(P1, through_day=k * cycle))
            after = min(adv.ledger.worth(P0, through_day=(k + 1) * cycle),
                        adv.ledger.worth(P1, through_day=(k + 1) * cycle))
            gains.append(after - before)
        return gains

    def test_world_uniform_extraction_at_the_set_gap_rate(self):
        days = 24
        adv, enf = self.run_pump(
            lambda h: adaptive_pump(h, self.low_era, Q(3, 5)), days
        )
        # World-uniform cash: the pump's worth rises at BOTH payoff patterns.
        self.assertGreater(adv.ledger.worth(P0), ONE)
        self.assertGreater(adv.ledger.worth(P1), ONE)
        # The enforcer is billed correspondingly at both patterns.
        self.assertLess(enf.ledger.worth(P0), -ONE)
        self.assertLess(enf.ledger.worth(P1), -ONE)
        # Extraction per unit tracks the SET GAP between the eras' regions
        # (4/5 - 1/5 = 3/5), not their Hausdorff distance (7/10): the pump
        # buys near the low region's high edge and sells near the high
        # region's low edge.
        bought = sum(s["phi"] for _, s, _ in adv.ledger.trades
                     if s.get("phi", ZERO) > 0)
        cash = min(adv.ledger.worth(P0), adv.ledger.worth(P1))
        per_unit = cash / bought
        self.assertGreater(per_unit, Q(3, 5) - Q(1, 5))
        self.assertLess(per_unit, Q(3, 5) + Q(1, 5))
        # Compounding: later cycles extract strictly more than early ones.
        gains = self.cycle_gains(adv, days)
        self.assertGreater(gains[-1], 2 * gains[0])
        # Exploitation shape: floored below by the budget, world-uniformly
        # increasing above — Theorem 4.4's contrapositive applies, so no
        # criterion-preserving market can hold this schedule.
        self.assertGreaterEqual(min(adv.ledger.worth(P0), adv.ledger.worth(P1)), -ONE)

    def test_constant_flow_is_linear_in_total_variation(self):
        days = 24
        F = Q(1, 20)
        def const_maker(holder):
            def base(day, prices):
                adv = holder[0]
                position = sum(s.get("phi", ZERO) for _, s, _ in adv.ledger.trades)
                if self.low_era(day):
                    return {"phi": F}
                return {"phi": -position} if position > 0 else {}
            return base
        adv, _ = self.run_pump(const_maker, days)
        gains = self.cycle_gains(adv, days)
        # With the war chest never redeployed, per-cycle extraction is flat.
        self.assertGreater(gains[0], ZERO)
        for g in gains[1:]:
            self.assertLessEqual(abs(g - gains[0]), Q(1, 8) * gains[0])


class TestDiachronicProbes(unittest.TestCase):
    """The addendum's two probes: the diachronic functional is the sum of
    SET GAPS between consecutive regions, not Hausdorff total variation."""

    def test_bounded_gap_sum_is_affordable(self):
        # Thin regions, jumps 4^-k, summable gaps, margin maintained: the
        # pump has almost nothing to extract and liability stays small.
        days = 18
        width = Q(1, 200)
        def center(era):
            m = HALF
            for j in range(1, era + 1):
                m += (Q(-1) ** (j + 1)) * Q(1, 4 ** (j + 1))
            return m
        def schedule(day):
            era = (day - 1) // 3
            m = center(era)
            return interval(m - width, m + width), intensity(ONE, day, HALF)
        low_era = lambda day: ((day - 1) // 3) % 2 == 0
        holder = [None]
        adv = BudgetedTrader("pump", PHI, lambda d, p: {}, ONE, undecided)
        holder[0] = adv
        adv.base = adaptive_pump(holder, low_era, ONE)
        enf = Enforcer(PHI, schedule)
        run_market([adv, enf], days, PHI)
        self.assertLessEqual(
            min(adv.ledger.worth(P0), adv.ledger.worth(P1)), Q(1, 4)
        )
        self.assertGreaterEqual(
            min(enf.ledger.worth(P0), enf.ledger.worth(P1)), -Q(1, 2)
        )

    def test_frequency_without_gap_is_free(self):
        # Rapid small oscillation between OVERLAPPING bands: the price can
        # stand still at the shared point, so there is no forced repricing
        # and nothing to pump — frequency alone cannot drive divergence.
        days = 20
        bands = (interval(Q(2, 5), HALF), interval(HALF, Q(3, 5)))
        def schedule(day):
            return bands[(day - 1) % 2], intensity(ONE, day, HALF)
        low_era = lambda day: (day - 1) % 2 == 0
        holder = [None]
        adv = BudgetedTrader("pump", PHI, lambda d, p: {}, ONE, undecided)
        holder[0] = adv
        adv.base = adaptive_pump(holder, low_era, HALF)
        enf = Enforcer(PHI, schedule)
        run_market([adv, enf], days, PHI)
        slack = geometric_slack(days)
        self.assertLessEqual(
            min(adv.ledger.worth(P0), adv.ledger.worth(P1)), slack
        )
        self.assertGreaterEqual(
            min(enf.ledger.worth(P0), enf.ledger.worth(P1)),
            -(Q(3, 2) + 7 * slack),
        )


class SettlementStream:
    """Three sequential one-sentence episodes; sentence k settles false at
    the end of its episode. The one adversary's war chest carries across
    episodes, and settlement vindicates it."""

    SUPPORT = ("s1", "s2", "s3")
    EPISODE = 6

    def __init__(self, delayed_days=0, settling=True):
        self.delayed = delayed_days
        self.settling = settling

    def episode_of(self, day):
        return min((day - 1) // self.EPISODE, 2)

    def live(self, day):
        tables = []
        for bits in product((ZERO, ONE), repeat=3):
            ok = True
            if self.settling:
                for j in range(3):
                    if day > (j + 1) * self.EPISODE and bits[j] != ZERO:
                        ok = False
                        break
            if ok:
                tables.append(bits)
        return tuple(tables)

    def region(self, day):
        bounds = []
        for j in range(3):
            start, end = j * self.EPISODE + 1, (j + 1) * self.EPISODE
            if start <= day <= end or not self.settling and day > end:
                bounds.append((Q(2, 5), Q(3, 5)))
            elif day > end:
                if day <= end + self.delayed:
                    bounds.append((Q(2, 5), Q(3, 5)))  # stale peg
                else:
                    bounds.append((ZERO, ZERO))  # tracked to the settled face
            else:
                bounds.append((ZERO, ONE))  # inert before the episode
        return Box(tuple(bounds))

    def build(self, budget=HALF):
        holder = []
        def base(day, prices):
            adv = holder[0]
            j = self.episode_of(day)
            active = j * self.EPISODE < day <= (j + 1) * self.EPISODE + self.delayed
            if not active:
                return {}
            avail = min(adv.available(day, t) for t in self.live(day))
            return {self.SUPPORT[j]: -avail / 2} if avail > 0 else {}
        adv = BudgetedTrader("adv", self.SUPPORT, base, budget, self.live)
        holder.append(adv)
        enf = Enforcer(
            self.SUPPORT,
            lambda day: (self.region(day), intensity(ONE, day, HALF)),
        )
        return adv, enf

    def run(self, budget=HALF):
        adv, enf = self.build(budget)
        days = 3 * self.EPISODE + self.delayed
        run_market([adv, enf], days, self.SUPPORT)
        return adv, enf, days


class TestW4SettlementSurprise(unittest.TestCase):
    """W4: geometrically perfect every day, billed at settlement; the
    vindicated war chest recharges and the stream diverges."""

    SURVIVOR = (ZERO, ZERO, ZERO)

    def test_stream_of_surprises_with_war_chest_recharge(self):
        stream = SettlementStream()
        adv, enf, days = stream.run()
        E = stream.EPISODE
        # Per-episode enforcer loss at the surviving table, increasing.
        losses = []
        for k in range(3):
            before = enf.ledger.worth(self.SURVIVOR, through_day=k * E)
            after = enf.ledger.worth(self.SURVIVOR, through_day=(k + 1) * E)
            losses.append(before - after)
        self.assertGreater(losses[0], Q(1, 10))
        self.assertGreater(losses[1], losses[0])
        self.assertGreater(losses[2], losses[1])
        # The adversary is never shut off: each settlement vindicates it.
        self.assertFalse(adv.shut_off(days + 1))
        self.assertGreater(adv.ledger.worth(self.SURVIVOR), ZERO)
        # The surprise term is inventory times mispricing: the episode's
        # loss equals the enforcement coefficients weighted by their entry
        # prices, up to the MarketMaker slack.
        for k in range(3):
            coord = stream.SUPPORT[k]
            inv_cost = sum(
                s.get(coord, ZERO) * p[coord]
                for d, s, p in enf.ledger.trades
                if k * E < d <= (k + 1) * E
            )
            episode_loss = (
                enf.ledger.worth(self.SURVIVOR, through_day=k * E)
                - enf.ledger.worth(self.SURVIVOR, through_day=(k + 1) * E)
            )
            self.assertLessEqual(abs(episode_loss - inv_cost), geometric_slack(days))

    def test_delayed_tracking_adds_a_w1_bleed(self):
        prompt = SettlementStream(delayed_days=0)
        _, enf_p, _ = prompt.run()
        delayed = SettlementStream(delayed_days=3)
        adv_d, enf_d, days_d = delayed.run()
        loss_p = -enf_p.ledger.worth(self.SURVIVOR)
        loss_d = -enf_d.ledger.worth(self.SURVIVOR)
        # The stale peg is attacked risklessly after settlement: the delayed
        # variant pays strictly more, by a per-delayed-day margin.
        self.assertGreater(loss_d, loss_p + Q(1, 4))

    def test_never_settling_complement_is_bounded(self):
        stream = SettlementStream(settling=False)
        adv, enf, days = stream.run()
        # Without settlement there is no vindication: one war chest, one
        # T2-style bound across the whole stream.
        tables = stream.live(days)
        bound = HALF * Q(3, 5) / Q(2, 5) + 7 * geometric_slack(days)
        self.assertLessEqual(lifetime_liability(enf.ledger, tables), bound)


class TestTier4Identity(unittest.TestCase):
    """The exploitation identity, both directions, and the quantifier
    attack."""

    def test_bounded_liability_caps_every_coalition_upside(self):
        # Ledger form of the forward direction: the summed cumulative value
        # of ALL traders is capped by the MarketMaker slack at every table,
        # so any coalition's upside is at most the enforcer's downside plus
        # slack — bounded liability leaves no uniformly unbounded coalition
        # income against the enforcement trades.
        days = 20
        adv1 = BudgetedTrader("a1", PHI, seller(ONE), HALF, undecided)
        adv2 = BudgetedTrader("a2", PHI, seller(ONE), Q(1, 4), undecided)
        enf = Enforcer(PHI, const_schedule(interval(Q(2, 5), Q(3, 5)), Q(2), delta_half))
        run_market([adv1, adv2, enf], days, PHI)
        slack = geometric_slack(days)
        for table in BOTH:
            coalition = adv1.ledger.worth(table) + adv2.ledger.worth(table)
            self.assertLessEqual(coalition, -enf.ledger.worth(table) + slack)

    def test_divergence_witnesses_carry_exploiters(self):
        # Reverse direction, exhibited on W1: unbounded liability comes with
        # a component whose horizon-live assessments are floored below and
        # unbounded above (asserted inside TestW1AntiSettlement); this test
        # records the conservation reading on the same fixture.
        days = 16
        adv = BudgetedTrader("buy", PHI, buyer(ONE), ONE, settled_true)
        enf = Enforcer(PHI, const_schedule(interval(ZERO, Q(3, 10)), ONE, delta_half))
        run_market([adv, enf], days, PHI)
        slack = geometric_slack(days)
        self.assertLessEqual(
            adv.ledger.worth(P1), -enf.ledger.worth(P1) + slack
        )
        self.assertGreaterEqual(adv.ledger.worth(P1), Q(1, 2) * days - 2)

    def test_nested_schedules_promote_per_day_uniform_income_to_horizon(self):
        # Support-local nesting in the model's finite form: the live set
        # shrinks monotonically, so a day trade whose value is constant on
        # the day's live tables is constant on every later horizon's live
        # tables. Checked exhaustively on the settlement stream's schedule.
        stream = SettlementStream()
        days = 3 * stream.EPISODE
        for n in range(1, days + 1):
            for N in range(n, days + 1):
                self.assertTrue(set(stream.live(N)) <= set(stream.live(n)))

    def test_non_nested_live_sets_break_the_per_day_quantifier(self):
        # The dispatch's required attack. Live sets alternate between the
        # two singletons (flagrantly non-nested). The trader always trades
        # toward the currently vindicated side at the {1/2} peg: every day's
        # income is positive and trivially uniform on that day's live set,
        # yet every horizon assessment is near zero — per-day-uniform income
        # never becomes horizon upside, and enforcement liability stays
        # bounded despite unbounded cumulative per-day income. The identity
        # must therefore quantify plausibility at the horizon; with nesting
        # (previous test) the two quantifiers agree.
        days = 16
        F = HALF

        def flip_live(day):
            return (P0,) if day % 2 == 1 else (P1,)

        def base(day, prices):
            return {"phi": -F} if day % 2 == 1 else {"phi": F}

        adv = BudgetedTrader("flip", PHI, base, ONE, flip_live)
        enf = Enforcer(PHI, const_schedule(interval(HALF, HALF), ONE, delta_half))
        run_market([adv, enf], days, PHI)
        slack = geometric_slack(days)
        per_day_income = ZERO
        for day, shares, prices in adv.ledger.trades:
            (table,) = flip_live(day)
            income = sum(
                c * (table[0] - prices[phi]) for phi, c in shares.items()
            )
            self.assertGreaterEqual(income, Q(1, 8))
            per_day_income += income
        self.assertGreaterEqual(per_day_income, Q(1, 8) * days)
        for N in (days - 1, days):
            (table,) = flip_live(N)
            self.assertLessEqual(abs(adv.ledger.worth(table, through_day=N)), ONE)
            self.assertGreaterEqual(
                enf.ledger.worth(table, through_day=N), -(ONE + slack)
            )


if __name__ == "__main__":
    unittest.main()
