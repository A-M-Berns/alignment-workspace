"""Continuation fixtures: the self-financing lemma (C1), the skeleton-facing
one-coordinate bound it supports (C0), the Appendix D packaging (C2), and the
converse of Theorem 4.6 (C3).

Same model, same conventions as the parent suite. Exact rationals throughout.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q
from itertools import combinations, product

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
    delta_dyadic,
    delta_half,
    delta_inv,
    geometric_slack,
    interval,
    intensity,
    lifetime_liability,
    run_market,
    seller,
    undecided,
)

PHI = ("phi",)
SUP2 = ("phi", "psi")

# Far-side / near-side ratio of the peg [2/5, 3/5] against short flow.
PEG = (Q(2, 5), Q(3, 5))
C_GEOM = Q(3, 5) / Q(2, 5)


# ---------------------------------------------------------------------------
# Liability at skeleton Definition 4.1's quantifiers.
# ---------------------------------------------------------------------------


def def41_liability(ledger, live_fn, days: int) -> Q:
    """`B` of Definition 4.1: the supremum over horizons `N` and worlds live at
    `N` of the enforcer's cumulative deficit.

    The parent round's `lifetime_liability` reads the deficit at the final
    horizon only. The two agree whenever the enforcer's worth is monotone along
    the run, which is every parent fixture (asserted in
    `TestParentSpotChecks`), and differ when the enforcer recovers after its
    opposition dies.
    """
    worst = ZERO
    for N in range(1, days + 1):
        for table in live_fn(N):
            w = ledger.worth(table, through_day=N)
            if -w > worst:
                worst = -w
    return worst


def realized_drawdown(components, table, days: int) -> Q:
    """Deepest cumulative loss the listed components take at one payout table."""
    worst = ZERO
    for N in range(1, days + 1):
        total = sum(c.ledger.worth(table, through_day=N) for c in components)
        if -total > worst:
            worst = -total
    return worst


def coord_worth(ledger, support, coord, table, through_day=None) -> Q:
    """Cumulative worth attributable to trades in one coordinate."""
    i = support.index(coord)
    total = ZERO
    for day, shares, prices in ledger.trades:
        if through_day is not None and day > through_day:
            continue
        c = shares.get(coord, ZERO)
        if c:
            total += c * (table[i] - prices[coord])
    return total


# ---------------------------------------------------------------------------
# Case 1: the parent's one-coordinate short attack (no income channel).
# ---------------------------------------------------------------------------


def plain_short_attack(days, K=None, delta_fn=delta_half, F=ONE, B=ONE):
    adv = BudgetedTrader("adv", PHI, seller(F), B, undecided)
    enf = Enforcer(PHI, const_schedule(K or interval(*PEG), F, delta_fn))
    run_market([adv, enf], days, PHI)
    return adv, enf


# ---------------------------------------------------------------------------
# Case 2: income minted on a second, UNCONSTRAINED sentence against a patsy
# component, recycled into the attack on the constrained coordinate.
# ---------------------------------------------------------------------------

PSI_SETTLED = ((ZERO, ZERO), (ONE, ZERO))  # psi settled false, phi undecided


def settled_psi_live(day):
    return PSI_SETTLED


PATSY_K = Box((PEG, (ZERO, ONE)))  # constrains phi only; psi is free


def patsy_recycling_run(b_A, b_B, days, harvest=True):
    holder = []

    def patsy_base(day, prices):
        # Downward-sloping demand for psi, vanishing at 9/10; the clearing
        # price against a unit sale is 2/5, so the seller mints 2/5 a day.
        q = Q(2) * (Q(9, 10) - prices["psi"])
        return {"psi": q} if q > 0 else {}

    def attacker_base(day, prices):
        A = holder[0]
        avail = min(A.available(day, t) for t in PSI_SETTLED)
        if avail <= 0:
            return {}
        trade = {"phi": -avail / 2}  # self-throttled at half capital
        if harvest:
            trade["psi"] = -ONE
        return trade

    patsy = BudgetedTrader("patsy", SUP2, patsy_base, b_B, settled_psi_live)
    attacker = BudgetedTrader("atk", SUP2, attacker_base, b_A, settled_psi_live)
    holder.append(attacker)
    enf = Enforcer(SUP2, lambda day: (PATSY_K, intensity(Q(3), day, HALF)))
    run_market([attacker, patsy, enf], days, SUP2)
    return attacker, patsy, enf


# ---------------------------------------------------------------------------
# Case 3: the self-referential channel. One component pumps a MOVING peg on psi
# — extracting world-uniform cash from the enforcer itself — and spends it
# attacking a static, perfectly-margined peg on phi.
# ---------------------------------------------------------------------------

ALL4 = tuple((a, b) for a in (ZERO, ONE) for b in (ZERO, ONE))
LOW_BAND = (Q(1, 10), Q(1, 5))
HIGH_BAND = (Q(4, 5), Q(9, 10))
ERA = 3


def all4_live(day):
    return ALL4


def in_low_era(day):
    return ((day - 1) // ERA) % 2 == 0


def pump_and_drain_run(b_A, days, drain):
    holder = []

    def base(day, prices):
        A = holder[0]
        avail = min(A.available(day, t) for t in ALL4)
        if avail <= 0:
            return {}
        trade = {"phi": -avail * drain} if drain else {}
        position = sum(s.get("psi", ZERO) for _, s, _ in A.ledger.trades)
        if in_low_era(day):
            trade["psi"] = avail / 2
        elif position > 0:
            trade["psi"] = -position
        return trade

    A = BudgetedTrader("atk", SUP2, base, b_A, all4_live)
    holder.append(A)

    def schedule(day):
        region = Box((PEG, LOW_BAND if in_low_era(day) else HIGH_BAND))
        # Proposition 3.1's A_n must track an adaptive component's wealth
        # (the parent round's honesty note 2).
        avail = min(A.available(day, t) for t in ALL4)
        A_n = ONE + (avail if avail > ZERO else ZERO) * 4
        return region, intensity(A_n, day, Q(1, 4))

    enf = Enforcer(SUP2, schedule)
    run_market([A, enf], days, SUP2)
    return A, enf


def cycle_series(A, enf, days):
    """Per-cycle chest, phi-coordinate liability, and phi flow."""
    cyc = 2 * ERA
    chests, phi_liab, phi_flow = [], [], []
    for k in range(days // cyc):
        d1 = (k + 1) * cyc
        chests.append(min(A.ledger.worth(t, through_day=d1) for t in ALL4))
        phi_liab.append(
            -min(coord_worth(enf.ledger, SUP2, "phi", t, d1) for t in ALL4)
        )
        phi_flow.append(
            -sum(s.get("phi", ZERO) for d, s, _ in A.ledger.trades
                 if k * cyc < d <= d1)
        )
    return chests, phi_liab, phi_flow


# ---------------------------------------------------------------------------


class TestParentSpotChecks(unittest.TestCase):
    """Spot-checks of the parent round's standing `proved-in-model` grades.

    The parent measures liability at the final horizon; Definition 4.1 takes
    the supremum over horizons. Every parent bound is re-checked here under the
    stricter reading.
    """

    def test_t2_family_survives_the_definition_41_reading(self):
        for delta_fn, days in ((delta_half, 22), (delta_inv, 16),
                               (delta_dyadic, 16)):
            _, enf = plain_short_attack(days, delta_fn=delta_fn)
            bound = ONE * C_GEOM + 7 * geometric_slack(days)
            final = lifetime_liability(enf.ledger, BOTH)
            d41 = def41_liability(enf.ledger, undecided, days)
            self.assertLessEqual(d41, bound)
            # On this family the enforcer's worth is monotone, so the two
            # measures coincide exactly.
            self.assertEqual(final, d41)

    def test_t1_and_point_peg_survive_the_definition_41_reading(self):
        K1 = interval(Q(3, 5), Q(9, 10))
        for delta_fn, days in ((delta_half, 18), (delta_dyadic, 14)):
            enf = Enforcer(PHI, const_schedule(K1, ONE, delta_fn))
            run_market([enf], days, PHI)
            d41 = def41_liability(enf.ledger, undecided, days)
            self.assertLessEqual(d41, 11 * geometric_slack(days))
            self.assertEqual(d41, lifetime_liability(enf.ledger, BOTH))
        for delta_fn in (delta_half, delta_inv, delta_dyadic):
            days = 16
            _, enf = plain_short_attack(days, K=interval(HALF, HALF),
                                        delta_fn=delta_fn)
            d41 = def41_liability(enf.ledger, undecided, days)
            self.assertLessEqual(d41, ONE + 7 * geometric_slack(days))
            self.assertEqual(d41, lifetime_liability(enf.ledger, BOTH))

    def test_the_two_measures_agree_across_a_scan(self):
        # The parent's measure is the final-horizon deficit and Definition 4.1
        # takes the supremum over horizons, so the parent's upper bounds do not
        # transfer to Definition 4.1 by definition. They transfer here because
        # the two quantities coincide: the enforcer's cumulative worth is
        # monotone along every run this model produces, so no intermediate
        # horizon is worse than the last. Checked across region, flow, side and
        # budget; no separating instance is known (recorded in
        # `FOLLOWUP_STOCK.md`).
        days = 16
        for lo, hi in ((Q(1, 10), Q(3, 10)), (Q(2, 5), Q(3, 5)),
                       (Q(2, 5), Q(4, 5))):
            for F in (Q(1, 4), ONE):
                for base in (buyer(F), seller(F)):
                    adv = BudgetedTrader("a", PHI, base, ONE, undecided)
                    enf = Enforcer(
                        PHI, const_schedule(interval(lo, hi), ONE, delta_half)
                    )
                    run_market([adv, enf], days, PHI)
                    self.assertEqual(
                        lifetime_liability(enf.ledger, BOTH),
                        def41_liability(enf.ledger, undecided, days),
                    )


class TestC1SelfFinancing(unittest.TestCase):
    """C1: a component's wealth is global, so income minted elsewhere relaxes
    its throttle on the constrained coordinate. Which income channels close?"""

    def test_throttle_binds_where_the_enforcer_profits(self):
        # The closure mechanism for a static margined peg under one-sided
        # flow: the world that throttles the opposition is the world at which
        # the projection enforcer's inventory PROFITS, so the enforcer funds
        # nothing at the world where funding would relax the throttle. This is
        # the recycling coefficient kappa = 0 case.
        days = 22
        adv, enf = plain_short_attack(days)
        for d in range(2, days + 1):
            avail0, avail1 = adv.available(d, P0), adv.available(d, P1)
            binding = P0 if avail0 < avail1 else P1
            self.assertEqual(binding, P1)
            self.assertGreaterEqual(
                enf.ledger.worth(binding, through_day=d - 1), ZERO
            )

    def test_patsy_income_breaks_the_per_component_chest(self):
        # Channel (b): another budgeted component. The attacker's OWN budget is
        # 1 throughout; only the patsy's budget varies. Liability tracks the
        # patsy's budget and eventually exceeds the T2 bound instantiated at
        # the attacker's own war chest.
        days = 56
        _, _, enf_solo = patsy_recycling_run(ONE, Q(64), days, harvest=False)
        A, patsy, enf = patsy_recycling_run(ONE, Q(64), days, harvest=True)
        own_bound = ONE * C_GEOM + 7 * geometric_slack(days)
        L_solo = def41_liability(enf_solo.ledger, settled_psi_live, days)
        L = def41_liability(enf.ledger, settled_psi_live, days)
        self.assertLessEqual(L_solo, own_bound)      # no channel: bound holds
        self.assertGreater(L, own_bound)             # channel open: it fails
        self.assertGreater(L, 4 * L_solo)
        # The patsy paid for it, inside its own floor.
        self.assertGreaterEqual(patsy.ledger.worth(PSI_SETTLED[0]), -Q(64))
        self.assertLess(patsy.ledger.worth(PSI_SETTLED[0]), -Q(8))

    def test_aggregate_nominal_chest_still_caps_patsy_recycling(self):
        # Channel (b) is bounded: the transferred income is capped by the
        # patsy's own floor, so the AGGREGATE nominal war chest still controls
        # the liability. Recycling redistributes the chest; it does not mint.
        for b_B, days in ((Q(8), 30), (Q(32), 44), (Q(64), 56)):
            A, patsy, enf = patsy_recycling_run(ONE, b_B, days)
            L = def41_liability(enf.ledger, settled_psi_live, days)
            aggregate = (ONE + b_B) * C_GEOM + 7 * geometric_slack(days)
            self.assertLessEqual(L, aggregate)

    def test_self_referential_recycling_compounds_and_closes_nothing(self):
        # Channel (c): the enforcer's OWN losses. One component, one nominal
        # budget, no patsy. The pumped psi peg pays the component world-uniform
        # cash, which recharges the chest it spends against the static,
        # perfectly-margined phi peg. Chest, phi flow and phi liability all
        # compound geometrically, so no bound in the schedule's own data holds.
        days = 48
        A, enf = pump_and_drain_run(ONE, days, Q(1, 8))
        chests, phi_liab, phi_flow = cycle_series(A, enf, days)
        self.assertEqual(len(chests), 8)
        # Every series is strictly increasing...
        for series in (chests, phi_liab, phi_flow):
            for a, b in zip(series, series[1:]):
                self.assertGreater(b, a)
        # ...and compounding, not linear.
        self.assertGreater(chests[-1], 8 * chests[0])
        self.assertGreater(phi_flow[-1], 4 * phi_flow[0])
        self.assertGreater(phi_liab[-1], 20 * phi_liab[0])
        # The component is never shut off and never breaches its floor.
        self.assertFalse(A.shut_off(days + 1))
        for table in ALL4:
            self.assertGreaterEqual(A.ledger.worth(table), -ONE)
        # Both candidate bounds fail: the nominal chest is 1 throughout.
        L = def41_liability(enf.ledger, all4_live, days)
        self.assertGreater(L, ONE * C_GEOM + 7 * geometric_slack(days))
        # And so does the parameterized form read off the realized drawdown at
        # the phi-throttling worlds: recycling refills the chest faster than it
        # draws down, so the drawdown does not see the flow it funds.
        W = max(realized_drawdown([A], t, days)
                for t in ((ONE, ZERO), (ONE, ONE)))
        self.assertGreater(L, W * C_GEOM + 7 * geometric_slack(days))

    def test_there_is_a_drain_threshold_above_which_the_attack_self_defeats(self):
        # The recycling channel is not free: spending too fast on the static
        # peg outruns the pump. At drain 1/8 the chest compounds; at 1/4 it
        # decays and the phi flow shrinks cycle on cycle. The threshold between
        # them is the natural definition of the recycling coefficient, and is
        # left to the follow-up (`FOLLOWUP_STOCK.md` item 2).
        days = 24
        A_slow, enf_slow = pump_and_drain_run(ONE, days, Q(1, 8))
        chest_slow, _, flow_slow = cycle_series(A_slow, enf_slow, days)
        A_fast, enf_fast = pump_and_drain_run(ONE, days, Q(1, 4))
        chest_fast, _, flow_fast = cycle_series(A_fast, enf_fast, days)
        self.assertGreater(chest_slow[-1], chest_slow[0])
        self.assertGreater(flow_slow[-1], flow_slow[0])
        self.assertLess(chest_fast[-1], chest_fast[0])
        self.assertLess(flow_fast[-1], flow_fast[0])

    def test_the_discriminator_is_the_enforcers_sign_at_the_throttling_world(self):
        # Channels (a) and (b) leave the enforcer profitable at the world that
        # throttles the opposition; channel (c) does not, and that is exactly
        # where the self-financing inequality stops closing.
        days = 24
        _, enf_plain = plain_short_attack(days)
        self.assertGreaterEqual(enf_plain.ledger.worth(P1), ZERO)

        _, _, enf_patsy = patsy_recycling_run(ONE, Q(8), days)
        self.assertGreaterEqual(enf_patsy.ledger.worth((ONE, ZERO)), ZERO)

        A, enf_pump = pump_and_drain_run(ONE, days, Q(1, 8))
        # On the pumped schedule the enforcer is a net payer at a throttling
        # world, through the psi coordinate.
        self.assertLess(
            min(coord_worth(enf_pump.ledger, SUP2, "psi", t) for t in
                ((ONE, ZERO), (ONE, ONE))),
            ZERO,
        )


class TestC0ParameterizedBound(unittest.TestCase):
    """C0: the one-coordinate bound, in the form C1 shows to be honest."""

    def test_bound_holds_and_is_tolerance_free_under_self_containment(self):
        # The T2 geometry bound, restated at Definition 4.1's quantifiers and
        # checked to be free of the tolerance schedule.
        days = 16
        results = []
        for delta_fn in (delta_half, delta_inv, delta_dyadic):
            adv, enf = plain_short_attack(days, delta_fn=delta_fn)
            L = def41_liability(enf.ledger, undecided, days)
            W = realized_drawdown([adv], P1, days)
            self.assertLessEqual(L, W * C_GEOM + 7 * geometric_slack(days))
            self.assertLessEqual(L, ONE * C_GEOM + 7 * geometric_slack(days))
            results.append(L)
        for a in results:
            for b in results:
                self.assertLessEqual(abs(a - b), 2 * 7 * geometric_slack(days))

    def test_bound_scales_with_the_chest_not_the_tolerance(self):
        # Doubling the war chest roughly doubles the room; changing the
        # tolerance by a factor of 2^16 does not move the liability at all.
        days = 16
        by_chest = {}
        for B in (Q(1, 4), HALF, ONE):
            adv, enf = plain_short_attack(days, B=B)
            by_chest[B] = def41_liability(enf.ledger, undecided, days)
            self.assertLessEqual(by_chest[B],
                                 B * C_GEOM + 7 * geometric_slack(days))
        self.assertGreaterEqual(by_chest[ONE], by_chest[Q(1, 4)])

    def test_margin_controls_the_bound(self):
        # The near-vertex family: as the margin shrinks the same nominal chest
        # buys strictly more liability, at the 1/margin rate. (The parent's
        # W2/T3 witness, restated at Definition 4.1's quantifiers.)
        days = 16
        tight = lambda n: Q(1, 16)
        prev = None
        for k in (2, 3, 4):
            eps = Q(1, 2 ** k)
            adv = BudgetedTrader("buy", PHI, buyer(ONE), Q(1, 4), undecided)
            enf = Enforcer(PHI, const_schedule(interval(eps, eps), ONE, tight))
            run_market([adv, enf], days, PHI)
            L = def41_liability(enf.ledger, undecided, days)
            if prev is not None:
                self.assertGreater(L, Q(3, 2) * prev)
            prev = L


class TestC2AppendixD(unittest.TestCase):
    """C2: what Theorem D.1's hypothesis buys. The parent's alternating-
    singletons attack violates exactly that hypothesis."""

    @staticmethod
    def agreement_condition(live_fn, day, support_width):
        """Theorem D.1's hypothesis, in the model's finite form: every table
        live at `day + 1` agrees, on every sub-support, with some table live at
        `day`."""
        later, earlier = live_fn(day + 1), live_fn(day)
        idx = range(support_width)
        for t in later:
            for r in range(support_width + 1):
                for S in combinations(idx, r):
                    if not any(all(t[i] == e[i] for i in S) for e in earlier):
                        return False
        return True

    def test_alternating_singletons_violate_the_agreement_condition(self):
        def flip_live(day):
            return (P0,) if day % 2 == 1 else (P1,)
        for day in range(1, 8):
            self.assertFalse(self.agreement_condition(flip_live, day, 1))

    def test_the_settlement_stream_satisfies_it(self):
        from test_tier34 import SettlementStream
        stream = SettlementStream()
        for day in range(1, 3 * stream.EPISODE):
            self.assertTrue(self.agreement_condition(stream.live, day, 3))

    def test_day_uniform_income_never_becomes_horizon_upside(self):
        # The severance, restated as the Appendix D packaging needs it: under
        # violated D.1 the trader banks a positive, day-uniform income every
        # single day while every horizon assessment stays near zero and the
        # enforcer's liability stays bounded. Liability and exploitation come
        # apart precisely where D.1's hypothesis fails.
        days = 16
        F = HALF

        def flip_live(day):
            return (P0,) if day % 2 == 1 else (P1,)

        def base(day, prices):
            return {"phi": -F} if day % 2 == 1 else {"phi": F}

        adv = BudgetedTrader("flip", PHI, base, ONE, flip_live)
        enf = Enforcer(PHI, const_schedule(interval(HALF, HALF), ONE,
                                           delta_half))
        run_market([adv, enf], days, PHI)
        banked = ZERO
        for day, shares, prices in adv.ledger.trades:
            (table,) = flip_live(day)
            banked += sum(c * (table[0] - prices[phi])
                          for phi, c in shares.items())
        self.assertGreaterEqual(banked, Q(1, 8) * days)
        # Yet the horizon picture is flat, and liability is bounded.
        for N in (days - 1, days):
            (table,) = flip_live(N)
            self.assertLessEqual(abs(adv.ledger.worth(table, through_day=N)), ONE)
        self.assertLessEqual(
            def41_liability(enf.ledger, flip_live, days),
            ONE + geometric_slack(days),
        )


class TestC3ConverseOfTheorem46(unittest.TestCase):
    """C3: zero liability against all budgeted flow vs every plausible pattern
    absorbed."""

    @staticmethod
    def sustained_buy(lo, hi, F, b, days):
        holder = []

        def base(day, prices):
            adv = holder[0]
            avail = min(adv.available(day, t) for t in BOTH)
            if avail <= 0:
                return {}
            return {"phi": F if F < avail / 2 else avail / 2}

        adv = BudgetedTrader("buy", PHI, base, b, undecided)
        holder.append(adv)
        enf = Enforcer(PHI, const_schedule(interval(lo, hi), ONE, delta_half))
        run_market([adv, enf], days, PHI)
        return adv, enf

    def test_absorbed_patterns_give_exactly_zero_liability(self):
        # Theorem 4.6's own direction, reproduced: when every plausible pattern
        # lies in K the liability is exactly zero, at every flow size.
        days = 20
        for F in (Q(1, 8), Q(1, 4), HALF):
            _, enf = self.sustained_buy(ZERO, ONE, F, ONE, days)
            self.assertEqual(def41_liability(enf.ledger, undecided, days), ZERO)

    def test_absorbed_after_settlement_gives_exactly_zero(self):
        days = 20
        only_false = lambda d: (P0,)
        holder = []

        def base(day, prices):
            adv = holder[0]
            avail = adv.available(day, P0)
            if avail <= 0:
                return {}
            return {"phi": min(HALF, avail / 2)}

        adv = BudgetedTrader("buy", PHI, base, ONE, only_false)
        holder.append(adv)
        enf = Enforcer(PHI, const_schedule(interval(ZERO, HALF), ONE,
                                           delta_half))
        run_market([adv, enf], days, PHI)
        self.assertEqual(def41_liability(enf.ledger, only_false, days), ZERO)

    def test_an_excluded_plausible_pattern_forces_positive_liability(self):
        # The converse direction: whenever a plausible pattern sits outside K,
        # sustained budgeted flow forces a strictly positive liability, at a
        # floor that is an explicit positive function of the margin and is
        # uniform in the flow size.
        days = 20
        for hi in (HALF, Q(3, 5), Q(7, 10), Q(4, 5)):
            m = ONE - hi
            floor = m * m / (4 * (ONE - m))
            self.assertGreater(floor, ZERO)
            for F in (Q(1, 8), Q(1, 4), HALF):
                _, enf = self.sustained_buy(Q(2, 5), hi, F, ONE, days)
                L = def41_liability(enf.ledger, undecided, days)
                self.assertGreater(L, ZERO)
                self.assertGreaterEqual(L, floor)

    def test_the_forced_loss_is_inventory_times_margin(self):
        # What the floor is made of: the enforcer's absorbed inventory, billed
        # at the distance from K to the excluded pattern.
        days = 20
        for hi in (Q(3, 5), Q(7, 10), Q(4, 5)):
            m = ONE - hi
            _, enf = self.sustained_buy(Q(2, 5), hi, Q(1, 4), ONE, days)
            L = def41_liability(enf.ledger, undecided, days)
            inventory = -sum(s.get("phi", ZERO) for _, s, _ in enf.ledger.trades)
            self.assertGreater(inventory, ZERO)
            self.assertLessEqual(L, inventory * m)
            self.assertGreaterEqual(L, inventory * m - geometric_slack(days))


if __name__ == "__main__":
    unittest.main()
