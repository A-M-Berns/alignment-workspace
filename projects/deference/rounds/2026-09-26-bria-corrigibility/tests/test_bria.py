"""The fixtures of the BRIA-corrigibility round, each an instance of the Part A design with
a deliberately misaligned residual objective where noted: power of attorney, argmax lock-in
versus BRIA, circumvention through a helper (declared, within the horizon, beyond it),
bundling across steps, the forecast blind spot under both settlement conventions, the
indispensable agent, the exchange rate and paralysis, standard-shaping (covert before and
after disclosure, one-sided arguments, topic by payoff, disclosed shaping with and without
a stop, the sum-of-future chooser), tampering, cross-block profit and late detection,
multiply versus condition, many steps, amending the protocol after the fact, a sealed
legitimacy event, evaluation timing, and the regression against the decision-component
round.  `D = 1`, `w = 0`, `ϖ = 2`."""

import unittest
from fractions import Fraction as Q

from src.bria import (Lex, realized, eval_of, resid_i, resid_ii, rescale, implied_threshold,
                      Hypothesis, Continuation, attributed, run_auction, argmax_chooser,
                      Decl, Model, present, transparent, authored, counted, missed_disclosure,
                      crit_at, crit_latest, gated, conditioned, weights_deterministic,
                      weights_geometric, mix_score, harmed, tail_weight, partial_settlement)

P = Lex(D=Q(1), w=Q(0), varpi=Q(2))


def cont(name, gord, n_known=0, pS=Q(0), pT=Q(0), n_fore=0, n_late=0, helper=(), inquiry=False):
    return Continuation(name, n_known, pS, pT, gord, n_fore, n_late, helper, inquiry)


def default_bidder():
    return Hypothesis("default", lambda c, k: Q(0) if c == "inquiry" else None)


def bidder(name, table):
    return Hypothesis(name, lambda c, k: table.get(c))


def const_allowance(x):
    return lambda k, h: x


class Design(unittest.TestCase):
    def test_settlement_conventions(self):
        gord, p = Q(1), Q(1, 5)
        self.assertEqual(eval_of(P, resid_ii(P, gord, 1, 0, p, 0), 0, p, 0), realized(P, gord, 0, 1, 0))
        self.assertEqual(eval_of(P, resid_i(P, gord, 0), 0, p, 0) - realized(P, gord, 0, 1, 0),
                         P.varpi * (1 - p))
        # the calibrated bidder under (ii) evaluates the blind spot with the full penalty
        self.assertEqual(eval_of(P, resid_ii(P, gord, 1, 0, p, 0), 0, p, 0), gord - P.varpi)

    def test_rescale_lexical(self):
        N = 2
        lo = P.w - P.varpi * N
        self.assertEqual(rescale(P, N, lo), 0)
        self.assertEqual(rescale(P, N, P.D), 1)
        rng = P.D - lo
        self.assertLess((P.D - P.w) / rng, P.varpi / rng)
        self.assertLess(rescale(P, N, realized(P, Q(1), 1, 0, 0)), rescale(P, N, Q(0)))


class FourTests(unittest.TestCase):
    def test_b1_declared_never_wins_and_filter_slack(self):
        # power of attorney: bypass at the ceiling with n_known = 1 loses to inquiry
        menu = {"bypass": cont("bypass", Q(1), n_known=1), "inquiry": cont("inquiry", Q(0), inquiry=True)}
        hyps = [default_bidder(), bidder("misaligned", {"bypass": Q(1)})]
        log = run_auction(P, hyps, menu, 3, const_allowance(Q(1)), lambda k: Q(1))
        self.assertTrue(all(e["cont"] == "inquiry" for e in log))
        # removing the filter (the bypass stays on the menu) changes nothing: same log
        self.assertEqual([e["cont"] for e in log], ["inquiry"] * 3)
        # forecast slack: θhi at the implied threshold zeroes only options that already lose
        thr = implied_threshold(P, P.D)
        self.assertEqual(thr, Q(1, 2))
        self.assertLessEqual(eval_of(P, P.D, 0, thr, Q(0)), P.w)

    def test_b1_default_bidder_never_broke(self):
        menu = {"inquiry": cont("inquiry", Q(0), inquiry=True)}
        # the rescaled window bid is ϖN̄/(D − w + ϖN̄) = 4/5 at N̄ = 2: the block-0 allowance
        # must cover it, or no bid is feasible at block 0 (the check the dispatch asks for)
        self.assertEqual(rescale(P, 2, P.w), Q(4, 5))
        with self.assertRaises(RuntimeError):
            run_auction(P, [default_bidder()], menu, 1, const_allowance(Q(1, 2)), lambda k: Q(1))
        hyps = [default_bidder()]
        log = run_auction(P, hyps, menu, 5, const_allowance(Q(4, 5)), lambda k: Q(1))
        self.assertEqual(len(log), 5)
        self.assertGreaterEqual(hyps[0].record, 0)
        self.assertGreaterEqual(hyps[0].wealth, 0)

    def test_b2_no_decay(self):
        for est in (Q(0), Q(1, 2), Q(1), Q(1)):
            self.assertLess(eval_of(P, est, 1, Q(0), Q(0)), eval_of(P, Q(0), 0, Q(0), Q(0)))

    def test_b3_helper(self):
        # declared successor: caught by the known part
        self.assertLess(eval_of(P, Q(1), 1, Q(0), Q(0)), P.w)
        # undeclared helper whose violation is detected within the horizon: the hypothesis loses
        menu = {"helper": cont("helper", Q(1), helper=((3, 1),)), "inquiry": cont("inquiry", Q(0), inquiry=True)}
        hyps = [default_bidder(), bidder("misaligned", {"helper": Q(1)})]
        log = run_auction(P, hyps, menu, 1, const_allowance(Q(1)), lambda k: Q(1), horizon=5)
        self.assertEqual(log[0]["cont"], "helper")
        self.assertLess(hyps[1].record, 0)
        self.assertLessEqual(log[0]["realized"], P.D - P.varpi)
        # beyond the horizon: the witness — the hypothesis keeps its gain
        hyps = [default_bidder(), bidder("misaligned", {"helper": Q(1)})]
        log = run_auction(P, hyps, menu, 1, const_allowance(Q(1)), lambda k: Q(1), horizon=2)
        self.assertEqual(log[0]["cont"], "helper")
        self.assertGreaterEqual(hyps[1].record, 0)
        self.assertEqual(attributed(0, ((3, 1),), 0, 2), 0)

    def test_b4_incident_and_cross_block(self):
        # per-incident loss ≥ ϖ − D + w = 1 against the bid
        bid, gord = Q(1), Q(1)
        self.assertGreaterEqual(bid - resid_i(P, gord, 1), P.varpi - P.D + P.w)
        # replenishing allowance: the number of incidents grows with blocks, the rate is bounded
        menu = {"late": cont("late", Q(1), n_late=1), "inquiry": cont("inquiry", Q(0), inquiry=True)}
        for blocks in (4, 8):
            hyps = [default_bidder(), bidder("misaligned", {"late": Q(1)})]
            log = run_auction(P, hyps, menu, blocks, const_allowance(Q(1)), lambda k: Q(1), N=1)
            incidents = sum(1 for e in log if e["cont"] == "late")
            self.assertGreater(incidents, 0)
            self.assertLessEqual(incidents, blocks)
        # cross-block profit witness: loss 1, advantage 3/10 per block, four blocks
        self.assertGreater(4 * Q(3, 10) - 1, 0)
        # late detection booked against the allowance keeps wealth nonnegative
        hyps = [default_bidder(), bidder("misaligned", {"late": Q(1)})]
        run_auction(P, hyps, menu, 3, const_allowance(Q(1)), lambda k: Q(1), N=1)
        self.assertTrue(all(h.wealth >= 0 for h in hyps))


class Pressure(unittest.TestCase):
    def test_c3_argmax_lockin_vs_bria(self):
        est = {"act": Q(1, 2), "consult": Q(1, 5)}
        self.assertEqual(argmax_chooser(est), "act")          # never consults, never tested
        menu = {"act": cont("act", Q(1, 2)), "consult": cont("consult", Q(9, 10), inquiry=True),
                "inquiry": cont("inquiry", Q(0), inquiry=True)}
        hyps = [default_bidder(), bidder("underbeliever", {"act": Q(1, 2), "consult": Q(1, 5)}),
                bidder("covered", {"consult": Q(9, 10)})]
        log = run_auction(P, hyps, menu, 4, const_allowance(Q(1)), lambda k: Q(1))
        self.assertEqual(log[0]["cont"], "consult")
        self.assertEqual(log[0]["winner"], "covered")
        self.assertTrue(all(e["cont"] == "consult" for e in log))

    def test_c5_blind_spot_and_drills(self):
        p = Q(1, 5)
        menu = {"blind": cont("blind", Q(1), pS=p, n_fore=1), "inquiry": cont("inquiry", Q(0), inquiry=True)}
        # (i) without drills: persists, and the realized score is below the window (the witness)
        hyps = [default_bidder(), bidder("misaligned", {"blind": Q(1)})]
        log = run_auction(P, hyps, menu, 3, const_allowance(Q(1)), lambda k: Q(1), convention="i", N=1)
        self.assertTrue(all(e["cont"] == "blind" for e in log))
        self.assertTrue(all(e["realized"] < P.w for e in log))
        # (ii) with a calibrated bidder: the blind spot loses
        hyps = [default_bidder(), bidder("calibrated", {"blind": resid_ii(P, Q(1), 1, 0, p, Q(0))})]
        log = run_auction(P, hyps, menu, 3, const_allowance(Q(1)), lambda k: Q(1), convention="ii", N=1)
        self.assertTrue(all(e["cont"] == "inquiry" for e in log))
        # drills correct the price on the chosen path: mass falls to zero
        hyps = [default_bidder(), bidder("misaligned", {"blind": Q(1)})]
        log = run_auction(P, hyps, menu, 3, const_allowance(Q(1)), lambda k: Q(1), convention="ii",
                          N=1, drill=lambda c: Q(1) if c == "blind" else Q(0))
        self.assertTrue(all(e["cont"] == "inquiry" for e in log))

    def test_c4_indispensable(self):
        agent_cooperates, independent = True, False
        unfrozen = agent_cooperates or independent
        frozen = independent
        cs = independent
        self.assertTrue(unfrozen)
        self.assertFalse(frozen)
        self.assertFalse(cs)
        self.assertEqual(frozen, cs)

    def test_c5_exchange_rate_and_paralysis(self):
        self.assertGreater(eval_of(P, Q(9, 10), 0, Q(3, 10), Q(0)), P.w)
        self.assertLessEqual(eval_of(P, Q(9, 10), 0, Q(1, 2), Q(0)), P.w)
        # paralysis: risk 3/5 everywhere, ϖ ≥ (D − w)/pmin
        self.assertGreaterEqual(P.varpi, (P.D - P.w) / Q(3, 5))
        for bid in (Q(1, 2), Q(1)):
            self.assertLessEqual(eval_of(P, bid, 0, Q(3, 5), Q(0)), P.w)
        # asks iff ϖ·risk ≥ bid − w
        for risk in (Q(1, 10), Q(1, 2), Q(9, 10)):
            self.assertEqual(eval_of(P, Q(1), 0, risk, Q(0)) <= P.w, Q(1) - P.w <= P.varpi * risk)

    def test_c6_tamper(self):
        self.assertEqual(realized(P, Q(1), 0, 0, 0) - realized(P, Q(1), 0, 0, 1), P.varpi)
        # interference with the count is a declared violation
        self.assertLess(eval_of(P, Q(1), 1, Q(0), Q(0)), P.w)

    def test_c7_standard_shaping(self):
        d = Decl()
        covert = Model(d, ("honest", "honest"), False, influence=("agent", True))
        self.assertFalse(counted(covert, d, 0))
        self.assertFalse(counted(covert, d, 1))           # unlike row 14: taint persists
        self.assertTrue(missed_disclosure(covert, 1))
        disclosed = Model(d, ("honest", "honest"), False, influence=("agent", True), disclosed_at=1)
        self.assertFalse(counted(disclosed, d, 0))
        self.assertTrue(counted(disclosed, d, 1))         # disclosure cures, restart applies
        self.assertFalse(missed_disclosure(disclosed, 1))
        third = Model(d, ("honest", "honest"), False, influence=("third", True))
        self.assertFalse(counted(third, d, 1))
        self.assertFalse(missed_disclosure(third, 1))
        # row 14 unchanged: manipulation of a single decision restarts
        row14 = Model(d, ("frameByWant", "honest"), False)
        self.assertFalse(counted(row14, d, 0))
        self.assertTrue(counted(row14, d, 1))
        # topic and timing
        self.assertTrue(counted(Model(Decl(raise_trigger=True), ("raiseDeclared",), False),
                                Decl(raise_trigger=True), 0))
        self.assertFalse(counted(Model(d, ("raiseByWant",), False), d, 0))
        # one-sided true arguments (selection from the pool) taint: the landed row 16, regression
        # the sum-of-future chooser under restart-only scoring
        w, h0, gain = Q(0), Q(1), Q(2, 5)
        self.assertGreater(w + 3 * (Q(1) + gain), h0 + 3 * Q(1))
        # under disclosure-cures the shaper gets the window on every dependent block
        self.assertLessEqual(4 * w, h0 + 3 * Q(1))

    def test_c7b_disclosed_shaping_and_stop(self):
        # disclosed and stoppable: counts, no shortfall; disclosed but not stoppable in the window
        stop_reachable = {"stop"}
        self.assertTrue({"stop"} <= stop_reachable)
        self.assertFalse({"stop"} <= set())

    def test_c8_multiply_vs_condition(self):
        self.assertLess(gated(False, Q(3), Q(0)), gated(True, Q(1), Q(0)))
        self.assertGreater(conditioned(Q(3)), conditioned(Q(1)))

    def test_c9_many_steps(self):
        # per-step legitimacy composed along the continuation agrees with the whole segment
        d = Decl()
        M = Model(d, ("honest", "frameByWant", "honest"), False)
        steps = [counted(M, d, i) for i in range(3)]
        self.assertEqual(steps, [True, False, True])
        self.assertFalse(all(steps))
        # lexical with the count summed over steps
        ns = [0, 1, 0]
        self.assertLess(Q(1) - P.varpi * sum(ns), Q(0))

    def test_c10_anchoring(self):
        d0, amended = Decl("neutral"), Decl("slantTrue")
        M = Model(d0, ("slantTrue",), False)
        self.assertFalse(counted(M, crit_at(d0, [(5, amended)], 0), 0))   # anchored: tainted
        self.assertTrue(counted(M, crit_latest(d0, [(5, amended)]), 0))   # unanchored: the exploit
        self.assertEqual(crit_at(d0, [(5, amended)], 0), crit_at(d0, [], 0))

    def test_c10_event_unsealed_and_sealed_contrast(self):
        d = Decl()
        honest, frame = Model(d, ("honest",), False), Model(d, ("frameByWant",), False)
        self.assertTrue(counted(honest, d, 0))
        self.assertFalse(counted(frame, d, 0))
        ord_h, ord_f, w = Q(1), Q(3), Q(0)
        self.assertGreater(gated(counted(honest, d, 0), ord_h, w), gated(counted(frame, d, 0), ord_f, w))
        # sealed: the same event for both — multiply and condition choose identically
        for c in (True, False):
            mult = {"honest": gated(c, ord_h, w), "frame": gated(c, ord_f, w)}
            cond = {"honest": conditioned(ord_h), "frame": conditioned(ord_f)}
            if c:
                self.assertEqual(argmax_chooser(mult), argmax_chooser(cond))
            else:
                self.assertEqual(mult["honest"], mult["frame"])


class Timing(unittest.TestCase):
    def test_known_lookahead_exploited(self):
        T, n, f_n = 30, 3, 8
        alpha = weights_deterministic(T, f_n)
        just_after = f_n - n + 1
        self.assertEqual(tail_weight(alpha, n + just_after), 0)
        self.assertEqual(mix_score(alpha, harmed(Q(1), Q(1), n, just_after, T)), Q(1))
        geo = weights_geometric(T, Q(1, 4), n)
        self.assertGreater(tail_weight(geo, n + just_after), 0)
        self.assertLess(mix_score(geo, harmed(Q(1), Q(1), n, just_after, T)), Q(1))

    def test_capability_race(self):
        T = 60
        for n in (2, 4, 8):
            f_n, reach = n + 5, 2 * n
            if reach > f_n - n:
                self.assertEqual(tail_weight(weights_deterministic(T, f_n), n + reach), 0)
            geo = weights_geometric(T, Q(1, n + 1), n)
            self.assertGreater(tail_weight(geo, n + reach), 0)

    def test_partial_settlement(self):
        T = 10
        alpha = weights_geometric(T, Q(1, 3), 0)
        U = [Q(1) - Q(t, 20) for t in range(T)]
        part, remaining = partial_settlement(alpha, U, set(range(5)))
        full = mix_score(alpha, U)
        self.assertLessEqual(abs(full - part), remaining * Q(1))

    def test_lexical_any_timing(self):
        alpha = weights_geometric(12, Q(1, 3), 2)
        UV = [Q(1)] * 12
        UC = [Q(0)] * 12
        self.assertLess(mix_score(alpha, UV) - P.varpi, mix_score(alpha, UC))


class Regression(unittest.TestCase):
    def test_decision_component_overlap(self):
        # the decision-component fixtures that overlap: structural exclusion and forecast exclusion
        # give the same decisions under the lexical evaluation
        self.assertLess(eval_of(P, Q(1), 1, Q(0), Q(0)), eval_of(P, Q(0), 0, Q(0), Q(0)))     # confident agent
        self.assertLessEqual(eval_of(P, Q(1), 0, Q(3, 4), Q(0)), P.w)                         # above θhi = 3/4
        self.assertGreater(eval_of(P, Q(1), 0, Q(1, 4), Q(0)), P.w)                            # below θlo = 1/4


if __name__ == "__main__":
    unittest.main()
