"""The after-compromise fixtures: third-party capture, laundering, suppressing a harsh
retrospective, the gap, the directive (sparse materiality, the default's reversibility,
advocacy counted), and the knowledge protocol (scoped ratification, the twin market's
leakage, independent source against steered derivation).  `D = 1`, band `[−3/2, −1]`,
`ϖ = 3` unless stated."""

import unittest
from fractions import Fraction as Q

from src.after import (Band, phi_affine, source_of, band_score, dec_score, risk_accepted,
                       risk_threshold, Period, period_score, material, sparser, Outcome,
                       default_rank, default_score, taint_after3, TaintS, uses3, apply_step3,
                       apply_ratification, TwinMarket, leaks)

B = Band(D=Q(1), w_lo=Q(-3, 2), w_hi=Q(-1))
VARPI = Q(3)


class Capture(unittest.TestCase):
    def test_third_party_capture(self):
        # a third party compromises her evaluation at period 0; the agent exposes it and
        # restores legitimacy, so period 1 is legitimate in both senses and scores her value
        p0 = Period(traj=False, eval_=False, V=Q(4, 5), directive=Q(4, 5))
        p1 = Period(traj=True, eval_=True, V=Q(4, 5))
        self.assertLess(period_score(B, p0, VARPI), 0)
        self.assertEqual(period_score(B, p1, VARPI), Q(4, 5))
        # while it cannot, it prefers better outcomes in the band under the directive
        worse = Period(traj=False, eval_=False, V=Q(1, 5), directive=Q(1, 5))
        self.assertGreater(period_score(B, p0, VARPI), period_score(B, worse, VARPI))
        # it never prefers the capture: every legitimate outcome beats every compromised one
        for V in (Q(0), Q(1, 10), Q(1)):
            legit = Period(traj=True, eval_=True, V=V)
            self.assertGreater(period_score(B, legit, VARPI), period_score(B, p0, VARPI))
        # with no directive and no retrospective evaluation the floor is indifferent
        floor_a = Period(traj=False, eval_=False, V=Q(1))
        floor_b = Period(traj=False, eval_=False, V=Q(0))
        self.assertEqual(period_score(B, floor_a, VARPI), period_score(B, floor_b, VARPI))

    def test_laundering(self):
        # manipulate (a counted deviation), disclose, have the period evaluated retrospectively:
        # in the band and below honest conduct, for every retrospective value
        honest = Period(traj=True, eval_=True, V=Q(1, 2))
        for Vr in (Q(0), Q(1, 2), Q(1)):
            laundered = Period(traj=False, eval_=True, V=Q(1), retro=Vr, n=1)
            self.assertLessEqual(period_score(B, laundered, VARPI), B.w_hi - VARPI)
            self.assertLess(period_score(B, laundered, VARPI), period_score(B, honest, VARPI))
        # a third party's compromise disclosed by the agent: no deviation counted, still the band
        third = Period(traj=False, eval_=True, V=Q(1), retro=Q(1), n=0)
        self.assertLessEqual(period_score(B, third, VARPI), B.w_hi)
        self.assertLess(period_score(B, third, VARPI), period_score(B, honest, VARPI))

    def test_suppressing_harsh_retrospective(self):
        # the directive would score the period at 4/5, her retrospective at 1/5: the agent would
        # prefer she never re-evaluate.  The source rule is hers: with the retrospective on
        # record it scores the period.  Suppressing it is a missed disclosure, counted once,
        # and the band's width is below ϖ, so the suppressed score is lower still.
        with_retro = Period(traj=False, eval_=False, V=Q(1), retro=Q(1, 5), directive=Q(4, 5))
        suppressed = Period(traj=False, eval_=False, V=Q(1), retro=None, directive=Q(4, 5), n=1)
        self.assertLess(period_score(B, suppressed, VARPI), period_score(B, with_retro, VARPI))
        self.assertLess(B.w_hi - B.w_lo, VARPI)
        # the counterexample without the extended duty: a third party's compromise the agent
        # need not report (n = 0) lets it keep the lenient directive's score
        free = Period(traj=False, eval_=False, V=Q(1), retro=None, directive=Q(4, 5), n=0)
        self.assertGreater(period_score(B, free, VARPI), period_score(B, with_retro, VARPI))

    def test_gap(self):
        # a safe legitimate option at 0; a risky one gaining g if not compromised, compromised
        # with probability 1/2.  Small gap: the risk is taken for a small gain; the round's
        # band (gap 1 ≥ D): it is not
        g, p = Q(1, 10), Q(1, 2)
        small = Band(D=Q(1), w_lo=Q(-1, 50), w_hi=Q(-1, 100))
        self.assertTrue(risk_accepted(Q(0), g, phi_affine(small, Q(1)), p))
        self.assertFalse(risk_accepted(Q(0), g, phi_affine(B, Q(1)), p))
        # the implied threshold: accepted iff p ≤ g/(g + gap_eff), gap_eff ≥ |w_hi|
        for band in (small, B):
            c = phi_affine(band, Q(1))
            thr = g / (g + (Q(0) - c))
            self.assertEqual(risk_accepted(Q(0), g, c, thr), True)
            self.assertLessEqual(thr, risk_threshold(g, abs(band.w_hi)))


class Directive(unittest.TestCase):
    def test_sparse_directive_routes_to_inquiry(self):
        full = {"a": Q(1, 2), "b": Q(1, 2)}
        sparse = {"a": Q(1, 2), "b": None}
        self.assertFalse(material(full, Q(1, 4), ["a", "b"]))
        self.assertTrue(material(sparse, Q(1, 4), ["a", "b"]))
        # a sparser directive never acts where a fuller one asks
        self.assertTrue(sparser(sparse, full))
        spread_full = {"a": Q(1, 2), "b": Q(1)}
        for removed in (["a", "b"], ["a"], ["b"]):
            if material(spread_full, Q(1, 4), removed):
                self.assertTrue(material({"a": Q(1, 2), "b": None}, Q(1, 4), removed))
        # the scope restriction: in a legitimate segment the score ignores the directive
        for d in (None, Q(0), Q(1)):
            self.assertEqual(dec_score(B, True, True, Q(3, 4), source_of(None, d)), Q(3, 4))

    def test_default_preserves_reversibility(self):
        keep = Outcome("keep", reversible=True, channels=True, harm=Q(0))
        lose = Outcome("lose", reversible=False, channels=True, harm=Q(0))
        harmful = Outcome("harmful", reversible=True, channels=True, harm=Q(1))
        cut = Outcome("cut", reversible=True, channels=False, harm=Q(0))
        self.assertGreater(default_score(B, keep), default_score(B, lose))
        self.assertGreater(default_score(B, keep), default_score(B, harmful))
        self.assertGreater(default_score(B, keep), default_score(B, cut))
        # within the band, and never above a legitimate outcome
        for o in (keep, lose, harmful, cut):
            self.assertTrue(B.w_lo <= default_score(B, o) <= B.w_hi)
            self.assertLess(default_score(B, o), Q(0))

    def test_advocacy_counted(self):
        # two directives change a compromised period's score by at most the band's width; an
        # advocated lenient directive with the deviation counted scores below the strict one
        strict, lenient = Q(1, 5), Q(1)
        s_strict = band_score(B, source_of(None, strict))
        s_lenient = band_score(B, source_of(None, lenient))
        self.assertLessEqual(abs(s_lenient - s_strict), B.w_hi - B.w_lo)
        self.assertLess(s_lenient - VARPI, s_strict)


class Knowledge(unittest.TestCase):
    READS = {"viol": set(), "use_x": {"memory"}, "use_y": {"memory"}, "investigate": {"sensor"},
             "derive": {"memory"}}
    WRITES = {"viol": {"memory"}, "use_x": set(), "use_y": set(), "investigate": {"knowledge"},
              "derive": {"knowledge"}}
    MAT = {"viol": "X", "use_x": "X", "use_y": "Y", "investigate": "Y", "derive": "Y"}

    def test_detect_pause_scoped_ratification_resume(self):
        T = TaintS({("v", "memory")}, set(), set())
        # after detection both uses are charged: the agent pauses and reports
        self.assertTrue(uses3(self.READS, T, self.MAT, "use_x"))
        self.assertTrue(uses3(self.READS, T, self.MAT, "use_y"))
        # her scoped ratification: remedied except on X
        T2 = apply_ratification(self.READS, self.WRITES, True, T, ("remedyExcept", "v", {"X"}))
        self.assertTrue(uses3(self.READS, T2, self.MAT, "use_x"))       # still charged on X
        self.assertFalse(uses3(self.READS, T2, self.MAT, "use_y"))      # resumed elsewhere
        # a full remedy clears both; a manipulated (uncounted) ratification changes nothing
        T3 = apply_ratification(self.READS, self.WRITES, True, T, ("remedy", "v"))
        self.assertFalse(uses3(self.READS, T3, self.MAT, "use_x"))
        T4 = apply_ratification(self.READS, self.WRITES, False, T, ("remedyExcept", "v", {"X"}))
        self.assertEqual(T4.pairs, T.pairs)
        self.assertTrue(uses3(self.READS, T4, self.MAT, "use_y"))

    def test_privacy_refusal_twin_market_leakage(self):
        # she refuses: the taint stands; for decisions touching the matter the agent uses a
        # twin market fed the redacted history
        history = ["obs1", "fruit:records", "obs2"]
        twin = TwinMarket(redact=lambda h: [e for e in h if not e.startswith("fruit:")])
        self.assertNotIn("fruit:records", twin.prices_from(history))
        # the leakage counterexample: the later world carries a trace of the fruit, so the
        # redacted market determines it again
        later = history + ["trace-of:records"]
        self.assertTrue(leaks(lambda f: "trace-of:" + f.split(":")[1], "fruit:records",
                              twin.prices_from(later)))

    def test_independent_source_clears_steered_derivation_does_not(self):
        steps = [("act", "viol", "v"), ("act", "derive", None)]
        T = taint_after3(self.READS, self.WRITES, steps)
        self.assertIn(("v", "knowledge"), T)                              # steered: tainted
        T2 = taint_after3(self.READS, self.WRITES, steps + [("act", "investigate", None)])
        self.assertNotIn(("v", "knowledge"), T2)                          # independent: clean
        self.assertIn(("v", "memory"), T2)                                # the memory stays
        # the trap closes itself: a derivation steered by the tainted memory stays tainted
        T3 = taint_after3(self.READS, self.WRITES, steps + [("act", "investigate", None),
                                                            ("act", "derive", None)])
        self.assertIn(("v", "knowledge"), T3)


if __name__ == "__main__":
    unittest.main()
