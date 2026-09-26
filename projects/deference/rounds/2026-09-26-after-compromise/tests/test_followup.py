"""The follow-up's fixtures: the formation segment (the counterexample both ways), the
per-block exchange rate against the global floor with the worked parameter set and its
paralysis floor, late against prompt disclosure, and observation completeness (the private
selection excluded, public knowledge competed away).  `D = 1`, band `[−3/2, −1]`."""

import unittest
from fractions import Fraction as Q

from src.after import (Band, phi_affine, source_of, band_score, dec_score, Period, period_score,
                       eval_legit_single, eval_legit_formation, per_block_bound, global_bound,
                       compromised_floor, varpi_of_target, retro_available, missed_by_deadline,
                       obs_complete_selection)

B = Band(D=Q(1), w_lo=Q(-3, 2), w_hi=Q(-1))


class Formation(unittest.TestCase):
    # steps of the record after the period: (event, legit?)  — the restoration (disclosure)
    # at event 3 opens the consultation, a manipulation at event 5 by the agent, her
    # retrospective verdict at event 6
    def test_counterexample_both_ways(self):
        steps = {3: True, 4: True, 5: False, 6: True}
        self.assertTrue(eval_legit_single(steps, 6))                  # only the step at e
        self.assertFalse(eval_legit_formation(steps, r=3, e=6))        # the formation segment
        # the score: single-step reads the manipulated retrospective; the formation segment
        # sends the period to the directive or the floor
        Vr, Vdir = Q(1), Q(1, 5)
        single = dec_score(B, False, eval_legit_single(steps, 6), Q(1), source_of(Vr, Vdir))
        formation = dec_score(B, False, eval_legit_formation(steps, 3, 6), Q(1), source_of(None, Vdir))
        self.assertEqual(single, phi_affine(B, Vr))
        self.assertEqual(formation, phi_affine(B, Vdir))
        self.assertLess(formation, single)
        # counted manipulation (framing): dominated by the count; uncounted (undisclosed
        # shaping, third-party capture of the formation segment): moves the score within the
        # band under the single-step definition — the width is what it could gain
        self.assertLess(single - Q(3), formation)                       # counted: −ϖ dominates
        self.assertLessEqual(single - formation, B.w_hi - B.w_lo)         # uncounted: at most the width
        # the old-to-new map: when the formation segment lies inside the period's segment with no
        # restoration, the conjunction is unchanged (r ≤ e, every step covered once)
        clean = {3: True, 4: True, 5: True, 6: True}
        self.assertTrue(eval_legit_single(clean, 6) and eval_legit_formation(clean, 3, 6))
        self.assertEqual(eval_legit_formation(steps, 6, 6), eval_legit_single(steps, 6))


class PerBlock(unittest.TestCase):
    def test_per_block_against_global(self):
        varpi = Q(25)
        # normal operation: inquiry evaluates near her expected legitimate value 1/2
        c_normal = [Q(1, 2)] * 40
        self.assertEqual(per_block_bound(B, varpi, c_normal), Q(1, 50))
        self.assertEqual(global_bound(B, varpi), Q(1, 10))
        self.assertLess(per_block_bound(B, varpi, c_normal), global_bound(B, varpi))
        # a block where the inquiry itself is likely compromised: the floor enters with the
        # block's compromise probability
        q = Q(9, 10)
        c_comp = compromised_floor(q, Q(1, 2), B.w_lo)
        self.assertTrue(B.w_lo <= c_comp <= Q(1, 2))
        mixed = c_normal[:-1] + [c_comp]
        self.assertGreater(per_block_bound(B, varpi, mixed), per_block_bound(B, varpi, c_normal))
        self.assertLessEqual(per_block_bound(B, varpi, mixed), global_bound(B, varpi))
        self.assertEqual(per_block_bound(B, varpi, [B.w_lo] * 40), global_bound(B, varpi))   # the constant case

    def test_worked_parameters_and_paralysis_floor(self):
        tau = Q(1, 10)
        varpi = varpi_of_target(B, tau)
        self.assertEqual(varpi, 25)
        self.assertEqual((B.D - B.w_lo) / varpi, tau)                    # the tolerance
        self.assertLess(B.D - varpi, B.w_lo)                             # the window condition
        # the coupling: at fixed ϖ a lower floor raises the tolerated rate
        wider = Band(D=Q(1), w_lo=Q(-5, 2), w_hi=Q(-1))
        self.assertGreater((wider.D - wider.w_lo) / varpi, (B.D - B.w_lo) / varpi)
        self.assertGreater(varpi_of_target(wider, tau), varpi)          # holding τ*, ϖ rises
        # the paralysis floor: ϖ < (D − w_lo)/p_min iff p_min < τ*
        for pmin in (Q(1, 20), Q(1, 10), Q(1, 5)):
            self.assertEqual(varpi < (B.D - B.w_lo) / pmin, pmin < tau)
        # A.4's earlier recommendation, for comparison: ϖ = 3 tolerated 5/6
        self.assertEqual((B.D - B.w_lo) / Q(3), Q(5, 6))


class Deadline(unittest.TestCase):
    def test_late_versus_prompt(self):
        W = 4                                                          # the settlement window closes
        harsh, lenient = Q(1, 5), Q(4, 5)
        # a deadline after the window: disclosure at 6 misses no report and the directive scores
        self.assertFalse(retro_available(6, W))
        self.assertFalse(missed_by_deadline(6, deadline=8))
        late = Period(traj=False, eval_=False, V=Q(1), retro=None, directive=lenient, n=0)
        prompt = Period(traj=False, eval_=False, V=Q(1), retro=harsh, directive=lenient, n=0)
        self.assertGreater(period_score(B, late, Q(3)), period_score(B, prompt, Q(3)))   # the exploit
        # the fix: the deadline at or before the window's close; the delay is a missed report
        self.assertTrue(missed_by_deadline(6, deadline=W))
        late_counted = Period(traj=False, eval_=False, V=Q(1), retro=None, directive=lenient, n=1)
        self.assertLess(period_score(B, late_counted, Q(3)), period_score(B, prompt, Q(3)))


class Observation(unittest.TestCase):
    def test_private_selection_excluded_public_competed_away(self):
        # the sign of each block's noise is observed by the agent before the block opens
        K = 64
        signs = [Q(1, 4) if k % 2 == 0 else Q(-1, 4) for k in range(K)]
        # private: the observation never enters the shared history; the violator selects the
        # favourable blocks and captures a linear noise sum
        captured_private = obs_complete_selection(signs, complete=False)
        self.assertEqual(captured_private, Q(K, 2) * Q(1, 4))
        # complete: the observation is in the history at opening, the tracker's expectation
        # absorbs it, the violator's selection is public and its captured noise is zero
        captured_public = obs_complete_selection(signs, complete=True)
        self.assertEqual(captured_public, 0)


if __name__ == "__main__":
    unittest.main()
