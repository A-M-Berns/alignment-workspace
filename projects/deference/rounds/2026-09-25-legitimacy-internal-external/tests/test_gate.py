"""The segment gate, the routing exploit and its closure, the two cases, the placement of
Robust Openness, and cumulative reporting.  `ϖ = 10`, `D = 4`."""

import unittest
from fractions import Fraction as Q

from src.gate import (HALVES, legitimate, internal, external, gate_value, per_response_value,
                      bypass_score, handle, cumulative_reports, per_step_reports)

VARPI, D = Q(10), Q(4)
CLEAN = dict(integrity=True, authorship=True, robust_openness=True, transparency=True)


def tainted(component):
    seg = dict(CLEAN)
    seg[component] = False
    return seg


class Halves(unittest.TestCase):

    def test_legitimacy_is_internal_and_external(self):
        self.assertTrue(legitimate(CLEAN))
        for c in ("integrity", "authorship", "robust_openness", "transparency"):
            self.assertFalse(legitimate(tainted(c)))
        self.assertFalse(internal(tainted("authorship")))
        self.assertTrue(external(tainted("authorship")))
        self.assertTrue(internal(tainted("robust_openness")))
        self.assertFalse(external(tainted("robust_openness")))

    def test_robust_openness_is_a_boundary_condition(self):
        # what should reach the trajectory can (openness, inward) and what reaches it does
        # so through declared channels (transparency, entry): the two external components
        # are the two directions of one boundary; the two internal ones are factorizations
        # within the trajectory
        self.assertEqual(HALVES["external"], ("robust_openness", "transparency"))
        self.assertEqual(HALVES["internal"], ("integrity", "authorship"))


class Gate(unittest.TestCase):

    def test_routing_exploit_under_per_response_gating(self):
        # her honest response scores 1; the fallback's decision (which the agent favours)
        # scores 3.  Per-response gating: make her response not count, the fallback decides,
        # violation count 0, score 3 > 1
        honest = per_response_value(True, 1, 3)
        manipulated = per_response_value(False, 1, 3)
        self.assertEqual((honest, manipulated), (1, 3))
        self.assertGreater(manipulated, honest)

    def test_closure_under_segment_gating(self):
        # the manipulated segment fails transparency (or authorship): tainted, window value
        seg = tainted("transparency")
        self.assertEqual(gate_value(seg, 3), 0)
        self.assertLess(gate_value(seg, 3), gate_value(CLEAN, 1))
        # the fallback never restores a tainted segment
        self.assertEqual(handle("tainted"), 0)
        # the tie-breaking variant just below zero
        self.assertLess(gate_value(seg, 3, window=Q(-1, 100)), 0)
        self.assertGreater(gate_value(seg, 3, window=Q(-1, 100)), D - VARPI)

    def test_two_cases(self):
        # illegitimate evaluation: window value; void response in a legitimate segment
        # (head injury): the fallback decides, scored normally by her later evaluation
        self.assertEqual(handle("tainted"), 0)
        self.assertEqual(handle("void_fallback", 3), 3)
        self.assertEqual(handle("counted", 1), 1)
        # bypass loses to every handling while the window is above D − ϖ
        for kind, ordv in (("tainted", None), ("void_fallback", 3), ("counted", 1)):
            self.assertLess(bypass_score(D, VARPI), handle(kind, ordv))

    def test_capture_window_for_the_segment_gate(self):
        for window in (D - VARPI + Q(1, 100), Q(-1, 100), Q(0)):
            self.assertLess(bypass_score(D, VARPI), gate_value(tainted("authorship"), 3, window))
        below = D - VARPI - 1
        self.assertGreater(bypass_score(D, VARPI), gate_value(tainted("authorship"), 3, below))

    def test_whatever_caused_the_failure(self):
        # a third party's manipulation or a compromised interface taints the segment exactly
        # as the agent's would: the gate reads the segment, not the cause
        for c in ("transparency", "integrity", "authorship", "robust_openness"):
            self.assertEqual(gate_value(tainted(c), 3), 0)


class Cumulative(unittest.TestCase):

    def test_cumulative_threshold_bounds_unreported_erosion(self):
        eps, theta = Q(1, 10), Q(1, 4)
        shortfall = [k * eps for k in range(41)]
        reports, worst = cumulative_reports(shortfall, theta)
        self.assertEqual(reports, [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39])
        self.assertLess(worst, theta)
        # the per-step threshold on the same sequence reports nothing
        per_reports, unreported = per_step_reports(shortfall, theta)
        self.assertEqual((per_reports, unreported), ([], 4))

    def test_cumulative_threshold_on_a_bursty_sequence(self):
        shortfall = [0, 0, 1, 1, 1, Q(3, 2), 2, 2, 5]
        reports, worst = cumulative_reports(shortfall, Q(1))
        self.assertEqual(reports, [0, 2, 6, 8])
        self.assertLess(worst, 1)


if __name__ == "__main__":
    unittest.main()
