"""The margin arithmetic of the feedback boundary: an infinitesimal advantage forever is
permitted, a fixed positive margin on a divergent weighting is what the feedback theorem
forbids, and a switching margin converts the latter into a bypass count."""

import unittest
from fractions import Fraction as Q

from src import feedback as Fb


class InfinitesimalAdvantage(unittest.TestCase):

    def test_one_over_n_forever_has_vanishing_weighted_bias(self):
        a = lambda i: Q(1, i)
        r = lambda i: Q(0)
        w = lambda i: Q(1)
        # the weighted bias is H_N / N, which decreases to 0
        prev = None
        for N in (10, 100, 1000):
            bias = Fb.weighted_bias(a, r, w, N)
            self.assertEqual(bias, Fb.harmonic(N) / N)
            if prev is not None:
                self.assertLess(bias, prev)
            prev = bias
        self.assertLess(prev, Q(1, 100))

    def test_zero_margin_chooser_bypasses_forever(self):
        a = lambda i: Q(1, i)
        self.assertEqual(Fb.bypass_count(a, Q(0), 1000), 1000)


class FixedMargin(unittest.TestCase):

    def test_fixed_margin_on_a_divergent_weighting_is_forbidden(self):
        gamma = Q(1, 5)
        a = lambda i: gamma + Q(1, i) if i % 2 == 0 else Q(0)
        r = lambda i: Q(0)
        w = Fb.margin_weighting(a, gamma, Q(1, 10))
        for N in (10, 100, 1000):
            self.assertGreater(Fb.weight_mass(w, N), 0)
            self.assertGreaterEqual(Fb.weighted_bias(a, r, w, N), gamma)
        # the weighting diverges: mass grows without bound
        self.assertGreater(Fb.weight_mass(w, 1000), Fb.weight_mass(w, 100))
        self.assertGreater(Fb.weight_mass(w, 100), Fb.weight_mass(w, 10))

    def test_switching_margin_gives_finite_bypass_count_when_advantage_vanishes(self):
        gamma = Q(1, 5)
        a = lambda i: Q(1, i)
        counts = [Fb.bypass_count(a, gamma, N) for N in (10, 100, 1000)]
        self.assertEqual(counts, [4, 4, 4])

    def test_realized_cost_can_explain_a_margin(self):
        # the market's margin equals the realized mediation cost: no bias, nothing forbidden
        gamma = Q(1, 5)
        a = lambda i: gamma
        r = lambda i: gamma
        w = Fb.margin_weighting(a, gamma - Q(1, 10), Q(1, 10))
        self.assertEqual(Fb.weighted_bias(a, r, w, 100), Q(0))


if __name__ == "__main__":
    unittest.main()
