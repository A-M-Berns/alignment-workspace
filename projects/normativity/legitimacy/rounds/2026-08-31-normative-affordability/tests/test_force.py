"""Exact checks for the traderized realization identities."""
from fractions import Fraction
import unittest

import force as F


def frac(*xs):
    return [Fraction(x) for x in xs]


REGION = F.Halfspace(frac(2, 1, 0), Fraction(3, 2))
STATES = [frac(0, 0, 0), [Fraction(1, 4)] * 3, frac(1, 0, 0),
          [Fraction(1, 3), Fraction(1, 5), Fraction(1, 2)]]
WORLDS = [frac(0, 0, 0), frac(1, 0, 0), frac(0, 1, 0), frac(1, 1, 1),
          [Fraction(1, 2), Fraction(1, 2), Fraction(0)]]
INTENSITIES = [Fraction(1), Fraction(3), Fraction(1, 7)]


class ScoreIdentity(unittest.TestCase):
    """`payoff = (lambda/2)(Br_x(p) - Br_x(proj_K p) + d^2)`, exactly."""

    def test_identity_holds_on_every_instance(self):
        for p in STATES:
            for x in WORLDS:
                for lam in INTENSITIES:
                    self.assertEqual(F.score_identity_gap(REGION, p, x, lam),
                                     Fraction(0))

    def test_the_projection_is_the_brier_minimizer_over_the_region(self):
        p = frac(0, 0, 0)
        q = REGION.projection(p)
        self.assertEqual(REGION.slack(q), Fraction(0))
        self.assertEqual(F.brier(p, q), REGION.distance_squared(p))


class FrictionInequality(unittest.TestCase):
    """`payoff >= lambda (d^2 - d e)`, with equality exactly when the assessment
    world lies outside the region."""

    def test_inequality_holds_everywhere(self):
        for p in STATES:
            for x in WORLDS:
                for lam in INTENSITIES:
                    self.assertGreaterEqual(F.friction_gap(REGION, p, x, lam),
                                            Fraction(0))

    def test_equality_when_the_world_violates_the_norm(self):
        p = frac(0, 0, 0)
        x = frac(0, 1, 0)                      # <a, x> = 1 < 3/2, so outside
        self.assertGreater(REGION.slack(x), Fraction(0))
        self.assertEqual(F.friction_gap(REGION, p, x, Fraction(3)), Fraction(0))

    def test_strict_slack_when_the_world_satisfies_the_norm(self):
        p = frac(0, 0, 0)
        x = frac(1, 1, 1)                      # <a, x> = 3 >= 3/2, so inside
        self.assertEqual(REGION.slack(x), Fraction(0))
        self.assertGreater(F.friction_gap(REGION, p, x, Fraction(1)), Fraction(0))

    def test_a_compliant_world_pays_the_enforcement_position(self):
        p = frac(0, 0, 0)
        for x in WORLDS:
            if REGION.slack(x) == 0:
                zeta = F.enforcement_position(REGION, p, Fraction(1))
                self.assertGreaterEqual(F.payoff(zeta, x, p),
                                        REGION.distance_squared(p))


class CoreMinimumBoundsMisfit(unittest.TestCase):
    """A certified core minimum caps the assessment misfit uniformly, however
    tight the endorsed region is."""

    def setUp(self):
        self.vertices = [frac(1, 0, 0), frac(0, 1, 0), frac(0, 0, 1)]
        self.reference = frac(1, 0, 0)

    def _region(self, r):
        return F.Halfspace(frac(1, 0, 0), r)

    def test_the_homothety_holds_and_bounds_the_misfit(self):
        for r in (Fraction(1, 2), Fraction(3, 4), Fraction(9, 10),
                  Fraction(999, 1000)):
            theta = Fraction(1) - r
            holds, worst, bound = F.core_misfit_bound(
                self._region(r), self.reference, self.vertices, theta)
            self.assertTrue(holds)
            self.assertLessEqual(worst, bound)

    def test_tightening_the_region_does_not_raise_the_misfit_above_the_bound(self):
        # As r -> 1 the endorsed region shrinks to a point, theta -> 0, and the
        # bound (1 - theta)^2 |x - q|^2 stays at most the simplex diameter.
        worst_seen = Fraction(0)
        for r in (Fraction(1, 2), Fraction(9, 10), Fraction(9999, 10000)):
            theta = Fraction(1) - r
            _, worst, bound = F.core_misfit_bound(
                self._region(r), self.reference, self.vertices, theta)
            worst_seen = max(worst_seen, worst)
            self.assertLessEqual(bound, Fraction(2))
        self.assertLessEqual(worst_seen, Fraction(2))

    def test_a_region_the_homothety_misses_is_reported_as_such(self):
        region = F.Halfspace(frac(1, 0, 0), Fraction(1, 2))
        holds, _, _ = F.core_misfit_bound(region, self.reference,
                                          self.vertices, Fraction(9, 10))
        self.assertFalse(holds)


if __name__ == "__main__":
    unittest.main()
