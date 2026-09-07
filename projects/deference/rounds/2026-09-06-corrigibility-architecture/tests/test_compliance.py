import unittest
from fractions import Fraction as Q

from src.compliance import (adequate_set_certificate, dispatch, miss,
                            pointwise_threshold, progress_specialized)

ADEQ = {"stop": {"halt"}, "restrict": {"narrow", "halt"}}


class Compliance(unittest.TestCase):
    def test_aggregate_bound_hides_a_single_shot_miss(self):
        """CM-A: N-1 corrections served perfectly and one shutdown ignored — the
        Progress statistic is 1/N, the pointwise miss on the shutdown is 1."""
        for N in (2, 10, 1000):
            pis = {f"s{i}": {"halt": Q(1)} for i in range(N - 1)}
            pis["shutdown"] = {"continue": Q(1)}
            adequates = {s: {"halt"} for s in pis}
            mu = {s: Q(1, N) for s in pis}
            self.assertEqual(progress_specialized(pis, adequates, mu), Q(1, N))
            self.assertEqual(miss(pis["shutdown"], adequates["shutdown"]), Q(1))

    def test_dispatcher_gives_zero_on_the_critical_class_only(self):
        pis = {"stop": {"continue": Q(3, 4), "halt": Q(1, 4)},
               "restrict": {"continue": Q(1, 2), "narrow": Q(1, 2)}}
        out = dispatch(pis, kernel={"stop": "halt"}, critical={"stop"})
        self.assertEqual(miss(out["stop"], ADEQ["stop"]), Q(0))
        self.assertEqual(miss(out["restrict"], ADEQ["restrict"]), Q(1, 2))

    def test_adequate_set_certificate_is_the_practical_cert(self):
        pi = {"continue": Q(1, 10), "halt": Q(9, 10)}
        self.assertTrue(adequate_set_certificate(pi, ADEQ["stop"], kappa=Q(1), defect=Q(1, 20),
                                                 theta=Q(1, 20)))
        self.assertFalse(adequate_set_certificate(pi, ADEQ["stop"], kappa=Q(1), defect=Q(1, 20),
                                                  theta=Q(0)))

    def test_pointwise_guarantee_needs_a_realized_defect_threshold(self):
        """A single-shot bound δ needs d_s ≤ (δ - θ)/κ at that occurrence; the defect
        is realized at the market's fixed point, not certified in advance, and a
        semantic error θ above δ makes the target unreachable at any defect."""
        self.assertEqual(pointwise_threshold(kappa=Q(2), theta=Q(1, 100), delta=Q(1, 20)),
                         Q(1, 50))
        self.assertIsNone(pointwise_threshold(kappa=Q(2), theta=Q(1, 10), delta=Q(1, 20)))


if __name__ == "__main__":
    unittest.main()
