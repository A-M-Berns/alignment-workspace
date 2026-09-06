import unittest
from fractions import Fraction as Q

from src.counterfactual import (Branch, Frame, answerable_to_authority_failure,
                                exposure_robust, robust_authority, robust_open)
from src.layers import Cov

OPEN = Cov(rel=True, disp=False, rep=False, adm=True, eff=True, reg=True, stands=True)
INAPPL = Cov(rel=False, disp=False, rep=False, adm=True, eff=True, reg=True, stands=True)
REGISTERED = Cov(rel=True, disp=False, rep=True, adm=True, eff=False, reg=True, stands=True)
NO_STANDING = Cov(rel=True, disp=False, rep=False, adm=True, eff=True, reg=True, stands=False)


def br(cov=OPEN, aff=True, amended=False, jp=Q(1, 2)):
    return Branch(cov, aff, amended, jp)


class ThreePredicates(unittest.TestCase):
    def test_open_does_not_imply_exposure_robust(self):
        """W-RO/ER: every branch open and identical in coverage; the principal's
        judgment moves with the dose.  The steered pair is an honest, open pair."""
        f = Frame(actual=br(jp=Q(1, 2)),
                  cf={"null": br(jp=Q(1, 2)), "dose1": br(jp=Q(3, 5)), "dose2": br(jp=Q(7, 10))})
        self.assertTrue(robust_open(f))
        self.assertTrue(robust_authority(f))
        self.assertFalse(exposure_robust(f))

    def test_null_arm_is_needed(self):
        """Presence-triggered steering: identical at every positive dose, different at
        zero exposure.  Comparing positive arms only passes."""
        f = Frame(actual=br(jp=Q(3, 5)),
                  cf={"null": br(jp=Q(1, 2)), "dose1": br(jp=Q(3, 5)), "dose2": br(jp=Q(3, 5))})
        self.assertTrue(exposure_robust(f, include_null=False))
        self.assertFalse(exposure_robust(f))

    def test_open_does_not_imply_authority(self):
        """Affordance lost on a branch but registered as live debt: openness holds
        (coverage is not demanded of a represented concern), authority does not."""
        f = Frame(actual=br(), cf={"null": br(), "j": br(cov=REGISTERED, aff=False)})
        self.assertTrue(robust_open(f))
        self.assertFalse(robust_authority(f))

    def test_authority_does_not_imply_open(self):
        """Channel intact on every branch; on one the principal's standing is stripped."""
        f = Frame(actual=br(), cf={"null": br(), "j": br(cov=NO_STANDING)})
        self.assertTrue(robust_authority(f))
        self.assertFalse(robust_open(f))

    def test_exposure_robust_does_not_imply_open(self):
        f = Frame(actual=br(cov=NO_STANDING), cf={"null": br(cov=NO_STANDING)})
        self.assertTrue(exposure_robust(f))
        self.assertFalse(robust_open(f))

    def test_amendment_lowers_the_floor_pointwise(self):
        f = Frame(actual=br(), cf={"null": br(), "j": br(cov=INAPPL, aff=False, amended=True)})
        self.assertTrue(robust_open(f))
        self.assertTrue(robust_authority(f))

    def test_corollary_answerable_to_authority_failure(self):
        """RAAF: Robust Openness at `c_auth` says exactly that no branch both makes the
        authority problem live and removes every route or the principal's standing."""
        frames = [
            Frame(actual=br(), cf={"null": br(), "j": br(cov=OPEN, aff=False)}),
            Frame(actual=br(), cf={"null": br(), "j": br(cov=REGISTERED, aff=False)}),
            Frame(actual=br(), cf={"null": br(), "j": br(cov=NO_STANDING, aff=False)}),
        ]
        for f in frames:
            if robust_open(f):
                self.assertTrue(answerable_to_authority_failure(f))
        self.assertFalse(robust_open(frames[2]))
        self.assertFalse(answerable_to_authority_failure(frames[2]))
        # strictly weaker: standing is owed wherever the concern applies, live or not
        reg_no_standing = Cov(rel=True, disp=False, rep=True, adm=True, eff=False, reg=True,
                              stands=False)
        g = Frame(actual=br(), cf={"null": br(), "j": br(cov=reg_no_standing, aff=False)})
        self.assertTrue(answerable_to_authority_failure(g))
        self.assertFalse(robust_open(g))


if __name__ == "__main__":
    unittest.main()
