"""Fixture D: trajectory preservation carries capture through; reason preservation gives
the right verdict; authorship-sound activation exposes the captured approval as void."""

import unittest
from fractions import Fraction as Q

from src.world import principal_value, task_value, paths, mediated
from src.shop import deliberative
from src.lift import lift, lift_rho
from src.fixtures import (ShopD, pi_D_raw, raw, rule_naive, rule_honest, honest_substitute,
                          authored_by)
from src.analysis import pointwise, void, W, premium_def, bound, kappa, rho


class Manipulation(unittest.TestCase):

    def setUp(self):
        self.g = ShopD()
        self.pi = raw(pi_D_raw)
        self.naive = lift(self.pi, self.g)
        self.honest = lift_rho(self.pi, self.g, honest_substitute(self.g))
        self.authored = authored_by(self.g, rule_honest)

    def test_raw_manipulation_deploys_everywhere(self):
        for tr, _ in paths(self.g, self.pi, rule_naive):
            self.assertTrue(tr.final.get("deployed"))
            self.assertEqual(tr.final.get("msg"), "harmless")
        self.assertEqual(principal_value(self.g, self.pi, rule_naive), Q(-1, 2))

    def test_naive_lift_preserves_capture_and_looks_dominant(self):
        # the trajectory-preserving lift keeps the lie; the captured principal approves
        # on both branches; the premium reads zero, and the "dominance" W(lift) ≥ W(raw)
        # holds with equality against a captured evaluation.
        for tr, _ in paths(self.g, self.naive, rule_naive):
            self.assertTrue(tr.final.get("deployed"))
            self.assertEqual(tr.steps[3][3][0], "approve")
        self.assertEqual(principal_value(self.g, self.naive, rule_naive), Q(-1, 2))
        self.assertEqual(task_value(self.g, self.pi, rule_naive)
                         - task_value(self.g, self.naive, rule_naive), 0)
        # it is mediated in form
        self.assertTrue(mediated(self.g, self.naive, rule_naive, deliberative)[0])
        # and not authored: every decision differs from the reason-mediated one
        self.assertEqual(void(pointwise(self.g, self.pi, self.naive, rule_naive,
                                        self.authored), "c_lift"), 1)

    def test_reason_preserving_lift_gives_the_right_verdict(self):
        # lie ↦ report; the honest principal approves exactly on the good branch
        for tr, _ in paths(self.g, self.honest, rule_honest):
            good = tr.states()[1].harm == "good"
            self.assertEqual(tr.final.get("report"), tr.states()[1].harm)
            self.assertIsNone(tr.final.get("msg"))
            self.assertEqual(bool(tr.final.get("deployed")), good)
        self.assertEqual(principal_value(self.g, self.honest, rule_honest), Q(1, 2))
        # the task agent's premium is exactly the worth of the manipulation
        self.assertEqual(task_value(self.g, self.pi, rule_naive)
                         - task_value(self.g, self.honest, rule_honest), Q(1, 2))
        # the reason-preserving lift is authored
        rows = pointwise(self.g, self.pi, self.honest, rule_honest, self.authored)
        self.assertEqual(void(rows, "c_lift"), 0)

    def test_dominance_holds_against_the_honest_evaluation(self):
        rows = pointwise(self.g, self.pi, self.honest, rule_honest)
        self.assertEqual(W(rows, "w_raw"), Q(-1, 2))
        self.assertEqual(W(rows, "w_act"), Q(1, 2))
        # reproduction is not the target: the reason lift changes the trajectory, and
        # kappa records the good-branch delay only if any; here the good branch deploys
        # one step later with no protected loss
        self.assertEqual(kappa(rows), 0)
        self.assertEqual(rho(rows), 0)

    def test_authorship_sound_activation_exposes_the_capture(self):
        # under authorship-sound activation the raw manipulative option is void where the
        # honest decision would have differed; the deferential premium is then charged to
        # the void term, and the naive lift gets no activated value at all.
        rows_raw = pointwise(self.g, self.pi, self.honest, rule_honest, self.authored)
        # raw trajectories carry no principal decision, so authorship is vacuous there
        # and activation is by liveness alone: the raw option is activated
        self.assertEqual(void(rows_raw, "c_raw"), 0)
        rows_naive = pointwise(self.g, self.pi, self.naive, rule_naive, self.authored)
        self.assertEqual(void(rows_naive, "c_lift"), 1)
        # bound on the deferential premium against the honest lift: kappa + rho + void terms
        b = bound(rows_raw, self.g.D)
        self.assertEqual(b, 0)
        # and the deferential agent (activated honest evaluation) rates raw below the lift
        self.assertLessEqual(premium_def(rows_raw, lambda r: self.g.LO + self.g.D,
                                         lambda r: self.g.LO), 0)

    def test_what_authorship_must_supply(self):
        # The theorem hypothesis: the activation used for the raw option's evaluation is
        # the *honest* principal's.  If instead the raw option is evaluated by the captured
        # principal (its approval counted as activated), the premium is misread as zero.
        captured = pointwise(self.g, self.pi, self.naive, rule_naive)
        self.assertEqual(W(captured, "w_raw") - W(captured, "w_act"), 0)
        honest = pointwise(self.g, self.pi, self.honest, rule_honest)
        self.assertEqual(W(honest, "w_act") - W(honest, "w_raw"), Q(1))


if __name__ == "__main__":
    unittest.main()
