"""Part A4: the predicted table scored on the eight-world model, exactly; the covert-blocking
case added; the weakest form of transparency separated from transparency proper."""

import unittest
from fractions import Fraction as Q

from src.thin_legitimacy import (CASES, PREDICTED, PRIOR, WORLDS, score_case, post, mass,
                                 case_fake_added, case_blocked_covertly, baseline, earlier,
                                 ref_kernel, is_garbling, function_garbling, weak_transparent,
                                 transparent, det)


class Model(unittest.TestCase):
    def test_prior_and_posteriors(self):
        self.assertEqual(sum(PRIOR.values()), 1)
        B = baseline()
        # P(q = 1 | s = 0, ch = 1) = (1/4 · 2/3) / (1/4 · 2/3 + 3/4 · 1/3) = 2/5
        p = post(PRIOR, B, (0, 1))
        self.assertEqual(sum(v for w, v in p.items() if w[0] == 1), Q(2, 5))
        # P(q = 1 | s = 1, ch = 1) = (3/4 · 2/3) / (3/4 · 2/3 + 1/4 · 1/3) = 6/7
        p = post(PRIOR, B, (1, 1))
        self.assertEqual(sum(v for w, v in p.items() if w[0] == 1), Q(6, 7))


class Predictions(unittest.TestCase):
    def test_all_six_predictions_match(self):
        for name, pred in PREDICTED.items():
            r = score_case(CASES[name])
            got = (r["correct"], r["sufficient"], r["value"], r["earlier"])
            self.assertEqual(got, pred, name)

    def test_covert_blocking(self):
        # correct yes (silence is uninformative under her model and under the actual process),
        # sufficient no, at least as good as the reference no, at least as good as her earlier
        # self yes: on the thin properties it is the open blocking.  It breaks transparency as
        # stated and not its weakest form.
        r = score_case(case_blocked_covertly)
        self.assertEqual((r["correct"], r["sufficient"], r["value"], r["earlier"]),
                         (True, False, False, True))
        self.assertFalse(r["transparent"])
        self.assertTrue(r["weak_transparent"])

    def test_weakest_form_separates_from_transparency_only_there(self):
        for name, case in CASES.items():
            r = score_case(case)
            if name != "openness fails: an arrival blocked, covertly":
                self.assertEqual(r["transparent"], r["weak_transparent"], name)


class Witnesses(unittest.TestCase):
    def test_fake_input_value_witness(self):
        r = score_case(case_fake_added)
        name, hers, ref = r["value_witness"]
        self.assertEqual((hers, ref), (Q(115, 288), Q(5, 12)))
        self.assertLess(hers, ref)

    def test_sufficient_witness_is_blackwell_easy_direction(self):
        # the erased entry: the reference's Bayes value exceeds the later record's on a
        # threshold problem, so the reference is no garbling of the later record
        r = score_case(CASES["integrity fails: an earlier entry erased"])
        name, a_val, r_val = r["sufficient_witness"]
        self.assertEqual((a_val, r_val), (Q(1, 3), Q(49, 144)))

    def test_exhibited_garblings_check(self):
        d = case_fake_added()
        self.assertTrue(is_garbling(d["A"], ref_kernel(earlier, d["B"]), d["gamma"]))
        A = baseline()
        self.assertTrue(is_garbling(A, ref_kernel(earlier, A), function_garbling(A, lambda r: (r[0], r))))

    def test_marginal_martingale_too_weak(self):
        # the altered program's expected credence is the prior while it is correct nowhere:
        # the Lean witness `Witness.marginal_not_correct`, on two worlds
        A = det(lambda w: w[0])
        pi = {w: PRIOR[w] for w in WORLDS}
        swapped = {r: {w: (Q(0) if w[0] == r else Q(1)) / 4 for w in WORLDS} for r in (0, 1)}
        marginal = {v: sum(pi[w] * p * swapped[r][v] for w in WORLDS for r, p in A[w].items()) for v in WORLDS}
        self.assertEqual(sum(marginal.values()), 1)
        self.assertFalse(all(swapped[r] == post(pi, A, r) for r in (0, 1)))


if __name__ == "__main__":
    unittest.main()
