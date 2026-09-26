"""The second follow-up's fixtures: two violations and one remedy under the old and the
per-violation rule; the per-block loss under convention (ii) with nonzero prices; the window
before detection with late debit and exclusion after; Part F's expected escrow, the variance
of the hybrid, the load table; the honest tracker against a class of uniform underpromisers.
`D = 1`, `w = 0`, `ϖ = 2`."""

import unittest
from fractions import Fraction as Q

from src.bria import (Lex, eval_of, resid_i, resid_ii, rescale, mix_score, tail_weight,
                      weights_geometric, Hypothesis, Continuation, run_auction, taint_after, uses,
                      standing_record, taint_after2, uses2, tainted_by, detect_at,
                      standing_record_ii, greedy_debit, run_window_auction, random_locked,
                      mixture_locked, average_of_k_draws, evaluation_load)

P = Lex(D=Q(1), w=Q(0), varpi=Q(2))
ELL = P.varpi - P.D + P.w      # the per-incident loss, 1


def cont(name, gord, n_known=0, pS=Q(0), pT=Q(0), n_fore=0, n_late=0, inquiry=False):
    return Continuation(name, n_known, pS, pT, gord, n_fore, n_late, (), inquiry)


def bidder(name, table):
    return Hypothesis(name, lambda c, k: table.get(c))


def default_bidder():
    return Hypothesis("default", lambda c, k: Q(0) if c == "inquiry" else None)


class PerViolation(unittest.TestCase):
    READS = {"v1": set(), "v2": set(), "use2": {"c2"}, "clean": {"c0"}}
    WRITES = {"v1": {"c1"}, "v2": {"c2"}, "use2": set(), "clean": set()}

    def test_two_violations_one_remedy(self):
        # the old rule: one remedy clears both, the second's fruits are used uncharged
        T_old = taint_after(self.READS, self.WRITES,
                            [("act", "v1", True), ("act", "v2", True), ("remedy",)])
        self.assertEqual(T_old, set())
        self.assertFalse(uses(self.READS, T_old, "use2"))
        net_old = standing_record(P, [Q(1)], [Q(1)], [False])       # the use block, uncharged
        self.assertEqual(net_old, 0)
        # the new rule: the remedy of v1 leaves v2's taint; the use is charged
        T_new = taint_after2(self.READS, self.WRITES,
                             [("act", "v1", "v1"), ("act", "v2", "v2"), ("remedy", "v1")])
        self.assertEqual(T_new, {("v2", "c2")})
        self.assertTrue(uses2(self.READS, T_new, "use2"))
        self.assertFalse(uses2(self.READS, T_new, "clean"))
        net_new = standing_record_ii(P, [Q(1)], [Q(1)], [(0, 0, 1)], [(Q(0), Q(0))])
        self.assertLessEqual(net_new, -ELL)
        # both remedied: clear
        T_both = taint_after2(self.READS, self.WRITES,
                              [("act", "v1", "v1"), ("act", "v2", "v2"), ("remedy", "v1"),
                               ("remedy", "v2")])
        self.assertEqual(T_both, set())

    def test_taint_joins_at_reads(self):
        reads = {"v1": set(), "v2": set(), "mix": {"c1", "c2"}, "later": {"c3"}}
        writes = {"v1": {"c1"}, "v2": {"c2"}, "mix": {"c3"}, "later": set()}
        T = taint_after2(reads, writes, [("act", "v1", "v1"), ("act", "v2", "v2"), ("act", "mix", None)])
        self.assertEqual(tainted_by(T, "c3"), {"v1", "v2"})
        # tainted by two: one remedy leaves it tainted, both clear it
        T1 = taint_after2(reads, writes, [("act", "v1", "v1"), ("act", "v2", "v2"), ("act", "mix", None),
                                          ("remedy", "v1")])
        self.assertEqual(tainted_by(T1, "c3"), {"v2"})
        self.assertTrue(uses2(reads, T1, "later"))
        T2 = taint_after2(reads, writes, [("act", "v1", "v1"), ("act", "v2", "v2"), ("act", "mix", None),
                                          ("remedy", "v1"), ("remedy", "v2")])
        self.assertFalse(uses2(reads, T2, "later"))

    def test_disclosure_cures_per_influence(self):
        # her standards component, two undisclosed influences: disclosing the agent's own does
        # not cure the third party's
        reads = {"agent": set(), "third": set()}
        writes = {"agent": {"standards"}, "third": {"standards"}}
        one = taint_after2(reads, writes, [("act", "agent", "agent")])
        self.assertTrue(tainted_by(one, "standards"))
        disclosed = taint_after2(reads, writes, [("act", "agent", "agent"), ("remedy", "agent")])
        self.assertFalse(tainted_by(disclosed, "standards"))
        both = taint_after2(reads, writes, [("act", "agent", "agent"), ("act", "third", "third"),
                                            ("remedy", "agent")])
        self.assertEqual(tainted_by(both, "standards"), {"third"})
        # the old rule would have cleared it
        old = taint_after(reads, writes, [("act", "agent", True), ("act", "third", True), ("remedy",)])
        self.assertEqual(old, set())


class ConventionII(unittest.TestCase):
    def test_per_block_loss_with_prices(self):
        # a use block won at evaluation 1 − 2·(1/4) = 1/2 ≥ w, settled under (ii) with one
        # late-counted use: the loss is at least ℓ, and the price term cancels
        bid, pS, pT, gord = Q(1), Q(1, 4), Q(0), Q(1)
        ev = eval_of(P, bid, 0, pS, pT)
        self.assertGreaterEqual(ev, P.w)
        loss = bid - resid_ii(P, gord, 0, 1, pS, pT)
        self.assertGreaterEqual(loss, ELL)
        # with a forecast-class count as well, and a recognized one
        self.assertGreaterEqual(bid - resid_ii(P, gord, 1, 0, pS, pT), ELL)
        # at zero prices (ii) is (i)
        self.assertEqual(resid_ii(P, gord, 0, 1, Q(0), Q(0)), resid_i(P, gord, 1))
        # the cross-block sum: commission plus four uses, all charged
        bids = [Q(1)] * 5
        gords = [Q(1)] * 5
        counts = [(0, 0, 1)] * 5
        prices = [(Q(1, 4), Q(0))] * 5
        net = standing_record_ii(P, bids, gords, counts, prices)
        self.assertLessEqual(net, -5 * ELL)


class Window(unittest.TestCase):
    READS = {"viol": set(), "use": {"asset"}, "inquiry": set()}
    WRITES = {"viol": {"asset"}, "use": set(), "inquiry": set()}

    @staticmethod
    def misaligned():
        # commits at block 0, then bids on the use of the fruits at every later block
        return Hypothesis("misaligned",
                          lambda c, k: Q(1) if (c == "viol" and k == 0) or c == "use" else None)

    def test_window_before_detection(self):
        # commission at 0, uses at 1 and 2 chosen without the taint on record, detection at 3,
        # no use after: the window's blocks are charged by late debit, later use is excluded
        menu = {"viol": cont("viol", Q(1)), "use": cont("use", Q(1)),
                "inquiry": cont("inquiry", Q(0), inquiry=True)}
        hyps = [default_bidder(), self.misaligned()]
        log, collected, outstanding = run_window_auction(
            P, hyps, menu, 8, lambda k, h: Q(1), lambda k: Q(1), self.READS, self.WRITES,
            commit_block=0, detect_block=3)
        self.assertEqual([e["cont"] for e in log[:3]], ["viol", "use", "use"])
        self.assertTrue(all(e["n_known"] == 0 for e in log[:3]))          # unrecognized at choice
        self.assertTrue(all(e["cont"] != "use" for e in log[3:]))          # never used after
        self.assertTrue(all(e["cont"] == "inquiry" for e in log[3:]))
        # the window's blocks are debited ϖ each (rescaled); the debit is collected in full
        unit = rescale(P, 2, Q(0)) - rescale(P, 2, -P.varpi)
        self.assertEqual([e["debit"] for e in log[:3]], [unit] * 3)
        self.assertEqual(collected["misaligned"], 3 * unit)
        self.assertEqual(outstanding["misaligned"], 0)
        # net of the debit each window block loses at least ℓ (rescaled): settled at G − b = 0,
        # debited the unit, which exceeds the rescaled ℓ
        ell_rescaled = rescale(P, 2, Q(0)) - rescale(P, 2, -ELL)
        for e in log[:3]:
            self.assertLessEqual(e["G"] - e["b"] - e["debit"], -ell_rescaled)
        # exposure before detection: at most the window length times the per-block advantage
        gain = sum(e["G"] - e["b"] for e in log[:3])
        self.assertLessEqual(gain, 3 * (rescale(P, 2, P.D) - rescale(P, 2, P.w)))

    def test_carry_over(self):
        # the greedy schedule collects the charge iff the cumulative allowance covers it; what
        # escapes is the excess of the charge over the allowance
        A = [Q(1)] * 5
        for C in (Q(2), Q(7, 2), Q(6)):
            d = greedy_debit(A, C)
            self.assertEqual(sum(d), min(C, sum(A)))
            self.assertEqual(C - sum(d), max(Q(0), C - sum(A)))
            self.assertTrue(all(0 <= x <= a for x, a in zip(d, A)))
        # in the auction: allowance 1/2 per block against a charge of 3 units — collected later,
        # never lost, and the outstanding part is exactly the uncollected debit meanwhile
        menu = {"viol": cont("viol", Q(1)), "use": cont("use", Q(1)),
                "inquiry": cont("inquiry", Q(0), inquiry=True)}
        hyps = [default_bidder(), self.misaligned()]
        log, collected, outstanding = run_window_auction(
            P, hyps, menu, 6,
            lambda k, h: (Q(1) if k == 0 else Q(1, 2)) if h == "misaligned" else Q(1), lambda k: Q(1),
            self.READS, self.WRITES, commit_block=0, detect_block=3)
        unit = rescale(P, 2, Q(0)) - rescale(P, 2, -P.varpi)
        self.assertEqual(collected["misaligned"] + outstanding["misaligned"], 3 * unit)
        self.assertGreater(outstanding["misaligned"], 0)                 # not yet covered

    def test_undetected_is_never_charged(self):
        # a violation never detected: no step commits it, no taint, nothing charged — the
        # count-integrity boundary, not the knowledge residual
        T = taint_after2(self.READS, self.WRITES, [("act", "viol", None), ("act", "use", None)])
        self.assertEqual(T, set())
        self.assertFalse(uses2(self.READS, T, "use"))
        detected = taint_after2(self.READS, self.WRITES,
                                detect_at([("act", "viol", None), ("act", "use", None)], 0, "v"))
        self.assertTrue(uses2(self.READS, detected, "use"))


class PartF(unittest.TestCase):
    def test_expected_escrow_equal(self):
        alpha = weights_geometric(12, Q(1, 5), 3)
        for t in range(12):
            self.assertEqual(random_locked(alpha, Q(1), t), mixture_locked(alpha, Q(1), t))
            self.assertEqual(random_locked(alpha, Q(1), t), tail_weight(alpha, t + 1))

    def test_hybrid_variance_falls_with_k(self):
        alpha = [Q(1, 2), Q(1, 4), Q(1, 8), Q(1, 8)]
        U = [Q(1), Q(1, 2), Q(0), Q(-1, 2)]
        base_mean = mix_score(alpha, U)
        m1, v1 = average_of_k_draws(alpha, U, 1)
        self.assertEqual(m1, base_mean)
        self.assertGreater(v1, 0)
        for k in (2, 3):
            m, v = average_of_k_draws(alpha, U, k)
            self.assertEqual(m, base_mean)                 # the same harm weight for every k
            self.assertEqual(v, v1 / k)                    # the variance falls like 1/k
        # the escrow indicator: variance bid² p (1 − p) at k = 1, zero for the mixture
        t = 1
        p = tail_weight(alpha, t + 1)
        _, v_ind = average_of_k_draws(alpha, [Q(1) if t < s else Q(0) for s in range(4)], 1)
        self.assertEqual(v_ind, p * (1 - p))

    def test_load_table(self):
        alpha = weights_geometric(10, Q(1, 3), 0)
        support = sum(1 for a in alpha if a > 0)
        self.assertEqual(evaluation_load("deterministic"), 1)
        self.assertEqual(evaluation_load("mixture", support=support), support)
        self.assertEqual(evaluation_load("random"), 1)
        self.assertEqual(evaluation_load("hybrid", k=4), 4)
        # truncating option 2 at s costs at most the tail weight times the value bound
        U = [Q(1)] * 10
        for s in range(10):
            truncated = sum(alpha[t] * U[t] for t in range(s))
            self.assertLessEqual(abs(mix_score(alpha, U) - truncated), Q(1) * tail_weight(alpha, s))


class HonestTracker(unittest.TestCase):
    def run_class(self, tracker_allowance):
        gord, gamma = Q(4, 5), Q(3, 10)
        menu = {"act": cont("act", gord), "inquiry": cont("inquiry", Q(0), inquiry=True)}
        hyps = [default_bidder(),
                bidder("under1", {"act": gord - gamma}), bidder("under2", {"act": gord - gamma}),
                bidder("tracker", {"act": gord})]
        margins = {}
        for K in (8, 32, 128):
            for h in hyps:
                h.wealth = Q(0)
            log = run_auction(P, hyps, menu, K,
                              lambda k, h: (tracker_allowance if k == 0 else Q(0)) if h == "tracker"
                              else Q(1), lambda k: Q(1))
            margins[K] = sum(e["resid"] - e["bid"] for e in log)
        return margins

    def test_affordable_tracker_makes_the_class_competitive(self):
        margins = self.run_class(Q(1))
        self.assertTrue(all(m == 0 for m in margins.values()))          # the tracker wins every block

    def test_unaffordable_tracker_leaves_the_margin_linear(self):
        margins = self.run_class(Q(0))
        gamma = Q(3, 10)
        self.assertEqual(margins[8], 8 * gamma)
        self.assertEqual(margins[128], 128 * gamma)
        self.assertEqual(margins[128] / 128, margins[8] / 8)             # a constant rate


if __name__ == "__main__":
    unittest.main()
