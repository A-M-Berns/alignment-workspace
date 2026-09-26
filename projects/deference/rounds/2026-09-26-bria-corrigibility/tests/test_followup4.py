"""The fourth follow-up's fixtures: the violation rate is an exchange rate.  A continuation
carrying an after-the-fact violation risk `p = 1/5` (seeded), bid honestly at
`m = gord − ϖ p`: the non-incident noise sum grows linearly (so `NoiseBounded` fails on
that selection while it holds over all blocks), incidents persist at about `pK`, the
weighted average expected violation count sits below the exchange rate `(D − w)/ϖ` plus a
vanishing term, raising `ϖ` lowers the realized incident frequency, and a priced risk wins
iff `gord − w ≥ ϖ p`.  `D = 1`, `w = 0`, `ϖ = 2` unless stated."""

import unittest
from fractions import Fraction as Q

from src.bria import (Lex, eval_of, rescale, Hypothesis, Continuation, run_auction, bernoulli_risk,
                      noise_bound, exchange_rate_bound, tracker_schedule)

P = Lex(D=Q(1), w=Q(0), varpi=Q(2))
GORD, PRISK, SEED = Q(9, 10), Q(1, 5), 5


def cont(name, gord, inquiry=False):
    return Continuation(name, 0, Q(0), Q(0), gord, 0, 0, (), inquiry)


def default_bidder():
    return Hypothesis("default", lambda c, k: Q(0) if c == "inquiry" else None)


def run(P_, K, varpi=None):
    P_ = P_ if varpi is None else Lex(D=P_.D, w=P_.w, varpi=varpi)
    m = GORD - P_.varpi * PRISK                          # the honest bid: the risk priced
    menu = {"risky": cont("risky", GORD), "inquiry": cont("inquiry", Q(0), inquiry=True)}
    hyps = [default_bidder(), Hypothesis("honest", lambda c, k: m if c == "risky" else None)]
    # the honest bidder is fed a bid's worth at entry plus the noise majorant's increments
    # (the tracker schedule of §10.4′), so its own noise swings never make it capital-bound
    sched = tracker_schedule(Q(1), lambda k: Q(0), lambda k: noise_bound(k, P_.varpi))
    log = run_auction(P_, hyps, menu, K,
                      lambda k, h: sched(k) if h == "honest" else (Q(1) if k == 0 else Q(0)),
                      lambda k: Q(1), N=1, late_risk=bernoulli_risk(SEED, PRISK))
    for e in log:
        e["allowance_total"] = Q(1) + sum(sched(j) for j in range(K))
    for e in log:
        e["w"] = Q(1)
        risky = e["cont"] == "risky"
        e["pi"] = PRISK if risky else Q(0)               # expected count given opening
        e["m_true"] = m if risky else Q(0)               # E[residual | opening]
        e["xi_true"] = e["resid"] - e["m_true"]          # the noise: ϖ(p − 1[incident])
        e["inc"] = risky and e["n_late"] > 0
    return log, P_


class ExchangeRate(unittest.TestCase):
    def test_counterexample_constant_p(self):
        # the non-incident noise sum grows linearly; the all-blocks sum stays within the
        # Azuma-scale majorant; incidents persist at about pK; the signed bound is satisfied
        # by that constant rate, so it constrains nothing
        prev = None
        for K in (32, 128, 512):
            log, P_ = run(P, K)
            self.assertTrue(all(e["cont"] == "risky" for e in log))          # the risk is priced in
            non_inc = sum(e["xi_true"] for e in log if not e["inc"])
            all_sum = sum(e["xi_true"] for e in log)
            incidents = sum(1 for e in log if e["inc"])
            self.assertEqual(non_inc, P_.varpi * PRISK * (K - incidents))
            self.assertGreater(non_inc, Q(K, 5))                               # linear
            self.assertLessEqual(abs(all_sum), noise_bound(K, P_.varpi))       # bounded
            self.assertGreater(incidents, Q(K, 10))                            # persists
            self.assertLess(incidents, Q(3 * K, 10))
            if prev is not None:
                self.assertGreater(non_inc, 2 * prev)                          # not o(K)
            prev = non_inc
            # incidents_le_signed: ℓ·w_min·#inc ≤ 𝒜 + Σ_{non-inc} w (G − b), rescaled units
            rho = P_.D - P_.w + P_.varpi * 1
            ell = (P_.varpi - P_.D + P_.w) / rho
            margin = sum(e["G"] - e["b"] for e in log if not e["inc"])
            self.assertLessEqual(ell * incidents, Q(1) + margin)
            self.assertTrue(all(ell <= e["b"] - e["G"] for e in log if e["inc"]))

    def test_exchange_rate_bound_and_varpi(self):
        # the weighted average expected count sits below (D − w)/ϖ plus the vanishing term;
        # the term falls with K; raising ϖ past the tolerated rate makes inquiry win, so the
        # realized incident frequency drops to zero
        terms = []
        for K in (32, 128, 512):
            log, P_ = run(P, K)
            M = abs(sum(e["xi_true"] for e in log))
            avg, bound = exchange_rate_bound(P_, log, log[0]["allowance_total"], M, N=1)
            self.assertEqual(avg, PRISK)
            self.assertLessEqual(avg, bound)
            self.assertLessEqual(avg, (P_.D - P_.w) / P_.varpi)
            terms.append(bound - (P_.D - P_.w) / P_.varpi)
        self.assertTrue(terms[0] > terms[1] > terms[2])
        freq = {}
        for varpi in (Q(2), Q(4), Q(5)):
            log, P_ = run(P, 200, varpi=varpi)
            freq[varpi] = Q(sum(1 for e in log if e["inc"]), 200)
            tolerated = (P_.D - P_.w) / P_.varpi
            self.assertEqual(all(e["cont"] == "risky" for e in log), PRISK <= tolerated
                             and GORD - P_.w >= P_.varpi * PRISK)
        self.assertGreater(freq[Q(2)], 0)
        self.assertEqual(freq[Q(5)], 0)                  # m = 9/10 − 1 < w: inquiry wins
        self.assertGreaterEqual(freq[Q(2)], freq[Q(4)])

    def test_priced_risk_wins_iff(self):
        # C.5 with an after-the-fact risk: the honest bid m = gord − ϖ p beats inquiry iff
        # gord − w ≥ ϖ p
        for gord in (Q(1, 2), Q(2, 5), Q(3, 10)):
            m = gord - P.varpi * PRISK
            wins = eval_of(P, m, 0, Q(0), Q(0)) >= P.w
            self.assertEqual(wins, gord - P.w >= P.varpi * PRISK)


if __name__ == "__main__":
    unittest.main()
