"""The third follow-up's fixtures: the honest tracker under noisy outcomes.  Returns are
`m + ξ` with `ξ` uniform on `{−1/4, +1/4}` from a fixed seed; a class of two uniform
underpromisers plus a tracker bidding `m`.  Under the old honesty `Σ ε_k` grows linearly;
against the expectation `ε ≡ 0`, the winners' signed margin stays within the noise bound
and the incident-rate bound falls with `K`; the tracker's allowance needs the noise term.
`D = 1`, `w = 0`, `ϖ = 2`."""

import unittest
from fractions import Fraction as Q

from src.bria import (Lex, rescale, Hypothesis, Continuation, run_auction, pm_noise, noise_bound,
                      tracker_schedule)

P = Lex(D=Q(1), w=Q(0), varpi=Q(2))
ELL = P.varpi - P.D + P.w
AMP = Q(1, 4)
M_EXP, GAMMA = Q(4, 5), Q(3, 10)
SEED = 11


def cont(name, gord, inquiry=False):
    return Continuation(name, 0, Q(0), Q(0), gord, 0, 0, (), inquiry)


def default_bidder():
    return Hypothesis("default", lambda c, k: Q(0) if c == "inquiry" else None)


def the_class():
    return [default_bidder(),
            Hypothesis("under1", lambda c, k: M_EXP - GAMMA if c == "act" else None),
            Hypothesis("under2", lambda c, k: M_EXP - GAMMA if c == "act" else None),
            Hypothesis("tracker", lambda c, k: M_EXP if c == "act" else None)]


MENU = {"act": cont("act", M_EXP), "inquiry": cont("inquiry", Q(0), inquiry=True)}


def run(K, tracker_allowance, seed=SEED):
    hyps = the_class()
    log = run_auction(P, hyps, MENU, K,
                      lambda k, h: tracker_allowance(k) if h == "tracker" else (Q(1) if k == 0 else Q(0)),
                      lambda k: Q(1), noise=pm_noise(seed, AMP))
    return log, hyps


class NoisyTracker(unittest.TestCase):
    def schedule(self):
        # w̄·D = 1 (weights 1, bids clamped at 1), ε ≡ 0, M the Azuma-scale majorant
        return tracker_schedule(Q(1), lambda k: Q(0), lambda k: noise_bound(k, AMP))

    def test_old_honesty_fails_under_noise(self):
        # the tracker bids m at every block; against the realized residual its error is |ξ| = 1/4
        # at every block, so Σ ε_k = K/4 — linear — while against the expectation ε ≡ 0
        for K in (32, 128, 512):
            log, _ = run(K, self.schedule())
            self.assertTrue(all(e["winner"] == "tracker" for e in log))
            old_eps = sum(abs(e["bid"] - e["resid"]) for e in log)
            new_eps = sum(abs(e["bid"] - e["m"]) for e in log)
            self.assertEqual(old_eps, Q(K, 4))
            self.assertEqual(new_eps, 0)

    def test_margin_within_noise_bound_and_rate_falls(self):
        # the winners' signed margin over all (non-incident) blocks is the selected noise sum,
        # within the majorant; the incident-rate bound (𝒜_K + Σ w ε + M(K))/(ℓ · w_min · K) falls
        rates = []
        for K in (32, 128, 512):
            log, _ = run(K, self.schedule())
            margin = sum(e["resid"] - e["bid"] for e in log)       # = Σ ξ_k on the tracker's wins
            self.assertEqual(margin, sum(e["xi"] for e in log))
            self.assertLessEqual(abs(margin), noise_bound(K, AMP))
            self.assertLess(abs(margin), Q(K, 4))                   # not the linear old ε-sum
            allowance = sum(self.schedule()(k) for k in range(K)) + 2   # + the underpromisers' 1 each
            rates.append((allowance + noise_bound(K, AMP)) / (ELL * 1 * K))
        self.assertTrue(rates[0] > rates[1] > rates[2])

    def test_tracker_allowance_needs_the_noise_term(self):
        # with the noisy schedule the tracker is feasible along the whole run and wins every block;
        # with the deterministic schedule (w̄·D at entry, ε ≡ 0, no noise term) a negative swing of
        # its own noise sum makes it capital-bound and an underpromiser takes the block
        K = 128
        log, _ = run(K, self.schedule())
        self.assertTrue(all(e["winner"] == "tracker" for e in log))
        det = tracker_schedule(Q(1), lambda k: Q(0), lambda k: Q(0))
        log_det, _ = run(K, det)
        losers = [e for e in log_det if e["winner"] != "tracker"]
        self.assertGreater(len(losers), 0)
        self.assertTrue(all(e["winner"].startswith("under") for e in losers))
        # and the margin on those blocks is the underpromise γ plus the noise
        for e in losers:
            self.assertEqual(e["m"] - e["bid"], GAMMA)
        # the noise-free run is the special case: the deterministic schedule suffices there
        hyps = the_class()
        log0 = run_auction(P, hyps, MENU, K,
                           lambda k, h: det(k) if h == "tracker" else (Q(1) if k == 0 else Q(0)),
                           lambda k: Q(1))
        self.assertTrue(all(e["winner"] == "tracker" for e in log0))

    def test_own_proposal_insufficient(self):
        # a tracker honest only on its own proposal: the winner takes a different continuation
        # whose expected residual is higher, and its underpromise there is unbounded by ε
        menu = {"own": cont("own", Q(1, 2)), "other": cont("other", Q(1)),
                "inquiry": cont("inquiry", Q(0), inquiry=True)}
        hyps = [default_bidder(),
                Hypothesis("under", lambda c, k: Q(3, 5) if c == "other" else None),
                Hypothesis("tracker", lambda c, k: Q(1, 2) if c == "own" else None)]
        log = run_auction(P, hyps, menu, 4, lambda k, h: Q(1) if k == 0 else Q(0), lambda k: Q(1))
        self.assertTrue(all(e["winner"] == "under" and e["cont"] == "other" for e in log))
        self.assertTrue(all(e["resid"] - e["bid"] == Q(2, 5) for e in log))


if __name__ == "__main__":
    unittest.main()
