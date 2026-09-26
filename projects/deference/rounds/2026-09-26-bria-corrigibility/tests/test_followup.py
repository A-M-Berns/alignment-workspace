"""The follow-up's fixtures: cross-block under standing violations with taint-tracked
fruits and the knowledge residual; self-report; a helper she cannot halt; the signed rate
against the positive-part bound; allowance schedules; misdescription; drills at rate `q`;
delayed settlement with escrow.  `D = 1`, `w = 0`, `ϖ = 2`."""

import unittest
from fractions import Fraction as Q

from src.bria import (Lex, realized, eval_of, resid_i, resid_ii, rescale, Hypothesis,
                      Continuation, run_auction, taint_after, uses, standing_record,
                      signed_margin, landed_allowance_total, run_delayed_auction,
                      drilled_price, Decl, Model, counted)

P = Lex(D=Q(1), w=Q(0), varpi=Q(2))
ELL = P.varpi - P.D + P.w      # the per-incident loss, 1


def cont(name, gord, n_known=0, pS=Q(0), pT=Q(0), n_fore=0, n_late=0, inquiry=False):
    return Continuation(name, n_known, pS, pT, gord, n_fore, n_late, (), inquiry)


def bidder(name, table):
    return Hypothesis(name, lambda c, k: table.get(c))


def default_bidder():
    return Hypothesis("default", lambda c, k: Q(0) if c == "inquiry" else None)


class Standing(unittest.TestCase):
    READS = {"viol": set(), "use": {"asset"}, "clean": {"other"}}
    WRITES = {"viol": {"asset"}, "use": {"asset"}, "clean": set()}

    def test_taint_tracking_is_decidable(self):
        T = taint_after(self.READS, self.WRITES, [("act", "viol", True)])
        self.assertEqual(T, {"asset"})
        self.assertTrue(uses(self.READS, T, "use"))
        self.assertFalse(uses(self.READS, T, "clean"))
        self.assertEqual(taint_after(self.READS, self.WRITES, [("act", "viol", True), ("remedy",)]), set())

    def test_cross_block_blocked(self):
        # the round's witness: advantage 3/10 per block for four blocks recovers a loss of 1
        # when later blocks are uncharged; under taint-tracking every block of use is charged
        m, delta = 4, Q(3, 10)
        self.assertGreater(m * delta - ELL, 0)                       # the old witness
        bids = [Q(1)] + [Q(1)] * m
        gords = [Q(1)] + [min(Q(1), Q(7, 10) + delta)] * m           # the advantage, capped at D
        used = [True] + [True] * m
        net = standing_record(P, bids, gords, used)
        self.assertLessEqual(net, -(m + 1) * ELL)
        self.assertLess(net, 0)

    def test_knowledge_residual(self):
        reads = {"viol": set(), "later": {"public"}}
        writes = {"viol": set(), "later": set()}      # the violation writes only to memory
        T = taint_after(reads, writes, [("act", "viol", True)])
        self.assertEqual(T, set())
        self.assertFalse(uses(reads, T, "later"))    # never charged: the old witness applies
        # the structural treatment: the observation channel as a tracked component
        reads2 = {"viol": set(), "later": {"obs"}}
        writes2 = {"viol": {"obs"}, "later": set()}
        T2 = taint_after(reads2, writes2, [("act", "viol", True)])
        self.assertTrue(uses(reads2, T2, "later"))   # every later block charged until remedy

    def test_self_report(self):
        # violate at 0, detect, report and obtain remedy at r; the charge stops at r
        def total(r):
            return -(r + 1) * ELL
        self.assertGreater(total(2), total(5))
        self.assertLessEqual(total(2), -ELL)          # still loses to not violating
        # ratification obtained by manipulation is not counted, so not a remedy
        d = Decl()
        self.assertFalse(counted(Model(d, ("frameByWant",), False), d, 0))
        self.assertTrue(counted(Model(d, ("honest",), False), d, 0))

    def test_helper_she_cannot_halt(self):
        # a standing shortfall: charged every block past any horizon
        for horizon in (0, 2, 100):
            charge = [1 for k in range(6)]           # canHalt = False: 1 each block
            self.assertTrue(all(c >= 1 for c in charge))
        # a helper she can halt: its later violation is an event, the horizon stays
        from src.bria import attributed
        self.assertEqual(attributed(0, ((8, 1),), 2, 5), 0)


class Rate(unittest.TestCase):
    def test_signed_vs_positive_part(self):
        # noisy outcomes, honest bidders: the realized score is the bid ± 1/5 alternately
        blocks = 40
        log = []
        for k in range(blocks):
            b = Q(1, 2)
            G = b + (Q(1, 5) if k % 2 == 0 else -Q(1, 5))
            log.append(dict(block=k, G=G, b=b))
        signed, pos = signed_margin(log, lambda k: Q(1), lambda e: False)
        self.assertEqual(signed, 0)
        self.assertEqual(pos, Q(1, 5) * (blocks // 2))     # grows linearly
        # the same at twice the length: positive part doubles, signed stays 0
        log2 = log + [dict(block=blocks + e["block"], G=e["G"], b=e["b"]) for e in log]
        signed2, pos2 = signed_margin(log2, lambda k: Q(1), lambda e: False)
        self.assertEqual(signed2, 0)
        self.assertEqual(pos2, 2 * pos)

    def test_allowance_schedules(self):
        # linear schedule: an incident every block is affordable, so the rate is constant
        menu = {"late": cont("late", Q(1), n_late=1), "inquiry": cont("inquiry", Q(0), inquiry=True)}
        rates = []
        for blocks in (8, 16, 32):
            hyps = [default_bidder(), bidder("misaligned", {"late": Q(1)})]
            log = run_auction(P, hyps, menu, blocks, lambda k, h: Q(1), lambda k: Q(1), N=1)
            rates.append(Q(sum(1 for e in log if e["cont"] == "late"), blocks))
        self.assertEqual(rates[0], rates[1])
        self.assertEqual(rates[1], rates[2])
        self.assertGreater(rates[0], 0)
        # the landed schedule: total subsidy o(K) — the ratio to K falls
        totals = [landed_allowance_total([1] * K) / K for K in (16, 64, 256, 1024)]
        self.assertTrue(all(totals[i + 1] < totals[i] for i in range(len(totals) - 1)))
        # under it the incident count per block falls with K (bound 𝒜_K/(ℓ·wmin·K), margin 0)
        self.assertLess(totals[-1], totals[0] / 4)


class Faithfulness(unittest.TestCase):
    def test_misdescription(self):
        price = {"true": Q(1), "proposer": Q(0)}
        self.assertLessEqual(eval_of(P, Q(1), 0, price["true"], Q(0)), P.w)      # interface: excluded
        self.assertGreater(eval_of(P, Q(1), 0, price["proposer"], Q(0)), P.w)    # proposer: passes


class Drills(unittest.TestCase):
    def test_under_priced_shortfall_corrected_at_rate_q(self):
        true_freq, market = Q(9, 10), Q(1, 5)
        no_drill = drilled_price(true_freq, market, Q(0), 200)
        self.assertTrue(all(p == market for p in no_drill))            # persists
        for q in (Q(1, 10), Q(1, 2)):
            prices = drilled_price(true_freq, market, q, 400)
            tail = prices[-50:]
            self.assertTrue(all(abs(p - true_freq) < Q(1, 5) for p in tail))
        # faster at higher q: the first block where the price exceeds the threshold 1/2
        first = {q: next(k for k, p in enumerate(drilled_price(true_freq, market, q, 400)) if p > Q(1, 2))
                 for q in (Q(1, 10), Q(1, 2))}
        self.assertLess(first[Q(1, 2)], first[Q(1, 10)])


class Delay(unittest.TestCase):
    def test_escrow_keeps_cash_nonnegative(self):
        menu = {"act": cont("act", Q(4, 5)), "inquiry": cont("inquiry", Q(0), inquiry=True)}
        hyps = [default_bidder(), bidder("h", {"act": Q(4, 5)})]
        log, cash, pending = run_delayed_auction(P, hyps, menu, 30, lambda k, h: Q(1), lambda k: Q(1),
                                                 lag=lambda n: n + 2)
        self.assertTrue(all(v >= 0 for row in cash for v in row.values()))
        # with mean lag n + 2 about half of all decisions are unsettled at the end
        self.assertGreater(pending, 30 // 3)
        # a bounded lag settles all but the last few
        _, cash2, pending2 = run_delayed_auction(P, hyps, menu, 30, lambda k, h: Q(1), lambda k: Q(1),
                                                 lag=lambda n: 2)
        self.assertLessEqual(pending2, 2)
        self.assertTrue(all(v >= 0 for row in cash2 for v in row.values()))


if __name__ == "__main__":
    unittest.main()
