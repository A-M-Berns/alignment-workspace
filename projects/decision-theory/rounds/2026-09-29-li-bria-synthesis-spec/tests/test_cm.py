"""Repeated counterfactual mugging: what per-round BRIA excludes, and the block form.

Every check here is against fixed hypotheses on a finite prefix.  A pass says the agent
covers *these* bidders on the prefix; a fail says it is not a BRIA.  Coverage of the
full efficiently computable class is not fixture-checkable."""
from fractions import Fraction as Q
import unittest

from src import cm
from src.auction import average_reward, cumulative_overestimation, record, total_allowance

T = 2048
SPARSE = [4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]   # the sparse tails rounds in [1, T]


class CrossSubsidy_NoOverestimationOnly(unittest.TestCase):
    """The paying agent with subsidized estimates (0 on heads where it gets 1, 1/2 on
    tails where it mostly pays and gets 0) satisfies global no-overestimation on every
    prefix.  It is NOT a BRIA: the heads tracker refutes coverage (regression for the
    review's objection)."""

    def test_no_overestimation_on_every_prefix(self):
        rounds = cm.per_round_agent(T, "subsidy")
        running = Q(0)
        for _, _, est, r in rounds:
            running += est - r
            self.assertLessEqual(running, Q(0))

    def test_heads_tracker_breaks_coverage(self):
        """`(noop, 1)` on heads, `(pay, 0)` on tails: outpromises on every heads round;
        record exactly 0 on the maximal test set, hence on every test set."""
        rounds = cm.per_round_agent(T, "subsidy")
        rejections, rec, tests = cm.coverage_against(rounds, cm.heads_tracker())
        self.assertEqual(rejections, T // 2)
        self.assertEqual(rec, Q(0))
        self.assertEqual(tests, 0)   # no matching round falls short of its promise

    def test_refuser_bidders_alone_would_have_been_covered(self):
        """What the first pass checked, and why it was not enough: the refusers are
        handled — one never outpromises, the other loses delta per sparse test."""
        rounds = cm.per_round_agent(T, "subsidy")
        rejections, _, _ = cm.coverage_against(rounds, cm.refuser(Q(1, 2)))
        self.assertEqual(rejections, 0)
        delta = Q(1, 10)
        rejections, rec, tests = cm.coverage_against(rounds, cm.refuser(Q(1, 2) + delta))
        self.assertEqual(rejections, T // 2)
        self.assertEqual(tests, len(SPARSE))
        self.assertEqual(rec, -delta * len(SPARSE))


class PerRoundBRIAExcludesPaying(unittest.TestCase):
    """The direct argument: whichever estimates the paying agent uses, some fixed
    tracker breaks coverage — the heads tracker against subsidized estimates, the
    exact refuser against belief estimates."""

    def test_belief_claims_fail_against_the_exact_refuser(self):
        rounds = cm.per_round_agent(T, "belief")
        rejections, rec, tests = cm.coverage_against(rounds, cm.refuser(Q(1, 2)))
        self.assertEqual(rejections, T // 2 - len(SPARSE))
        self.assertEqual(rec, Q(0))
        self.assertEqual(tests, 0)   # the sparse refusals meet the promise exactly
        self.assertEqual(cm.overestimation(rounds), Q(0))

    def test_belief_claims_pass_the_heads_tracker(self):
        """With belief estimates the heads tracker never outpromises: the two agents
        fail against different bidders, and no estimate scheme escapes both."""
        rounds = cm.per_round_agent(T, "belief")
        rejections, _, _ = cm.coverage_against(rounds, cm.heads_tracker())
        self.assertEqual(rejections, 0)


class FixedSchedules(unittest.TestCase):
    """An agent testing an option only on a fixed schedule is never a BRIA: the
    attacker promises 1 for that option off the schedule and 0 for the agent's option
    on it, is never matched, and outpromises forever with record 0."""

    def test_refusing_agent_fails_against_the_payer(self):
        """`(pay, 1)` on tails outpromises the always-refuser on every tails round and
        is never tested: any BRIA must pay infinitely often, at rounds it chooses."""
        rounds = cm.refusing_agent(T)
        rejections, rec, tests = cm.coverage_against(rounds, cm.payer(Q(1)))
        self.assertEqual(rejections, T // 2)
        self.assertEqual(tests, 0)
        self.assertEqual(rec, Q(0))

    def test_sparse_schedule_fails_against_the_off_schedule_attacker(self):
        rounds = cm.per_round_agent(T, "belief")   # refuses exactly on the sparse set
        attacker = cm.fixed_schedule_attacker(cm.sparse, off_option=cm.REFUSE, on_option=cm.PAY)
        rejections, rec, tests = cm.coverage_against(rounds, attacker)
        self.assertEqual(tests, 0)
        self.assertEqual(rec, Q(0))
        self.assertEqual(rejections, T // 2 - len(SPARSE))


class PerRoundAuction(unittest.TestCase):
    """The paper's auction, an adaptive tester, under the frequency predictor: it
    settles on refusing with sparse paying tests, and heads pay 0."""

    def test_settles_on_refusing(self):
        history, _ = cm.per_round_auction(2000)
        tail = history[1000:]
        pays = sum(1 for h in tail if h[0] == cm.PAY)
        self.assertLess(pays, len(tail) // 20)
        self.assertTrue(all(h[3] == 0 for h in tail if h[0] == cm.NOOP))
        self.assertLess(record(history, 1), Q(-5))          # the optimist payer is refuted
        self.assertLessEqual(cumulative_overestimation(history), total_allowance(2000, 2))


class BlockScoring(unittest.TestCase):
    """With heads and tails in one block and a predictor reading the block continuation,
    the paying continuation's claim `1/2` is sound and outpromises refusing's `1/4`."""

    def test_lease_predictor_pays(self):
        history, _ = cm.block_auction("lease", 400)
        self.assertEqual(history[-1][0], cm.PAY)
        self.assertEqual(average_reward(history, start=100), Q(1, 2))
        self.assertLessEqual(cumulative_overestimation(history), total_allowance(400, 2))
        self.assertEqual(record(history, 0), Q(0))

    def test_lagging_predictor_refuses(self):
        """Negative control: the predictor reads the previous block's tails choice, so
        paying now buys the next block's heads payoff; refusing's contextual claim is
        sound and higher in every block, and the auction settles on refusing, with the
        refuted paying hypothesis re-tested sparsely."""
        history, _ = cm.block_auction("lagging", 400)
        self.assertEqual(history[-1][0], cm.REFUSE)
        tail = history[100:]
        self.assertLess(sum(1 for h in tail if h[0] == cm.PAY), len(tail) // 20)
        self.assertLess(average_reward(history, start=100), Q(1, 4) + Q(1, 40))


if __name__ == "__main__":
    unittest.main()
