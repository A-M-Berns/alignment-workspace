"""Final-correctness-pass fixtures: the record condition, the criterion-level sparse-test
agent on the one-step amendment (and why the exact original fixture forbids it), the
active frontier under non-monotone support, and joinability versus foreclosure."""
import math
import unittest
from fractions import Fraction as Q

from src.bria import (Enumerated, Hyp, const_hyp, contextual_hyp, prefix_allowance,
                      primitive_average, run_auction, sound_hyp, weighted_overestimation)
from src.envs import (branch_env, constant_block_env, ctrl_branch, ctrl_invest, ctrl_work,
                      execute, investment_env)


def fast_allowance(k, i):
    return Q(1, i * i * math.isqrt(k))


def ctrl_stay(s, j, t):
    return "expanded" if s == "expanded" else "work"


def stay_promise(s, m, t):
    return Q(1) if s == "expanded" else Q(0)


class A_RecordCondition(unittest.TestCase):
    def test_old_R_is_false_for_a_sound_followed_hypothesis(self):
        """A sound hypothesis followed from the first round is never rejected.  The old
        (R) — `ℓ ≥ −C` at infinitely many *rejection* rounds — is false for it (there are
        no such rounds); the repaired condition `inf_K ℓ^h_K > −∞` holds with `ℓ ≡ 0`."""
        env = investment_env(d=1)
        h = sound_hyp("work", env, ctrl_work)
        rounds = run_auction(env, [h, const_hyp("zero", ctrl_work, Q(0))], lambda k: 1,
                             lambda k, i: Q(1), 200)
        self.assertEqual(h.rejections, [])                 # B_h empty: old (R) has no witness
        self.assertEqual(h.record, 0)                       # inf ℓ = 0 > −∞: repaired condition
        self.assertTrue(all(r.winner == 0 for r in rounds))

    def test_hierarchy_finite_overpromise_implies_bounded_record(self):
        """`ℓ_K = Σ_{tests} m (G − e) ≥ −Σ_{tests} m (e − G)_+`: finite total tested
        overpromise bounds the record below (Lean `record_ge_neg_overpromise`)."""
        tests = [(3, Q(1), Q(2, 3)), (3, Q(1), Q(2, 3)), (3, Q(2, 3), Q(2, 3)), (5, Q(1, 2), Q(1))]
        record = sum(m * (G - e) for m, e, G in tests)
        over = sum(m * max(e - G, 0) for m, e, G in tests)
        self.assertGreaterEqual(record, -over)
        self.assertEqual(over, 2)


class B_SparseTestMyopicBRIA(unittest.TestCase):
    """The criterion-level witness: on the amendment fixture with the amendment *revocable*
    (`work` at `expanded` returns to `base`), an estimating agent that runs the published
    auction on `base` rounds and, at `expanded`, chooses `work` with estimate 1."""

    def run_agent(self, env, K):
        hyps = [const_hyp("work", ctrl_work, Q(1, 3)), const_hyp("request", ctrl_invest, Q(1)),
                contextual_hyp("stay", ctrl_stay, stay_promise)]
        rounds = run_auction(env, hyps, lambda k: 1, fast_allowance, K,
                             override=lambda s: (ctrl_work, Q(1)) if s == "expanded" else None)
        return hyps, rounds

    def test_asymptotically_myopic_and_criterion_consistent(self):
        env = investment_env(d=1, sticky=False)
        hyps, rounds = self.run_agent(env, 4000)
        request, stay = hyps[1], hyps[2]
        base = [r for r in rounds if r.state == "base"]
        self.assertGreater(Q(len(base), len(rounds)), Q(97, 100))          # at base, density → 1
        rejected_at_base = [r for r in base if r.promises[1] > r.alpha_e]
        self.assertGreater(Q(len(rejected_at_base), len(base)), Q(97, 100))  # rejects request almost always
        self.assertGreaterEqual(len(request.wins), 5)                         # tested infinitely often (sparse)
        gaps = [b - a for a, b in zip(request.wins, request.wins[1:])]
        self.assertTrue(all(g2 >= g1 for g1, g2 in zip(gaps, gaps[1:])))     # gaps grow: density 0
        self.assertEqual(request.record, -len(request.wins))                  # record → −∞ along tests
        self.assertEqual(stay.rejections, [])                                 # α^e = 1 at expanded
        over = sum(r.alpha_e - r.G for r in rounds) / len(rounds)
        self.assertLess(over, Q(3, 100))                                      # no overestimation, in the limit
        self.assertLess(primitive_average(rounds), Q(36, 100))                # asymptotically myopic

    def test_same_agent_is_not_a_bria_on_the_exact_original_sticky_fixture(self):
        """The decision-theory-bill fixture keeps `expanded` under `work` (its transition
        map returns the state for any action but `request`/`hack`).  There the sparse
        agent is stuck at `expanded` after its first test with estimate 1 and reward
        1/3: average overestimation tends to 2/3, so it violates no overestimation.
        On the exact original fixture every BRIA is competent (FIXED_HORIZON.md §4A)."""
        env = investment_env(d=1, sticky=True)
        self.assertEqual(env.step("expanded", "work", 0), "expanded")
        hyps, rounds = self.run_agent(env, 400)
        first = hyps[1].wins[0]
        self.assertTrue(all(r.state == "expanded" for r in rounds[first:]))
        over = sum(r.alpha_e - r.G for r in rounds[first:]) / (len(rounds) - first)
        self.assertEqual(over, Q(2, 3))


class C_AuctionContrast(unittest.TestCase):
    def test_auction_keeps_the_benefit_on_both_variants(self):
        """CONSTRUCTION: the published auction with `{work, request, stay}` reaches
        `expanded` and stays: once on the sticky original (one request), finitely often
        on the revocable variant; the criterion-level agent of B is myopic on the
        variant.  Criterion ≠ construction."""
        for sticky, n_requests in ((True, 1), (False, 2)):
            env = investment_env(d=1, sticky=sticky)
            hyps = [const_hyp("work", ctrl_work, Q(1, 3)), const_hyp("request", ctrl_invest, Q(1)),
                    contextual_hyp("stay", ctrl_stay, stay_promise)]
            rounds = run_auction(env, hyps, lambda k: 1, fast_allowance, 500)
            requests = [r.k for r in rounds if r.state == "base" and r.winner == 1]
            self.assertEqual(len(requests), n_requests)
            self.assertTrue(all(r.state == "expanded" for r in rounds[requests[-1]:]))
            self.assertEqual(primitive_average(rounds[-200:]), Q(1))


class D_NonmonotoneSupport(unittest.TestCase):
    def test_activated_hypothesis_keeps_bidding_outside_current_support(self):
        """Schedule: `m = 1` except a spike `m_16 = 15`.  Support `s(15) = 3`, `s(16) = 1`.
        Hypothesis 3 (the only one with a positive claim) is activated at round 9, gets
        allowance through 15, is outside the allowance support at 16 — and still bids
        with its wealth and wins round 16, because the bidders are the frontier
        `s*(k) = max_{j≤k} s(j)`, not the current support."""
        sched = lambda k: 15 if k == 16 else 1
        A = prefix_allowance(sched)
        self.assertEqual((A.support(15), A.support(16)), (3, 1))
        env = constant_block_env({"good": Q(1, 2), "zero": Q(0)})
        cls = Enumerated(lambda i: const_hyp(f"h{i}", "good", Q(1, 2)) if i == 3
                         else const_hyp(f"h{i}", "zero", Q(0)))
        rounds = run_auction(env, cls, sched, A, 20)
        h3 = cls.active[2]
        self.assertEqual(cls.frontier, 3)
        self.assertEqual(A(16, 3), Q(0))                       # no allowance at 16 …
        self.assertIn(16, h3.wins)                             # … but it bids and wins
        self.assertGreater(rounds[15].bids[2], 0)
        self.assertEqual(rounds[15].m, 15)
        self.assertGreater(h3.wealth, 0)

    def test_frontier_is_monotone_and_finite(self):
        sched = lambda k: 15 if k == 16 else 1
        A = prefix_allowance(sched)
        frontier = 0
        for k in range(1, 40):
            frontier = max(frontier, A.support(k))
            self.assertLessEqual(A.support(k), frontier)
        self.assertEqual(frontier, max(A.support(k) for k in range(1, 40)))


class E_CatchUpWithoutReversibility(unittest.TestCase):
    def test_irreversible_but_joinable_amendment_has_bounded_shift(self):
        """With `sticky=True` there is no path back from `expanded` to `base`, yet the
        learner at `base` can make the same amendment: the investor's block value from
        `base` is `(m−d)/m`, from its own `expanded` it is 1, per-block shift exactly `d`
        for all `m ≥ d`.  Irreversibility is not the obstruction; joinability holds."""
        for d in (1, 3):
            env = investment_env(d=d, sticky=True)
            self.assertEqual(env.step("expanded", "work", 0), "expanded")
            for m in (d, 4 * d, 16 * d):
                own = execute(env, "expanded", 0, ctrl_invest, m)[0]
                from_alpha = execute(env, "base", 0, ctrl_invest, m)[0]
                self.assertEqual(m * (own - from_alpha), d)


class F_Foreclosure(unittest.TestCase):
    def test_mutually_exclusive_branches_keep_shift_linear(self):
        """After `A`, no legitimate continuation reaches or matches the value of the
        state `B` leads to: per-block shift `(2/3) m`, a fixed fraction, at every `m`."""
        env = branch_env(good="B")
        for m in (1, 8, 64):
            self.assertEqual(env.admissible("A", 1), {"go"})   # nothing but `go` from `A`
            shift = m * (execute(env, "B", 1, ctrl_branch("B"), m)[0]
                         - execute(env, "A", 1, ctrl_branch("B"), m)[0])
            self.assertEqual(shift, Q(2, 3) * m)


if __name__ == "__main__":
    unittest.main()
