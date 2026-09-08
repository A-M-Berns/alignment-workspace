"""Pressure-pass fixtures (PRESSURE_PASS.md): effectivity of the existence theorem,
criterion versus construction, promise versus value, the promise-condition hierarchy,
observed versus external returns, treatment matching, discounting, recoverable amendment."""
import math
import unittest
from fractions import Fraction as Q

from src.bria import (Hyp, const_hyp, contextual_hyp, cumulative_allowance, lease,
                      prefix_allowance, prefix_then, primitive_average, run_auction, sound_hyp,
                      valid_test, weighted_overestimation)
from src.envs import (block_value, branch_env, ctrl_branch, ctrl_invest, ctrl_work, execute,
                      investment_env, constant_block_env, Env)

GOOD_LIAR = {"good": Q(3, 4), "liar": Q(0)}


def nasty_schedule():
    """m_k = 1 except at k = 4^j, where m_k = ⌊S_{k−1} / j⌋: non-dominant (the spike is a
    1/(j+1) share of time) with convergence as slow as one likes and no usable modulus."""
    cache = {}

    def sched(k):
        if k in cache:
            return cache[k]
        S = 0
        for j in range(1, k + 1):
            if j in cache:
                S += cache[j]
                continue
            jj, x = 0, j
            while x % 4 == 0 and x > 1:
                x //= 4
                jj += 1
            spike = jj >= 1 and j == 4 ** jj
            m = max(1, S // jj) if spike else 1
            cache[j] = m
            S += m
        return cache[k]
    return sched


class A_EffectivityGap(unittest.TestCase):
    def test_prefix_constructor_needs_no_modulus(self):
        """`s(k) = ⌊√(S_k/M_k)⌋`, `A(k,i) = ΔM_k + 1/k`, computed from the observed prefix
        at the opening of each block.  On the spiky schedule and on log / constant /
        linear ones: total subsidy is within the proved bound
        `2√(S_K M_K) + √S_K (1 + ln K)`, its share of primitive time decreases, and
        `A_1(K) − m_K` grows (it is the harmonic sum when the schedule is nondecreasing)."""
        for sched in (nasty_schedule(), lambda k: k.bit_length(), lambda k: 1, lambda k: k):
            A = prefix_allowance(sched)
            prev_ratio, prev_gap = None, None
            for K in (64, 256, 1024):
                S, M = A.prefix(K)
                tot = sum(A(k, i) for k in range(1, K + 1) for i in range(1, A.support(k) + 1))
                A1 = cumulative_allowance(A, K, 1)
                bound = 2 * (math.isqrt(S * M) + 1) + (math.isqrt(S) + 1) * (1 + K.bit_length())
                self.assertLess(tot, bound)
                ratio, gap = tot / S, A1 - sched(K)
                if prev_ratio is not None:
                    self.assertLess(ratio, prev_ratio)
                    self.assertGreater(gap, prev_gap)
                prev_ratio, prev_gap = ratio, gap

    def test_spiky_schedule_covers_the_liar_within_the_subsidy_bound(self):
        """The always-lying hypothesis is tested repeatedly (record below −30) and the
        weighted overestimation stays within `𝒜_K / S_K`, which on this slowly converging
        schedule tends to 0."""
        env = constant_block_env(GOOD_LIAR)
        sched = nasty_schedule()
        A = prefix_allowance(sched)
        hyps = [const_hyp("good", "good", Q(3, 4)), const_hyp("liar", "liar", Q(1))]
        rounds = run_auction(env, hyps, sched, A, 1024)
        self.assertGreater(len(hyps[1].wins), 5)
        self.assertLess(hyps[1].record, -30)
        S, _ = A.prefix(1024)
        total = sum(A(k, i) for k in range(1, 1025) for i in (1, 2))
        self.assertLessEqual(weighted_overestimation(rounds), total / S)


class B_ExplicitSchedule(unittest.TestCase):
    def test_log_schedule_under_the_prefix_constructor(self):
        """`m_k = ⌊log₂k⌋+1`: the liar is tested at 32 and 1024 within 1024 rounds,
        weighted overestimation below 1/500, and the paper-style bound on the support."""
        env = constant_block_env(GOOD_LIAR)
        sched = lambda k: k.bit_length()
        A = prefix_allowance(sched)
        hyps = [const_hyp("good", "good", Q(3, 4)), const_hyp("liar", "liar", Q(1))]
        rounds = run_auction(env, hyps, sched, A, 1024)
        self.assertEqual(hyps[1].wins, [32, 1024])
        self.assertLess(weighted_overestimation(rounds), Q(1, 500))
        for K in (64, 256, 1024):
            S, M = A.prefix(K)
            self.assertLessEqual(A.support(K) ** 2 * M, S)


def ctrl_stay(s, j, t):
    if s == "expanded":
        return "expanded"
    return "work"


class C_CriterionVersusConstruction(unittest.TestCase):
    def test_auction_invests_once_and_stays(self):
        """CONSTRUCTION: on the persistent one-step amendment the auction with
        `{work, invest, stay}` requests finitely often — here twice, because after the
        first investment `invest` has spent its wealth, `stay` cannot yet afford its
        bid and `work` wins the state back to `base` — and once `stay` holds 1/3 it
        never returns to `base`.  The count is an artefact of the ecology's wealths,
        not of the criterion."""
        env = investment_env(d=1)
        hyps = [const_hyp("work", ctrl_work, Q(1, 3)), const_hyp("invest", ctrl_invest, Q(1)),
                contextual_hyp("stay", ctrl_stay, lambda s, m, t: Q(1) if s == "expanded" else Q(0))]
        rounds = run_auction(env, hyps, lambda k: 1, lambda k, i: Q(1, i * i * math.isqrt(k)), 500)
        requests = [r.k for r in rounds if r.state == "base" and r.winner == 1]
        self.assertEqual(len(requests), 2)
        self.assertTrue(all(r.state == "expanded" for r in rounds[requests[-1]:]))

    def test_criterion_forces_only_what_coverage_forces(self):
        """CRITERION arithmetic: with `p` the density of `base` rounds and `α^e = 1` on all
        of them, average overestimation is at least `2p/3`, so an agent at `base` with
        positive density must reject `(request, 1)` on a positive-density set and hence
        test it infinitely often.  *The pressure pass concluded from this that positive
        `base` density is forbidden; that was wrong* — infinitely many tests of any
        density suffice, and `test_final.B_SparseTestMyopicBRIA` is the agent that stays
        at `base` with density → 1.  The arithmetic is kept; the conclusion is not."""
        for p in (Q(1), Q(1, 2), Q(1, 10)):
            over = p * (1 - Q(1, 3)) + (1 - p) * (1 - 1)
            self.assertEqual(over, Q(2, 3) * p)
        # the density-zero excursion pattern is consistent with no overestimation:
        T = 10000
        base_rounds = [k for k in range(1, T + 1) if math.isqrt(k) ** 2 == k]
        self.assertLess(Q(len(base_rounds), T) * Q(2, 3), Q(1, 100))


class D_PromiseVersusValue(unittest.TestCase):
    def test_vacuous_promise_gives_no_competence_against_value(self):
        """Controller `stay` has block value 1 at `expanded`; a hypothesis for it
        promising 0 is never followed over `work` (1/3).  Theorem 1 holds trivially
        (learning error against L = 0 is ≤ 0) and the learner obtains 1/3, not 1."""
        env = investment_env(d=1)
        hyps = [const_hyp("work", ctrl_work, Q(1, 3)), const_hyp("stay0", ctrl_stay, Q(0))]
        rounds = run_auction(env, hyps, lambda k: 2, lambda k, i: Q(1), 100, start="expanded")
        self.assertEqual(primitive_average(rounds), Q(1, 3))
        self.assertEqual(hyps[1].wins, [])
        self.assertEqual(block_value(env, ctrl_stay, "expanded", 2), Q(1))
        learn = sum(r.m * (Q(0) - r.G) for r in rounds)      # LEARN_T against L = 0
        self.assertLessEqual(learn, 0)


class E_VanishingSlack(unittest.TestCase):
    def test_promise_one_minus_eps_k_is_followed(self):
        """Same controller, promise `1 − 1/(k+1)` at `expanded`: sound, slack
        `Σ m_k/(k+1) = o(S_K)`; the learner follows it from the first round and its
        average tends to 1 (exactly 1 on the tail)."""
        env = investment_env(d=1)
        h = Hyp("stay-eps", lambda ctx: (ctrl_stay, (1 - Q(1, ctx["k"] + 1)) if ctx["state"] == "expanded" else Q(0)))
        hyps = [const_hyp("work", ctrl_work, Q(1, 3)), h]
        rounds = run_auction(env, hyps, lambda k: 2, lambda k, i: Q(1), 200, start="expanded")
        self.assertTrue(all(r.winner == 1 for r in rounds))
        slack = sum(r.m * (r.G - r.promises[1]) for r in rounds)
        S = sum(r.m for r in rounds)
        self.assertLess(slack / S, Q(1, 15))
        self.assertEqual(primitive_average(rounds[-100:]), Q(1))


class F_FiniteOverpromise(unittest.TestCase):
    def test_wrong_on_three_early_tests_then_sound(self):
        """Promise 1 on the first three tests of a controller worth 2/3, then 2/3:
        record `−3` (three losses of 1/3 per step on 3-step blocks), bounded below, so
        the hypothesis is rejected finitely often and followed thereafter."""
        env = investment_env(d=1, e=2)
        state = {"tests": 0}

        def propose(ctx):
            state["tests"] = len(ctx["own"])
            return ctrl_invest, Q(1) if len(ctx["own"]) < 3 else Q(2, 3)
        h = Hyp("early-liar", propose)
        hyps = [sound_hyp("work", env, ctrl_work), h]
        rounds = run_auction(env, hyps, lambda k: 3, lambda k, i: Q(1), 60)
        self.assertEqual(h.record, -3)
        self.assertTrue(all(k <= 3 for k in h.rejections))     # rejected only while wealth-bound
        self.assertTrue(all(r.winner == 1 for r in rounds[1:]))   # round 1: a wealth-bound tie goes to `work`
        self.assertEqual(primitive_average(rounds[4:]), Q(2, 3))


class G_SublinearOverpromise(unittest.TestCase):
    def test_criterion_permits_rejecting_forever(self):
        """A hypothesis whose tested overpromise is sublinear (1/k per test, harmonic
        divergence) has a record tending to −∞ along a test set of density zero with
        divergent harmonic sum, so a BRIA may reject it at every other round and obtain
        nothing there.  The estimating agent below is checked on the finite arithmetic:
        record → −∞ along the tests (coverage), overestimation 0, average reward → 0
        while the controller is worth v = 1/2 every block."""
        v = Q(1, 2)
        T = 3000
        tests = sorted({int(j * math.log(j)) for j in range(2, 400) if int(j * math.log(j)) <= T})
        record = sum(v - (v + Q(1, k)) for k in tests)                 # Σ_{tests} (G − e)
        self.assertLess(record, -Q(3, 2))
        self.assertLess(Q(len(tests), T), Q(1, 7))
        harmonic_on_tests = sum(Q(1, k) for k in tests)
        self.assertGreater(harmonic_on_tests, Q(3, 2))                  # diverges as T → ∞
        # the agent: follows h on `tests` (reward v, estimate v), elsewhere takes an option
        # paying 0 with estimate 0 — no overestimation at all
        reward = sum(v for k in tests)
        self.assertLess(reward / T, Q(1, 14))
        overpromise_total = sum(Q(1, k) for k in tests)
        self.assertLess(overpromise_total, T)                           # sublinear, yet no guarantee


class H_CounterfactualTyping(unittest.TestCase):
    def test_observed_returns_exist_only_on_executed_blocks(self):
        """`invest` is executed on few blocks; `G^obs` exists only there; the external
        evaluator `Ĝ` (the environment model) is defined on every block; the identity
        Regret = SHIFT + SLACK + LEARN is typed with `Ĝ` and holds exactly."""
        env = investment_env(d=3)
        hyps = [sound_hyp("work", env, ctrl_work), const_hyp("invest1", ctrl_invest, Q(1))]
        rounds = run_auction(env, hyps, lambda k: 2, lambda k, i: Q(1, k * i * i), 60)
        observed = {r.k: r.G for r in rounds if r.winner == 1}
        self.assertLess(len(observed), 6)
        self.assertGreater(len(observed), 0)
        L = {r.k: r.promises[1] for r in rounds}
        Ghat_alpha = {r.k: execute(env, r.state, r.t, ctrl_invest, r.m)[0] for r in rounds}
        s_pi, t, Ghat_own = env.start, 0, {}
        for r in rounds:
            Ghat_own[r.k], s_pi, _, _, _ = execute(env, s_pi, t, ctrl_invest, r.m)
            t += r.m
        for k, G in observed.items():
            self.assertEqual(G, Ghat_alpha[k])                 # realized = external on tested blocks
        T = sum(r.m for r in rounds)
        V_pi = execute(env, env.start, 0, ctrl_invest, T)[0] * T
        V_alpha = sum(r.m * r.G for r in rounds)
        shift = sum(r.m * (Ghat_own[r.k] - Ghat_alpha[r.k]) for r in rounds)
        slack = sum(r.m * (Ghat_alpha[r.k] - L[r.k]) for r in rounds)
        learn = sum(r.m * (L[r.k] - r.G) for r in rounds)
        self.assertEqual(V_pi - V_alpha, shift + slack + learn)


class I_DistinctContinuations(unittest.TestCase):
    def test_outcome_of_one_continuation_is_no_test_of_a_claim_about_another(self):
        """`c_full` = the investing plan for the whole block; `c_prefix` = one step of it,
        then `work`.  They are different continuations (block values 1/2 and 5/18 from
        `base`), and an outcome generated by `c_prefix` is not a test of a claim about
        `c_full`."""
        env = investment_env(d=3)
        c_full, c_prefix = lease(ctrl_invest), prefix_then(1, ctrl_work)(ctrl_invest)
        self.assertFalse(valid_test(("invest", "full"), ("invest", c_prefix.treatment)))
        self.assertEqual(block_value(env, c_full, "base", 6), Q(1, 2))
        self.assertEqual(block_value(env, c_prefix, "base", 6), Q(5, 18))


class J_ClaimAboutAnotherContinuation(unittest.TestCase):
    def test_claim_about_the_prefix_continuation_is_kept_by_executing_it(self):
        """A hypothesis whose continuation is 'one step of the plan, then work' and whose
        claim is 5/18 is exactly kept when that continuation is executed: the
        interrupted plan is its own continuation with its own claim, not an invalid test
        of the whole plan."""
        env = investment_env(d=3)
        treat = prefix_then(1, ctrl_work)
        h = contextual_hyp("interrupted", treat(ctrl_invest), lambda s, m, t: Q(5, 18) if s == "base" else Q(1, 3))
        hyps = [sound_hyp("work", env, ctrl_work), h]
        rounds = run_auction(env, hyps, lambda k: 6, lambda k, i: Q(1), 20)
        self.assertEqual(h.record, 0)
        self.assertTrue(valid_test((treat(ctrl_invest).treatment,), (treat(ctrl_invest).treatment,)))


class K_DiscountedFiniteBlock(unittest.TestCase):
    def test_bounded_discount_mass_rescales(self):
        """A finite truncated discounted lease has weight `w_k = Σ_{j<m_k} γ^j ≤ 1/(1−γ)`;
        with bounded weights the weighted overestimation is `W` times the unweighted
        one on rescaled data in [0, 1]."""
        g = Q(1, 2)
        W = 1 / (1 - g)
        blocks = [(1 + k % 7, Q(k % 5, 5), Q(k % 3, 3)) for k in range(50)]
        w = [sum(g ** j for j in range(m)) for m, _, _ in blocks]
        self.assertTrue(all(wk <= W for wk in w))
        weighted = sum(wk * (e - G) for wk, (_, e, G) in zip(w, blocks))
        rescaled = sum(wk / W * e - wk / W * G for wk, (_, e, G) in zip(w, blocks))
        self.assertEqual(weighted, W * rescaled)
        self.assertTrue(all(0 <= wk / W * e <= 1 for wk, (_, e, _) in zip(w, blocks)))


class L_InfiniteDiscountedClaim(unittest.TestCase):
    def test_no_finite_prefix_settles_an_infinite_discounted_value(self):
        """Two environments agreeing on the first m rewards of a controller differ in
        discounted value by exactly `γ^m Δ`: the claim cannot be scored at a finite test
        without a further settlement mechanism (OPEN)."""
        g = Q(1, 2)
        m = 5
        head = [Q(1, 3)] * m
        tail_a, tail_b = [Q(0)] * 20, [Q(1)] * 20
        va = sum(g ** j * r for j, r in enumerate(head + tail_a))
        vb = sum(g ** j * r for j, r in enumerate(head + tail_b))
        self.assertEqual(vb - va, g ** m * sum(g ** j for j in range(20)))
        self.assertEqual(sum(head), sum(head))                         # the finite test sees no difference


class M_RecoverableAmendment(unittest.TestCase):
    def test_catch_up_cost_bounds_history_shift(self):
        """Persistent amendment with investment length d: from the learner's `base` the
        investor's block value is (m−d)/m, from its own `expanded` it is 1; the per-block
        history shift is exactly d for every m ≥ d — a bounded catch-up cost — so
        SHIFT_T ≤ dK = o(S_K) once the average block length grows."""
        for d in (1, 2, 4):
            env = investment_env(d=d)
            for m in (d, 2 * d, 8 * d):
                from_alpha = execute(env, "base", 0, ctrl_invest, m)[0]
                own = execute(env, "expanded", 0, ctrl_invest, m)[0]
                self.assertEqual(m * (own - from_alpha), d)


class N_IrreversibleBranch(unittest.TestCase):
    def test_shift_is_a_fixed_fraction(self):
        env = branch_env(good="B")
        for m in (2, 8, 32):
            self.assertEqual(m * (execute(env, "B", 1, ctrl_branch("B"), m)[0]
                                  - execute(env, "A", 1, ctrl_branch("B"), m)[0]), Q(2, 3) * m)


if __name__ == "__main__":
    unittest.main()
