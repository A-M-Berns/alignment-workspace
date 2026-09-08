"""Fixtures L–O: the irreversible branch (continuation competence without policy regret),
the exact regret decomposition, recoverable environments, easy policy with hard value,
and the hypothesis that learns its own promise."""
import math
import unittest
from fractions import Fraction as Q

from src.bria import const_hyp, contextual_hyp, learning_hyp, run_auction, sound_hyp
from src.envs import (branch_env, ctrl_branch, ctrl_const, ctrl_invest, ctrl_work, execute,
                      investment_env, mixing_env, Env)


def own_trajectory(env, controller, T):
    return execute(env, env.start, 0, controller, T)[0] * T


def decompose(env, pi, alpha_rounds, promises):
    """V_T(π) − V_T(α) = history-shift + slack + learning error, with T = Σ m_k.

    history-shift  Δ = Σ_k m_k (G_k(π | H^π_{t_k}) − G_k(π | H^α_{t_k}))
    slack          Σ_k m_k (G_k(π | H^α_{t_k}) − L_k)          (L_k the promise π's hypothesis makes)
    learning       Σ_k m_k (L_k − G_k(α))
    Every term is exact; the first two are counterfactual except on tested blocks."""
    T = sum(r.m for r in alpha_rounds)
    V_pi = own_trajectory(env, pi, T)
    V_alpha = sum(r.m * r.G for r in alpha_rounds)
    s_pi, t = env.start, 0
    shift = slack = learn = Q(0)
    for r, L in zip(alpha_rounds, promises):
        G_own, s_pi, _, _, _ = execute(env, s_pi, t, pi, r.m)
        G_from_alpha = execute(env, r.state, r.t, pi, r.m)[0]
        shift += r.m * (G_own - G_from_alpha)
        slack += r.m * (G_from_alpha - L)
        learn += r.m * (L - r.G)
        t += r.m
    return V_pi - V_alpha, shift, slack, learn


class L_IrreversibleBranch(unittest.TestCase):
    def test_continuation_competence_holds_and_policy_regret_is_linear(self):
        """The learner took A at t = 0 (for a deterministic learner the environment can
        always make the taken branch the bad one).  From then on every controller's block
        value from the actual history is 1/3, every sound promise is 1/3, the learner
        obtains 1/3: continuation competence is exact.  The own-trajectory value of the
        policy "B" is 1 per step: regret (2/3)(T−1), all of it history-shift except the
        one block in which the blind prior under-promised the untaken branch."""
        env = branch_env(good="B")
        m = 4
        piB = ctrl_branch("B")

        def blind(controller):
            # the environment hides which branch is good: at `start` both hypotheses
            # promise the same prior; afterwards each promises its sound block value
            def promise_of(s, m, t):
                return Q(1, 4) if s == "start" else execute(env, s, t, controller, m)[0]
            return contextual_hyp(controller.__name__, controller, promise_of)
        hyps = [blind(ctrl_branch("A")), blind(piB)]
        rounds = run_auction(env, hyps, lambda k: m, lambda k, i: Q(1), 25)
        self.assertEqual(rounds[0].state, "start")
        self.assertEqual(rounds[0].winner, 0)                    # tie at the prior, lowest index
        self.assertEqual(rounds[0].G, Q(1, 4))                   # and the prior happened to be kept
        self.assertTrue(all(r.state == "A" for r in rounds[1:]))
        self.assertTrue(all(r.G == r.alpha_e for r in rounds))    # every promise exactly kept
        T = m * len(rounds)
        regret, shift, slack, learn = decompose(env, piB, rounds, [r.alpha_e for r in rounds])
        self.assertEqual(learn, 0)
        self.assertEqual(slack, 2)                     # the blind prior at the branch point only
        self.assertEqual(shift, regret - 2)
        self.assertEqual(regret, Q(2, 3) * (T - 1))

    def test_no_learner_escapes(self):
        """Whichever branch a deterministic learner takes first, the environment with the
        other branch good gives it 1/3 forever; the hindsight-best legitimate policy gets
        1.  Sublinear regret against the unrestricted legitimate class is impossible."""
        for first in ("A", "B"):
            other = "B" if first == "A" else "A"
            env = branch_env(good=other)
            T = 30
            learner_value = own_trajectory(env, ctrl_branch(first), T)
            best = own_trajectory(env, ctrl_branch(other), T)
            self.assertEqual(best - learner_value, Q(2, 3) * (T - 1))


class RegretDecomposition(unittest.TestCase):
    def test_identity_is_exact_on_a_generic_run(self):
        """V_T(π) − V_T(α) = Δ + slack + learning, term by term, on the renewable
        amendment fixture with an over-promising and a sound hypothesis in play."""
        env = investment_env(d=1, e=2)
        hyps = [sound_hyp("work", env, ctrl_work), sound_hyp("invest", env, ctrl_invest),
                learning_hyp("learner", ctrl_invest, Q(1, 10))]
        rounds = run_auction(env, hyps, lambda k: 2, lambda k, i: Q(1, k * i * i), 60)
        promises = [r.promises[1] for r in rounds]           # the sound investor's promises
        regret, shift, slack, learn = decompose(env, ctrl_invest, rounds, promises)
        self.assertEqual(regret, shift + slack + learn)
        self.assertEqual(slack, 0)                             # sound promise is exact here


class M_Recoverable(unittest.TestCase):
    def test_episodic_reset_makes_history_shift_vanish(self):
        """Every block starts at the common state: G_k(π | H^α) = G_k(π | H^π) exactly."""
        env = investment_env(d=1, e=2)
        hyps = [sound_hyp("work", env, ctrl_work), sound_hyp("invest", env, ctrl_invest)]
        rounds = run_auction(env, hyps, lambda k: 3, lambda k, i: Q(1), 30, reset=lambda s: "base")
        self.assertTrue(all(r.state == "base" for r in rounds))
        for r in rounds:
            self.assertEqual(execute(env, "base", r.t, ctrl_invest, 3)[0],
                             execute(env, "base", 0, ctrl_invest, 3)[0])

    def test_mixing_recovers_within_one_step(self):
        """`go` from x and from y differ by exactly one step per block: the history-shift
        per block is ≤ 1, so Δ_T / T ≤ 1/m, which vanishes as the horizon grows."""
        env = mixing_env()
        for m in (2, 4, 8, 16):
            gx = execute(env, "x", 0, ctrl_const("go"), m)[0]
            gy = execute(env, "y", 0, ctrl_const("go"), m)[0]
            self.assertEqual(m * (gy - gx), 1)

    def test_irreversible_branch_is_not_recoverable(self):
        env = branch_env(good="B")
        for m in (2, 4, 8, 16):
            from_alpha = execute(env, "A", 1, ctrl_branch("B"), m)[0]
            own = execute(env, "B", 1, ctrl_branch("B"), m)[0]
            self.assertEqual(m * (own - from_alpha), Q(2, 3) * m)


def sqrt2_bit(t):
    """The t-th binary digit of √2 after the point (an easy policy's hard-to-predict
    reward): computable, and no efficiently computable promise better than the running
    mean is available to the fixture."""
    return (math.isqrt(2 * 4 ** (t + 1)) >> 0) & 1


class N_EasyPolicyHardValue(unittest.TestCase):
    def test_averaged_promise_survives_where_the_pointwise_value_is_opaque(self):
        """Controller `a` pays the t-th bit of √2.  The hypothesis promising 1/2 − 1/10
        is never refuted over 4000 steps (its record grows), though its pointwise value is
        the bit itself.  Theorem 4's class, not Theorem 3's."""
        def reward(s, a, t):
            return Q(sqrt2_bit(t)) if a == "a" else Q(3, 10)
        env = Env(reward, lambda s, a, t: s, lambda s, t: {"a", "b"}, "s")
        hyps = [sound_hyp("b", env, ctrl_const("b")), const_hyp("a", ctrl_const("a"), Q(2, 5))]
        rounds = run_auction(env, hyps, lambda k: 1, lambda k, i: Q(1), 4000)
        self.assertGreater(hyps[1].record, 300)
        self.assertGreater(len(hyps[1].wins), 3900)


class O_LearningHypothesis(unittest.TestCase):
    def test_promise_converges_to_the_observed_block_value(self):
        """The learning hypothesis promises the minimum block value observed on its own
        past leases from the same state, less a margin.  It must be tested to learn, and
        a test needs a bid above the incumbent's, so it starts optimistic (prior 1), is
        refuted exactly once (record −1), and from then on promises the observed value
        less the margin, which it keeps on every later lease."""
        env = investment_env(d=1, e=2)
        margin = Q(1, 10)
        h = learning_hyp("learn", ctrl_invest, margin, prior=Q(1))
        hyps = [sound_hyp("work", env, ctrl_work), h]
        rounds = run_auction(env, hyps, lambda k: 3, lambda k, i: Q(1), 40)
        self.assertGreater(len(h.wins), 35)
        self.assertEqual(h.record, -1 + Q(3, 10) * (len(h.wins) - 1))   # refuted once, then +margin per lease
        true_value = execute(env, "base", 0, ctrl_invest, 3)[0]
        self.assertEqual(true_value, Q(2, 3))
        self.assertEqual({s for (s, m, G) in h.own}, {"base"})
        self.assertEqual(h.propose({"state": "base", "m": 3, "t": 0, "k": 0, "own": h.own})[1],
                         true_value - margin)
        self.assertTrue(all(r.alpha_e == true_value - margin for r in rounds[2:]))
        pessimistic = learning_hyp("learn0", ctrl_invest, margin, prior=Q(0))
        run_auction(env, [sound_hyp("work", env, ctrl_work), pessimistic], lambda k: 3, lambda k, i: Q(1), 40)
        self.assertEqual(pessimistic.wins, [])                 # never tested, never learns


if __name__ == "__main__":
    unittest.main()
