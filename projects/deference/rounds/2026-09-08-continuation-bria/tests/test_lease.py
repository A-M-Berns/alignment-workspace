"""Fixtures D–H: the one-step pseudo-test, hard commitment against a live principal,
the gated lease and its transparency, biased testing and the contextual-promise repair."""
import unittest
from fractions import Fraction as Q

from src.bria import const_hyp, primitive_average, run_auction, sound_hyp
from src.envs import (BOT, block_value, context_env, ctrl_const, ctrl_hack, ctrl_invest,
                      ctrl_work, execute, investment_env)


def pseudo_test(env, s, plan, m, j):
    """Follow `plan` for j steps, then `work` for the remaining m − j: the return the
    learner would score the plan on if it withdrew control after j steps."""
    def c(state, i, t):
        return plan(state, i, t) if i < j else ctrl_work(state, i, t)
    return execute(env, s, 0, c, m)[0]


class D_PseudoTest(unittest.TestCase):
    def test_withdrawing_control_refutes_a_sound_promise(self):
        """d = 3, m = 6.  The plan's sound promise is (6−3)/6 = 1/2.  Every execution
        that hands control back before the lease ends scores strictly below it."""
        env = investment_env(d=3)
        m = 6
        promise = block_value(env, ctrl_invest, "base", m)
        self.assertEqual(promise, Q(1, 2))
        for j in range(0, m):
            self.assertLess(pseudo_test(env, "base", ctrl_invest, m, j), promise)
        self.assertEqual(pseudo_test(env, "base", ctrl_invest, m, 1), Q(5, 18))
        self.assertEqual(pseudo_test(env, "base", ctrl_invest, m, m), promise)

    def test_necessity_of_execution_rights(self):
        """For every proper prefix length j < d the truncated return is at most 1/3,
        whatever follows the prefix: the benefit is reachable only through the whole
        investment, so no test that stops early can be evidence about the promise."""
        env = investment_env(d=3)
        m = 6
        for j in range(0, 3):
            for tail in (ctrl_work, ctrl_const("continue"), ctrl_const("request")):
                def c(state, i, t, j=j, tail=tail):
                    return ctrl_invest(state, i, t) if i < j else tail(state, i, t)
                self.assertLessEqual(execute(env, "base", 0, c, m)[0], Q(1, 3))


class E_HardCommitment(unittest.TestCase):
    def test_hard_lease_executes_a_prohibited_action(self):
        """The principal revokes `expanded` from t = 3.  Ungated execution of the
        investing plan takes it anyway (3 prohibited actions in 6 steps); the gated
        lease refuses them.  The ungated promise 5/6 is a promise about a trajectory the
        constitution does not permit."""
        env = investment_env(d=1, revoke_at=3)
        G_hard, _, _, traj_hard, _ = execute(env, "base", 0, ctrl_invest, 6, gated=False)
        self.assertEqual(G_hard, Q(5, 6))
        self.assertEqual(sum(1 for i, (s, a, r) in enumerate(traj_hard) if i >= 3 and a == "expanded"), 3)
        G_gated, _, _, traj_gated, refused = execute(env, "base", 0, ctrl_invest, 6, gated=True)
        self.assertEqual(refused, 3)
        self.assertEqual([a for (s, a, r) in traj_gated], ["request", "expanded", "expanded", BOT, BOT, BOT])
        self.assertEqual(G_gated, Q(1, 3))


class F_GatedLease(unittest.TestCase):
    def test_transparency_for_a_legitimate_controller(self):
        """Every proposal of the investing controller is admitted along its own gated
        trajectory, so gated and ungated executions coincide (Lean `exec_gated_eq`)."""
        env = investment_env(d=2)
        gated = execute(env, "base", 0, ctrl_invest, 8, gated=True)
        plain = execute(env, "base", 0, ctrl_invest, 8, gated=False)
        self.assertEqual(gated[3], plain[3])
        self.assertEqual(gated[4], 0)

    def test_illegitimate_controller_is_tested_through_the_gate(self):
        """The hacking controller is a valid test object: its gated execution is
        well-defined (every step refused, return 0), so its promise 1 is refuted on the
        gated trajectory without any prohibited action being executed."""
        env = investment_env(d=1, typed=True)
        G, _, _, traj, refused = execute(env, "base", 0, ctrl_hack, 4)
        self.assertEqual((G, refused), (Q(0), 4))
        self.assertTrue(all(a == BOT for (s, a, r) in traj))
        untyped = investment_env(d=1, typed=False)
        G_u, _, _, traj_u, _ = execute(untyped, "base", 0, ctrl_hack, 4)
        self.assertEqual([a for (s, a, r) in traj_u], ["hack", "violate", "violate", "violate"])
        self.assertGreater(G_u, Q(1, 3))

    def test_correction_mid_lease_changes_the_return_not_the_lease(self):
        """With the principal live, the same controller under the same lease yields
        different legitimate trajectories depending on the exterior's response; the
        sound contextual promise is computed through the gate and stays exact."""
        for revoke in (None, 2, 5):
            env = investment_env(d=1, revoke_at=revoke)
            h = sound_hyp("invest", env, ctrl_invest)
            ctrl, e = h.propose({"state": "base", "m": 6, "t": 0, "own": []})
            self.assertEqual(e, execute(env, "base", 0, ctrl, 6)[0])
        self.assertEqual(execute(investment_env(1, revoke_at=2), "base", 0, ctrl_invest, 6)[0], Q(1, 6))
        self.assertEqual(execute(investment_env(1, revoke_at=5), "base", 0, ctrl_invest, 6)[0], Q(4, 6))


class G_BiasedTesting(unittest.TestCase):
    def test_raw_averages_reverse_a_pointwise_dominance(self):
        """`a` beats `b` in both contexts; a scheduler that tests `a` on hard steps and
        `b` on easy steps records a: 3/10, b: 9/10."""
        env = context_env()
        s, t = env.start, 0
        totals = {"a": [], "b": []}
        for _ in range(100):
            tested = "a" if s == "hard" else "b"
            r = env.reward(s, tested, t)
            totals[tested].append(r)
            s, t = env.step(s, tested, t), t + 1
        avg = {c: sum(v) / len(v) for c, v in totals.items()}
        self.assertEqual(avg, {"a": Q(3, 10), "b": Q(9, 10)})
        for ctx in ("easy", "hard"):
            self.assertGreater(env.reward(ctx, "a", 0), env.reward(ctx, "b", 0))


class H_ContextualPromiseRepair(unittest.TestCase):
    def test_contextual_promises_rank_within_the_context(self):
        """Hypotheses promise from the actual context.  `a`'s promise exceeds `b`'s at
        every step, both records stay 0, and the auction follows `a` from the first
        round it can afford to: average (1 + 3/10)/2 = 13/20."""
        env = context_env()
        hyps = [sound_hyp("b", env, ctrl_const("b")), sound_hyp("a", env, ctrl_const("a"))]
        rounds = run_auction(env, hyps, lambda k: 1, lambda k, i: Q(1), 200)
        self.assertTrue(all(r.winner == 1 for r in rounds))
        self.assertEqual({(r.state, r.alpha_e) for r in rounds}, {("easy", Q(1)), ("hard", Q(3, 10))})
        self.assertEqual(hyps[0].record, 0)
        self.assertEqual(hyps[1].record, 0)
        self.assertEqual(primitive_average(rounds), Q(13, 20))

    def test_a_context_free_promise_is_refuted_where_the_contextual_one_is_kept(self):
        """A hypothesis for `a` promising its easy value everywhere is tested and loses
        7/10 on every hard step; its record diverges while the contextual `a` keeps 0."""
        env = context_env()
        hyps = [const_hyp("a-flat", ctrl_const("a"), Q(1)), sound_hyp("a", env, ctrl_const("a"))]
        rounds = run_auction(env, hyps, lambda k: 1, lambda k, i: Q(1), 100)
        self.assertLess(hyps[0].record, -Q(7, 10) * 10)
        self.assertEqual(hyps[1].record, 0)


if __name__ == "__main__":
    unittest.main()
