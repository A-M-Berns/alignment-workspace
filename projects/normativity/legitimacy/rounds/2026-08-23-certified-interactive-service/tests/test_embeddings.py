"""Exact-preservation checks for the five prior-model translations.
Finite evidence for the paper derivations in PRIOR_ART_EMBEDDINGS.md."""
import itertools
import pathlib
import sys
import unittest
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "src"))

from embeddings import (GKInstance, ISSCInstance, MLSCInstance, RRGame,
                        SCDInstance, SCDRequest, gk_adaptive_submodular,
                        gk_certified, gk_env, gk_self_certifying,
                        gk_semantic, issc_certified, issc_env,
                        issc_fixed_target_witness, issc_semantic,
                        issc_version_space, mlsc_cover_time,
                        mlsc_generic_cover_times, mlsc_objective, mlsc_spec,
                        rr_occurrences, rr_play_winning, rr_value_periodic,
                        rr_wt_vector, scd_generic_objective, scd_objective,
                        scd_service_time)
from service_core import is_monotone, is_submodular, transcript_of


class TestSetCoverWithDelay(unittest.TestCase):
    def make_instance(self):
        one = Fraction(1)
        return SCDInstance(
            sets={"S1": frozenset({"e1", "e2"}), "S2": frozenset({"e2"})},
            cost={"S1": Fraction(3), "S2": Fraction(1)},
            requests=(
                SCDRequest("q1", "e1", 0, (one, one, one, one, one)),
                SCDRequest("q2", "e2", 1, (Fraction(1, 2),) * 5),
                SCDRequest("q3", "e1", 3, (one, one)),
            ),
            horizon=5)

    def test_objective_preserved_term_by_term(self):
        inst = self.make_instance()
        for schedule in ([(2, "S1"), (4, "S1")],
                         [(1, "S2"), (2, "S1")],
                         [(0, "S1")],
                         []):
            buy_a, delay_a, total_a = scd_objective(inst, schedule)
            buy_b, delay_b, total_b, taus = scd_generic_objective(
                inst, schedule)
            self.assertEqual(buy_a, buy_b)
            self.assertEqual(delay_a, delay_b)
            self.assertEqual(total_a, total_b)
            for req in inst.requests:
                self.assertEqual(scd_service_time(inst, schedule, req),
                                 taus[req.rid])

    def test_past_purchase_does_not_serve_future_arrival(self):
        inst = self.make_instance()
        schedule = [(2, "S1")]           # q3 arrives at 3: not served
        self.assertIsNone(scd_service_time(inst, schedule,
                                           inst.requests[2]))
        *_, taus = scd_generic_objective(inst, schedule)
        self.assertIsNone(taus["q3"])

    def test_permanent_nonservice_is_permitted(self):
        # Paper footnote 2: the model does not force service; both
        # sides account the empty schedule identically.
        inst = self.make_instance()
        _, delay, total = scd_objective(inst, [])
        self.assertEqual(total, delay)
        self.assertGreater(delay, 0)


class TestSubmodularRankingMLSC(unittest.TestCase):
    def make_instance(self, uniform=False):
        vs = ("r", "u", "v", "w")
        if uniform:
            d = {(a, b): Fraction(1) for a in vs for b in vs if a != b}
        else:
            d = {}
            coords = {"r": 0, "u": 2, "v": 3, "w": 7}
            for a in vs:
                for b in vs:
                    if a != b:
                        d[(a, b)] = Fraction(abs(coords[a] - coords[b]))
        f1 = lambda s: Fraction(1) if "u" in s else Fraction(0)
        f2 = lambda s: min(Fraction(1),
                           Fraction(len(s & {"u", "v", "w"}), 2))
        return MLSCInstance(vs, d, "r", {"f1": f1, "f2": f2})

    def test_functions_are_normalized_monotone_submodular(self):
        inst = self.make_instance()
        ground = ("u", "v", "w")
        for f in inst.functions.values():
            self.assertTrue(is_monotone(f, ground))
            self.assertTrue(is_submodular(f, ground))
            self.assertEqual(f(frozenset(ground) | {"r"}), 1)

    def test_cover_times_preserved_on_metric_paths(self):
        inst = self.make_instance()
        for path in itertools.permutations(("u", "v", "w")):
            generic = mlsc_generic_cover_times(inst, path)
            for name in inst.functions:
                self.assertEqual(mlsc_cover_time(inst, path, name),
                                 generic[name])

    def test_uniform_metric_is_submodular_ranking(self):
        # Cover time under the uniform metric = number of elements in
        # the covering prefix, the Submodular Ranking objective.
        inst = self.make_instance(uniform=True)
        path = ("v", "u", "w")
        self.assertEqual(mlsc_cover_time(inst, path, "f1"), 2)
        self.assertEqual(mlsc_cover_time(inst, path, "f2"), 2)
        self.assertEqual(mlsc_objective(inst, path), 4)
        generic = mlsc_generic_cover_times(inst, path)
        self.assertEqual(generic["f1"], 2)
        self.assertEqual(generic["f2"], 2)

    def test_repetition_harmless_under_set_factoring(self):
        inst = self.make_instance(uniform=True)
        spec = mlsc_spec(inst, "f2")
        t1 = transcript_of((("u", "ok"), ("v", "ok")))
        t2 = transcript_of((("u", "ok"), ("u", "ok"), ("v", "ok")))
        self.assertTrue(spec.certified(t1))
        self.assertTrue(spec.certified(t2))


class TestAdaptiveSubmodularity(unittest.TestCase):
    def modular_instance(self):
        # f counts items observed working; states independent.
        names = {}
        for s1 in "01":
            for s2 in "01":
                names[f"phi{s1}{s2}"] = {"e1": s1, "e2": s2}
        f = lambda dom, n: sum(
            Fraction(1) for e in dom if names[n][e] == "1")
        return GKInstance(("e1", "e2"), names,
                          {k: Fraction(1, 4) for k in names},
                          f, Fraction(1))

    def synergy_instance(self):
        # Value only when both items observed working: conditional
        # synergy violates adaptive submodularity (GK Section 3.4).
        names = {"phiA": {"e1": "1", "e2": "1"},
                 "phiB": {"e1": "1", "e2": "0"}}
        f = lambda dom, n: (Fraction(1)
                            if {"e1", "e2"} <= set(dom)
                            and all(names[n][e] == "1" for e in dom)
                            else Fraction(0))
        return GKInstance(("e1", "e2"), names,
                          {"phiA": Fraction(1, 2), "phiB": Fraction(1, 2)},
                          f, Fraction(1))

    def test_env_is_consistency_relational(self):
        inst = self.modular_instance()
        env = gk_env(inst)
        self.assertEqual(env.responses((), "e1"), frozenset({"0", "1"}))
        self.assertEqual(env.responses((("e1", "1"),), "e1"),
                         frozenset({"1"}))

    def test_certificate_sound_for_every_consistent_realization(self):
        # Check_sigma(h, c) => Goal_sigma(h, w) for every w compatible
        # with h: GK Definition 7 gives exactly this.
        inst = self.modular_instance()
        for h in [(("e1", "1"),), (("e1", "0"), ("e2", "1"))]:
            if gk_certified(inst, h):
                for n in inst.realizations:
                    consistent = all(inst.realizations[n][e] == s
                                     for e, s in h)
                    if consistent:
                        self.assertTrue(gk_semantic(inst, h, n))

    def test_modular_instance_is_adaptive_submodular_and_self_certifying(self):
        inst = self.modular_instance()
        self.assertTrue(gk_adaptive_submodular(inst))
        self.assertTrue(gk_self_certifying(inst))

    def test_synergy_instance_fails_adaptive_submodularity(self):
        self.assertFalse(gk_adaptive_submodular(self.synergy_instance()))


class TestInteractiveSubmodularSetCover(unittest.TestCase):
    def make_instance(self):
        # Two hypotheses; question qx separates them; question qc makes
        # covering progress for both.
        hyps = ("h1", "h2")
        questions = ("qx", "qc")
        valid = {("qx", "h1"): frozenset({"x1"}),
                 ("qx", "h2"): frozenset({"x2"}),
                 ("qc", "h1"): frozenset({"c", "cq"}),
                 ("qc", "h2"): frozenset({"c"})}
        def F_of(h):
            def F(pairs):
                return (Fraction(1)
                        if any(q == "qc" for (q, r) in pairs)
                        else Fraction(0))
            return F
        return ISSCInstance(hyps, questions, valid,
                            {"qx": Fraction(1), "qc": Fraction(1)},
                            {h: F_of(h) for h in hyps}, Fraction(1))

    def test_env_responses_union_over_version_space(self):
        inst = self.make_instance()
        env = issc_env(inst)
        self.assertEqual(env.responses((), "qx"), frozenset({"x1", "x2"}))
        self.assertEqual(env.responses((("qx", "x1"),), "qc"),
                         frozenset({"c", "cq"}))

    def test_consistency_adversary_equals_fixed_target(self):
        # Every finite run of the consistency-relational environment is
        # a run of the fixed-target environment for EVERY member of the
        # final version space.
        inst = self.make_instance()
        env = issc_env(inst)
        def runs(h, depth):
            if depth == 0:
                return [h]
            out = [h]
            for q in inst.questions:
                for r in env.responses(h, q):
                    out.extend(runs(h + ((q, r),), depth - 1))
            return out
        for h in runs((), 2):
            self.assertTrue(issc_fixed_target_witness(inst, h))
            self.assertTrue(issc_version_space(inst, h))

    def test_certificate_sound_for_true_target(self):
        inst = self.make_instance()
        h = (("qc", "c"),)
        self.assertTrue(issc_certified(inst, h))
        for target in issc_version_space(inst, h):
            self.assertTrue(issc_semantic(inst, h, target))

    def test_semantic_without_certificate_blocks_sound_stopping(self):
        # F_{h*} >= alpha can hold while the version-space certificate
        # fails; a learner stopping on hidden truth would be unsound.
        hyps = ("h1", "h2")
        valid = {("q", "h1"): frozenset({"r"}),
                 ("q", "h2"): frozenset({"r"})}
        F = {"h1": lambda pairs: Fraction(1),
             "h2": lambda pairs: Fraction(0)}
        inst = ISSCInstance(hyps, ("q",), valid, {"q": Fraction(1)},
                            F, Fraction(1))
        h = (("q", "r"),)
        self.assertTrue(issc_semantic(inst, h, "h1"))
        self.assertFalse(issc_certified(inst, h))


class TestRequestResponseGames(unittest.TestCase):
    def paper_example_game(self):
        # Figure 1 of arXiv 1406.4648v1: q (Player 1) chooses which
        # conditions to request; p (Player 0) answers one, both by
        # detour, or none.
        vertices = ("q", "m1", "m12", "m2", "p", "c1", "c2", "cr")
        edges = {"q": ("m1", "m12", "m2"),
                 "m1": ("p",), "m12": ("p",), "m2": ("p",),
                 "p": ("c1", "c2", "cr"),
                 "c1": ("cr",), "c2": ("cr",), "cr": ("q",)}
        owner = {"q": 1, "m1": 1, "m12": 1, "m2": 1,
                 "p": 0, "c1": 0, "c2": 0, "cr": 0}
        conditions = ((frozenset({"m1", "m12"}), frozenset({"c1"})),
                      (frozenset({"m12", "m2"}), frozenset({"c2"})))
        return RRGame(vertices, edges, owner, conditions)

    def test_paper_example_value_56_over_10(self):
        # Example 2: adversary always requests both; Player 0
        # alternates c1, c2. The play settles into a loop of length 10
        # with waiting-time sum 56; value 56/10.
        game = self.paper_example_game()
        cycle = ("q", "m12", "p", "c1", "cr",
                 "q", "m12", "p", "c2", "cr")
        val = rr_value_periodic(game, (), cycle)
        self.assertEqual(val, Fraction(56, 10))
        self.assertTrue(rr_play_winning(game, (), cycle))

    def test_starving_play_loses_and_diverges(self):
        game = self.paper_example_game()
        cycle = ("q", "m12", "p", "c1", "cr")   # condition 2 starves
        self.assertIsNone(rr_value_periodic(game, (), cycle))
        self.assertFalse(rr_play_winning(game, (), cycle))

    def test_waiting_time_coalesces_repeat_requests(self):
        # Paper Section 3: while a request is open, additional requests
        # of the same condition are ignored.
        game = self.paper_example_game()
        prefix = ("q", "m12", "p", "cr", "q", "m12", "p", "c1", "cr")
        wt = rr_wt_vector(game, prefix)
        # Condition 1 was requested twice but closed once: wt reset.
        self.assertEqual(wt[0], 0)
        occ = rr_occurrences(game, prefix)
        cond1 = [o for o in occ if o[0] == 0]
        self.assertEqual(len(cond1), 1)          # coalesced: ONE occurrence

    def test_identity_bearing_multiplicity_breaks_coalescing(self):
        # Occurrence-level accounting with per-occurrence exclusive
        # evidence: two openings coalesced into one RR occurrence are
        # closed by one response, but two identity-bearing liabilities
        # under an exclusive-evidence account rule need two. The RR
        # verdict (satisfied) and the occurrence-level verdict (one
        # liability unclosed) separate.
        game = self.paper_example_game()
        prefix = ("q", "m12", "p", "cr", "q", "m12", "p", "c1", "cr")
        openings = [t for t, v in enumerate(prefix) if v == "m12"]
        self.assertEqual(len(openings), 2)       # two identity-bearing accruals
        responses = [t for t, v in enumerate(prefix) if v == "c1"]
        self.assertEqual(len(responses), 1)      # one closing receipt
        occ = rr_occurrences(game, prefix)
        self.assertEqual(len([o for o in occ if o[0] == 0]), 1)
        # Exclusive evidence: 2 liabilities, 1 receipt -> one strands.
        self.assertLess(len(responses), len(openings))


if __name__ == "__main__":
    unittest.main()
