"""Third pass: the discovery residual, the information-cell obstruction, the frontier
theorem, adaptivity, the countermodels, and the chain actual → discovered → full."""

import random
import unittest
from fractions import Fraction as Q
from itertools import product

from src.inquiry import Inquiry, Action, query, greedy_frontier
from src.sensitivity import (WeightedCount, Defeat, GroundedDefeat, Redundant, adverse,
                             omission_gain, subsets)
from src.attacks_discovery import cases, W
from src.supply import Reason, Instance


def random_inquiry(rng, n_reasons, n_worlds, n_actions):
    reasons = [f"r{i}" for i in range(n_reasons)]
    worlds = {f"w{j}": frozenset(r for r in reasons if rng.random() < 0.5) for j in range(n_worlds)}
    acts = []
    for k in range(n_actions):
        if rng.random() < 0.6:
            acts.append(query(rng.choice(reasons), rng.randint(1, 2)))
        else:
            S = frozenset(r for r in reasons if rng.random() < 0.5)
            acts.append(Action(f"t{k}", rng.randint(1, 2), (lambda S: lambda t: len(t & S) % 2)(S)))
    F = WeightedCount({r: -Q(rng.randint(0, 4), 8) for r in reasons})
    return Inquiry(worlds, acts, F)


class Residual(unittest.TestCase):

    def test_programs_are_antitone_on_the_adverse_universe(self):
        for c in cases():
            if c.inq is not None:
                self.assertTrue(c.inq.is_antitone(), c.name)

    def test_residual_is_bounded_by_conditional_adverse_mass(self):
        rng = random.Random(1)
        for _ in range(60):
            I = random_inquiry(rng, rng.randint(1, 3), rng.randint(1, 4), rng.randint(1, 3))
            for w, T in I.worlds.items():
                for D in [frozenset(), *[frozenset(x) for x in [list(T)[:1]]]]:
                    if not D <= T:
                        continue
                    res = I.residual(D, w)
                    self.assertGreaterEqual(res, 0)
                    self.assertLessEqual(res, sum((I.cond_adverse(r, D) for r in T - D), Q(0)))

    def test_frontier_empty_implies_zero_residual(self):
        rng = random.Random(2)
        for _ in range(60):
            I = random_inquiry(rng, rng.randint(1, 3), rng.randint(1, 4), rng.randint(1, 3))
            K = frozenset(I.worlds)
            D = I.certain(K)
            if not I.frontier(K, D):
                for w in K:
                    self.assertEqual(I.residual(D, w), Q(0))

    def test_conditional_mass_is_the_right_quantity_under_defeat(self):
        F = Defeat({"for": W, "c": -W}, {"c": {"e"}})
        I0 = Inquiry({"w0": set(), "w1": {"c"}}, [query("c")], F, pro={"for"})
        I1 = Inquiry({"w0": set(), "w1": {"c"}}, [query("c")], F, pro={"for", "e"})
        self.assertEqual(I0.cond_adverse("c", frozenset()), W)
        self.assertEqual(I1.cond_adverse("c", frozenset()), Q(0))
        self.assertEqual(I0.frontier(frozenset(I0.worlds), frozenset()), ["c"])
        self.assertEqual(I1.frontier(frozenset(I1.worlds), frozenset()), [])

    def test_redundancy_conditional_mass_vanishes_after_one(self):
        F = Redundant([(-W, {"r1", "r2"})])
        I = Inquiry({"w0": set(), "w1": {"r1"}, "w2": {"r2"}, "w12": {"r1", "r2"}}, [query("r1"), query("r2")], F)
        self.assertEqual(I.cond_adverse("r2", frozenset()), W)
        self.assertEqual(I.cond_adverse("r2", frozenset({"r1"})), Q(0))
        self.assertEqual(I.gap(frozenset(I.worlds)), W)


class Obstruction(unittest.TestCase):

    def test_every_sound_policy_is_bounded_below_by_the_cell_gap(self):
        """Exhaustive over sound policies on tiny models: a sound docket is a choice of a
        subset of the certain docket per repertoire cell."""
        rng = random.Random(3)
        for _ in range(40):
            I = random_inquiry(rng, rng.randint(1, 2), rng.randint(1, 3), rng.randint(1, 2))
            cells = I.cells(I.actions)
            for K in cells:
                cert = I.certain(K)
                gap = I.gap(K)
                subs = [frozenset(x) for k in range(len(cert) + 1)
                        for x in __import__("itertools").combinations(sorted(cert), k)]
                for D in subs:
                    worst = max(I.residual(D, w) for w in K)
                    self.assertGreaterEqual(worst, gap)
                self.assertEqual(max(I.residual(cert, w) for w in K), gap)

    def test_minimax_with_unbounded_budget_is_the_obstruction(self):
        rng = random.Random(4)
        for _ in range(40):
            I = random_inquiry(rng, rng.randint(1, 3), rng.randint(1, 4), rng.randint(1, 3))
            self.assertEqual(I.minimax(), I.obstruction())

    def test_minimax_is_monotone_in_budget_and_above_the_obstruction(self):
        rng = random.Random(5)
        for _ in range(40):
            I = random_inquiry(rng, rng.randint(1, 3), rng.randint(1, 4), rng.randint(1, 3))
            vals = [I.minimax(B=b) for b in range(0, 6)]
            for x, y in zip(vals, vals[1:]):
                self.assertGreaterEqual(x, y)
            for v in vals:
                self.assertGreaterEqual(v, I.obstruction())
                self.assertGreaterEqual(I.nonadaptive(vals.index(v)), v)

    def test_minimax_matches_exhaustive_decision_trees(self):
        """Enumerate every adaptive policy as a decision tree on a tiny instance."""
        I = Inquiry({"w0": set(), "w1": {"a"}, "w2": {"b"}, "w3": {"a", "b"}},
                    [query("a"), query("b")], WeightedCount({"a": -W, "b": -Q(1, 8)}))

        def best(K, B):
            # a policy: stop, or pick an affordable action then recurse per outcome
            vals = [I.gap(K)]
            for a in I.actions:
                if a.cost > B:
                    continue
                parts = {}
                for w in K:
                    parts.setdefault(a.outcome(I.worlds[w]), set()).add(w)
                vals.append(max(best(frozenset(p), B - a.cost) for p in parts.values()))
            return min(vals)
        for B in range(0, 3):
            self.assertEqual(I.minimax(B=B), best(frozenset(I.worlds), B))
        self.assertEqual(I.minimax(B=1), Q(1, 8))   # ask about the heavy one
        self.assertEqual(I.minimax(B=2), Q(0))


class GeneralObstruction(unittest.TestCase):
    """The best-response form for arbitrary extensional programs."""

    def test_general_gap_equals_antitone_gap_on_antitone_models(self):
        rng = random.Random(6)
        for _ in range(40):
            I = random_inquiry(rng, rng.randint(1, 3), rng.randint(1, 4), rng.randint(1, 3))
            for K in I.cells(I.actions):
                self.assertEqual(I.gap_general(K), I.gap(K))

    def test_larger_dockets_never_help_the_advisor(self):
        rng = random.Random(7)
        F = GroundedDefeat({"for": W, "d": Q(0), "e": Q(0)}, {"for": {"d"}, "d": {"e"}})
        for _ in range(30):
            T = frozenset(r for r in ["d", "e"] if rng.random() < 0.6)
            I = Inquiry({"w": T}, [], F, pro={"for"})
            for D in subsets(sorted(T)):
                for D2 in subsets(sorted(T)):
                    if D <= D2:
                        self.assertLessEqual(I.best_response(D2, T), I.best_response(D, T))

    def test_general_gap_is_exact_for_a_non_antitone_program(self):
        """`d` defeats `for` (adverse), `e` defeats `d` (pro): the verdict is not antitone in
        the universe {d, e}.  Every sound docket, with the advisor's best response, is
        bounded below by the general gap, and the exhaustive docket attains it."""
        F = GroundedDefeat({"for": W, "d": Q(0), "e": Q(0)}, {"for": {"d"}, "d": {"e"}})
        worlds = {"w0": set(), "wd": {"d"}, "wde": {"d", "e"}, "we": {"e"}}
        I = Inquiry(worlds, [query("e")], F, pro={"for"})
        self.assertFalse(I.is_antitone())
        for K in I.cells(I.actions):
            cert = I.certain(K)
            gap = I.gap_general(K)
            for D in subsets(sorted(cert)):
                worst = max(I.best_response(D, I.worlds[w]) - I.V(I.worlds[w]) for w in K)
                self.assertGreaterEqual(worst, gap)
            self.assertEqual(max(I.best_response(cert, I.worlds[w]) - I.V(I.worlds[w]) for w in K), gap)
        # the cell {w0, wd} (e false): docket ∅; in wd the advisor gains W from d's absence
        Kd = I.cell("wd", I.actions)
        self.assertEqual(Kd, frozenset({"w0", "wd"})); self.assertEqual(I.gap_general(Kd), W)
        # the cell {we, wde}: docket {e}; in wde, d is defeated by e: no gain
        Ke = I.cell("wde", I.actions)
        self.assertEqual(I.gap_general(Ke), Q(0))


class Countermodels(unittest.TestCase):

    def test_table(self):
        t = {c.name.split()[0]: c for c in cases()}
        r = t["1"].report(); self.assertEqual(r["obstruction"], Q(0)); self.assertEqual(r["minimax"], Q(0))
        r = t["2"].report(); self.assertEqual(r["obstruction"], Q(0)); self.assertEqual(r["minimax"], W)
        r = t["3"].report(); self.assertEqual(r["minimax"], Q(1, 16))
        r = t["5"].report(); self.assertEqual(r["minimax"], W); self.assertEqual(t["5"].alt.minimax(B=1), Q(0))
        r = t["6"].report(); self.assertEqual(r["minimax"], Q(0)); self.assertEqual(t["6"].inq.minimax(B=1), Q(0))
        r = t["7"].report(); self.assertEqual(r["minimax"], Q(0))
        r = t["9"].report(); self.assertEqual(r["obstruction"], Q(0)); self.assertEqual(r["minimax"], W)
        r = t["10"].report(); self.assertEqual(r["obstruction"], Q(0)); self.assertEqual(r["minimax"], W)
        r = t["11"].report(); self.assertEqual(r["obstruction"], W); self.assertEqual(r["minimax"], W)
        r = t["12"].report(); self.assertEqual(r["obstruction"], W); self.assertEqual(r["minimax"], W)
        r = t["13"].report(); self.assertEqual(r["minimax"], W); self.assertEqual(t["13"].inq.minimax(B=3), Q(0))
        r = t["14"].report(); self.assertEqual(r["minimax"], W); self.assertEqual(t["14"].inq.minimax(B=4), Q(0))
        r = t["15"].report(); self.assertEqual(r["minimax"], Q(0)); self.assertGreaterEqual(r["nonadaptive"], Q(1, 8))
        r = t["17"].report(); self.assertEqual(r["minimax"], W)
        r = t["18"].report(); self.assertEqual(r["obstruction"], Q(0))
        r = t["19"].report(); self.assertEqual(r["obstruction"], Q(0))

    def test_distractors_greedy_asks_the_heavy_reason_first(self):
        c = [c for c in cases() if c.name.startswith("3 ")][0]
        I = c.inq
        K, D = frozenset(I.worlds), frozenset()
        a = greedy_frontier(I, K, D, Q(1))
        self.assertEqual(a.name, "q:hi")
        D2, K2, spent = I.run(greedy_frontier, "hi", Q(1))
        self.assertEqual(D2, frozenset({"hi"})); self.assertEqual(I.residual(D2, "hi"), Q(0))

    def test_flooding_does_not_reach_the_frontier(self):
        c = [c for c in cases() if c.name.startswith("4 ")][0]
        I = c.inq
        K = frozenset(I.worlds)
        self.assertEqual(I.frontier(K, frozenset()), ["against"])
        self.assertEqual(I.minimax(B=1), Q(0))

    def test_defeater_obligation_appears_and_closes(self):
        c = [c for c in cases() if c.name.startswith("7 ")][0]
        I = c.inq
        K = frozenset(I.worlds)
        self.assertEqual(set(I.frontier(K, frozenset())), {"d", "against"})
        self.assertEqual(I.cond_adverse("d", frozenset()), W)
        D, K2, spent = I.run(greedy_frontier, "wda", Q(2))
        self.assertEqual(D, frozenset({"d", "against"})); self.assertEqual(I.residual(D, "wda"), Q(0))

    def test_needle_no_fractional_progress(self):
        c = [c for c in cases() if c.name.startswith("14 ")][0]
        I = c.inq
        n = len(I.actions)
        for b in range(n):
            self.assertEqual(I.minimax(B=b), W)
        self.assertEqual(I.minimax(B=n), Q(0))
        # the potential does not decrease in the worst case after any single query
        K, D = frozenset(I.worlds), frozenset()
        p0 = I.potential(K, D)
        for a in I.actions:
            worst = max(I.potential(I.cell(w, [a]), I.certain(I.cell(w, [a]))) for w in K)
            self.assertEqual(worst, p0)

    def test_adaptive_beats_nonadaptive(self):
        c = [c for c in cases() if c.name.startswith("15 ")][0]
        I = c.inq
        self.assertEqual(I.minimax(B=2), Q(0))
        self.assertGreaterEqual(I.nonadaptive(2), Q(1, 8))
        self.assertEqual(I.nonadaptive(3), Q(0))

    def test_stopping_control_violates_the_frontier(self):
        c = [c for c in cases() if c.name.startswith("16 ")][0]
        I = c.inq
        K = frozenset(I.worlds)
        self.assertNotEqual(I.frontier(K, frozenset()), [])
        self.assertEqual(max(I.residual(frozenset(), w) for w in K), W)


class Chain(unittest.TestCase):

    def test_actual_to_discovered_to_full_adds(self):
        """`Adv(actual, full) = Adv(actual, disc) + (U_disc − U_full)`, and each part is
        bounded by its own residual on the audited branch."""
        F = WeightedCount({"for": W, "a": -W, "b": -W, "c": -W})
        pro = frozenset({"for"})
        full = frozenset({"a", "b", "c"})
        disc = frozenset({"a", "b"})            # `c` undiscovered
        actual = frozenset({"a"})               # `b` discovered but unserved
        V = lambda S: F(pro | S)
        total = V(actual) - V(full)
        service = V(actual) - V(disc)
        discovery = V(disc) - V(full)
        self.assertEqual(total, service + discovery)
        self.assertEqual(service, W); self.assertEqual(discovery, W)
        # service bound: the second-pass instance; discovery bound: the conditional mass
        I = Instance([Reason("a", W, release=0), Reason("b", W, release=0)], T=1, cap=[1])
        best, _ = I.min_miss(); self.assertEqual(best, service)
        inq = Inquiry({"w": full, "w'": disc}, [], F, pro=pro)
        self.assertLessEqual(discovery, inq.cond_adverse("c", disc))


if __name__ == "__main__":
    unittest.main()
