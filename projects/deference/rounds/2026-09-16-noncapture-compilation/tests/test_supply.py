"""Second pass: sensitivity certificates, the service obstruction, the exact dual for unit
costs, the hybrid bound, the decomposition, and the bridge to the steering model."""

import random
import unittest
from fractions import Fraction as Q

from src.supply import Reason, Instance, unit_schedules_exist, general_schedule_exists
from src.sensitivity import (WeightedCount, Defeat, Redundant, sensitivity, adverse,
                             telescoping_holds, adverse_holds, omission_gain, subsets)
from src.attacks_second_pass import cases, W
from src.model import (A, T3, REASON, World, Program, entry, canon, N_full, audit, advantage)


def random_unit_instance(rng, n, T):
    reasons = [Reason(f"r{i}", Q(rng.randint(0, 4), 4), release=rng.randint(0, T - 1)) for i in range(n)]
    cap = [rng.randint(0, 1) for _ in range(T)]
    return Instance(reasons, T, cap)


class Sensitivity(unittest.TestCase):

    def test_telescoping_and_adverse_hold_for_every_program(self):
        progs = [WeightedCount({"a": W, "b": -W, "c": -Q(1, 8)}),
                 Defeat({"for": W, "against": -W}, {"against": {"d"}}),
                 Redundant([(-W, {"a1", "a2"}), (W, {"p"})])]
        for F in progs:
            self.assertTrue(telescoping_holds(F))
            self.assertTrue(adverse_holds(F))

    def test_weighted_count_certificates_are_the_weights(self):
        F = WeightedCount({"a": W, "b": -W, "c": Q(0)}, base=Q(1, 2))
        self.assertEqual(sensitivity(F, "a"), W); self.assertEqual(sensitivity(F, "b"), W)
        self.assertEqual(adverse(F, "a"), Q(0)); self.assertEqual(adverse(F, "b"), W)
        self.assertEqual(adverse(F, "c"), Q(0))

    def test_defeat_moves_sensitivity_to_the_defeater(self):
        F = Defeat({"for": W, "against": -W}, {"against": {"d"}})
        self.assertEqual(sensitivity(F, "d"), W)        # removing d restores the counterreason
        self.assertEqual(adverse(F, "d"), Q(0))         # but adding d never hurts the advisor
        self.assertEqual(adverse(F, "against"), W)
        # the counterreason's adverse mass is conditional: with d present, omitting it gains nothing
        self.assertEqual(omission_gain(F, {"for", "d"}, {"against"}), Q(0))
        self.assertEqual(omission_gain(F, {"for"}, {"against"}), W)

    def test_redundancy_makes_the_mass_bound_loose(self):
        F = Redundant([(-W, {"a1", "a2"})])
        self.assertEqual(omission_gain(F, set(), {"a1", "a2"}), W)
        self.assertEqual(adverse(F, "a1") + adverse(F, "a2"), 2 * W)
        self.assertLessEqual(omission_gain(F, set(), {"a1", "a2"}), adverse(F, "a1") + adverse(F, "a2"))


class ServiceObstruction(unittest.TestCase):

    def test_cut_condition_matches_exhaustive_unit_schedules(self):
        rng = random.Random(7)
        for _ in range(150):
            I = random_unit_instance(rng, rng.randint(1, 4), rng.randint(1, 4))
            S = {r.id for r in I.servable()}
            self.assertEqual(I.feasible(S), unit_schedules_exist(I, S))

    def test_cut_condition_matches_exhaustive_general_schedules(self):
        rng = random.Random(11)
        for _ in range(80):
            T = rng.randint(1, 3)
            reasons = [Reason(f"r{i}", W, cost=rng.randint(1, 2), release=rng.randint(0, T - 1))
                       for i in range(rng.randint(1, 3))]
            I = Instance(reasons, T, [rng.randint(0, 2) for _ in range(T)])
            S = {r.id for r in I.servable()}
            self.assertEqual(I.feasible(S), general_schedule_exists(I, S))

    def test_cut_excess_is_the_least_unserved_count(self):
        rng = random.Random(3)
        for _ in range(100):
            I = random_unit_instance(rng, rng.randint(1, 5), rng.randint(1, 4))
            for r in I.reasons:
                r.weight = Q(1)
            best, _ = I.min_miss()
            self.assertEqual(best, I.cut_excess())

    def test_layer_formula_and_greedy_are_exact_for_unit_costs(self):
        rng = random.Random(5)
        for _ in range(150):
            I = random_unit_instance(rng, rng.randint(1, 5), rng.randint(1, 4))
            best, _ = I.min_miss()
            self.assertEqual(best, I.min_miss_formula())
            self.assertEqual(best, I.miss(I.greedy()))

    def test_online_greedy_is_offline_optimal(self):
        rng = random.Random(9)
        for _ in range(150):
            I = random_unit_instance(rng, rng.randint(1, 5), rng.randint(1, 4))
            best, _ = I.min_miss()
            self.assertEqual(I.miss(I.online_greedy()), best)

    def test_greedy_is_not_exact_for_general_costs(self):
        c = [c for c in cases() if c.name.startswith("17 ")][0]
        I = c.inst
        best, S = I.min_miss()
        self.assertEqual(best, Q(3, 8)); self.assertEqual(S, {"a", "b"})
        self.assertEqual(I.miss(I.greedy()), Q(1, 2))
        self.assertLess(best, I.miss(I.greedy()))


class Countermodels(unittest.TestCase):

    def test_reports(self):
        table = {c.name.split()[0]: c for c in cases()}
        r = table["1"].report(); self.assertEqual(r["cut_excess"], 1); self.assertEqual(r["min_miss"], W)
        r = table["2"].report(); self.assertEqual(r["min_miss"], Q(1, 8)); self.assertEqual(r["best_set"], {"hi"})
        r = table["4"].report(); self.assertEqual(r["min_miss"], W)
        r = table["5"].report(); self.assertFalse(r["cut_ok"]); self.assertEqual(table["5"].inst.Cap(0), 4)
        r = table["10"].report(); self.assertEqual(r["cut_excess"], 2); self.assertEqual(r["min_miss"], 2 * W)
        r = table["14"].report(); self.assertEqual(r["decomposition"]["discovery"], W)
        self.assertEqual(r["decomposition"]["service"], Q(0))
        r = table["15"].report(); self.assertEqual(r["decomposition"]["scope"], W)
        self.assertEqual(r["min_miss"], Q(0))

    def test_protected_high_vs_unprotected_low(self):
        c = [c for c in cases() if c.name.startswith("3 ")][0]
        I = c.inst
        # serve the protected reason: audit on, charge the low mass
        self.assertEqual(I.miss({"hi"}), Q(1, 8))
        self.assertTrue(all(r.id in {"hi"} for r in I.reasons if r.protected))
        # serve the low one: the protected reason is missing, the audit is off
        self.assertFalse(all(r.id in {"lo"} for r in I.reasons if r.protected))

    def test_authentication_trade(self):
        c = [c for c in cases() if c.name.startswith("6 ")][0]
        best, S = c.inst.min_miss()
        self.assertEqual(best, W)
        d = c.alt.decompose({"r", "q"})
        self.assertEqual(d["service"], Q(0)); self.assertEqual(d["authentication"], 2 * W)

    def test_correlated_discovery_is_policy_dependent(self):
        c = [c for c in cases() if c.name.startswith("9 ")][0]
        best_a, _ = c.inst.min_miss(); best_b, _ = c.alt.min_miss()
        self.assertEqual(c.inst.decompose(set())["discovery"], Q(1, 2))
        self.assertEqual(best_b, Q(0))

    def test_flooding_is_harmless_under_weighted_service(self):
        c = [c for c in cases() if c.name.startswith("11 ")][0]
        best, S = c.inst.min_miss()
        self.assertEqual(best, Q(0)); self.assertIn("against", S)
        # FIFO on the flooded docket would serve noise1, noise2 and miss the counterreason
        fifo = ["noise1", "noise2", "against"][:sum(c.inst.cap)]
        self.assertEqual(c.inst.miss(fifo), W)

    def test_cost_influence_breaks_the_cut(self):
        c = [c for c in cases() if c.name.startswith("12 ")][0]
        self.assertTrue(c.alt.cut_ok()); self.assertFalse(c.inst.cut_ok())

    def test_two_suppliers_add(self):
        c = [c for c in cases() if c.name.startswith("13 ")][0]
        self.assertTrue(c.inst.cut_ok()); self.assertTrue(c.alt.cut_ok())

    def test_realizable_versus_ideal_regret(self):
        c = [c for c in cases() if c.name.startswith("16 ")][0]
        best, S = c.inst.min_miss()
        self.assertEqual(c.inst.realizable_regret(S), Q(0))
        self.assertEqual(c.inst.ideal_regret(S), Q(1, 2))


class Hybrid(unittest.TestCase):

    def test_hybrid_bound_and_the_scope_tradeoff(self):
        """Protecting a reason converts its missing mass into void; the charged mass is the
        unprotected missing adverse mass.  Protect exactly what the cut condition serves."""
        F = WeightedCount({"for": W, "hi": -Q(1, 2), "lo": -Q(1, 8)})
        full = {"for", "hi", "lo"}
        for present in [{"for", "hi"}, {"for", "lo"}, {"for"}]:
            missing = full - present
            for prot in [set(), {"hi"}, {"hi", "lo"}]:
                audit_on = not (missing & prot)
                gain = omission_gain(F, present, missing)
                charged = sum(adverse(F, r) for r in missing - prot)
                if audit_on:
                    self.assertLessEqual(gain, charged)
                # the void case charges nothing (the advisor's security is 0)
        # optimal protection with one slot: protect `hi` (servable), charge `lo`
        I = Instance([Reason("hi", Q(1, 2), release=0, protected=True), Reason("lo", Q(1, 8), release=0)],
                     T=1, cap=[1])
        self.assertTrue(I.cut_ok({"hi"}))
        self.assertFalse(I.cut_ok({"hi", "lo"}))


class Bridge(unittest.TestCase):

    def test_supply_bound_is_the_steering_content_term(self):
        """Served set → actual trace; the steering advantage against N_full equals the
        omission gain and is bounded by the missed adverse mass."""
        w = World({"for": True, "against": True, "p_against": True, "noise": True}, protected=("p_against",))
        p = Program({"for": W, "against": -W, "p_against": -W, "noise": Q(0)})
        I = Instance([Reason("against", W, release=0), Reason("p_against", W, release=0, protected=True),
                      Reason("noise", Q(0), release=0)], T=2, cap=[1, 1])
        best, S = I.min_miss()
        self.assertEqual(best, Q(0))
        # one slot only: the supplier serves the protected reason, misses `against`
        I1 = Instance(I.reasons, T=1, cap=[1])
        best1, _ = I1.min_miss()
        self.assertEqual(best1, W)
        S1 = {"p_against"}                      # protect what you serve: the audit stays on
        self.assertTrue(I1.feasible(S1)); self.assertEqual(I1.miss(S1), best1)
        trace = (entry(A, REASON, "for"),) + tuple(entry(T3, REASON, r) for r in sorted(S1))
        self.assertTrue(audit(trace, w))
        self.assertEqual(advantage(p, trace, N_full(trace, w), w), best1)
        F = lambda c: p.value(tuple(entry(T3, REASON, r) for r in sorted(c)), w)
        self.assertEqual(omission_gain(F, canon(trace, w), w.true_declared() - canon(trace, w)), best1)


if __name__ == "__main__":
    unittest.main()
