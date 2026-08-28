"""The PR60 prosecution pass.

Every test here exists because something was wrong or unclear, and each says
which. A test that only re-encodes the desired theorem into its own fixture is
not doing work; these are the ones that would have caught the bugs.
"""
from __future__ import annotations

import math
import unittest

import cases as cm
import evidence as ev
import regret as rg
import surface as sf


def ident(_p, _o, a):
    return a


class TestTheFixedPoint(unittest.TestCase):
    """Prevents: shipping power iteration justified by stochasticity alone."""

    PERIODIC = ("A", "B", "C")

    def kernel(self):
        def cyc(_p, _o, a):
            return {"A": "B", "B": "A", "C": "A"}[a]
        occ = rg.Occasion(self.PERIODIC, {a: 0.0 for a in self.PERIODIC}, tag=0)
        comps = (rg.Comparator("cyc", lambda _p, _o: 1.0, cyc),
                 rg.Comparator("asleep", lambda _p, _o: 0.0, ident))
        q = {"cyc": 0.5, "asleep": 0.5}
        sel = {"cyc": 1.0, "asleep": 0.0}
        return occ, comps, q, sel

    def test_power_iteration_would_have_oscillated_forever(self):
        """The kernel `A->B, B->A, C->A` has period 2. Powers never converge."""
        occ, comps, q, sel = self.kernel()
        rows = rg.kernel(occ, comps, [], q, sel)
        p = {a: 1.0 / 3 for a in self.PERIODIC}
        seen = []
        for _ in range(6):
            nxt = {a: 0.0 for a in self.PERIODIC}
            for a in self.PERIODIC:
                for b, w in rows[a].items():
                    nxt[b] += p[a] * w
            p = nxt
            seen.append(round(p["A"], 6))
        self.assertEqual(len(set(seen)), 2)               # a 2-cycle, forever
        self.assertGreater(rg.stationary_residual(p, rows, self.PERIODIC), 0.5)

    def test_the_solver_returns_an_exact_stationary_distribution(self):
        occ, comps, q, sel = self.kernel()
        rows = rg.kernel(occ, comps, [], q, sel)
        p = rg._fixed_point(occ, comps, [], q, sel)
        self.assertLess(rg.stationary_residual(p, rows, self.PERIODIC), 1e-12)
        self.assertAlmostEqual(p["A"], 0.5)
        self.assertAlmostEqual(p["C"], 0.0)

    def test_it_is_exact_when_the_stationary_distribution_is_not_unique(self):
        """Two absorbing classes: any point of the simplex satisfies the
        equation, and the reduction needs only that it is one of them."""
        occ = rg.Occasion(("GOOD", "BAD", "C"),
                          {"GOOD": 0.0, "BAD": 1.0, "C": 0.5}, tag=0)
        comps = (rg.Comparator("r", lambda _p, _o: 1.0, cm.repair_fn),
                 rg.Comparator("id", lambda _p, _o: 1.0, ident))
        q, sel = {"r": 0.5, "id": 0.5}, {"r": 1.0, "id": 1.0}
        rows = rg.kernel(occ, comps, [], q, sel)
        p = rg._fixed_point(occ, comps, [], q, sel)
        self.assertLess(rg.stationary_residual(p, rows, occ.menu), 1e-12)
        self.assertEqual(p["BAD"], 0.0)

    def test_every_occasion_in_every_countermodel_is_exactly_stationary(self):
        for make in cm.ALL:
            tr = make()
            if not getattr(tr, "runs_the_algorithm", True):
                continue          # a stubborn process does not play the fixed point
            with self.subTest(tr.name):
                for occ, p, _own, _i in tr.learner.plays:
                    sel = {c.name: float(c.select([], occ))
                           for c in tr.learner.comparators}
                    if sum(sel.values()) == 0:
                        continue
                    q = tr.learner.inner.distribution(
                        [c.name for c in tr.learner.comparators])
                    rows = rg.kernel(occ, tr.learner.comparators, [], q, sel)
                    if rows is None:
                        continue
                    self.assertLess(
                        rg.stationary_residual(p, rows, occ.menu), 1e-6)


class TestTheAdaNormalHedgeBound(unittest.TestCase):
    """Prevents: calling a numerically convenient expression the theorem."""

    def test_B_is_global_and_prior_weighted(self):
        anh = rg.AdaNormalHedge(prior=lambda i: 0.5)
        anh.R, anh.C = {"i": 0.0, "j": 0.0}, {"i": 1.0, "j": 10000.0}
        local = 1.0 + 1.5 * (1.0 + math.log(1.0 + anh.C["i"]))
        self.assertAlmostEqual(
            anh.B(), 1.0 + 1.5 * sum(0.5 * (1.0 + math.log(1.0 + c))
                                     for c in anh.C.values()))
        self.assertGreater(anh.B(), 2.5 * local / 1.0 - local)   # they differ

    def test_the_old_local_B_understated_the_bound(self):
        anh = rg.AdaNormalHedge(prior=lambda i: 0.5)
        anh.R, anh.C = {"i": 0.0, "j": 0.0}, {"i": 1.0, "j": 10000.0}
        local_b = 1.0 + 1.5 * (1.0 + math.log(1.0 + anh.C["i"]))
        old = math.sqrt(3.0 * anh.C["i"] * (math.log(2.0) + math.log(local_b)
                                            + math.log(1.0 + math.log(2))))
        self.assertLess(old, anh.bound("i", 2))

    def test_it_matches_the_paper_for_a_point_competitor(self):
        anh = rg.AdaNormalHedge(prior=lambda i: 0.25)
        anh.R, anh.C = {"i": 0.0}, {"i": 9.0}
        want = math.sqrt(3.0 * 9.0 * (math.log(4.0) + math.log(anh.B())
                                      + math.log(1.0 + math.log(2))))
        self.assertAlmostEqual(anh.bound("i", 2), want)

    def test_B_grows_with_another_experts_regret(self):
        """The dependence the local version dropped."""
        a = rg.AdaNormalHedge(prior=lambda i: 0.5)
        a.R, a.C = {"i": 0.0, "j": 0.0}, {"i": 1.0, "j": 1.0}
        b = rg.AdaNormalHedge(prior=lambda i: 0.5)
        b.R, b.C = {"i": 0.0, "j": 0.0}, {"i": 1.0, "j": 5000.0}
        self.assertGreater(b.bound("i", 2), a.bound("i", 2))


class TestTheSurgicalClaim(unittest.TestCase):
    """Prevents: `pi(d) = pi(d) M(d,d)`, which drops the inflow term."""

    def test_inflow_defeats_it(self):
        d = cm.cm14_inflow_defeats_surgical()
        self.assertAlmostEqual(d["diagnosed_mass"], 1.0 / 3, places=4)
        self.assertFalse(d["inflow_free"])
        self.assertFalse(d["corollary_applies"])
        self.assertLess(d["residual"], 1e-12)

    def test_without_inflow_the_conclusion_holds(self):
        for make in cm.ALL:
            tr = make()
            if not getattr(tr, "runs_the_algorithm", True):
                continue
            with self.subTest(tr.name):
                for occ, p, _own, _i in tr.learner.plays[:5]:
                    sel = {c.name: float(c.select([], occ))
                           for c in tr.learner.comparators}
                    if sum(sel.values()) == 0:
                        continue
                    q = tr.learner.inner.distribution(
                        [c.name for c in tr.learner.comparators])
                    rows = rg.kernel(occ, tr.learner.comparators, [], q, sel)
                    if rows and rg.cor_surgical_empties_diagnosed(
                            rows, occ.menu, cm.BAD):
                        self.assertLess(p[cm.BAD], 1e-9)

    def test_and_theorem_B_now_has_something_to_bound(self):
        """The inflow discovery makes a positive live defect constructible under
        a genuine no-regret process, which no fixture had before."""
        d = cm.cm18_live_defect_under_no_regret()
        self.assertGreater(d["d_live"], 0.5)
        self.assertEqual(d["violations"], ())
        self.assertLess(d["uptake"], d["bound"])
        self.assertLess(d["d_live"], d["thm_b"])


class TestEvidenceIsNotUptakeRegret(unittest.TestCase):
    """The pass's main conceptual repair. Prevents: reading one as the other."""

    def test_evidence_accrues_while_uptake_regret_is_zero(self):
        """CM15. The process adopted the repair; the improvement is still
        demonstrated, because evidence is measured against the baseline."""
        tr = cm.cm15_evidence_without_uptake_regret()
        r = ev.independence_report(tr.learner, tr.evidence, cm.NAME)
        self.assertAlmostEqual(r["uptake"], 0.0, places=9)
        self.assertGreater(r["evidence"], 40.0)
        self.assertTrue(r["demonstrated"])
        self.assertGreater(tr.split()[sf.CONTESTED], 100)

    def test_uptake_regret_without_a_demonstration_grounds_nothing(self):
        """CM16. Advantage left unused, threshold never reached, no challenge."""
        tr = cm.cm16_uptake_regret_without_demonstration()
        r = ev.independence_report(tr.learner, tr.evidence, cm.NAME)
        self.assertGreater(r["uptake"], 0.0)
        self.assertFalse(r["demonstrated"])
        self.assertEqual(sum(len(v) for v in tr.challenges.duties.opens.values()),
                         0)

    def test_the_challenge_never_consults_uptake_regret(self):
        import ast
        import inspect
        import challenge as ch
        tree = ast.parse(inspect.getsource(ch))
        names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)}
        names |= {n.attr for n in ast.walk(tree) if isinstance(n, ast.Attribute)}
        for word in ("adv", "bound", "regret", "uptake", "mass"):
            self.assertNotIn(word, names, word)

    def test_they_are_the_same_functional_on_different_distributions(self):
        occ = rg.Occasion((cm.GOOD, cm.BAD), {cm.GOOD: 0.2, cm.BAD: 0.8}, tag=0)
        comp = rg.Comparator("r", lambda _p, _o: 1.0, cm.repair_fn)
        adopted = {cm.GOOD: 1.0, cm.BAD: 0.0}
        base = {cm.GOOD: 0.0, cm.BAD: 1.0}
        self.assertAlmostEqual(rg.advantage(occ, [], comp, adopted), 0.0)
        self.assertAlmostEqual(rg.advantage(occ, [], comp, base), 0.6)


class TestTheBaselineIsNotFrozen(unittest.TestCase):
    """Prevents: treating BASE_POLICY as a settled semantics."""

    def test_two_baselines_give_two_verdicts_on_one_trace(self):
        a, b = cm.cm17_baseline_changes_the_verdict()
        self.assertGreater(a.split()[sf.CONTESTED], 100)
        self.assertEqual(a.split()[sf.ESCAPED], 0.0)
        self.assertEqual(b.split()[sf.CONTESTED], 0.0)
        self.assertGreater(b.split()[sf.ESCAPED], 100)

    def test_a_hindsight_baseline_is_caught(self):
        """What stops a consumer picking, after the fact, whatever reference
        makes the repair look best."""
        def peek(_prefix, occ):
            worst = max(occ.loss, key=occ.loss.get)
            return {a: (1.0 if a == worst else 0.0) for a in occ.menu}
        occ = [rg.Occasion(("GOOD", "BAD"), {"GOOD": 0.2, "BAD": 0.8}, tag=t)
               for t in range(20)]
        L = rg.Learner((rg.Comparator("r", lambda _p, _o: 1.0, cm.repair_fn),))
        bad = rg.predictability_violations(
            L, occ, lambda o: {a: 1.0 - v for a, v in o.loss.items()},
            baseline=peek)
        self.assertTrue(any(k == "baseline" for k, _w, _t in bad))

    def test_an_honest_baseline_passes(self):
        occ = [rg.Occasion(("GOOD", "BAD"), {"GOOD": 0.2, "BAD": 0.8}, tag=t)
               for t in range(20)]
        L = rg.Learner((rg.Comparator("r", lambda _p, _o: 1.0, cm.repair_fn),))
        self.assertEqual(rg.predictability_violations(
            L, occ, lambda o: {a: 1.0 - v for a, v in o.loss.items()},
            baseline=ev.fixed(cm.BASE_POLICY)), ())


class TestTheBoundariesStayOutside(unittest.TestCase):

    def test_pre_demonstration_withdrawal_escapes(self):
        tr = cm.cm2_preemptive_delicensing()
        self.assertFalse(ev.independence_report(
            tr.learner, tr.evidence, cm.NAME)["demonstrated"])
        self.assertGreater(tr.split()[sf.ESCAPED], 150)

    def test_evaluator_change_is_not_a_retirement(self):
        """CM5. The repair stays live, evidence simply stops accruing, and the
        theorem is silent -- it is not caught by the retirement mechanism and
        the round does not pretend otherwise."""
        tr = cm.cm5_evaluator_shedding()
        self.assertEqual(sum(len(v) for v in tr.challenges.duties.opens.values()),
                         0)
        self.assertEqual(tr.split()[sf.CONTESTED], 0.0)
        self.assertEqual(tr.split()[sf.ESCAPED], 0.0)

    def test_withdrawal_after_demonstration_is_contested(self):
        tr = cm.cm1_reactive_delicensing()
        self.assertGreater(tr.split()[sf.CONTESTED], 100)

    def test_trivial_resolve_settles(self):
        tr = cm.cm7_trivial_resolve()
        self.assertGreater(tr.split()[sf.SETTLED], 200)


if __name__ == "__main__":
    unittest.main()
