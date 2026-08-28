"""SR1-SR12 and CV1-CV8. The question is whether S1 is derived or assumed."""
from __future__ import annotations

import ast
import inspect
import unittest

import cases as c
import coverage as cv
import schedule as sc


class TestS1IsDerived(unittest.TestCase):
    """The round's primary question."""

    def test_countably_many_challenges_fit_a_unit_budget(self):
        """SR2. The core feasibility fixture, and it is not close.

        Twenty-four challenges, each with opportunity 1 at every position, a
        single unit of service per position, and every one of them served
        positively throughout.
        """
        w, served = c.sr2_countably_many()
        self.assertEqual(sc.budget_violations(w, served), ())
        peak = max(sum(served.get((x.cid, t), 0.0) for x in w.challenges)
                   for t in range(w.horizon))
        self.assertLessEqual(peak, w.budget + 1e-12)
        for ch in w.challenges:
            self.assertGreater(sc.service_mass(w, served, ch), 0.0, ch.cid)

    def test_the_theorem_inequality_holds(self):
        """`U >= floor * O` is the theorem; this is what a fixture can check."""
        for name, make in c.SERVICE:
            w, served = make()
            if not served or w.atomic:
                continue          # the atomic case has its own theorem
            with self.subTest(name):
                for cid, v in sc.thm_s1_from_positive_share(w, served).items():
                    self.assertTrue(v["holds"], (name, cid, v))

    def test_every_share_is_strictly_positive(self):
        w, served = c.sr2_countably_many()
        for ch in w.challenges:
            self.assertGreater(w.share(ch, 0), 0.0)

    def test_a_late_registration_still_gets_a_positive_share(self):
        """SR3."""
        w, served = c.sr3_late_registration()
        late = next(x for x in w.challenges if x.cid == "late")
        self.assertGreater(w.share(late, 199), 0.0)
        self.assertGreater(sc.service_mass(w, served, late), 0.0)

    def test_zero_service_is_the_failure_case(self):
        """SR1. Unbounded opportunity, nothing served."""
        w, served = c.sr1_zero_service()
        self.assertNotEqual(sc.s1_non_starvation(w, served), ())

    def test_finite_opportunity_demands_nothing(self):
        """SR4. Infinitely many occasions is not unbounded opportunity mass."""
        w, served = c.sr4_finite_opportunity()
        ch = w.challenges[0]
        self.assertLess(sc.opportunity_mass(w, ch), 3.0)
        self.assertEqual(sc.s1_non_starvation(w, served), ())


class TestTheAtomicCase(unittest.TestCase):
    """Service need not be divisible -- but the scheduler must be adaptive."""

    def test_a_fixed_dovetailer_is_starved_by_adversarial_timing(self):
        """SR8. Opportunity is offered only when the cycle is elsewhere."""
        w, served = c.sr8_adversarial_timing_fixed_cycle()
        c2 = next(x for x in w.challenges if x.cid == "c2")
        self.assertGreater(sc.opportunity_mass(w, c2), 50.0)
        self.assertEqual(sc.service_mass(w, served, c2), 0.0)
        self.assertNotEqual(sc.s1_non_starvation(w, served), ())

    def test_least_recently_served_is_not(self):
        w, served = c.sr8_adversarial_timing_adaptive()
        c2 = next(x for x in w.challenges if x.cid == "c2")
        self.assertGreater(sc.service_mass(w, served, c2), 50.0)
        self.assertEqual(sc.s1_non_starvation(w, served), ())

    def test_the_two_differ_only_in_the_scheduler(self):
        a, _ = c.sr8_adversarial_timing_fixed_cycle()
        b, _ = c.sr8_adversarial_timing_adaptive()
        self.assertEqual([x.cid for x in a.challenges],
                         [x.cid for x in b.challenges])
        for t in range(a.horizon):
            for x in a.challenges:
                self.assertEqual(a.opp(x, t), b.opp(x, t))

    def test_every_challenge_is_served_recurrently(self):
        w, served = c.sr8_adversarial_timing_adaptive()
        rep = sc.thm_s1_from_least_recently_served(w, served)
        for cid, v in rep.items():
            self.assertGreater(v["served_at"], 10, cid)
            self.assertLess(v["max_gap"], 10, cid)


class TestWhatMustPersist(unittest.TestCase):
    """W1: a positive floor, not a pinned value. The round's second finding."""

    def test_geometric_shrinkage_destroys_the_floor(self):
        """SR6. Never zero, never defeated, never transferred, and fatal."""
        w, served = c.sr6_weight_revision()
        bad = sc.w1_positive_floor(w)
        self.assertTrue(bad)
        self.assertEqual(bad[0][0], "c1")
        self.assertLess(bad[0][1], 1e-30)

    def test_and_a_finite_horizon_does_not_show_it_as_starvation(self):
        """Why `W1` is the invariant to state rather than `S1` alone.

        On any finite prefix some service has been delivered, so the finite
        proxy for S1 is satisfied while the mechanism guaranteeing it has
        already been dismantled.
        """
        w, served = c.sr6_weight_revision()
        self.assertEqual(sc.s1_non_starvation(w, served), ())
        self.assertNotEqual(sc.w1_positive_floor(w), ())

    def test_reprioritisation_is_still_allowed(self):
        """W1 forbids approaching zero, not falling. A share may drop by any
        finite factor any number of times."""
        def halved_once(cid, t):
            return 0.5 if t < 100 else 0.25
        w = c.world([sc.Chal("c1", 0)], c.ALWAYS, entitle=halved_once)
        self.assertEqual(sc.w1_positive_floor(w), ())

    def test_an_explicit_transfer_is_legitimate(self):
        """SR7."""
        w, served = c.sr7_explicit_transfer()
        self.assertEqual(sc.w1_positive_floor(w), ())
        self.assertEqual(sc.s1_non_starvation(w, served), ())

    def test_closing_a_challenge_ends_the_obligation(self):
        """SR5 and SR11."""
        for name, make in (("SR5", c.sr5_legitimate_defeat),
                           ("SR11", c.sr11_closed_frees_resources)):
            w, served = make()
            with self.subTest(name):
                self.assertEqual(sc.s1_non_starvation(w, served), ())
                closed = [x for x in w.challenges if x.closed is not None]
                for ch in closed:
                    self.assertEqual(
                        sum(served.get((ch.cid, t), 0.0)
                            for t in range(ch.closed, w.horizon)), 0.0)


class TestWhatSurvivesButIsNotSolved(unittest.TestCase):

    def test_spam_degrades_throughput_without_breaking_S1(self):
        """SR9. A priority problem, and the round classifies it as one."""
        w, served = c.sr9_challenge_spam()
        real = next(x for x in w.challenges if x.cid == "real")
        self.assertEqual(sc.s1_non_starvation(w, served), ())
        self.assertGreater(w.share(real, 0), 0.0)
        self.assertLess(w.share(real, 0), 1e-5)

    def test_toggled_defeat_evades_service_and_is_the_old_boundary(self):
        """SR10. The challenge is never open *and* serviceable at once.

        No premise here is violated. This is the same shape as the round below's
        pre-existing self-sealing rule, and no ad hoc condition is added to
        reject it.
        """
        w, served = c.sr10_toggled_defeat()
        self.assertEqual(sc.s1_non_starvation(w, served), ())
        self.assertEqual(sc.w1_positive_floor(w), ())
        for t in range(w.horizon):
            ch = w.challenges[0]
            self.assertFalse(ch.open_at(t) and w.opp(ch, t) > 0)

    def test_service_is_not_progress(self):
        """SR12. Unbounded service, and nothing is concluded."""
        w, served = c.sr12_service_without_progress()
        self.assertEqual(sc.s1_non_starvation(w, served), ())
        self.assertGreater(sc.service_mass(w, served, w.challenges[0]), 50.0)
        src = inspect.getsource(sc)
        for word in ("promote", "progress", "converge"):
            self.assertNotIn(f"def {word}", src)


class TestTheLiabilityShape(unittest.TestCase):
    """Whether the bridge is mathematically real or only analogical."""

    def test_S1_holds_while_the_debt_diverges(self):
        """The precise reason they are not the same shape.

        A liability theorem bounds accumulated exposure. `S1` requires
        accumulated service to *diverge*. Positive-share service satisfies S1 and
        leaves debt `(1-w)O`, which grows without bound.
        """
        w, served = c.sr12_service_without_progress()
        d = sc.debt_diverges_while_s1_holds(w, served)["c1"]
        self.assertEqual(sc.s1_non_starvation(w, served), ())
        self.assertGreater(d["debt"], 50.0)

    def test_bounded_debt_would_be_strictly_stronger(self):
        """`U >= O - D`, so bounded `D` implies S1 -- and is not what the
        feasible construction delivers."""
        w, served = c.sr2_countably_many()
        for ch in w.challenges[:4]:
            o = sc.opportunity_mass(w, ch)
            u = sc.service_mass(w, served, ch)
            d = sc.starvation_debt(w, served, ch)
            self.assertAlmostEqual(u, o - d, places=6)


class TestCoverage(unittest.TestCase):
    """The world-to-representation interface, kept separate."""

    def test_full_coverage(self):
        self.assertTrue(cv.qualitative_coverage(c.cv1_full()))

    def test_infinite_latent_finite_represented_fails(self):
        self.assertFalse(cv.qualitative_coverage(
            c.cv2_infinite_latent_finite_represented()))

    def test_qualitative_and_fractional_come_apart(self):
        """CV4. Both masses unbounded; the represented fraction tends to zero.

        This is why the stronger form is offered and not adopted: no consumer in
        this round needs it.
        """
        s = c.cv4_sparse_but_infinite()
        self.assertTrue(cv.qualitative_coverage(s))
        self.assertFalse(cv.fractional_coverage(s, 0.5))

    def test_no_internal_probe_reads_the_latent_stream(self):
        tree = ast.parse(inspect.getsource(cv))
        fn = next(n for n in ast.walk(tree)
                  if isinstance(n, ast.FunctionDef) and n.name == "composed")
        names = {x.attr for x in ast.walk(fn) if isinstance(x, ast.Attribute)}
        self.assertIn("Zhat", names)
        self.assertIn("Z", names)      # reported, and only for the diagnosis

    def test_a_class_is_always_named(self):
        """Coverage is consumer-relative; no fixture leaves the class implicit."""
        for _name, make in c.COVERAGE:
            self.assertTrue(make().klass)


class TestTheSeparationPair(unittest.TestCase):
    """The two failures are independent, in both directions."""

    def test_coverage_fails_while_service_is_perfect(self):
        s, served = c.cv5_registered_evidence_hidden()
        got = cv.composed(s, served)
        self.assertEqual(got["verdict"], "coverage fails")

    def test_service_fails_while_coverage_is_perfect(self):
        s, served = c.cv6_represented_but_ignored()
        got = cv.composed(s, served)
        self.assertEqual(got["verdict"], "service fails")

    def test_the_two_gates_are_different(self):
        """CV8. Opportunity coverage perfect, criticism never formulated."""
        s = c.cv8_evidence_without_criticism()
        self.assertTrue(cv.qualitative_coverage(s))
        self.assertEqual(s.cid, "unformulated")


class TestTheBoundaryObservation(unittest.TestCase):

    def test_same_represented_history_different_coverage(self):
        a, b = c.cv3_indistinguishable()
        probes = [lambda s: round(s.Zhat(), 9),
                  lambda s: tuple(round(s.zhat(t), 9) for t in range(20))]
        got = cv.obs_coverage_is_not_internal(a, b, probes)
        self.assertTrue(got["same_represented_history"])
        self.assertTrue(got["coverage_differs"])
        self.assertTrue(got["probes_agree"])

    def test_it_is_stated_as_an_observation(self):
        doc = inspect.getdoc(cv.obs_coverage_is_not_internal)
        self.assertIn("not", doc)
        self.assertIn("impossibility theorem", doc)


class TestScopeDiscipline(unittest.TestCase):

    def test_no_closure_theorem_is_added(self):
        for mod in (sc, cv):
            src = inspect.getsource(mod)
            for word in ("import replay", "import answer", "Duties", "A1 "):
                self.assertNotIn(word, src, (mod.__name__, word))

    def test_service_is_not_defined_as_evidence(self):
        src = inspect.getsource(sc)
        self.assertNotIn("evidence", src)


if __name__ == "__main__":
    unittest.main()
