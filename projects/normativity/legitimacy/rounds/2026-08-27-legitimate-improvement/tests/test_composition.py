"""Theorems B and C, and the countermodel suite that decides them."""
from __future__ import annotations

import unittest

import answer as an
import replay as rp

import cases as cm
import challenge as ch
import evidence as ev
import consumers as co
import regret as rg
import surface as sf


class TestFrozenLEIsUntouched(unittest.TestCase):
    """The hard boundary. Nothing here edits or weakens the frozen package."""

    def test_every_countermodel_satisfies_the_frozen_package(self):
        for make in cm.ALL:
            tr = make()
            with self.subTest(tr.name):
                self.assertEqual(tr.challenges.le_premises(), {})
                self.assertEqual(tr.challenges.le_conformance(), {})
                self.assertEqual(tr.challenges.le_resolution(), ())
                self.assertEqual(tr.challenges.le_grounded(), ())

    def test_the_composition_only_reads_the_frozen_interfaces(self):
        import ast
        import inspect
        tree = ast.parse(inspect.getsource(ch))
        used = {n.attr for n in ast.walk(tree) if isinstance(n, ast.Attribute)
                and isinstance(n.value, ast.Name) and n.value.id in ("an", "rp")}
        self.assertTrue(used <= {"Duties", "Ob", "Frame", "Edit", "Occ", "BASE",
                                 "outstanding", "incurred", "newly_due",
                                 "accepted", "violations", "nonconformance",
                                 "thm_answerability_resolution",
                                 "thm_grounded_replay"}, used)

    def test_the_learning_kernel_names_no_legitimacy(self):
        import ast
        import inspect
        tree = ast.parse(inspect.getsource(rg))
        names = {n.id for n in ast.walk(tree) if isinstance(n, ast.Name)}
        for word in ("Due", "Resolve", "Permit", "an", "rp", "outstanding"):
            self.assertNotIn(word, names)


class TestTheTrichotomy(unittest.TestCase):
    """Theorem C: LIVE / CONTESTED / SETTLED, and whether ESCAPED is empty."""

    def test_the_cells_partition_the_diagnosed_mass(self):
        for make in cm.ALL:
            tr = make()
            with self.subTest(tr.name):
                self.assertTrue(sf.cor_partition(tr.accounting))

    def test_only_undemonstrated_withdrawals_escape(self):
        """Both escapes are exactly the cases where the improvement was never
        demonstrated -- which is the theorem's own hypothesis, not a leak."""
        escaping = {make().name for make in cm.ALL if make().escaped()}
        self.assertEqual(escaping, {"CM2 preemptive de-licensing",
                                    "CM16 uptake regret, no demonstration"})
        for make in cm.ALL:
            tr = make()
            if tr.escaped():
                self.assertFalse(ev.independence_report(
                    tr.learner, tr.evidence, cm.NAME)["demonstrated"], tr.name)

    def test_retirement_after_evidence_leaves_a_challenge(self):
        """CM1. The repair goes; a claim stays."""
        tr = cm.cm1_reactive_delicensing()
        s = tr.split()
        self.assertGreater(s[sf.CONTESTED], 100)
        self.assertEqual(s[sf.ESCAPED], 0.0)
        self.assertEqual(tr.escaped(), ())

    def test_one_retirement_covers_an_unbounded_later_stream(self):
        """CM3, and the thing §2 warned counting events could not do.

        340 diagnosed occasions after a single retirement, none of them escaped:
        they are covered because the claim is *outstanding at each of them*, not
        because each minted one.
        """
        tr = cm.cm3_post_retirement_continuation()
        s = tr.split()
        self.assertGreater(s[sf.CONTESTED], 300)
        self.assertEqual(s[sf.ESCAPED], 0.0)
        opened = sum(len(v) for v in tr.challenges.duties.opens.values())
        self.assertEqual(opened, 1)

    def test_the_contested_cell_is_not_bounded(self):
        """And the theorem does not pretend otherwise."""
        short = cm.cm3_post_retirement_continuation(horizon=200)
        long = cm.cm3_post_retirement_continuation(horizon=800)
        self.assertGreater(long.split()[sf.CONTESTED],
                           3 * short.split()[sf.CONTESTED])
        self.assertEqual(long.escaped(), ())

    def test_a_settled_challenge_moves_the_mass_to_settled(self):
        """CM7, and it must not require the settlement to be any good."""
        tr = cm.cm7_trivial_resolve()
        s = tr.split()
        self.assertGreater(s[sf.SETTLED], 200)
        self.assertEqual(s[sf.ESCAPED], 0.0)

    def test_outstanding_forever_is_permitted(self):
        """CM8. Qualitative LE allows it; so does this."""
        tr = cm.cm8_outstanding_forever()
        self.assertGreater(tr.split()[sf.CONTESTED], 300)
        self.assertEqual(tr.challenges.le_premises(), {})

    def test_menu_and_designation_shedding_are_caught(self):
        """CM6 and CM6b: the same abstraction covers all three components."""
        for make in (cm.cm6_menu_shedding, cm.cm6b_designation_shedding):
            tr = make()
            with self.subTest(tr.name):
                self.assertGreater(tr.split()[sf.CONTESTED], 100)
                self.assertEqual(tr.escaped(), ())

    def test_recurrence_opens_a_second_claim(self):
        """CM11. Two retirements, two evidence episodes, two claims."""
        tr = cm.cm11_recurrence()
        opened = sum(len(v) for v in tr.challenges.duties.opens.values())
        self.assertEqual(opened, 2)
        self.assertEqual(tr.escaped(), ())


class TestTheEscape(unittest.TestCase):
    """CM2, the one that gets away, and what would be needed to catch it."""

    def test_preemptive_delicensing_escapes(self):
        tr = cm.cm2_preemptive_delicensing()
        self.assertGreater(tr.split()[sf.ESCAPED], 150)
        self.assertNotEqual(tr.escaped(), ())

    def test_and_it_escapes_legitimately(self):
        """Nothing in the frozen package objects, which is the point."""
        tr = cm.cm2_preemptive_delicensing()
        self.assertEqual(tr.challenges.le_premises(), {})
        self.assertEqual(tr.challenges.le_conformance(), {})
        self.assertEqual(tr.challenges.le_grounded(), ())

    def test_the_escape_is_exactly_the_absence_of_evidence(self):
        """Retire late enough for the evidence to exist and it is caught."""
        early = cm.cm2_preemptive_delicensing(retire_at=4)
        late = cm.cm2_preemptive_delicensing(retire_at=60)
        self.assertGreater(early.split()[sf.ESCAPED], 150)
        self.assertEqual(late.escaped(), ())

    def test_the_escaped_cell_is_representable(self):
        """A trichotomy that could not express its own failure would prove
        nothing, which is the trap the frozen round twice fell into."""
        self.assertIn(sf.ESCAPED, cm.cm2_preemptive_delicensing().split())


class TestTheSurfaceIsNotAnOracle(unittest.TestCase):
    """CM12. The surface must be a function of the legitimate state."""

    def test_a_refused_retirement_that_still_changes_the_surface_is_caught(self):
        tr = cm.cm12_unentitled_retirement()
        bad = ch.coherence_violations(tr.surface, cm.RID, tr.challenges.frame,
                                      tr.challenges.retire_labels)
        self.assertTrue(bad)
        self.assertEqual(bad[0][1], 60)

    def test_an_accepted_retirement_is_coherent(self):
        tr = cm.cm1_reactive_delicensing()
        self.assertEqual(ch.coherence_violations(
            tr.surface, cm.RID, tr.challenges.frame, {}), ())


class TestTheLiveBound(unittest.TestCase):
    """Theorem B, and the hypothesis that makes it mean anything."""

    def test_a_surgical_repair_empties_the_live_cell_by_construction(self):
        """Stronger than the bound, and it is why no fixture exercises it.

        `pi(BAD) = pi(BAD) M(BAD,BAD)`, and a surgical repair with any weight
        makes `M(BAD,BAD) < 1`, so the diagnosed action gets exactly zero
        stationary mass however the losses fall.
        """
        for make in cm.ALL:
            tr = make()
            with self.subTest(tr.name):
                if not getattr(tr, "runs_the_algorithm", True):
                    continue          # a stubborn process; see TestTheLiveBound
                self.assertLess(tr.split()[sf.LIVE], 1e-9)

    def test_it_holds_even_when_the_repair_sometimes_loses(self):
        tr = cm.cm13_surgical_empties_the_live_cell()
        self.assertLess(tr.split()[sf.LIVE], 1e-9)
        self.assertEqual(rg.thm_a_repair_regret(tr.learner), ())
        live_plays = [p for o, p, _w, _i in tr.learner.plays
                      if tr.surface.live(cm.RID, o.tag)]
        self.assertTrue(all(p[cm.BAD] < 1e-12 for p in live_plays))

    def test_the_algebra(self):
        self.assertAlmostEqual(sf.thm_b_live_bound(0.0, 12.0, 3.0, 0.5), 30.0)
        self.assertEqual(sf.thm_b_live_bound(0.0, 12.0, 3.0, 0.0), float("inf"))

    def test_a_process_that_declines_to_learn_has_no_bound(self):
        """The hypothesis is not decorative: without it there is no theorem.

        A stubborn process is outside every learning result, so `Adv` runs away
        from its bound and Theorem B yields nothing to compose with.
        """
        occ = cm.occasions(300)
        surf = sf.Surface(cm.ALWAYS, cm.ALWAYS, cm.ONE, lambda t: "e0")
        L = rg.Learner((rg.Comparator(cm.NAME, surf.selector(cm.RID),
                                      cm.repair_fn),
                        rg.Comparator("id", lambda _p, _o: 1.0,
                                      lambda _p, _o, a: a)))
        for o in occ:
            L.observe(o, dict(cm.BASE_POLICY))
        self.assertGreater(L.adv[cm.NAME], L.bound(cm.NAME))
        self.assertNotEqual(rg.thm_a_repair_regret(L), ())


class TestConsumers(unittest.TestCase):

    def test_answerable_stalling(self):
        tr = co.stalling()
        self.assertGreater(tr.split()[sf.CONTESTED], 100)
        self.assertEqual(tr.escaped(), ())
        self.assertEqual(tr.challenges.le_premises(), {})

    def test_stalling_without_a_retirement_has_nothing_to_report(self):
        tr = co.stalling(retire_at=None)
        self.assertEqual(tr.split()[sf.ESCAPED], 0.0)
        self.assertEqual(tr.split()[sf.CONTESTED], 0.0)

    def test_override_of_a_correction(self):
        tr = co.override()
        self.assertGreater(tr.split()[sf.CONTESTED], 100)
        self.assertEqual(tr.escaped(), ())

    def test_the_delay_anchor_exists_but_is_not_used(self):
        """The delayed theorem is not claimed; the field is present for it."""
        self.assertEqual(co.override().tau, 0)

    def test_the_negative_consumer_has_no_force(self):
        """A success condition, not a failure."""
        tr = co.meta_improvement()
        s = tr.split()
        self.assertEqual(sum(s.values()), 0.0)
        self.assertEqual(tr.escaped(), ())
        self.assertEqual(sum(len(v) for v in tr.challenges.duties.opens.values()),
                         0)


class TestCM5AndCM10AreBoundaries(unittest.TestCase):
    """Two cases the theorem is silent on, deliberately."""

    def test_evaluator_shedding_is_invisible(self):
        """CM5. The repair stays live and simply stops being better.

        Nothing distinguishes *the repair stopped helping* from *we changed the
        evaluator so it stopped looking like it helped*. That needs evaluator
        independence, which this round does not have and does not claim.
        """
        tr = cm.cm5_evaluator_shedding()
        s = tr.split()
        self.assertEqual(s[sf.CONTESTED], 0.0)
        self.assertEqual(s[sf.ESCAPED], 0.0)
        self.assertEqual(sum(len(v) for v in tr.challenges.duties.opens.values()),
                         0)

    def test_a_tiny_improvement_grounds_no_challenge(self):
        """CM9. Correct: it is not a demonstrated improvement."""
        tr = cm.cm9_tiny_mass()
        self.assertEqual(sum(len(v) for v in tr.challenges.duties.opens.values()),
                         0)

    def test_a_meta_level_repair_grounds_no_challenge(self):
        tr = cm.cm10_delayed_meta()
        self.assertEqual(sum(len(v) for v in tr.challenges.duties.opens.values()),
                         0)


if __name__ == "__main__":
    unittest.main()
