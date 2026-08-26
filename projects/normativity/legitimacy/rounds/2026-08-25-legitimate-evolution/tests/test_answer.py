"""Answerability: required entry, controlled resolution.

The previous pass's conclusion was false on the whole resolve-after-transfer
family, its second premise was doing no work, and its coupling could not
represent an unauthorized act that generates a complaint. All three are here.
"""
from __future__ import annotations

import ast
import inspect
import unittest

import replay as rp
import office as of
import answer as an


def frame_and_duties(c, alpha=None):
    return of.build(c, alpha), of.duties(c)


def leaves(f, d, q, s, t=None):
    return tuple((of.duty_names(d, {n["ob"]}).pop(), n["verdict"])
                 for n in an.frontier(an.resolution(f, d, q, s, t)))


class TestTheOldConclusionWasFalse(unittest.TestCase):
    """§2. Four constitutions with clean premises that the old statement failed."""

    FAMILY = (("transfer then discharge", of.transfer_then_discharge),
              ("split then discharge both", of.split_then_discharge_both),
              ("merge then discharge", of.merge_then_discharge),
              ("reconverging split", of.reconverging_split))

    def test_the_premises_were_never_in_doubt(self):
        for name, make in self.FAMILY:
            with self.subTest(name):
                f, d = frame_and_duties(make())
                self.assertEqual(rp.violations(f), {})
                self.assertEqual(an.violations(f, d), {})

    def test_the_old_disjunction_fails_on_each(self):
        """Neither disjunct held: the root was not discharged and carried to
        nothing outstanding, because its descendants had been resolved."""
        for name, make in self.FAMILY:
            with self.subTest(name):
                f, d = frame_and_duties(make())
                end = len(f.trace)
                for q in d.base:
                    carried = [x for x in an.frontier(an.resolution(f, d, q, 0))
                               if x["verdict"] == an.OPEN]
                    discharged_root = any(
                        q in d.discharged(u) for u in rp.accepted(f))
                    self.assertFalse(discharged_root)
                    if name != "reconverging split":
                        self.assertEqual(carried, [])

    def test_the_corrected_statement_holds_on_all_of_them(self):
        for name, make in self.FAMILY:
            with self.subTest(name):
                f, d = frame_and_duties(make())
                self.assertEqual(an.thm_answerability_continuity(f, d), ())
                self.assertEqual(an.cor_no_silent_loss(f, d), ())


class TestTheWitnessObject(unittest.TestCase):
    """§3. A finite tree, and the smallest thing that handles every lifecycle."""

    def test_a_direct_discharge_is_a_leaf(self):
        f, d = frame_and_duties(of.answered())
        q = sorted(d.base)[0]
        self.assertEqual(leaves(f, d, q, 0), (("q:complaint", an.DISCHARGED),))

    def test_indefinite_persistence_is_a_leaf(self):
        f, d = frame_and_duties(of.transferred_once())
        q = sorted(d.base)[0]
        self.assertEqual(leaves(f, d, q, 0), (("q:referred", an.OPEN),))

    def test_a_chain_is_a_path(self):
        f, d = frame_and_duties(of.transfer_chain(3))
        q = sorted(d.base)[0]
        node = an.resolution(f, d, q, 0)
        depth = 0
        while node["children"]:
            node = node["children"][0]
            depth += 1
        self.assertEqual(depth, 3)

    def test_a_split_branches(self):
        f, d = frame_and_duties(of.split_then_discharge_one())
        q = sorted(d.base)[0]
        self.assertEqual(leaves(f, d, q, 0),
                         (("q:left", an.DISCHARGED), ("q:right", an.OPEN)))

    def test_a_merge_gives_each_parent_its_own_tree(self):
        f, d = frame_and_duties(of.merge_then_discharge())
        for q in sorted(d.base, key=str):
            self.assertEqual(leaves(f, d, q, 0),
                             (("q:joint", an.DISCHARGED),))

    def test_succession_is_a_dag_and_the_derivation_is_still_a_tree(self):
        """The reconverged obligation is two distinct leaves of one unfolding."""
        f, d = frame_and_duties(of.reconverging_split())
        q = sorted(d.base)[0]
        self.assertEqual(leaves(f, d, q, 0),
                         (("q:rejoined", an.OPEN), ("q:rejoined", an.OPEN)))

    def test_every_frontier_is_open_or_discharged(self):
        for c in of.ANSWER_CONSTITUTIONS:
            f, d = frame_and_duties(c)
            for q in an.ever_open(f, d):
                s = 0 if q.pos == an.BASE else q.pos + 1
                node = an.resolution(f, d, q, s)
                self.assertIsNotNone(node)
                for leaf in an.frontier(node):
                    self.assertIn(leaf["verdict"], (an.OPEN, an.DISCHARGED))


class TestA2WasNotLoadBearing(unittest.TestCase):
    """§4. Violate freshness, satisfy A1, and the theorem does not budge."""

    def build(self):
        f = of.build(of.Constitution(
            chartered=of.CHARTER,
            acts=(of._one(label="a"), of._one(label="b"), of._one(label="c"))))
        q0, q1 = an.Ob(an.BASE, 0), an.Ob(an.BASE, 1)
        d = an.Duties(
            base=frozenset({q0}),
            opens={0: frozenset({q1}), 1: frozenset({q0})},
            discharges={2: frozenset({q0})},
            transfers={0: {q0: frozenset({q1})}, 1: {q1: frozenset({q0})}})
        return f, d, q0

    def test_freshness_is_maximally_violated(self):
        f, d, _ = self.build()
        kinds = {v[0] for v in an.fresh_by_construction(f, d)}
        self.assertEqual(kinds, {"mis-positioned", "reopened"})

    def test_a1_still_holds(self):
        f, d, _ = self.build()
        self.assertEqual(an.a1_controlled_resolution(f, d), ())

    def test_and_so_does_the_theorem(self):
        f, d, q0 = self.build()
        self.assertEqual(an.thm_answerability_continuity(f, d), ())
        self.assertEqual(an.cor_no_silent_loss(f, d), ())
        node = an.resolution(f, d, q0, 0)
        self.assertIsNotNone(node)
        self.assertEqual(tuple(x["verdict"] for x in an.frontier(node)),
                         (an.DISCHARGED,))

    def test_termination_comes_from_the_interval_not_from_freshness(self):
        """An obligation is its own descendant here and the unfolding is finite."""
        f, d, q0 = self.build()
        node = an.resolution(f, d, q0, 0)
        self.assertEqual(node["ob"], q0)
        self.assertEqual(node["children"][0]["children"][0]["ob"], q0)

    def test_a2_is_not_a_premise(self):
        self.assertEqual([n for n, _ in an.PREMISES], ["D1", "A1"])
        self.assertEqual([n for n, _ in an.HYGIENE], ["fresh"])


class TestDue(unittest.TestCase):
    """§§5-7. Recognized-due-but-never-entered, and what it does not require."""

    def test_the_countermodel_the_old_package_passed(self):
        f, d = frame_and_duties(of.recognized_due_but_never_entered())
        self.assertEqual(rp.violations(f), {})
        self.assertEqual(rp.thm_grounded_replay(f), ())
        self.assertEqual(an.a1_controlled_resolution(f, d), ())
        self.assertEqual(an.cor_no_silent_loss(f, d), ())
        self.assertIn("D1", an.violations(f, d))
        self.assertNotEqual(an.cor_recognized_is_entered(f, d), ())

    def test_entering_it_is_enough(self):
        """It may then stay open forever. D1 requires entry, never closure."""
        f, d = frame_and_duties(of.recognized_due_and_entered())
        self.assertEqual(an.violations(f, d), {})
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)),
                         {"q:recognized"})

    def test_due_reads_the_state_so_it_can_arrive_later(self):
        f, d = frame_and_duties(of.due_arrives_later())
        self.assertEqual(d.owed(0), frozenset())
        self.assertNotEqual(d.owed(1), frozenset())
        self.assertEqual(an.violations(f, d), {})

    def test_d1_does_not_smuggle_in_coverage(self):
        """Nothing is represented, so nothing is owed, and this stays legitimate."""
        f, d = frame_and_duties(of.unobservant())
        self.assertEqual(d.due, {})
        self.assertEqual(an.violations(f, d), {})
        self.assertEqual(an.outstanding(f, d), frozenset())

    def test_d1_does_not_smuggle_in_progress(self):
        for make in (of.recognized_due_and_entered, of.due_arrives_later):
            f, d = frame_and_duties(make())
            self.assertEqual(an.violations(f, d), {})
            self.assertNotEqual(an.outstanding(f, d), frozenset())

    def test_high_regret_is_still_legitimate(self):
        f, d = frame_and_duties(of.high_regret())
        self.assertEqual(rp.violations(f), {})
        self.assertEqual(an.violations(f, d), {})


class TestStrictPreState(unittest.TestCase):
    """§12. A resolution cannot use what it creates to certify itself."""

    def test_open_and_close_in_one_act_is_refused(self):
        f, d = frame_and_duties(of.due_entered_then_closed_same_act())
        self.assertIn("A1", an.violations(f, d))
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)), {"q:instant"})

    def test_self_ratifying_resolution_is_refused(self):
        f, d = frame_and_duties(of.self_ratifying_resolution())
        self.assertIn("A1", an.violations(f, d))
        self.assertIn("q:successor", of.duty_names(d, an.outstanding(f, d)))

    def test_it_is_structural_not_a_clause(self):
        """Openings are unioned last, so the two cases need no premise of their own."""
        src = inspect.getsource(an.step)
        self.assertIn("| d.opened(t)", src)


class TestTheAsymmetricCoupling(unittest.TestCase):
    """§§9-11. One acceptance bit could not gate both channels."""

    def test_an_unentitled_act_discharges_nothing(self):
        f, d = frame_and_duties(of.rogue_discharge(), "alpha:audited")
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)), {"q:complaint"})
        self.assertEqual(
            of.duty_names(d, an.cor_discharge_requires_entitlement(f, d)),
            {"q:complaint"})

    def test_an_unentitled_act_may_still_open_one(self):
        f, d = frame_and_duties(of.unauthorized_act_opens_complaint())
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)),
                         {"q:complaint-about-alice"})
        self.assertEqual(
            of.duty_names(d, an.cor_opening_needs_no_entitlement(f, d)),
            {"q:complaint-about-alice"})

    def test_one_act_exercising_both_channels(self):
        """The decisive case: the opening lands and the discharge does not."""
        f, d = frame_and_duties(of.unauthorized_act_attempts_discharge())
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)),
                         {"q:complaint-about-alice", "q:standing"})
        self.assertEqual(
            of.duty_names(d, an.cor_discharge_requires_entitlement(f, d)),
            {"q:standing"})

    def test_a_rejection_on_provenance_behaves_the_same_way(self):
        """The reason for refusal does not change whether the fact is owed for."""
        f, d = frame_and_duties(of.rejected_edit_with_descriptive_consequences())
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(of.duty_names(d, an.outstanding(f, d)),
                         {"q:coercion-complaint"})

    def test_a_rejected_edit_still_removes_nothing(self):
        for make in (of.unauthorized_act_attempts_discharge, of.rogue_discharge):
            f, d = frame_and_duties(make(), "alpha:audited")
            for t in range(len(f.trace)):
                if t in rp.accepted(f):
                    continue
                before = an.outstanding(f, d, t)
                after = an.outstanding(f, d, t + 1)
                self.assertTrue(before <= after)

    def test_the_kernel_is_still_the_only_thing_consulted(self):
        tree = ast.parse(inspect.getsource(an))
        from_kernel = {n.attr for n in ast.walk(tree)
                       if isinstance(n, ast.Attribute)
                       and isinstance(n.value, ast.Name) and n.value.id == "rp"}
        self.assertEqual(from_kernel, {"accepted", "Frame", "BASE"})


class TestTheQuantitativeRepair(unittest.TestCase):
    """§§13-14. Narrow the claim, and fix the helper that overstated it."""

    def test_dilution_still_passes_every_structural_premise(self):
        for name, make in (("halving", lambda: of.transfer_chain(3, 0.5)),
                           ("to nothing", of.diluted_to_nothing),
                           ("split a quarter", lambda: of.split(0.25)),
                           ("merge to a half", lambda: of.merge(0.5))):
            with self.subTest(name):
                f, d = frame_and_duties(make())
                self.assertEqual(an.violations(f, d), {})
                self.assertEqual(an.thm_answerability_continuity(f, d), ())

    def test_per_parent_accounting_is_wrong_on_a_merge(self):
        f, d = frame_and_duties(of.merge_lenient())
        w = of.burden(d)
        self.assertEqual(an.diluting_edits(f, d, w), ())
        self.assertEqual(len(an.diluting_edits_total(f, d, w)), 1)
        self.assertEqual((an.potential_trace(f, d, w)[0],
                          an.potential_trace(f, d, w)[-1]), (2.0, 1.5))

    def test_fresh_openings_raise_the_potential_with_nothing_diluted(self):
        """The hypothesis the withdrawn version omitted."""
        f, d = frame_and_duties(of.high_regret())
        w = of.burden(d)
        self.assertEqual(an.diluting_edits_total(f, d, w), ())
        self.assertEqual(len(an.unheralded_openings(f, d)), 3)
        self.assertEqual(an.potential_trace(f, d, w), (0, 1.0, 2.0, 3.0))

    def test_the_conditional_holds_where_both_hypotheses_do(self):
        for make in (lambda: of.split(0.5), lambda: of.merge(2.0),
                     of.transferred_once, of.transfer_then_discharge):
            f, d = frame_and_duties(make())
            w = of.burden(d)
            self.assertEqual(an.diluting_edits_total(f, d, w), ())
            self.assertEqual(an.unheralded_openings(f, d), ())
            trace = an.potential_trace(f, d, w)
            self.assertTrue(all(b <= a + 1e-9 for a, b in zip(trace, trace[1:])))
            self.assertTrue(
                an.thm_conserving_transfers_give_monotone_potential(f, d, w))

    def test_the_withdrawn_version_is_gone(self):
        self.assertFalse(hasattr(an, "thm_no_dilution_gives_monotone_potential"))


class TestTheKernelIsUntouched(unittest.TestCase):
    def test_the_kernel_does_not_import_the_second_replay(self):
        tree = ast.parse(inspect.getsource(rp))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported |= {n.name.split(".")[0] for n in node.names}
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertNotIn("answer", imported)

    def test_the_kernel_has_no_obligation_notion(self):
        for word in ("duty", "obligation", "outstanding", "discharge", "owed",
                     "due"):
            self.assertNotIn(word, rp.Frame.__dataclass_fields__)
            self.assertNotIn(word, rp.Edit.__dataclass_fields__)

    def test_everything_holds_on_every_answerability_constitution(self):
        for c in of.ANSWER_CONSTITUTIONS:
            f, d = frame_and_duties(c)
            self.assertEqual(rp.violations(f), {})
            self.assertEqual(rp.thm_grounded_replay(f), ())
            self.assertEqual(an.violations(f, d), {})
            self.assertEqual(an.thm_answerability_continuity(f, d), ())
            self.assertEqual(an.cor_no_silent_loss(f, d), ())
            self.assertEqual(an.cor_recognized_is_entered(f, d), ())

    def test_each_premise_has_a_countermodel(self):
        for c in of.D1_BROKEN:
            f, d = frame_and_duties(c)
            self.assertIn("D1", an.violations(f, d))
        for c in of.A1_BROKEN:
            f, d = frame_and_duties(c)
            self.assertIn("A1", an.violations(f, d))

    def test_a1_failure_breaks_the_theorem(self):
        for c in of.A1_BROKEN:
            f, d = frame_and_duties(c)
            self.assertNotEqual(an.cor_no_silent_loss(f, d), ())

    def test_two_semantic_parameters_not_four(self):
        doc = inspect.getdoc(an)
        self.assertIn("Due", doc)
        self.assertIn("Resolve", doc)
        for gone in ("Disposes", "Transfers   "):
            self.assertNotIn(f"\n{gone}", doc)


if __name__ == "__main__":
    unittest.main()
