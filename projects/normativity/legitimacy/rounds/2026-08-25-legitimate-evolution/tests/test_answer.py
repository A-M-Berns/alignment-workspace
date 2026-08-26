"""Answerability: incurred versus outstanding, Due as activation, A1 alone.

The previous pass shipped D1 as a structural premise. It is not one: the
induction never consults it, and a process can satisfy the theorem while ignoring
what its own semantics recognized as owed. That separation is
`TestD1IsNotATheoremPremise`, and it is the point of this pass.
"""
from __future__ import annotations

import ast
import inspect
import unittest

import replay as rp
import office as of
import answer as an


def fd(c, alpha=None):
    return of.build(c, alpha), of.duties(c)


def nm(d, obs):
    return set(of.duty_names(d, obs))


def leaves(f, d, q, t=None):
    node = an.resolution(f, d, q, an.born(q), t)
    return tuple((of.duty_names(d, {n["ob"]}).pop(), n["verdict"])
                 for n in an.frontier(node))


class TestTheTenLifecycles(unittest.TestCase):
    """§1. Every branch accounted for, with no existential escape."""

    CASES = (("direct discharge", of.answered),
             ("transfer", of.transferred_once),
             ("transfer chain", lambda: of.transfer_chain(3)),
             ("transfer then discharge", of.transfer_then_discharge),
             ("split", lambda: of.split(0.5)),
             ("split then discharge one", of.split_then_discharge_one),
             ("split then discharge all", of.split_then_discharge_both),
             ("merge", lambda: of.merge(2.0)),
             ("merge then discharge", of.merge_then_discharge),
             ("indefinite persistence", of.high_regret))

    def test_each_one_holds(self):
        for name, make in self.CASES:
            with self.subTest(name):
                f, d = fd(make())
                self.assertEqual(an.violations(f, d), {})
                self.assertEqual(an.thm_answerability_resolution(f, d), ())
                self.assertEqual(an.cor_no_silent_loss(f, d), ())

    def test_the_theorem_quantifies_over_incurred(self):
        """A claim incurred and resolved between two observations still counts."""
        f, d = fd(of.due_and_resolved_in_one_step())
        self.assertEqual(an.outstanding(f, d), frozenset())
        self.assertEqual(nm(d, an.incurred(f, d)), {"q:instant"})
        self.assertEqual(leaves(f, d, sorted(an.incurred(f, d))[0]),
                         (("q:instant", an.DISCHARGED),))

    def test_every_branch_must_be_accounted_for(self):
        """One lost branch kills the root's derivation; the survivor does not
        rescue it."""
        f, d = fd(of.split_one_branch_lost())
        self.assertIn("A1", an.violations(f, d))
        bad = {q for q, _ in an.thm_answerability_resolution(f, d)}
        self.assertEqual(nm(d, bad), {"q:claim", "q:lost"})
        self.assertEqual(nm(d, an.outstanding(f, d)), {"q:kept"})

    def test_a_merge_gives_each_parent_a_derivation(self):
        f, d = fd(of.merge_then_discharge())
        for q in sorted(d.base, key=str):
            self.assertEqual(leaves(f, d, q), (("q:joint", an.DISCHARGED),))

    def test_a_dag_unfolds_to_a_tree(self):
        f, d = fd(of.reconverging_split())
        q = sorted(d.base)[0]
        self.assertEqual(leaves(f, d, q),
                         (("q:rejoined", an.OPEN), ("q:rejoined", an.OPEN)))


class TestTheCarryLaw(unittest.TestCase):
    """§3. Successors need not be fresh; they must be outstanding after the step."""

    def test_carrying_into_an_existing_claim_is_legitimate(self):
        f, d = fd(of.carry_into_existing_claim())
        self.assertEqual(an.violations(f, d), {})
        self.assertEqual(nm(d, an.outstanding(f, d)), {"q:major"})
        self.assertEqual(leaves(f, d, sorted(d.base, key=str)[1]),
                         (("q:major", an.OPEN),))

    def test_two_claims_may_share_a_preexisting_successor(self):
        f, d = fd(of.carry_into_shared_successor())
        self.assertEqual(an.violations(f, d), {})
        self.assertEqual(nm(d, an.outstanding(f, d)), {"q:omnibus"})

    def test_carrying_into_something_the_same_event_resolves_is_refused(self):
        f, d = fd(of.carry_into_something_resolved())
        self.assertIn("A1", an.violations(f, d))
        kinds = {v[0] for v in an.a1_controlled_resolution(f, d)}
        self.assertIn("successor not outstanding after the step", kinds)

    def test_carrying_to_nothing_is_refused(self):
        f, d = fd(of.transfer_to_nowhere())
        self.assertIn("A1", an.violations(f, d))
        self.assertNotEqual(an.cor_no_silent_loss(f, d), ())

    def test_freshness_is_consulted_nowhere(self):
        """A2 is gone, not demoted-but-still-checked."""
        self.assertFalse([n for n in dir(an) if "fresh" in n])
        self.assertFalse([n for n, _ in an.PREMISES + an.CONFORMANCE
                          if n == "A2"])
        for fn in (an.a1_controlled_resolution, an.resolution,
                   an.thm_answerability_resolution):
            self.assertNotIn("q.pos", inspect.getsource(fn))


class TestActivationEpisodes(unittest.TestCase):
    """§§3-6, 15. `Due` is a level; what obliges is its rising edge."""

    def test_persistent_activation_does_not_reopen(self):
        """§4. The claim stays active across its own discharge and stays closed."""
        f, d = fd(of.resolved_stays_resolved())
        self.assertEqual({t: set(d.active(t)) for t in range(len(f.trace))},
                         {t: {"q:claim"} for t in range(4)})
        self.assertEqual({t: set(an.newly_due(d, t)) for t in range(len(f.trace))
                          if an.newly_due(d, t)}, {0: {"q:claim"}})
        self.assertEqual(an.nonconformance(f, d), {})
        self.assertEqual(an.outstanding(f, d), frozenset())

    def test_recurrence_incurs_a_second_occurrence(self):
        """§5. Two episodes of one claim kind, and memoizing forbids this."""
        f, d = fd(of.recurrence())
        self.assertEqual([t for t in range(len(f.trace)) if an.newly_due(d, t)],
                         [0, 3])
        self.assertEqual(nm(d, an.incurred(f, d)), {"q:lapse-1", "q:lapse-2"})
        self.assertEqual({d.key_of(q) for q in an.incurred(f, d)}, {"q:lapse"})
        self.assertEqual(nm(d, an.outstanding(f, d)), {"q:lapse-2"})
        self.assertEqual(an.nonconformance(f, d), {})

    def test_content_difference_would_have_missed_it(self):
        """§15. Set difference on content gives one episode where there are two."""
        f, d = fd(of.recurrence())
        ever = {d.key_of(q) for q in an.incurred(f, d)}
        self.assertEqual(len(ever), 1)
        self.assertEqual(len([t for t in range(len(f.trace))
                              if an.newly_due(d, t)]), 2)

    def test_an_ignored_second_episode_is_caught(self):
        f, d = fd(of.recurrence_ignored())
        self.assertIn("D1", an.nonconformance(f, d))
        self.assertEqual([v[1] for v in an.nonconformance(f, d)["D1"]], [3])

    def test_a_falling_edge_resolves_nothing(self):
        """What stops being owed is decided by Resolve, not by Due going quiet."""
        f, d = fd(of.falling_edge_is_not_resolution())
        self.assertEqual(set(an.newly_due(d, 0)), {"q:claim"})
        self.assertEqual(d.active(1), frozenset())
        self.assertEqual(nm(d, an.outstanding(f, d)), {"q:claim"})

    def test_an_old_reason_may_become_newly_due(self):
        """§6. Nothing arrives; the normative context changed."""
        f, d = fd(of.old_reason_becomes_newly_due())
        self.assertEqual(an.newly_due(d, 0), frozenset())
        self.assertEqual(set(an.newly_due(d, 2)), {"q:under-new-standard"})
        self.assertEqual(an.nonconformance(f, d), {})

    def test_radical_change_can_activate_a_longstanding_reason(self):
        """§27 case 13. The successor constitution owes for the old practice."""
        f, d = fd(of.refoundation_activates_an_old_reason())
        self.assertEqual(set(an.newly_due(d, 2)),
                         {"q:account-for-the-practice"})
        self.assertEqual(rp.violations(f), {})
        self.assertEqual(an.nonconformance(f, d), {})

    def test_several_reasons_may_jointly_activate_one_claim(self):
        """§12. No support sets on the obligation: Due reads the state."""
        f, d = fd(of.joint_reasons_one_claim())
        self.assertEqual(an.newly_due(d, 0), frozenset())
        self.assertEqual(an.newly_due(d, 1), frozenset())
        self.assertEqual(set(an.newly_due(d, 2)), {"q:joint-claim"})

    def test_one_reason_may_activate_several_claims(self):
        """§13. No special machinery either."""
        f, d = fd(of.one_reason_many_claims())
        self.assertEqual(set(an.newly_due(d, 0)), {"q:explain", "q:repair"})

    def test_the_edge_never_consults_answerability(self):
        """§16. Bookkeeping over Due's own output, not a normative loop."""
        src = inspect.getsource(an.newly_due)
        for word in ("outstanding", "incurred", "Incurred", "opened"):
            self.assertNotIn(word, src.split('"""')[2], word)

    def test_same_step_activation_and_resolution(self):
        """§8. Incurred, resolved, never outstanding, and still covered."""
        f, d = fd(of.due_and_resolved_in_one_step())
        self.assertEqual(set(an.newly_due(d, 0)), {"q:instant"})
        self.assertEqual(an.outstanding(f, d, 1), frozenset())
        self.assertEqual(an.nonconformance(f, d), {})
        self.assertEqual(an.cor_recognized_is_resolved(f, d), ())

    def test_same_step_activation_with_an_unauthorized_resolution(self):
        """§27 case 8. Incurrence lands; the resolution does not."""
        f, d = fd(of.same_step_activation_unauthorized_resolution())
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(nm(d, an.incurred(f, d)), {"q:revealed"})
        self.assertEqual(nm(d, an.outstanding(f, d)), {"q:revealed"})

    def test_but_same_step_is_not_a_loophole(self):
        f, d = fd(of.due_and_ignored_in_one_step())
        self.assertIn("D1", an.nonconformance(f, d))
        self.assertNotEqual(an.cor_recognized_is_resolved(f, d), ())

    def test_due_is_not_coverage(self):
        """§10. Nothing represented, nothing active, still legitimate."""
        f, d = fd(of.unobservant())
        self.assertEqual(d.due, {})
        self.assertEqual(an.violations(f, d), {})
        self.assertEqual(an.nonconformance(f, d), {})


class TestD1IsAnInclusion(unittest.TestCase):
    """§18. Due is not the only legitimate genesis for a claim."""

    def test_succession_incurs_a_claim_Due_never_activates(self):
        f, d = fd(of.succession_incurs_without_due())
        self.assertEqual(d.due, {})
        self.assertEqual(nm(d, an.incurred(f, d)), {"q:original", "q:successor"})
        self.assertEqual(an.nonconformance(f, d), {})

    def test_so_equality_would_refuse_ordinary_succession(self):
        f, d = fd(of.succession_incurs_without_due())
        newly = frozenset().union(frozenset(),
                                  *[an.newly_due(d, t) for t in range(len(f.trace))])
        self.assertEqual(newly, frozenset())
        self.assertNotEqual(an.incurred(f, d), frozenset())


class TestD1IsNotATheoremPremise(unittest.TestCase):
    """§19. The pass's central finding: D1 lives at a different layer."""

    def test_the_theorem_holds_while_the_process_ignores_what_it_recognized(self):
        for make in (of.recognized_due_but_never_entered,
                     of.due_and_ignored_in_one_step):
            with self.subTest(make.__name__):
                f, d = fd(make())
                self.assertEqual(an.violations(f, d), {})
                self.assertEqual(an.thm_answerability_resolution(f, d), ())
                self.assertEqual(an.cor_no_silent_loss(f, d), ())
                self.assertIn("D1", an.nonconformance(f, d))

    def test_the_induction_never_consults_it(self):
        src = inspect.getsource(an.thm_answerability_resolution) \
            + inspect.getsource(an.resolution) + inspect.getsource(an.step)
        for word in ("due", "d1_", "activated", "newly_due"):
            self.assertNotIn(word, src, word)

    def test_it_is_a_conformance_check_not_a_premise(self):
        self.assertEqual([n for n, _ in an.PREMISES], ["A1"])
        self.assertEqual([n for n, _ in an.CONFORMANCE], ["D1"])

    def test_it_is_still_representable_as_failing(self):
        """§19's trap: a conformance condition hidden in the type checks nothing."""
        self.assertTrue(of.D1_BROKEN)
        for c in of.D1_BROKEN:
            f, d = fd(c)
            self.assertIn("D1", an.nonconformance(f, d))

    def test_the_package_is_the_composition(self):
        """Dropping D1 loses the conclusion, not the induction."""
        f, d = fd(of.recognized_due_but_never_entered())
        self.assertEqual(an.thm_answerability_resolution(f, d), ())
        self.assertNotEqual(an.cor_recognized_is_resolved(f, d), ())

    def test_the_two_failures_are_different(self):
        """§18. Dropping A1 loses a claim; dropping D1 never takes one on."""
        f, d = fd(of.silently_deleted())
        self.assertIn("A1", an.violations(f, d))
        self.assertEqual(an.nonconformance(f, d), {})
        g, e = fd(of.recognized_due_but_never_entered())
        self.assertEqual(an.violations(g, e), {})
        self.assertIn("D1", an.nonconformance(g, e))


class TestTheVerifierTest(unittest.TestCase):
    """§22. Can a consumer tell an omitted claim from a valid record?"""

    def test_the_bad_case_has_perfect_continuity_on_every_recorded_claim(self):
        """Which is why no structural check can catch it."""
        for c in of.D1_BROKEN:
            with self.subTest(c.acts[-1].label):
                f, d = fd(c)
                self.assertEqual(rp.thm_grounded_replay(f), ())
                self.assertEqual(an.violations(f, d), {})
                self.assertEqual(an.thm_answerability_resolution(f, d), ())
                self.assertEqual(an.cor_no_silent_loss(f, d), ())
                self.assertIn("D1", an.nonconformance(f, d))

    def test_and_recomputing_the_activation_catches_it(self):
        """The verifier's whole job: replay Due over the represented state and
        compare its rising edges against what the record incurred."""
        for c in of.D1_BROKEN:
            with self.subTest(c.acts[-1].label):
                f, d = fd(c)
                reported = [(t, k) for _, t, k in an.nonconformance(f, d)["D1"]]
                self.assertTrue(reported)
                for t, k in reported:
                    self.assertIn(k, an.newly_due(d, t))
                    self.assertNotIn(k, {d.key_of(q) for q in d.opened(t)})

    def test_a_conforming_record_recomputes_clean(self):
        for c in of.ACTIVATION_CONSTITUTIONS:
            f, d = fd(c)
            self.assertEqual(an.nonconformance(f, d), {})
            self.assertEqual(an.cor_recognized_is_resolved(f, d), ())

    def test_what_the_verifier_needs(self):
        """`Due` is a parameter, exactly as `Permit` is. The record carries the
        represented state; the semantics has to be agreed out of band."""
        f, d = fd(of.recurrence())
        self.assertIsNotNone(d.due)
        blind = an.Duties(d.base, d.opens, d.discharges, d.transfers, d.drops,
                          {}, d.key)
        self.assertEqual(an.nonconformance(f, blind), {})
        self.assertEqual(an.violations(f, blind), an.violations(f, d))


class TestTheThreeGates(unittest.TestCase):
    """§§11-13. Permit, Due and Resolve act independently."""

    def test_an_amendment_changes_standing_and_no_claim(self):
        f, d = fd(of.amendment_without_answerability())
        self.assertEqual(rp.accepted(f), (0,))
        self.assertEqual(an.incurred(f, d), frozenset())

    def test_a_response_resolves_a_claim_and_changes_no_standing(self):
        f, d = fd(of.response_without_normative_change())
        self.assertEqual(rp.live(f), f.base)
        self.assertEqual(nm(d, an.incurred(f, d)), {"q:claim"})
        self.assertEqual(an.outstanding(f, d), frozenset())

    def test_represented_evidence_incurs_a_claim_with_no_norm_event(self):
        f, d = fd(of.evidence_opens_without_norm_event())
        self.assertEqual(set(an.newly_due(d, 0)), {"q:from-evidence"})
        self.assertEqual(nm(d, an.outstanding(f, d)), {"q:from-evidence"})

    def test_an_unauthorized_act_incurs_a_claim(self):
        f, d = fd(of.unauthorized_act_opens_complaint())
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(nm(d, an.cor_opening_needs_no_entitlement(f, d)),
                         {"q:complaint-about-alice"})

    def test_and_cannot_resolve_one(self):
        f, d = fd(of.unauthorized_act_attempts_discharge())
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(nm(d, an.outstanding(f, d)),
                         {"q:complaint-about-alice", "q:standing"})
        self.assertEqual(nm(d, an.cor_discharge_requires_entitlement(f, d)),
                         {"q:standing"})

    def test_self_authorizing_does_not_license_a_resolution(self):
        """§13. Resolve reads the legitimate pre-state, not what the act creates."""
        f, d = fd(of.self_authorize_then_discharge())
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(nm(d, an.outstanding(f, d)), {"q:safety-claim"})
        self.assertEqual(nm(d, an.cor_discharge_requires_entitlement(f, d)),
                         {"q:safety-claim"})

    def test_the_kernel_is_still_the_only_thing_consulted(self):
        tree = ast.parse(inspect.getsource(an))
        from_kernel = {n.attr for n in ast.walk(tree)
                       if isinstance(n, ast.Attribute)
                       and isinstance(n.value, ast.Name) and n.value.id == "rp"}
        self.assertEqual(from_kernel, {"accepted", "Frame", "BASE"})


class TestTheBoundary(unittest.TestCase):
    """§22. What must be legitimate and what must not, separated automatically."""

    LEGITIMATE = (("radical replacement", of.constitutional_replacement),
                  ("permitted persuasion", of.persuasion),
                  ("high regret", of.high_regret),
                  ("never observed", of.unobservant),
                  ("open forever", of.transferred_once),
                  ("burden reduced", lambda: of.transfer_chain(3, 0.5)))

    ILLEGITIMATE = (("silent deletion", of.silently_deleted, "A1"),
                    ("empty frontier", of.transfer_to_nowhere, "A1"),
                    ("one branch lost", of.split_one_branch_lost, "A1"),
                    ("unauthorized discharge", of.entitled_with_laundered_obligation,
                     "A1"),
                    ("due ignored", of.recognized_due_but_never_entered, "D1"),
                    ("due ignored at once", of.due_and_ignored_in_one_step, "D1"))

    def test_the_legitimate_ones_pass(self):
        for name, make in self.LEGITIMATE:
            with self.subTest(name):
                f, d = fd(make())
                self.assertEqual(an.violations(f, d), {})
                self.assertEqual(an.nonconformance(f, d), {})
                self.assertEqual(an.thm_answerability_resolution(f, d), ())
                self.assertEqual(an.cor_recognized_is_resolved(f, d), ())

    def test_the_illegitimate_ones_fail_and_say_which_way(self):
        for name, make, which in self.ILLEGITIMATE:
            with self.subTest(name):
                f, d = fd(make())
                found = dict(an.violations(f, d), **an.nonconformance(f, d))
                self.assertIn(which, found)

    def test_ex_nihilo_entitlement_is_the_kernel_s_business(self):
        """Refused by the semantics, so nothing is manufactured and the
        structural premises never have to catch it."""
        f = of.build(of.ex_nihilo())
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(rp.live(f), f.base)
        self.assertEqual(rp.thm_grounded_replay(f), ())


class TestTheQuantitativeConclusionIsPreserved(unittest.TestCase):
    """§23. Preserved, narrow, and not extended."""

    def test_dilution_passes_the_structural_premise(self):
        for make in (lambda: of.transfer_chain(3, 0.5), of.diluted_to_nothing,
                     lambda: of.split(0.25), lambda: of.merge(0.5)):
            f, d = fd(make())
            self.assertEqual(an.violations(f, d), {})
            self.assertEqual(an.thm_answerability_resolution(f, d), ())

    def test_total_accounting_is_required(self):
        f, d = fd(of.merge_lenient())
        w = of.burden(d)
        self.assertEqual(an.diluting_edits(f, d, w), ())
        self.assertEqual(len(an.diluting_edits_total(f, d, w)), 1)

    def test_no_weight_in_the_theorem(self):
        for fn in (an.thm_answerability_resolution, an.resolution,
                   an.a1_controlled_resolution, an.d1_due_realization):
            self.assertNotIn("weight", inspect.getsource(fn))


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

    def test_everything_holds_on_every_answerability_constitution(self):
        for c in of.ANSWER_CONSTITUTIONS:
            f, d = fd(c)
            self.assertEqual(rp.violations(f), {})
            self.assertEqual(rp.thm_grounded_replay(f), ())
            self.assertEqual(an.violations(f, d), {})
            self.assertEqual(an.nonconformance(f, d), {})
            self.assertEqual(an.thm_answerability_resolution(f, d), ())
            self.assertEqual(an.cor_no_silent_loss(f, d), ())
            self.assertEqual(an.cor_recognized_is_resolved(f, d), ())

    def test_a1_has_countermodels_and_each_breaks_the_theorem(self):
        for c in of.A1_BROKEN:
            f, d = fd(c)
            self.assertIn("A1", an.violations(f, d))
            self.assertNotEqual(an.cor_no_silent_loss(f, d), ())

    def test_one_structural_premise_and_one_conformance_condition(self):
        self.assertEqual(len(an.PREMISES), 1)
        self.assertEqual(len(an.CONFORMANCE), 1)

    def test_two_semantic_parameters(self):
        doc = inspect.getdoc(an)
        self.assertIn("Due", doc)
        self.assertIn("Resolve", doc)


if __name__ == "__main__":
    unittest.main()
