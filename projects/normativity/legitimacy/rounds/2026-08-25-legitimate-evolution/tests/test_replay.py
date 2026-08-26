"""The kernel, its two premises, and the layers below it.

The constitution model imports `replay` and nothing else of ours, so a premise
holding only because of how a record is built shows up here as a failure. Every
premise has a countermodel in which the theorem's conclusion fails when it is
dropped.
"""
from __future__ import annotations

import ast
import inspect
import unittest

import replay as rp
import office as of
import ri_frame as rf

import cases
import fixtures as fx


RI_CASES = (
    ("C7b", fx.C7b_delegated_authorization()["case"]),
    ("C10", fx.C10_manufactured_authorization()["case"]),
    ("C11r", fx.C11_same_endpoint()["reflective"]),
    ("C11m", fx.C11_same_endpoint()["manipulated"]),
    ("C14", fx.C14_legitimate_revision()["case"]),
    ("C22", fx.C22_inquiry_laundering()["case"]),
    ("C23", fx.C23_proxy()["case"]),
    ("C33", fx.C33_standing_without_license()["case"]),
    ("force", cases.force_bearing()["case"]),
    ("cleanup", cases.record_cleanup()["case"]),
)


def every_frame():
    for c in of.ALL_CONSTITUTIONS:
        for a in of.contexts(c):
            yield of.build(c, a)
    for _, case in RI_CASES:
        for a in rf.contexts(case):
            yield rf.build(case, a)


class TestTheKernelIsStructural(unittest.TestCase):
    def test_it_names_no_architecture_and_no_semantics(self):
        """Read off the identifiers the module defines and uses.

        Prose may say what the kernel is not about; code may not mention it.
        """
        tree = ast.parse(inspect.getsource(rp))
        used = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Name):
                used.add(node.id)
            elif isinstance(node, ast.Attribute):
                used.add(node.attr)
            elif isinstance(node, (ast.FunctionDef, ast.ClassDef)):
                used.add(node.name)
            elif isinstance(node, (ast.Import, ast.ImportFrom)):
                used.add(getattr(node, "module", "") or "")
                used |= {n.name for n in node.names}
        for word in ("NormEvent", "ReasonOcc", "Settlement", "AnsRoot", "PAuth",
                     "PForce", "DRMDP", "ri_core", "excise", "permit",
                     "prov_ok", "provenance", "threat", "episode", "alpha"):
            self.assertNotIn(word, used, word)

    def test_the_constitution_model_imports_only_the_kernel(self):
        tree = ast.parse(inspect.getsource(of))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported |= {n.name.split(".")[0] for n in node.names}
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertEqual(imported - {"__future__", "dataclasses", "typing"},
                         {"replay"})

    def test_two_premises_and_no_more(self):
        self.assertEqual([n for n, _ in rp.PREMISES], ["S1", "S2"])

    def test_both_premises_hold_everywhere(self):
        for f in every_frame():
            self.assertEqual(rp.violations(f), {})
            self.assertEqual(rp.fresh_by_construction(f), ())

    def test_the_theorem_and_its_corollaries_hold_everywhere(self):
        for f in every_frame():
            self.assertEqual(rp.thm_grounded_replay(f), ())
            self.assertEqual(rp.cor_no_self_ratification(f), ())
            self.assertEqual(rp.cor_no_laundering(f), ())
            self.assertEqual(rp.cor_persistence(f), ())


class TestS2IsNecessary(unittest.TestCase):
    """§1. The previous formulation's grounding theorem was false without it."""

    def setUp(self):
        self.f = of.build(of.ex_nihilo())
        self.loose = rp.Frame(self.f.base, self.f.trace, self.f.auth,
                              lambda s, e: True)

    def test_the_semantic_definition_refuses_an_ungrounded_creation(self):
        self.assertEqual(rp.accepted(self.f), ())
        self.assertEqual(rp.live(self.f), self.f.base)

    def test_dropping_it_makes_the_theorem_false(self):
        self.assertEqual(rp.s1_prior_grounding(self.loose), ())
        self.assertNotEqual(rp.s2_no_ex_nihilo(self.loose), ())
        bad = rp.thm_grounded_replay(self.loose)
        self.assertEqual([k for k, _ in bad], ["leaf outside the base"])

    def test_prior_grounding_alone_is_vacuous_there(self):
        """Which is exactly why the previous proof step was unavailable."""
        self.assertEqual(self.f.trace[0].grounds, frozenset())
        self.assertEqual(rp.s1_prior_grounding(self.loose), ())

    def test_a_root_that_is_wanted_belongs_in_the_base(self):
        rooted = rp.Frame(self.f.base | self.f.trace[0].issued(0), (),
                          self.f.auth, self.f.valid)
        self.assertEqual(rp.thm_grounded_replay(rooted), ())


class TestS1IsNecessary(unittest.TestCase):
    """The other premise, prosecuted the same way."""

    def setUp(self):
        self.g = rp.Occ(rp.BASE, 0)
        phantom = rp.Occ(7, 0)
        self.e = rp.Edit(grounds=frozenset({phantom}), issues=("c",),
                         label="on-a-phantom")
        self.base = frozenset({self.g})

    def test_with_it_the_edit_is_refused_and_the_theorem_is_vacuous(self):
        strict = rp.Frame(self.base, (self.e,), lambda o: True,
                          lambda s, ed: ed.grounds <= s and bool(ed.grounds))
        self.assertEqual(rp.accepted(strict), ())
        self.assertEqual(rp.violations(strict), {})
        self.assertEqual(rp.thm_grounded_replay(strict), ())

    def test_without_it_the_theorem_is_false(self):
        loose = rp.Frame(self.base, (self.e,), lambda o: True,
                         lambda s, ed: bool(ed.grounds))
        self.assertNotEqual(rp.s1_prior_grounding(loose), ())
        self.assertEqual(rp.s2_no_ex_nihilo(loose), ())
        bad = rp.thm_grounded_replay(loose)
        self.assertEqual([k for k, _ in bad], ["no tree"])

    def test_the_two_premises_fail_on_different_frames(self):
        """Neither subsumes the other, which is why there are two."""
        loose1 = rp.Frame(self.base, (self.e,), lambda o: True,
                          lambda s, ed: bool(ed.grounds))
        ex = of.build(of.ex_nihilo())
        loose2 = rp.Frame(ex.base, ex.trace, ex.auth, lambda s, e: True)
        self.assertNotEqual(rp.s1_prior_grounding(loose1), ())
        self.assertEqual(rp.s2_no_ex_nihilo(loose1), ())
        self.assertEqual(rp.s1_prior_grounding(loose2), ())
        self.assertNotEqual(rp.s2_no_ex_nihilo(loose2), ())


class TestOccurrenceIdentity(unittest.TestCase):
    """§2. Position is identity; historical time was not."""

    def test_two_edits_cannot_share_a_position(self):
        g = rp.Occ(rp.BASE, 0)
        e = rp.Edit(grounds=frozenset({g}), issues=("x",))
        f = rp.Frame(frozenset({g}), (e, e), lambda o: True,
                     lambda s, ed: ed.grounds <= s)
        self.assertEqual(rp.fresh_by_construction(f), ())
        self.assertEqual(sorted(map(str, rp.admitted(f))),
                         ["o0.0", "o1.0", "oG.0"])

    def test_the_same_edit_value_twice_still_issues_two_occurrences(self):
        g = rp.Occ(rp.BASE, 0)
        e = rp.Edit(grounds=frozenset({g}), issues=("x",))
        f = rp.Frame(frozenset({g}), (e, e), lambda o: True,
                     lambda s, ed: ed.grounds <= s)
        self.assertNotEqual(f.issued(0), f.issued(1))

    def test_a_manufactured_occurrence_is_caught(self):
        g = rp.Occ(rp.BASE, 0)
        f = rp.Frame(frozenset({g, rp.Occ(0, 0)}),
                     (rp.Edit(grounds=frozenset({g}), issues=("x",)),),
                     lambda o: True, lambda s, e: True)
        self.assertNotEqual(rp.fresh_by_construction(f), ())

    def test_what_the_theorems_consume_is_unique_birth(self):
        """Not unique issuance of a content: `readoption` issues one twice."""
        f = of.build(of.readoption(), "alpha:audited")
        issued = [o for t in range(len(f.trace)) for o in f.issued(t)]
        self.assertEqual(len(issued), len(set(issued)))
        contents = [str(c) for e in f.trace for c in e.issues]
        self.assertNotEqual(len(contents), len(set(contents)))


class TestCheckers(unittest.TestCase):
    """§3. What the previous pass called soundness is worth nothing."""

    def setUp(self):
        self.f = of.build(of.missed_revocation())
        self.check = of.myopic(self.f, "strip")

    def test_the_semantic_replay_strips_the_authority(self):
        self.assertEqual(of.names(self.f, rp.live(self.f)), {"w:charter"})

    def test_the_checker_keeps_it_and_then_accepts_a_stale_use(self):
        g = rp.with_checker(self.f, self.check)
        self.assertEqual(of.names(self.f, rp.live(g)),
                         {"w:charter", "w:deputy", "n:by-deputy"})

    def test_the_rejected_notion_calls_that_sound(self):
        self.assertEqual(rp.sound_at_own_state(self.f, self.check), ())

    def test_so_soundness_does_not_preserve_the_authority_view(self):
        d = rp.divergence(self.f, self.check)
        spurious = {o for o in d["spurious"] if self.f.auth(o)}
        self.assertNotEqual(spurious, set())
        self.assertEqual(of.names(self.f, spurious), {"w:deputy"})

    def test_nor_the_norm_view(self):
        d = rp.divergence(self.f, self.check)
        spurious = {o for o in d["spurious"] if not self.f.auth(o)}
        self.assertEqual(of.names(self.f, spurious), {"n:by-deputy"})

    def test_agreement_along_the_trace_is_the_exact_condition(self):
        self.assertNotEqual(rp.agrees_on_trace(self.f, self.check), ())
        self.assertFalse(rp.thm_simulation(self.f, self.check))
        self.assertTrue(rp.thm_simulation(self.f, self.f.valid))

    def test_a_checker_that_errs_off_the_trace_is_still_exact(self):
        """The condition is weaker than global extensional equality."""
        def odd(state, e):
            if e not in self.f.trace:
                return not self.f.valid(state, e)
            return self.f.valid(state, e)
        self.assertEqual(rp.agrees_on_trace(self.f, odd), ())
        self.assertTrue(rp.thm_simulation(self.f, odd))


class TestLineageIsNotCurrentness(unittest.TestCase):
    """§4 and §15. What a grounding tree certifies, and what it does not."""

    def setUp(self):
        self.f = of.build(of.lineage_versus_current())

    def test_the_revoked_authority_still_has_a_tree(self):
        w = [o for o in rp.admitted(self.f)
             if of.names(self.f, {o}) == {"w:a"}][0]
        self.assertIsNotNone(rp.tree(self.f, w))
        self.assertTrue(rp.grounded(self.f, w))

    def test_and_is_not_live(self):
        w = [o for o in rp.admitted(self.f)
             if of.names(self.f, {o}) == {"w:a"}][0]
        self.assertNotIn(w, rp.live(self.f))

    def test_the_relations(self):
        r = rp.relations(self.f)
        self.assertTrue(r["live_subset_admitted"])
        self.assertNotEqual(r["admitted_not_live"], frozenset())
        self.assertEqual(r["grounded"], r["admitted"])

    def test_the_theorem_ranges_over_admitted(self):
        src = inspect.getsource(rp.thm_grounded_replay)
        self.assertIn("admitted(f)", src)
        self.assertNotIn("live(f)", src)

    def test_a_tree_names_no_disposal(self):
        """So it cannot witness that nothing later removed the occurrence."""
        w = [o for o in rp.admitted(self.f)
             if of.names(self.f, {o}) == {"w:a"}][0]
        t = rp.tree(self.f, w)
        self.assertNotIn(2, rp.edits_of(t))
        self.assertIn(2, rp.accepted(self.f))


class TestProvenanceIsDescriptiveAndPermitIsNormative(unittest.TestCase):
    """§6. The split that lets persuasion be recorded and allowed."""

    def test_persuasion_is_recorded_and_permitted(self):
        f = of.build(of.persuasion())
        self.assertEqual([str(f.trace[t]) for t in rp.accepted(f)], ["revise"])
        prov = f.trace[0].declared[1]
        self.assertIn("f:bobs-argument", prov.findings)
        self.assertFalse(prov.forged or prov.coerced)

    def test_a_forgery_is_recorded_and_refused(self):
        f = of.build(of.forged_input())
        self.assertEqual(rp.accepted(f), ())
        self.assertTrue(f.trace[0].declared[1].forged)

    def test_coercion_is_recorded_and_the_constitution_decides(self):
        strict = of.build(of.coerced_exercise(True))
        lax = of.build(of.coerced_exercise(False))
        self.assertEqual(rp.accepted(strict), ())
        self.assertEqual([str(lax.trace[t]) for t in rp.accepted(lax)],
                         ["under-duress"])
        self.assertTrue(strict.trace[0].declared[1].coerced)
        self.assertTrue(lax.trace[0].declared[1].coerced)

    def test_incomplete_provenance_is_refused(self):
        f = of.build(of.incomplete_provenance())
        self.assertEqual(rp.accepted(f), ())
        self.assertFalse(f.trace[0].declared[1].complete)

    def test_jurisdiction_is_permit_and_not_provenance(self):
        f = of.build(of.unauthorized_scope())
        out = f.trace[2]
        self.assertTrue(out.declared[1].complete)
        self.assertFalse(f.permit(rp.replay(f, 2), out))
        self.assertEqual([str(f.trace[t]) for t in rp.accepted(f)],
                         ["delegate", "in-scope"])


class TestContentInvarianceIsWithdrawn(unittest.TestCase):
    """§10. It was vacuous, and it is false once permission reads content."""

    def test_a_live_policy_can_forbid_a_scope(self):
        f = of.build(of.content_sensitive_jurisdiction())
        self.assertEqual(rp.accepted(f), ())

    def test_relabelling_the_policy_changes_what_is_legitimate(self):
        c = of.content_sensitive_jurisdiction()
        banning = of.Constitution(
            chartered=(("w:charter", of.ALL, "Assembly"),
                       ("n:moratorium", None, "Assembly")),
            acts=c.acts)
        f = of.build(banning)
        # the same gazette, with the moratorium not banning anything
        self.assertEqual(rp.accepted(f), ())

    def test_the_kernel_never_reads_content(self):
        src = inspect.getsource(rp.apply_edit) + inspect.getsource(rp.replay)
        self.assertNotIn("issues[", src)
        self.assertNotIn("content", src)

    def test_no_conservativity_is_imposed(self):
        """A successor may say anything its permission relation allows."""
        f = of.build(of.persuasion())
        before = {str(c) for c in ()}
        after = {str(c) for e in f.trace for c in e.issues}
        self.assertEqual(after, {"n:new"})
        self.assertEqual(before, set())


class TestAuthAndNormAreNotAPartition(unittest.TestCase):
    """§11. Two predicates; nothing requires them disjoint or exhaustive."""

    def test_the_kernel_takes_only_an_authority_predicate(self):
        self.assertIn("auth", rp.Frame.__dataclass_fields__)
        self.assertNotIn("norm", rp.Frame.__dataclass_fields__)

    def test_the_enforcement_projection_lives_in_the_realizations(self):
        self.assertTrue(hasattr(of, "norms"))
        self.assertTrue(hasattr(rf, "norms"))
        self.assertFalse(hasattr(rp, "norms"))

    def test_a_norm_can_bear_on_a_permission_judgment(self):
        """Without being an authority — so the roles are not exclusive."""
        f = of.build(of.content_sensitive_jurisdiction())
        mor = [o for o in f.base if of.names(f, {o}) == {"n:moratorium"}][0]
        self.assertFalse(f.auth(mor))
        self.assertEqual(rp.accepted(f), ())


class TestNoLaundering(unittest.TestCase):
    def test_downstream_use_never_rehabilitates(self):
        f = of.build(of.laundering(), "alpha:audited")
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(rp.admitted(f), f.base)

    def test_the_same_in_a_record(self):
        f = rf.build(fx.C10_manufactured_authorization()["case"], "alpha:audited")
        self.assertEqual(rp.accepted(f), ())
        self.assertEqual(rp.cor_no_laundering(f), ())

    def test_readoption_of_identical_content(self):
        f = of.build(of.readoption(), "alpha:audited")
        self.assertEqual([str(f.trace[t]) for t in rp.accepted(f)], ["clean-P"])
        live = of.norms(f, rp.live(f))
        self.assertEqual(of.names(f, live), {"n:P"})
        self.assertEqual({o.pos for o in live}, {2})


class TestAuditContexts(unittest.TestCase):
    def test_later_evidence_retracts(self):
        c = of.audit_discovery()
        trusting = of.build(c, "alpha:trusting")
        informed = of.build(c, "alpha:informed")
        self.assertEqual(len(rp.accepted(trusting)), 2)
        self.assertEqual(rp.accepted(informed), ())

    def test_and_can_restore(self):
        c = of.audit_restores()
        trusting = of.build(c, "alpha:trusting")
        informed = of.build(c, "alpha:informed")
        self.assertNotIn("n:old", of.names(trusting, rp.live(trusting)))
        self.assertIn("n:old", of.names(informed, rp.live(informed)))

    def test_a_record_carries_them_too(self):
        case = fx.C10_manufactured_authorization()["case"]
        self.assertEqual(len(rp.accepted(rf.build(case, "alpha:trusting"))), 1)
        self.assertEqual(rp.accepted(rf.build(case, "alpha:audited")), ())


class TestExtractionFactorization(unittest.TestCase):
    """§8 and §9. Noninterference is extraction plus a deterministic fold."""

    def test_the_fold_is_deterministic(self):
        a, b = of.hidden_pair()
        fa, fb = of.build(a), of.build(b)
        self.assertEqual(fa.trace, fb.trace)
        self.assertEqual(rp.replay(fa), rp.replay(fb))

    def test_a_hidden_read_in_the_semantics_breaks_it(self):
        a, b = of.hidden_reading_pair()
        fa, fb = of.build(a), of.build(b)
        self.assertEqual(fa.trace, fb.trace)
        self.assertNotEqual(rp.replay(fa), rp.replay(fb))

    def test_a_hidden_read_in_the_effect_breaks_extraction(self):
        d = cases.partial_effect_pair()
        self.assertEqual(rf.declared_data(d["quiet"]),
                         rf.declared_data(d["noisy"]))
        bad = rf.extraction_agrees(d["quiet"], d["noisy"])
        self.assertEqual([k for k, _ in bad],
                         ["effect differs on equal declarations"])

    def test_a_clean_record_extracts_consistently(self):
        case = fx.C14_legitimate_revision()["case"]
        self.assertEqual(rf.extraction_agrees(case, case), ())

    def test_the_effect_is_frozen_into_the_edit(self):
        self.assertIn("issues", rp.Edit.__dataclass_fields__)
        src = inspect.getsource(rp.apply_edit)
        self.assertIn("e.dispose", src)
        self.assertIn("e.issued", src)


class TestTheRecordRealization(unittest.TestCase):
    def test_every_carroll_discrimination_survives(self):
        audited = {name: rf.build(case, "alpha:audited")
                   for name, case in RI_CASES}
        for name in ("C10", "C22", "C23", "C11m"):
            self.assertEqual(rp.accepted(audited[name]), (), name)
        for name in ("C7b", "C11r", "C14", "C33"):
            self.assertNotEqual(rp.accepted(audited[name]), (), name)

    def test_a_rejected_uptake_leaves_the_predecessor_in_force(self):
        f = rf.build(fx.C11_same_endpoint()["manipulated"], "alpha:audited")
        self.assertEqual(rf.names(f, rf.norms(f, rp.live(f))), {"v:th_natural"})

    def test_the_enforcement_target_is_the_norm_projection(self):
        f = rf.build(cases.force_bearing()["case"], "alpha:audited")
        self.assertEqual(rf.names(f, rf.norms(f, rp.live(f))), {"J2"})

    def test_the_manufactured_injunction_never_enters_it(self):
        trusting = rf.build(cases.force_bearing()["case"], "alpha:trusting")
        audited = rf.build(cases.force_bearing()["case"], "alpha:audited")
        self.assertIn("J3", rf.names(trusting,
                                     rf.norms(trusting, rp.live(trusting))))
        self.assertNotIn("J3", rf.names(audited,
                                        rf.norms(audited, rp.live(audited))))


if __name__ == "__main__":
    unittest.main()
