"""The interface, run against two realizations that share no code.

Every hypothesis is checked on both and every theorem is run on both. The
constitution model imports nothing from the normative architecture, so a
hypothesis holding only because of how a record is built shows up here as a
failure rather than as a claim nobody tested — and it decides the questions
Reflective Integrity cannot see.
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


def ri(case, **kw):
    return rf.build(case, **kw)


ALL_CONSTITUTIONS = (
    of.rogue_revocation(), of.unauthorized_scope(), of.persuasion(),
    of.laundering(), of.readoption(), of.audit_discovery(),
    of.audit_restores(), of.forged_input(), of.coerced_exercise(),
    of.cleanup(), of.repealable(),
)

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


class TestTheInterfaceIsNotAboutOurLedger(unittest.TestCase):
    def test_the_constitution_model_imports_nothing_of_ours_but_replay(self):
        tree = ast.parse(inspect.getsource(of))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported |= {n.name.split(".")[0] for n in node.names}
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertEqual(imported - {"__future__", "dataclasses", "typing"},
                         {"replay"})

    def test_the_headline_module_names_no_architecture(self):
        src = inspect.getsource(rp)
        for word in ("NormEvent", "ReasonOcc", "Settlement", "AnsRoot",
                     "PForce", "PAuth", "DRMDP", "Logical Induction",
                     "ri_core", "excise"):
            self.assertNotIn(word, src, word)

    def test_the_hypotheses_hold_in_every_constitution(self):
        for c in ALL_CONSTITUTIONS:
            p = of.build(c)
            for a in p.contexts:
                self.assertEqual(rp.structural_violations(p, a), {}, str(c.acts))

    def test_the_hypotheses_hold_in_every_record(self):
        for name, case in RI_CASES:
            with self.subTest(name):
                p = ri(case)
                for a in p.contexts:
                    self.assertEqual(rp.structural_violations(p, a), {})

    def test_both_realizations_run_the_same_theorems(self):
        for p in [of.build(c) for c in ALL_CONSTITUTIONS] + \
                 [ri(case) for _, case in RI_CASES]:
            for a in p.contexts:
                self.assertEqual(rp.thm_finite_grounding(p, a), ())
                self.assertEqual(rp.thm_no_self_ratification(p, a), ())
                self.assertEqual(rp.thm_no_laundering(p, a), ())
                self.assertEqual(rp.thm_persistence(p, a), ())


class TestTheRawLifecycleWasWrong(unittest.TestCase):
    """§1 of COUNTERMODELS. The attack that replaced the previous object."""

    def setUp(self):
        self.c = of.rogue_revocation()
        self.p = of.build(self.c)
        self.a = "alpha:audited"

    def test_the_rogue_authority_is_never_legitimate(self):
        names = {str(self.p.contents()[o]) for o in rp.replay(self.p, self.a)}
        self.assertNotIn("w:rogue", names)

    def test_the_revocation_is_rejected_and_the_norm_survives(self):
        accepted = [str(e) for e in rp.accepted(self.p, self.a)]
        self.assertEqual(accepted, ["issue"])
        names = {str(self.p.contents()[o]) for o in rp.norms(rp.replay(self.p, self.a))}
        self.assertEqual(names, {"n:standard"})

    def test_persistence_holds_across_the_attack(self):
        self.assertEqual(rp.thm_persistence(self.p, self.a), ())

    def test_the_raw_process_and_the_legitimate_state_disagree(self):
        """The raw gazette removed the norm; the legitimate state kept it."""
        raw = {"w:charter", "w:rogue"}
        legit = {str(self.p.contents()[o]) for o in rp.replay(self.p, self.a)}
        self.assertNotEqual(raw, legit)
        self.assertIn("n:standard", legit)


class TestAuthorityIsNotAuthorization(unittest.TestCase):
    """§2. A grounded warrant used outside its domain."""

    def test_the_out_of_scope_act_is_refused(self):
        p = of.build(of.unauthorized_scope())
        a = p.contexts[0]
        accepted = [str(e) for e in rp.accepted(p, a)]
        self.assertEqual(accepted, ["delegate", "in-scope"])
        names = {str(p.contents()[o]) for o in rp.norms(rp.replay(p, a))}
        self.assertEqual(names, {"n:budget"})

    def test_its_grounds_were_impeccable(self):
        p = of.build(of.unauthorized_scope())
        a = p.contexts[0]
        out = p.at(2)
        self.assertTrue(out.grounds <= rp.auth(rp.replay(p, a, 2)))
        self.assertTrue(p.prov_ok(a, out))
        self.assertFalse(p.permit(rp.replay(p, a, 2), out))

    def test_permit_soundness_is_a_real_hypothesis(self):
        for c in ALL_CONSTITUTIONS:
            p = of.build(c)
            for a in p.contexts:
                self.assertEqual(rp.h4_permit_soundness(p, a), ())


class TestLegitimateInfluenceNeedsNoOutcomeSurvival(unittest.TestCase):
    """§3. Removing Bob's argument removes the edit; the edit stays legitimate."""

    def test_the_revision_is_valid(self):
        p = of.build(of.persuasion())
        a = p.contexts[0]
        self.assertEqual([str(e) for e in rp.accepted(p, a)], ["revise"])
        names = {str(p.contents()[o]) for o in rp.norms(rp.replay(p, a))}
        self.assertEqual(names, {"n:new"})

    def test_the_judgment_reads_one_state_and_one_edit(self):
        """No second history is available to it, so no outcome counterfactual is.

        `valid(alpha, state, edit)` is the whole signature. The previous branch's
        criterion took a record and an excision set, and that is what made
        removing Bob's argument bear on whether Alice's revision was legitimate.
        """
        sig = inspect.signature(rp.h3_prestate_grounding)
        self.assertEqual(list(sig.parameters), ["p", "alpha"])
        p = of.build(of.persuasion())
        self.assertEqual(len(inspect.signature(p.valid).parameters), 3)


class TestNoLaundering(unittest.TestCase):
    """§4 and §5. Rejected authority never becomes legitimate; content is free."""

    def test_downstream_use_never_rehabilitates(self):
        p = of.build(of.laundering())
        a = "alpha:audited"
        self.assertEqual(rp.accepted(p, a), ())
        self.assertEqual(rp.replay(p, a), p.base)
        self.assertEqual(rp.thm_no_laundering(p, a), ())

    def test_the_same_in_a_record(self):
        p = ri(fx.C10_manufactured_authorization()["case"])
        self.assertEqual(rp.accepted(p, "alpha:audited"), ())
        self.assertEqual(rp.thm_no_laundering(p, "alpha:audited"), ())

    def test_later_clean_readoption_of_identical_content(self):
        p = of.build(of.readoption())
        a = "alpha:audited"
        self.assertEqual([str(e) for e in rp.accepted(p, a)], ["clean-P"])
        live = rp.norms(rp.replay(p, a))
        self.assertEqual({str(p.contents()[o]) for o in live}, {"n:P"})
        self.assertEqual({o.at for o in live}, {2})

    def test_the_illicit_occurrence_is_a_different_occurrence(self):
        p = of.build(of.readoption())
        illicit = p.at(1).issued()[0]
        clean = p.at(2).issued()[0]
        self.assertNotEqual(illicit, clean)
        self.assertEqual(str(p.contents()[illicit]), str(p.contents()[clean]))
        self.assertNotIn(illicit, rp.replay(p, "alpha:audited"))

    def test_no_self_ratification(self):
        for c in ALL_CONSTITUTIONS:
            p = of.build(c)
            for a in p.contexts:
                self.assertEqual(rp.thm_no_self_ratification(p, a), ())


class TestFiniteGrounding(unittest.TestCase):
    """§6. Every legitimate occurrence has a finite tree with strict descent."""

    def test_trees_exist_and_descend(self):
        for p in [of.build(c) for c in ALL_CONSTITUTIONS] + \
                 [ri(case) for _, case in RI_CASES]:
            for a in p.contexts:
                self.assertEqual(rp.thm_finite_grounding(p, a), ())

    def test_a_tree_names_the_actual_accepted_edits(self):
        p = of.build(of.audit_discovery())
        a = "alpha:trusting"
        rule = [o for o in rp.norms(rp.replay(p, a))][0]
        g = rp.certificate(p, a, rule)
        self.assertIsNotNone(g)
        self.assertTrue(rp.tree_leaves(g) <= p.base)
        self.assertEqual(rp.tree_edits(g), frozenset({0, 1}))

    def test_unique_issuance_is_free_rather_than_assumed(self):
        """The question the previous pass argued about does not arise here.

        An occurrence carries the index of the edit that issued it, so two edits
        cannot issue one occurrence and no axiom has to say so. `H2` is what
        reports any attempt, and the previous branch's two-issuer register has no
        analogue to build.
        """
        for p in [of.build(c) for c in ALL_CONSTITUTIONS] + \
                 [ri(case) for _, case in RI_CASES]:
            self.assertEqual(rp.h2_fresh_occurrence(p), ())
            issued = [o for e in p.edits for o in e.issued()]
            self.assertEqual(len(issued), len(set(issued)))


class TestAuditContexts(unittest.TestCase):
    """§7. Historical time and audit time are two indices."""

    def test_later_evidence_retracts_an_old_edit_and_its_descendants(self):
        p = of.build(of.audit_discovery())
        trusting = rp.replay(p, "alpha:trusting")
        informed = rp.replay(p, "alpha:informed")
        self.assertEqual(len(rp.accepted(p, "alpha:trusting")), 2)
        self.assertEqual(rp.accepted(p, "alpha:informed"), ())
        self.assertEqual(informed, p.base)
        self.assertEqual(len(rp.retracted(p, "alpha:trusting", "alpha:informed")), 2)

    def test_a_stricter_audit_can_leave_more_in_force(self):
        """Because the edit it invalidates was a revocation."""
        p = of.build(of.audit_restores())
        restored = rp.restored(p, "alpha:trusting", "alpha:informed")
        self.assertNotEqual(restored, frozenset())
        self.assertEqual({str(p.contents()[o]) for o in restored}, {"n:old"})

    def test_the_historical_rule_did_not_change(self):
        """Only what is believed about the past did."""
        p = of.build(of.audit_discovery())
        self.assertEqual([e.declared() for e in p.edits],
                         [e.declared() for e in p.edits])
        for a in p.contexts:
            self.assertEqual(rp.structural_violations(p, a), {})

    def test_a_record_carries_the_two_contexts_too(self):
        p = ri(fx.C10_manufactured_authorization()["case"])
        self.assertEqual(len(rp.accepted(p, "alpha:trusting")), 1)
        self.assertEqual(rp.accepted(p, "alpha:audited"), ())


class TestNoninterference(unittest.TestCase):
    """§8. Hidden state cannot move the legitimate state."""

    def test_the_positive_control(self):
        a, b = of.clean_pair()
        pa, pb = of.build(a), of.build(b)
        self.assertEqual(rp.h5_declared_factorization(pa, pb, pa.contexts[0]), ())
        self.assertTrue(rp.thm_noninterference(pa, pb, pa.contexts[0]))

    def test_a_hidden_variable_that_decides_admission_is_rejected(self):
        a, b = of.hidden_admission_pair()
        pa, pb = of.build(a), of.build(b)
        bad = rp.h5_declared_factorization(pa, pb, pa.contexts[0])
        self.assertEqual([k for k, _ in bad], ["verdict differs"])
        self.assertFalse(rp.thm_noninterference(pa, pb, pa.contexts[0]))

    def test_a_hidden_read_that_changes_the_effect_is_rejected(self):
        d = cases.partial_effect_pair()
        pq, pn = ri(d["quiet"]), ri(d["noisy"])
        a = "alpha:trusting"
        self.assertEqual(pq.view(a, 1), pn.view(a, 1))
        self.assertEqual(pq.at(d["at"]).declared(), pn.at(d["at"]).declared())
        bad = rp.h5_declared_factorization(pq, pn, a)
        self.assertEqual([k for k, _ in bad], ["effect differs"])
        self.assertFalse(rp.thm_noninterference(pq, pn, a))

    def test_authorized_influence_is_not_excluded(self):
        """Changing the declared input changes the view, and that is allowed."""
        p = of.build(of.persuasion())
        e = p.edits[0]
        self.assertIn("f:bobs-argument", e.input[0])
        self.assertIn("f:bobs-argument", str(e.declared()))


class TestInputAndExercise(unittest.TestCase):
    """§9. Two ways an exercise fails provenance, and they are different."""

    def test_a_forged_input_is_refused(self):
        p = of.build(of.forged_input())
        a = p.contexts[0]
        self.assertEqual(rp.accepted(p, a), ())
        self.assertFalse(p.prov_ok(a, p.edits[0]))

    def test_a_coerced_exercise_is_refused(self):
        p = of.build(of.coerced_exercise())
        a = p.contexts[0]
        self.assertEqual(rp.accepted(p, a), ())
        self.assertFalse(p.prov_ok(a, p.edits[0]))

    def test_they_fail_different_clauses(self):
        forged = of.build(of.forged_input()).edits[0]
        coerced = of.build(of.coerced_exercise()).edits[0]
        self.assertTrue(forged.input[1])
        self.assertFalse(coerced.input[1])
        self.assertTrue(coerced.exercise[0])
        self.assertFalse(forged.exercise[0])


class TestCoverage(unittest.TestCase):
    """§10. Provenance adequacy is relative to a stated threat class."""

    def test_a_process_that_doubts_nothing_certifies_everything(self):
        p = of.build(of.laundering())
        self.assertNotEqual(rp.accepted(p, "alpha:nothing-doubted"), ())

    def test_and_fails_coverage_against_the_influence_it_misses(self):
        p = of.build(of.laundering())
        threat = {"xi:campaign": frozenset({0})}
        bad = rp.h6_provenance_adequacy(p, "alpha:nothing-doubted", threat)
        self.assertTrue([b for b in bad if b[0] == "uncovered influence"])

    def test_the_audited_context_covers_it(self):
        p = of.build(of.laundering())
        threat = {"xi:campaign": frozenset({0})}
        self.assertEqual(rp.h6_provenance_adequacy(p, "alpha:audited", threat), ())

    def test_a_records_own_episodes_cover_by_construction(self):
        case = fx.C10_manufactured_authorization()["case"]
        p = ri(case)
        threat = rf.threat(case, "alpha:audited")
        self.assertNotEqual(threat, {})
        self.assertEqual(rp.h6_provenance_adequacy(p, "alpha:audited", threat), ())


class TestVerifiers(unittest.TestCase):
    """§11. Soundness is not enough for the enforcement consumer."""

    def setUp(self):
        self.p = of.build(of.repealable())
        self.a = self.p.contexts[0]

    def test_the_semantic_replay_repeals(self):
        self.assertEqual([str(e) for e in rp.accepted(self.p, self.a)],
                         ["enact", "repeal"])
        self.assertEqual(rp.norms(rp.replay(self.p, self.a)), frozenset())

    def test_a_sound_incomplete_checker_leaves_the_obsolete_norm_in_force(self):
        verify = of.myopic(self.p, "repeal")
        self.assertEqual(rp.verifier_sound(self.p, verify, self.a), ())
        missed = rp.missed_disposals(self.p, verify, self.a)
        self.assertNotEqual(missed, ())
        checked = rp.with_verifier(self.p, verify)
        left = rp.norms(rp.replay(checked, self.a))
        self.assertEqual({str(self.p.contents()[o]) for o in left}, {"n:obsolete"})

    def test_missing_an_issuance_is_merely_conservative(self):
        verify = of.myopic(self.p, "enact")
        self.assertEqual(rp.verifier_sound(self.p, verify, self.a), ())
        self.assertEqual(rp.missed_disposals(self.p, verify, self.a), ())
        checked = rp.with_verifier(self.p, verify)
        self.assertEqual(rp.norms(rp.replay(checked, self.a)), frozenset())


class TestTheTwoProjections(unittest.TestCase):
    """§12. One legitimate state, two consumer views."""

    def test_they_partition_the_state(self):
        for p in [of.build(c) for c in ALL_CONSTITUTIONS] + \
                 [ri(case) for _, case in RI_CASES]:
            for a in p.contexts:
                L = rp.replay(p, a)
                self.assertEqual(rp.auth(L) | rp.norms(L), L)
                self.assertEqual(rp.auth(L) & rp.norms(L), frozenset())

    def test_the_enforcement_target_moves_on_a_legitimate_supersession(self):
        case = cases.force_bearing()["case"]
        p = ri(case)
        a = "alpha:audited"
        early = rp.norms(rp.replay(p, a, 4))
        late = rp.norms(rp.replay(p, a))
        self.assertNotEqual(early, frozenset())
        self.assertNotEqual(early, late)
        self.assertEqual(len(late), 1)

    def test_a_manufactured_norm_never_enters_the_target(self):
        d = cases.force_bearing()
        p = ri(d["case"])
        late = rp.norms(rp.replay(p, "alpha:audited"))
        self.assertEqual({o.at for o in late}, {6})

    def test_content_is_unconstrained(self):
        case = fx.C14_legitimate_revision()["case"]
        p = ri(case)
        self.assertTrue(rp.thm_content_unconstrained(p, "alpha:audited",
                                                     {"v:th_later": "v:zzz"}))
        q = ri(rf.relabel(case, {"v:th_prior": "v:zzz", "v:th_later": "v:yyy"}))
        self.assertEqual(rp.replay(p, "alpha:audited"),
                         rp.replay(q, "alpha:audited"))


class TestTheCompressionIsNotDefinitional(unittest.TestCase):
    """§13. The global theorems have to be able to fail, and they do."""

    def test_finite_grounding_fails_when_grounding_is_dropped(self):
        """An edit grounded in an occurrence nobody ever issued.

        With **H3** the edit is refused and the theorem holds vacuously; without
        it the edit is applied and what it issues has no tree at all. So the
        conclusion is not an unfolding of the replay: it fails exactly when the
        hypothesis does.
        """
        base = frozenset({rp.Occ(rp.BASE_TIME, 0)})
        phantom = rp.Occ(7, 0)
        e = rp.Edit(at=0, grounds=frozenset({phantom}),
                    issue=((rp.AUTHORITY, "c"),), label="ungrounded")
        strict = rp.Process(base, (e,), lambda a, s, ed: ed.grounds <= rp.auth(s),
                            ("a",))
        loose = rp.Process(base, (e,), lambda a, s, ed: True, ("a",))

        self.assertEqual(rp.h3_prestate_grounding(strict, "a"), ())
        self.assertEqual(rp.thm_finite_grounding(strict, "a"), ())

        self.assertNotEqual(rp.h3_prestate_grounding(loose, "a"), ())
        self.assertNotEqual(rp.thm_finite_grounding(loose, "a"), ())

    def test_no_laundering_fails_when_freshness_is_dropped(self):
        """An edit re-issuing an occurrence a rejected edit proposed."""
        p = of.build(of.readoption())
        illicit = p.at(1).issued()[0]
        forged = rp.Edit(at=3, grounds=frozenset({rp.Occ(rp.BASE_TIME, 0)}),
                         issue=(), label="forge")
        object.__setattr__(forged, "issue", p.at(1).issue)
        object.__setattr__(forged, "at", 1)
        clashing = rp.Process(p.base, p.edits + (forged,), p.valid, p.contexts,
                              p.permit, p.prov_ok, p.view, p.content)
        self.assertNotEqual(rp.h2_fresh_occurrence(clashing), ())


if __name__ == "__main__":
    unittest.main()
