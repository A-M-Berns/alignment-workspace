"""The interface, run against two realizations that share no code.

Every axiom is checked on both and every theorem is run on both. The second
realization imports nothing from the normative architecture, so an axiom holding
only because of how a ledger is built shows up here as a failure rather than as
a claim nobody tested — and three of this pass's decisions were settled by it,
because Reflective Integrity's admission preconditions make the alternatives
indistinguishable inside our own records.
"""
from __future__ import annotations

import ast
import inspect
import unittest

import frame as fr
import ri_frame as rf
import warrant as wt

import cases
import fixtures as fx
import legitimacy as lg


CLEAN = wt.clean_register()
LAUNDERED = wt.laundered_register()
MERGE = wt.merge_register()
ATTACK = wt.stable_but_illegitimate_register()
CLEANUP = wt.cleanup_register()
TWO = wt.two_issuers_register()
UNCOVERED = wt.undercovered_register()

REGISTERS = (CLEAN, LAUNDERED, MERGE, ATTACK, CLEANUP, TWO, UNCOVERED)


def ri(d, **kw):
    return rf.build(d["case"], **kw)


class TestTheInterfaceIsNotAboutOurLedger(unittest.TestCase):
    def test_the_second_realization_imports_no_normative_architecture(self):
        tree = ast.parse(inspect.getsource(wt))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported |= {n.name.split(".")[0] for n in node.names}
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertEqual(imported - {"__future__", "dataclasses", "typing"},
                         {"frame"})

    def test_the_spine_holds_in_every_register(self):
        for reg in REGISTERS:
            f, _ = wt.build(reg)
            self.assertEqual(fr.violations(f), {})

    def test_the_spine_holds_in_reflective_integrity_records(self):
        for name, d in (("C7b", fx.C7b_delegated_authorization()),
                        ("C10", fx.C10_manufactured_authorization()),
                        ("C14", fx.C14_legitimate_revision()),
                        ("C33", fx.C33_standing_without_license()),
                        ("cleanup", cases.record_cleanup())):
            with self.subTest(name):
                f, _ = ri(d)
                self.assertEqual(fr.violations(f), {})

    def test_the_lifecycle_and_account_axioms_hold_in_both(self):
        for f, acc in (wt.build(CLEAN), ri(cases.record_cleanup()),
                       ri(cases.split_with_due_branch())):
            self.assertEqual(fr.lifecycle_violations(f), {})
            self.assertEqual(fr.account_violations(f, acc), {})

    def test_both_realizations_run_the_same_theorems(self):
        for f, acc in (wt.build(CLEAN), ri(fx.C7b_delegated_authorization())):
            self.assertEqual(fr.thm_finite_lineage(f), ())
            self.assertEqual(fr.thm_visible_discontinuity(f, acc), ())
            for q in f.challenges:
                self.assertEqual(fr.thm_stability_of_derivable(f, q), ())
                self.assertEqual(fr.thm_no_bootstrap(f, q), ())
                self.assertEqual(fr.thm_persistence(f, q), ())


class TestTheLicenceMustBeDerived(unittest.TestCase):
    """§1 of COUNTERMODELS. The attack that refuted the first pass's theorem."""

    def setUp(self):
        self.f, _ = wt.build(ATTACK)
        self.q = "q:campaign"

    def test_the_laundered_licence_is_stable_and_not_derivable(self):
        self.assertTrue(self.f.stable(self.q, "w:m"))
        self.assertNotIn("w:m", fr.derivable(self.f, self.q))
        self.assertFalse(self.f.stable(self.q, "w:tainted"))

    def test_the_rejected_rule_admits_it_and_the_theorem_is_false_there(self):
        reach = fr.derivable_stable_licence(self.f, self.q)
        self.assertIn("w:y", reach)
        self.assertNotEqual(fr.bootstrapped_under(self.f, self.q, reach), ())

    def test_the_repaired_rule_refuses_it_and_the_theorem_holds(self):
        reach = fr.derivable(self.f, self.q)
        self.assertNotIn("w:y", reach)
        self.assertEqual(fr.bootstrapped_under(self.f, self.q, reach), ())
        self.assertEqual(fr.thm_no_bootstrap(self.f, self.q), ())

    def test_stability_does_not_imply_legitimacy(self):
        stable = {x for x in self.f.authorities if self.f.stable(self.q, x)}
        self.assertTrue(stable - fr.derivable(self.f, self.q))

    def test_the_licence_is_a_ground(self):
        for t in self.f.exercises:
            self.assertIn(self.f.lic[t], self.f.grounds(t))


class TestAffectedIsNotParents(unittest.TestCase):
    """§2 of COUNTERMODELS. Acting on a standing is not inheriting from it."""

    def test_a_cleanup_produces_a_legitimate_successor(self):
        f, _ = wt.build(CLEANUP)
        reach = fr.derivable(f, "q:campaign")
        self.assertNotIn("w:tainted", reach)
        self.assertIn("w:proper", reach)

    def test_the_control_that_inherits_instead_is_refused(self):
        f, _ = wt.build(CLEANUP)
        self.assertNotIn("w:carried", fr.derivable(f, "q:campaign"))

    def test_the_record_calculus_expresses_a_cleanup_in_two_events(self):
        d = cases.record_cleanup()
        f, _ = ri(d)
        reach = fr.derivable_everywhere(f)
        self.assertNotIn(d["tainted"], reach)
        self.assertIn(d["replacement"], reach)

    def test_a_create_inherits_from_its_licence_alone(self):
        d = cases.record_cleanup()
        f, _ = ri(d)
        replace = [t for t in f.exercises if t.event_id == "a:replace"][0]
        self.assertEqual(f.parents[replace], frozenset())
        self.assertEqual(f.affected[replace], frozenset())

    def test_a_revocation_acts_without_inheriting(self):
        d = cases.record_cleanup()
        f, _ = ri(d)
        revoke = [t for t in f.exercises if t.event_id == "a:revoke"][0]
        self.assertEqual(f.affected[revoke], frozenset({d["tainted"]}))
        self.assertEqual(f.parents[revoke], frozenset())
        self.assertEqual(f.tgt[revoke], frozenset())

    def test_all_of_parents_and_not_one_of_them(self):
        f, _ = wt.build(MERGE)
        q = "q:campaign"
        self.assertNotIn("w:merged", fr.derivable(f, q))
        out = set(f.base)
        changed = True
        while changed:
            changed = False
            for t in sorted(f.exercises, key=str):
                if not f.stable(q, t):
                    continue
                if f.parents[t] and not f.parents[t] & out:
                    continue
                if f.lic[t] not in out:
                    continue
                if f.tgt[t] - out:
                    out |= f.tgt[t]
                    changed = True
        self.assertIn("w:merged", out)


class TestUniqueIssuanceIsOptional(unittest.TestCase):
    """§3 of COUNTERMODELS. Existence and canonicity really do come apart."""

    def setUp(self):
        self.f, _ = wt.build(TWO)
        self.q = "q:campaign"

    def test_unique_issuance_fails(self):
        self.assertNotEqual(fr.l2_unique_issuance(self.f), ())
        self.assertFalse(fr.thm_canonical_provenance(self.f))

    def test_lineage_existence_holds_anyway(self):
        self.assertEqual(fr.thm_finite_lineage(self.f), ())
        self.assertNotIn("L2'", fr.violations(self.f))

    def test_the_authority_is_derivable_by_the_clean_route(self):
        self.assertIn("w:dual", fr.derivable(self.f, self.q))
        self.assertIn("w:downstream", fr.derivable(self.f, self.q))

    def test_the_route_blind_provenance_contains_the_challenged_issuer(self):
        """Which is why the theorem is stated over a derivation, not a union."""
        self.assertIn("act:chancery-a", self.f.chal[self.q])
        used = {s.exercise for s in fr.derivation(self.f, self.q, "w:downstream")}
        self.assertNotIn("act:chancery-a", used)
        self.assertIn("act:chancery-b", used)
        self.assertEqual(fr.thm_no_bootstrap(self.f, self.q), ())

    def test_the_spine_never_calls_unique_issuance(self):
        self.assertNotIn("L2'", [name for name, _ in fr.SPINE])


class TestExerciseIdentity(unittest.TestCase):
    """§4 of COUNTERMODELS. The hypothesis moves; it does not vanish."""

    def test_c28_is_repaired_by_effect_identity(self):
        d = fx.C28_prestate_reading_schema(True)
        self.assertFalse(rf.prestate_blind(d["case"]))
        event, _ = ri(d, identity=rf.EVENT)
        effect, _ = ri(d, identity=rf.EFFECT)
        self.assertIn("L3", fr.violations(event))
        self.assertEqual(fr.violations(effect), {})

    def test_but_a_partial_effect_refutes_the_other_axiom(self):
        d = cases.partial_effect()
        self.assertFalse(rf.prestate_blind(d["case"]))
        event, _ = ri(d, identity=rf.EVENT)
        effect, _ = ri(d, identity=rf.EFFECT)
        self.assertEqual(sorted(fr.violations(event)), ["L3"])
        self.assertEqual(sorted(fr.violations(effect)), ["L3'"])

    def test_the_two_failures_name_the_two_halves_of_one_effect(self):
        d = cases.partial_effect()
        event, _ = ri(d, identity=rf.EVENT)
        effect, _ = ri(d, identity=rf.EFFECT)
        self.assertEqual([y for _, _, y in fr.l3_issuance_stability(event)],
                         [d["changed"]])
        self.assertEqual([y for _, y, _ in fr.l3p_origin_necessity(effect)],
                         [d["unchanged"]])

    def test_prestate_blindness_discharges_both_under_both_identities(self):
        for d in (fx.C28_prestate_reading_schema(False),
                  fx.C7b_delegated_authorization(),
                  cases.record_cleanup()):
            self.assertTrue(rf.prestate_blind(d["case"]))
            for ident in (rf.EVENT, rf.EFFECT):
                f, _ = ri(d, identity=ident)
                self.assertEqual(fr.violations(f), {})


class TestChallengeCoverage(unittest.TestCase):
    """§5 of COUNTERMODELS. Form is not coverage."""

    def test_a_frame_with_no_challenges_satisfies_every_axiom(self):
        f, _ = wt.build(UNCOVERED)
        self.assertEqual(fr.violations(f), {})
        self.assertEqual(f.challenges, ())
        self.assertEqual(fr.derivable_everywhere(f), f.authorities)

    def test_and_certifies_nothing_against_a_threat_model_it_misses(self):
        f, _ = wt.build(UNCOVERED)
        threat = wt.undercovered_threat()
        self.assertNotEqual(fr.coverage(f, threat), ())
        self.assertEqual(fr.certified_against(f, threat), frozenset())

    def test_a_frame_that_does_challenge_it_certifies_its_clean_part(self):
        f, _ = wt.build(LAUNDERED)
        threat = wt.covered_threat()
        self.assertEqual(fr.coverage(f, threat), ())
        certified = fr.certified_against(f, threat)
        self.assertIn("w:charter", certified)
        self.assertNotIn("w:permit", certified)

    def test_no_certificate_is_issued_against_an_uncovered_threat(self):
        f, _ = wt.build(UNCOVERED)
        self.assertIsNone(fr.certify(f, "w:permit", wt.undercovered_threat()))

    def test_a_records_own_episodes_make_coverage_true_by_construction(self):
        """Which is the honest ceiling on what a record can supply about itself."""
        d = fx.C10_manufactured_authorization()
        f, _ = ri(d)
        self.assertEqual(fr.coverage(f, rf.threat_from_episodes(d["case"])), ())


class TestTheLifecycle(unittest.TestCase):
    """§6. What is legitimately live, through time."""

    def test_the_frontier_is_live_and_derivable(self):
        d = cases.record_cleanup()
        f, _ = ri(d)
        q = f.challenges[0]
        last = f.times[-1]
        self.assertIn(d["replacement"], fr.frontier(f, q, last))
        self.assertNotIn(d["tainted"], fr.frontier(f, q, last))

    def test_a_manufactured_authority_is_live_and_not_in_the_frontier(self):
        d = fx.C10_manufactured_authorization()
        f, _ = ri(d)
        q = f.challenges[0]
        last = f.times[-1]
        self.assertIn("@s3.0", f.live[last])
        self.assertNotIn("@s3.0", fr.frontier(f, q, last))

    def test_persistence_until_something_acts_on_it(self):
        for f, _ in (wt.build(CLEAN), wt.build(CLEANUP),
                     ri(cases.record_cleanup())):
            for q in f.challenges:
                self.assertEqual(fr.thm_persistence(f, q), ())

    def test_legitimate_supersession_moves_the_frontier(self):
        f, _ = wt.build(CLEAN)
        q = "q:rumour"
        self.assertIn("w:inspector", fr.frontier(f, q, 1))
        self.assertNotIn("w:inspector", fr.frontier(f, q, 2))
        self.assertIn("w:inspector-2", fr.frontier(f, q, 2))

    def test_a_new_challenge_is_the_second_exit_route(self):
        base = wt.Register(
            chartered=("w:charter",), holder0={"w:charter": "Assembly"},
            acts=UNCOVERED.acts, findings=UNCOVERED.findings,
            challenges=(), voids={})
        more = wt.Register(
            chartered=("w:charter",), holder0={"w:charter": "Assembly"},
            acts=UNCOVERED.acts, findings=UNCOVERED.findings,
            challenges=("q:campaign",), voids={"q:campaign": ("f:planted",)})
        f0, _ = wt.build(base)
        f1, _ = wt.build(more)
        self.assertTrue(fr.thm_legitimacy_is_antitone_in_challenges(f0, f1))
        self.assertIn("w:captured", fr.derivable_everywhere(f0))
        self.assertNotIn("w:captured", fr.derivable_everywhere(f1))

    def test_the_norm_view_is_what_an_enforcement_consumer_would_read(self):
        """A force-bearing record: one norm superseded, one manufactured."""
        d = cases.force_bearing()
        f, _ = ri(d)
        q, last = f.challenges[0], f.times[-1]
        kind = rf.classify(d["case"])
        norms = fr.project(f, q, last, kind, "norm")
        self.assertEqual(norms, frozenset({d["successor"]}))
        self.assertIn(d["manufactured"], f.live[last])
        self.assertNotIn(d["manufactured"], norms)
        self.assertIn(d["first"], fr.frontier(f, q, 3))
        self.assertNotIn(d["first"], fr.frontier(f, q, last))

    def test_the_two_projections_split_one_frontier(self):
        d = cases.record_cleanup()
        f, _ = ri(d)
        q, last = f.challenges[0], f.times[-1]
        kind = rf.classify(d["case"])
        auth = fr.project(f, q, last, kind, "authority")
        norm = fr.project(f, q, last, kind, "norm")
        self.assertEqual(auth | norm, fr.frontier(f, q, last))
        self.assertEqual(auth & norm, frozenset())
        self.assertIn(d["replacement"], auth)


class TestTheThreeInterfacesAreIndependent(unittest.TestCase):
    """Entitled, accountable and serviceable are three things."""

    def test_the_frame_carries_no_liability_field(self):
        """Serviceability is the enforcement consumer's, not legitimacy's."""
        fields = set(fr.Frame.__dataclass_fields__)
        for word in ("liability", "allowance", "charge", "budget", "price",
                     "cost"):
            self.assertFalse([n for n in fields if word in n], word)

    def test_a_norm_can_be_legitimate_and_its_account_outstanding(self):
        d = cases.delegated_custody(answered=False)
        f, acc = ri(d)
        self.assertIn(cases.DELEGABLE, fr.derivable_everywhere(f))
        self.assertFalse(fr.continuous(f, acc, d["disposed_root"]))

    def test_the_lifetime_of_a_norm_is_readable_from_the_frontier(self):
        d = cases.force_bearing()
        f, _ = ri(d)
        q = f.challenges[0]
        kind = rf.classify(d["case"])
        lifetime = {s for s in f.times
                    if d["first"] in fr.project(f, q, s, kind, "norm")}
        after = {s for s in f.times
                 if d["successor"] in fr.project(f, q, s, kind, "norm")}
        self.assertTrue(lifetime)
        self.assertTrue(after)
        self.assertEqual(lifetime & after, set())
        self.assertLess(max(lifetime), min(after))


class TestContentIndependence(unittest.TestCase):
    def test_relabelling_what_the_standings_say_changes_nothing_derivable(self):
        d = fx.C14_legitimate_revision()
        case = d["case"]
        sigma = {"v:th_prior": "v:zzz", "v:th_later": "v:yyy"}
        before, _ = rf.build(case)
        after, _ = rf.build(rf.relabel_content(case, sigma))
        self.assertEqual(fr.derivable_everywhere(before),
                         fr.derivable_everywhere(after))
        self.assertNotEqual(rf.content_map(case),
                            rf.content_map(rf.relabel_content(case, sigma)))

    def test_a_successor_may_say_something_else_entirely(self):
        d = fx.C14_legitimate_revision()
        f, _ = ri(d)
        h = d["case"].history()
        self.assertIn("@s3.0", fr.derivable_everywhere(f))
        self.assertNotEqual(rf.content(h, "val.prior"), rf.content(h, "@s3.0"))

    def test_a_later_independent_adoption_of_an_influenced_value(self):
        d = fx.C33_standing_without_license()
        f, _ = ri(d)
        self.assertIn("@s4.0", fr.derivable_everywhere(f))
        self.assertEqual(lg.prospective_license(d["case"], d["iv"]).status,
                         lg.UNRESOLVED)

    def test_two_trajectories_to_one_endpoint_differ(self):
        d = fx.C11_same_endpoint()
        good, _ = rf.build(d["reflective"])
        bad, _ = rf.build(d["manipulated"])
        self.assertIn("@s3.0", fr.derivable_everywhere(good))
        self.assertNotIn("@s3.0", fr.derivable_everywhere(bad))
        self.assertEqual(rf.content(d["reflective"].history(), "@s3.0"),
                         rf.content(d["manipulated"].history(), "@s3.0"))


class TestNoBootstrap(unittest.TestCase):
    def test_a_laundered_warrant_is_refused_with_no_record_anywhere(self):
        f, _ = wt.build(LAUNDERED)
        reach = fr.derivable(f, "q:campaign")
        self.assertIn("w:charter", reach)
        self.assertNotIn("w:special", reach)
        self.assertNotIn("w:permit", reach)

    def test_the_same_refusal_in_a_reflective_integrity_record(self):
        f, _ = ri(fx.C10_manufactured_authorization())
        self.assertNotIn("@s3.0", fr.derivable(f, "E"))

    def test_a_proxy_does_not_launder(self):
        f, _ = ri(fx.C23_proxy())
        self.assertNotIn("@s3.0", fr.derivable_everywhere(f))

    def test_no_certified_ancestor_was_issued_by_a_challenged_exercise(self):
        for f, _ in (wt.build(LAUNDERED), wt.build(MERGE), wt.build(ATTACK),
                     wt.build(CLEANUP), wt.build(TWO),
                     ri(fx.C10_manufactured_authorization()),
                     ri(fx.C23_proxy()), ri(cases.record_cleanup()),
                     ri(cases.force_bearing())):
            for q in f.challenges:
                self.assertEqual(fr.thm_no_bootstrap(f, q), ())


class TestTheAccountLayerIsSeparate(unittest.TestCase):
    def test_an_unanswered_delegation_leaves_the_spine_clean(self):
        d = cases.delegated_custody(answered=False)
        f, acc = ri(d)
        self.assertEqual(fr.violations(f), {})
        self.assertIn(cases.DELEGABLE, fr.derivable_everywhere(f))
        self.assertFalse(fr.continuous(f, acc, d["disposed_root"]))
        self.assertEqual(fr.outstanding_below(f, acc, d["disposed_root"]),
                         (d["disposed_root"],))

    def test_the_same_in_a_register_with_no_record(self):
        f, acc = wt.build(wt.unanswered_delegation_register())
        self.assertEqual(fr.violations(f), {})
        moved = fr.thm_delegation_is_invisible_on_authorities(f, acc)
        self.assertEqual([t for t, _, _ in moved], ["act:handover"])
        ended = [a for a in acc.ends["act:handover"]]
        self.assertTrue(any(fr.condition(f, acc, a) == "outstanding"
                            for a in ended))

    def test_answering_it_changes_nothing_derivable(self):
        yes, _ = ri(cases.delegated_custody(True))
        no, _ = ri(cases.delegated_custody(False))
        self.assertEqual(fr.derivable_everywhere(yes),
                         fr.derivable_everywhere(no))

    def test_delegation_and_disposal_are_invisible_on_authorities(self):
        d = cases.delegated_custody(True)
        f, acc = ri(d)
        moved = fr.thm_delegation_is_invisible_on_authorities(f, acc)
        self.assertEqual(len(moved), 1)
        _, before, after = moved[0]
        self.assertNotEqual(before, after)
        s = cases.split_with_due_branch()
        g, gacc = ri(s)
        self.assertEqual([t.event_id for t, _, _ in
                          fr.thm_disposal_is_invisible_on_authorities(g, gacc)],
                         ["a:revoke"])

    def test_a_chain_certificate_cannot_carry_the_branch(self):
        d = cases.split_with_due_branch()
        f, acc = ri(d)
        self.assertIn(d["left"], fr.derivable_everywhere(f))
        self.assertFalse(fr.continuous(f, acc, d["base_root"]))
        self.assertEqual(fr.outstanding_below(f, acc, d["base_root"]),
                         (d["right_root"],))


class TestTheCertificate(unittest.TestCase):
    def test_a_certificate_verifies_and_a_forged_one_does_not(self):
        f, _ = ri(fx.C7b_delegated_authorization())
        cert = fr.certify(f, "@s3.0")
        self.assertIsNotNone(cert)
        self.assertTrue(fr.verify(f, cert))
        self.assertNotEqual(cert.stability, ())
        forged = fr.Cert(cert.base, "@s3.0", cert.steps, cert.challenges,
                         tuple((q, u, not v) for q, u, v in cert.stability))
        self.assertFalse(fr.verify(f, forged))

    def test_no_certificate_for_a_manufactured_authority(self):
        f, _ = ri(fx.C10_manufactured_authorization())
        self.assertIsNone(fr.certify(f, "@s3.0"))

    def test_no_certificate_for_the_laundered_licence_chain(self):
        f, _ = wt.build(ATTACK)
        self.assertIsNone(fr.certify(f, "w:y"))

    def test_the_verifier_recomputes_rather_than_reading_the_verdicts(self):
        src = inspect.getsource(fr.verify)
        self.assertIn("derivable_everywhere", src)
        self.assertIn("f.stable", src)

    def test_the_stability_half_is_a_claim_about_the_whole_record(self):
        src = inspect.getsource(rf.build)
        self.assertIn("en.excise(case", src)

    def test_no_verdict_is_assembled_across_two_challenges(self):
        src = inspect.getsource(fr.derivable_everywhere)
        self.assertIn("&=", src)
        self.assertNotIn("union", src)


if __name__ == "__main__":
    unittest.main()
