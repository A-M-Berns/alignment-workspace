"""The interface, run against two realizations that share no code.

Every axiom of the spine is checked on both, and every theorem is run on both.
The point of the second realization is that it imports nothing from the
normative architecture, so an axiom that held only because of how a ledger is
built would show up here as a failure rather than as a claim nobody tested.
"""
from __future__ import annotations

import ast
import inspect
import unittest

import frame as fr
import ri_frame as rf
import warrant as wt

import fixtures as fx
import legitimacy as lg
import cases


CLEAN = wt.clean_register()
LAUNDERED = wt.laundered_register()
MERGE = wt.merge_register()


def ri(d):
    return rf.build(d["case"])


class TestTheInterfaceIsNotAboutOurLedger(unittest.TestCase):
    def test_the_second_realization_imports_no_normative_architecture(self):
        """`warrant.py` imports `frame` and nothing else of ours.

        Read off the module's own import statements rather than off its text, so
        that naming a module in a comment does not pass or fail the check.
        """
        tree = ast.parse(inspect.getsource(wt))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported |= {n.name.split(".")[0] for n in node.names}
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertEqual(imported - {"__future__", "dataclasses", "typing"},
                         {"frame"})

    def test_the_spine_holds_in_a_register_of_warrants(self):
        for reg in (CLEAN, LAUNDERED, MERGE):
            f, _ = wt.build(reg)
            self.assertEqual(fr.violations(f), {})

    def test_the_spine_holds_in_a_reflective_integrity_record(self):
        for name, d in (("C7b", fx.C7b_delegated_authorization()),
                        ("C10", fx.C10_manufactured_authorization()),
                        ("C14", fx.C14_legitimate_revision()),
                        ("C33", fx.C33_standing_without_license())):
            with self.subTest(name):
                f, _ = ri(d)
                self.assertEqual(fr.violations(f), {})

    def test_both_realizations_run_the_same_theorems(self):
        for f, acc in (wt.build(CLEAN), ri(fx.C7b_delegated_authorization())):
            self.assertEqual(fr.thm_finite_lineage(f), ())
            self.assertEqual(fr.thm_visible_discontinuity(f, acc), ())
            for q in f.challenges:
                self.assertEqual(fr.thm_stability_of_derivable(f, q), ())
                self.assertEqual(fr.thm_no_bootstrap(f, q), ())


class TestLineageExistsWithoutLegitimacy(unittest.TestCase):
    """T2. The provenance is there whether or not anything is legitimate."""

    def test_every_authority_bottoms_out_in_the_base(self):
        for f, _ in (wt.build(LAUNDERED), ri(fx.C10_manufactured_authorization())):
            self.assertEqual(fr.thm_finite_lineage(f), ())

    def test_a_manufactured_authority_has_a_lineage_and_is_not_derivable(self):
        f, _ = ri(fx.C10_manufactured_authorization())
        manufactured = "@s3.0"
        self.assertIn(manufactured, f.current)
        self.assertTrue(fr.provenance(f, manufactured) & f.base)
        self.assertNotIn(manufactured, fr.derivable_everywhere(f))

    def test_the_issuer_is_unique_so_the_lineage_is_not_a_choice(self):
        for f, _ in (wt.build(CLEAN), ri(fx.C7b_delegated_authorization())):
            self.assertEqual(fr.l2_unique_issuance(f), ())


class TestNoBootstrap(unittest.TestCase):
    """T3. Step-local stability gives a statement about every ancestor."""

    def test_a_laundered_warrant_is_refused_with_no_record_anywhere(self):
        f, _ = wt.build(LAUNDERED)
        derivable = fr.derivable(f, "q:campaign")
        self.assertIn("w:charter", derivable)
        self.assertNotIn("w:special", derivable)
        self.assertNotIn("w:permit", derivable)

    def test_the_same_refusal_in_a_reflective_integrity_record(self):
        f, _ = ri(fx.C10_manufactured_authorization())
        self.assertNotIn("@s3.0", fr.derivable(f, "E"))

    def test_no_certified_ancestor_was_issued_by_a_challenged_exercise(self):
        for f, _ in (wt.build(LAUNDERED), wt.build(MERGE),
                     ri(fx.C10_manufactured_authorization()),
                     ri(fx.C23_proxy())):
            for q in f.challenges:
                self.assertEqual(fr.thm_no_bootstrap(f, q), ())

    def test_a_proxy_does_not_launder(self):
        """C23: another actor performs the installation and the record still says so."""
        f, _ = ri(fx.C23_proxy())
        self.assertNotIn("@s3.0", fr.derivable_everywhere(f))

    def test_all_of_src_and_not_one_of_it(self):
        """The merge register separates the two rules; the RI realization cannot.

        An act revoking a manufactured warrant and an earned one, relying only on
        clean findings. Under `all` the successor is refused; under `one of` it is
        admitted.
        """
        f, _ = wt.build(MERGE)
        q = "q:campaign"
        self.assertNotIn("w:merged", fr.derivable(f, q))

        out = set(f.base)
        changed = True
        while changed:
            changed = False
            for t in sorted(f.exercises):
                if fr.certified(f, q, t) and (f.src[t] & out or not f.src[t]):
                    if f.tgt[t] - out:
                        out |= f.tgt[t]
                        changed = True
        self.assertIn("w:merged", out)


class TestContentIndependence(unittest.TestCase):
    """T4. Recognition transports without endorsing what is recognized."""

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
        """C33. The value the influence produced ends up in force, legitimately."""
        d = fx.C33_standing_without_license()
        f, _ = ri(d)
        self.assertIn("@s4.0", fr.derivable_everywhere(f))
        self.assertEqual(lg.prospective_license(d["case"], d["iv"]).status,
                         lg.UNRESOLVED)

    def test_two_trajectories_to_one_endpoint_differ(self):
        """C11. The cognitive endpoint is the same and the derivability is not."""
        d = fx.C11_same_endpoint()
        good, _ = rf.build(d["reflective"])
        bad, _ = rf.build(d["manipulated"])
        self.assertIn("@s3.0", fr.derivable_everywhere(good))
        self.assertNotIn("@s3.0", fr.derivable_everywhere(bad))
        self.assertEqual(rf.content(d["reflective"].history(), "@s3.0"),
                         rf.content(d["manipulated"].history(), "@s3.0"))


class TestWhereTheRealizationIsConditional(unittest.TestCase):
    """L3 is the axiom Reflective Integrity has to work for."""

    def test_a_prestate_reading_schema_refutes_issuance_stability(self):
        d = fx.C28_prestate_reading_schema(True)
        f, _ = ri(d)
        self.assertFalse(rf.prestate_blind(d["case"]))
        self.assertNotEqual(fr.l3_issuance_stability(f), ())

    def test_the_blind_arm_satisfies_it(self):
        d = fx.C28_prestate_reading_schema(False)
        f, _ = ri(d)
        self.assertTrue(rf.prestate_blind(d["case"]))
        self.assertEqual(fr.l3_issuance_stability(f), ())

    def test_origin_necessity_needs_no_such_hypothesis(self):
        """L3' holds in the reading arm too: it rests on the id scheme alone."""
        f, _ = ri(fx.C28_prestate_reading_schema(True))
        self.assertEqual(fr.l3p_origin_necessity(f), ())

    def test_the_challenge_set_is_read_off_the_reasons_not_the_replay(self):
        src = inspect.getsource(rf.challenged_exercises)
        self.assertIn("derivation.leaves", src)
        self.assertNotIn("survives_excision", src)

    def test_the_challenge_bites(self):
        for d in (fx.C10_manufactured_authorization(), fx.C22_inquiry_laundering(),
                  fx.C23_proxy()):
            f, _ = ri(d)
            self.assertNotEqual(f.chal[f.challenges[0]], frozenset())
            self.assertEqual(fr.l4_challenge_bite(f), ())


class TestTheAccountLayerIsSeparate(unittest.TestCase):
    """What answerability adds, and what it does not."""

    def test_an_unanswered_delegation_leaves_the_spine_clean(self):
        d = cases.delegated_custody(answered=False)
        f, acc = ri(d)
        self.assertEqual(fr.violations(f), {})
        self.assertIn(cases.DELEGABLE, fr.derivable_everywhere(f))
        self.assertFalse(fr.continuous(f, acc, d["disposed_root"]))
        self.assertEqual(fr.outstanding_below(f, acc, d["disposed_root"]),
                         (d["disposed_root"],))

    def test_answering_it_restores_continuity_and_changes_nothing_else(self):
        yes, acc_y = ri(cases.delegated_custody(True))
        no, acc_n = ri(cases.delegated_custody(False))
        self.assertEqual(fr.derivable_everywhere(yes), fr.derivable_everywhere(no))
        d = cases.delegated_custody(True)
        self.assertTrue(fr.continuous(*ri(d), d["disposed_root"]))

    def test_delegation_is_invisible_on_the_authority_graph(self):
        d = cases.delegated_custody(True)
        f, acc = ri(d)
        moves = fr.thm_delegation_is_invisible_on_authorities(f, acc)
        self.assertEqual(len(moves), 1)
        _, before, after = moves[0]
        self.assertNotEqual(before, after)
        self.assertEqual(f.issued(d["event"]), frozenset())

    def test_disposal_is_invisible_on_the_authority_graph(self):
        d = cases.split_with_due_branch()
        f, acc = ri(d)
        disposals = fr.thm_disposal_is_invisible_on_authorities(f, acc)
        self.assertEqual([t for t, _, _ in disposals], ["a:revoke"])
        self.assertEqual(f.tgt["a:revoke"], frozenset())

    def test_a_chain_certificate_cannot_carry_the_branch(self):
        """A lineage to one successor says nothing about the other's account."""
        d = cases.split_with_due_branch()
        f, acc = ri(d)
        self.assertIn(d["left"], fr.derivable_everywhere(f))
        steps = fr.derivation(f, f.challenges[0] if f.challenges else None,
                              d["left"]) or ()
        touched = {a for s in steps for a in acc.ends[s.exercise]}
        self.assertTrue(all(acc.answered(a) for a in touched))
        self.assertFalse(fr.continuous(f, acc, d["base_root"]))
        self.assertEqual(fr.outstanding_below(f, acc, d["base_root"]),
                         (d["right_root"],))

    def test_visibility_is_a_theorem_of_the_account_layer(self):
        for d in (cases.delegated_custody(False), cases.split_with_due_branch(),
                  fx.C7b_delegated_authorization()):
            f, acc = ri(d)
            self.assertEqual(fr.account_violations(f, acc), {})
            self.assertEqual(fr.thm_visible_discontinuity(f, acc), ())
        f, acc = wt.build(CLEAN)
        self.assertEqual(fr.thm_visible_discontinuity(f, acc), ())


class TestTheCertificate(unittest.TestCase):
    def test_a_certificate_verifies_and_a_forged_target_does_not(self):
        f, acc = ri(fx.C7b_delegated_authorization())
        cert = fr.certify(f, "@s3.0")
        self.assertIsNotNone(cert)
        self.assertTrue(fr.verify(f, cert))
        self.assertNotEqual(cert.stability, ())
        forged = fr.Cert(cert.base, "@s3.0", cert.steps, cert.challenges,
                         tuple((q, u, not v) for q, u, v in cert.stability))
        self.assertFalse(fr.verify(f, forged))

    def test_no_certificate_exists_for_a_manufactured_authority(self):
        f, _ = ri(fx.C10_manufactured_authorization())
        self.assertIsNone(fr.certify(f, "@s3.0"))

    def test_the_verifier_recomputes_rather_than_reading_the_verdicts(self):
        src = inspect.getsource(fr.verify)
        self.assertIn("derivable_everywhere", src)
        self.assertIn("f.stable", src)

    def test_the_stability_half_is_a_claim_about_the_whole_record(self):
        """In the RI realization every stability judgment replays the record."""
        src = inspect.getsource(rf.build)
        self.assertIn("en.excise(case", src)
        self.assertIn("lg.survives_excision(case", src)

    def test_no_verdict_is_assembled_across_two_challenges(self):
        """`derivable_everywhere` intersects per-challenge verdicts; it never
        excises a union, which the excision operator does not support."""
        src = inspect.getsource(fr.derivable_everywhere)
        self.assertIn("&=", src)
        self.assertNotIn("union", src)


if __name__ == "__main__":
    unittest.main()
