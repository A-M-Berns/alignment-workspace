"""Parts II–IV fixtures: the reason-accounted transition certificate."""
from __future__ import annotations

import unittest

from reason_state import (
    App,
    Atom,
    Incomp,
    Inst,
    ReasonState,
    Receipt,
    enabled,
    neg,
    reasons,
)
from transitions import (
    AuthorityAct,
    Certificate,
    applicability_provenance,
    check_certificate,
    genealogy_errors,
    licensed,
    pre_transcript,
    transition_lost_basis,
)


def standard_acts():
    """Seed plus a diamond: s0 licenses a1 and a2, which jointly license a3
    (dispatch fixture 10)."""
    return {
        "s0": AuthorityAct("s0", 0, seed=True, scope=frozenset({"rule-amendment"})),
        "a1": AuthorityAct("a1", 1, license_parents=("s0",),
                           scope=frozenset({"belief-revision", "schema-reclassification"})),
        "a2": AuthorityAct("a2", 2, license_parents=("s0",),
                           scope=frozenset({"practical-undertaking"})),
        "a3": AuthorityAct("a3", 3, license_parents=("a1", "a2"),
                           scope=frozenset({"belief-revision", "inquiry-launch"})),
    }


class TestOrdinaryCertificate(unittest.TestCase):
    def setUp(self):
        self.state = ReasonState()
        self.state.mint(
            "e1",
            {Atom("witness"), App("testimony", "c", 2), Receipt("r1")},
            Atom("liable"),
            born=2,
            instantiates={("testimony", "c", 2)},
        )
        self.acts = standard_acts()
        self.arrivals = {"r1": 1}
        self.pre_stance = frozenset({Atom("witness"), App("testimony", "c", 2)})
        self.cert = Certificate(
            move="m1", kind="belief-revision", index=5,
            basis=("e1",), license="a3",
        )

    def test_valid_certificate(self):
        result = check_certificate(
            self.state, self.acts, {}, self.cert, self.pre_stance, self.arrivals
        )
        self.assertTrue(result.valid, result.failures)
        self.assertTrue(
            licensed(self.state, self.acts, {}, self.cert, self.pre_stance, self.arrivals)
        )

    def test_applicability_provenance_is_derived_from_structure(self):
        self.assertEqual(
            applicability_provenance(self.state, self.cert),
            frozenset({App("testimony", "c", 2)}),
        )

    def test_diamond_genealogy_is_valid(self):
        self.assertEqual(genealogy_errors(self.acts), ())

    def test_receipt_is_reproducible_after_later_activity(self):
        before = check_certificate(
            self.state, self.acts, {}, self.cert, self.pre_stance, self.arrivals
        ).receipt
        self.state.mint("later", {Atom("new")}, Atom("other"), born=9)
        after = check_certificate(
            self.state, self.acts, {}, self.cert, self.pre_stance, self.arrivals
        ).receipt
        self.assertEqual(before, after)


class TestCitationNecessity(unittest.TestCase):
    """Dispatch fixtures 4 and 5: particular occurrences, not conclusions."""

    def setUp(self):
        self.state = ReasonState()
        src = {Atom("witness"), App("testimony", "c", 2)}
        self.state.mint("e1", src, Atom("liable"), born=2,
                        instantiates={("testimony", "c", 2)})
        self.state.mint("e2", src, Atom("liable"), born=3,
                        instantiates={("testimony", "c", 2)})
        self.acts = standard_acts()
        self.cert = Certificate("m1", "belief-revision", 5, ("e1",), "a3")

    def test_identical_content_distinct_history(self):
        one, two = self.state.occurrence("e1"), self.state.occurrence("e2")
        self.assertEqual((one.sources, one.target), (two.sources, two.target))
        # Conclusion- or content-level citation cannot separate them; the
        # certificate does.
        lost = transition_lost_basis(self.state, self.cert, frozenset(), frozenset())
        self.assertEqual(lost, ("e1",))

    def test_alternative_support_does_not_silence_basis_loss(self):
        self.state.mint(
            "alt",
            {Atom("forensics"), App("forensic", "c", 7)},
            Atom("liable"),
            born=7,
            instantiates={("forensic", "c", 7)},
        )
        now = frozenset({Atom("witness"), Atom("forensics"), App("forensic", "c", 7)})
        # Conclusion-level monitoring sees nothing wrong: a live reason for
        # the conclusion exists. Occurrence-level monitoring reports the loss.
        self.assertEqual(reasons(self.state, Atom("liable"), now, frozenset()), ("alt",))
        self.assertEqual(
            transition_lost_basis(self.state, self.cert, now, frozenset()), ("e1",)
        )


class TestPreStateDiscipline(unittest.TestCase):
    """Requirement B and the non-laundering attacks (fixtures 6 and 7)."""

    def setUp(self):
        self.state = ReasonState()
        self.acts = standard_acts()

    def test_transition_cannot_mint_its_own_basis(self):
        self.state.mint("fresh", {Atom("p")}, Atom("q"), born=5)
        cert = Certificate("m", "belief-revision", 5, ("fresh",), "a3")
        result = check_certificate(
            self.state, self.acts, {}, cert, frozenset({Atom("p")}), {}
        )
        self.assertFalse(result.valid)
        self.assertIn(("posterior-basis", "fresh"), result.failures)

    def test_transition_cannot_mint_its_own_license(self):
        self.state.mint("e", {Atom("p")}, Atom("q"), born=1)
        acts = dict(self.acts)
        acts["self"] = AuthorityAct("self", 5, license_parents=("s0",),
                                    scope=frozenset({"belief-revision"}))
        cert = Certificate("m", "belief-revision", 5, ("e",), "self")
        result = check_certificate(self.state, acts, {}, cert, frozenset({Atom("p")}), {})
        self.assertFalse(result.valid)
        self.assertIn(("posterior-license", "self"), result.failures)

    def test_mutual_licensing_is_refused_by_strict_priority(self):
        self.state.mint("e", {Atom("p")}, Atom("q"), born=1)
        acts = {
            "s0": AuthorityAct("s0", 0, seed=True),
            "b1": AuthorityAct("b1", 5, license_parents=("b2",),
                               scope=frozenset({"belief-revision"})),
            "b2": AuthorityAct("b2", 5, license_parents=("b1",),
                               scope=frozenset({"belief-revision"})),
        }
        errs = genealogy_errors(acts)
        self.assertIn("non-prior-parent:b1:b2", errs)
        self.assertIn("non-prior-parent:b2:b1", errs)
        cert = Certificate("m", "belief-revision", 6, ("e",), "b1")
        result = check_certificate(self.state, acts, {}, cert, frozenset({Atom("p")}), {})
        self.assertFalse(result.valid)

    def test_no_self_grounding_clause_exists_yet_the_attacks_fail(self):
        # Postulate collapse: the checker has no dedicated self-grounding
        # rule; every self-certification attack dies on strict priority or
        # genealogy. The failure codes prove which clause did the work.
        self.state.mint("fresh", {Atom("p")}, Atom("q"), born=5)
        cert = Certificate("m", "belief-revision", 5, ("fresh",), "a3")
        result = check_certificate(
            self.state, self.acts, {}, cert, frozenset({Atom("p")}), {}
        )
        codes = {code for code, _ in result.failures}
        self.assertEqual(codes, {"posterior-basis"})

    def test_pre_state_transcript_is_strict(self):
        self.state.mint(
            "e", {Atom("p"), Receipt("late")}, Atom("q"), born=2
        )
        arrivals = {"late": 7}
        early = Certificate("m", "belief-revision", 5, ("e",), "a3")
        result = check_certificate(
            self.state, self.acts, {}, early, frozenset({Atom("p")}), arrivals
        )
        self.assertFalse(result.valid)
        self.assertIn(("basis-not-enabled", ("e", "late")), result.failures)
        late = Certificate("m2", "belief-revision", 9, ("e",), "a3")
        self.assertTrue(
            check_certificate(
                self.state, self.acts, {}, late, frozenset({Atom("p")}), arrivals
            ).valid
        )

    def test_new_interpretation_cannot_retroactively_license(self):
        # The check is a function of the frozen pre-state inputs; a receipt
        # arriving later, or a richer current stance, does not flip the old
        # verdict on re-derivation.
        self.state.mint("e", {Atom("p"), Receipt("late")}, Atom("q"), born=2)
        cert = Certificate("m", "belief-revision", 5, ("e",), "a3")
        pre = frozenset({Atom("p")})
        first = check_certificate(self.state, self.acts, {}, cert, pre, {"late": 7})
        self.assertFalse(first.valid)
        again = check_certificate(self.state, self.acts, {}, cert, pre, {"late": 7})
        self.assertEqual(first, again)
        self.assertNotIn("late", pre_transcript({"late": 7}, 5))


class TestGroundsVersusLicense(unittest.TestCase):
    """Requirement D and dispatch fixtures 11, 12, 15."""

    def setUp(self):
        self.state = ReasonState()
        self.state.mint(
            "e1",
            {Atom("witness"), App("testimony", "c", 2)},
            Atom("liable"),
            born=2,
            instantiates={("testimony", "c", 2)},
        )
        self.acts = standard_acts()
        self.pre = frozenset({Atom("witness"), App("testimony", "c", 2)})

    def test_valid_genealogy_absent_grounds(self):
        cert = Certificate("m", "belief-revision", 5, ("e1",), "a3")
        result = check_certificate(self.state, self.acts, {}, cert, frozenset(), {})
        codes = {code for code, _ in result.failures}
        self.assertEqual(codes, {"basis-not-enabled"})

    def test_excellent_grounds_without_authority(self):
        cert = Certificate("m", "rule-amendment", 5, ("e1",), "a3")
        result = check_certificate(self.state, self.acts, {}, cert, self.pre, {})
        codes = {code for code, _ in result.failures}
        self.assertEqual(codes, {"license-scope"})

    def test_conflation_kill(self):
        # A checker that pools basis, license, and lineage into one generic
        # support set accepts an ordinary reason occurrence standing in for
        # authority. The repaired checker refuses it as an unknown license.
        cert = Certificate("m", "belief-revision", 5, ("e1",), "e1")

        def conflated_check(state, acts, cert, stance, arrivals):
            cited = set(cert.basis) | {cert.license} | set(cert.consumed)
            return all(
                (state.has(i) and enabled(state, i, stance, pre_transcript(arrivals, cert.index)))
                or i in acts
                for i in cited
            )

        self.assertTrue(conflated_check(self.state, self.acts, cert, self.pre, {}))
        result = check_certificate(self.state, self.acts, {}, cert, self.pre, {})
        self.assertFalse(result.valid)
        self.assertIn(("unknown-license", "e1"), result.failures)

    def test_lineage_must_cite_existing_prior_commitments(self):
        commitments = {"ell-1": 3}
        good = Certificate("m", "practical-undertaking", 5, ("e1",), "a2",
                           consumed=("ell-1",))
        self.assertTrue(
            check_certificate(self.state, self.acts, commitments, good, self.pre, {}).valid
        )
        bad = Certificate("m2", "practical-undertaking", 5, ("e1",), "a2",
                          consumed=("ell-9",))
        result = check_certificate(self.state, self.acts, commitments, bad, self.pre, {})
        self.assertIn(("unknown-lineage", "ell-9"), result.failures)


class TestBasisLossAfterCertification(unittest.TestCase):
    """Requirement F and dispatch fixtures 5, 8, and the persistence and
    incompatibility laundering attacks."""

    def setUp(self):
        self.state = ReasonState()
        self.state.mint(
            "e1",
            {Atom("witness"), App("testimony", "c", 3)},
            Atom("liable"),
            born=3,
            instantiates={("testimony", "c", 3)},
        )
        self.acts = standard_acts()
        self.pre = frozenset({Atom("witness"), App("testimony", "c", 3)})
        self.cert = Certificate("m", "belief-revision", 5, ("e1",), "a3")
        assert check_certificate(self.state, self.acts, {}, self.cert, self.pre, {}).valid

    def test_schema_reclassification_alone_does_not_lose_basis(self):
        # Dispatch fixture 8: after a split, the organization claims move and
        # the certified basis stands; only withdrawing the cited staged
        # applicability disables it.
        reorganized = self.pre | {neg(Inst("e1", "testimony")), Inst("e1", "tau1")}
        self.assertEqual(
            transition_lost_basis(self.state, self.cert, reorganized, frozenset()), ()
        )
        withdrawn = frozenset({Atom("witness")})
        self.assertEqual(
            transition_lost_basis(self.state, self.cert, withdrawn, frozenset()), ("e1",)
        )

    def test_later_persistence_does_not_launder_the_relied_on_stage(self):
        # The transition relied on applicability at stage 3. A later carry to
        # stage 4 does not restore the withdrawn stage-3 claim.
        laundered = frozenset({Atom("witness"), App("testimony", "c", 4)})
        self.assertEqual(
            transition_lost_basis(self.state, self.cert, laundered, frozenset()), ("e1",)
        )

    def test_defeated_incompatibility_underlying_a_transition(self):
        clash = Incomp(frozenset({Atom("attend-m1"), Atom("attend-m2")}))
        self.state.mint(
            "resolve",
            {clash, App("conflict-resolution", "c", 4)},
            Atom("respond:decline-m2"),
            born=4,
            instantiates={("conflict-resolution", "c", 4)},
        )
        pre = frozenset({clash, App("conflict-resolution", "c", 4)})
        cert = Certificate("m2", "practical-undertaking", 5, ("resolve",), "a2")
        self.assertTrue(check_certificate(self.state, self.acts, {}, cert, pre, {}).valid)
        after_defeat = frozenset({App("conflict-resolution", "c", 4)})
        self.assertEqual(
            transition_lost_basis(self.state, cert, after_defeat, frozenset()),
            ("resolve",),
        )


class TestCheckerDoesNotAdjudicate(unittest.TestCase):
    """The certificate licenses the citation discipline, not stance
    coherence: a licitly certified transition into a criticizable stance is
    accepted and left to the criticism machinery."""

    def test_certified_transition_into_conflict(self):
        state = ReasonState()
        state.mint(
            "e",
            {Atom("invited"), App("invitation", "c", 1)},
            Atom("respond:attend-m2"),
            born=1,
            instantiates={("invitation", "c", 1)},
        )
        acts = standard_acts()
        clash = Incomp(frozenset({Atom("respond:attend-m1"), Atom("respond:attend-m2")}))
        pre = frozenset({Atom("invited"), App("invitation", "c", 1),
                         Atom("respond:attend-m1"), clash})
        cert = Certificate("m", "practical-undertaking", 3, ("e",), "a2")
        self.assertTrue(check_certificate(state, acts, {}, cert, pre, {}).valid)


class TestFrozenCitationLocality(unittest.TestCase):
    """The loss report is a function of the cited identities' own sources:
    exhaustively checked over every stance on a small claim universe."""

    def test_sweep(self):
        state = ReasonState()
        a, b, w = Atom("a"), Atom("b"), App("sigma", "c", 1)
        state.mint("e1", {a, w}, Atom("t1"), born=1, instantiates={("sigma", "c", 1)})
        state.mint("e2", {b}, Atom("t2"), born=1)
        cert = Certificate("m", "belief-revision", 3, ("e1", "e2"), "a3")
        universe = [a, b, w, Atom("noise")]
        for mask in range(1 << len(universe)):
            stance = frozenset(c for i, c in enumerate(universe) if mask >> i & 1)
            expected = tuple(
                ident
                for ident in ("e1", "e2")
                if not state.occurrence(ident).claim_sources() <= stance
            )
            self.assertEqual(
                transition_lost_basis(state, cert, stance, frozenset()), expected
            )


class TestIndependenceWitnesses(unittest.TestCase):
    """Part III: each principle has a minimal failure witness without it."""

    def test_without_strict_priority_self_certification_passes(self):
        state = ReasonState()
        state.mint("fresh", {Atom("p")}, Atom("q"), born=5)
        acts = standard_acts()
        cert = Certificate("m", "belief-revision", 5, ("fresh",), "a3")

        def lax_check(state, acts, cert, stance, arrivals):
            # The repaired checker minus the posterior-* clauses.
            return all(
                state.has(i) and enabled(state, i, stance, pre_transcript(arrivals, cert.index))
                for i in cert.basis
            ) and cert.license in acts and cert.kind in acts[cert.license].scope

        self.assertTrue(lax_check(state, acts, cert, frozenset({Atom("p")}), {}))
        self.assertFalse(
            check_certificate(state, acts, {}, cert, frozenset({Atom("p")}), {}).valid
        )

    def test_without_occurrence_citation_the_loss_is_invisible(self):
        # Monitoring conclusions instead of cited occurrences misses the
        # substitution in TestCitationNecessity; restated here as the
        # continuation principle's witness.
        state = ReasonState()
        state.mint("e1", {Atom("w"), App("s", "c", 1)}, Atom("t"), born=1,
                   instantiates={("s", "c", 1)})
        state.mint("alt", {Atom("f")}, Atom("t"), born=2)
        now = frozenset({Atom("f")})
        self.assertEqual(reasons(state, Atom("t"), now, frozenset()), ("alt",))
        cert = Certificate("m", "belief-revision", 3, ("e1",), "a3")
        self.assertEqual(transition_lost_basis(state, cert, now, frozenset()), ("e1",))


if __name__ == "__main__":
    unittest.main()
