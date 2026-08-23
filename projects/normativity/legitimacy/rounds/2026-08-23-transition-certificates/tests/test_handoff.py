"""Continuation fixtures: the frozen waist and its two consumer contracts.

Covers the `born` layer move, the schema-use constructor, the left (inquiry)
and right (frontier) handoff fixtures including the quantitative content
demonstration, and the notebook/stance/diary collapse witnesses.
"""
from __future__ import annotations

import unittest

from reason_state import (
    App,
    Atom,
    ReasonState,
    Receipt,
    Reliance,
    bearing,
    conflict,
    enabled,
    lost_basis,
    neg,
    provenance_manifest,
    reasons,
)
from transitions import Certificate, check_certificate, transition_lost_basis
from test_certificates import standard_acts


class TestTemporalProvenanceLayer(unittest.TestCase):
    """Part I.A of the continuation: birth is ledger provenance, not a fact
    about the reason object."""

    def test_occurrences_carry_no_birth_field(self):
        state = ReasonState()
        occ = state.mint("e", {Atom("p")}, Atom("q"), at=3)
        self.assertFalse(hasattr(occ, "born"))
        self.assertEqual(
            set(occ.__dataclass_fields__), {"ident", "sources", "target", "applied_as"}
        )

    def test_prefix_query_answers_the_temporal_question(self):
        state = ReasonState()
        state.mint("e", {Atom("p")}, Atom("q"), at=3)
        self.assertTrue(state.existed_before("e", 5))
        self.assertFalse(state.existed_before("e", 3))
        self.assertFalse(state.existed_before("missing", 5))

    def test_strict_pre_state_citation_still_holds_through_the_prefix(self):
        # The subtraction witness for the temporal capability itself: the
        # self-minted-basis attack is refused via existed_before, so the
        # field was redundant but the prefix question is load-bearing.
        state = ReasonState()
        state.mint("fresh", {Atom("p")}, Atom("q"), at=5)
        cert = Certificate("m", "belief-revision", 5, ("fresh",), "a3")
        result = check_certificate(
            state, standard_acts(), {}, cert, frozenset({Atom("p")}), {}
        )
        self.assertIn(("posterior-basis", "fresh"), result.failures)


class TestSchemaUseConstructor(unittest.TestCase):
    """Part I.B: the enforcing constructor makes the invariant structural."""

    def test_constructor_inserts_applicability_and_provenance_together(self):
        state = ReasonState()
        occ = state.mint_schema_use(
            "e", {Atom("bird"), Receipt("r1")}, "sigma", "c", 4, Atom("flies"), at=4
        )
        self.assertIn(App("sigma", "c", 4), occ.claim_sources())
        self.assertEqual(occ.applied_as, frozenset({("sigma", "c", 4)}))

    def test_constructor_agrees_with_manual_minting(self):
        one, two = ReasonState(), ReasonState()
        a = one.mint_schema_use("e", {Atom("g")}, "s", "c", 1, Atom("t"), at=1)
        b = two.mint(
            "e", {Atom("g"), App("s", "c", 1)}, Atom("t"), at=1,
            applied_as={("s", "c", 1)},
        )
        self.assertEqual(a, b)


class TestLeftHandoff(unittest.TestCase):
    """Part V: the inquiry contract — what enters, and what pressure looks
    like from the waist's side."""

    def test_investigation_round_trip(self):
        # world → L → new reason occurrence → pressure on B. Inquiry adds a
        # receipt and an interpretation occurrence; the pressure is visible
        # as new bearing, and the stance itself is untouched by the additions.
        state = ReasonState()
        stance = frozenset({App("assay", "c", 6)})
        transcript_before = frozenset()
        self.assertEqual(bearing(state, stance, transcript_before), frozenset())
        transcript_after = frozenset({"lab-result"})
        state.mint_schema_use(
            "interpret", {Receipt("lab-result")}, "assay", "c", 6,
            Atom("sample-positive"), at=6,
        )
        self.assertEqual(
            bearing(state, stance, transcript_after),
            frozenset({Atom("sample-positive")}),
        )
        self.assertNotIn(Atom("sample-positive"), stance)

    def test_docketable_conditions_are_query_level(self):
        # Basis loss and exposed conflict are inquiry triggers the left side
        # reads off the queries; neither is a stored status on any reason.
        state = ReasonState()
        state.mint_schema_use(
            "e", {Atom("w")}, "s", "c", 1, Atom("t"), at=1
        )
        log = (Reliance("undertake-1", "e", 1),)
        withdrawn = frozenset({Atom("w")})  # applicability not adopted
        self.assertEqual(lost_basis(state, log, withdrawn, frozenset()), log)
        occ = state.occurrence("e")
        self.assertFalse(hasattr(occ, "defeated"))
        self.assertFalse(hasattr(occ, "status"))


class TestRightHandoff(unittest.TestCase):
    """Part VI: the frontier contract — quantitative content, certified
    reliance, and the two-sorted provenance manifest."""

    def setUp(self):
        self.v = Atom("P(rain|front)>=4/5")
        self.state = ReasonState()
        self.state.mint_schema_use(
            "freq",
            {Receipt("station-log"), Atom("frontal-pattern")},
            "frequency-inference", "c", 3,
            self.v,
            at=3,
        )

    def test_quantitative_content_with_qualitative_endorsement(self):
        # The constraint's coefficients live inside the content; endorsement
        # is membership, not a weight.
        pre = frozenset({Atom("frontal-pattern"), App("frequency-inference", "c", 3)})
        self.assertEqual(
            reasons(self.state, self.v, pre, frozenset({"station-log"})), ("freq",)
        )
        endorsed = pre | {self.v}
        self.assertIn(self.v, endorsed)

    def test_certified_reliance_on_quantitative_content(self):
        pre = frozenset({Atom("frontal-pattern"), App("frequency-inference", "c", 3)})
        cert = Certificate("m", "belief-revision", 5, ("freq",), "a3")
        result = check_certificate(
            self.state, standard_acts(), {}, cert, pre, {"station-log": 2}
        )
        self.assertTrue(result.valid, result.failures)
        after_correction = frozenset({Atom("frontal-pattern")})
        self.assertEqual(
            transition_lost_basis(self.state, cert, after_correction, frozenset({"station-log"})),
            ("freq",),
        )

    def test_provenance_manifest_splits_settled_from_revisable(self):
        receipts, claims = provenance_manifest(self.state, ("freq",))
        self.assertEqual(receipts, frozenset({"station-log"}))
        self.assertEqual(
            claims,
            frozenset({Atom("frontal-pattern"), App("frequency-inference", "c", 3)}),
        )

    def test_manifest_frontier_excludes_supplied_targets(self):
        # Chained citation: a cited occurrence's target is not an open claim
        # dependency of the set that supplies it.
        self.state.mint_schema_use(
            "act-on-it", {self.v}, "decision", "c", 4, Atom("respond:carry-umbrella"),
            at=4,
        )
        receipts, claims = provenance_manifest(self.state, ("freq", "act-on-it"))
        self.assertEqual(receipts, frozenset({"station-log"}))
        self.assertNotIn(self.v, claims)
        self.assertIn(App("decision", "c", 4), claims)


class TestNotebookStanceDiarySplit(unittest.TestCase):
    """Part VII: minimal failure witnesses for each attempted collapse."""

    def test_collapsing_ledger_into_stance_loses_the_loss_report(self):
        # If the graph kept only currently-enabled reasoning, a disabled
        # occurrence would be gone and its reliance loss unreportable. The
        # witness simulates the pruned store: the same log against a store
        # without the occurrence yields an empty transition report, so the
        # loss became invisible exactly when it mattered.
        full = ReasonState()
        full.mint_schema_use("e", {Atom("w")}, "s", "c", 1, Atom("t"), at=1)
        cert = Certificate("m", "belief-revision", 3, ("e",), "a3")
        withdrawn = frozenset({Atom("w")})
        self.assertEqual(transition_lost_basis(full, cert, withdrawn, frozenset()), ("e",))
        pruned = ReasonState()  # the store as a stance-only graph would leave it
        self.assertEqual(transition_lost_basis(pruned, cert, withdrawn, frozenset()), ())

    def test_collapsing_stance_into_record_breaks_hypothetical_queries(self):
        # Queries take an arbitrary candidate stance with no record event
        # behind it; a stance derivable only from the diary would need a fake
        # record entry per hypothetical.
        state = ReasonState()
        state.mint("e", {Atom("p")}, Atom("q"), at=1)
        hypothetical = frozenset({Atom("p")})
        self.assertTrue(enabled(state, "e", hypothetical, frozenset()))

    def test_collapsing_endorsement_into_the_graph_makes_support_endorsement(self):
        # If endorsement were a graph fact, having a live reason would be
        # endorsing its conclusion. The witness is their divergence.
        state = ReasonState()
        state.mint("e", {Atom("p")}, Atom("q"), at=1)
        stance = frozenset({Atom("p")})
        self.assertIn(Atom("q"), bearing(state, stance, frozenset()))
        self.assertNotIn(Atom("q"), stance)

    def test_conflicted_view_remains_neutral_in_the_ledger(self):
        # The ledger holds both sides of a conflict without either being
        # privileged; only a stance takes a side.
        state = ReasonState()
        p = Atom("p")
        state.mint("for", {Atom("a")}, p, at=1)
        state.mint("against", {Atom("b")}, neg(p), at=1)
        everything = frozenset({Atom("a"), Atom("b")})
        self.assertEqual(reasons(state, p, everything, frozenset()), ("for",))
        self.assertEqual(reasons(state, neg(p), everything, frozenset()), ("against",))
        self.assertTrue(conflict(frozenset({p, neg(p)}), everything))


if __name__ == "__main__":
    unittest.main()
