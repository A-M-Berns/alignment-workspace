"""Addendum fixtures: the narrow-waist closure phase.

Subtraction witnesses that removing a surviving primitive loses a
distinction, and the microhistory classes from the representation-
completeness search that earlier suites did not already cover. Every test
asks only whether the content and dependency structure is expressible and
totally queryable — never what the correct response is.
"""
from __future__ import annotations

import unittest

from reason_state import (
    App,
    Atom,
    Incomp,
    ReasonState,
    Receipt,
    bearing,
    enabled,
    incompatible,
    neg,
    reasons,
    rebuts,
    undercuts,
)


class TestSubtractionWitnesses(unittest.TestCase):
    """Prosecution by subtraction: each removal has a concrete loss."""

    def test_extensional_identity_collapses_answerability(self):
        # Removing occurrence identity in favor of (sources, target): two
        # historically distinct applications become one object, so a reliance
        # log can no longer say which was relied on. The witness is that the
        # extensional key is identical while the identities differ.
        state = ReasonState()
        src = {Atom("w"), App("s", "c", 1)}
        e1 = state.mint("e1", src, Atom("t"), at=1, applied_as={("s", "c", 1)})
        e2 = state.mint("e2", src, Atom("t"), at=4, applied_as={("s", "c", 1)})
        self.assertEqual((e1.sources, e1.target), (e2.sources, e2.target))
        self.assertNotEqual(e1, e2)

    def test_compiling_hyperedges_to_binary_edges_is_nonconservative(self):
        # Removing hyper-sources by routing {a, b} through an invented
        # conjunction vertex changes enabledness: the original occurrence is
        # live once the learner holds a and b, while the compiled main edge
        # waits on a conjunction claim the learner never adopted. Keeping
        # them synchronized would be a hidden bookkeeping policy.
        a, b, conj = Atom("a"), Atom("b"), Atom("a-and-b")
        original = ReasonState()
        original.mint("e", {a, b}, Atom("t"), at=1)
        compiled = ReasonState()
        compiled.mint("intro", {a, b}, conj, at=1)
        compiled.mint("main", {conj}, Atom("t"), at=1)
        stance = frozenset({a, b})
        self.assertTrue(enabled(original, "e", stance, frozenset()))
        self.assertFalse(enabled(compiled, "main", stance, frozenset()))
        # The compilation also invents a reason application ("intro") the
        # practice never performed, which a reliance log could then cite.
        self.assertEqual(len(compiled.occurrences()), 2)

    def test_floor_removal_would_make_correction_contingent(self):
        # With all incompatibility revisable, App and its negation conflict
        # only under an adopted norm; at the empty stance nothing would mark
        # a correction as a correction. The floor supplies exactly that one
        # conflict without obliging any response.
        early = App("sigma", "c", 3)
        self.assertTrue(incompatible(early, neg(early), frozenset()))
        stance = frozenset({early, neg(early)})
        state = ReasonState()
        state.mint("e", {early}, Atom("q"), at=1)
        self.assertTrue(enabled(state, "e", stance, frozenset()))


class TestMicrohistorySweep(unittest.TestCase):
    """Representation-completeness search: classes not already fixtured."""

    def test_testimony_about_testimony(self):
        # A reports that B said q; B's saying q is a content claim reached by
        # one testimony application, and q by a second application citing it.
        state = ReasonState()
        state.mint(
            "hear-a",
            {Atom("a-reports"), App("testimony-a", "c", 1), Receipt("r1")},
            Atom("b-said-q"),
            at=1,
            applied_as={("testimony-a", "c", 1)},
        )
        state.mint(
            "trust-b",
            {Atom("b-said-q"), App("testimony-b", "c", 1)},
            Atom("q"),
            at=1,
            applied_as={("testimony-b", "c", 1)},
        )
        stance = frozenset({Atom("a-reports"), App("testimony-a", "c", 1)})
        self.assertEqual(reasons(state, Atom("b-said-q"), stance, frozenset({"r1"})), ("hear-a",))
        uptaken = stance | {Atom("b-said-q"), App("testimony-b", "c", 1)}
        self.assertEqual(reasons(state, Atom("q"), uptaken, frozenset({"r1"})), ("trust-b",))

    def test_unreliable_is_not_inapplicable(self):
        # A reason that a source is unreliable bears on the reliability claim
        # only. It neither undercuts the base application nor rebuts it; a
        # further reason from unreliability to non-applicability is a
        # separate, mintable step.
        state = ReasonState()
        state.mint(
            "base",
            {Atom("b-said-q"), App("testimony-b", "c", 1)},
            Atom("q"),
            at=1,
            applied_as={("testimony-b", "c", 1)},
        )
        state.mint(
            "doubt",
            {Atom("track-record"), App("reliability-audit", "c", 2)},
            Atom("source-b-unreliable"),
            at=2,
            applied_as={("reliability-audit", "c", 2)},
        )
        stance = frozenset(
            {Atom("b-said-q"), App("testimony-b", "c", 1), Atom("track-record"),
             App("reliability-audit", "c", 2)}
        )
        self.assertTrue(enabled(state, "base", stance, frozenset()))
        self.assertFalse(undercuts(state, "doubt", "base", stance, frozenset()))
        self.assertFalse(rebuts(state, "doubt", "base", stance, frozenset()))
        state.mint(
            "bridge",
            {Atom("source-b-unreliable"), App("unreliability-defeat", "c", 2)},
            neg(App("testimony-b", "c", 1)),
            at=2,
            applied_as={("unreliability-defeat", "c", 2)},
        )
        wider = stance | {Atom("source-b-unreliable"), App("unreliability-defeat", "c", 2)}
        self.assertTrue(undercuts(state, "bridge", "base", wider, frozenset()))

    def test_circular_and_mutual_structures_are_total(self):
        state = ReasonState()
        p, q = Atom("p"), Atom("q")
        state.mint("pq", {p}, q, at=1)
        state.mint("qp", {q}, p, at=1)
        state.mint(
            "u1", {Atom("g1"), App("s1", "c", 1)}, neg(App("s2", "c", 1)),
            at=1, applied_as={("s1", "c", 1)},
        )
        state.mint(
            "u2", {Atom("g2"), App("s2", "c", 1)}, neg(App("s1", "c", 1)),
            at=1, applied_as={("s2", "c", 1)},
        )
        both = frozenset({Atom("g1"), Atom("g2"), App("s1", "c", 1), App("s2", "c", 1)})
        self.assertTrue(undercuts(state, "u1", "u2", both, frozenset()))
        self.assertTrue(undercuts(state, "u2", "u1", both, frozenset()))
        # Circular support is exposed, not resolved: at a stance holding
        # neither p nor q, neither occurrence bears; holding one enables the
        # other's reason. What a policy does with that is not asked here.
        self.assertEqual(bearing(state, frozenset(), frozenset()), frozenset())
        self.assertIn(q, bearing(state, frozenset({p, Atom("g1"), Atom("g2")}), frozenset()))

    def test_case_merge_judgment_and_its_retraction(self):
        state = ReasonState()
        same = Atom("same-situation:c1:c2")
        state.mint(
            "merge-reason",
            {Atom("shared-parties"), App("identity-analysis", "c9", 3)},
            same,
            at=3,
            applied_as={("identity-analysis", "c9", 3)},
        )
        state.mint(
            "unmerge-reason",
            {Atom("distinct-contracts"), App("identity-analysis", "c9", 7)},
            neg(same),
            at=7,
            applied_as={("identity-analysis", "c9", 7)},
        )
        stance = frozenset(
            {Atom("shared-parties"), Atom("distinct-contracts"),
             App("identity-analysis", "c9", 3), App("identity-analysis", "c9", 7)}
        )
        self.assertEqual(reasons(state, same, stance, frozenset()), ("merge-reason",))
        self.assertEqual(reasons(state, neg(same), stance, frozenset()), ("unmerge-reason",))

    def test_one_receipt_bears_differently_on_two_cases(self):
        state = ReasonState()
        state.mint(
            "for-c1",
            {Receipt("lab"), App("contamination", "c1", 2)},
            Atom("sample-tainted:c1"),
            at=2,
            applied_as={("contamination", "c1", 2)},
        )
        state.mint(
            "for-c2",
            {Receipt("lab"), App("alibi", "c2", 2)},
            Atom("absent:c2"),
            at=2,
            applied_as={("alibi", "c2", 2)},
        )
        stance = frozenset({App("contamination", "c1", 2)})
        self.assertEqual(
            bearing(state, stance, frozenset({"lab"})),
            frozenset({Atom("sample-tainted:c1")}),
        )

    def test_perspectival_conflict_is_stance_parametric(self):
        # Two scorekeepers over one structure: the queries take the stance as
        # an argument, so practices disagreeing about an incompatibility get
        # different derived conflict at no representational cost.
        state = ReasonState()
        a, b = Atom("respond:x"), Atom("respond:y")
        state.mint("ra", {Atom("ga")}, a, at=1)
        state.mint("rb", {Atom("gb")}, b, at=1)
        clash = Incomp(frozenset({a, b}))
        strict = frozenset({Atom("ga"), Atom("gb"), clash})
        permissive = frozenset({Atom("ga"), Atom("gb")})
        self.assertTrue(rebuts(state, "ra", "rb", strict, frozenset()))
        self.assertFalse(rebuts(state, "ra", "rb", permissive, frozenset()))


if __name__ == "__main__":
    unittest.main()
