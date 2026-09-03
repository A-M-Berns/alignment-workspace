"""Hostile fixtures for unified grounds and answerable defeat.

Every test names the clause that did the work. Two tests record findings rather than
successes — `test_self_grounding_survives_priority` and
`test_two_author_alternating_walk_is_accepted` — and both are asserted in the
direction the round actually found, not the direction the dispatch expected.
"""
from __future__ import annotations

import unittest
from fractions import Fraction

import fixtures as F
from defeat_model import (
    ANSWER,
    DISPOSE,
    DefeatModel,
    DefeatViolation,
    MassLedger,
    issue,
)


class TestGroundsUnification(unittest.TestCase):
    def test_licence_occurrences_are_issues(self):
        """Standing is a filter on live issues; there is no separate `L_n`."""
        M = F.genesis()
        self.assertTrue(M.stands_for("P", "audit", "sys"))
        self.assertTrue(M.stands_for("V", "audit", "sys"))
        self.assertFalse(M.stands_for("Z", "audit", "sys"))

    def test_freshness_is_birth_uniqueness(self):
        M = F.genesis()
        with self.assertRaises(DefeatViolation) as cm:
            M.step([("open", "a", "audit", "sys", "P", [], "P")])
        self.assertEqual(cm.exception.code, "born-twice")

    def test_grounded_replay_is_ancestry(self):
        """Every issue descends from a parentless issue: the authorization tree, now
        a consequence of the birth discipline rather than a separate postulate."""
        M = F.wait_on_disposed_root()
        self.assertEqual(M.ancestor_tree("a1"), {"a"})
        self.assertEqual(M.ancestor_tree("l_P"), {"l_P"})

    def test_mixed_grounds_are_expressible(self):
        """The point of the sum type: one disposal citing an issue and a settled fact.
        Before unification these had no common type and could not both be cited."""
        M = F.genesis()
        M.step([("settle", "s0")])
        M.step([
            ("open", "g_W", "audit", "sys", "W", [], "W"),
        ])
        M.step([
            ("open", "a1", "audit", "sys", "P", ["a"], "W"),
            ("resolve", "a", ["a1"], (DISPOSE, {issue("g_W"), ("settled", "s0")}), "V"),
        ])
        self.assertTrue(M.grounded(issue("g_W")))
        self.assertTrue(M.grounded(("settled", "s0")))


class TestNoSelfGrounding(unittest.TestCase):
    def test_grounding_in_successor_refused_by_ancestry(self):
        """Postulate 5 collapsing again: priority alone refuses it."""
        with self.assertRaises(DefeatViolation) as cm:
            F.disposal_grounded_in_successor()
        self.assertEqual(cm.exception.code, "D1-ungrounded")

    def test_self_grounding_survives_priority(self):
        """**Finding.** A disposed issue *is* in the record strictly before its own
        disposal, so `Grounded` holds of it and priority refuses nothing. The
        transition-certificates collapse re-derives for the successor and the batch and
        fails for the issue itself, which is why `not_self` is a clause."""
        M = F.genesis()
        self.assertTrue(M.grounded(issue("a")))          # priority is satisfied
        with self.assertRaises(DefeatViolation) as cm:   # only the explicit clause refuses
            F.disposal_self_grounded()
        self.assertEqual(cm.exception.code, "D1-self-grounded")


class TestSettlementIndependence(unittest.TestCase):
    def test_disposer_may_not_settle_its_own_ground(self):
        with self.assertRaises(DefeatViolation) as cm:
            F.disposal_on_own_settlement(settled_writer="V")
        self.assertEqual(cm.exception.code, "settlement-not-independent")

    def test_independence_is_necessary_not_decorative(self):
        """The identical trace is accepted when settlement belongs to nobody. The
        hypothesis is doing work: drop it and the fixture above goes through."""
        M = F.disposal_on_own_settlement(settled_writer=None)
        self.assertIn("s0", M.Settled)
        self.assertEqual(M.kind[(2, "a")][0], "settle")


class TestMetIsADefinition(unittest.TestCase):
    def test_wait_on_disposed_root_reroutes_and_is_not_met(self):
        """A prerequisite cannot be disposed away: the route survives into the
        successor and `Met` stays false."""
        M = F.wait_on_disposed_root()
        self.assertEqual(M.routes("d0"), {"a1"})
        self.assertFalse(M.met("d0"))

    def test_wait_on_answered_root_is_met(self):
        M = F.wait_on_answered_root()
        self.assertTrue(M.met("d0"))
        self.assertEqual(M.routes("d0"), set())

    def test_met_is_monotone(self):
        """Requirement 9 is now a theorem of the definition."""
        M = F.wait_on_answered_root()
        n = M.n
        self.assertTrue(M.met("d0", n))
        self.assertTrue(M.met("d0", n + 1))
        self.assertTrue(M.met("d0", n + 5))


class TestLaundering(unittest.TestCase):
    def test_single_author_walk_is_refused(self):
        with self.assertRaises(DefeatViolation) as cm:
            F.single_author_laundering()
        self.assertIn(cm.exception.code, {"D3-uncontested", "D3-self-grounds"})

    def test_separation_forbids_single_author_walks(self):
        """On a disciplined trace every disposal edge has a foreign ground, so no
        walk has all its edges, grounds and standings in one hand."""
        M = F.two_author_alternating()
        self.assertEqual(M.laundering_walks(), [])

    def test_two_author_alternating_walk_is_accepted(self):
        """**Finding.** Each edge satisfies D3 and the coalition still launders. Filed
        for the coalition-indexed predicate, not repaired in this round."""
        M = F.two_author_alternating()
        walks = M.alternating_walks()
        self.assertEqual(len(walks), 1)
        (e, f) = walks[0]
        self.assertEqual((e[0], e[1], e[2]), ("a", "a1", "V"))
        self.assertEqual((f[0], f[1], f[2]), ("a1", "a2", "W"))
        self.assertNotEqual(e[2], f[2])


class TestConservation(unittest.TestCase):
    def test_disposal_contributes_zero_to_terminal_fates(self):
        """T1, service layer. Disposal moves mass; only answer and settlement remove
        it from the open account."""
        L = MassLedger({"a": Fraction(3, 4), "b": Fraction(1, 4)})
        L.dispose("a", ["a1", "a2"])
        self.assertTrue(L.conserved())
        self.assertEqual(L.answered, Fraction(0))
        self.assertEqual(L.settled, Fraction(0))
        self.assertEqual(L.open_mass(), Fraction(1))

    def test_answer_and_settle_are_the_only_exits(self):
        L = MassLedger({"a": Fraction(1, 2), "b": Fraction(1, 2)})
        L.dispose("a", ["a1"])
        L.answer("a1")
        L.settle("b")
        self.assertTrue(L.conserved())
        self.assertEqual(L.open_mass(), Fraction(0))
        self.assertEqual(L.answered + L.settled, Fraction(1))

    def test_transport_step_is_lossless(self):
        """Disposal is a claim-to-claim transport step with L = 1, eps = 0: the mass
        arriving on successors equals the mass leaving the disposed issue."""
        L = MassLedger({"a": Fraction(2, 3)})
        L.dispose("a", ["a1", "a2", "a3"])
        moved = sum((s for (_, _, s) in L.edges), Fraction(0))
        self.assertEqual(moved, Fraction(2, 3))
        self.assertEqual(L.moved, Fraction(2, 3))

    def test_mixed_resolution_components(self):
        L = F.mixed_resolution_mismatched()
        self.assertTrue(L.conserved())
        self.assertEqual(L.answered, Fraction(1))
        self.assertEqual(L.open_mass(), Fraction(0))

    def test_dispose_without_successor_is_refused(self):
        L = MassLedger({"a": Fraction(1)})
        with self.assertRaises(DefeatViolation) as cm:
            L.dispose("a", [])
        self.assertEqual(cm.exception.code, "dispose-successor")

    def test_contest_residual(self):
        L = MassLedger({"a": Fraction(1), "b": Fraction(1)})
        L.dispose("a", ["a1"])
        self.assertEqual(L.contest_residual(), Fraction(1, 2))


class TestPersistenceUnderContest(unittest.TestCase):
    def test_bounded_contest_is_summable(self):
        """T4: under `liminf L_t(1) = 0`, persistence needs the contest durations to
        sum finitely. Bounded durations do."""
        d = F.contest_durations(bounded=True, horizon=8)
        self.assertEqual(F.total_contest(d), Fraction(8))

    def test_unbounded_contest_diverges(self):
        d = F.contest_durations(bounded=False, horizon=8)
        self.assertEqual(F.total_contest(d), Fraction(36))
        longer = F.contest_durations(bounded=False, horizon=16)
        self.assertGreater(F.total_contest(longer), 2 * F.total_contest(d))

    def test_settlement_closes_with_no_successor_and_no_charge(self):
        M = F.settlement_without_successor()
        self.assertNotIn("a", M.O)
        self.assertEqual(M.disposal_edges, [])


class TestNoFourthKind(unittest.TestCase):
    def test_only_three_kinds(self):
        M = F.genesis()
        with self.assertRaises(DefeatViolation) as cm:
            M.step([("resolve", "a", [], ("waive",), "V")])
        self.assertEqual(cm.exception.code, "bad-kind")


if __name__ == "__main__":
    unittest.main()
