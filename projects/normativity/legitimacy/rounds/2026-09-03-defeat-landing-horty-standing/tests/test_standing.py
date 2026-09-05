"""Fixtures for the standing repair, and the principal-relative laundering theorem."""
from __future__ import annotations

import unittest

import fixtures as F
from standing_model import DefeatViolation, StandingModel


class TestStandingIsNoLongerVacuous(unittest.TestCase):
    def test_standing_only_resolver_is_refused(self):
        """The repair's point. `V` has a foreign ground — `W` opened `g_W` — so
        `foreign_ground` is satisfied, and the disposal is refused anyway because only
        `V` holds standing on the successor."""
        with self.assertRaises(DefeatViolation) as cm:
            F.standing_only_resolver()
        self.assertEqual(cm.exception.code, "D3-uncontested")

    def test_stands_for_reads_the_participant(self):
        """`stands_for` now takes a holder, so two different participants get two
        different answers from the same trace. The pre-repair Lean could not express
        this question."""
        M = F.coalition_case()
        self.assertTrue(M.stands_for("V", "V", "audit", "sys"))
        self.assertTrue(M.stands_for("W", "W", "audit", "sys"))
        self.assertFalse(M.stands_for("P", "P", "audit", "sys"))


class TestCoalitionUnchanged(unittest.TestCase):
    def test_coalition_case_is_accepted(self):
        """Restated under the explicit licence type: each edge satisfies D3 on both
        sides, and the pair still launders. The repair does not close this."""
        M = F.coalition_case()
        self.assertEqual(len(M.disposal_edges), 2)
        self.assertEqual(len(M.alternating_walks()), 1)

    def test_no_edge_is_single_handed(self):
        """Both sides agree: no edge has its grounds and its standing in one hand."""
        M = F.coalition_case()
        self.assertEqual(M.single_handed_edges(), [])


class TestPrincipalRelative(unittest.TestCase):
    def test_principal_holds_throughout(self):
        """The positive case: no coalition excluding `P` holds all the standing on any
        edge, because `P` holds standing on every successor."""
        M = F.principal_holds_throughout()
        self.assertEqual(len(M.disposal_edges), 2)
        self.assertTrue(M.principal_holds_throughout("P"))
        self.assertEqual(M.coalition_walks_excluding("P"), [])

    def test_principal_absent_from_one_successor(self):
        """`P`'s licence is answered away before the second edge, so `{V, W}` holds all
        the standing on `a2`. Plain separation still accepts every edge; the
        `P`-relative form does not."""
        M = F.principal_absent_from_one()
        self.assertEqual(len(M.disposal_edges), 2)
        self.assertFalse(M.principal_holds_throughout("P"))
        excluded = M.coalition_walks_excluding("P")
        self.assertEqual(len(excluded), 1)
        self.assertEqual(excluded[0][1], "a2")
        # and plain separation is untroubled by it — which is the difference
        self.assertEqual(M.single_handed_edges(), [])

    def test_the_two_forms_come_apart(self):
        """Exactly the point of stating the P-relative form: it is strictly stronger."""
        ok = F.principal_holds_throughout()
        bad = F.principal_absent_from_one()
        self.assertEqual(ok.single_handed_edges(), bad.single_handed_edges())
        self.assertNotEqual(
            ok.principal_holds_throughout("P"), bad.principal_holds_throughout("P")
        )


if __name__ == "__main__":
    unittest.main()
