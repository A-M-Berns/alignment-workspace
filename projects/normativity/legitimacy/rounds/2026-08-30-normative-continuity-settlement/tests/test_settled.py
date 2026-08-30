"""The settled specification is jointly satisfiable, each departure is exercised by the
witness, and the red-team attacks fail as claimed."""
from __future__ import annotations

import hashlib
import pathlib
import unittest
from fractions import Fraction

import fixtures as F
import settled_model as S

ROUND = pathlib.Path(__file__).resolve().parents[1]


class TestWitness(unittest.TestCase):
    def setUp(self):
        self.M = S.run_witness()

    def test_all_requirements_hold_jointly(self):
        self.assertEqual(self.M.violations, [])

    def test_standing_gain_and_loss_with_authorized_grounds(self):
        Ls = [h["L"] for h in self.M.history]
        self.assertIn("r1", Ls[1]); self.assertIn("g0", Ls[1])
        self.assertNotIn("g0", Ls[3]); self.assertIn("r2", Ls[6])

    def test_issue_outlives_its_protocols_standing(self):
        # `a` is anchored to P (licensed by g0); g0 is repealed at 2; `a` resolves at 8.
        self.assertEqual(self.M.anchor["a"][2], "P")
        self.assertFalse(any(("P", "audit", "sys") in S.RULES[l]["licenses"]
                             for l in self.M.history[3]["L"]))
        self.assertNotIn("a", self.M.O)

    def test_due_rises_twice_and_falling_edge_closes_nothing(self):
        dues = [h["due"] for h in self.M.history]
        self.assertIn(("review", "sys"), dues[2]); self.assertNotIn(("review", "sys"), dues[4])
        self.assertIn(("review", "sys"), dues[6])
        self.assertIn("v", self.M.born_at); self.assertEqual(self.M.born_at["v"], 2)

    def test_reintroduced_prerequisite_is_a_fresh_occurrence(self):
        self.assertEqual(self.M.roots["d0"], {"t"}); self.assertEqual(self.M.roots["d1"], {"t1"})

    def test_route_extinction_then_met(self):
        # t1 resolved terminally at 6; d1 met at 7; a resolved at 8.
        self.assertNotIn("t1", self.M.O); self.assertIn("d1", self.M.met)

    def test_designated_matter_overlaps_ancestor_and_budget_holds(self):
        self.assertIn("t1", self.M.matters); self.assertIn("t", self.M.matters)
        self.assertEqual(self.M.M_birth["t1"], 4)
        self.assertTrue(all(sum(self.M.share[m] for m in self.M.matters) < 1 for _ in [0]))

    def test_attention_is_share_times_opportunity(self):
        for m in self.M.matters:
            self.assertEqual(self.M.attention[m], self.M.share[m] * self.M.omega[m])
            self.assertIsInstance(self.M.attention[m], Fraction)


class TestSettledChoicesRegressions(unittest.TestCase):
    def test_rotating_prerequisite_still_rejected_by_reach_gate_only(self):
        M, _ = F.run(F.TRACE_A, gate="reach", tail=F.fixture_A, horizon=4)
        self.assertEqual(M.violations[0][:2], (2, "reach"))
        M, _ = F.run(F.TRACE_A, gate="live", tail=F.fixture_A, horizon=6)
        self.assertEqual(M.violations, [])

    def test_same_batch_open_and_resolve_is_refused(self):
        with self.assertRaises(AssertionError):
            F.run([[("open", "a", []), ("resolve", "a", [])]])

    def test_preexisting_successor_is_refused(self):
        with self.assertRaises(AssertionError):
            F.run([[("open", "a", []), ("open", "b", [])], [("resolve", "a", ["b"])]])

    def test_consolidation_by_route_edge_credits_the_matter(self):
        # a waits through b (existing); b's readiness is a's work.
        M, opps = F.run([[("open", "a", []), ("open", "b", [])],
                         [("addpre", "d", "a", ["b"])], []])
        self.assertIn("b", M.reach("a")); self.assertTrue(opps[2]["a"])

    def test_designation_never_retroactive(self):
        M, _ = F.run(F.TRACE_F[:4])
        self.assertEqual(M.M_birth["a2"], 4)

    def test_empty_history_is_consistent(self):
        M = S.SettledModel(S.RULES, genesis=set(), due=lambda n, m: set())
        for _ in range(3):
            M.step([])
        self.assertEqual(M.matters, set()); self.assertEqual(M.violations, [])


class TestDigests(unittest.TestCase):
    def test_origin_digests(self):
        origin = (ROUND / "ORIGIN.md").read_text()
        rows = [l for l in origin.splitlines() if l.startswith("| `") and "sha256:" in l]
        self.assertTrue(rows)
        for line in rows:
            cells = [c.strip() for c in line.strip("|").split("|")]
            name = cells[0].strip("`")
            digest = cells[1].split("sha256:")[1].strip().strip("`")
            path = ROUND / name if not name.startswith("lean/") else ROUND.parents[4] / name
            self.assertTrue(path.exists(), name)
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), digest, name)


if __name__ == "__main__":
    unittest.main()
