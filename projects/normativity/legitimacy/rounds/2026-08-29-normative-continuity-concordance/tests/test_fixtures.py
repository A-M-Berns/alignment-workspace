"""The proof-pass fixtures, as tests. `src/fixtures.py` is the checkpoint artifact and is
imported unchanged; these tests re-assert its claims individually so a regression names
the fixture that broke."""
from __future__ import annotations

import hashlib
import pathlib
import unittest

import fixtures as F

ROUND = pathlib.Path(__file__).resolve().parents[1]


class TestFixtureA(unittest.TestCase):
    """Rotating prerequisite: the necessity witness for Requirement 12."""

    def test_live_gate_admits_the_rotation(self):
        M, opps = F.run(F.TRACE_A, gate="live", tail=F.fixture_A, horizon=10)
        self.assertEqual(M.violations, [])
        self.assertTrue(M.live("a"))
        self.assertTrue(all(not o["a"] for o in opps[2:]))

    def test_no_route_wait_keeps_moving_under_the_live_gate(self):
        waits = []
        for h in (6, 7, 8):
            M, _ = F.run(F.TRACE_A, gate="live", tail=F.fixture_A, horizon=h)
            waits.append(M.noroute("a"))
        self.assertTrue(all(waits))
        self.assertFalse(waits[0] & waits[1])
        self.assertFalse(waits[1] & waits[2])

    def test_reach_gate_rejects_at_the_first_rotation(self):
        M, _ = F.run(F.TRACE_A, gate="reach", tail=F.fixture_A, horizon=4)
        self.assertEqual(M.violations[0], (2, "reach", "e1", "b1", "a"))

    def test_every_other_requirement_holds(self):
        # `Model.step` asserts Requirements 5, 8, 10 and one-shot occurrences on every
        # batch; a violation would raise rather than be recorded.
        F.run(F.TRACE_A, gate="live", tail=F.fixture_A, horizon=10)


class TestOtherFixtures(unittest.TestCase):
    def test_B_co_opened_root(self):
        M, _ = F.run(F.TRACE_B[:1]); M.roots["d"] = {"t"}
        self.assertEqual(M.routes("d"), set())
        M, _ = F.run(F.TRACE_B[:2])
        self.assertEqual(M.routes("d"), {"t"})

    def test_C_fixed_no_route_wait(self):
        M, opps = F.run(F.TRACE_C, tail=lambda n: [], horizon=5)
        self.assertEqual(M.noroute("a"), {"d"})
        self.assertFalse(opps[-1]["a"])

    def test_D_route_extinction(self):
        M, opps = F.run(F.TRACE_D)
        self.assertEqual(M.noroute("a"), {"d"})
        self.assertTrue(opps[2]["a"])

    def test_E_cycle_is_work(self):
        _, opps = F.run(F.TRACE_E, tail=lambda n: [], horizon=6)
        self.assertTrue(all(o["a"] and o["t"] for o in opps[2:]))

    def test_F_branch_merge_designate(self):
        M, _ = F.run(F.TRACE_F)
        self.assertEqual(M.live("a"), {"a3"})
        self.assertEqual(M.live("a2"), {"a3"})
        self.assertEqual(M.M_birth["a2"], 4)
        self.assertEqual(M.violations, [])


class TestCheckpointDigests(unittest.TestCase):
    """The checkpoint artifacts are the bytes `ORIGIN.md` names."""

    def test_digests(self):
        origin = (ROUND / "ORIGIN.md").read_text()
        for line in origin.splitlines():
            if line.startswith("| `") and "sha256:" in line:
                cells = [c.strip() for c in line.strip("|").split("|")]
                name = cells[0].strip("`")
                digest = cells[1].split("sha256:")[1].strip().strip("`")
                path = ROUND / name
                self.assertTrue(path.exists(), name)
                self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), digest, name)


if __name__ == "__main__":
    unittest.main()
