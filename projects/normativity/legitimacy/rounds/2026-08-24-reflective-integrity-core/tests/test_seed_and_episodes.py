"""Seed conditions and Episode Uniqueness.

The base case of `EP` is exactly Z3 + Z3' + Z6 with D2 supplying non-closure.
`test_ungated_seed_demand_breaks_episode_uniqueness` is the one-object,
one-step counterexample the surviving red-team recap names; it is the reason
D1/D2 are conditions on the interface rather than facts about one demand.
"""
from __future__ import annotations

import unittest

from ri_core import (ACCOUNT_FOR_SUCCESSION, ACTIVE, GENESIS, AnsRoot,
                     History, PAuth, Seed, StandingState, WFError, check_seed,
                     standing_tag, root_tag, superseding)
import scenarios as S


class TestSeed(unittest.TestCase):
    def test_single_seed_object_is_well_formed_and_current(self):
        h = History(S.seed_from({"x": S.commitment("x")}))
        self.assertTrue(h.current_episode(h.root("q0:x"), 0))
        self.assertEqual([], h.answerability_conservation(0))

    def test_multiple_seed_objects(self):
        h = History(S.seed_from({f"x{i}": S.commitment(str(i)) for i in range(4)}))
        self.assertEqual(4, len(h.roots(0)))
        self.assertEqual([], h.answerability_conservation(0))
        for i in range(4):
            self.assertEqual("P0", h.custodian(f"x{i}", 0))

    def test_duplicate_seed_roots_for_one_subject_are_refused(self):
        """Z3 is `exists!`, not `exists`: two roots for one object is malformed."""
        seed = S.seed_from({"x": S.commitment("x")})
        extra = AnsRoot("q0:dup", ("P0", 0), "P0", "x",
                        ACCOUNT_FOR_SUCCESSION, GENESIS, 0)
        broken = Seed(seed.std0, seed.roots0 + (extra,))
        self.assertTrue(any(v[0] == "Z3" for v in check_seed(broken)))
        with self.assertRaises(WFError):
            History(broken)

    def test_root_without_seed_standing_is_refused(self):
        """Z3': a genesis root whose subject does not exist would be a custody
        episode for nothing, and `EP` would report it against an absent status."""
        seed = S.seed_from({"x": S.commitment("x")})
        orphan = AnsRoot("q0:ghost", ("P0", 0), "P0", "ghost",
                         ACCOUNT_FOR_SUCCESSION, GENESIS, 0)
        broken = Seed(seed.std0, seed.roots0 + (orphan,))
        self.assertTrue(any(v[0] == "Z3'" for v in check_seed(broken)))

    def test_seed_ids_may_not_occupy_the_minted_range(self):
        """F2/F3: the allocator's range is reserved, so no later Create can
        collide with a seed id."""
        seed = S.seed_from({standing_tag(1, 0): S.commitment("x")})
        self.assertTrue(any(v[0] == "F2" for v in check_seed(seed)))
        base = S.seed_from({"x": S.commitment("x")})
        collide = Seed(base.std0, (AnsRoot(root_tag(1, 0), ("P0", 0), "P0", "x",
                                           ACCOUNT_FOR_SUCCESSION, GENESIS, 0),))
        self.assertTrue(any(v[0] == "F3" for v in check_seed(collide)))

    def test_terminated_seed_standing_is_refused(self):
        from ri_core import terminated
        seed = Seed({"x": StandingState(terminated("a0"), frozenset(),
                                        S.commitment("x"))}, ())
        self.assertTrue(any(v[0] == "Z1" for v in check_seed(seed)))

    def test_ungated_seed_demand_breaks_episode_uniqueness(self):
        """The recap's counterexample, executed: without D2 the base case of EP
        already fails at t = 0 for a one-object seed."""
        seed = S.seed_from({"x": S.commitment("x")}, demand=S.always_closed())
        h = History(seed)                      # structurally well-formed
        self.assertEqual("Closed", h.fate(h.root("q0:x"), 0))
        self.assertIsNone(h.custodian("x", 0))
        self.assertIn("vi", h.answerability_conservation(0))
        # and the repaired interface refuses exactly this seed
        self.assertTrue(any(v[0] == "D1/D2"
                            for v in check_seed(seed, sampler=S.sample_for)))

    def test_repaired_seed_passes_every_clause(self):
        seed = S.seed_from({"x": S.commitment("x"), "y": S.commitment("y")})
        self.assertEqual([], check_seed(seed, sampler=S.sample_for))


class TestEpisodeUniqueness(unittest.TestCase):
    def _ep(self, h, t=None):
        return h.answerability_conservation(t)

    def test_ep_holds_across_supersession(self):
        h = S.supersession_history()
        self.assertEqual([], self._ep(h))
        self.assertEqual(("Terminated", "a1"), h.status("x"))
        self.assertIsNone(h.custodian("x"))
        successor = standing_tag(1, 0)
        self.assertEqual("A", h.custodian(successor))

    def test_ep_holds_across_transfer(self):
        h = S.transfer_history()
        self.assertEqual([], self._ep(h))
        self.assertEqual("B", h.custodian("x"))

    def test_ep_holds_across_suspension_and_resume(self):
        h = S.suspension_history()
        for t in range(h.now + 1):
            self.assertEqual([], self._ep(t=t, h=h), t)
        self.assertEqual("A", h.custodian("x"))

    def test_ep_under_respond_cannot_close_a_current_episode(self):
        """D2 is what blocks a Respond step from vacating a live custody."""
        h = History(S.seed_from({"x": S.commitment("x")}))
        h.respond("rho1", roots=["q0:x"], cited=[])
        self.assertEqual("LiveNotDue", h.fate(h.root("q0:x")))
        self.assertEqual([], self._ep(h))

    def test_ep_holds_for_merge_and_split(self):
        for h in (S.merge_history(), S.split_history()):
            self.assertEqual([], self._ep(h))

    def test_revocation_leaves_no_current_episode(self):
        h = S.revocation_history()
        self.assertEqual([], self._ep(h))
        self.assertIsNone(h.custodian("x"))
        self.assertEqual((), h.succ(h.root("q0:x")))


if __name__ == "__main__":
    unittest.main()
