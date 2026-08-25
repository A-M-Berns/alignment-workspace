"""Fresh standing and root ids: F1, F2, F3, and what fails without them.

`test_allocator_without_time_collides` is the necessity witness: it replaces
the allocator with one that drops the time component and shows the collision
reaching Episode Uniqueness, so F1 is doing work rather than restating S6.
"""
from __future__ import annotations

import unittest
from unittest import mock

import ri_core
from ri_core import (History, PAuth, WFError, root_tag, standing_tag,
                     superseding)
import scenarios as S


class TestAllocator(unittest.TestCase):
    def test_allocation_is_injective_in_time_and_index(self):
        ids = [standing_tag(t, i) for t in range(1, 6) for i in range(4)]
        self.assertEqual(len(ids), len(set(ids)))
        rids = [root_tag(t, j) for t in range(1, 6) for j in range(4)]
        self.assertEqual(len(rids), len(set(rids)))
        self.assertEqual(set(), set(ids) & set(rids))

    def test_siblings_are_distinct(self):
        h = S.split_history()
        fresh = [x for x in h.std() if x.startswith(ri_core.MINTED_PREFIX)]
        self.assertEqual(2, len(set(fresh)))
        self.assertEqual({standing_tag(1, 0), standing_tag(1, 1)}, set(fresh))

    def test_create_cannot_collide_with_seed_standing(self):
        h = History(S.seed_from({
            "x": S.commitment("x"),
            "auth:mk": PAuth(S.creating("mk", [S.commitment("new")])),
        }))
        before = set(h.std(0))
        h.norm("a1", "auth:mk", author="A")
        self.assertEqual(set(), before & {standing_tag(1, 0)})
        self.assertTrue(before <= set(h.std()))

    def test_supersede_successor_does_not_collide_with_earlier_standing(self):
        h = S.chain_history(3)
        minted = [x for x in h.std() if x.startswith(ri_core.MINTED_PREFIX)]
        self.assertEqual(3, len(set(minted)))
        self.assertEqual([], h.answerability_conservation())

    def test_allocator_without_time_collides(self):
        """Necessity witness for F1. Two Creates at different times allocate
        the same id, the second overwrites the first, and the first object's
        current episode is left pointing at standing that is no longer there."""
        with mock.patch.object(ri_core, "standing_tag",
                               lambda tau, i: f"@s.{i}"):
            h = History(S.seed_from({
                "x": S.commitment("x"),
                "auth:mk": PAuth(S.creating("mk", [S.commitment("k")])),
            }))
            h.norm("a1", "auth:mk", author="A")
            h.norm("a2", "auth:mk", author="A")
            self.assertEqual(1, len([x for x in h.std() if x.startswith("@s.")]))
            self.assertEqual(4, len(h.roots()))
            self.assertIn("vi", h.answerability_conservation())


class TestEffectPreconditions(unittest.TestCase):
    def test_supersede_of_absent_standing_is_refused(self):
        """G6 resolves targets in the strict pre-state before `delta` reads
        `pred` and `payload` off them."""
        h = History(S.seed_from({
            "x": S.commitment("x"),
            "auth:ghost": PAuth(superseding("ghost", ["nope"], [])),
        }))
        with self.assertRaises(WFError) as caught:
            h.norm("a1", "auth:ghost", author="A")
        self.assertEqual("G6-domain", caught.exception.clause)

    def test_supersede_of_terminated_standing_is_refused(self):
        h = History(S.seed_from({
            "x": S.commitment("x"),
            "auth:sup": PAuth(superseding("sup", ["x"], [S.commitment("x2")])),
            "auth:again": PAuth(superseding("again", ["x"], [])),
        }))
        h.norm("a1", "auth:sup", author="A")
        with self.assertRaises(WFError) as caught:
            h.norm("a2", "auth:again", author="A")
        self.assertEqual("G6-terminated", caught.exception.clause)


if __name__ == "__main__":
    unittest.main()
