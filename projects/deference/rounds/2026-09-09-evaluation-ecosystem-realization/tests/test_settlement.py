"""The settlement channel (`SETTLEMENT_CHANNEL.md`)."""
from __future__ import annotations

import unittest

from src import settlement as st


class TestLaundering(unittest.TestCase):
    def test_untyped_independence_launders(self):
        """Independence `none` (fixture 3′'s rule): the principal settles the external
        fact itself, disposes of the live protected concern on it, and the evaluation
        certifies with the concern suppressed."""
        r = st.laundering_fixture("none")
        self.assertTrue(r["disposal_valid"])
        self.assertFalse(r["protected_live_at_slot"])
        self.assertTrue(r["C"])

    def test_typed_independence_refuses(self):
        r = st.laundering_fixture("typed")
        self.assertFalse(r["disposal_valid"])
        self.assertTrue(r["protected_live_at_slot"])
        self.assertFalse(r["committed"])
        self.assertFalse(r["C"])

    def test_strict_independence_refuses(self):
        r = st.laundering_fixture("strict")
        self.assertFalse(r["disposal_valid"])
        self.assertFalse(r["C"])

    def test_engine_settlement_is_accepted_under_every_rule(self):
        """Fixture 3′ proper: the ground belongs to nobody."""
        for rule in ("none", "typed", "strict"):
            r = st.engine_settled_fixture(rule)
            self.assertTrue(r["disposal_valid"], rule)
            self.assertTrue(r["C"], rule)

    def test_own_deliberation_is_a_valid_ground_only_under_typed(self):
        """A sentence observational of the disposer's own move: settled by the move.
        Typed independence accepts it; strict independence refuses it and with it every
        disposal the principal could ground in its own record."""
        self.assertTrue(st.deliberation_ground_fixture("typed")["disposal_valid"])
        self.assertTrue(st.deliberation_ground_fixture("none")["disposal_valid"])
        self.assertFalse(st.deliberation_ground_fixture("strict")["disposal_valid"])

    def test_classification_marks_every_kind(self):
        rows = st.classify()
        self.assertEqual(len(rows), 12)
        self.assertEqual(sum(1 for _, _, obs in rows if obs is None), 1)


if __name__ == "__main__":
    unittest.main()
