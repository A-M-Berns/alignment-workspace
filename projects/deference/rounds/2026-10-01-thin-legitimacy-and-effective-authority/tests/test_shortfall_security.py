"""Part E: the entrenchment, storm and latency fixtures on the priced shortfall event."""

import unittest
from fractions import Fraction as Q

from src.shortfall_security import entrenchment, storm, latency, excluded, limit_price

THETA = Q(1, 2)


class PricedShortfall(unittest.TestCase):
    def test_entrenchment(self):
        table = entrenchment()
        self.assertEqual(table, {"idle": False, "build_dep": True, "repaint": False, "ask": False})
        ex = excluded(table, THETA, inquiry=("ask",))
        self.assertTrue(ex["build_dep"])
        self.assertFalse(ex["idle"] or ex["repaint"] or ex["ask"])

    def test_storm(self):
        # after the storm every option but restoring leaves her short; the priced event
        # excludes them and leaves restore and ask — the required notice
        table = storm()
        self.assertEqual(table, {"idle": True, "restore_wire": False, "build_dep": True, "ask": True})
        ex = excluded(table, THETA, inquiry=("ask",))
        self.assertEqual(ex, {"idle": True, "restore_wire": False, "build_dep": True, "ask": False})

    def test_latency(self):
        routine, high_veto = latency()
        self.assertTrue(all(routine.values()))
        self.assertFalse(any(high_veto.values()))
        ex = excluded(routine, THETA, inquiry=("ask",))
        self.assertEqual(ex, {"idle": True, "build_dep": True, "repaint": True, "ask": False})

    def test_limit_prices(self):
        self.assertEqual(limit_price(True), 1)
        self.assertEqual(limit_price(False), 0)


if __name__ == "__main__":
    unittest.main()
