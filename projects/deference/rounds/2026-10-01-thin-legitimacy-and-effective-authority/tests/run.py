#!/usr/bin/env python3
"""Self-contained runner for the thin-legitimacy round: the A4 model, the attention,
revocation and latency fixtures, the comparative witnesses, the priced shortfall tables."""

from pathlib import Path
import sys
import unittest

ROUND = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROUND))

suite = unittest.defaultTestLoader.discover(str(ROUND / "tests"), pattern="test_*.py")
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
