#!/usr/bin/env python3
"""Self-contained runner for the LI/BRIA synthesis specification round: the per-round
conflict fixtures, the troll family, Newcomb under two predictors, and the
market-reading interaction diagnostic."""

from pathlib import Path
import sys
import unittest

ROUND = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROUND))

suite = unittest.defaultTestLoader.discover(str(ROUND / "tests"), pattern="test_*.py")
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
