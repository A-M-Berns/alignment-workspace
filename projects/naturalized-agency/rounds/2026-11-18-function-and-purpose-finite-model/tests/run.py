#!/usr/bin/env python3
"""Self-contained runner for the function-and-purpose finite model round."""

from pathlib import Path
import sys
import unittest

ROUND = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROUND))
sys.path.insert(0, str(ROUND / "tests"))

suite = unittest.defaultTestLoader.discover(str(ROUND / "tests"), pattern="test_*.py")
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
