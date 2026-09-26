#!/usr/bin/env python3
"""Self-contained runner for the BRIA-corrigibility round: the lexical evaluation, the
settlement conventions, the auction on realized scores, the extended consultation model,
the anchoring of criteria, the evaluation-timing options and the fixtures."""

from pathlib import Path
import sys
import unittest

ROUND = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROUND))

suite = unittest.defaultTestLoader.discover(str(ROUND / "tests"), pattern="test_*.py")
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
