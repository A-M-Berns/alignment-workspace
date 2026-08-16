#!/usr/bin/env python3
"""Run the fixed-action bridge tests."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
PREP = HERE.parent / "2026-08-11-phi-regret-prep"
APPLICABILITY = HERE.parent / "2026-08-11-phi-regret-applicability"
sys.path[:0] = [str(HERE / "src"), str(APPLICABILITY / "src"), str(PREP)]

suite = unittest.defaultTestLoader.discover(str(HERE / "tests"), pattern="test_*.py")
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
