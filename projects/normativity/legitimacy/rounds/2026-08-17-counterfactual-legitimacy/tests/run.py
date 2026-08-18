#!/usr/bin/env python3
"""Run this round's checks.

The procedural-legitimacy round's `src/` is on the path: its `Trajectory`, its
four conditions and its target `L*` are the objects prosecuted here, and copying
them would have made "the same fixture" a claim rather than a fact.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
PROCEDURAL = HERE.parent / "2026-08-13-procedural-legitimacy" / "src"

if not PROCEDURAL.is_dir():
    raise SystemExit(f"missing declared dependency: {PROCEDURAL}")

sys.path[:0] = [str(HERE / "src"), str(PROCEDURAL)]

suite = unittest.defaultTestLoader.discover(str(HERE / "tests"), pattern="test_*.py")
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
