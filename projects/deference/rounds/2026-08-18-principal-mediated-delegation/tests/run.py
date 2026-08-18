#!/usr/bin/env python3
"""Run this round's checks.

Two declared dependencies are put on the path rather than copied. The
counterfactual-legitimacy round's `src/` carries the protected normative process,
the non-capture clause and the scenarios this round composes with; that round in
turn reads the procedural-legitimacy round's `src/`. Copying either would have
made "the same object" a claim instead of a fact.

The runner fails with a named error if a declared dependency is absent, rather
than skipping the composition tests and reporting green.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[3]
LEGITIMACY = (ROOT / "projects" / "normativity" / "legitimacy" / "rounds"
              / "2026-08-17-counterfactual-legitimacy" / "src")
PROCEDURAL = (ROOT / "projects" / "normativity" / "legitimacy" / "rounds"
              / "2026-08-13-procedural-legitimacy" / "src")

for dependency in (LEGITIMACY, PROCEDURAL):
    if not dependency.is_dir():
        raise SystemExit(f"missing declared dependency: {dependency}")

sys.path[:0] = [str(HERE / "src"), str(LEGITIMACY), str(PROCEDURAL)]

suite = unittest.defaultTestLoader.discover(str(HERE / "tests"), pattern="test_*.py")
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
