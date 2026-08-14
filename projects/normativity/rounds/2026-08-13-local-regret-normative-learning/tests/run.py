#!/usr/bin/env python3
"""Run the local-regret normative-learning tests."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROUNDS = HERE.parent
BRIDGE = ROUNDS.parent / "legitimacy" / "rounds" / "2026-08-13-relational-scorekeeping-bridge"
LEARNER = ROUNDS / "2026-08-11-phi-regret-learner"
sys.path[:0] = [str(HERE / "src"), str(BRIDGE / "src"), str(LEARNER / "src")]

suite = unittest.defaultTestLoader.discover(str(HERE / "tests"), pattern="test_*.py")
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() else 1)
