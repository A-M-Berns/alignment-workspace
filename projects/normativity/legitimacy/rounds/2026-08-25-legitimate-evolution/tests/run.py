#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import sys
import unittest

HERE = pathlib.Path(__file__).resolve().parent
ROUND = HERE.parent
ROUNDS = ROUND.parent
RI = ROUNDS / "2026-08-24-reflective-integrity-core" / "src"
SLICE = ROUNDS / "2026-08-25-end-to-end-vertical-slice" / "src"
CARROLL = ROUNDS / "2026-08-25-carroll-legitimacy-test" / "src"

sys.path[:0] = [str(ROUND / "src"), str(CARROLL), str(RI), str(SLICE)]


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.discover(str(HERE), pattern="test_*.py")
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
