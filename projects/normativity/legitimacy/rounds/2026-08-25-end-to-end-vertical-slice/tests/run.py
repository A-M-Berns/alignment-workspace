#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import sys
import unittest

HERE = pathlib.Path(__file__).resolve().parent
ROUND = HERE.parent
RI = ROUND.parents[1] / "2026-08-24-reflective-integrity-core" / "src"

sys.path[:0] = [str(ROUND / "src"), str(RI)]


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.discover(str(HERE), pattern="test_*.py")
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
