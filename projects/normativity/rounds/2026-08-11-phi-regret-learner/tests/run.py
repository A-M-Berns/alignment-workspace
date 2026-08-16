#!/usr/bin/env python3
"""Run the item-30 learner tests from any working directory."""

from __future__ import annotations

import pathlib
import sys
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
PREP = ROOT.parent / "2026-08-11-phi-regret-prep"
APPLICABILITY = ROOT.parent / "2026-08-11-phi-regret-applicability"
BRIDGE = ROOT.parent / "2026-08-11-phi-regret-bridge"
sys.path[:0] = [str(ROOT / "src"), str(BRIDGE / "src"),
                str(APPLICABILITY / "src"), str(PREP)]


def main() -> int:
    suite = unittest.defaultTestLoader.discover(str(ROOT / "tests"),
                                                pattern="test_*.py")
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
