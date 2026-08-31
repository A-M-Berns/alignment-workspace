#!/usr/bin/env python3
"""Run the exact finite refinement fixtures."""

import pathlib
import sys
import unittest

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "src"))

suite = unittest.defaultTestLoader.discover(str(HERE), pattern="test_*.py")
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(not result.wasSuccessful())
