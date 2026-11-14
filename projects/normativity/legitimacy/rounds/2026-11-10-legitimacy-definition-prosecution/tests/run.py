#!/usr/bin/env python3
"""The repository-level runner finds projects/**/tests/run.py; the round's runner
is run.py at the round root, as its prompt specifies.  This hands over to it."""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.exit(subprocess.run([sys.executable, "run.py"], cwd=ROOT).returncode)
