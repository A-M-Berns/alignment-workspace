#!/usr/bin/env python3
"""Self-contained runner for the corrigibility note dump: the value-change note's
fixture, which recomputes every number the note marks *computed* in exact
rational arithmetic and asserts it."""

from pathlib import Path
import subprocess
import sys

TREE = Path(__file__).resolve().parents[1]
FIXTURES = ("fixtures/value_change_journey.py",)

failed = []
for fixture in FIXTURES:
    proc = subprocess.run([sys.executable, fixture], cwd=TREE, capture_output=True, text=True)
    ok = proc.returncode == 0 and "all assertions passed" in proc.stdout
    print(f"  {'PASS' if ok else 'FAIL'}  {fixture}")
    if not ok:
        failed.append(fixture)
        print(proc.stdout[-2000:]); print(proc.stderr[-2000:])
raise SystemExit(1 if failed else 0)
