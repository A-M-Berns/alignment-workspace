#!/usr/bin/env python3
"""Workspace runner: test discovery, the vocabulary gate, and optional Lean.

This tree is a **disposable forward workspace**. It carries no freeze machinery:
no checksum manifest, no rename roundtrip, no consolidation-locating logic, and
no pinned path into pre-consolidation history. The completed consolidation is
the sole authoritative record; see `WORKSPACE.md` and `CONSOLIDATION_REF.md`.
"""
from __future__ import annotations

import os
import pathlib
import re
import shutil
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

RETIRED = ("floor", "rent", "defect", "kernel", "AnsLearn", "ARC", "shock",
           "round", "period", "alpha", "extortion", "martyrdom", "firewall")
RETIRED_NOTATION = ("B_R", "D_N", "E_N", "E_*", "a_t", "R_t", "S_t", "S(R)")
CLAIM_ID = re.compile(r"\b(?:C|NL|AM|CM|ST|CD|CS|GR|LG|AD)-[A-Z0-9-]+\b")


def documents() -> list[pathlib.Path]:
    """Live workspace documents. `attic/` is retired material and is not gated."""
    return sorted(p for p in ROOT.rglob("*.md") if "attic" not in p.parts)


def audit_vocabulary() -> int:
    failures: list[str] = []
    for path in documents():
        for number, raw in enumerate(path.read_text().splitlines(), 1):
            line = CLAIM_ID.sub("", raw)
            for word in RETIRED:
                if not re.search(rf"\b{re.escape(word)}\b", line, re.I):
                    continue
                if word == "floor" and any(x in line for x in
                                           ("integer-floor", "rational-floor", "⌊")):
                    continue
                failures.append(f"{path.relative_to(ROOT)}:{number}: retired {word!r}")
            for notation in RETIRED_NOTATION:
                if re.search(rf"(?<![A-Za-z]){re.escape(notation)}(?![A-Za-z])", line):
                    failures.append(
                        f"{path.relative_to(ROOT)}:{number}: retired notation {notation!r}")
    if failures:
        raise AssertionError("retired vocabulary remains:\n" + "\n".join(failures))
    return len(documents())


def run_lean() -> bool:
    configured = os.environ.get("MATHLIB_DIR")
    if not configured:
        print("LEAN SKIPPED: set MATHLIB_DIR to a Mathlib-enabled Lake project")
        return False
    mathlib = pathlib.Path(configured).expanduser()
    lake = shutil.which("lake")
    if lake is None or not mathlib.is_dir():
        print("LEAN SKIPPED: no usable Lake project")
        return False
    for source in sorted((ROOT / "lean").glob("*.lean")):
        subprocess.run([lake, "env", "lean", str(source)], cwd=mathlib, check=True)
    print("LEAN CHECKED")
    return True


if __name__ == "__main__":
    print(f"VOCABULARY GATE: clean over {audit_vocabulary()} live documents")
    suite = unittest.defaultTestLoader.discover(str(ROOT / "tests"), pattern="test_*.py")
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    if not result.wasSuccessful():
        sys.exit(1)
    run_lean()
    print("WORKSPACE GREEN")
