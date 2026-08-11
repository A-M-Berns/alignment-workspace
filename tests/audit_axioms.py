#!/usr/bin/env python3
"""Gate 2b: the axiom audit over the Lean library.

Every committed Lean file must end with `#print axioms` lines, and every result
they report must depend on **only** `propext`, `Classical.choice`, `Quot.sound`.
Anything else fails — which also catches `sorryAx`, since a `sorry` shows up
there rather than as a build error.

The audit re-elaborates each file with `lake env lean` rather than reading a
`lake build` log. That matters: an incremental build that has nothing to do
prints no `#print axioms` output at all, so a log-scraping audit silently passes
on an unchanged tree. Re-elaborating cannot be fooled that way.
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
LIB = LEAN / "Workstudio"

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")


def sources() -> list[pathlib.Path]:
    return sorted(LIB.rglob("*.lean"))


def main() -> int:
    files = sources()
    if not files:
        print("AXIOM AUDIT: no Lean sources found", file=sys.stderr)
        return 1

    failures: list[str] = []

    for path in files:
        text = path.read_text()
        if "sorry" in text:
            failures.append(f"{path.relative_to(ROOT)}: contains `sorry`")
        if "#print axioms" not in text:
            failures.append(f"{path.relative_to(ROOT)}: no `#print axioms` line")

    audited = 0
    for path in files:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path.relative_to(LEAN))],
            cwd=LEAN, capture_output=True, text=True)
        out = proc.stdout + proc.stderr
        if proc.returncode != 0:
            failures.append(f"{path.relative_to(ROOT)}: failed to elaborate\n{out[-1500:]}")
            continue
        reported = False
        for name, axioms in AXIOM_LINE.findall(out):
            reported = True
            audited += 1
            used = {a.strip() for a in axioms.split(",") if a.strip()}
            extra = used - ALLOWED
            if extra:
                failures.append(
                    f"{path.relative_to(ROOT)}: '{name}' depends on {sorted(extra)} "
                    f"outside the allowed {sorted(ALLOWED)}")
        for name in NO_AXIOMS.findall(out):
            reported = True
            audited += 1
        if not reported:
            failures.append(
                f"{path.relative_to(ROOT)}: `#print axioms` present but reported "
                "nothing — the declarations it names may not exist")

    if failures:
        print("AXIOM AUDIT FAILED:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1

    print(f"AXIOM AUDIT: {audited} results across {len(files)} files, "
          f"all within {sorted(ALLOWED)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
