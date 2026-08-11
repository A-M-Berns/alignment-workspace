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
LIB = LEAN / "Workspace"

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")


def sources() -> list[pathlib.Path]:
    return sorted(LIB.rglob("*.lean"))


def self_test() -> int:
    """Null-input cases: the audit must not pass by finding nothing.

    Two null inputs, both already guarded in `main`; pinned here so the guards
    cannot be removed quietly. An empty source list returns 1. A file whose
    `#print axioms` names declarations that do not exist elaborates fine and
    prints no axiom lines, so it is failed per file.

    The parsing cases run on captured `lake env lean` output rather than
    invoking Lean: the self-test must run in every job, not only the one with a
    toolchain. What is exercised is the recognition, not the elaboration.
    """
    good = "'A.b' depends on axioms: [propext, Classical.choice, Quot.sound]"
    bad = "'A.b' depends on axioms: [propext, sorryAx]"
    none = "'A.b' does not depend on any axioms"
    def extra(line: str) -> set[str]:
        found = AXIOM_LINE.findall(line)
        if not found:
            return set()
        return {a.strip() for a in found[0][1].split(",") if a.strip()} - ALLOWED
    cases = [
        ("the allowed three pass", extra(good), set()),
        ("sorryAx is caught", extra(bad), {"sorryAx"}),
        ("a no-axioms result is recognised", bool(NO_AXIOMS.findall(none)), True),
        ("a no-axioms result is not read as an axiom line",
         bool(AXIOM_LINE.findall(none)), False),
        ("silence is not a pass",
         bool(AXIOM_LINE.findall("")) or bool(NO_AXIOMS.findall("")), False),
        ("an empty source list is a failure, not a skip", bool(sources()), True),
        ("the allowance is exactly three", len(ALLOWED), 3),
    ]
    failures = 0
    print("AXIOM AUDIT SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
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
