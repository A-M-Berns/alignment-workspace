#!/usr/bin/env python3
"""Prose in this repository does not name the maintainers personally.

The program has no name and is not named after people. Maintainer *handles* are
necessarily public in a public repository and are fine anywhere; personal names
in prose are not.

Why a lint and not a memo. The licensing round ran a residue sweep and reported
clean while `README.md` line 3 read "the Berns-Demski research program" — the
sweep searched for change-memorial phrasing ("formerly", "migrated from") and so
could not see a standing decision being violated in plain sight. A decision that
is only written down is a decision that gets re-violated; this one is now
checked.

Scope, deliberately narrow:

- Tracked Markdown only. `prompts/` is dispatch history kept verbatim and
  `frozen/` is immutable, so both are out of scope by construction.
- `DECISIONS.md` is allowed. The ledger is where this repository keeps history,
  including the entry recording a maintainer joining, which cannot be written
  without a name.
- Anything inside backticks is allowed: handles, paths, URLs and command lines
  are infrastructure, not prose about a program.

This is not a specification-layer dependency for contributors. Nothing a
contributor writes needs to touch this file; it exists so a maintainer's own
prose cannot drift.

To update when the maintainer set changes: edit `MAINTAINER_NAMES` below. Keep
it to personal names — handles belong in `CODEOWNERS` and `tests/path_gate.py`.
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

MAINTAINER_NAMES = ("Berns", "Demski", "Anson", "Abram")

EXCLUDED_DIRS = ("prompts/", "frozen/")
ALLOWED_FILES = ("DECISIONS.md",)

CODE_SPAN = re.compile(r"`[^`]*`")
FENCE = re.compile(r"^\s*```")


def markdown_files() -> list[str]:
    out = subprocess.run(["git", "ls-files", "*.md"], cwd=ROOT,
                         capture_output=True, text=True, check=True)
    return [f for f in out.stdout.split("\n")
            if f and not f.startswith(EXCLUDED_DIRS) and f not in ALLOWED_FILES]


def offences(path: str) -> list[str]:
    found: list[str] = []
    in_fence = False
    for number, raw in enumerate((ROOT / path).read_text().splitlines(), 1):
        if FENCE.match(raw):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        line = CODE_SPAN.sub("", raw)
        for name in MAINTAINER_NAMES:
            if re.search(rf"\b{re.escape(name)}\b", line):
                found.append(f"{path}:{number}: {name!r} in prose — {raw.strip()[:80]}")
    return found


def main() -> int:
    files = markdown_files()
    if not files:
        print("NAME LINT: no Markdown in scope", file=sys.stderr)
        return 1

    failures = [f for path in files for f in offences(path)]
    if failures:
        print("NAME LINT FAILED: the program is not named after people.",
              file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        print("\n  Describe what the work is instead. Handles, paths and URLs are "
              "fine inside backticks; DECISIONS.md is exempt as the ledger.",
              file=sys.stderr)
        return 1

    print(f"NAME LINT: clean over {len(files)} Markdown files "
          f"(prompts/ and frozen/ out of scope, DECISIONS.md exempt)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
