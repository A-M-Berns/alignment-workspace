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

- Tracked Markdown only. `prompts/` is dispatch history kept verbatim, and the
  consolidated trees are received work whose own wording is not this
  repository's to rewrite; both are out of scope.
- `wiki/` is in scope. It is the source of the published human register, which
  is the prose most likely to name people and the prose a stranger reads first.
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

EXCLUDED_DIRS = ("prompts/",) + tuple(d + "/" for d in (
    "projects/normativity/consolidation-aug9",
    "projects/deference/note-dump-2026-06-27",
    "projects/deference/note-dump-2026-08-11",
    "projects/deference/dose-response-note-dump-2026-07-02",
    "projects/deference/references-citations-2026-08-11",
))
ALLOWED_FILES = ("DECISIONS.md",)

CODE_SPAN = re.compile(r"`[^`]*`")
LINK_TARGET = re.compile(r"\]\([^)]*\)")
FENCE = re.compile(r"^\s*```")


def markdown_files() -> list[str]:
    out = subprocess.run(["git", "ls-files", "*.md"], cwd=ROOT,
                         capture_output=True, text=True, check=True)
    return [f for f in out.stdout.split("\n")
            if f and (ROOT / f).is_file() and
            not f.startswith(EXCLUDED_DIRS) and f not in ALLOWED_FILES]


def offences(path: str) -> list[str]:
    found: list[str] = []
    in_fence = False
    for number, raw in enumerate((ROOT / path).read_text().splitlines(), 1):
        if FENCE.match(raw):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        line = LINK_TARGET.sub("]()", CODE_SPAN.sub("", raw))
        for name in MAINTAINER_NAMES:
            if re.search(rf"\b{re.escape(name)}\b", line):
                found.append(f"{path}:{number}: {name!r} in prose — {raw.strip()[:80]}")
    return found


def self_test() -> int:
    """Null-input cases: the lint must not pass by scanning nothing.

    Its null input is an empty file list — which already fails — and a name it
    cannot see. The backtick exemption is the deliberate hole (handles, paths,
    URLs), so it is pinned here: if someone widens it, these cases say so.
    """
    import tempfile
    tmp = pathlib.Path(tempfile.mkdtemp())
    def scan(text: str, path: str = "sample.md") -> int:
        f = tmp / path
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text)
        global ROOT
        keep, ROOT = ROOT, tmp
        try:
            return len(offences(path))
        finally:
            ROOT = keep
    cases = [
        ("a maintainer name in prose is caught", scan("The Berns program.\n") > 0, True),
        ("a second maintainer name is caught", scan("Ask Demski.\n") > 0, True),
        ("a handle in backticks is allowed", scan("See `A-M-Berns` on GitHub.\n"), 0),
        ("a handle in a Markdown link target is allowed",
         scan("See [the wiki](https://example.test/A-M-Berns/wiki).\n"), 0),
        ("a path in backticks is allowed",
         scan("Open `projects/deference/note-dump-2026-06-27/x.md`.\n"), 0),
        ("a fenced block is allowed",
         scan("```\nSigned-off-by: A. M. Berns\n```\n"), 0),
        ("ordinary prose is clean", scan("The program is not named.\n"), 0),
        ("the name list is non-empty", bool(MAINTAINER_NAMES), True),
        ("an empty file list fails rather than passing",
         len(markdown_files()) > 0, True),
        # The wiki's source is in scope by construction — it matches no
        # exclusion — which is exactly the kind of coverage that disappears
        # when someone adds an exclusion later. Both halves are pinned: that
        # the files are scanned, and that a name in one of them is caught.
        ("the wiki's pages are scanned",
         any(f.startswith("wiki/") for f in markdown_files()), True),
        ("a maintainer name in a wiki page is caught",
         scan("Written up by Demski.\n", "wiki/Home.md") > 0, True),
        ("no exclusion covers the wiki",
         "wiki/Home.md".startswith(EXCLUDED_DIRS), False),
    ]
    import shutil; shutil.rmtree(tmp)
    failures = 0
    print("NAME LINT SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
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
          f"(prompts/ and the consolidated trees out of scope, DECISIONS.md exempt)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
