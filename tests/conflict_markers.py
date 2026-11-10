#!/usr/bin/env python3
"""No tracked text file carries git conflict markers.

The failure this exists for reached `main`: a pull request resolved a merge in
`DECISIONS.md` by committing both sides with the `<<<<<<<`, `=======` and
`>>>>>>>` lines still between them, and every gate stayed green — the ledger's
anchor lines parse, the markdown renders, and nothing read the file as a whole.
A marker in a ledger is the one kind of defect no reader is supposed to have to
look for, so this reads every tracked text file for the opening and closing
marker lines. The middle one (`=======`) is also a markdown heading underline
and is not matched on its own.

Scope: every file `git ls-files` lists, except files that do not decode as
text, this file, and completed round records — anything under `prompts/` or a
`rounds/` directory — which are history and may quote a marker. A line is a
marker when it starts with seven `<` or seven `>` followed by a space, the exact
form git writes.

Null input (`--self-test`): a tree with no tracked files is a broken run, not a
clean one, and fails; a file carrying the markers fails; a clean file passes.
"""
from __future__ import annotations

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OPEN = "<" * 7 + " "
CLOSE = ">" * 7 + " "
ROUND_RECORD_DIRS = ("prompts", "rounds")


def tracked(root: pathlib.Path) -> list[pathlib.Path]:
    out = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True,
                         text=True, check=True).stdout
    return [root / name for name in out.split("\0") if name]


def markers(path: pathlib.Path) -> list[int]:
    try:
        text = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        return []
    return [number for number, line in enumerate(text.splitlines(), 1)
            if line.startswith(OPEN) or line.startswith(CLOSE)]


def round_record(path: pathlib.Path, root: pathlib.Path) -> bool:
    """Completed round records are history: they may quote a marker line."""
    return any(part in ROUND_RECORD_DIRS for part in path.relative_to(root).parts[:-1])


def problems(root: pathlib.Path, files: list[pathlib.Path]) -> list[str]:
    found: list[str] = []
    me = pathlib.Path(__file__).resolve()
    for path in files:
        if path.resolve() == me or not path.is_file() or round_record(path, root):
            continue
        hits = markers(path)
        if hits:
            found.append(f"{path.relative_to(root).as_posix()}: conflict marker at line(s) "
                         + ", ".join(str(n) for n in hits))
    return found


def self_test() -> int:
    import shutil, tempfile
    tmp = pathlib.Path(tempfile.mkdtemp())
    subprocess.run(["git", "init", "-q", str(tmp)], check=True)
    (tmp / "clean.md").write_text("# Title\n=======\n\ntext\n")
    (tmp / "conflicted.md").write_text(OPEN + "HEAD\nours\n=======\ntheirs\n"
                                       + CLOSE + "origin/main\n")
    (tmp / "lone.md").write_text(OPEN + "HEAD\nours\n")
    (tmp / "prompts" / "2026-01-01-round").mkdir(parents=True)
    (tmp / "prompts" / "2026-01-01-round" / "REPORT.md").write_text("quoted:\n" + OPEN + "HEAD\n")
    subprocess.run(["git", "-C", str(tmp), "add", "."], check=True)
    empty = tmp / "nowhere"
    empty.mkdir()
    subprocess.run(["git", "init", "-q", str(empty)], check=True)
    cases = [
        ("a tracked file carrying both markers is caught",
         len(problems(tmp, [tmp / "conflicted.md"])), 1),
        ("the opening marker alone is caught",
         len(problems(tmp, [tmp / "lone.md"])), 1),
        ("a setext heading underline is not a marker",
         len(problems(tmp, [tmp / "clean.md"])), 0),
        ("a completed round record quoting a marker is history, not a finding",
         len(problems(tmp, [tmp / "prompts" / "2026-01-01-round" / "REPORT.md"])), 0),
        ("the tracked set is what is scanned",
         len(problems(tmp, tracked(tmp))), 2),
        ("a tree with no tracked files is the null input, which main() must reject",
         len(tracked(empty)), 0),
        ("the live tree has tracked files, so the run is not vacuous",
         len(tracked(ROOT)) > 0, True),
    ]
    shutil.rmtree(tmp)
    failures = 0
    print("CONFLICT MARKERS SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    files = tracked(ROOT)
    if not files:
        print("CONFLICT MARKERS FAILED: git lists no tracked files", file=sys.stderr)
        return 1
    found = problems(ROOT, files)
    if found:
        print("CONFLICT MARKERS FAILED:", file=sys.stderr)
        for f in found:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(f"CONFLICT MARKERS: clean over {len(files)} tracked file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
