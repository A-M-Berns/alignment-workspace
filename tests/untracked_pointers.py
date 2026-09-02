#!/usr/bin/env python3
"""Gate: a cited path is in the repository, not merely on this disk.

**The failure this exists for.** Six research rounds sat off `main` for a day
behind a merged badge. Their pull requests were merged — into *each other*: the
stack was based on a branch that had already reached `main`, so eleven commits
carrying six round directories stayed on the branch and nothing from the top of the
stack to `main` was ever opened. The forge said MERGED and meant it; a merged badge
names the base the pull request had, not the default branch.

It surfaced only because a consolidation happened to cite two of the missing
directories by path. `tests/dead_pointers.py` failed in CI and **passed locally**,
and the local pass was the misleading signal: the shared checkout carried those
directories as untracked files left by another session, so `exists()` was true there
and false on a clean clone.

That gap is the whole content of this gate. A pointer that resolves only because of
what is lying around in one working tree is not a pointer, and every other gate
agrees with the local run rather than with the repository.

**What is checked.** Two populations, both required to be tracked by git:

- every `path`, `verdict_source` and `prompt` a round record names in
  `state/rounds.json` — a round index is a claim about repository contents;
- every rooted path cited in the live documents that **exists on disk**. Existence
  is the precondition, because a path that does not exist at all is
  `dead_pointers.py`'s business and reporting it twice helps nobody. What is left
  is exactly the dangerous case: present, cited, and not in the repository.

**Why not fold this into the dead-pointer gate.** That gate adjudicates whether a
pointer resolves. This one adjudicates whether the thing it resolves to is shared.
They fail for different reasons and a reader deserves to be told which happened —
"you deleted something" and "you never committed something" call for opposite
fixes.

**Untracked and uncited is fine.** Scratch files, worktrees and local notes are
nobody's business here. A file becomes this gate's concern when a tracked document
points at it.
"""
from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

CITATION = re.compile(r"`([^`\n]+)`")


def tracked_paths() -> set[str]:
    """Every path git has, as posix strings, plus every directory containing one."""
    out = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "-z"],
        capture_output=True, text=True, check=True).stdout
    files = {p for p in out.split("\0") if p}
    dirs: set[str] = set()
    for f in files:
        parts = f.split("/")
        for i in range(1, len(parts)):
            dirs.add("/".join(parts[:i]))
    return files | dirs


def rooted_names() -> set[str]:
    return {p.name for p in ROOT.iterdir() if p.name != ".git"}


def live_documents() -> list[pathlib.Path]:
    docs = [ROOT / name for name in
            ("README.md", "AGENTS.md", "CONTRIBUTING.md", "PRIORITIES.md",
             "DECISIONS.md", "PROVENANCE.md", "RESEARCH_STATE.md")]
    docs += sorted(ROOT.glob("wiki/*.md"))
    docs += sorted(ROOT.glob("projects/*/CLAIMS.md"))
    docs += sorted(ROOT.glob("projects/*/notes/*.md"))
    docs += sorted(ROOT.glob("projects/*/legitimacy/checkpoint-*/*.md"))
    return [d for d in docs if d.is_file()]


def cited_paths(text: str, rooted: set[str]) -> list[str]:
    found = []
    for match in CITATION.finditer(text):
        raw = match.group(1).strip().rstrip(",.;:")
        if "*" in raw or " " in raw or "/" not in raw:
            continue
        if raw.split("/", 1)[0] not in rooted:
            continue
        found.append(raw.rstrip("/"))
    return found


def round_record_paths() -> list[tuple[str, str]]:
    index = ROOT / "state" / "rounds.json"
    if not index.is_file():
        return []
    data = json.loads(index.read_text())
    rounds = data["rounds"] if isinstance(data, dict) else data
    out = []
    for record in rounds:
        for field in ("path", "verdict_source", "prompt"):
            value = record.get(field)
            if isinstance(value, str) and value:
                out.append((f"state/rounds.json[{record.get('id')}].{field}",
                            value.rstrip("/")))
    return out


def audit() -> tuple[list[str], dict[str, int]]:
    tracked = tracked_paths()
    problems: list[str] = []
    counts = {"round-records": 0, "citations": 0}

    for origin, path in round_record_paths():
        counts["round-records"] += 1
        if path not in tracked:
            problems.append(
                f"{origin}: `{path}` is not in the repository"
                + (" — it exists here but is untracked"
                   if (ROOT / path).exists() else " — and does not exist"))

    rooted = rooted_names()
    for doc in live_documents():
        name = doc.relative_to(ROOT).as_posix()
        for path in cited_paths(doc.read_text(encoding="utf-8"), rooted):
            if not (ROOT / path).exists():
                continue  # dead_pointers.py's business, not this gate's
            counts["citations"] += 1
            if path not in tracked:
                problems.append(
                    f"{name}: `{path}` exists here but is not in the repository")
    return problems, counts


def self_test() -> int:
    tracked = tracked_paths()
    rooted = rooted_names()
    cases = [
        ("a tracked file is tracked", "tests/run.py" in tracked, True),
        ("a tracked file's directory is tracked", "tests" in tracked, True),
        ("a nonexistent path is not tracked",
         "tests/no-such-file-here.py" in tracked, False),
        ("a path is not confused with a longer sibling",
         "test" in tracked, False),
        ("a rooted citation is extracted",
         cited_paths("See `tests/run.py`.", rooted), ["tests/run.py"]),
        ("an unrooted citation is skipped",
         cited_paths("See `src/model.py`.", rooted), []),
        ("a bare word is not a path", cited_paths("The `README` file.", rooted), []),
        ("a glob is not a pointer",
         cited_paths("Files `projects/*/CLAIMS.md` match.", rooted), []),
        ("prose in backticks is not a path",
         cited_paths("Call it `the claim measure`.", rooted), []),
        # The live tree, so the patterns cannot pass by matching nothing.
        ("the live documents exist", len(live_documents()) > 10, True),
        ("round records are found", len(round_record_paths()) > 10, True),
        ("git reports a populated tree", len(tracked) > 100, True),
    ]
    failures = 0
    print("UNTRACKED POINTERS SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")

    # The null input, run against a real fixture: a file that exists and is not
    # tracked is exactly the September 2026 failure, reproduced.
    scratch = ROOT / ".untracked-pointer-selftest"
    scratch.mkdir(exist_ok=True)
    (scratch / "note.md").write_text("fixture\n", encoding="utf-8")
    try:
        live = tracked_paths()
        got = ".untracked-pointer-selftest/note.md" in live
        failures += got is not False
        print(f"  {'ok' if got is False else 'FAIL'}: "
              "a file present on disk but uncommitted is not tracked")
    finally:
        (scratch / "note.md").unlink()
        scratch.rmdir()
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    problems, counts = audit()
    if counts["round-records"] == 0:
        print("UNTRACKED POINTERS FAILED: no round record was read. The gate "
              "cannot see what it is meant to check.", file=sys.stderr)
        return 1
    if problems:
        print("UNTRACKED POINTERS FAILED:", file=sys.stderr)
        for problem in problems:
            print(f"  - {problem}", file=sys.stderr)
        print("\n  A path that resolves only because of what is lying around in "
              "one working tree is not a pointer. Commit it, or stop citing it. "
              "If a round directory is missing, check whether its pull request "
              "merged into another branch rather than into the default one — a "
              "merged badge names the base the pull request had, not `main`.",
              file=sys.stderr)
        return 1
    print(f"UNTRACKED POINTERS: clean — {counts['round-records']} round-record "
          f"path(s) and {counts['citations']} resolving citation(s) are in the "
          "repository, not merely on this disk")
    return 0


if __name__ == "__main__":
    sys.exit(main())
