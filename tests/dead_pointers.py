#!/usr/bin/env python3
"""Gate: the live documents' pointers resolve, and pointers into declared trees say so.

Two failures this catches, and they are different.

**A pointer that no longer resolves.** `CONTRIBUTING.md` told readers to run a
script that had been deleted, and three documents claimed eight gates where seven
ran. Nothing noticed, because a dead pointer is invisible to every other gate: the
Lean gate sees no Lean, the path gate sees a path outside its list, and the name
lint sees ordinary prose.

**A pointer into a tree that has declared itself disposable or superseded.** Both
resolve, so the first check passes on both, and only one of them is safe to build
on. A superseding intake silently converts an unknown subset of live pointers into
stale ones, and the only way to find out which is to re-read both trees — the
corpus-reconciliation round paid that by hand across seven pointers, of which one
had materially changed.

**What is checked, and what is deliberately not.**

A citation is checked when it is *rooted*: its first segment names something this
repository has at top level. `src/outflow.py` inside a round's own prose is
relative to that round and this gate does not adjudicate it; `tests/run.py` is
rooted and must exist. That rule is what keeps the gate from drowning in false
positives, and the count of skipped citations is printed rather than hidden, so
"checked nothing" and "checked everything" cannot look alike.

**Globs are not checked.** A glob in the specification list is a pattern, not a
pointer: `projects/*/THEOREMS.md` protects a shape that may have no instance
today, and failing it would punish the enumeration for being prospective. Their
count is printed too.

A path that a document is *about* having deleted is wrapped in
`<!--historical-->…<!--/historical-->`, the marker `wiki/CONVENTIONS.md` already
defines for a statement that cannot rot. That is visible in the diff rather than
living in an allowlist here.

**The declared-tree half asks of a section, not of a sentence**, and it does not
ask it of `DECISIONS.md` at all. Section granularity, because a heading that says
*disposable* has said it for the paragraphs under it, and demanding the word again
per sentence would buy nothing and cost every future edit. The ledger is exempt
because *no negative ontologies* names it one of exactly two places history is
kept: a citation there records what was true when the entry was written, and
asking the history file to annotate history inverts its job. Its pointers must
still resolve, like everyone's.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

TICK = re.compile(r"`([^`\n]+)`")
PATHLIKE = re.compile(r"^[\w][\w./*-]*$")
HISTORICAL = re.compile(r"<!--historical-->.*?<!--/historical-->", re.S)

# A tree that says of itself, or that a successor says of it, that building on it
# is not safe. The word is what a citing paragraph has to carry.
DECLARED = {
    "projects/normativity/forward": "disposable",
    "projects/normativity/deck-2026-08-10": "snapshot",
    "projects/deference/note-dump-2026-06-27": "superseded",
}


def live_documents() -> list[pathlib.Path]:
    docs = [ROOT / name for name in
            ("README.md", "AGENTS.md", "CONTRIBUTING.md", "PRIORITIES.md",
             "DECISIONS.md", "PROVENANCE.md", "RESEARCH_STATE.md")]
    docs += sorted(ROOT.glob("wiki/*.md"))
    docs += sorted(ROOT.glob("projects/*/CLAIMS.md"))
    docs += sorted(ROOT.glob("projects/*/notes/*.md"))
    return [d for d in docs if d.is_file()]


def rooted_names() -> set[str]:
    return {p.name for p in ROOT.iterdir() if p.name != ".git"}


def sections(text: str) -> list[str]:
    """Blocks delimited by Markdown headings, each keeping its own heading.

    A table row is a section of one line, because a `PROVENANCE.md` row is a
    self-contained record and the row above it says nothing about it.
    """
    blocks: list[str] = []
    current: list[str] = []
    for line in text.splitlines():
        if line.startswith("#"):
            if current:
                blocks.append("\n".join(current))
            current = [line]
        elif line.lstrip().startswith("|"):
            if current:
                blocks.append("\n".join(current))
                current = []
            blocks.append(line)
        else:
            current.append(line)
    if current:
        blocks.append("\n".join(current))
    return blocks


def citations(text: str, rooted: set[str]) -> list[tuple[str, str]]:
    """(path, enclosing section) for every rooted, concrete, non-historical path."""
    stripped = HISTORICAL.sub(" ", text)
    found = []
    for block in sections(stripped):
        for match in TICK.finditer(block):
            raw = match.group(1).strip().rstrip(".,;:")
            if "/" not in raw or "*" in raw or not PATHLIKE.match(raw):
                continue
            if raw.split("/", 1)[0] in rooted:
                found.append((raw, block))
    return found


def declared_tree(path: str) -> tuple[str, str] | None:
    for tree, status in DECLARED.items():
        if path == tree or path.startswith(tree + "/"):
            return tree, status
    return None


def audit() -> tuple[list[str], list[str], dict[str, int]]:
    rooted = rooted_names()
    problems: list[str] = []
    listed: list[str] = []
    counts = {"checked": 0, "skipped-unrooted": 0, "globs": 0, "historical": 0,
              "into-declared-trees": 0, "ledger-exempt": 0}
    for doc in live_documents():
        text = doc.read_text()
        name = doc.relative_to(ROOT).as_posix()
        counts["historical"] += len(HISTORICAL.findall(text))
        for match in TICK.finditer(HISTORICAL.sub(" ", text)):
            raw = match.group(1).strip().rstrip(".,;:")
            if "/" not in raw or not PATHLIKE.match(raw):
                continue
            if "*" in raw:
                counts["globs"] += 1
            elif raw.split("/", 1)[0] not in rooted:
                counts["skipped-unrooted"] += 1
        for path, block in citations(text, rooted):
            counts["checked"] += 1
            if not (ROOT / path).exists():
                problems.append(f"{name}: `{path}` does not exist")
                continue
            declared = declared_tree(path)
            if declared is None:
                continue
            tree, status = declared
            counts["into-declared-trees"] += 1
            listed.append(f"{name}: `{path}` — {status} ({tree})")
            if name == "DECISIONS.md":
                counts["ledger-exempt"] += 1
                continue
            if status not in block.lower():
                problems.append(
                    f"{name}: `{path}` is under `{tree}`, which is declared "
                    f"{status}, and the section citing it does not say so")
    return problems, listed, counts


def self_test() -> int:
    """Null inputs: both failure directions, and the live tree behind them."""
    rooted = {"tests", "wiki", "projects"}
    cases = [
        ("a rooted path is picked up",
         citations("see `tests/run.py` here", rooted)[0][0], "tests/run.py"),
        ("an unrooted path is not this gate's business",
         citations("see `src/outflow.py` here", rooted), []),
        ("a glob is not a pointer",
         citations("see `projects/*/THEOREMS.md` here", rooted), []),
        ("prose without a slash is not a path",
         citations("the `Budgeter` lemma", rooted), []),
        ("a historical span is exempt",
         citations("<!--historical-->`tests/gone.py`<!--/historical-->", rooted), []),
        ("a declared tree is recognised from its root",
         declared_tree("projects/normativity/forward")[1], "disposable"),
        ("a declared tree is recognised from a file inside it",
         declared_tree("projects/normativity/forward/src/x.py")[1], "disposable"),
        ("a tree that declares nothing is not flagged",
         declared_tree("projects/normativity/notes/X.md"), None),
        ("a path is not confused with a longer sibling",
         declared_tree("projects/normativity/forwarding/x.md"), None),
        # The live tree, so the patterns cannot pass by matching nothing.
        ("the live documents exist", len(live_documents()) > 10, True),
        ("every declared tree is really there",
         all((ROOT / t).is_dir() for t in DECLARED), True),
    ]
    failures = 0
    print("DEAD POINTERS SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")

    # The two null inputs, run against real fixtures rather than asserted.
    fixtures = [
        ("a citation that does not resolve fails",
         "See `tests/no-such-file-here.py`.", True),
        ("a citation into a disposable tree without the word fails",
         "See `projects/normativity/forward/FORWARD.md` for the interface.", True),
        ("the same citation naming the status passes",
         "The disposable tree `projects/normativity/forward/FORWARD.md` says so.",
         False),
        ("an ordinary resolving citation passes", "Run `tests/run.py`.", False),
    ]
    rooted_live = rooted_names()
    for label, text, should_fail in fixtures:
        bad = []
        for path, block in citations(text, rooted_live):
            if not (ROOT / path).exists():
                bad.append(path)
                continue
            declared = declared_tree(path)
            if declared and declared[1] not in block.lower():
                bad.append(path)
        got = bool(bad)
        failures += got != should_fail
        print(f"  {'ok' if got == should_fail else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    problems, listed, counts = audit()
    if counts["checked"] == 0:
        print("DEAD POINTERS FAILED: no rooted path citation was found in any live "
              "document. The gate cannot see what it is meant to check.",
              file=sys.stderr)
        return 1
    for line in listed:
        print(f"  into a declared tree — {line}")
    if problems:
        print("DEAD POINTERS FAILED:", file=sys.stderr)
        for problem in problems:
            print(f"  - {problem}", file=sys.stderr)
        print("\n  A pointer either resolves or it is not a pointer. A pointer into "
              "a tree declared disposable or superseded resolves and is still not "
              "safe to build on, so the passage citing it says which it is. Wrap a "
              "path a document is about having deleted in "
              "<!--historical-->…<!--/historical-->.", file=sys.stderr)
        return 1
    print(f"DEAD POINTERS: clean over {len(live_documents())} live document(s) — "
          f"{counts['checked']} rooted path(s) resolve, "
          f"{counts['into-declared-trees']} of them into declared trees and each "
          f"saying so; {counts['skipped-unrooted']} unrooted and {counts['globs']} "
          f"glob(s) not this gate's business; {counts['historical']} historical "
          f"span(s) and {counts['ledger-exempt']} ledger citation(s) exempt")
    return 0


if __name__ == "__main__":
    sys.exit(main())
