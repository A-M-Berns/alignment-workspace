#!/usr/bin/env python3
"""A change that lands a round lands the round's provenance row with it.

The failure this exists for happened, and it was found by accident. A pull
request's `DECISIONS.md` entries and five `PROVENANCE.md` rows never reached
`main` while every other file it wrote did: both files take new material at a
shared anchor — the head of a section, the end of a table — and another pull
request had inserted at that same anchor in between. `main` then stated a
constitutional rule whose decision the ledger did not record, and three
trust-chain files had no provenance row. Every gate was green throughout.

**This checks what a change adds, not what the repository contains.** The
distinction is the whole design. Over the whole tree the rule is not true and
cannot be made true: 30 of 49 completed rounds carry no `prompts/<round>/`
citation, because early rounds are covered by globs like `prompts/*/REPORT.md`
and the convention of a per-round row arrived later. A check needing a
thirty-entry allowlist is a check that matches nothing. Scoped to the diff, the
rule is exact — a round arriving now brings its row now — and it needs no
history rewritten and no exceptions.

Where it runs, and why both:

- **On a pull request**, against the base branch. Catches the author.
- **On a push to `main`**, against the previous commit on `main`. Catches the
  *merge*, which is where the loss actually happened — the pull request had its
  rows and the merge commit did not.

The null input is a context that should have a diff and does not: inside a pull
request or a push, an empty file list means the diff is broken, not that the
change is clean, and this fails rather than reporting green.

What it does not check: that a report's claim to have landed a `DECISIONS.md`
entry is true. Detecting that claim means reading English, and the counterpart
in this repository — `checkers/wiki_state_bindings.py` — exists because
detection in prose is the thing to avoid. A declaration convention would be the
way, and nothing here invents one.
"""
from __future__ import annotations

import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PROVENANCE = ROOT / "PROVENANCE.md"

ADDED_REPORT = re.compile(r"^prompts/([^/]+)/REPORT[^/]*\.md$")


def landed_rounds(added: list[str]) -> list[str]:
    """Round directories this change brings a report for."""
    found = []
    for path in added:
        match = ADDED_REPORT.match(path)
        if match and match.group(1) not in found:
            found.append(match.group(1))
    return sorted(found)


def unrecorded(rounds: list[str], provenance: str) -> list[str]:
    return [r for r in rounds if f"prompts/{r}/" not in provenance]


def diff_range() -> tuple[str, str] | None:
    """(range, description), or None outside a context that has a diff."""
    base = os.environ.get("GITHUB_BASE_REF")
    if base:
        subprocess.run(["git", "fetch", "--depth=1", "origin", base],
                       cwd=ROOT, capture_output=True)
        return f"origin/{base}...HEAD", f"the pull request against origin/{base}"
    if os.environ.get("GITHUB_EVENT_NAME") == "push":
        return "HEAD^..HEAD", "the push, against the previous commit"
    return None


def _names(span: str, *filters: str) -> list[str] | None:
    diff = subprocess.run(["git", "diff", *filters, "--name-only", span],
                          cwd=ROOT, capture_output=True, text=True)
    if diff.returncode != 0:
        return None
    return [l for l in diff.stdout.splitlines() if l.strip()]


def changed_and_added() -> tuple[list[str] | None, list[str] | None, str]:
    """(every changed path, the added ones, a description of the window).

    Both are needed, and conflating them was a bug this gate shipped with. The
    null input is a change that touches **nothing** — inside a pull request or a
    push that means the diff is broken, and passing would gate nothing. A change
    that modifies files without adding any is an ordinary change: it lands no
    round record, so there is nothing here to check, and failing it made every
    modify-only pull request red.
    """
    window = diff_range()
    if window is None:
        return None, None, "no pull-request or push context"
    span, description = window
    changed = _names(span)
    if changed is None:
        return [], [], f"{description} (git diff failed)"
    return changed, _names(span, "--diff-filter=A") or [], description


def verdict(changed: list[str] | None, added: list[str] | None,
            provenance: str) -> tuple[bool, str]:
    """The decision, separated from git so the null inputs are testable."""
    if changed is None:
        return True, "no pull-request or push context; nothing to compare"
    if not changed:
        return False, ("the diff listed no files at all, which is a broken diff "
                       "and not a clean change")
    rounds = landed_rounds(added or [])
    if not rounds:
        return True, f"{len(changed)} changed file(s) land no round record"
    missing = unrecorded(rounds, provenance)
    if missing:
        return False, "a round arrived without its provenance row: " + ", ".join(
            f"prompts/{r}/ is cited nowhere in PROVENANCE.md" for r in missing)
    return True, f"{len(rounds)} round(s) landed, each cited in PROVENANCE.md"


def self_test() -> int:
    """Null inputs, and the fixture drawn from the loss that motivated this."""
    row = ("| `wiki/**` | a round | `ci-only` | 2026-08-16 | "
           "`prompts/2026-08-16-wiki-in-repo-sync/` |")
    attribution_only = ("| `2026-08-16-wiki-in-repo-sync` | Claude Fable 5 | "
                        "Claude Opus 5 | 2026-08-16 |")
    added = ["prompts/2026-08-16-wiki-in-repo-sync/PROMPT.md",
             "prompts/2026-08-16-wiki-in-repo-sync/REPORT.md",
             "wiki/Home.md"]
    cases = [
        ("a landed round is detected from its report",
         landed_rounds(added), ["2026-08-16-wiki-in-repo-sync"]),
        ("a round with a provenance row passes",
         unrecorded(landed_rounds(added), row), []),
        # The fixture. This is what reached `main`: the attribution row survived
        # and every row citing the round's path did not.
        ("a round whose provenance rows were lost is caught",
         unrecorded(landed_rounds(added), attribution_only),
         ["2026-08-16-wiki-in-repo-sync"]),
        ("a change landing no round has nothing to check",
         landed_rounds(["AGENTS.md", "checkers/run.py"]), []),
        ("a round directory without a report is not a landed round",
         landed_rounds(["prompts/2026-08-17-x/PROMPT.md"]), []),
        ("an alternate report name still counts",
         landed_rounds(["prompts/2026-08-17-x/REPORT-ADDENDUM.md"]), ["2026-08-17-x"]),
        ("a nested path is not mistaken for a round",
         landed_rounds(["prompts/2026-08-17-x/sub/REPORT.md"]), []),
        ("an empty added-file list yields nothing to check", landed_rounds([]), []),
        ("an empty provenance file fails every landed round",
         unrecorded(["2026-08-17-x"], ""), ["2026-08-17-x"]),
        # The live tree: the patterns must still match something real.
        ("the provenance file exists", PROVENANCE.is_file(), True),
        ("the live provenance file cites at least one round",
         "prompts/2026-08-16-wiki-state-bindings/" in PROVENANCE.read_text(), True),
        # `verdict`, and the null input that decides whether this gate is usable.
        # The first case is the one it shipped wrong: a modify-only pull request
        # adds nothing and is perfectly ordinary, and failing it made every such
        # pull request red. The second is the real null input.
        ("a change that modifies files and adds none is not a broken diff",
         verdict(["AGENTS.md", "wiki/Home.md"], [], "")[0], True),
        ("a diff listing no files at all fails",
         verdict([], [], "")[0], False),
        ("outside a pull request or push there is nothing to compare",
         verdict(None, None, "")[0], True),
        ("a landed round without its provenance row fails",
         verdict(["prompts/2026-08-17-x/REPORT.md"],
                 ["prompts/2026-08-17-x/REPORT.md"], "")[0], False),
        ("a landed round with its provenance row passes",
         verdict(["prompts/2026-08-17-x/REPORT.md"],
                 ["prompts/2026-08-17-x/REPORT.md"],
                 "cites prompts/2026-08-17-x/ here")[0], True),
    ]
    failures = 0
    print("ROUND RECORDS SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    changed, added, description = changed_and_added()
    ok, message = verdict(changed, added, PROVENANCE.read_text())
    where = "" if changed is None else f"{description}: "
    if ok:
        print(f"ROUND RECORDS: {where}{message}")
        return 0
    print(f"ROUND RECORDS FAILED: {where}{message}", file=sys.stderr)
    print("\n  A round's report and its provenance row land together or the "
          "record is wrong in the direction nobody notices. If this fired on "
          "a merge rather than on the pull request, the row was written and "
          "lost — recover it rather than rewriting it.", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
