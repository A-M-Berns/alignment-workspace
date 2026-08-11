#!/usr/bin/env python3
"""Gate 8b: the pull request declares model attribution.

Commit trailers already carry `Model:` and `Prompt-author-model:`. This gate
covers the level they miss. A reviewer reads the pull-request body, not each
commit in turn, and a squash merge composes `main`'s commit message from that
body — so attribution that lives only in trailers is invisible where it matters
and can vanish from history entirely.

**This checks that an assertion was made, not that it is true**, exactly as the
DCO gate says of itself. No gate can tell which model wrote a paragraph. What it
can do is refuse the silent omission, which is the failure mode actually seen:
not a false claim, but no claim at all.

It reads the body from the workflow event payload rather than the API, so it
needs no token and no network. Two consequences worth knowing:

- Outside a pull request there is no payload and the gate reports that it has
  nothing to check, rather than inventing a verdict.
- The payload is a snapshot from when the event fired. GitHub's "re-run jobs"
  replays that same snapshot, so a body edited after a failure will *not* be
  seen by a re-run. The workflow therefore lists `edited` among its
  `pull_request` trigger types, which fires a fresh event with the new body.
  Remove that and this gate becomes unfixable without an empty commit.
"""
from __future__ import annotations

import json
import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

HEADING = re.compile(r"^##+\s*Model attribution\s*$", re.I | re.M)
NEXT_HEADING = re.compile(r"^##+\s", re.M)
COMMENT = re.compile(r"<!--.*?-->", re.S)
UNCHECKED = re.compile(r"^\s*[-*]\s*\[\s*\]")
CHECKED = re.compile(r"^\s*[-*]\s*\[[xX]\]", re.M)
BULLET = re.compile(r"^\s*[-*]\s")
INDENTED = re.compile(r"^\s+\S")


def body() -> str | None:
    """The pull-request body from the event payload, or None outside a PR."""
    path = os.environ.get("GITHUB_EVENT_PATH")
    if not path or not pathlib.Path(path).is_file():
        return None
    payload = json.loads(pathlib.Path(path).read_text())
    pull = payload.get("pull_request")
    if pull is None:
        return None
    return pull.get("body") or ""


def section(text: str) -> str | None:
    """The Model attribution section's content, or None if there is no heading."""
    match = HEADING.search(text)
    if match is None:
        return None
    rest = text[match.end():]
    following = NEXT_HEADING.search(rest)
    return rest[:following.start()] if following else rest


def asserted(content: str) -> bool:
    """Something was actually filled in.

    Template comments and unchecked boxes do not count: an untouched template is
    non-empty as a string while asserting nothing, and treating that as a pass
    would make the gate ceremonial. A ticked box counts, and so does free prose —
    a contributor who writes `Model: X` without ticking anything has attributed.
    """
    stripped = COMMENT.sub("", content)
    if CHECKED.search(stripped):
        return True
    leftover: list[str] = []
    dropping = False
    for line in stripped.splitlines():
        if UNCHECKED.match(line):
            # Drop the whole option, not just its `- [ ]` marker: the template's
            # options carry their own label text, and stripping the marker alone
            # would leave "Human-written — no model produced…" behind and read an
            # untouched template as an assertion.
            dropping = True
            continue
        if dropping and (INDENTED.match(line) or not line.strip()):
            continue
        dropping = False
        if not BULLET.match(line) or line.strip():
            leftover.append(line)
    return bool("".join(leftover).strip())


def self_test() -> int:
    """The cases that decide whether this gate is real or ceremonial.

    The pristine template is the one that matters. An earlier draft passed it,
    because stripping the `- [ ]` marker left each option's label behind and the
    section read as non-empty. A gate that accepts an untouched template checks
    nothing at all, so that case is pinned here rather than tested once by hand.
    """
    template = (ROOT / ".github" / "PULL_REQUEST_TEMPLATE.md").read_text()
    cases: list[tuple[str, str, bool]] = [
        ("no section", "## Layer touched\n\n- [x] Specification layer\n", False),
        ("pristine template asserts nothing", template, False),
        ("comments only", "## Model attribution\n\n<!-- pick one -->\n", False),
        ("empty body", "", False),
        ("a box ticked", template.replace("- [ ] **Human-written**",
                                          "- [x] **Human-written**", 1), True),
        ("prose without a box",
         "## Model attribution\n\nModel: Claude Opus 5 (Anthropic)\n", True),
        ("unrecorded, ticked", "## Model attribution\n\n- [x] **unrecorded**\n", True),
    ]
    failures = 0
    print("ATTRIBUTION SELF-TEST:")
    for label, text, want in cases:
        content = section(text)
        got = content is not None and asserted(content)
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    text = body()
    if text is None:
        print("ATTRIBUTION: no pull-request context; nothing to check")
        return 0

    content = section(text)
    if content is None:
        print("ATTRIBUTION FAILED: the pull-request body has no `## Model "
              "attribution` section.", file=sys.stderr)
        print("\n  Add it, per `.github/PULL_REQUEST_TEMPLATE.md`. One of: "
              "human-written; the executor model; executor plus "
              "prompt-author-model for a dispatched round; or `unrecorded` where "
              "the executor is genuinely unknown. `unrecorded` is a better answer "
              "than a guess.", file=sys.stderr)
        return 1

    if not asserted(content):
        print("ATTRIBUTION FAILED: the `Model attribution` section asserts "
              "nothing — it holds only template comments and unticked boxes.",
              file=sys.stderr)
        print("\n  Tick one, or write the attribution in prose. This gate checks "
              "that a claim was made; it cannot check that the claim is true.",
              file=sys.stderr)
        return 1

    print("ATTRIBUTION: the pull request declares model attribution "
          "(asserted, not verified)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
