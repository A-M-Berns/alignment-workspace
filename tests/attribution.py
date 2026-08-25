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
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

HEADING = re.compile(r"^##+\s*Model attribution\s*$", re.I | re.M)
NEXT_HEADING = re.compile(r"^##+\s", re.M)
COMMENT = re.compile(r"<!--.*?-->", re.S)
UNCHECKED = re.compile(r"^\s*[-*]\s*\[\s*\]")
CHECKED = re.compile(r"^\s*[-*]\s*\[[xX]\]", re.M)
BULLET = re.compile(r"^\s*[-*]\s")
INDENTED = re.compile(r"^\s+\S")

# A body that names a model, and a commit that names one. The body form allows
# the `Prompt-author-model:` variant and the template's bold markers; the trailer
# form is the `Model:` line `AGENTS.md` asks each commit to carry.
#
# Two things the body form is deliberate about, both found by running it against
# a real pull request. It is **not** anchored to the start of a line: the
# template's dispatched-round option puts `Model:` on a continuation line after
# `and`, and an anchored pattern skipped the check on the very pull request that
# introduced it — a gate matching nothing. And a backticked `` `Model:` `` is
# excluded, because prose *about* this gate would otherwise read as a
# declaration. Emphasis asterisks are skipped on both sides of the colon rather
# than counted as a value: `- [x] **Model:**` with the name still inside the
# template's comment names nobody, and reading `**` as content would let a ticked
# empty option pass.
DECLARES_MODEL = re.compile(r"(?<!`)\**(?:Prompt-author-)?Model\**[^\S\n]*"
                            r":[\t *]*[^\s*`]", re.I)
TRAILER = re.compile(r"^Model:[^\S\n]*\S", re.M)


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


def evidence(content: str) -> str:
    """What the section actually says, once the template is subtracted.

    Template comments and unchecked boxes assert nothing: an untouched template
    is non-empty as a string, and treating that as a pass would make the gate
    ceremonial. Dropping an unchecked option means dropping the whole option,
    not just its `- [ ]` marker — the template's options carry their own label
    text, and stripping the marker alone would leave "Human-written — no model
    produced…" behind and read an untouched template as an assertion.
    """
    kept: list[str] = []
    dropping = False
    for line in COMMENT.sub("", content).splitlines():
        if UNCHECKED.match(line):
            dropping = True
            continue
        if dropping and (INDENTED.match(line) or not line.strip()):
            continue
        dropping = False
        if not BULLET.match(line) or line.strip():
            kept.append(line)
    return "\n".join(kept)


def asserted(content: str) -> bool:
    """Something was actually filled in.

    A ticked box counts, and so does free prose — a contributor who writes
    `Model: X` without ticking anything has attributed.
    """
    if CHECKED.search(COMMENT.sub("", content)):
        return True
    return bool(evidence(content).strip())


def declares_model(content: str) -> bool:
    """The section names a model, rather than declaring the work human-written."""
    return bool(DECLARES_MODEL.search(evidence(content)))


def commits() -> list[str]:
    """The non-merge commits this pull request adds, or [] outside one.

    Merges are excluded for the reason `tests/dco.py` excludes them: GitHub
    checks out a synthetic merge of the branch into its base, and that commit has
    no author who could have written a trailer on it.
    """
    base = os.environ.get("GITHUB_BASE_REF")
    if not base:
        return []
    subprocess.run(["git", "fetch", "--depth=50", "origin", base],
                   cwd=ROOT, capture_output=True)
    out = subprocess.run(["git", "rev-list", "--no-merges", f"origin/{base}..HEAD"],
                         cwd=ROOT, capture_output=True, text=True)
    return [c for c in out.stdout.split() if c]


def untrailered(shas: list[str]) -> list[str]:
    missing = []
    for sha in shas:
        message = subprocess.run(["git", "log", "-1", "--format=%B", sha],
                                 cwd=ROOT, capture_output=True, text=True).stdout
        if not TRAILER.search(message):
            subject = message.strip().splitlines()[0] if message.strip() else "(empty)"
            missing.append(f"{sha[:9]}  {subject[:70]}")
    return missing


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

    # The per-commit half. It fires only where the body names a model, so a
    # human-written pull request is asked for nothing new; the null input is a
    # body that names one against a commit list that does not.
    trailer_cases = [
        ("a body naming an executor declares a model",
         declares_model("Model: Claude Opus 5 (Anthropic)\n"), True),
        ("a bulleted, bolded declaration is seen",
         declares_model("- **Model:** Claude Opus 5\n"), True),
        ("a ticked model box with a value is seen",
         declares_model("- [x] **Model:** Claude Opus 5 (Anthropic)\n"), True),
        ("a prompt-author declaration is seen",
         declares_model("Prompt-author-model: Claude Fable 5\n"), True),
        ("a ticked human-written box declares no model",
         declares_model("- [x] **Human-written** — no model produced it\n"), False),
        ("an empty section declares no model", declares_model(""), False),
        ("a label with no value declares no model", declares_model("Model:\n"), False),
        ("the pristine template declares no model",
         declares_model(section(template) or ""), False),
        ("the template's model option, ticked but unfilled, declares no model",
         declares_model(section(template.replace("- [ ] **Model:**",
                                                 "- [x] **Model:**", 1)) or ""), False),
        # The dispatched-round option, filled in as the template lays it out.
        # This is the shape that slipped past an anchored pattern.
        ("a declaration on a continuation line is seen",
         declares_model("- [x] **Dispatched round** — **Prompt-author-model:** "
                        "Claude Fable 5\n      and **Model:** Claude Opus 5\n"),
         True),
        ("prose about a `Model:` trailer is not a declaration",
         declares_model("This gate requires a `Model:` trailer on each commit.\n"),
         False),
        ("a trailered message passes",
         TRAILER.search("Subject\n\nModel: Claude Opus 5 (Anthropic)\n") is not None,
         True),
        ("a message with only a sign-off is caught",
         TRAILER.search("Subject\n\nSigned-off-by: A <a@b.c>\n") is not None, False),
        ("a prompt-author trailer alone is not the executor trailer",
         TRAILER.search("Subject\n\nPrompt-author-model: X\n") is not None, False),
        ("an empty message is caught", TRAILER.search("") is not None, False),
    ]
    for label, got, want in trailer_cases:
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

    if not DECLARES_MODEL.search(content):
        print("ATTRIBUTION: the pull request declares model attribution "
              "(asserted, not verified); it names no model, so no commit trailer "
              "is required")
        return 0

    shas = commits()
    if not shas:
        if os.environ.get("GITHUB_BASE_REF"):
            # The null input. A pull request has at least one non-merge commit,
            # so an empty list means the enumeration failed, and passing here
            # would check no trailers at all while reporting green.
            print("ATTRIBUTION FAILED: the body names a model, but no non-merge "
                  f"commit was found against origin/{os.environ['GITHUB_BASE_REF']}. "
                  "The gate cannot check trailers it cannot enumerate.",
                  file=sys.stderr)
            return 1
        print("ATTRIBUTION: the pull request declares model attribution "
              "(asserted, not verified); no commit context, so trailers are "
              "unchecked")
        return 0

    missing = untrailered(shas)
    if missing:
        print("ATTRIBUTION FAILED: the body names a model and these commits "
              "carry no `Model:` trailer:", file=sys.stderr)
        for m in missing:
            print(f"  - {m}", file=sys.stderr)
        print("\n  Attribution is recorded at both levels, and they are not "
              "redundant: the body is what a reviewer reads and what a squash "
              "composes `main`'s message from, and the trailer is what survives a "
              "merge that is not a squash. Amend with a `Model:` line, or "
              "`unrecorded` where the executor is genuinely unknown.",
              file=sys.stderr)
        return 1

    print(f"ATTRIBUTION: the pull request declares model attribution "
          f"(asserted, not verified), and all {len(shas)} commit(s) carry a "
          "`Model:` trailer")
    return 0


if __name__ == "__main__":
    sys.exit(main())
