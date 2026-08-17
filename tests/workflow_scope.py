#!/usr/bin/env python3
"""Write scope in CI is enumerated, conditioned, and read by something.

`AGENTS.md`'s *Security* section permits a job to hold write scope under four
conditions and names the jobs holding it. A conditional permission nothing reads
is the failure this repository has already paid for once: the residue sweep
reported clean while `README.md`'s third line violated a standing decision in
plain sight, which is why the naming rule became `tests/name_lint.py`. This is
the same move for the same reason.

**The enumeration lives in `AGENTS.md`**, not here, and is read from the
`write-scope` markers in that section — so the list a reader sees and the list
this gate enforces cannot come apart. Adding a job to it is an edit to the
document that states the rule, which is where a grant of write scope should be
visible.

What is checked, against the four conditions:

1. *`push` to a protected branch, never `pull_request`.* A workflow with a
   write-granting job must trigger on `push`, must restrict it to a branch this
   repository protects, and must not list `pull_request` or
   `pull_request_target` — which would put the scope within reach of anything a
   contributor submits.
2. *Publishes rather than adjudicates.* Checked in the one form a script can
   see: a write-granting job's context is not in the required-check list, so
   nothing merges on its verdict. **That no registry or protected setting is
   downstream of what it writes is a review matter**, and this gate does not
   pretend otherwise.
3. *The run token rather than a stored credential.* No workflow references any
   secret but `GITHUB_TOKEN`. This one is checked over every workflow, not only
   the write-granting ones: it is the absolute half of the rule.
4. *The grant on the job.* No workflow's top-level `permissions:` grants write,
   so a job added beside an existing one inherits nothing.

And the enumeration's own two failure directions: a write grant absent from it,
and an entry naming a job no workflow defines. The second reads as a reviewed
grant and is not one.

YAML is not in the standard library, and the parse below is line-oriented like
the rest of the harness. It is deliberately literal: it understands the
indentation these workflows are written in and reports what it could not parse
rather than assuming the file is clean.
"""
from __future__ import annotations

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"
AGENTS = ROOT / "AGENTS.md"
PROTECTION = ROOT / ".github" / "branch-protection.json"

# Branches this repository protects. `.github/apply-branch-protection.sh`
# applies the payload to exactly this one; a second protected branch belongs
# here and in that script together.
PROTECTED_BRANCHES = ("main",)

# The only credential any workflow may name. Everything else is a stored secret,
# which AGENTS.md forbids outright.
ALLOWED_SECRET = "GITHUB_TOKEN"

FORBIDDEN_TRIGGERS = ("pull_request", "pull_request_target")

MARKER = re.compile(
    r"<!--\s*write-scope:\s*job=([A-Za-z0-9_.-]+);\s*workflow=(\S+?)\s*-->")
KEY = re.compile(r"^(\s*)([A-Za-z0-9_.-]+)\s*:\s*(.*?)\s*$")
SECRET = re.compile(r"secrets\.([A-Za-z_][A-Za-z0-9_]*)")
WRITE_ENTRY = re.compile(r"^\s*[A-Za-z0-9_-]+\s*:\s*write\s*$")
INLINE_LIST = re.compile(r"\[([^]]*)\]")


def indent_of(line: str) -> int:
    return len(line) - len(line.lstrip())


def entries(lines: list[str], indent: int) -> list[tuple[str, str, list[str]]]:
    """Mapping keys at exactly `indent`, each with the lines nested under it.

    Blank and comment lines never end a block: the workflows carry comments at
    the indent of what they explain, and a parse that stopped at one would read
    a commented job as having no permissions at all."""
    found: list[tuple[str, str, list[str]]] = []
    index = 0
    while index < len(lines):
        match = KEY.match(lines[index])
        if match and len(match.group(1)) == indent:
            body: list[str] = []
            cursor = index + 1
            while cursor < len(lines):
                line = lines[cursor]
                if line.strip() and not line.lstrip().startswith("#") \
                        and indent_of(line) <= indent:
                    break
                body.append(line)
                cursor += 1
            found.append((match.group(2), match.group(3), body))
            index = cursor
        else:
            index += 1
    return found


def grants_write(inline: str, body: list[str]) -> bool:
    """A `permissions:` value granting write, in either form it is written."""
    if inline.strip() == "write-all":
        return True
    return any(WRITE_ENTRY.match(line) for line in body)


def branches(body: list[str]) -> list[str] | None:
    """The branch list a `push:` trigger is restricted to, or None if it is not."""
    for key, inline, nested in entries(body, indent_of(body[0]) if body else 0):
        if key != "branches":
            continue
        match = INLINE_LIST.search(inline)
        if match:
            return [b.strip().strip("'\"") for b in match.group(1).split(",") if b.strip()]
        return [line.strip().lstrip("-").strip().strip("'\"")
                for line in nested if line.strip().startswith("-")]
    return None


def parse(text: str) -> dict:
    lines = text.splitlines()
    top = entries(lines, 0)
    parsed: dict = {"triggers": set(), "push_branches": None,
                    "default_write": False, "jobs": {},
                    "secrets": set(SECRET.findall(text))}
    for key, inline, body in top:
        if key == "on":
            listed = INLINE_LIST.search(inline)
            if listed:
                parsed["triggers"] = {t.strip() for t in listed.group(1).split(",") if t.strip()}
            elif inline:
                parsed["triggers"] = {inline.strip()}
            else:
                for trigger, _, nested in entries(body, indent_of(body[0]) if body else 0):
                    parsed["triggers"].add(trigger)
                    if trigger == "push":
                        parsed["push_branches"] = branches(nested)
        elif key == "permissions":
            parsed["default_write"] = grants_write(inline, body)
        elif key == "jobs":
            depth = indent_of(body[0]) if body else 2
            for job, _, job_body in entries(body, depth):
                record = {"name": job, "write": False}
                for field, field_inline, field_body in entries(job_body, depth + 2):
                    if field == "name" and field_inline:
                        record["name"] = field_inline
                    elif field == "permissions":
                        record["write"] = grants_write(field_inline, field_body)
                parsed["jobs"][job] = record
    return parsed


def enumerated(text: str) -> set[tuple[str, str]]:
    """The (job, workflow) pairs AGENTS.md declares may hold write scope."""
    return {(m.group(1), m.group(2)) for m in MARKER.finditer(text)}


def required_contexts(payload: str) -> list[str]:
    return json.loads(payload)["required_status_checks"]["contexts"]


def problems(files: dict[str, str], agents: str, protection: str) -> list[str]:
    found: list[str] = []
    allowed = enumerated(agents)
    required = set(required_contexts(protection))
    defined: set[tuple[str, str]] = set()

    for path in sorted(files):
        parsed = parse(files[path])
        stored = parsed["secrets"] - {ALLOWED_SECRET}
        if stored:
            found.append(f"{path}: names stored secret(s) {sorted(stored)}; the only "
                         f"credential a workflow may name is {ALLOWED_SECRET}")
        if parsed["default_write"]:
            found.append(f"{path}: the workflow's default `permissions:` grants write. "
                         "The grant belongs on the job, so a job added beside an "
                         "existing one inherits nothing")
        for job, record in parsed["jobs"].items():
            defined.add((job, path))
            if not record["write"]:
                continue
            if (job, path) not in allowed:
                found.append(f"{path}: job {job!r} grants write scope and is not "
                             "named in AGENTS.md's Security section")
            if set(parsed["triggers"]) & set(FORBIDDEN_TRIGGERS):
                found.append(f"{path}: job {job!r} grants write scope in a workflow "
                             f"triggered by {sorted(set(parsed['triggers']) & set(FORBIDDEN_TRIGGERS))} — "
                             "reachable by what a contributor submits")
            if "push" not in parsed["triggers"]:
                found.append(f"{path}: job {job!r} grants write scope in a workflow "
                             "that does not trigger on `push`")
            elif parsed["push_branches"] is None:
                found.append(f"{path}: job {job!r} grants write scope on an "
                             "unrestricted `push` trigger; restrict it to a "
                             f"protected branch {list(PROTECTED_BRANCHES)}")
            else:
                loose = [b for b in parsed["push_branches"] if b not in PROTECTED_BRANCHES]
                if loose:
                    found.append(f"{path}: job {job!r} grants write scope on push to "
                                 f"unprotected branch(es) {loose}")
            if record["name"] in required:
                found.append(f"{path}: job {job!r} grants write scope and its context "
                             f"{record['name']!r} is a required check — a write-scoped "
                             "job publishes, it does not adjudicate")

    for job, path in sorted(allowed - defined):
        found.append(f"AGENTS.md names {job!r} in {path} as holding write scope, and "
                     "no workflow defines it. A stale entry reads as a reviewed grant")
    return found


def live_files() -> dict[str, str]:
    return {p.relative_to(ROOT).as_posix(): p.read_text()
            for p in sorted(WORKFLOWS.glob("*.yml")) + sorted(WORKFLOWS.glob("*.yaml"))}


def self_test() -> int:
    """Null inputs, and one crafted workflow per condition.

    The null input is an empty workflow set or an empty enumeration: both make
    `problems` return nothing, which is exactly what a clean repository returns,
    so `main` refuses them and that refusal is pinned here."""
    agents = "<!-- write-scope: job=publish; workflow=.github/workflows/publish.yml -->\n"
    protection = json.dumps({"required_status_checks": {"contexts": ["gate"]}})
    good = """name: publish
on:
  push:
    branches: [main]
permissions:
  contents: read
jobs:
  publish:
    name: publish
    permissions:
      contents: write
    steps:
      - env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
"""

    def over(text: str, path: str = ".github/workflows/publish.yml",
             marks: str = agents) -> int:
        return len(problems({path: text}, marks, protection))

    read_only = ("name: ci\non:\n  pull_request:\npermissions:\n  contents: read\n"
                 "jobs:\n  gate:\n    name: gate\n    permissions:\n"
                 "      contents: read\n    steps: []\n")

    cases = [
        ("an enumerated, conditioned write grant passes", over(good), 0),
        ("a read-only workflow on pull_request passes",
         len(problems({".github/workflows/ci.yml": read_only}, "", protection)), 0),
        # One crafted failure per condition. Each is the `good` workflow with a
        # single condition broken, so the count that changes names the cause.
        ("a write grant absent from the enumeration is caught",
         over(good, marks=""), 1),
        ("a write grant in a pull_request workflow is caught",
         over(good.replace("on:\n  push:\n    branches: [main]",
                           "on:\n  push:\n    branches: [main]\n  pull_request:")), 1),
        ("a write grant on an unprotected branch is caught",
         over(good.replace("branches: [main]", "branches: [scratch]")), 1),
        ("a write grant on an unrestricted push is caught",
         over(good.replace("  push:\n    branches: [main]", "  push:")), 1),
        ("a workflow-level write default is caught",
         over(good.replace("permissions:\n  contents: read",
                           "permissions:\n  contents: write")), 1),
        ("write-all at the workflow level is caught",
         over(good.replace("permissions:\n  contents: read", "permissions: write-all")), 1),
        ("a write-scoped job that is a required check is caught",
         over(good.replace("    name: publish", "    name: gate")), 1),
        ("a stored secret is caught",
         over(good.replace("secrets.GITHUB_TOKEN", "secrets.WIKI_PAT")), 1),
        ("an enumeration entry no workflow defines is caught",
         len(problems({".github/workflows/other.yml": read_only}, agents, protection)), 1),
        ("a comment above `permissions:` does not hide the grant",
         over(good.replace("    permissions:", "    # why this job writes\n    permissions:"),
              marks=""), 1),
        # Null inputs. Both return nothing, which is what a clean repository
        # returns, so main refuses them — and that refusal is what these pin.
        ("no workflows at all makes every enumerated entry stale",
         len(problems({}, agents, protection)), 1),
        ("an empty tree with an empty enumeration yields nothing to check",
         len(problems({}, "", protection)), 0),
        ("an empty enumeration over read-only workflows yields nothing to check",
         len(problems({".github/workflows/ci.yml": read_only}, "", protection)), 0),
        ("the gate refuses an empty workflow set",
         run({}, agents, protection, quiet=True), 1),
        ("the gate refuses an empty enumeration",
         run({".github/workflows/publish.yml": good}, "", protection, quiet=True), 1),
        # The live tree, so the gate cannot pass by having stopped matching.
        ("the workflow directory exists", WORKFLOWS.is_dir(), True),
        ("the live repository has workflows", len(live_files()) > 0, True),
        ("the live enumeration is non-empty",
         len(enumerated(AGENTS.read_text())) > 0, True),
        ("the required-check list is non-empty",
         len(required_contexts(PROTECTION.read_text())) > 0, True),
    ]
    failures = 0
    print("WORKFLOW SCOPE SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def run(files: dict[str, str], agents: str, protection: str,
        quiet: bool = False) -> int:
    """The gate's verdict over inputs it is handed, so the refusals are testable."""
    def say(message: str) -> None:
        if not quiet:
            print(message, file=sys.stderr)

    if not files:
        # A null input. No workflows means no findings, which is the same output
        # as a clean repository — and this one has CI.
        say("WORKFLOW SCOPE FAILED: no workflow files under .github/workflows")
        return 1
    if not enumerated(agents):
        # The other. An empty enumeration turns every write grant into a
        # finding, but over read-only workflows it passes while meaning
        # nothing, and a marker deleted from AGENTS.md is a lost grant.
        say("WORKFLOW SCOPE FAILED: AGENTS.md declares no write-scope entries. "
            "The Security section is where the list lives; a missing marker is a "
            "lost grant, not an empty one.")
        return 1
    found = problems(files, agents, protection)
    if found:
        say("WORKFLOW SCOPE FAILED:")
        for f in found:
            say(f"  - {f}")
        say("\n  AGENTS.md, Security: no credential is stored, and a job holds "
            "write scope only on a push-only trigger to a protected branch, "
            "publishing rather than adjudicating, on the run token, granted on "
            "the job. The jobs holding it are named in that section.")
        return 1
    if not quiet:
        print(f"WORKFLOW SCOPE: clean over {len(files)} workflow(s); "
              f"{len(enumerated(agents))} enumerated write-scope job(s)")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    return run(live_files(), AGENTS.read_text(), PROTECTION.read_text())


if __name__ == "__main__":
    sys.exit(main())
