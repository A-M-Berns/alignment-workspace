"""The path gate: proof-layer pull requests may not touch the specification layer.

Every file belongs to exactly one layer. The specification layer is
maintainer-owned and its contents are what the repository's verdicts depend on;
the proof layer is open to anyone. There is **no intermediate trust tier** — no
"trusted contributor" role that bypasses this. Verdicts come from the checkers or
from the maintainer, and nothing in between.

On a pull request this fails if a non-maintainer touches a specification path.
Locally, with no pull-request context, it prints the classification so a
contributor can see where a file lands before submitting.
"""
from __future__ import annotations

import fnmatch
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

# The specification layer. Proposed enumeration — AUTHOR CONFIRMS (DECISIONS.md).
SPEC_PATHS = (
    "AGENTS.md", "CONTRIBUTING.md", "DECISIONS.md", "OPEN_PROBLEMS.md",
    "README.md", "PROVENANCE.md", "SETUP_REPORT.md", "GOVERNANCE_REPORT.md",
    "LICENSE", "LICENSE.*",
    ".github/**", ".gitattributes", ".gitignore",
    "checkers/**",
    "tests/**",
    "frozen/**",
    "prompts/**",
    "lean/lakefile.toml", "lean/lean-toolchain", "lean/lake-manifest.json",
    "lean/Workstudio.lean",
    "lean/Workstudio/Smoke.lean",
    "lean/Workstudio/*/Basic.lean",
    "lean/Workstudio/*/Spec/**",
    "projects/*/CLAIMS.md", "projects/*/MODEL.md", "projects/*/README.md",
    "projects/*/THEOREMS.md",
)

# The proof layer. Open; anyone or anyone's agent.
PROOF_PATHS = (
    "lean/Workstudio/*/Contrib/**",
    "projects/*/contrib/**",
    "projects/*/rounds/**",
)

MAINTAINERS = {"A-M-Berns"}


def is_spec(path: str) -> bool:
    return any(fnmatch.fnmatch(path, pattern) for pattern in SPEC_PATHS)


def changed_files() -> list[str]:
    base = os.environ.get("GITHUB_BASE_REF")
    if not base:
        return []
    subprocess.run(["git", "fetch", "--depth=1", "origin", base],
                   cwd=ROOT, capture_output=True)
    diff = subprocess.run(["git", "diff", "--name-only", f"origin/{base}...HEAD"],
                          cwd=ROOT, capture_output=True, text=True)
    return [l for l in diff.stdout.splitlines() if l.strip()]


def main() -> int:
    actor = os.environ.get("GITHUB_ACTOR", "")
    files = changed_files()
    if not files:
        print("PATH GATE: no pull-request context; classification only")
        print(f"  specification patterns: {len(SPEC_PATHS)}")
        print(f"  proof patterns:         {len(PROOF_PATHS)}")
        return 0
    touched_spec = [f for f in files if is_spec(f)]
    if not touched_spec:
        print(f"PATH GATE: {len(files)} file(s) changed, none in the specification layer")
        return 0
    if actor in MAINTAINERS:
        print(f"PATH GATE: {len(touched_spec)} specification path(s) touched by "
              f"maintainer {actor!r} — allowed, and requires a review that means "
              "actually reading")
        for f in touched_spec:
            print(f"    {f}")
        return 0
    print("PATH GATE FAILED: this pull request touches the specification layer, "
          "which is maintainer-owned:", file=sys.stderr)
    for f in touched_spec:
        print(f"  - {f}", file=sys.stderr)
    print("\n  The specification layer is what the repository's verdicts depend on: "
          "definitions and statements of record, the checker harness, CI, toolchain "
          "pins, the axiom allowance, budgets, and the governance documents.\n"
          "  Proof-layer contributions go under the contribution namespaces. If your "
          "work genuinely needs a specification change, open an issue proposing it — "
          "that is a maintainer decision, not a gate to route around.", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
