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
    "AGENTS.md", "CONTRIBUTING.md", "DECISIONS.md", "PRIORITIES.md",
    "README.md", "PROVENANCE.md", "RESEARCH_STATE.md",
    "state/**",
    "LICENSE", "LICENSE.*",
    ".github/**", ".gitattributes", ".gitignore",
    "checkers/*.py", "checkers/README.md",
    "tests/**",
    "prompts/**",
    # Consolidated trees. Ordinary content, but not contributors' to edit:
    # the protection that used to be a hash gate is this list plus review.
    "projects/normativity/consolidation-aug9/**",
    "projects/normativity/deck-2026-08-10/**",
    "projects/deference/note-dump-2026-06-27/**",
    "projects/deference/note-dump-2026-08-11/**",
    "projects/deference/dose-response-note-dump-2026-07-02/**",
    "projects/deference/references-citations-2026-08-11/**",
    "lean/lakefile.toml", "lean/lean-toolchain", "lean/lake-manifest.json",
    "lean/Workspace.lean",
    "lean/Workspace/Smoke.lean",
    "lean/Workspace/*/Basic.lean",
    "lean/Workspace/*/Spec/**",
    "projects/*/CLAIMS.md", "projects/*/MODEL.md", "projects/*/README.md",
    "projects/*/THEOREMS.md",
    # A research line's notes/ is maintainer working space: roadmaps, status
    # ledgers, and the frozen per-round specification objects that dispatched
    # tracks bind to. Those are maintainer-owned by intent, and the enumeration
    # protected only four basenames there, so a canonical document was
    # specification layer or not according to what it was called.
    "projects/*/notes/**",
)

# The proof layer. Open; anyone or anyone's agent.
PROOF_PATHS = (
    # Contributor-supplied checkers. Adding one is prospective and contained;
    # modifying a house checker is retroactive, which is why only this
    # subdirectory is open. See AGENTS.md.
    "checkers/contrib/**",
    "lean/Workspace/*/Contrib/**",
    "projects/*/contrib/**",
    "projects/*/rounds/**",
)

# The maintainer set. This list and .github/CODEOWNERS must agree; changing one
# without the other is a defect. Maintainers are co-equal — see AGENTS.md.
MAINTAINERS = {"A-M-Berns", "abramdemski"}


def is_proof(path: str) -> bool:
    return any(fnmatch.fnmatch(path, pattern) for pattern in PROOF_PATHS)


def is_spec(path: str) -> bool:
    """Proof patterns win. `checkers/contrib/**` sits inside a specification
    directory and must not be captured by it."""
    if is_proof(path):
        return False
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


def self_test() -> int:
    """Null-input cases: the gate must not pass by matching nothing.

    Per AGENTS.md, every gate ships a case proving it fails on its null input.
    Here the null input is an empty changed-file list *inside* a pull request —
    which used to print "no pull-request context" and pass, indistinguishable
    from a gate that had classified the files and found them clean.
    """
    cases = [
        ("a specification path is recognised", is_spec("AGENTS.md"), True),
        ("a contributor checker is proof layer", is_proof("checkers/contrib/x.py"), True),
        ("proof patterns beat spec patterns",
         is_spec("checkers/contrib/x.py"), False),
        ("a house checker stays specification", is_spec("checkers/witness.py"), True),
        ("an unknown path is in neither layer",
         is_spec("scratch/notes.txt") or is_proof("scratch/notes.txt"), False),
        ("the renamed priorities file is specification",
         is_spec("PRIORITIES.md"), True),
        # A root governance document matches no other pattern, and the default
        # for an unlisted path is the proof layer. Enumerating it is the whole
        # protection; nothing else would have caught its absence.
        ("the research-state document is specification",
         is_spec("RESEARCH_STATE.md"), True),
        ("structured workspace state is specification",
         is_spec("state/projects.json"), True),
        # A line's notes/ is maintainer working space whatever a file is called.
        # The enumeration matches on basename — `*` crosses a separator — so
        # before this pattern `notes/README.md` was specification and
        # `notes/ROADMAP.md` was in neither layer.
        ("an arbitrary file under a line's notes is specification",
         is_spec("projects/aline/notes/arbitrary-name.md"), True),
        ("a notes file at depth is specification",
         is_spec("projects/aline/notes/sub/dir/thing.txt"), True),
        ("a contribution surface under notes stays proof layer",
         is_spec("projects/aline/notes/contrib/x.py"), False),
        # Author-written material is enumerated like a received tree: a
        # contributor may cite it and may not edit it. An unlisted path defaults
        # to the proof layer, so the enumeration is the whole protection.
        ("the author's deck is specification",
         is_spec("projects/normativity/deck-2026-08-10/ORIGIN.md"), True),
        ("a round output tree stays proof layer",
         is_spec("projects/normativity/rounds/2026-08-11-phi-regret-prep/src/model.py"),
         False),
        ("the maintainer set is non-empty", bool(MAINTAINERS), True),
        ("no specification pattern is empty", all(SPEC_PATHS), True),
    ]
    failures = 0
    print("PATH GATE SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    actor = os.environ.get("GITHUB_ACTOR", "")
    files = changed_files()
    in_pull_request = bool(os.environ.get("GITHUB_BASE_REF"))
    if not files:
        if in_pull_request:
            # The null input. A pull request always changes something, so an
            # empty list means the diff failed, not that the branch is clean —
            # and passing here would gate nothing while reporting green.
            print("PATH GATE FAILED: in a pull request but the diff against "
                  f"origin/{os.environ.get('GITHUB_BASE_REF')} listed no files. "
                  "The gate cannot classify what it cannot see.", file=sys.stderr)
            return 1
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
