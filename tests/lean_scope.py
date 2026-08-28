#!/usr/bin/env python3
"""Does this pull request reach the Lean gate? Decided here, and it fails closed.

The Lean build is the one check with a wall time in minutes, and most pull
requests here change no Lean at all. Skipping the work on those is what
`PRIORITIES.md` item 10 asks for — **restructuring the gate, not disabling it.**

Two things make that safe rather than a hole.

**The job still runs and still reports.** `lean` is a required check, and branch
protection matches it by exact string: a context that never arrives leaves every
pull request waiting for a status nobody will report. So the conditional is on
the *work*, not on the verdict — the job always emits its context, and when
nothing it verifies could have changed it emits success in seconds.

**The decision fails closed.** Every uncertainty builds: no pull-request context,
a diff that lists nothing, a git command that errors. A gate that skipped when it
could not see is a gate that grants passes precisely when something is wrong with
its inputs, which is the failure the null-input rule exists to prevent. The cost
of failing closed is one wasted build; the cost of failing open is an unverified
merge that reports green.

What reaches the gate, and why each is here:

- `lean/**` — the library, the toolchain pin, the lakefile and the manifest.
  Everything the build reads.
- `tests/audit_axioms.py` — the axiom audit the job runs after the build. Its
  verdict changes when it changes, with no Lean file touched.
- `tests/replay.py`, `tests/blanket_axioms.py` — the kernel-replay and
  blanket-axiom gates the job runs beside it, for the same reason. The second
  also carries the pinned commit of the tool it fetches, so a pin bump is a
  change to the Lean verdict with no Lean file touched.
- `tests/replay_fixture/**` — the replay gate's live fixture. It is Lean, it is
  built and replayed by the gate, and the gate's verdict is that replaying it
  *fails*; editing it changes what a green replay means.
- `.github/workflows/ci.yml` — the job definition. A change to how the gate runs
  re-runs it.
- `tests/lean_scope.py` — this file. The decision procedure must not be able to
  use itself to skip verifying a change to the decision procedure.

Adding to that list is safe; removing from it is a trust-chain edit, because a
path that leaves it is a path that can change the Lean verdict with the gate
reporting green.
"""
from __future__ import annotations

import fnmatch
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

REACHES_LEAN = (
    "lean/**",
    "tests/audit_axioms.py",
    "tests/replay.py",
    "tests/blanket_axioms.py",
    "tests/replay_fixture/**",
    ".github/workflows/ci.yml",
    "tests/lean_scope.py",
)


def reaches(path: str) -> bool:
    return any(fnmatch.fnmatch(path, pattern) for pattern in REACHES_LEAN)


def must_build(files: list[str] | None) -> tuple[bool, str]:
    """`None` means the diff could not be determined. Both unknowns build."""
    if files is None:
        return True, "no pull-request context; building"
    if not files:
        return True, "the diff listed no files, which is a broken diff and not a "\
                     "clean branch; building"
    reaching = sorted(f for f in files if reaches(f))
    if reaching:
        return True, f"{len(reaching)} changed file(s) reach the Lean gate: {reaching}"
    return False, f"none of the {len(files)} changed file(s) reach the Lean gate"


def changed_files() -> list[str] | None:
    base = os.environ.get("GITHUB_BASE_REF")
    if not base:
        return None
    fetch = subprocess.run(["git", "fetch", "--depth=1", "origin", base],
                           cwd=ROOT, capture_output=True)
    diff = subprocess.run(["git", "diff", "--name-only", f"origin/{base}...HEAD"],
                          cwd=ROOT, capture_output=True, text=True)
    if diff.returncode != 0:
        print(f"  git diff failed: {diff.stderr.strip()[:200]}", file=sys.stderr)
        if fetch.returncode != 0:
            print(f"  git fetch failed: {fetch.stderr.strip()[:200]}", file=sys.stderr)
        return None
    return [line for line in diff.stdout.splitlines() if line.strip()]


def self_test() -> int:
    """Null-input cases: every unknown builds.

    The null input here is an undetermined or empty diff, and the direction of
    its failure is the whole point — it must build, not skip."""
    cases = [
        ("a Lean source reaches the gate", must_build(["lean/Workspace/Smoke.lean"])[0], True),
        ("the toolchain pin reaches the gate", must_build(["lean/lean-toolchain"])[0], True),
        ("the lakefile reaches the gate", must_build(["lean/lakefile.toml"])[0], True),
        ("the manifest reaches the gate", must_build(["lean/lake-manifest.json"])[0], True),
        ("the axiom audit reaches the gate", must_build(["tests/audit_axioms.py"])[0], True),
        ("the replay gate reaches the gate", must_build(["tests/replay.py"])[0], True),
        ("the blanket axiom gate reaches the gate",
         must_build(["tests/blanket_axioms.py"])[0], True),
        ("the replay gate's live fixture reaches the gate",
         must_build(["tests/replay_fixture/Fixture/Unchecked.lean"])[0], True),
        ("the workflow definition reaches the gate",
         must_build([".github/workflows/ci.yml"])[0], True),
        ("this file reaches the gate", must_build(["tests/lean_scope.py"])[0], True),
        ("one reaching file among many still builds",
         must_build(["wiki/Home.md", "README.md", "lean/Workspace/Smoke.lean"])[0], True),
        # The skip, which is the only case that saves anything.
        ("a wiki-only change does not reach the gate",
         must_build(["wiki/Home.md", "wiki/CONVENTIONS.md"])[0], False),
        ("a documentation change does not reach the gate",
         must_build(["README.md", "DECISIONS.md", "PRIORITIES.md"])[0], False),
        ("a checker change does not reach the gate",
         must_build(["checkers/wiki_links.py"])[0], False),
        ("the sync workflow does not reach the gate",
         must_build([".github/workflows/wiki-sync.yml"])[0], False),
        # Fail-closed. Both of these would be a silent unverified merge if they
        # went the other way.
        ("an undetermined diff builds", must_build(None)[0], True),
        ("an empty diff builds rather than skipping", must_build([])[0], True),
        ("the reaching-path list is non-empty", bool(REACHES_LEAN), True),
        ("no reaching pattern is empty", all(REACHES_LEAN), True),
        # The live tree, so the patterns cannot pass by matching nothing.
        ("the Lean tree exists", (ROOT / "lean").is_dir(), True),
        ("the live Lean sources match the reaching patterns",
         all(reaches(p.relative_to(ROOT).as_posix())
             for p in (ROOT / "lean").rglob("*.lean")), True),
        ("the audit this job runs is a real file",
         (ROOT / "tests" / "audit_axioms.py").is_file(), True),
        ("every gate this job runs is a real file",
         all((ROOT / "tests" / f).is_file()
             for f in ("audit_axioms.py", "replay.py", "blanket_axioms.py")), True),
    ]
    failures = 0
    print("LEAN SCOPE SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    build, why = must_build(changed_files())
    print(f"LEAN SCOPE: {'build' if build else 'skip'} — {why}")
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a") as handle:
            handle.write(f"build={'true' if build else 'false'}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
