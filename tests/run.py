#!/usr/bin/env python3
"""Repo-level runner: gate 1, plus the parts of gates 2 and 3 that need no toolchain.

Each project owns a self-contained runner; this one discovers and runs them, and
reports a per-project verdict. It adds the repo-level checks the projects cannot
do for themselves: every gate's null-input self-test, gate coverage, the name
lint, contributor-checker hygiene, conservativity, and the Lean sorry-free gate.

Lean compilation itself is not run here — it needs a toolchain and a warm cache,
and it is the one check with a wall time measured in minutes. Run
`lake build` in `lean/`, or set `WORKSPACE_LEAN=1` to have this runner do it.
"""
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]


def project_runners() -> list[pathlib.Path]:
    """Every `tests/run.py` under projects/, excluding this one."""
    return sorted(p for p in (ROOT / "projects").rglob("tests/run.py")
                  if "attic" not in p.parts)


def run_projects() -> list[tuple[str, bool]]:
    results = []
    for runner in project_runners():
        project = runner.parents[1].relative_to(ROOT).as_posix()
        proc = subprocess.run([sys.executable, "tests/run.py"], cwd=runner.parents[1],
                              capture_output=True, text=True)
        ok = proc.returncode == 0
        results.append((project, ok))
        print(f"  {'PASS' if ok else 'FAIL'}  {project}")
        if not ok:
            print(proc.stdout[-2000:]); print(proc.stderr[-2000:])
    return results


# Every gate ships a case proving it fails on its null input — see AGENTS.md.
# Running them here as well as in CI means a local run cannot report green off a
# gate that has quietly stopped matching anything.
GATE_SELF_TESTS = ("path_gate", "dco", "attribution", "name_lint",
                   "contrib_hygiene", "conservativity", "audit_axioms",
                   "workflow_scope", "lean_scope", "round_records",
                   "dead_pointers")


# Gates whose real form needs a pull request: they read the event payload or a
# base ref, so locally they can only run their self-test. Listed rather than
# omitted, so the coverage check below can tell "no local form" from "forgotten".
PULL_REQUEST_ONLY = ("path_gate", "dco", "attribution", "lean_scope",
                     "round_records")


def self_tests() -> None:
    for gate in GATE_SELF_TESTS:
        subprocess.run([sys.executable, f"tests/{gate}.py", "--self-test"],
                       cwd=ROOT, check=True)
    subprocess.run([sys.executable, "-m", "checkers.run", "--self-test"],
                   cwd=ROOT, check=True)
    subprocess.run([sys.executable, "-m", "checkers.wiki_links", "--self-test"],
                   cwd=ROOT, check=True)
    subprocess.run([sys.executable, "-m", "checkers.wiki_state_bindings",
                    "--self-test"], cwd=ROOT, check=True)


def coverage() -> None:
    """Every gate script in tests/ is accounted for by this runner.

    A gate that exists and is never invoked is the same failure as a gate that
    matches nothing: green here would mean less than it appears to. This fails
    if someone adds a script to tests/ without wiring it in or declaring it
    pull-request-only.
    """
    present = {p.stem for p in (ROOT / "tests").glob("*.py")} - {"run.py", "run"}
    accounted = set(GATE_SELF_TESTS) | set(PULL_REQUEST_ONLY)
    missing = sorted(present - accounted)
    if missing:
        raise AssertionError(
            f"gate script(s) in tests/ that this runner never invokes: {missing}. "
            "Wire them in, or add them to PULL_REQUEST_ONLY with a reason.")
    print(f"GATE COVERAGE: {len(present)} gate scripts, all invoked "
          f"({len(PULL_REQUEST_ONLY)} self-test only — no local form)")


def lean_sorry_gate() -> int:
    """No `sorry` reaches a committed Lean file."""
    sources = sorted((ROOT / "lean" / "Workspace").rglob("*.lean"))
    offenders = [p.relative_to(ROOT).as_posix() for p in sources
                 if "sorry" in p.read_text()]
    if offenders:
        raise AssertionError(f"sorry in committed Lean source: {offenders}")
    return len(sources)


def lean_axiom_discipline() -> int:
    """Every committed Lean file ends with `#print axioms` lines."""
    missing = [p.relative_to(ROOT).as_posix()
               for p in sorted((ROOT / "lean" / "Workspace").rglob("*.lean"))
               if "#print axioms" not in p.read_text()]
    if missing:
        raise AssertionError(f"Lean file without `#print axioms`: {missing}")
    return 1


def lean_build() -> bool:
    if not os.environ.get("WORKSPACE_LEAN"):
        print("LEAN BUILD SKIPPED: set WORKSPACE_LEAN=1 to run `lake build`")
        return False
    subprocess.run(["lake", "build"], cwd=ROOT / "lean", check=True)
    print("LEAN BUILD: green")
    subprocess.run([sys.executable, "tests/audit_axioms.py"], cwd=ROOT, check=True)
    return True


if __name__ == "__main__":
    coverage()
    self_tests()
    subprocess.run([sys.executable, "tests/name_lint.py"], cwd=ROOT, check=True)
    subprocess.run([sys.executable, "tests/contrib_hygiene.py"], cwd=ROOT, check=True)
    subprocess.run([sys.executable, "tests/conservativity.py"], cwd=ROOT, check=True)
    subprocess.run([sys.executable, "tests/workflow_scope.py"], cwd=ROOT, check=True)
    subprocess.run([sys.executable, "-m", "checkers.workspace_state", "--check"],
                   cwd=ROOT, check=True)
    subprocess.run([sys.executable, "-m", "checkers.wiki_links"], cwd=ROOT, check=True)
    subprocess.run([sys.executable, "-m", "checkers.wiki_state_bindings"],
                   cwd=ROOT, check=True)
    print(f"LEAN SORRY GATE: clean over {lean_sorry_gate()} files")
    print(f"LEAN AXIOM DISCIPLINE: every file carries `#print axioms`")
    print("PROJECTS:")
    results = run_projects()
    lean_build()
    if not results:
        print("NO PROJECT RUNNERS FOUND")
    if any(not ok for _, ok in results):
        sys.exit(1)
    print(f"ALL GREEN ({len(results)} project(s))")
