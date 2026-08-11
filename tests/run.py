#!/usr/bin/env python3
"""Repo-level runner: every project's own runner, then the Lean gates.

Each project owns a self-contained runner; this one discovers and runs them, and
reports a per-project verdict. It adds two repo-level checks the projects cannot
do for themselves: the frozen-input digests, and the Lean sorry-free gate.

Lean compilation itself is not run here — it needs a toolchain and a warm cache,
and it is the one check with a wall time measured in minutes. Run
`lake build` in `lean/`, or set `WORKSTUDIO_LEAN=1` to have this runner do it.
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


def verify_frozen() -> int:
    """Frozen inputs are immutable; this is the check that says so."""
    manifest = json.loads((ROOT / "frozen" / "FROZEN_INPUT_CHECKSUMS.json").read_text())
    checked = 0
    for name, record in sorted(manifest["entries"].items()):
        target = ROOT / "frozen" / name
        if record["kind"] == "archive":
            if hashlib.sha256(target.read_bytes()).hexdigest() != record["sha256"]:
                raise AssertionError(f"frozen input changed: {name}")
        else:
            digest = hashlib.sha256()
            files = sorted(p for p in target.rglob("*") if p.is_file()
                           and "__pycache__" not in p.parts and p.name != ".DS_Store")
            for p in files:
                digest.update(p.relative_to(target).as_posix().encode())
                digest.update(hashlib.sha256(p.read_bytes()).digest())
            if digest.hexdigest() != record["sha256_tree"]:
                raise AssertionError(f"frozen tree changed: {name}")
        checked += 1
    return checked


def lean_sorry_gate() -> int:
    """No `sorry` reaches a committed Lean file."""
    sources = sorted((ROOT / "lean" / "Workstudio").rglob("*.lean"))
    offenders = [p.relative_to(ROOT).as_posix() for p in sources
                 if "sorry" in p.read_text()]
    if offenders:
        raise AssertionError(f"sorry in committed Lean source: {offenders}")
    return len(sources)


def lean_axiom_discipline() -> int:
    """Every committed Lean file ends with `#print axioms` lines."""
    missing = [p.relative_to(ROOT).as_posix()
               for p in sorted((ROOT / "lean" / "Workstudio").rglob("*.lean"))
               if "#print axioms" not in p.read_text()]
    if missing:
        raise AssertionError(f"Lean file without `#print axioms`: {missing}")
    return 1


def lean_build() -> bool:
    if not os.environ.get("WORKSTUDIO_LEAN"):
        print("LEAN BUILD SKIPPED: set WORKSTUDIO_LEAN=1 to run `lake build`")
        return False
    subprocess.run(["lake", "build"], cwd=ROOT / "lean", check=True)
    print("LEAN BUILD: green")
    return True


if __name__ == "__main__":
    print(f"FROZEN INPUTS VERIFIED: {verify_frozen()}")
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
