#!/usr/bin/env python3
"""Gate 2d: every declaration in the library, not only the enumerated ones.

`tests/audit_axioms.py` audits what the `#print axioms` lines name. That is the
right shape for a *trust-surface inventory* — the lines are a per-file statement
of which results the file is standing behind, and this round does not touch
them. But its reach is the set of names somebody remembered to type. A helper
lemma, a definition nobody listed, a declaration added to a file whose print
lines were written before it: all built, all exported, none audited.

This gate closes that by asking a different question — *every* declaration
defined in a module under `Workspace`, against the same three axioms. The tool is
`leanprover-community/axiom-audit`, which reads the compiled environment rather
than the source text, so it also sees what no `grep` can: `native_decide`, whose
axiom is generated during compilation and appears in no source file, and an axiom
reaching in through an import.

**It classifies axioms; it does not revalidate proofs.** The tool loads the
environment at `trustLevel := 1024`, meaning imported constants are taken as
type-correct rather than re-checked. That is not a gap in the tool, it is the
division of labour: `tests/replay.py` revalidates proofs and classifies no
axioms, this gate classifies axioms and revalidates no proofs, and a fault that
is green in both had to defeat two different questions.

**Scope, and why it is not the default.** The lakefile globs `Workspace.+`, which
builds the submodules and *not* the root module `lean/Workspace.lean` — so the
tool's default (import the root module, audit its closure) would find no olean at
all, and the closure of that root would in any case miss every `Contrib/` module,
since the two `Basic.lean` namespace roots import none of them. The audit is
therefore given the module list explicitly, from the source tree, with
`--modules-from`. The consequence worth stating: this gate's coverage is defined
by what is on disk under `lean/Workspace/`, not by what any module happens to
import.

**The pin.** The tool is pinned to a tag *and* to the commit that tag resolved
to, and the commit is verified after the clone, because a tag is mutable and a
pin that can be moved by its publisher is not a pin. This is the same discipline
`leanprover/lean-action` applies to the same dependency.
"""
from __future__ import annotations

import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
LIB = LEAN / "Workspace"

# Same three as `tests/audit_axioms.py`. The self-test pins the agreement: two
# gates over the same library disagreeing about what is allowed would be a
# silent policy split, and the one a reader happened to open would be wrong.
ALLOWED = ("propext", "Classical.choice", "Quot.sound")

REPO = "https://github.com/leanprover-community/axiom-audit.git"
PINNED_REF = "v0.1.2"
PINNED_SHA = "46024e005996495c65ef609368e11ab39c4222e3"

# The module prefix audited, and the directory the module list is read from
# (relative to `lean/`, so the tool derives module names correctly).
AUDIT_ROOT = "Workspace"
AUDIT_DIR = "Workspace"


def verdict(returncode: int, stdout: str) -> tuple[list[str], dict]:
    """Every problem with an audit run, plus whatever report was parseable.

    Fails closed. Unparseable output, a report claiming nothing was audited, a
    root other than the one asked for, an allowlist other than the one asked for,
    and any violation are all failures — and so is a zero exit with no report,
    which is what an audit that silently did nothing looks like."""
    problems: list[str] = []
    try:
        report = json.loads(stdout.strip().splitlines()[-1]) if stdout.strip() else {}
    except (json.JSONDecodeError, IndexError):
        return [f"the audit printed no parseable JSON report (exit {returncode})"], {}
    if not report:
        return [f"the audit printed no report (exit {returncode})"], {}
    if "error" in report:
        problems.append(f"the audit could not run: {report['error']}")
    audited = report.get("audited")
    if not isinstance(audited, int) or audited <= 0:
        problems.append(f"the audit reports {audited!r} declarations audited; an audit "
                        "that audited nothing passes by checking nothing")
    if report.get("root") != AUDIT_ROOT:
        problems.append(f"the audit reports root {report.get('root')!r}, not {AUDIT_ROOT!r}")
    allowed = tuple(report.get("allowed") or ())
    if allowed != ALLOWED:
        problems.append(f"the audit ran with allowlist {list(allowed)}, not {list(ALLOWED)}")
    for violation in report.get("violations") or []:
        problems.append(f"{violation.get('decl')} depends on "
                        f"{violation.get('axioms')} outside {list(ALLOWED)}")
    if returncode != 0 and not problems:
        problems.append(f"the audit exited {returncode} while reporting no violation")
    return problems, report


def fetch_tool(workdir: pathlib.Path) -> tuple[pathlib.Path | None, list[str]]:
    """Clone the pinned tool, verify the commit, and build it against our pin."""
    clone = workdir / "axiom-audit"
    got = subprocess.run(["git", "clone", "--depth", "1", "--branch", PINNED_REF,
                          REPO, str(clone)], capture_output=True, text=True)
    if got.returncode != 0:
        return None, [f"cloning {REPO} at {PINNED_REF} failed: {got.stderr.strip()[:300]}"]
    head = subprocess.run(["git", "-C", str(clone), "rev-parse", "HEAD"],
                          capture_output=True, text=True).stdout.strip()
    if head != PINNED_SHA:
        return None, [f"{PINNED_REF} resolved to {head!r}, not the pinned {PINNED_SHA!r}. "
                      "A tag is mutable; the commit is the pin"]
    # Build it under *our* toolchain, not the one its own repository names, so the
    # tool and the oleans it reads agree about the olean format.
    shutil.copy(LEAN / "lean-toolchain", clone / "lean-toolchain")
    build = subprocess.run(["lake", "build"], cwd=clone, capture_output=True, text=True)
    if build.returncode != 0:
        return None, [f"building axiom-audit at {PINNED_SHA} under "
                      f"{(LEAN / 'lean-toolchain').read_text().strip()!r} failed:\n"
                      f"{(build.stdout + build.stderr)[-1500:]}"]
    binary = clone / ".lake" / "build" / "bin" / "axiom-audit"
    if not binary.is_file():
        return None, [f"axiom-audit built but produced no binary at {binary}"]
    return binary, []


def self_test() -> int:
    """Null inputs first: an audit that audited nothing must not pass.

    The cases run on captured `--json` reports rather than invoking the tool, so
    this self-test runs in a job with no toolchain and no network. What is
    exercised is the verdict, not the audit.
    """
    clean = json.dumps({"root": "Workspace", "allowed": list(ALLOWED), "audited": 412,
                        "ok": True, "axiomsUsed": ["Classical.choice", "propext"],
                        "violations": []})
    dirty = json.dumps({"root": "Workspace", "allowed": list(ALLOWED), "audited": 412,
                        "ok": False, "axiomsUsed": ["sorryAx"],
                        "violations": [{"decl": "Workspace.X.y", "axioms": ["sorryAx"]}]})
    empty = json.dumps({"root": "Workspace", "allowed": list(ALLOWED), "audited": 0,
                        "ok": False, "axiomsUsed": [], "violations": []})
    failed = json.dumps({"ok": False, "audited": 0, "error": "could not load the environment"})

    sys.path.insert(0, str(ROOT / "tests"))
    import audit_axioms

    cases = [
        # Null inputs: four ways to check nothing and report success.
        ("no output at all is a failure", bool(verdict(0, "")[0]), True),
        ("unparseable output is a failure", bool(verdict(0, "not json")[0]), True),
        ("zero declarations audited is a failure", bool(verdict(0, empty)[0]), True),
        ("a tool error is a failure", bool(verdict(2, failed)[0]), True),
        # The pass.
        ("a clean report over a non-empty library passes", verdict(0, clean)[0], []),
        # Failure recognition.
        ("a violation is reported", len(verdict(1, dirty)[0]), 1),
        ("the violated declaration is named",
         "Workspace.X.y" in verdict(1, dirty)[0][0], True),
        ("a non-zero exit with no violation is still a failure",
         bool(verdict(1, clean)[0]), True),
        ("an audit of a different root is a failure",
         bool(verdict(0, clean.replace('"Workspace"', '"Scratch"'))[0]), True),
        ("a widened allowlist is a failure",
         bool(verdict(0, json.dumps({"root": "Workspace",
                                     "allowed": list(ALLOWED) + ["sorryAx"],
                                     "audited": 1, "ok": True, "axiomsUsed": [],
                                     "violations": []}))[0]), True),
        # The pin, and the agreement between the two axiom gates.
        ("the pinned commit is a full 40-character SHA", len(PINNED_SHA), 40),
        ("the pinned commit is hexadecimal",
         all(c in "0123456789abcdef" for c in PINNED_SHA), True),
        ("this gate and the trust-surface audit allow the same three axioms",
         set(ALLOWED), audit_axioms.ALLOWED),
        ("the allowance is exactly three", len(ALLOWED), 3),
        # The live tree, so the gate cannot pass by having stopped matching.
        ("the audited directory exists", (LEAN / AUDIT_DIR).is_dir(), True),
        ("the audited directory holds modules",
         len(list(LIB.rglob("*.lean"))) > 0, True),
    ]
    failures = 0
    print("BLANKET AXIOM AUDIT SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()

    with tempfile.TemporaryDirectory() as tmp:
        binary, problems = fetch_tool(pathlib.Path(tmp))
        if problems:
            print("BLANKET AXIOM AUDIT FAILED — the tool:", file=sys.stderr)
            for p in problems:
                print(f"  - {p}", file=sys.stderr)
            return 1

        proc = subprocess.run(
            ["lake", "env", str(binary), "--root", AUDIT_ROOT,
             "--modules-from", AUDIT_DIR, "--json"],
            cwd=LEAN, capture_output=True, text=True)
        problems, report = verdict(proc.returncode, proc.stdout)

    if report.get("audited"):
        print(f"BLANKET AXIOM AUDIT: {report['audited']} declaration(s) under "
              f"'{report.get('root')}', axioms used: "
              f"{report.get('axiomsUsed') or ['none']}")
    if problems:
        print("BLANKET AXIOM AUDIT FAILED:", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        if proc.stderr.strip():
            print("\n  axiom-audit stderr:\n" + "\n".join(
                f"    {line}" for line in proc.stderr.splitlines()[-40:]), file=sys.stderr)
        return 1

    print(f"BLANKET AXIOM AUDIT: {report['audited']} declaration(s) audited across the "
          f"whole library, all within {list(ALLOWED)} — "
          f"axiom-audit {PINNED_REF} ({PINNED_SHA})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
