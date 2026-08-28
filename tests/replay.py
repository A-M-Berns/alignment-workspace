#!/usr/bin/env python3
"""Gate 2c: the library's `.olean`s are replayed through the kernel.

`lake build` and `tests/audit_axioms.py` are one process trusted twice. The
build elaborates the library; the audit then asks that same environment which
axioms a declaration depends on. A declaration that entered the environment
*without the kernel checking it* is clean to both — `addDeclCore (doCheck :=
false)`, a tactic reaching past the checked environment, or a bug in Lean's own
import or parallel-elaboration handling. It elaborates, it ships an `.olean`, and
`#print axioms` reports nothing wrong, because reading an environment is not
re-deriving it.

Replay re-derives it. `leanchecker` reads each compiled module and pushes every
declaration back through the kernel, and a declaration the kernel will not accept
fails here and nowhere else. The demonstration is in this round's report: a
theorem of `False`, added with `doCheck := false`, builds green, audits green
under `tests/audit_axioms.py`, audits green under `tests/blanket_axioms.py`, and
is caught here.

What replay does *not* establish (`lean-lang.org/doc/reference/latest/
ValidatingProofs/`): it trusts that the `.olean` files are structurally
well-formed, so it is not a defence against a forged olean, and it says nothing
about whether the statements mean what their names suggest.

**No pin, and no second toolchain.** `leanchecker` ships inside the Lean
toolchain from v4.28.0 onward — the standalone `leanprover/lean4checker`
repository is deprecated — so the checker is the one `lean/lean-toolchain`
already names and a version skew between library and checker cannot arise from a
pin drifting out of date. `assert_toolchain` below still checks it, because
"cannot arise" is a claim about the current arrangement and this file is where
that claim would stop being true.

**Scope: this library only.** `leanchecker Workspace` replays modules under the
`Workspace` prefix and leaves Mathlib, Foundation and Formalized-Agent-Foundations
to their own repositories. `--fresh` is deliberately not passed: it re-replays
every imported constant into an empty environment, which is a Mathlib-sized job
for a workspace-sized library.

**The failure this gate is written against is its own vacuity.** A replay that
checked nothing exits zero and prints nothing, which is indistinguishable from a
clean run unless something insists on the count. So the modules replayed are
enumerated, and they are compared against the modules the committed sources say
must exist: a replay missing any of them fails. The comparison is one-directional
— replaying *more* than the sources name is fine, since a warm `.lake` cache can
still hold an olean for a module this change deleted.
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
LIB = LEAN / "Workspace"
TOOLCHAIN = LEAN / "lean-toolchain"

# The module prefix handed to `leanchecker`. The lakefile globs `Workspace.+`,
# which builds the submodules and not the root module, so this is a prefix over
# the built tree rather than a module that must itself exist.
ROOT_PREFIX = "Workspace"

REPLAYING = re.compile(r"^replaying (\S+)$", re.M)


def module_of(path: pathlib.Path) -> str:
    """`lean/Workspace/Deference/Basic.lean` -> `Workspace.Deference.Basic`."""
    return ".".join(path.relative_to(LEAN).with_suffix("").parts)


def expected_modules() -> list[str]:
    """What the committed sources say the build must have produced.

    Sources under `lean/Workspace/`, which is exactly what the lakefile's
    `Workspace.+` glob builds — the root `lean/Workspace.lean` is not among
    them and is deliberately not expected here."""
    return sorted(module_of(p) for p in LIB.rglob("*.lean"))


def replayed_modules(output: str) -> list[str]:
    return sorted(set(REPLAYING.findall(output)))


def verdict(returncode: int, output: str, expected: list[str]) -> list[str]:
    """Every problem with a replay run, in the order they are worth reading.

    Fails closed: a non-zero exit, an empty enumeration and a missing module are
    all failures, and so is an empty expectation — a library with no sources is a
    broken checkout, not a library with nothing to check."""
    problems: list[str] = []
    if not expected:
        problems.append("the committed sources name no modules to replay; "
                        "that is a broken checkout, not a clean library")
    got = replayed_modules(output)
    if returncode != 0:
        problems.append(f"leanchecker exited {returncode}")
    if not got:
        problems.append("leanchecker enumerated no modules — it replayed nothing, "
                        "which exits zero and looks exactly like a clean run")
    missing = [m for m in expected if m not in set(got)]
    if missing:
        problems.append(f"{len(missing)} committed module(s) were not replayed: {missing}")
    return problems


def assert_toolchain() -> list[str]:
    """The checker Lean hands us is the toolchain `lean/lean-toolchain` names.

    `elan which` resolves through the directory's pin, so agreement is the normal
    case and disagreement means the pin and the resolved binary have come apart —
    which must be loud, because a checker from the wrong toolchain does not
    quietly check less, it crashes or reads an incompatible olean header."""
    problems: list[str] = []
    if not TOOLCHAIN.is_file():
        return [f"{TOOLCHAIN.relative_to(ROOT)} is missing"]
    pinned = TOOLCHAIN.read_text().strip()
    version = pinned.rsplit(":", 1)[-1]

    which = subprocess.run(["elan", "which", "leanchecker"],
                           cwd=LEAN, capture_output=True, text=True)
    if which.returncode != 0:
        return [f"`elan which leanchecker` failed ({which.returncode}): "
                f"{which.stderr.strip()[:200]}. The toolchain pinned as {pinned!r} "
                "ships no `leanchecker`; it arrived in v4.28.0"]
    resolved = which.stdout.strip()
    if version not in resolved:
        problems.append(f"`elan which leanchecker` resolved to {resolved!r}, which does "
                        f"not name the pinned toolchain {pinned!r}")

    lean = subprocess.run(["lake", "env", "lean", "--version"],
                          cwd=LEAN, capture_output=True, text=True)
    if lean.returncode != 0:
        problems.append(f"`lake env lean --version` failed ({lean.returncode})")
    elif version.lstrip("v") not in lean.stdout:
        problems.append(f"`lake env lean --version` reports {lean.stdout.strip()!r}, "
                        f"which does not name the pinned toolchain {pinned!r}")
    return problems


def self_test() -> int:
    """Null inputs first: every way a replay can check nothing is a failure.

    The parsing cases run on captured `leanchecker -v` output rather than
    invoking it, so this self-test runs in a job with no toolchain. What is
    exercised is the recognition and the verdict, not the replay.
    """
    good = "replaying Workspace.Smoke\nreplaying Workspace.Deference.Basic\n"
    noisy = ("leanchecker found a problem in Workspace.Smoke\n"
             "replaying Workspace.Smoke\n"
             "uncaught exception: (kernel) declaration type mismatch\n")
    two = ["Workspace.Smoke", "Workspace.Deference.Basic"]
    cases = [
        # Null inputs. Each of these is a run that verified nothing, and each
        # would exit zero and print a plausible line if it were not failed here.
        ("silent success on no output is a failure", bool(verdict(0, "", two)), True),
        ("an empty expectation is a failure, not a skip",
         bool(verdict(0, good, [])), True),
        ("a zero exit with a missing module is a failure",
         bool(verdict(0, "replaying Workspace.Smoke\n", two)), True),
        # The pass, which is the only case that lets a build through.
        ("every expected module replayed, exit zero, passes",
         verdict(0, good, two), []),
        ("replaying more than the sources name is not a failure",
         verdict(0, good + "replaying Workspace.Deleted\n", two), []),
        # Failure recognition.
        ("a non-zero exit fails even with a full enumeration",
         bool(verdict(1, good, two)), True),
        ("a kernel rejection is recognised as a failure",
         bool(verdict(1, noisy, ["Workspace.Smoke"])), True),
        # Parsing.
        ("the enumeration is read off the verbose output",
         replayed_modules(good), sorted(two)),
        ("a repeated module is counted once",
         len(replayed_modules(good + good)), 2),
        ("a line that is not an enumeration line is not read as one",
         replayed_modules("uncaught exception: replaying is hard\n"), []),
        ("no output enumerates nothing", replayed_modules(""), []),
        # The live tree, so the gate cannot pass by having stopped matching.
        ("the library tree exists", LIB.is_dir(), True),
        ("the live library has modules to replay", len(expected_modules()) > 0, True),
        ("the toolchain pin is a real file", TOOLCHAIN.is_file(), True),
        ("module names are derived from paths, not guessed",
         module_of(LIB / "Deference" / "Basic.lean"), "Workspace.Deference.Basic"),
        ("the root module is not expected, because the glob does not build it",
         "Workspace" in expected_modules(), False),
    ]
    failures = 0
    print("REPLAY SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()

    problems = assert_toolchain()
    if problems:
        print("REPLAY FAILED — toolchain:", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        return 1

    expected = expected_modules()
    proc = subprocess.run(["lake", "env", "leanchecker", "-v", ROOT_PREFIX],
                          cwd=LEAN, capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    got = replayed_modules(output)

    print(f"REPLAY: {len(got)} module(s) replayed through the kernel:")
    for module in got:
        print(f"  {module}")

    problems = verdict(proc.returncode, output, expected)
    if problems:
        print("REPLAY FAILED:", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        print("\n  leanchecker output:\n" + "\n".join(
            f"    {line}" for line in output.splitlines()[-40:]), file=sys.stderr)
        return 1

    print(f"REPLAY: {len(got)} module(s) replayed, covering all "
          f"{len(expected)} committed source module(s); the kernel accepted every "
          "declaration.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
