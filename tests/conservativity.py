"""Spec conservativity: a proof-layer change may not alter the specification's shape.

Three checks, all textual and fast, over the Lean specification namespaces.

1. **No new axioms.** No `axiom` declaration anywhere in the library. External
   theory enters as a named hypothesis; an `axiom` standing in for a citation is
   the failure this exists to catch.
2. **Instance and notation counts in spec namespaces are unchanged.** A
   contributor adding an instance or a notation in a core namespace can change
   how existing code elaborates without touching a spec file. The counts are
   recorded here and compared.
3. **Every spec file still carries its axiom print.**

Check 2 compares against `tests/spec_shape.json`, which is itself a
specification-layer file: updating it is a maintainer act.
"""
from __future__ import annotations

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LIB = ROOT / "lean" / "Workspace"
SHAPE = ROOT / "tests" / "spec_shape.json"

SPEC_GLOBS = ("Smoke.lean", "*/Basic.lean", "*/Spec/**/*.lean")


def spec_files() -> list[pathlib.Path]:
    out: list[pathlib.Path] = []
    for glob in SPEC_GLOBS:
        out.extend(sorted(LIB.glob(glob)))
    return sorted(set(out))


def measure() -> dict[str, dict[str, int]]:
    shape: dict[str, dict[str, int]] = {}
    for path in spec_files():
        text = path.read_text()
        shape[path.relative_to(LIB).as_posix()] = {
            "instances": len(re.findall(r"^\s*(?:noncomputable\s+)?instance\b", text, re.M)),
            "notations": len(re.findall(r"^\s*(?:scoped\s+)?(?:notation|infix|prefix|postfix)\b", text, re.M)),
        }
    return shape


def self_test() -> int:
    """Null-input cases: the gate must not pass by measuring nothing.

    Two null inputs. An empty specification-file set makes `measure()` return
    `{}` — every recorded file then reads as removed, which fails, and that is
    pinned here. A missing `spec_shape.json` used to be *written* and the run
    passed, so deleting the baseline silently re-baselined the shape it exists
    to freeze; that is now a failure.
    """
    cases = [
        ("the library has specification files", len(spec_files()) > 0, True),
        ("the recorded shape exists", SHAPE.is_file(), True),
        ("an empty measurement reads every recorded file as removed",
         len(set(json.loads(SHAPE.read_text())) - set()) > 0, True),
        ("an axiom declaration is matched",
         bool(re.search(r"^\s*axiom\b", "axiom foo : True", re.M)), True),
        ("the word axiom inside an identifier is not matched",
         bool(re.search(r"^\s*axiom\b", "axiomatic_thing := 1", re.M)), False),
        ("an instance line is counted",
         len(re.findall(r"^\s*(?:noncomputable\s+)?instance\b",
                        "instance : Foo := ...", re.M)), 1),
        ("a notation line is counted",
         len(re.findall(r"^\s*(?:scoped\s+)?(?:notation|infix|prefix|postfix)\b",
                        "scoped notation \"x\" => y", re.M)), 1),
    ]
    failures = 0
    print("CONSERVATIVITY SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    if "--record" in sys.argv:
        shape = measure()
        SHAPE.write_text(json.dumps(shape, indent=2, sort_keys=True) + "\n")
        print(f"CONSERVATIVITY: recorded shape for {len(shape)} spec files")
        return 0
    problems: list[str] = []

    for path in sorted(LIB.rglob("*.lean")):
        text = path.read_text()
        for match in re.finditer(r"^\s*axiom\b", text, re.M):
            line = text.count("\n", 0, match.start()) + 1
            problems.append(f"{path.relative_to(ROOT)}:{line}: `axiom` declaration — "
                            "external theory enters as a named hypothesis, never an axiom")
        if "#print axioms" not in text:
            problems.append(f"{path.relative_to(ROOT)}: no `#print axioms` line")

    current = measure()
    if SHAPE.exists():
        recorded = json.loads(SHAPE.read_text())
        for name, counts in sorted(current.items()):
            was = recorded.get(name)
            if was is None:
                problems.append(f"{name}: new specification file; recording it is a "
                                "maintainer act (update tests/spec_shape.json)")
            elif was != counts:
                problems.append(f"{name}: specification shape changed {was} -> {counts}")
        for name in sorted(set(recorded) - set(current)):
            problems.append(f"{name}: specification file removed")
    else:
        # The null input. Writing the baseline here and passing would mean that
        # deleting tests/spec_shape.json re-baselines the shape this gate exists
        # to freeze — a green run that checked nothing. Recording it is a
        # maintainer act, done deliberately and reviewed.
        print("CONSERVATIVITY FAILED: tests/spec_shape.json is missing, so there "
              "is nothing to compare against.", file=sys.stderr)
        print("  Recording a baseline is a maintainer act. To record the current "
              "shape deliberately:\n"
              f"    python3 tests/conservativity.py --record", file=sys.stderr)
        return 1

    if problems:
        print("CONSERVATIVITY FAILED:", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        return 1
    print(f"CONSERVATIVITY: {len(current)} spec files, no axioms, shape unchanged")
    return 0


if __name__ == "__main__":
    sys.exit(main())
