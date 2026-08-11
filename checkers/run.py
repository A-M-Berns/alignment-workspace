"""Run the house checkers over a claims registry.

Usage:
    python3 -m checkers.run [CLAIMS.md ...]
    python3 -m checkers.run --self-test
"""
from __future__ import annotations

import pathlib
import sys

from checkers import enumeration, registry, witness

ROOT = pathlib.Path(__file__).resolve().parents[1]


def run_registry(path: pathlib.Path) -> bool:
    ok, problems = registry.check(path, ROOT)
    print(f"  registry schema: {'ok' if ok else 'FAILED'}")
    for p in problems:
        print(f"    - {p}")
    if not ok:
        return False
    entries = registry.parse(path)
    verdicts = 0
    for e in entries:
        record = e["statement_of_record"]
        if record["kind"] == "lean":
            print(f"  {e['id']}: lean-proved — adjudicated by the Lean gate, "
                  f"not here ({record['declaration']})")
            continue
        params = record["parameters"]
        if record["checker"] == "witness":
            passed, detail = witness.check(record["instance"], params)
        else:
            passed, detail = enumeration.check(params)
        verdicts += 1
        print(f"  {e['id']}: {'PASS' if passed else 'FAIL'} — {detail}")
        if not passed:
            return False
    print(f"  {len(entries)} entries, {verdicts} adjudicated here")
    return True


def self_test() -> bool:
    from fractions import Fraction as Q
    cases = [
        (witness.check({"point": ["1/2", "1/2"]},
                       {"property": "satisfies-linear-constraints",
                        "constraints": [{"coefficients": [1, 1], "rhs": 1,
                                         "equality": True}]})[0], True, "witness pass"),
        (witness.check({"point": ["1/3", "1/3"]},
                       {"property": "satisfies-linear-constraints",
                        "constraints": [{"coefficients": [1, 1], "rhs": 1,
                                         "equality": True}]})[0], False, "witness fail"),
        (witness.check({"point": [0.5]},
                       {"property": "satisfies-linear-constraints",
                        "constraints": []})[0], False, "float rejected"),
        (enumeration.check({"domain": "rational-simplex", "dimension": 3,
                            "denominator": 5, "property": "satisfies-linear-constraints",
                            "constraints": [{"coefficients": [1, 1, 1], "rhs": 1,
                                             "equality": True}]})[0], True,
         "simplex sums to one"),
        (enumeration.check({"domain": "rational-grid", "denominator": 2,
                            "axes": [{"low": 0, "high": 2}],
                            "property": "satisfies-linear-constraints",
                            "constraints": [{"coefficients": [1], "rhs": 1}]})[0], False,
         "grid counterexample found"),
        (enumeration.check({"domain": "rational-grid", "denominator": 1,
                            "axes": [{"low": 1, "high": 0}],
                            "property": "equals"})[0], False, "empty domain refused"),
    ]
    ok = True
    for got, want, name in cases:
        status = "ok" if got == want else "FAILED"
        if got != want:
            ok = False
        print(f"  {status}: {name}")
    return ok


if __name__ == "__main__":
    args = sys.argv[1:]
    if "--self-test" in args:
        print("CHECKER SELF-TEST:")
        sys.exit(0 if self_test() else 1)
    paths = [pathlib.Path(a) for a in args] or sorted(ROOT.glob("projects/*/CLAIMS.md"))
    if not paths:
        print("no claims registry found")
        sys.exit(0)
    good = True
    for path in paths:
        print(f"REGISTRY {path.relative_to(ROOT)}:")
        good &= run_registry(path)
    sys.exit(0 if good else 1)
