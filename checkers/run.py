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
        name = record["checker"]
        if name.startswith("contrib/"):
            import importlib
            module = importlib.import_module(f"checkers.contrib.{name[len('contrib/'):]}")
            passed, detail = module.check(record.get("instance", {}), params)
            detail = f"[contributor-checked] {detail}"
        elif name == "witness":
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
    # The contributor-checked ceiling is derived from the invocation path, so it
    # is tested here rather than trusted.
    import json, tempfile, shutil
    tmp = pathlib.Path(tempfile.mkdtemp())
    (tmp / "checkers" / "contrib").mkdir(parents=True)
    (tmp / "checkers" / "contrib" / "demo.py").write_text('"""d."""\ndef check(i, p):\n    return True, "ok"\n')
    (tmp / "lean" / "Workspace").mkdir(parents=True)
    (tmp / "PRIORITIES.md").write_text("### 1. item\n")
    def registered_as(klass, item="1"):
        body = {"class": klass,
                "statement_of_record": {"kind": "checker", "checker": "contrib/demo",
                                        "parameters": {"property": "x"}},
                "answers_item": item,
                "provenance": {"generator": "external", "review_status": "ci-only"}}
        f = tmp / "CLAIMS.md"
        f.write_text("### demo.claim\n\n```json\n" + json.dumps(body) + "\n```\n")
        return registry.check(f, tmp)[0]
    cases += [
        (registered_as("witness-checked"), False, "contrib checker cannot claim witness-checked"),
        (registered_as("enumeration-verified"), False, "contrib checker cannot claim enumeration-verified"),
        (registered_as("contributor-checked"), True, "contrib checker at its ceiling is accepted"),
    ]
    # That the registry reads PRIORITIES.md at all. An unfiled item must fail,
    # and so must a missing priorities file: the check used to default to an
    # empty item set and skip itself, which looks exactly like a pass.
    cases.append((registered_as("contributor-checked", item="99"), False,
                  "claim answering an unfiled priorities item is rejected"))
    (tmp / "PRIORITIES.md").unlink()
    cases.append((registered_as("contributor-checked"), False,
                  "missing PRIORITIES.md fails rather than skipping the check"))
    shutil.rmtree(tmp)

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
