"""This pass's runner: the bank under the account, the checks behind THEOREMS.md, and the
facts the two addenda cite.  Fails on a divergence from CASE_BANK.md not listed in
DIVERGENCES.md, a listed divergence that does not occur, a status in THEOREMS.md the checks
do not support, a banked case with no module or a module with no banked case, or a bank
that parses to nothing."""
from __future__ import annotations

import json
import pathlib
import re
from fractions import Fraction

from . import bank, extensions, theorems
from .cases import all_cases

HERE = pathlib.Path(__file__).resolve().parent
LISTED = re.compile(r"^DIVERGENCE ([DPBTNXY]\d+):", re.M)
STATUS = re.compile(r"^\| ([1-9]) \|[^|]*\| \*\*([a-z ]+)\*\* \|", re.M)
STATUSES = ("holds on the stated domain", "proved", "refuted", "open")


def main():
    failures = []
    pre = bank.load()
    if not pre:
        return 2, {"failures": ["decomposition/CASE_BANK.md parsed to no cases"]}
    cases = all_cases()
    rows, diverging = [], []
    for case in cases:
        if case.id not in pre:
            failures.append("%s has no prediction in the bank" % case.id)
            continue
        computed, ok, _ = bank.evaluate(case, pre[case.id])
        rows.append({"case": case.id, "title": case.title, "prediction": pre[case.id], "computed": computed, "match": ok})
        if not ok:
            diverging.append(case.id)
    missing = sorted(set(pre) - {c.id for c in cases})
    if missing:
        failures.append("banked cases with no module: %s" % missing)
    listed = LISTED.findall((HERE / "DIVERGENCES.md").read_text(encoding="utf-8"))
    for cid in diverging:
        if cid not in listed:
            failures.append("%s diverges from its prediction and is not listed in DIVERGENCES.md" % cid)
    for cid in listed:
        if cid not in diverging:
            failures.append("DIVERGENCES.md lists %s, which does not diverge" % cid)

    stated = dict(STATUS.findall((HERE / "THEOREMS.md").read_text(encoding="utf-8")))
    checks = {}
    for key, check in theorems.CHECKS.items():
        result = check()
        checks[key] = result
        if key not in stated:
            failures.append("THEOREMS.md gives no status for statement %s" % key)
        elif stated[key] not in STATUSES:
            failures.append("statement %s: %r is not a status" % (key, stated[key]))
        elif stated[key] != result["supports"]:
            failures.append("statement %s: THEOREMS.md says %r, the checks support %r" % (key, stated[key], result["supports"]))
    facts = {name: fn() for name, fn in extensions.FACTS.items()}
    return (1 if failures else 0), {"verdicts": rows, "diverging": diverging, "checks": checks, "statuses": stated,
                                    "addenda": facts, "failures": failures}


def dumps(report):
    def plain(x):
        if isinstance(x, Fraction):
            return str(x)
        if isinstance(x, dict):
            return {str(k): plain(v) for k, v in x.items()}
        if isinstance(x, (list, tuple, set, frozenset)):
            return [plain(v) for v in x]
        return x
    return json.dumps(plain(report), indent=1, default=str)


def render(report):
    out = ["case  prediction -> computed  match"]
    for r in report.get("verdicts", []):
        out.append("%-4s %-30s -> %s  %s" % (r["case"], r["prediction"], r["computed"], "ok" if r["match"] else "DIVERGES"))
    out.append("")
    for key, result in report.get("checks", {}).items():
        out.append("statement %s: %s" % (key, result["supports"]))
    out.append("")
    out.append("OK" if not report["failures"] else "FAILURES:\n  " + "\n  ".join(report["failures"]))
    return "\n".join(out)
