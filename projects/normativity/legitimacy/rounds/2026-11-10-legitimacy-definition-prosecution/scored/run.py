"""This pass's runner: the bank under the account and the checks behind THEOREMS.md.  Fails on a
row that diverges from CASE_BANK.md without a line in DIVERGENCES.md, a listed divergence that
does not occur, a status in THEOREMS.md the checks do not support, a banked case with no module
or a module with no banked case, or a bank that parses to nothing."""
from __future__ import annotations

import pathlib
import re

from decomposition.run import dumps  # noqa: F401  (re-exported for the round runner)

from . import bank, theorems

HERE = pathlib.Path(__file__).resolve().parent
LISTED = re.compile(r"^DIVERGENCE ([DPBTNXYZ]\d+[abc]?):", re.M)
STATUS = re.compile(r"^\| ([1-9]) \|[^|]*\| \*\*([a-z ]+)\*\* \|", re.M)
STATUSES = ("holds on the stated domain", "proved", "refuted", "open")


def main():
    failures = []
    pre = bank.load()
    if not pre:
        return 2, {"failures": ["scored/CASE_BANK.md parsed to no cases"]}
    results = theorems.bank_results()
    covered = {rid if rid in pre else rid[:-1] for rid in results}
    missing = sorted(set(pre) - covered)
    if missing:
        failures.append("banked cases with no module: %s" % missing)
    from .cases import all_rows
    unbanked = sorted(r.id for r in all_rows() if r.id not in results)
    if unbanked:
        failures.append("modules with no banked case: %s" % unbanked)
    rows = [{"row": rid, "title": r["row"].title, "aim": r["row"].aim, "prediction": r["prediction"],
             "computed": r["shown"], "match": r["match"]} for rid, r in results.items()]
    diverging = [r["row"] for r in rows if not r["match"]]
    listed = LISTED.findall((HERE / "DIVERGENCES.md").read_text(encoding="utf-8"))
    for rid in diverging:
        if rid not in listed:
            failures.append("%s diverges from its prediction and is not listed in DIVERGENCES.md" % rid)
    for rid in listed:
        if rid not in diverging:
            failures.append("DIVERGENCES.md lists %s, which does not diverge" % rid)
    stated = dict(STATUS.findall((HERE / "THEOREMS.md").read_text(encoding="utf-8")))
    checks = {}
    for k, check in theorems.CHECKS.items():
        result = check()
        checks[k] = result
        if k not in stated:
            failures.append("THEOREMS.md gives no status for statement %s" % k)
        elif stated[k] not in STATUSES:
            failures.append("statement %s: %r is not a status" % (k, stated[k]))
        elif stated[k] != result["supports"]:
            failures.append("statement %s: THEOREMS.md says %r, the checks support %r" % (k, stated[k], result["supports"]))
    return (1 if failures else 0), {"verdicts": rows, "diverging": diverging, "checks": checks, "statuses": stated,
                                    "failures": failures}


def render(report):
    out = ["row   aim       prediction -> computed  match"]
    for r in report.get("verdicts", []):
        out.append("%-5s %-8s %-44s -> %s  %s" % (r["row"], r["aim"], r["prediction"], r["computed"],
                                                   "ok" if r["match"] else "DIVERGES"))
    out.append("")
    weights = report.get("checks", {}).get("4", {}).get("weight of illegitimacy, Chain rows", {})
    if weights:
        out.append("weight of illegitimacy, Chain rows (corrector, non-corrector, divided; then the same under view-best)")
        for rid, cell in weights.items():
            out.append("%-5s %s" % (rid, "  ".join(cell.values())))
        out.append("")
    for k, result in report.get("checks", {}).items():
        out.append("statement %s: %s" % (k, result["supports"]))
    out.append("")
    out.append("OK" if not report["failures"] else "FAILURES:\n  " + "\n  ".join(report["failures"]))
    return "\n".join(out)
