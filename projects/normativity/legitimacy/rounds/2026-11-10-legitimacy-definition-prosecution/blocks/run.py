"""This pass's runner: the bank under the setting and the checks behind RESULTS.md.  Fails on a
row that diverges from CASE_BANK.md without a line in DIVERGENCES.md, a listed divergence that
does not occur, a status in RESULTS.md the checks do not support, a banked case with no scene or
a scene with no banked case, or a bank that parses to nothing."""
from __future__ import annotations

import pathlib
import re
from fractions import Fraction

from . import bank, cases, results

HERE = pathlib.Path(__file__).resolve().parent
LISTED = re.compile(r"^DIVERGENCE (\d+[abc]?):", re.M)
STATUS = re.compile(r"^\| (\d\.\d) \| \*\*([a-z ]+)\*\* \|", re.M)
STATUSES = ("proved", "holds on the stated example", "refuted", "open")


def plain(x):
    if isinstance(x, Fraction):
        return str(x)
    if isinstance(x, dict):
        return {str(k): plain(v) for k, v in x.items()}
    if isinstance(x, (list, tuple, set)):
        return [plain(v) for v in (sorted(x, key=str) if isinstance(x, set) else x)]
    return x if isinstance(x, (bool, int, str, type(None))) else str(x)


def main():
    failures = []
    pre = bank.load()
    if not pre:
        return 2, {"failures": ["blocks/CASE_BANK.md parsed to no cases"]}
    for cid in sorted(set(pre) - set(cases.CASES)):
        failures.append("banked case %s has no scene" % cid)
    for cid in sorted(set(cases.CASES) - set(pre)):
        failures.append("scene %s has no banked case" % cid)
    rows = []
    for cid, (title, items) in pre.items():
        if cid not in cases.CASES:
            continue
        tokens, facts = cases.CASES[cid]()
        missed = [i for i in items if not bank.matches(i, tokens)]
        rows.append({"case": cid, "title": title, "prediction": "; ".join(items), "computed": sorted(tokens),
                     "missed": missed, "match": not missed, "facts": plain(facts)})
    diverging = [r["case"] for r in rows if not r["match"]]
    listed = LISTED.findall((HERE / "DIVERGENCES.md").read_text(encoding="utf-8"))
    for cid in diverging:
        if cid not in listed:
            failures.append("%s diverges from its prediction and is not listed in DIVERGENCES.md" % cid)
    for cid in listed:
        if cid not in diverging:
            failures.append("DIVERGENCES.md lists %s, which does not diverge" % cid)
    stated = dict(STATUS.findall((HERE / "RESULTS.md").read_text(encoding="utf-8")))
    checks = {}
    for k, check in results.CHECKS.items():
        result = plain(check())
        checks[k] = result
        if k not in stated:
            failures.append("RESULTS.md gives no status for statement %s" % k)
        elif stated[k] not in STATUSES:
            failures.append("statement %s: %r is not a status" % (k, stated[k]))
        elif stated[k] != result["supports"]:
            failures.append("statement %s: RESULTS.md says %r, the checks support %r" % (k, stated[k], result["supports"]))
    for k in sorted(set(stated) - set(results.CHECKS)):
        if stated[k] != "open":
            failures.append("RESULTS.md gives statement %s the status %r and no check stands behind it" % (k, stated[k]))
    return (1 if failures else 0), {"verdicts": rows, "diverging": diverging, "checks": checks, "statuses": stated,
                                    "failures": failures}


def render(report):
    out = ["case  prediction -> computed  match"]
    for r in report.get("verdicts", []):
        out.append("%-4s %-52s -> %s  %s" % (r["case"], r["prediction"], "; ".join(r["computed"]),
                                              "ok" if r["match"] else "DIVERGES on %s" % r["missed"]))
    out.append("")
    for k, result in report.get("checks", {}).items():
        out.append("statement %s: %s" % (k, result["supports"]))
    out.append("")
    out.append("OK" if not report["failures"] else "FAILURES:\n  " + "\n  ".join(report["failures"]))
    return "\n".join(out)
