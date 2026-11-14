"""This pass's runner: the bank under the setting and the checks behind RESULTS.md and
NEGATIVE_RESULTS.md.  Fails on a row that diverges from CASE_BANK.md without a line in
DIVERGENCES.md, a listed divergence that does not occur, a status the checks do not support, a
count in RESULTS.md the bank does not give, a banked case with no scene or a scene with no
banked case, or a bank that parses to nothing."""
from __future__ import annotations

import pathlib
import re
from fractions import Fraction

from . import bank, cases, checks
from .model import STANCES

HERE = pathlib.Path(__file__).resolve().parent
LISTED = re.compile(r"^DIVERGENCE ([A-Z]+\d+[abc]?) \((start|end|both)\):", re.M)
STATUS = re.compile(r"^\| (\d\.\d+) \| \*\*([a-z ]+)\*\* \|", re.M)
COUNT = re.compile(r"^COUNT (start|end): right (\d+), missed (\d+), convicted (\d+), routed (\d+), unfixed (\d+), not counted (\d+)$", re.M)
STATUSES = ("proved", "holds on the stated example", "refuted", "open")
STANDINGS = ("right", "missed", "convicted", "routed", "unfixed", "not counted")


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
        return 2, {"failures": ["estimates/CASE_BANK.md parsed to no cases"]}
    for cid in sorted(set(pre) - set(cases.CASES)):
        failures.append("banked case %s has no scene" % cid)
    for cid in sorted(set(cases.CASES) - set(pre)):
        failures.append("scene %s has no banked case" % cid)
    rows, diverging = [], set()
    tally = {st: {k: [] for k in STANDINGS} for st in STANCES}
    for cid, (title, evident, pred) in pre.items():
        if cid not in cases.CASES:
            continue
        scene = cases.CASES[cid]()
        for st in STANCES:
            tokens, facts = scene.tokens(st)
            missed = [i for i in pred[st] if not bank.matches(i, tokens)]
            standing = bank.standing(evident, tokens)
            tally[st][standing].append(cid)
            if missed:
                diverging.add((cid, st))
            rows.append({"case": cid, "stance": st, "title": title, "evident": evident, "prediction": "; ".join(pred[st]),
                         "computed": sorted(tokens), "missed": missed, "standing": standing, "facts": plain(facts)})
    listed = set()
    for cid, st in LISTED.findall((HERE / "DIVERGENCES.md").read_text(encoding="utf-8")):
        listed |= {(cid, s) for s in (STANCES if st == "both" else (st,))}
    for cid, st in sorted(diverging - listed):
        failures.append("%s (%s) diverges from its prediction and is not listed in DIVERGENCES.md" % (cid, st))
    for cid, st in sorted(listed - diverging):
        failures.append("DIVERGENCES.md lists %s (%s), which does not diverge" % (cid, st))
    results = (HERE / "RESULTS.md").read_text(encoding="utf-8")
    stated = dict(STATUS.findall(results))
    stated.update(dict(STATUS.findall((HERE / "NEGATIVE_RESULTS.md").read_text(encoding="utf-8"))))
    out = {}
    for k, check in checks.CHECKS.items():
        result = plain(check())
        out[k] = result
        if k not in stated:
            failures.append("no status is given for statement %s" % k)
        elif stated[k] not in STATUSES:
            failures.append("statement %s: %r is not a status" % (k, stated[k]))
        elif stated[k] != result["supports"]:
            failures.append("statement %s: the document says %r, the checks support %r" % (k, stated[k], result["supports"]))
    for k in sorted(set(stated) - set(checks.CHECKS)):
        if stated[k] != "open":
            failures.append("statement %s has the status %r and no check stands behind it" % (k, stated[k]))
    counts = {m[0]: tuple(int(x) for x in m[1:]) for m in COUNT.findall(results)}
    for st in STANCES:
        have = tuple(len(tally[st][k]) for k in STANDINGS)
        if counts.get(st) != have:
            failures.append("RESULTS.md's COUNT line for %s is %s; the bank gives %s" % (st, counts.get(st), have))
    return (1 if failures else 0), {"verdicts": rows, "tally": tally, "diverging": sorted(diverging), "checks": out,
                                    "statuses": stated, "failures": failures}


def render(report):
    out = ["case  stance  evident  standing  computed  (prediction)"]
    for r in report.get("verdicts", []):
        out.append("%-5s %-5s %-3s %-11s %-40s (%s)%s" % (r["case"], r["stance"], r["evident"], r["standing"],
                                                           "; ".join(r["computed"]), r["prediction"],
                                                           "" if not r["missed"] else "  DIVERGES on %s" % r["missed"]))
    out.append("")
    for st, t in report.get("tally", {}).items():
        out.append("%s: %s" % (st, ", ".join("%s %d" % (k, len(v)) for k, v in t.items())))
        for k in ("missed", "convicted", "routed", "unfixed"):
            out.append("  %s: %s" % (k, " ".join(t[k])))
    out.append("")
    for k, result in report.get("checks", {}).items():
        out.append("statement %s: %s" % (k, result["supports"]))
    out.append("")
    out.append("OK" if not report["failures"] else "FAILURES:\n  " + "\n  ".join(report["failures"]))
    return "\n".join(out)
