"""The follow-up's runner.  Nonzero on: a computed verdict that differs from its
prediction and is not listed in DIVERGENCES.md; a listed divergence that does
not occur; a status in THEOREMS.md the checks contradict; a bank that parses to
nothing or a banked case with no module."""
from __future__ import annotations

import json
import pathlib
import re

from . import theorems
from .cases import all_cases, new_cases
from .model import evaluate

HERE = pathlib.Path(__file__).resolve().parent
ROW = re.compile(r"^\|\s*([NBT]\d+)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|$")
COLUMNS = ("arm's-length", "faithful-adviser", "first-pass")
FIRST_PASS = {"passes": "legitimate", "fails": "illegitimate"}


def load_bank():
    text = (HERE / "CASE_BANK.md").read_text(encoding="utf-8")
    table = text.split("## The table the runner reads")[-1]
    return {m.group(1): m.groups()[1:] for m in map(ROW.match, map(str.strip, table.splitlines())) if m}


def matches(predicted, computed, column):
    if column == "first-pass":
        if predicted in ("no prediction", "-"):
            return True
        return FIRST_PASS.get(predicted, predicted) == computed
    if predicted == "acquits":
        return computed != "steered"
    return predicted == computed


def listed(name):
    text = (HERE / name).read_text(encoding="utf-8")
    return set(re.findall(r"^DIVERGENCE\s+(\S+)\s+(arm's-length|faithful-adviser|first-pass)\b", text, re.M))


def recorded_statuses():
    text = (HERE / "THEOREMS.md").read_text(encoding="utf-8")
    return dict(re.findall(r"^## (C\d) .*?\n\n\*\*Status: (holds|refuted|open)", text, re.M))


def main(argv=()):
    failures = []
    bank = load_bank()
    if not bank:
        return 2, {"failures": ["steering/CASE_BANK.md parsed to no cases"]}
    cases = all_cases()
    verdicts, divergences = {}, set()
    for case in cases:
        v = evaluate(case)
        computed = (v["al"], v["fa"], v["first_pass"])
        pred = bank.get(case.id)
        rec = {"title": case.title, "arm's-length": v["al"], "faithful-adviser": v["fa"],
               "first-pass": v["first_pass"], "first-pass failing": v["first_pass_failing"],
               "varies": [x["varies"] for _, x in v["scenes"]],
               "nonworking": [sorted({"%s (%s): %s" % (p, n, "; ".join(why)) for _, n, p, why in x["nonworking"]})
                              for _, x in v["scenes"]]}
        if pred is None:
            failures.append("%s has no prediction" % case.id)
        else:
            rec["predicted"] = dict(zip(COLUMNS, pred))
            for col, p, c in zip(COLUMNS, pred, computed):
                if not matches(p, c, col):
                    divergences.add((case.id, col))
        verdicts[case.id] = rec
    missing = sorted(set(bank) - set(verdicts))
    if missing:
        failures.append("banked cases with no module: %s" % missing)
    declared = listed("DIVERGENCES.md")
    for d in sorted(divergences - declared):
        failures.append("unlisted divergence: %s under %s" % d)
    for d in sorted(declared - divergences):
        failures.append("DIVERGENCES.md lists %s under %s, which does not diverge" % d)
    th = theorems.run_all(cases, new_cases())
    recorded = recorded_statuses()
    for c in ("C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8"):
        if recorded.get(c) != th[c]["status"]:
            failures.append("%s: THEOREMS.md records %s, the checks give %s" % (c, recorded.get(c), th[c]["status"]))
    report = {"verdicts": verdicts, "divergences": sorted(divergences), "theorems": th, "failures": failures}
    return (0 if not failures else 1), report


def render(report):
    out = ["", "steering follow-up", "case  arm's-length | faithful-adviser | L0-L3^W   (predicted)"]
    for cid, r in report["verdicts"].items():
        p = r.get("predicted", {})
        out.append("%-4s %-20s| %-20s| %-24s (%s | %s | %s)" % (
            cid, r["arm's-length"], r["faithful-adviser"], r["first-pass"],
            p.get("arm's-length"), p.get("faithful-adviser"), p.get("first-pass")))
    out.append("\ndivergences: %s" % (report["divergences"] or "none"))
    out.append("\ncandidate statements:")
    for c in ("C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8"):
        out.append("  %s: %s" % (c, report["theorems"][c]["status"]))
    out.append("\n%s" % ("OK" if not report["failures"] else "FAILURES:\n  " + "\n  ".join(report["failures"])))
    return "\n".join(out)


def dumps(report):
    def key(o):
        if isinstance(o, dict):
            return {str(k): key(v) for k, v in o.items()}
        if isinstance(o, (list, tuple, set, frozenset)):
            return [key(x) for x in (sorted(o, key=repr) if isinstance(o, (set, frozenset)) else o)]
        return o if isinstance(o, (str, int, bool, type(None))) else str(o)
    return json.dumps(key(report), indent=1, ensure_ascii=False)
