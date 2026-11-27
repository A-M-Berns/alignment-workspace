"""The scores of the two blind runs on the literature's cases (VC_RESULTS.md).

`vc_coded.json` is one reader's coding of the fifty-two cases of LIT_CASES.md Part A against
VC_FORMULATION.md; `vc_coded_B.json` is another reader's against VC_FORMULATION_B.md.
Neither reader saw a source's verdict.  The sets scored are those LIT_CASES.md fixed before
anything was classified, read here from its text: the five cases whose source calls the act
acceptable and the fourteen whose source faults it.

A coding *agrees* with a source that calls the act acceptable when its verdict is
*legitimate*, and with one that faults it when its verdict is *illegitimate* (first run) or
*violation* or *exploitation* (second run).  It *contradicts* when it gives the opposite of
those.  *depends* and *silent* are neither.

`report()` fails when LIT_CASES.md does not yield the two sets, or when VC_RESULTS.md's
rows or counts are not the ones computed.
"""
from __future__ import annotations

import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
CLASS = {"legitimate": "acceptable", "illegitimate": "faulted", "violation": "faulted", "exploitation": "faulted"}


def sets():
    text = (HERE / "LIT_CASES.md").read_text(encoding="utf-8")
    ok = re.search(r"\*The source calls the act acceptable\* \(5\): ([^.]*)\.", text)
    bad = re.search(r"\*The source faults the act or marks it undesirable\* \(14\):([^.]*)\.", text)
    split = lambda m: [x.strip() for x in m.group(1).replace("\n", " ").split(",")] if m else []
    return split(ok), split(bad)


def outcome(verdict, source):
    c = CLASS.get(verdict)
    if c is None:
        return verdict
    return "agrees" if c == source else "contradicts"


def compute():
    A = {c["id"]: c for c in json.loads((HERE / "vc_coded.json").read_text(encoding="utf-8"))}
    B = {c["id"]: c for c in json.loads((HERE / "vc_coded_B.json").read_text(encoding="utf-8"))}
    ok, bad = sets()
    rows = [(i, src, A[i]["verdict"], outcome(A[i]["verdict"], src), B[i]["verdict"], outcome(B[i]["verdict"], src))
            for src, ids in (("acceptable", ok), ("faulted", bad)) for i in ids]
    return A, B, ok, bad, rows


def report():
    A, B, ok, bad, rows = compute()
    failures = []
    if len(ok) != 5 or len(bad) != 14:
        failures.append("LIT_CASES.md yields %d acceptable and %d faulted cases, not 5 and 14" % (len(ok), len(bad)))
    if len(A) != 52 or set(A) != set(B):
        failures.append("the two codings do not cover the same fifty-two cases")
    path = HERE / "VC_RESULTS.md"
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = {m.group(1): [x.strip() for x in m.group(2).split("|")]
              for m in re.finditer(r"^\|\s*([PKCN]\d+n?)\s*\|(.*)\|\s*$", text, re.M)}
    counts = {}
    for i, src, va, oa, vb, ob in rows:
        if stated.get(i, [None] * 5)[:5] != [src, va, oa, vb, ob]:
            failures.append("%s: VC_RESULTS.md says %r, computed %r" % (i, stated.get(i), [src, va, oa, vb, ob]))
        for run, o in (("first run", oa), ("second run", ob)):
            k = "%s, source %s, %s" % (run, src, o)
            counts[k] = counts.get(k, 0) + 1
    for run in ("first run", "second run"):
        for src in ("acceptable", "faulted"):
            for o in ("agrees", "contradicts"):
                counts.setdefault("%s, source %s, %s" % (run, src, o), 0)
    counts["adviser acts, first run"] = sum(bool(c["adviser_acts"]) for c in A.values())
    counts["adviser acts, second run"] = sum(bool(c["adviser_acts"]) for c in B.values())
    for name, val in sorted(counts.items()):
        if not re.search(r"^- %s: \*\*%d\*\*" % (re.escape(name), val), text, re.M):
            failures.append("VC_RESULTS.md does not state '%s: %d'" % (name, val))
    summary = ["%s: %d" % kv for kv in sorted(counts.items()) if "agrees" in kv[0] or "contradicts" in kv[0]]
    return {"summary": summary, "failures": failures, "rows": rows, "counts": counts, "A": A, "B": B}


if __name__ == "__main__":
    rep = report()
    for r in rep["rows"]:
        print("| %s | %s | %s | %s | %s | %s |" % r)
    for k, v in sorted(rep["counts"].items()):
        print("- %s: **%d**" % (k, v))
    for i in ("P2", "C4"):
        print(i, rep["A"][i]["verdict"], rep["B"][i]["verdict"])
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
