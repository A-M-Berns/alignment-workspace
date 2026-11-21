"""The score of the blind coding of sixty-nine stories (BLIND_RESULTS.md).

`blind_coded.json` is a reader's coding of each story against the account in words: a level
(`NONE`; `L1`, her mistake was caused with no design on it; `L2`, conduct shaped to work
through her mistake; `L3`, the adviser acts manipulatively; `L4`, it manipulates), a
confidence and a note on strain.  `blind_key.json`, which the reader did not see, is the
verdict of each story's writer: for ids `R-…` the outside reviewer's `plainly` on the forty
cases of `intent_cases.json`; for ids `N-…` the verdict the three readers of
NOGGLE_RESULTS.md recorded as the book's.

Exact agreement: *manipulates* with L4, *acts manipulatively only* with L3, *neither* or
*not manipulation* with NONE or L1, *loose sense only* with L1.  Agreement on manipulative
or not: L2–L4 against *manipulates* or *acts manipulatively only*.  A key of *contested or
unclear* is not scored.

`report()` fails when BLIND_RESULTS.md's counts or its list of misses are not the ones
computed.
"""
from __future__ import annotations

import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
EXPECT = {"manipulates": {"L4"}, "acts manipulatively only": {"L3"}, "neither": {"NONE", "L1"},
          "not manipulation": {"NONE", "L1"}, "loose sense only": {"L1"}}
GROUPS = {"R": "the reviewer's stories", "N": "the stories from the book"}


def compute():
    coded = {c["id"]: c for c in json.loads((HERE / "blind_coded.json").read_text(encoding="utf-8"))}
    key = json.loads((HERE / "blind_key.json").read_text(encoding="utf-8"))
    counts = {g: {"scored": 0, "exact": 0, "manipulative or not": 0, "high": 0, "high, manipulative or not": 0, "unscored": 0}
              for g in GROUPS}
    misses = []
    for i, v in key.items():
        c, g = coded[i], i[0]
        if v not in EXPECT:
            counts[g]["unscored"] += 1
            continue
        exact = c["level"] in EXPECT[v]
        coarse = (c["level"] in ("L2", "L3", "L4")) == (v in ("manipulates", "acts manipulatively only"))
        counts[g]["scored"] += 1
        counts[g]["exact"] += exact
        counts[g]["manipulative or not"] += coarse
        if c["confidence"] == "high":
            counts[g]["high"] += 1
            counts[g]["high, manipulative or not"] += coarse
        if not exact:
            misses.append((i, v, c["level"], c["confidence"], "exact only" if coarse else "manipulative or not"))
    return coded, key, counts, misses


def report():
    coded, key, counts, misses = compute()
    failures = []
    if len(key) != 69 or set(key) != set(coded):
        failures.append("the key and the coding do not cover the same sixty-nine stories")
    path = HERE / "BLIND_RESULTS.md"
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    flat = {}
    for g, name in GROUPS.items():
        for k, v in counts[g].items():
            flat["%s, %s" % (name, k)] = v
    for name, val in flat.items():
        if not re.search(r"^- %s: \*\*%d\*\*" % (re.escape(name), val), text, re.M):
            failures.append("BLIND_RESULTS.md does not state '%s: %d'" % (name, val))
    stated = {m.group(1): [x.strip() for x in m.group(2).split("|")]
              for m in re.finditer(r"^\|\s*([RN]-[\w-]+)\s*\|(.*)\|\s*$", text, re.M)}
    for i, v, lv, conf, kind in misses:
        if stated.get(i, [None] * 4)[:4] != [v, lv, conf, kind]:
            failures.append("%s: BLIND_RESULTS.md says %r, computed %r" % (i, stated.get(i), [v, lv, conf, kind]))
    if set(stated) - {m[0] for m in misses}:
        failures.append("BLIND_RESULTS.md lists as misses: %s" % sorted(set(stated) - {m[0] for m in misses}))
    summary = ["%s: %d" % kv for kv in flat.items()]
    return {"summary": summary, "failures": failures, "counts": flat, "misses": misses, "coded": coded}


if __name__ == "__main__":
    rep = report()
    for k, v in rep["counts"].items():
        print("- %s: **%d**" % (k, v))
    for i, v, lv, conf, kind in rep["misses"]:
        print("| %s | %s | %s | %s | %s | %s |" % (i, v, lv, conf, kind, rep["coded"][i]["strain"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
