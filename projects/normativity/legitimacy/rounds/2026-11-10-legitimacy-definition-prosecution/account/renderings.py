"""The two renderings of TEST_CASES.md compared, by the rules that file fixes.

Reads RENDERING_EXECUTOR.md and RENDERING_REVIEWER.md (one table each), the evident verdicts of
CASES.md and those the eighth pass's reviewer stated for its own twelve cases, and computes the
agreement on each question and each verdict, the disagreements, the cases whose verdict goes
against a recorded one, the cases either renderer judges plain subversion that the statement
passes, and how condition 1 was evaluated.  `report()` compares RENDERINGS.md's table with it."""
from __future__ import annotations

import pathlib
import re
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
COLS = ("a", "b", "c", "d", "narrow", "wide", "wb", "sub", "reading")
ROW = re.compile(r"^\|\s*([CRA]\d+)\s*\|(.*)\|\s*$")

# what the eighth pass's reviewer stated of its own cases (REVIEW-astra-followup-8.md, points 3-14)
REVIEWER_EVIDENT = {"R1": "ill", "R2": "ill", "R3": "ill", "R4": "ill", "R5": "con", "R6": "con",
                    "R7": "leg", "R8": "leg", "R9": "leg", "R10": "ill", "R11": "leg", "R12": "leg"}


def case_ids():
    return [m.group(1) for line in (HERE / "TEST_CASES.md").read_text(encoding="utf-8").splitlines()
            if (m := ROW.match(line))]


def load(rel):
    rows = {}
    path = HERE / rel
    if not path.exists():
        return rows
    for line in path.read_text(encoding="utf-8").splitlines():
        m = ROW.match(line)
        if not m:
            continue
        cells = [c.strip().strip("`") for c in m.group(2).split("|")]
        if len(cells) != len(COLS):
            raise SystemExit("%s: row %s has %d cells, expected %d" % (rel, m.group(1), len(cells), len(COLS)))
        if m.group(1) in rows:
            raise SystemExit("%s: case %s occurs twice" % (rel, m.group(1)))
        rows[m.group(1)] = dict(zip(COLS, cells))
    return rows


def value(ans):
    """An answer's value, marks dropped."""
    return ans.split(".")[0].strip() or "?"


def mark(ans):
    return "not fixed" if value(ans) == "?" else {"c": "case", "r": "reading"}.get(ans.split(".")[-1], "unmarked")


def verdict_class(v):
    v = v.strip()
    if v in ("NA", "none", "?"):
        return v
    digits = "".join(sorted(set(ch for ch in v if ch in "123")))
    if not digits:
        return "?"
    return "manipulation" if ("2" in digits or "3" in digits) else "settling"


def norm_verdict(v):
    v = v.strip()
    return v if v in ("NA", "none", "?") else "".join(sorted(set(ch for ch in v if ch in "123"))) or "?"


def evident():
    out = {}
    for line in (HERE / "CASES.md").read_text(encoding="utf-8").splitlines():
        m = ROW.match(line)
        if m:
            last = m.group(2).split("|")[-1]
            ev = re.search(r"\b(leg|ill|con)\b", last)
            src = re.search(r"\*([se])\*", last)
            if ev:
                out[m.group(1)] = (ev.group(1), "source" if src and src.group(1) == "s" else "executor of the eighth pass")
    for k, v in REVIEWER_EVIDENT.items():
        out[k] = (v, "source")
    return out


def against(row, reading, ev):
    """Does this row's verdict under `reading` go against the evident verdict `ev`?"""
    cls = verdict_class(row[reading])
    belief_fault = value(row["c"]) == "N" or value(row["d"]) == "N"
    if ev == "leg":
        return cls in ("manipulation", "settling") or (cls == "NA" and belief_fault)
    if ev == "ill":
        return cls == "none" or (cls == "NA" and value(row["c"]) == "Y" and value(row["d"]) == "Y")
    return False


def passes(row, reading):
    cls = verdict_class(row[reading])
    return cls == "none" or (cls == "NA" and value(row["c"]) == "Y" and value(row["d"]) == "Y")


def compare():
    ids = case_ids()
    ex, rv = load("RENDERING_EXECUTOR.md"), load("RENDERING_REVIEWER.md")
    failures = []
    for name, r in (("executor", ex), ("reviewer", rv)):
        missing = [i for i in ids if i not in r]
        if not r:
            failures.append("the %s's rendering parsed to nothing" % name)
        elif missing:
            failures.append("the %s's rendering lacks %s" % (name, missing))
    if failures:
        return {"failures": failures}
    n = len(ids)
    out = {"n": n, "failures": failures, "agree": {}, "disagree": {}, "exact": {}}
    for q in ("a", "b", "c", "d"):
        dis = [i for i in ids if value(ex[i][q]) != value(rv[i][q])]
        out["agree"][q] = n - len(dis)
        out["disagree"][q] = dis
    for reading in ("narrow", "wide"):
        dis = [i for i in ids if verdict_class(ex[i][reading]) != verdict_class(rv[i][reading])]
        out["agree"][reading] = n - len(dis)
        out["disagree"][reading] = dis
        out["exact"][reading] = sum(norm_verdict(ex[i][reading]) == norm_verdict(rv[i][reading]) for i in ids)
    out["sub agree"] = sum(value(ex[i]["sub"]) == value(rv[i]["sub"]) for i in ids)
    ev = evident()
    out["counted"] = {src: sorted(i for i in ids if i in ev and ev[i][0] in ("leg", "ill") and ev[i][1] == src)
                      for src in ("source", "executor of the eighth pass")}
    out["against"] = {}
    for reading in ("narrow", "wide"):
        for src, pool in out["counted"].items():
            a_ex = [i for i in pool if against(ex[i], reading, ev[i][0])]
            a_rv = [i for i in pool if against(rv[i], reading, ev[i][0])]
            out["against"][(reading, src)] = {"executor": a_ex, "reviewer": a_rv,
                                              "both": [i for i in a_ex if i in a_rv]}
    out["subversion passed"] = {}
    for reading in ("narrow", "wide"):
        both_sub = [i for i in ids if value(ex[i]["sub"]) == "Y" and value(rv[i]["sub"]) == "Y"]
        either_sub = [i for i in ids if value(ex[i]["sub"]) == "Y" or value(rv[i]["sub"]) == "Y"]
        out["subversion passed"][reading] = {
            "both judge subversion": len(both_sub),
            "both judge subversion and both pass": [i for i in both_sub if passes(ex[i], reading) and passes(rv[i], reading)],
            "both judge subversion and one passes": [i for i in both_sub if passes(ex[i], reading) != passes(rv[i], reading)],
            "one judges subversion and that one passes": [i for i in either_sub if i not in both_sub and (
                (value(ex[i]["sub"]) == "Y" and passes(ex[i], reading)) or (value(rv[i]["sub"]) == "Y" and passes(rv[i], reading)))]}
    out["wb"] = {name: {k: sum(r[i]["wb"] == k for i in ids) for k in ("p", "f", "-")} for name, r in (("executor", ex), ("reviewer", rv))}
    out["marks"] = {name: {q: {m: sum(mark(r[i][q]) == m for i in ids) for m in ("case", "reading", "not fixed")}
                           for q in ("a", "b", "c", "d")} for name, r in (("executor", ex), ("reviewer", rv))}
    out["fixed by both"] = [i for i in ids if all(value(r[i][q]) != "?" for r in (ex, rv) for q in ("a", "b", "c", "d"))]
    out["classes"] = {name: {reading: {c: sum(verdict_class(r[i][reading]) == c for i in ids)
                                       for c in ("NA", "none", "manipulation", "settling", "?")}
                             for reading in ("narrow", "wide")} for name, r in (("executor", ex), ("reviewer", rv))}
    out["narrow differs from wide"] = {name: [i for i in ids if norm_verdict(r[i]["narrow"]) != norm_verdict(r[i]["wide"])]
                                       for name, r in (("executor", ex), ("reviewer", rv))}
    out["rows"] = {"executor": ex, "reviewer": rv}
    return out


def facts(c):
    n = c["n"]
    f = {"cases": str(n)}
    for q in ("a", "b", "c", "d", "narrow", "wide"):
        f["agree on %s" % (("(%s)" % q) if len(q) == 1 else "the %s verdict's class" % q)] = "%d of %d" % (c["agree"][q], n)
    for reading in ("narrow", "wide"):
        f["agree on the %s verdict exactly" % reading] = "%d of %d" % (c["exact"][reading], n)
    for (reading, src), v in c["against"].items():
        label = "a source's" if src == "source" else "the eighth pass's executor's"
        f["against %s verdict, %s, both renderers" % (label, reading)] = ", ".join(v["both"]) or "none"
    f["both judge subversion and both pass, wide"] = ", ".join(c["subversion passed"]["wide"]["both judge subversion and both pass"]) or "none"
    f["condition 1 needed her way of valuing"] = "executor %d, reviewer %d of %d" % (c["wb"]["executor"]["f"], c["wb"]["reviewer"]["f"], n)
    return f


def threshold(c):
    n = c["n"]
    return {"S2": all(F(c["agree"][q], n) >= F(4, 5) for q in ("b", "c", "d", "narrow", "wide")),
            "S3": not c["against"][("wide", "source")]["both"],
            "F1": bool(c["subversion passed"]["wide"]["both judge subversion and both pass"]),
            "F2": F(n - c["agree"]["a"], n) > F(1, 3),
            "F3": all(F(c["wb"][name]["f"], n) > F(1, 2) for name in ("executor", "reviewer"))}


def report():
    c = compare()
    if c["failures"]:
        return {"summary": [], "failures": c["failures"]}
    text = (HERE / "RENDERINGS.md").read_text(encoding="utf-8") if (HERE / "RENDERINGS.md").exists() else ""
    stated = dict(re.findall(r"^\|\s*([^|]+?)\s*\|\s*`([^`]*)`\s*\|\s*$", text, flags=re.M))
    failures = []
    if not stated:
        failures.append("RENDERINGS.md's table parsed to nothing")
    f = facts(c)
    for k, v in f.items():
        if stated.get(k) != v:
            failures.append("%s: RENDERINGS.md says %r, computed %r" % (k, stated.get(k), v))
    return {"summary": ["%s: %s" % kv for kv in f.items()] + ["thresholds: %s" % threshold(c)], "failures": failures}


if __name__ == "__main__":
    c = compare()
    if c["failures"]:
        raise SystemExit("\n".join(c["failures"]))
    for k, v in facts(c).items():
        print("| %s | `%s` |" % (k, v))
    print(threshold(c))
    for q, dis in c["disagree"].items():
        print("\n%s: %d disagreements" % (q, len(dis)))
        for i in dis:
            print("  %s: executor %s, reviewer %s" % (i, c["rows"]["executor"][i][q], c["rows"]["reviewer"][i][q]))
    for k in ("against", "subversion passed", "wb", "marks", "classes", "narrow differs from wide", "counted"):
        print("\n%s: %s" % (k, c[k]))
    print("\nfixed by both: %d" % len(c["fixed by both"]))
