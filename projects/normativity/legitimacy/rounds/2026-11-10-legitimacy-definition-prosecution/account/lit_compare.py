"""LIT_RENDERINGS.md: the executor's classification (LIT_RESULTS.md) against the outside renderer's
(LIT_RENDERING_REVIEWER.md), on the cases of LIT_CASES.md in which an adviser acts.  A failure is a count in
LIT_RENDERINGS.md that is not the one computed."""
from __future__ import annotations

import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
REVIEWER_COLS = ("adv", "chg", "L1", "L2", "L3", "L3p", "verdict", "bk")
ID = r"[HPKCN]\d+[abn]?"


def load_reviewer():
    path = HERE / "LIT_RENDERING_REVIEWER.md"
    rows = {}
    if not path.exists():
        return rows
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^\|\s*(%s)\s*\|(.*)\|\s*$" % ID, line)
        if m and m.group(1) not in rows:
            cells = [c.strip().strip("`") for c in m.group(2).split("|")]
            rows[m.group(1)] = dict(zip(REVIEWER_COLS, cells))
    return rows


def base(x):
    return x.split(".")[0]


def fixed(row):
    return all(base(row[c]) != "?" for c in ("L1", "L2", "L3", "verdict"))


def source_act(s):
    """The source's verdict on the act as the verdict code that agrees with it."""
    out = {i: "P" for i in s["acceptable"]}
    out.update({i: "F" for i in s["faulted"]})
    out["C4"] = "F"
    return out


def compute(a, b, s):
    adv = s["adviser"]
    src = source_act(s)
    c = {"n": len(adv)}
    for col in ("L1", "L2", "L3", "L3p", "verdict"):
        c[col] = [i for i in adv if base(a[i][col]) == base(b[i][col])]
        c[col + "_opposite"] = [i for i in adv if {base(a[i][col]), base(b[i][col])} in ({"R", "N"}, {"F", "P"})]
    c["adv_differ"] = sorted(i for i in a if i in b and a[i]["adv"] != b[i]["adv"])
    c["l3_unfixed_a"] = [i for i in adv if base(a[i]["L3"]) == "?"]
    c["l3_unfixed_b"] = [i for i in adv if base(b[i]["L3"]) == "?"]
    c["bk_a"] = [i for i in adv if a[i]["bk"] == "Y"]
    c["bk_b"] = [i for i in adv if b[i]["bk"] == "Y"]
    c["both_fixed"] = [i for i in s["on_act"] if i in src and fixed(a[i]) and fixed(b[i])]
    for k, r in (("a", a), ("b", b)):
        c["against_" + k] = [i for i in s["on_act"] if i in src and base(r[i]["verdict"]) in "FP"
                             and base(r[i]["verdict"]) != src[i]]
    c["both_fixed_agree"] = [i for i in c["both_fixed"] if base(a[i]["verdict"]) == src[i] == base(b[i]["verdict"])]
    c["acc_flag_a"] = [i for i in s["acceptable"] if base(a[i]["verdict"]) == "F"]
    c["acc_flag_b"] = [i for i in s["acceptable"] if base(b[i]["verdict"]) == "F"]
    return c


def lines(c):
    j = lambda xs: ", ".join(xs) if xs else "none"
    n = c["n"]
    return [
        "line 1: the two agree in %d of %d" % (len(c["L1"]), n),
        "line 2: the two agree in %d of %d" % (len(c["L2"]), n),
        "line 3: the two agree in %d of %d; opposite fixed answers: %s" % (len(c["L3"]), n, j(c["L3_opposite"])),
        "3′: the two agree in %d of %d; opposite fixed answers: %s" % (len(c["L3p"]), n, j(c["L3p_opposite"])),
        "verdict: the two agree in %d of %d; opposite: %s" % (len(c["verdict"]), n, j(c["verdict_opposite"])),
        "whether an adviser acts, differing: %s" % j(c["adv_differ"]),
        "line 3 not fixed: executor %d, reviewer %d of %d" % (len(c["l3_unfixed_a"]), len(c["l3_unfixed_b"]), n),
        "line 3 turns on the booking: executor %d, reviewer %d of %d" % (len(c["bk_a"]), len(c["bk_b"]), n),
        "verdict on the act and every answer fixed by both: %d (%s); the statement's verdict is the source's by both in %d (%s)"
        % (len(c["both_fixed"]), j(c["both_fixed"]), len(c["both_fixed_agree"]), j(c["both_fixed_agree"])),
        "against the source's verdict on the act: executor %s; reviewer %s" % (j(c["against_a"]), j(c["against_b"])),
        "acceptable by the source and flagged: executor %s; reviewer %s" % (j(c["acc_flag_a"]), j(c["acc_flag_b"])),
    ]


def report(a, _other, s):
    b = load_reviewer()
    failures = []
    missing = [i for i in s["adviser"] if i not in b]
    if missing or len(b) < 52:
        failures.append("the reviewer's rendering parses to %d cases; adviser-act cases missing: %s" % (len(b), missing))
        return {"summary": [], "failures": failures}
    out = lines(compute(a, b, s))
    doc = HERE / "LIT_RENDERINGS.md"
    text = doc.read_text(encoding="utf-8") if doc.exists() else ""
    failures += ["LIT_RENDERINGS.md does not state: " + l for l in out if l not in text]
    return {"summary": ["renderings: " + l for l in out], "failures": failures}
