"""LIT_RESULTS.md: the counts of its section 3 recomputed from its table and the sets of LIT_CASES.md
Part B; and, once the outside rendering exists, the comparison of LIT_RENDERINGS.md.  A failure is a
count in a document that is not the one computed, or a table that parses to nothing."""
from __future__ import annotations

import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
COLS = ("adv", "chg", "L1", "L2", "L3", "L3p", "verdict", "vs", "bk")
ID = r"[HPKCN]\d+[abn]?"


def load(rel):
    path = HERE / rel
    if not path.exists():
        return {}
    rows = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^\|\s*(%s)\s*\|(.*)\|\s*$" % ID, line)
        if m:
            cells = [c.strip() for c in m.group(2).split("|")]
            if len(cells) >= len(COLS) and m.group(1) not in rows:
                rows[m.group(1)] = dict(zip(COLS, cells))
    return rows


def sets():
    text = (HERE / "LIT_CASES.md").read_text(encoding="utf-8")
    text = text.split("**Sets fixed for the counts", 1)[1].split("## Part C", 1)[0]
    out = {}
    for key, label in (("adviser", "An adviser acts"), ("on_act", "The source's verdict is on that act"),
                       ("acceptable", "The source calls the act acceptable"),
                       ("faulted", "The source faults the act")):
        body = text.split("*" + label, 1)[1].split("\n- *", 1)[0].split(".", 1)[0]
        body = re.sub(r"P1–P6 with P3n and P5n", "P1, P2, P3, P3n, P4, P5, P5n, P6", body)
        for a, lo, hi in re.findall(r"([KCN])(\d+)–[KCN](\d+)", body):
            body += " " + " ".join("%s%d" % (a, i) for i in range(int(lo), int(hi) + 1))
        out[key] = sorted(set(re.findall(r"\b%s\b" % ID, body)))
    return out


def base(x):
    return x.split(".")[0]


def fixed(row):
    return all(base(row[c]) != "?" for c in ("L1", "L2", "L3", "verdict"))


def counts(rows, s):
    adv = [i for i in rows if rows[i]["adv"] == "Y"]
    on = [i for i in s["on_act"] if i in rows]
    fx = [i for i in on if fixed(rows[i])]
    return {
        "cases": len(rows), "adviser": len(adv), "adviser_matches_set": sorted(adv) == s["adviser"],
        "on_act": len(on), "on_act_fixed": fx,
        "agree": [i for i in fx if rows[i]["vs"] == "A"], "disagree": [i for i in fx if rows[i]["vs"] == "D"],
        "acceptable_flagged": [i for i in s["acceptable"] if base(rows[i]["verdict"]) == "F"],
        "l3_unfixed": [i for i in adv if base(rows[i]["L3"]) == "?"],
        "booking": [i for i in adv if rows[i]["bk"] == "Y"],
        "l3_differs_3p": [i for i in adv if base(rows[i]["L3"]) != base(rows[i]["L3p"])],
    }


def compare(a, b, s):
    """Agreement of two renderings on the adviser-act cases of the bank."""
    adv = s["adviser"]
    out = {"n": len(adv)}
    for c in ("L1", "L2", "L3", "L3p", "verdict"):
        same = [i for i in adv if i in a and i in b and base(a[i][c]) == base(b[i][c])]
        out[c] = len(same)
        out[c + "_differ"] = [i for i in adv if i not in same]
    out["both_fixed_on_act"] = [i for i in s["on_act"] if i in a and i in b and fixed(a[i]) and fixed(b[i])]
    return out


def report():
    rows, s = load("LIT_RESULTS.md"), sets()
    failures, summary = [], []
    if len(rows) != 52:
        failures.append("LIT_RESULTS.md parses to %d cases, the bank has 52" % len(rows))
        return {"summary": summary, "failures": failures}
    c = counts(rows, s)
    text = (HERE / "LIT_RESULTS.md").read_text(encoding="utf-8")
    want = [
        (c["adviser_matches_set"], "the cases marked as having an adviser are not the set of LIT_CASES.md"),
        ("in %d of 52" % c["adviser"] in text, "adviser count"),
        ("in %d. The executor fixes every answer in %d" % (c["on_act"], len(c["on_act_fixed"])) in text, "on-act counts"),
        ("the source's in %d and\n  against it in %d" % (len(c["agree"]), len(c["disagree"])) in text, "agreement counts"),
        (all("**%s**" % i in text for i in c["disagree"]), "a disagreement is not named"),
        ("a line flags %d," % len(c["acceptable_flagged"]) in text, "acceptable-and-flagged count"),
        ("**Line 3 is left unfixed** in %d of %d: %s." % (len(c["l3_unfixed"]), c["adviser"], ", ".join(c["l3_unfixed"])) in text, "line 3 unfixed"),
        ("**Line 3 turns on the booking** in %d of %d: %s." % (len(c["booking"]), c["adviser"], ", ".join(c["booking"])) in text, "booking"),
        (not c["l3_differs_3p"], "a fixed answer of 3' differs from line 3's and the document says none does"),
    ]
    failures += ["LIT_RESULTS.md: " + msg for ok, msg in want if not ok]
    summary.append("executor: adviser acts in %d of 52; verdict on the act in %d, all answers fixed in %d, agrees %d, "
                   "disagrees %d (%s); line 3 unfixed in %d; turns on the booking in %d"
                   % (c["adviser"], c["on_act"], len(c["on_act_fixed"]), len(c["agree"]), len(c["disagree"]),
                      ", ".join(c["disagree"]), len(c["l3_unfixed"]), len(c["booking"])))
    other = load("LIT_RENDERING_REVIEWER.md")
    if other:
        try:
            from . import lit_compare
        except ImportError:
            lit_compare = None
        if lit_compare:
            extra = lit_compare.report(rows, other, s)
            summary += extra["summary"]
            failures += extra["failures"]
    return {"summary": summary, "failures": failures}


if __name__ == "__main__":
    r = report()
    print("\n".join(r["summary"]))
    print("OK" if not r["failures"] else "FAILURES:\n  " + "\n  ".join(r["failures"]))
