"""The counts of the section *A second coding* of CASE_RUNS.md: sheets BANK_CODING_11.md and
BANK_CODING_16.md each coded a second time (`bank_coded_11_second.json`, `bank_coded_16_second.json`),
counted against the first codings and against the author's verdicts.

The measures and the predictions are those of SECOND_CODING.md, written before the second codings
existed; `PREDICTIONS` below repeats its table.  The scorers are those of `case_runs.py`, called
unchanged: a tally under the second coding is `run11` or `run_prior` with the file it loads replaced.
`prior` below repeats the clause of `run_prior`, which is local to it; `report()` fails if the tallies
of the copy are not the scorer's on any coding.

`report()` fails when a line of CASE_RUNS.md beginning `- second coding` is not among those computed,
or the reverse.
"""
from __future__ import annotations

import collections
import contextlib
import re

from . import case_runs as cr

DOC = "CASE_RUNS.md"
SECOND = {"bank_coded_11.json": "bank_coded_11_second.json", "bank_coded_16.json": "bank_coded_16_second.json"}

# number, measure, predicted, tolerance (SECOND_CODING.md)
PREDICTIONS = [
    (1, "sheet 11, has_influencer the same", 256, 10),
    (2, "sheet 11, seeks_response the same", 252, 10),
    (3, "sheet 11, lapse_expected the same", 180, 10),
    (4, "sheet 11, value_change_expected the same", 240, 10),
    (5, "sheet 11, value_change_known the same", 240, 10),
    (6, "sheet 11, what is told the same", 205, 10),
    (7, "sheet 11, the multiset of (kind, told) the same", 105, 10),
    (8, "sheet 11, the rule's verdict the same, of 263", 205, 10),
    (9, "sheet 11, the rule's verdict the same, of the 240", 188, 10),
    (10, "sheet 11, second coding against the author: settled", 212, 5),
    (11, "sheet 11, second coding against the author: agree", 197, 5),
    (12, "sheet 11, second coding against the author: missed", 8, 2),
    (13, "sheet 11, second coding against the author: over", 7, 2),
    (14, "sheet 16, act_sought the same", 138, 10),
    (15, "sheet 16, means the same", 136, 10),
    (16, "sheet 16, asked the same", 144, 10),
    (17, "sheet 16, earlier_rating the same", 100, 10),
    (18, "sheet 16, form the same", 95, 10),
    (19, "sheet 16, the clause's verdict the same, of 152", 112, 10),
    (20, "sheet 16, second coding, lapse expected, the clause alone: settled", 31, 5),
    (21, "sheet 16, second coding, lapse expected, the clause alone: agree", 29, 5),
    (22, "sheet 16, second coding, lapse expected, the clause alone: missed", 2, 2),
    (23, "sheet 16, second coding, control, the clause alone: settled", 60, 5),
    (24, "sheet 16, second coding, control, the clause alone: over", 3, 2),
    (25, "sheet 16, second coding of both sheets, all coded, untold mistake or the clause: agree", 112, 5),
]


@contextlib.contextmanager
def swapped(*names):
    """`case_runs.load` reading the second coding in place of each named first coding."""
    orig = cr.load
    cr.load = lambda name: orig(SECOND[name] if name in names else name)
    try:
        yield
    finally:
        cr.load = orig


def told(c):
    t = [x["told"] for x in c["mistakes"]]
    return "no" if "no" in t else "unclear" if "unclear" in t else "yes" if t else "none"


def pairs(c):
    return sorted((x["kind"], x["told"]) for x in c["mistakes"])


def prior(c):
    parts = [{"yes": True, "no": False}.get(c["act_sought"]), {"other": True, "both": True, "telling": False}.get(c["means"]),
             {"lower": True, "not_lower": False, "no_view": False}.get(c["earlier_rating"]), {"no": True, "yes": False}.get(c["asked"])]
    return False if any(p is False for p in parts) else None if any(p is None for p in parts) else True


W11 = {True: "fails", False: "passes", None: "not settled"}
W16 = {True: "convicts", False: "passes", None: "not settled"}
F16 = ("act_sought", "earlier_rating", "means", "form", "asked")


def compute():
    counts, lists, failures = collections.OrderedDict(), collections.OrderedDict(), []
    bank, a11 = cr.bank_and_c11()
    with swapped("bank_coded_11.json"):
        _, b11 = cr.bank_and_c11()
    a16 = {c["id"]: c for c in cr.load("bank_coded_16.json")}
    b16 = {c["id"]: c for c in cr.load(SECOND["bank_coded_16.json"])}
    if set(a11) != set(b11) or set(a16) != set(b16):
        failures.append("the second codings do not cover the cases of the first")
        return counts, lists, failures
    definite = [i for i in bank if cr.tN(bank[i]["author_verdict"]) is not None]

    # sheet 11
    counts["sheet 11: cases coded twice"] = len(a11)
    for f in ("has_influencer", "seeks_response", "lapse_expected", "value_change_expected", "value_change_known"):
        counts["sheet 11, %s the same" % f] = sum(a11[i][f] == b11[i][f] for i in a11)
    counts["sheet 11, what is told the same"] = sum(told(a11[i]) == told(b11[i]) for i in a11)
    counts["sheet 11, the multiset of (kind, told) the same"] = sum(pairs(a11[i]) == pairs(b11[i]) for i in a11)
    same = lambda i: cr.manip11(a11[i]) == cr.manip11(b11[i])
    counts["sheet 11, the rule's verdict the same, of 263"] = sum(same(i) for i in a11)
    counts["sheet 11, the rule's verdict the same, of the 240"] = sum(same(i) for i in definite)
    for x in (True, False, None):
        for y in (True, False, None):
            counts["sheet 11, of the 240, first %s and second %s" % (W11[x], W11[y])] = sum(
                cr.manip11(a11[i]) is x and cr.manip11(b11[i]) is y for i in definite)
    sc, sl = collections.OrderedDict(), collections.OrderedDict()
    with swapped("bank_coded_11.json"):
        cr.run11(sc, sl)
    for k in ("settled", "agree", "missed", "over", "not settled"):
        counts["sheet 11, second coding against the author: %s" % k] = sc["run 11, manipulation, all: %s" % k]
    for k in ("settled", "agree", "missed", "over"):
        counts["sheet 11, second coding against the author, without the lapse clause: %s" % k] = sc["rule without the lapse clause: %s" % k]
    lists["sheet 11, second coding, over"] = sl["run 11, over"]
    lists["sheet 11, second coding, missed"] = sl["run 11, missed"]
    for f in ("fails", "passes", "not settled"):
        for s in ("fails", "passes", "not settled"):
            if f != s:
                lists["sheet 11, verdict differs, first %s and second %s" % (f, s)] = []
    show = lambda c: "told %s, lapse %s" % (told(c), c["lapse_expected"]) if c["has_influencer"] == "yes" and c["seeks_response"] == "yes" else "no influencer seeking a response"
    for i in sorted(a11):
        if not same(i):
            x, y = cr.manip11(a11[i]), cr.manip11(b11[i])
            lists["sheet 11, verdict differs, first %s and second %s" % (W11[x], W11[y])].append(
                "%s [%s; %s; author: %s]" % (i, show(a11[i]), show(b11[i]), {True: "manipulation", False: "not", None: "none"}[cr.tN(bank[i]["author_verdict"])]))

    # sheet 16
    counts["sheet 16: cases coded twice"] = len(a16)
    for f in F16:
        counts["sheet 16, %s the same" % f] = sum(a16[i][f] == b16[i][f] for i in a16)
    same16 = lambda i: prior(a16[i]) == prior(b16[i])
    counts["sheet 16, the clause's verdict the same, of 152"] = sum(same16(i) for i in a16)
    for x in (True, False, None):
        for y in (True, False, None):
            counts["sheet 16, first %s and second %s" % (W16[x], W16[y])] = sum(prior(a16[i]) is x and prior(b16[i]) is y for i in a16)
    for f in ("convicts", "passes", "not settled"):
        for s in ("convicts", "passes", "not settled"):
            if f != s:
                lists["sheet 16, verdict differs, first %s and second %s" % (f, s)] = []
    show16 = lambda c: ", ".join("%s %s" % (f.replace("_", " "), c[f]) for f in ("act_sought", "earlier_rating", "means", "asked"))
    for i in sorted(a16):
        if not same16(i):
            lists["sheet 16, verdict differs, first %s and second %s" % (W16[prior(a16[i])], W16[prior(b16[i])])].append(
                "%s [%s; %s; author: %s]" % (i, show16(a16[i]), show16(b16[i]), {True: "manipulation", False: "not", None: "none"}[cr.tN(bank[i]["author_verdict"])]))
    for title, names, c11, c16 in (("sheet 16, second coding", ("bank_coded_16.json",), a11, b16),
                                   ("sheet 16, second coding of both sheets", ("bank_coded_11.json", "bank_coded_16.json"), b11, b16)):
        sc, sl = collections.OrderedDict(), collections.OrderedDict()
        with swapped(*names):
            cr.run_prior(sc, sl, 16)
        for grp in ("lapse expected", "lapse unclear", "control"):
            counts["%s, %s: cases" % (title, grp)] = sc["run 16, %s: cases" % grp]
            counts["%s, %s: manipulation on the author's verdict" % (title, grp)] = sc["run 16, %s: manipulation on the author's verdict" % grp]
            sel = [i for i in c16 if c11[i]["lapse_expected"] == {"lapse expected": "yes", "lapse unclear": "unclear", "control": "no"}[grp]]
            mine = cr.tally([(cr.tN(bank[i]["author_verdict"]), prior(c16[i])) for i in sel])
            for k in ("settled", "agree", "missed", "over"):
                counts["%s, %s, the clause alone: %s" % (title, grp, k)] = sc["run 16, %s, the clause alone: %s" % (grp, k)]
                if mine[k] != sc["run 16, %s, the clause alone: %s" % (grp, k)]:
                    failures.append("the copy of the clause differs from the scorer: %s, %s, %s" % (title, grp, k))
        for k in ("settled", "agree", "missed", "over"):
            counts["%s, all coded, untold mistake or the clause: %s" % (title, k)] = sc["run 16, all coded, untold mistake or the clause: %s" % k]
        for val in ("lower", "not_lower", "no_view", "unclear"):
            if len(names) == 1:
                counts["%s, earlier rating %s: cases" % (title, val)] = sc["run 16, all coded, earlier rating %s: cases" % val]
        if len(names) == 1:
            counts[title + ", form bend: cases"] = sc["run 16, all coded, form bend: cases"]
            counts[title + ", form bend, with a lapse expected: cases"] = sc["run 16, lapse expected, form bend: cases"]
            counts[title + ", form bend: convicted by the clause"] = sc["run 16, all coded, form bend: convicted by the clause"]
            for i in ("byron-tunnel-vision", "missed-train-paternalistic"):
                counts["%s, %s convicted by the clause (1 yes, 0 no)" % (title, i)] = sc["run 16, %s convicted by the clause (1 yes, 0 no)" % i]
        lists[title + ", control cases convicted"] = sl["run 16, control cases convicted"]
        lists[title + ", lapse expected, not convicted"] = sl["run 16, lapse expected, not convicted"]
    # the copy against the scorer on the first coding
    sc = collections.OrderedDict()
    cr.run_prior(sc, collections.OrderedDict(), 16)
    for grp, v in (("lapse expected", "yes"), ("lapse unclear", "unclear"), ("control", "no")):
        mine = cr.tally([(cr.tN(bank[i]["author_verdict"]), prior(a16[i])) for i in a16 if a11[i]["lapse_expected"] == v])
        if any(mine[k] != sc["run 16, %s, the clause alone: %s" % (grp, k)] for k in ("settled", "agree", "missed", "over")):
            failures.append("the copy of the clause differs from the scorer on the first coding: %s" % grp)
    return counts, lists, failures


def predictions(counts):
    out = []
    for n, key, p, tol in PREDICTIONS:
        c = counts[key]
        out.append((n, key, p, tol, c, abs(c - p) <= tol))
    return out


def render():
    counts, lists, _ = compute()
    lines = ["- second coding, %s: **%d**" % kv for kv in counts.items()]
    lines += ["- second coding, %s: %s" % (k, ", ".join("`%s`" % x for x in v) or "none") for k, v in lists.items()]
    P = predictions(counts)
    lines += ["- second coding, prediction %d, %s: predicted **%d** within %d, counted **%d**, %s" % (n, k, p, t, c, "held" if h else "failed") for n, k, p, t, c, h in P]
    lines.append("- second coding, predictions that failed: %s" % (", ".join(str(n) for n, *_, h in P if not h) or "none"))
    return lines


def report():
    counts, lists, failures = compute()
    failures = list(failures)
    lines = render() if not failures else []
    path = cr.HERE / DOC
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = [l for l in text.splitlines() if re.match(r"^- second coding", l)]
    for l in lines:
        if l not in stated:
            failures.append("%s does not state: %s" % (DOC, l))
    for l in stated:
        if l not in lines:
            failures.append("%s states what is not computed: %s" % (DOC, l))
    if not lines:
        failures.append("nothing computed")
    pick = ("sheet 11, the rule's verdict the same, of 263", "sheet 11, second coding against the author: settled",
            "sheet 11, second coding against the author: agree", "sheet 16, the clause's verdict the same, of 152",
            "sheet 16, second coding, lapse expected, the clause alone: settled", "sheet 16, second coding, lapse expected, the clause alone: agree",
            "sheet 16, second coding, control, the clause alone: over")
    failed = [n for n, *_, h in predictions(counts) if not h] if counts else []
    return {"summary": ["%s: %d" % (k, counts[k]) for k in pick if k in counts] + ["predictions failed: %d of %d" % (len(failed), len(PREDICTIONS)), "%d lines" % len(lines)],
            "failures": failures}


if __name__ == "__main__":
    print("\n".join(render()))
