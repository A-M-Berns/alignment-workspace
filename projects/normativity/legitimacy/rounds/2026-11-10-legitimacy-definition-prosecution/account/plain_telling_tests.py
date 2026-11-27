"""The counts of PLAIN_TELLING_TESTS.md §1 and §2: blind runs 18 and 19 of the statement against
plain telling, on the bank of cases from Noggle's book and on the value-change bank.

Verdicts on the book's cases are read from `noggle_bank.json` (`author_verdict`; where an id occurs
in two readers' parts the later part is used).  Verdicts on the 90 value-change cases are read from
`vc2_key.json`; `vc2_judges_conduct.json` lists the 38 of them whose source judges someone's conduct,
and not something else, picked out by run 19's scorer from a description
that is outside the repository.  The codings are the coders' categorical answers keyed by case id:
`bank_coded_18.json`, `vc2_coded_18.json` (sheet BANK_CODING_18.md, one coder per case);
`bank_coded_19_1.json`, `bank_coded_19_2.json`, `vc2_coded_19_1.json`, `vc2_coded_19_2.json` (sheet
BANK_CODING_19.md, two coders).  Run 18's comparison with the rule of 23 November reads
`bank_coded_11.json` and the ids of `bank_coded_16.json`.  The case texts the coders read, and the
words they wrote beside their answers, are not in the repository, so no coding can be redone from
it.

Each scoring rule and each prediction is that of the scorer written before its coding existed, moved
here unchanged in substance.  A rule's value is True (the conduct fails), False, or None (not
settled: no answer makes it fail and an unclear answer could).  The coders answered questions in
words; no quantity of the formal statement is computed here.

`report()` fails when a line of PLAIN_TELLING_TESTS.md beginning `- run 18` or `- run 19` is not
among those computed, or the reverse.
"""
from __future__ import annotations

import collections
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
DOC = "PLAIN_TELLING_TESTS.md"
Y = {"yes": True, "no": False}


def load(name):
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def tN(v):
    return True if v in ("manipulates", "acts manipulatively only") else False if v in ("not manipulation", "loose sense only") else None


def tally(pairs):
    S = [p for p in pairs if p[1] is not None]
    return collections.OrderedDict([
        ("cases", len(pairs)), ("settled", len(S)), ("agree", sum(a == b for a, b in S)),
        ("missed", sum(bool(a) and not b for a, b in S)), ("over", sum(bool(b) and not a for a, b in S)),
        ("not settled", len(pairs) - len(S))])


def share(n, d, at_least):
    """n/d >= at_least per cent, exactly."""
    return d > 0 and 100 * n >= at_least * d


# ---------------------------------------------------------------- the two rules

def rule18(c, auth=False):
    """Fails iff untold, or induced, or pressed and not asked; with `auth`, or forced."""
    if c["has_influencer"] != "yes":
        return False
    u, i, p, a = Y.get(c["untold"]), Y.get(c["induced"]), Y.get(c["pressed"]), c["asked"]
    press = False if p is False else (False if a == "yes" else (None if (p is None or a == "unclear") else True))
    parts = [u, i, press] + ([Y.get(c["forced"])] if auth else [])
    return True if any(x is True for x in parts) else None if any(x is None for x in parts) else False


def rule19(c, auth=False):
    """Fails iff hidden, or (astray or pressed) and not asked; with `auth`, or forced."""
    if c["has_influencer"] != "yes":
        return False
    h, a, p, k = Y.get(c["hidden"]), Y.get(c["astray"]), Y.get(c["pressed"]), c["asked"]

    def ex(v):
        return False if v is False else (False if k == "yes" else (None if (v is None or k == "unclear") else True))
    parts = [h, ex(a), ex(p)] + ([Y.get(c["forced"])] if auth else [])
    return True if any(x is True for x in parts) else None if any(x is None for x in parts) else False


def rule_1123(c):
    """The rule of 23 November on sheet 11's answers: an untold mistake, or a lapse expected."""
    m = c["mistakes"]
    u = True if any(x["told"] == "no" for x in m) else None if any(x["told"] == "unclear" for x in m) else False
    l = Y.get(c["lapse_expected"])
    return True if (u is True or l is True) else None if (u is None or l is None) else False


def ground(c, keys):
    return "+".join(k for k in keys if c.get(k) == "yes") or "none"


def the_bank():
    bank = {}
    for c in load("noggle_bank.json"):
        bank[c["id"]] = c
    return bank


def vc_key():
    key = load("vc2_key.json")
    tV = lambda i: {"unacceptable": True, "acceptable": False}.get(key[i]["verdict"])
    vids = [i for i in key if tV(i) is not None]
    cond = [i for i in load("vc2_judges_conduct.json") if i in vids]
    return key, tV, vids, cond


# ---------------------------------------------------------------- run 18

def run18(counts, lists, preds):
    bank = the_bank()
    cod = {c["id"]: c for c in load("bank_coded_18.json")}
    c11 = {c["id"]: c for c in load("bank_coded_11.json")}
    assert set(cod) == set(bank), (len(cod), len(bank))
    T = lambda i: tN(bank[i]["author_verdict"])
    ids = [i for i in bank if T(i) is not None]
    inf = [i for i in ids if cod[i]["has_influencer"] == "yes"]
    old = [c["id"] for c in load("bank_coded_16.json") if T(c["id"]) is not None]
    counts["run 18, manipulation bank: cases with a verdict of the book's"] = len(ids)
    counts["run 18, manipulation bank: of those, cases with an influencer"] = len(inf)
    counts["run 18, manipulation bank: of those, manipulation on the book's verdict"] = sum(T(i) for i in inf)
    tl = {}
    for title, pairs in (
            ("cases with an influencer", [(T(i), rule18(cod[i])) for i in inf]),
            ("all cases with a verdict", [(T(i), rule18(cod[i])) for i in ids]),
            ("the 152 cases of earlier runs", [(T(i), rule18(cod[i])) for i in old]),
            ("the rule of 23 November on the same 152", [(T(i), rule_1123(c11[i])) for i in old])):
        tl[title] = tally(pairs)
        for k, v in tl[title].items():
            counts["run 18, manipulation bank, %s: %s" % (title, k)] = v
    missed = [i for i in inf if T(i) and rule18(cod[i]) is False]
    over = [i for i in inf if T(i) is False and rule18(cod[i]) is True]
    lists["run 18, manipulation bank, missed"] = missed
    lists["run 18, manipulation bank, over"] = over
    G = ("untold", "induced", "pressed", "forced")
    for g, n in sorted(collections.Counter(ground(cod[i], G) for i in over).items()):
        counts["run 18, manipulation bank, over, by ground, %s" % g] = n
    key, tV, vids, cond = vc_key()
    vc = {c["id"]: c for c in load("vc2_coded_18.json")}
    assert set(vc) == set(key), (len(vc), len(key))
    rest = [i for i in vids if i not in cond]
    vinf = [i for i in vids if vc[i]["has_influencer"] == "yes"]
    counts["run 18, value-change bank: cases with a verdict of the source's"] = len(vids)
    counts["run 18, value-change bank: of those, faulted by the source"] = sum(tV(i) for i in vids)
    vt = {}
    for title, sel, auth in (
            ("legitimacy alone", vids, False), ("with forced as authority", vids, True),
            ("with forced as authority, cases with an influencer", vinf, True),
            ("post hoc, the source judges conduct, legitimacy alone", cond, False),
            ("post hoc, the source judges conduct, with forced as authority", cond, True),
            ("post hoc, the source judges something other than conduct, legitimacy alone", rest, False),
            ("post hoc, the source judges something other than conduct, with forced as authority", rest, True)):
        vt[title] = tally([(tV(i), rule18(vc[i], auth)) for i in sel])
        for k, v in vt[title].items():
            counts["run 18, value-change bank, %s: %s" % (title, k)] = v
    auth_only = sum(1 for i in vids if tV(i) and rule18(vc[i]) is False and rule18(vc[i], True) is True)
    counts["run 18, value-change bank: convictions by forced alone that the source faults"] = auth_only
    lists["run 18, value-change bank, with forced as authority, passes what the source faults"] = [
        i for i in vids if tV(i) and rule18(vc[i], True) is False]
    lists["run 18, value-change bank, with forced as authority, fails what the source accepts"] = [
        i for i in vids if tV(i) is False and rule18(vc[i], True) is True]
    a, b, o = tl["cases with an influencer"], tl["the 152 cases of earlier runs"], tl["the rule of 23 November on the same 152"]
    alone = sum(1 for i in over if ground(cod[i], G) == "untold")
    v1, v2 = vt["legitimacy alone"], vt["with forced as authority"]
    preds["run 18, prediction M1, settles at least 85% of influencer cases and agrees with the book on at least 92% of those"] = (
        share(a["settled"], a["cases"], 85) and share(a["agree"], a["settled"], 92))
    preds["run 18, prediction M2, at most 6 missed"] = a["missed"] <= 6
    preds["run 18, prediction M3, first part, at most 12 over"] = a["over"] <= 12
    preds["run 18, prediction M3, second part, at least two thirds of those over fail on untold alone"] = 3 * alone >= 2 * len(over)
    preds["run 18, prediction M4, on the 152 not more than 3 agreements worse than the rule of 23 November"] = o["agree"] - b["agree"] <= 3
    preds["run 18, prediction V1, first part, with forced as authority settles at least 50% of the value-change bank"] = share(v2["settled"], v2["cases"], 50)
    preds["run 18, prediction V1, second part, and agrees with the sources on at least 80% of those"] = share(v2["agree"], v2["settled"], 80)
    preds["run 18, prediction V2, at least 5 convictions by forced alone that the source faults"] = auth_only >= 5


# ---------------------------------------------------------------- run 19

def run19(counts, lists, preds):
    bank = the_bank()
    cod = {k: {c["id"]: c for c in load("bank_coded_19_%d.json" % k)} for k in (1, 2)}
    for k in (1, 2):
        assert set(cod[k]) == set(bank), (k, len(cod[k]))
    T = lambda i: tN(bank[i]["author_verdict"])
    ids = [i for i in bank if T(i) is not None]
    inf = [i for i in ids if cod[1][i]["has_influencer"] == "yes" or cod[2][i]["has_influencer"] == "yes"]
    counts["run 19, manipulation bank: cases with a verdict of the book's"] = len(ids)
    counts["run 19, manipulation bank: of those, cases with an influencer on either coding"] = len(inf)
    counts["run 19, manipulation bank: of those, manipulation on the book's verdict"] = sum(T(i) for i in inf)
    tl = {}
    G = ("hidden", "astray", "pressed", "forced")
    for k in (1, 2):
        tl[k] = tally([(T(i), rule19(cod[k][i])) for i in inf])
        for n, v in tl[k].items():
            counts["run 19, manipulation bank, coder %d: %s" % (k, n)] = v
        over = [i for i in inf if T(i) is False and rule19(cod[k][i]) is True]
        lists["run 19, manipulation bank, coder %d, missed" % k] = [i for i in inf if T(i) and rule19(cod[k][i]) is False]
        lists["run 19, manipulation bank, coder %d, over" % k] = over
        lists["run 19, manipulation bank, coder %d, over on hidden alone" % k] = [i for i in over if ground(cod[k][i], G) == "hidden"]
        for g, n in sorted(collections.Counter(ground(cod[k][i], G) for i in over).items()):
            counts["run 19, manipulation bank, coder %d, over, by ground, %s" % (k, g)] = n
    for g, n in sorted(collections.Counter(ground(cod[1][i], G) for i in inf if T(i) and rule19(cod[1][i]) is True).items()):
        counts["run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, %s" % g] = n
    same = [i for i in inf if rule19(cod[1][i]) == rule19(cod[2][i])]
    both = [i for i in same if rule19(cod[1][i]) is not None]
    counts["run 19, manipulation bank, the two coders: same verdict"] = len(same)
    tb = tally([(T(i), rule19(cod[1][i])) for i in both])
    for n in ("cases", "agree", "missed", "over"):
        counts["run 19, manipulation bank, both settle and give the same verdict: %s" % n] = tb[n]
    for q in ("has_influencer", "hidden", "astray", "pressed", "asked", "forced"):
        counts["run 19, manipulation bank, the two coders: same answer on %s" % q] = sum(cod[1][i][q] == cod[2][i][q] for i in inf)
    key, tV, vids, cond = vc_key()
    counts["run 19, value-change bank: cases with a verdict of the source's"] = len(vids)
    counts["run 19, value-change bank: of those, faulted by the source"] = sum(tV(i) for i in vids)
    counts["run 19, value-change bank: of those, the source judges conduct"] = len(cond)
    vc, vt = {}, {}
    for k in (1, 2):
        vc[k] = {c["id"]: c for c in load("vc2_coded_19_%d.json" % k)}
        assert set(vc[k]) == set(key), (k, len(vc[k]))
        for title, sel, auth in (("legitimacy alone", vids, False), ("with forced as authority", vids, True),
                                 ("the source judges conduct, legitimacy alone", cond, False)):
            vt[k, title] = tally([(tV(i), rule19(vc[k][i], auth)) for i in sel])
            for n, v in vt[k, title].items():
                counts["run 19, value-change bank, coder %d, %s: %s" % (k, title, n)] = v
        lists["run 19, value-change bank, coder %d, the source judges conduct, passes what the source faults" % k] = [
            i for i in cond if tV(i) and rule19(vc[k][i]) is False]
        lists["run 19, value-change bank, coder %d, the source judges conduct, fails what the source accepts" % k] = [
            i for i in cond if tV(i) is False and rule19(vc[k][i]) is True]
    counts["run 19, value-change bank, the two coders: same verdict, legitimacy alone"] = sum(
        rule19(vc[1][i]) == rule19(vc[2][i]) for i in vids)
    for k in (1, 2):
        a, v, c = tl[k], vt[k, "legitimacy alone"], vt[k, "the source judges conduct, legitimacy alone"]
        preds["run 19, prediction M1, coder %d, settles at least 85%% of influencer cases and agrees with the book on at least 94%% of those" % k] = (
            share(a["settled"], a["cases"], 85) and share(a["agree"], a["settled"], 94))
        preds["run 19, prediction M2, coder %d, at most 6 missed and at most 10 over" % k] = a["missed"] <= 6 and a["over"] <= 10
        preds["run 19, prediction V1, coder %d, legitimacy alone settles at least 50%% of the value-change bank and agrees with the sources on at least 78%% of those" % k] = (
            share(v["settled"], v["cases"], 50) and share(v["agree"], v["settled"], 78))
        preds["run 19, prediction V2, coder %d, where the source judges conduct agrees on at least 80%% of what it settles" % k] = share(c["agree"], c["settled"], 80)
    preds["run 19, prediction M3, the two coders give the same verdict on at least 88% of cases"] = share(len(same), len(inf), 88)
    preds["run 19, prediction M4, where both settle and give the same verdict, at least 96% agree with the book"] = share(tb["agree"], tb["cases"], 96)


def compute():
    counts, lists, preds = collections.OrderedDict(), collections.OrderedDict(), collections.OrderedDict()
    run18(counts, lists, preds)
    run19(counts, lists, preds)
    return counts, lists, preds


def render():
    counts, lists, preds = compute()
    lines = ["- %s: **%d**" % kv for kv in counts.items()]
    lines += ["- %s: %s" % (k, ", ".join("`%s`" % i for i in v) or "none") for k, v in lists.items()]
    lines += ["- %s: **%s**" % (k, "held" if v else "failed") for k, v in preds.items()]
    return lines


def report():
    failures = []
    lines = render()
    path = HERE / DOC
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = [l for l in text.splitlines() if re.match(r"^- run 1[89]", l)]
    for l in lines:
        if l not in stated:
            failures.append("%s does not state: %s" % (DOC, l))
    for l in stated:
        if l not in lines:
            failures.append("%s states what is not computed: %s" % (DOC, l))
    if not lines:
        failures.append("nothing computed")
    counts, _, preds = compute()
    failed = lambda r: sum(1 for k, v in preds.items() if k.startswith("run %d" % r) and not v)
    total = lambda r: sum(1 for k in preds if k.startswith("run %d" % r))
    pick = ("run 18, manipulation bank, cases with an influencer: settled", "run 18, manipulation bank, cases with an influencer: agree",
            "run 19, manipulation bank, coder 1: agree", "run 19, manipulation bank, coder 2: agree")
    return {"summary": ["%s: %d" % (k, counts[k]) for k in pick]
            + ["run %d: %d of %d predictions failed" % (r, failed(r), total(r)) for r in (18, 19)]
            + ["%d lines" % len(lines)], "failures": failures}


if __name__ == "__main__":
    print("\n".join(render()))
    rep = report()
    print("OK" if not rep["failures"] else "FAILURES: %d" % len(rep["failures"]))
