"""The counts of CASE_RUNS.md: five blind codings of the bank of cases from Noggle's book, and the
value-change test of 2026-11-23.

Verdicts on the book's cases are read from `noggle_bank.json` (`author_verdict`; where an id occurs in
two readers' parts the later part is used, and the three such ids carry the same verdict in both).  The
codings are the coders' categorical answers keyed by case id: `bank_coded_11.json` (sheet
BANK_CODING_11.md, all 263 cases), `bank_coded_11_small.json` with `bank_small_key.json` (the same sheet
on 84 cases written outside the book), `bank_coded_14.json`, `bank_coded_15.json`, `bank_coded_16.json`,
`bank_coded_17.json` (sheets BANK_CODING_14.md to _17.md, on subsets fixed by run 11's answers).  The case texts the coders
read, and the words they wrote beside their answers, are not in the repository, so no coding can be
redone from it.

Each scoring rule below is the rule of the scorer that was written before its coding existed, moved
here unchanged in substance, except `posthoc17`, which was written after run 17's result was seen.  A rule's value is True (the conduct fails), False, or None (not settled:
no answer makes it fail and an unclear answer could).

`report()` fails when a count line of CASE_RUNS.md is not among those computed, or the reverse.
"""
from __future__ import annotations

import collections
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
DOC = "CASE_RUNS.md"


def load(name):
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def tN(v):
    """Noggle's verdict as manipulation (True), not (False), or no definite verdict (None)."""
    return True if v in ("manipulates", "acts manipulatively only") else False if v in ("not manipulation", "loose sense only") else None


def either(a, b):
    return True if (a is True or b is True) else None if (a is None or b is None) else False


def tri(*conds):
    return True if any(c is True for c in conds) else None if any(c is None for c in conds) else False


def tally(pairs):
    """pairs of (verdict, rule value): cases, settled, agree, missed, over, unsettled."""
    S = [p for p in pairs if p[1] is not None]
    return collections.OrderedDict([
        ("cases", len(pairs)), ("settled", len(S)), ("agree", sum(a == b for a, b in S)),
        ("missed", sum(bool(a) and not b for a, b in S)), ("over", sum(bool(b) and not a for a, b in S)),
        ("not settled", len(pairs) - len(S))])


# ---------------------------------------------------------------- run 11: the disclosure rule

def manip11(c):
    if c["has_influencer"] == "no" or c["seeks_response"] == "no":
        return False
    m = c["mistakes"]
    if c["lapse_expected"] == "yes" or any(x["told"] == "no" for x in m):
        return True
    return None if (c["lapse_expected"] == "unclear" or any(x["told"] == "unclear" for x in m)) else False


def ivc11(c):
    if c["has_influencer"] == "no":
        return False
    e, k = c["value_change_expected"], c["value_change_known"]
    if e == "yes" and k == "no":
        return True
    return None if (e == "unclear" or (e == "yes" and k == "unclear")) else False


def chapter(where):
    m = re.search(r"(\d+)\.\d", where)
    return int(m.group(1)) if m else None


def bank_and_c11():
    bank, cod = {}, {}
    for c in load("noggle_bank.json"):
        bank[c["id"]] = c
    for c in load("bank_coded_11.json"):
        cod[c["id"]] = c
    return bank, cod


def run11(counts, lists):
    bank, cod = bank_and_c11()
    ids = [i for i in bank if tN(bank[i]["author_verdict"]) is not None]
    counts["run 11: cases of the bank"] = len(bank)
    counts["run 11: cases with a definite verdict of the author's"] = len(ids)
    for part in ("chapters 2 and 3", "chapter 4 on", "all"):
        sel = [i for i in ids if part == "all" or (((chapter(bank[i]["where"]) or 9) <= 3) == part.startswith("chapters"))]
        for k, v in tally([(tN(bank[i]["author_verdict"]), manip11(cod[i])) for i in sel]).items():
            counts["run 11, manipulation, %s: %s" % (part, k)] = v
    lists["run 11, over"] = [i for i in ids if tN(bank[i]["author_verdict"]) is False and manip11(cod[i]) is True]
    lists["run 11, missed"] = [i for i in ids if tN(bank[i]["author_verdict"]) and manip11(cod[i]) is False]
    key = load("bank_small_key.json")
    S = {c["id"]: c for c in load("bank_coded_11_small.json")}
    tI = lambda v: True if v in ("manipulates", "acts manipulatively only") else False if v == "neither" else None
    tL = lambda v: {"ill": True, "leg": False}.get(v.split(":")[0])
    I = [i for i in key if i.startswith("I-")]
    E = [i for i in key if i.startswith("E-") and tL(key[i]) is not None]
    both = lambda i: either(manip11(S[i]), ivc11(S[i]))
    for title, pairs in (
            ("forty cases of the outside model, manipulation", [(tI(key[i]), manip11(S[i])) for i in I]),
            ("forty cases of the outside model, with the value-change clause", [(tI(key[i]), both(i)) for i in I]),
            ("value-change cases with a definite key", [(tL(key[i]), both(i)) for i in E]),
            ("value-change cases keyed by the source's own verdict", [(tL(key[i]), both(i)) for i in E if key[i].endswith(":s")])):
        for k, v in tally(pairs).items():
            counts["run 11, %s: %s" % (title, k)] = v
    # the lapse clause alone
    act = lambda c: c["has_influencer"] == "yes" and c["seeks_response"] == "yes"
    untold = lambda c: any(x["told"] == "no" for x in c["mistakes"])
    unc = lambda c: any(x["told"] == "unclear" for x in c["mistakes"])
    A = [i for i in ids if act(cod[i])]
    for title, sel in (
            ("lapse expected", [i for i in A if cod[i]["lapse_expected"] == "yes"]),
            ("lapse expected, no untold or unclear mistake", [i for i in A if cod[i]["lapse_expected"] == "yes" and not untold(cod[i]) and not unc(cod[i])]),
            ("lapse expected and an untold mistake", [i for i in A if cod[i]["lapse_expected"] == "yes" and untold(cod[i])]),
            ("lapse unclear, no untold mistake", [i for i in A if cod[i]["lapse_expected"] == "unclear" and not untold(cod[i])]),
            ("no lapse expected, no untold or unclear mistake", [i for i in A if cod[i]["lapse_expected"] == "no" and not untold(cod[i]) and not unc(cod[i])])):
        y = sum(tN(bank[i]["author_verdict"]) for i in sel)
        counts["lapse clause, %s: cases" % title] = len(sel)
        counts["lapse clause, %s: manipulation on the author's verdict" % title] = y

    def rule(c, lapse):
        if not act(c):
            return False
        if untold(c) or (lapse and c["lapse_expected"] == "yes"):
            return True
        return None if (unc(c) or (lapse and c["lapse_expected"] == "unclear")) else False
    for lp, title in ((True, "with the lapse clause"), (False, "without the lapse clause")):
        t = tally([(tN(bank[i]["author_verdict"]), rule(cod[i], lp)) for i in ids])
        for k in ("settled", "agree", "missed", "over"):
            counts["rule %s: %s" % (title, k)] = t[k]


# ---------------------------------------------------------------- run 14: regulating against prohibiting

def run14(counts, lists):
    bank, c11 = bank_and_c11()
    c14 = {c["id"]: c for c in load("bank_coded_14.json")}
    counts["run 14: cases coded"] = len(c14)
    untold = lambda i: any(x["told"] == "no" for x in c11[i]["mistakes"])
    y = lambda v: {"yes": True, "no": False}.get(v)
    n = lambda v: {"no": True, "yes": False}.get(v)

    def versions(i):
        c = c14[i]
        lapse = y(c11[i]["lapse_expected"])
        press = lambda *fail: (False if lapse is False else tri(*fail) if lapse else (None if tri(*fail) is not False else False))
        return {
            "regulated": tri(untold(i), press(n(c["open"]), n(c["can_stop"]))),
            "regulated, and she knows its effect": tri(untold(i), press(n(c["open"]), n(c["can_stop"]), n(c["knows_effect"]))),
            "regulated, knows its effect, stopping cheap": tri(untold(i), press(n(c["open"]), n(c["can_stop"]), n(c["knows_effect"]),
                                                                {"costly": True, "cheap": False, "na": False}.get(c["stop_cost"]))),
            "prohibited": tri(untold(i), press(n(c["asked"]))),
        }
    for grp in ("yes", "unclear"):
        sel = [i for i in c14 if c11[i]["lapse_expected"] == grp]
        counts["run 14, lapse %s: cases" % grp] = len(sel)
        counts["run 14, lapse %s: manipulation on the author's verdict" % grp] = sum(tN(bank[i]["author_verdict"]) for i in sel)
        for v in ("regulated", "regulated, and she knows its effect", "regulated, knows its effect, stopping cheap", "prohibited"):
            t = tally([(tN(bank[i]["author_verdict"]), versions(i)[v]) for i in sel])
            for k in ("settled", "agree", "missed", "over"):
                counts["run 14, lapse %s, %s: %s" % (grp, v, k)] = t[k]
    sel = [i for i in c14 if c11[i]["lapse_expected"] == "yes"]
    lists["run 14, regulated misses"] = [i for i in sel if tN(bank[i]["author_verdict"]) and versions(i)["regulated"] is False]


# ---------------------------------------------------------------- runs 15 and 16: the earlier-rating clause

def run_prior(counts, lists, n):
    bank, c11 = bank_and_c11()
    cod = {c["id"]: c for c in load("bank_coded_%d.json" % n)}
    tag = "run %d" % n
    counts[tag + ": cases coded"] = len(cod)
    untold = lambda i: any(x["told"] == "no" for x in c11[i]["mistakes"])
    unc11 = lambda i: any(x["told"] == "unclear" for x in c11[i]["mistakes"])

    def prior(i):
        c = cod[i]
        parts = [{"yes": True, "no": False}.get(c["act_sought"]), {"other": True, "both": True, "telling": False}.get(c["means"]),
                 {"lower": True, "not_lower": False, "no_view": False}.get(c["earlier_rating"]), {"no": True, "yes": False}.get(c["asked"])]
        return False if any(p is False for p in parts) else None if any(p is None for p in parts) else True
    mistake = lambda i: True if untold(i) else None if unc11(i) else False
    rule = lambda i: either(mistake(i), prior(i))
    old = lambda i: either(mistake(i), {"yes": True, "no": False}.get(c11[i]["lapse_expected"]))
    sets = collections.OrderedDict([
        ("lapse expected", [i for i in cod if c11[i]["lapse_expected"] == "yes"]),
        ("lapse unclear", [i for i in cod if c11[i]["lapse_expected"] == "unclear"]),
        ("control", [i for i in cod if c11[i]["lapse_expected"] == "no"])])
    for name, sel in sets.items():
        counts["%s, %s: cases" % (tag, name)] = len(sel)
        counts["%s, %s: manipulation on the author's verdict" % (tag, name)] = sum(tN(bank[i]["author_verdict"]) for i in sel)
        for title, f in (("the clause alone", prior), ("untold mistake or the clause", rule), ("untold mistake or lapse", old)):
            t = tally([(tN(bank[i]["author_verdict"]), f(i)) for i in sel])
            for k in ("settled", "agree", "missed", "over"):
                counts["%s, %s, %s: %s" % (tag, name, title, k)] = t[k]
    for title, f in (("untold mistake or the clause", rule), ("untold mistake or lapse", old)):
        t = tally([(tN(bank[i]["author_verdict"]), f(i)) for i in cod])
        for k in ("settled", "agree", "missed", "over"):
            counts["%s, all coded, %s: %s" % (tag, title, k)] = t[k]
    L = sets["lapse expected"]
    for form in ("override", "bend", "neither", "unclear", "na"):
        counts["%s, lapse expected, form %s: cases" % (tag, form)] = sum(cod[i]["form"] == form for i in L)
    bend = [i for i in cod if cod[i]["form"] == "bend"]
    counts[tag + ", all coded, form bend: cases"] = len(bend)
    counts[tag + ", all coded, form bend: settled by the clause"] = sum(prior(i) is not None for i in bend)
    counts[tag + ", all coded, form bend: convicted by the clause"] = sum(prior(i) is True for i in bend)
    for val in ("lower", "not_lower", "no_view", "unclear"):
        counts["%s, all coded, earlier rating %s: cases" % (tag, val)] = sum(cod[i]["earlier_rating"] == val for i in cod)
    lists[tag + ", control cases convicted"] = [i for i in sets["control"] if prior(i) is True]
    lists[tag + ", lapse expected, not convicted"] = ["%s (%s)" % (i, "passes" if prior(i) is False else "not settled") for i in L if prior(i) is not True]
    for i in ("byron-tunnel-vision", "missed-train-paternalistic"):
        counts["%s, %s convicted by the clause (1 yes, 0 no)" % (tag, i)] = int(prior(i) is True) if i in cod else 0


# ---------------------------------------------------------------- run 17: her prior view of the hypothetical

def run17(counts, lists):
    bank, c11 = bank_and_c11()
    c17 = {c["id"]: c for c in load("bank_coded_17.json")}
    c16 = {c["id"]: c for c in load("bank_coded_16.json")}
    counts["run 17: cases coded"] = len(c17)
    untold = lambda i: any(x["told"] == "no" for x in c11[i]["mistakes"])
    unc11 = lambda i: any(x["told"] == "unclear" for x in c11[i]["mistakes"])

    def clause(i):
        c = c17[i]
        parts = [{"yes": True, "no": False}.get(c["act_sought"]), {"yes": True, "no": False}.get(c["moved"]),
                 {"would_not": True, "would": False, "cannot_say": False}.get(c["prior_view"]), {"no": True, "yes": False}.get(c["asked"])]
        return False if any(p is False for p in parts) else None if any(p is None for p in parts) else True

    def posthoc17(i):
        """Written after the result of `clause` was seen: the same, and her earlier rating on sheet 16 is "lower"."""
        a, b = c17[i], c16[i]
        parts = [{"yes": True, "no": False}.get(a["act_sought"]), {"yes": True, "no": False}.get(a["moved"]),
                 {"would_not": True, "would": False, "cannot_say": False}.get(a["prior_view"]),
                 {"lower": True, "not_lower": False, "no_view": False}.get(b["earlier_rating"]), {"no": True, "yes": False}.get(a["asked"])]
        return False if any(p is False for p in parts) else None if any(p is None for p in parts) else True
    rule = lambda i: either(True if untold(i) else None if unc11(i) else False, clause(i))
    sets = collections.OrderedDict([
        ("lapse expected", [i for i in c17 if c11[i]["lapse_expected"] == "yes"]),
        ("lapse unclear", [i for i in c17 if c11[i]["lapse_expected"] == "unclear"]),
        ("control", [i for i in c17 if c11[i]["lapse_expected"] == "no"])])
    for name, sel in sets.items():
        counts["run 17, %s: cases" % name] = len(sel)
        counts["run 17, %s: manipulation on the author's verdict" % name] = sum(tN(bank[i]["author_verdict"]) for i in sel)
        for title, f in (("the clause alone", clause), ("untold mistake or the clause", rule),
                         ("written after the result, the clause with sheet 16's earlier rating", posthoc17)):
            t = tally([(tN(bank[i]["author_verdict"]), f(i)) for i in sel])
            for k in ("settled", "agree", "missed", "over"):
                counts["run 17, %s, %s: %s" % (name, title, k)] = t[k]
        for val in ("would", "would_not", "cannot_say", "unclear"):
            counts["run 17, %s, prior view %s: cases" % (name, val)] = sum(c17[i]["prior_view"] == val for i in sel)
        for val in ("yes", "no", "unclear"):
            counts["run 17, %s, moved %s: cases" % (name, val)] = sum(c17[i]["moved"] == val for i in sel)
    t = tally([(tN(bank[i]["author_verdict"]), rule(i)) for i in c17])
    for k in ("settled", "agree", "missed", "over"):
        counts["run 17, all coded, untold mistake or the clause: %s" % k] = t[k]
    over = [i for i in sets["control"] if clause(i) is True]
    for val in ("lower", "not_lower", "no_view", "unclear"):
        counts["run 17, control cases convicted, earlier rating on sheet 16 %s: cases" % val] = sum(c16[i]["earlier_rating"] == val for i in over)
    lists["run 17, control cases convicted"] = over
    lists["run 17, lapse expected, not convicted"] = ["%s (%s)" % (i, "passes" if clause(i) is False else "not settled") for i in sets["lapse expected"] if clause(i) is not True]
    lists["run 17, written after the result, control cases convicted"] = [i for i in sets["control"] if posthoc17(i) is True]
    lists["run 17, written after the result, lapse unclear, missed"] = [i for i in sets["lapse unclear"] if tN(bank[i]["author_verdict"]) and posthoc17(i) is False]


# ---------------------------------------------------------------- the value-change test of 2026-11-23

def clause(c):
    if c["has_influencer"] == "no":
        return "outside"
    kn = "yes" if c["asked"] == "yes" else c["known"]
    alt = c["changes_ratings"] == "yes" and c["route"] in ("other", "both")
    if c["untold_relevant"] == "yes" or c["against_own_judgment"] == "yes" or (alt and (kn == "no" or c["can_stop"] == "no")):
        return "illegitimate"
    unc = (c["untold_relevant"] == "unclear" or c["against_own_judgment"] == "unclear" or c["changes_ratings"] == "unclear"
           or (c["changes_ratings"] == "yes" and c["route"] == "unclear") or (alt and (kn == "unclear" or c["can_stop"] == "unclear")))
    return "unclear" if unc else "legitimate"


def third(c):
    if c["has_influencer"] == "no":
        return "outside"
    acts = c["acts_on_her"]
    if c["untold_would_change_her_mind"] == "yes":
        return "illegitimate"
    if acts == "yes" and (c["knows_what_he_is_doing"] == "no" or c["can_stop"] == "no"):
        return "illegitimate"
    unc = c["untold_would_change_her_mind"] == "unclear" or acts == "unclear" or (acts == "yes" and "unclear" in (c["knows_what_he_is_doing"], c["can_stop"]))
    return "unclear" if unc else "legitimate"


def intended(f):
    kn = "yes" if f["asked"] == "yes" else f["known"]
    if f["untold"] == "yes" or (f["route"] == "other" and (kn == "no" or f["can_stop"] == "no")):
        return "illegitimate"
    return "legitimate"


def vc2(counts, lists):
    MAP = {"acceptable": "legitimate", "unacceptable": "illegitimate"}
    key = load("vc2_key.json")
    cases = load("vc2_cases.json")
    var = {v["id"]: v for v in cases["variants"]}
    adv = {c["id"]: c for c in cases["adversarial"]}
    coded = load("vc2_coded.json")
    by = lambda name: {c["id"]: c for c in coded[name]}
    O1, O2 = by("clause, coder 1"), by("clause, coder 2")
    V = collections.OrderedDict([("the clause, coder 1", {i: clause(c) for i, c in O1.items()}), ("the clause, coder 2", {i: clause(c) for i, c in O2.items()})])
    for nm, k in (("self-determination and course-correction", "SC"), ("her judgment about reasons", "JR"), ("would she resist knowing the history", "HR")):
        V[nm] = {i: MAP.get(c["verdict"], c["verdict"]) for i, c in by(k).items()}
    V["the third form"] = {i: third(c) for i, c in by("third, all").items()}
    sets = (("existing sources", [i for i in key if key[i]["set"] == "base"]), ("new sources", [i for i in key if key[i]["set"] == "new"]))
    for sname, ids in sets:
        counts["value change, %s: cases" % sname] = len(ids)
        counts["value change, %s: acceptable on the source's verdict" % sname] = sum(key[i]["verdict"] == "acceptable" for i in ids)
        for nm, v in V.items():
            S = [i for i in ids if v[i] in ("legitimate", "illegitimate")]
            pre = "value change, %s, %s: " % (sname, nm)
            counts[pre + "settled"] = len(S)
            counts[pre + "agree"] = sum(v[i] == MAP[key[i]["verdict"]] for i in S)
            counts[pre + "accepts what the source faults"] = sum(v[i] == "legitimate" and key[i]["verdict"] == "unacceptable" for i in S)
            counts[pre + "faults what the source accepts"] = sum(v[i] == "illegitimate" and key[i]["verdict"] == "acceptable" for i in S)
            counts[pre + "no influencer"] = sum(v[i] == "outside" for i in ids)
    both = sets[0][1] + sets[1][1]
    counts["value change, published cases: the two coders of the clause give the same verdict"] = sum(V["the clause, coder 1"][i] == V["the clause, coder 2"][i] for i in both)
    lists["value change, the clause against a source"] = sorted({i for i in both for nm in ("the clause, coder 1", "the clause, coder 2")
                                                                 if V[nm][i] in ("legitimate", "illegitimate") and V[nm][i] != MAP[key[i]["verdict"]]})
    vid = [i for i in var if i.startswith("V-")]
    counts["value change, minimal pairs: texts"] = len(vid)
    for nm, C in (("coder 1", O1), ("coder 2", O2)):
        f = lambda i: var[i]["factors"]
        counts["value change, minimal pairs, %s: all five intended facts recovered" % nm] = sum(
            (C[i]["route"] if C[i]["route"] != "both" else "other") == f(i)["route"] and C[i]["known"] == f(i)["known"] and C[i]["can_stop"] == f(i)["can_stop"]
            and C[i]["asked"] == f(i)["asked"] and C[i]["untold_relevant"] == f(i)["untold"] for i in vid)
        counts["value change, minimal pairs, %s: the clause gives the intended verdict" % nm] = sum(V["the clause, " + nm][i] == intended(f(i)) for i in vid)
    for kind in ("base", "route", "known", "stop", "asked", "untold"):
        ids = [i for i in vid if i.endswith("-" + kind)]
        for nm in ("the clause, coder 1", "her judgment about reasons", "self-determination and course-correction", "would she resist knowing the history", "the third form"):
            counts["value change, minimal pairs, variant %s, %s: legitimate" % (kind, nm)] = sum(V[nm][i] == "legitimate" for i in ids)
    rid = sorted({i[:-2] for i in var if i.startswith("R-")})
    counts["value change, redescription: pairs"] = len(rid)
    for nm, v in V.items():
        counts["value change, redescription, %s: same verdict under both wordings" % nm] = sum(v[p + "-d"] == v[p + "-c"] for p in rid)
    counts["value change, adversarial: cases"] = len(adv)
    counts["value change, adversarial: with a definite verdict of the outside model's"] = sum(a["your_verdict"] in ("legitimate", "illegitimate") for a in adv.values())
    for form, f, names in (("the clause", clause, ("clause, adversarial, coder 1", "clause, adversarial, coder 2")),
                           ("the third form", third, ("third, adversarial, coder 1", "third, adversarial, coder 2"))):
        C = [by(n) for n in names]
        for n, c in enumerate(C, 1):
            S = [i for i in adv if adv[i]["your_verdict"] in ("legitimate", "illegitimate") and f(c[i]) in ("legitimate", "illegitimate")]
            pre = "value change, adversarial, %s, coder %d: " % (form, n)
            counts[pre + "settled"] = len(S)
            counts[pre + "agree"] = sum(f(c[i]) == adv[i]["your_verdict"] for i in S)
            counts[pre + "legitimate where the outside model says illegitimate"] = sum(f(c[i]) == "legitimate" and adv[i]["your_verdict"] == "illegitimate" for i in S)
            counts[pre + "illegitimate where the outside model says legitimate"] = sum(f(c[i]) == "illegitimate" and adv[i]["your_verdict"] == "legitimate" for i in S)
        counts["value change, adversarial, %s: the two coders give the same verdict" % form] = sum(f(C[0][i]) == f(C[1][i]) for i in adv)
        lists["value change, adversarial, %s, coder 1 differs from the outside model" % form] = [
            i for i in adv if adv[i]["your_verdict"] in ("legitimate", "illegitimate") and f(C[0][i]) in ("legitimate", "illegitimate") and f(C[0][i]) != adv[i]["your_verdict"]]


def compute():
    counts, lists = collections.OrderedDict(), collections.OrderedDict()
    run11(counts, lists)
    run14(counts, lists)
    run_prior(counts, lists, 15)
    run_prior(counts, lists, 16)
    run17(counts, lists)
    vc2(counts, lists)
    return counts, lists


def render():
    counts, lists = compute()
    return ["- %s: **%d**" % kv for kv in counts.items()] + ["- %s: %s" % (k, ", ".join("`%s`" % x for x in v) or "none") for k, v in lists.items()]


def report():
    failures = []
    lines = render()
    path = HERE / DOC
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = [l for l in text.splitlines() if re.match(r"^- (run 1[14567]|lapse clause|rule with|value change)", l)]
    for l in lines:
        if l not in stated:
            failures.append("%s does not state: %s" % (DOC, l))
    for l in stated:
        if l not in lines:
            failures.append("%s states what is not computed: %s" % (DOC, l))
    if not lines:
        failures.append("nothing computed")
    counts, _ = compute()
    pick = ("run 11, manipulation, all: settled", "run 11, manipulation, all: agree", "run 16, lapse expected, the clause alone: settled",
            "run 16, lapse expected, the clause alone: agree", "run 16, control, the clause alone: over",
            "run 17, lapse expected, the clause alone: settled", "run 17, lapse expected, the clause alone: agree", "run 17, control, the clause alone: over")
    return {"summary": ["%s: %d" % (k, counts[k]) for k in pick] + ["%d count lines" % len(lines)], "failures": failures}


if __name__ == "__main__":
    print("\n".join(render()))
    rep = report()
    print("OK" if not rep["failures"] else "FAILURES: %d" % len(rep["failures"]))
