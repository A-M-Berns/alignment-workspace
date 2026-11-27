"""The adversarial test of the formal clauses (PLAIN_TELLING_TESTS.md §3), and the smallest cases of
outside reviews 18 to 20 that fit its format.

`adv/cases.json` holds sixteen cases in prose, written for this test by the author of the account;
each says what plain telling would have done.  `adv/SCHEMA.md` is the sheet two coders were given
with the cases: each turned every case into a small numerical model without being told the clauses
or what the models were for (`adv/encoded_1.json`, `adv/encoded_2.json`).  `adv/key.json` is the
verdict the account is meant to give on each case and the clause meant to fail, fixed before either
encoding existed and kept from the coders.  `evaluate` computes the three clauses from a model in
exact arithmetic (`fractions.Fraction`); it is the checker written before any encoding existed, moved
here unchanged in substance.  A model has two options for her and a rating of A over B that is
`base + sum of weight * view`, so it is a `Problem` of `LegitimacyPlainTelling.lean` with two
options, one case of weight 1 and a linear comparison, at tolerance 0.

Open     fails iff on some matter not declined she takes his view to be other than it is under his
         conduct, and under some plain telling she takes it rightly.
Beliefs  fails iff, not asked, for some plain telling and some matter not declined, her view under
         his conduct is outside the closed interval between her view under that telling and his.
Will     fails iff, not asked, for some plain telling, what she does under his conduct falls further
         below what she herself rates best than under that telling.
Also computed, not part of the definition: whether what she does is worse by his views than under
some plain telling.

Predictions, written with the checker.
 P1  Every encoding is well formed and both coders give a verdict on all 16 cases.
 P2  Each coder's computed verdict matches the key on at least 13 of 16.
 P3  The two coders' computed verdicts agree with each other on at least 13 of 16.
 P4  Where a coder's verdict is 'fail' and the key says 'fail', the failing clauses include the key's
     clause in at least 80% of such cases.
 P5  The case most likely to be encoded differently is A3 (a lie she sees through) or A16 (the
     mood).

`adv/review_cases.json` holds six models written in this round from the replies of reviews 18 to 20,
each with the verdict the present clauses are expected to give; they are by the hand that wrote the
record, not by a blind coder.

`report()` fails when a line of PLAIN_TELLING_TESTS.md beginning `- adversarial test` or
`- review case` is not among those computed, or the reverse.
"""
from __future__ import annotations

import collections
import json
import pathlib
import re
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
DOC = "PLAIN_TELLING_TESTS.md"


def load(name):
    return json.loads((HERE / "adv" / name).read_text(encoding="utf-8"))


def num(x):
    return F(str(x))


def evaluate(m):
    matters = [x["name"] for x in m["matters"]]
    live = [i for i in matters if i not in m.get("declined", [])]
    his = {i: num(m["his"][i]) for i in matters}
    opts = {o["name"]: o for o in m["his_options"]}
    c = opts["conduct"]
    tells = [o for o in m["his_options"] if o.get("is_plain_telling") and o["name"] != "conduct"]
    assert tells, "no plain telling"

    def W(o):
        return {i: num((o.get("weights") or m["weights"])[i]) for i in matters}, num(o.get("base", m["base"]))

    def own(o):
        w, b = W(o)
        return b + sum(w[i] * num(o["her_views"][i]) for i in matters)

    def informed(o):
        w, b = W(o)
        return b + sum(w[i] * (his[i] if i in live else num(o["her_views"][i])) for i in matters)

    def short(o, d):
        return max(F(0), -d) if o["she_does"] == "A" else max(F(0), d)

    def shown(o, i):
        v = o["she_takes_his_views_to_be"][i]
        return None if isinstance(v, str) else num(v)
    asked = bool(m.get("asked"))
    open_fail = [i for i in live if shown(c, i) != his[i] and any(shown(t, i) == his[i] for t in tells)]
    bel_fail = [] if asked else [
        (t["name"], i) for t in tells for i in live
        if not (min(num(t["her_views"][i]), his[i]) <= num(c["her_views"][i]) <= max(num(t["her_views"][i]), his[i]))]
    will_fail = [] if asked else [t["name"] for t in tells if short(c, own(c)) > short(t, own(t))]
    worse = [t["name"] for t in tells if short(c, informed(c)) > short(t, informed(t))]
    clauses = [n for n, f in (("open", open_fail), ("beliefs", bel_fail), ("will", will_fail)) if f]
    return {"verdict": "fail" if clauses else "pass", "clauses": clauses, "worse_by_him": bool(worse)}


def safe(m):
    try:
        return evaluate(m)
    except Exception as e:  # an ill-formed encoding is a result, counted under P1
        return {"verdict": "error", "clauses": [], "worse_by_him": None, "detail": repr(e)[:120]}


def compute():
    key = load("key.json")
    ids = list(key)
    res = {k: {m["id"]: safe(m) for m in load("encoded_%d.json" % k)} for k in (1, 2)}
    missing = {"verdict": "missing", "clauses": [], "worse_by_him": None}
    get = lambda k, i: res[k].get(i, missing)
    lines, counts = [], collections.OrderedDict()
    counts["adversarial test: cases"] = len(ids)
    counts["adversarial test: cases the key fails"] = sum(key[i]["verdict"] == "fail" for i in ids)
    for i in ids:
        a, b = get(1, i), get(2, i)
        show = lambda r: r["verdict"] + (" on " + "+".join(r["clauses"]) if r["clauses"] else "")
        yn = lambda r: {True: "yes", False: "no", None: "none"}[r["worse_by_him"]]
        lines.append("- adversarial test, %s: key %s; coder 1 %s; coder 2 %s; worse by his views than under plain telling: %s, %s" % (
            i, key[i]["verdict"] + (" on " + key[i]["clause"] if key[i]["clause"] else ""), show(a), show(b), yn(a), yn(b)))
    ok = {}
    for k in (1, 2):
        ok[k] = sum(get(k, i)["verdict"] == key[i]["verdict"] for i in ids)
        f = [i for i in ids if key[i]["verdict"] == "fail" and get(k, i)["verdict"] == "fail"]
        right = sum(key[i]["clause"] in get(k, i)["clauses"] for i in f)
        counts["adversarial test, coder %d: verdict matches the key" % k] = ok[k]
        counts["adversarial test, coder %d: fails where the key fails" % k] = len(f)
        counts["adversarial test, coder %d: of those, the key's clause among the failing clauses" % k] = right
        counts["adversarial test, coder %d: encodings ill formed or missing" % k] = sum(get(k, i)["verdict"] in ("error", "missing") for i in ids)
    agree = sum(get(1, i)["verdict"] == get(2, i)["verdict"] for i in ids)
    same_clauses = sum(get(1, i)["clauses"] == get(2, i)["clauses"] for i in ids)
    counts["adversarial test, the two coders: same verdict"] = agree
    counts["adversarial test, the two coders: same failing clauses"] = same_clauses
    counts["adversarial test: cases that pass on both encodings with what she does worse by his views"] = sum(
        get(1, i)["verdict"] == "pass" and get(2, i)["verdict"] == "pass" and get(1, i)["worse_by_him"] and get(2, i)["worse_by_him"] for i in ids)
    preds = collections.OrderedDict()
    preds["adversarial test, prediction P1, every encoding well formed and a verdict on all 16"] = all(
        counts["adversarial test, coder %d: encodings ill formed or missing" % k] == 0 for k in (1, 2)) and len(ids) == 16
    preds["adversarial test, prediction P2, each coder matches the key on at least 13 of 16"] = min(ok.values()) >= 13
    preds["adversarial test, prediction P3, the coders agree with each other on at least 13 of 16"] = agree >= 13
    preds["adversarial test, prediction P4, the key's clause among the failing clauses in at least 80% of shared fails"] = all(
        5 * counts["adversarial test, coder %d: of those, the key's clause among the failing clauses" % k]
        >= 4 * counts["adversarial test, coder %d: fails where the key fails" % k] > 0 for k in (1, 2))
    differ = [i for i in ids if get(1, i)["verdict"] != get(2, i)["verdict"] or get(1, i)["clauses"] != get(2, i)["clauses"]]
    preds["adversarial test, prediction P5, A3 or A16 is given different verdicts or clauses by the two coders"] = bool({"A3", "A16"} & set(differ))
    lines = ["- %s: **%d**" % kv for kv in counts.items()] + lines
    lines += ["- %s: **%s**" % (k, "held" if v else "failed") for k, v in preds.items()]
    failures = []
    rc = load("review_cases.json")
    for m in rc:
        r = safe(m)
        e = m["expect"]
        good = r["verdict"] == e["verdict"] and (not e["clause"] or e["clause"] in r["clauses"])
        if not good:
            failures.append("review case %s: expected %s %s, computed %s %s" % (m["id"], e["verdict"], e["clause"], r["verdict"], r["clauses"]))
        lines.append("- review case %s (%s): %s%s; worse by his views than under plain telling: %s" % (
            m["id"], m["from"], r["verdict"], " on " + "+".join(r["clauses"]) if r["clauses"] else "",
            {True: "yes", False: "no", None: "none"}[r["worse_by_him"]]))
    if not rc:
        failures.append("no review cases")
    return lines, counts, preds, failures


def render():
    return compute()[0]


def report():
    lines, counts, preds, failures = compute()
    path = HERE / DOC
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = [l for l in text.splitlines() if re.match(r"^- (adversarial test|review case)", l)]
    for l in lines:
        if l not in stated:
            failures.append("%s does not state: %s" % (DOC, l))
    for l in stated:
        if l not in lines:
            failures.append("%s states what is not computed: %s" % (DOC, l))
    if not lines:
        failures.append("nothing computed")
    pick = ("adversarial test, coder 1: verdict matches the key", "adversarial test, coder 2: verdict matches the key",
            "adversarial test, the two coders: same verdict")
    return {"summary": ["%s: %d" % (k, counts[k]) for k in pick]
            + ["predictions failed: %d of %d" % (sum(not v for v in preds.values()), len(preds)), "%d lines" % len(lines)],
            "failures": failures}


if __name__ == "__main__":
    print("\n".join(render()))
    rep = report()
    print("OK" if not rep["failures"] else "FAILURES: %d" % len(rep["failures"]))
