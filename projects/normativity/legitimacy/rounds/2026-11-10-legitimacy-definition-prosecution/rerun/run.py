"""This pass's runner: the bank, the review's four scenes and the new scenes under the revised
definition.  Fails on a case with no scene or no prediction, a computed verdict that diverges
from PREDICTIONS.md without a line in DIVERGENCES.md, a listed divergence that does not occur,
a COUNT or WRONG line in RESULTS.md the computation does not give, a predictions file that
parses to nothing, or a well-definedness check whose stated outcome does not hold."""
from __future__ import annotations

import pathlib
import re
from fractions import Fraction as F

from . import cases
from .model import CANDS, Scene, const

HERE = pathlib.Path(__file__).resolve().parent
ROW = re.compile(r"^\|\s*((?:[A-Z]+\d+[abc]?)(?:\s*,\s*[A-Z]+\d+[abc]?)*)\s*\|(.*)\|\s*$")
LISTED = re.compile(r"^DIVERGENCE ([A-Z]+\d+[abc]?) \((start|end|learning|all)\):", re.M)
COUNT = re.compile(r"^COUNT ([\w-]+) (\w+): right (\d+), wrong (\d+), not counted (\d+)$", re.M)
WRONG = re.compile(r"^WRONG ([\w-]+) (\w+):(.*)$", re.M)
QUESTION = re.compile(r"^QUESTION ([\w-]+): M (\d+)/(\d+), C (\d+)/(\d+), W (\d+)/(\d+)$", re.M)
STRICT_YES = ("NP8", "E6", "K15", "K21", "K23", "X1", "X2b", "X3b", "K31", "D1")
STRICT_NO = ("NP13",)


def parse_items(cell):
    d = {}
    for item in cell.split(";"):
        if "=" in item:
            k, v = item.split("=", 1)
            d[k.strip()] = v.strip()
    return d


def parse_prediction(cell):
    parts = [p.strip() for p in cell.split("//")]
    if len(parts) == 1:
        parts = parts * 3
    out = {}
    for cand, part in zip(CANDS, parts):
        d = parse_items(part)
        m = d.get("M", "none")
        w = d.get("W", "none")
        out[cand] = {"M": [] if m == "none" else sorted(x.strip() for x in m.split(",")),
                     "I": d.get("I") == "yes", "C": d.get("C") == "yes",
                     "W": [] if w == "none" else sorted(x.strip() for x in w.split(","))}
    return out


def load():
    """{id: {'evident': {...}, 'prediction': {cand: {...}}, 'by': str}} from the three tables."""
    text = (HERE / "PREDICTIONS.md").read_text(encoding="utf-8")
    rows = {}
    for line in text.splitlines():
        m = ROW.match(line)
        if not m:
            continue
        cells = [c.strip() for c in m.group(2).split("|")]
        ev = next(i for i, c in enumerate(cells) if re.match(r"^M=(yes|no|con|either)", c))
        for cid in (i.strip() for i in m.group(1).split(",")):
            if cid in rows:
                raise SystemExit("rerun/PREDICTIONS.md: case %s occurs twice" % cid)
            rows[cid] = {"evident": parse_items(cells[ev]), "prediction": parse_prediction(cells[ev + 1]),
                         "by": cells[ev + 2] if len(cells) > ev + 2 else "ex"}
    return rows


def strict_evident(cid, ev):
    if cid in STRICT_YES:
        return {"M": "yes"}
    if cid in STRICT_NO:
        return {"M": "no", "W": ev.get("W", "no")}
    return ev


def score(ev, m, c, w):
    """'right', 'wrong' or 'not counted', with the questions missed."""
    missed, settled = [], 0
    em = ev.get("M", "con")
    if em == "either":
        settled += 1
        if not (m or w):
            missed.append("M or W")
        return ("wrong" if missed else "right"), missed
    if em in ("yes", "no"):
        settled += 1
        if m != (em == "yes"):
            missed.append("M")
    if ev.get("C") in ("yes", "no"):
        settled += 1
        if c != (ev["C"] == "yes"):
            missed.append("C")
    if ev.get("W") in ("yes", "no"):
        settled += 1
        if w != (ev["W"] == "yes"):
            missed.append("W")
    if not settled:
        return "not counted", []
    return ("wrong" if missed else "right"), missed


def by_question(ev, m, c, w):
    """{question: True/False} for each question the evident character settles."""
    out = {}
    em = ev.get("M", "con")
    if em == "either":
        out["M"] = bool(m or w)
        return out
    if em in ("yes", "no"):
        out["M"] = m == (em == "yes")
    if ev.get("C") in ("yes", "no"):
        out["C"] = c == (ev["C"] == "yes")
    if ev.get("W") in ("yes", "no"):
        out["W"] = w == (ev["W"] == "yes")
    return out


def sixth():
    """The sixth follow-up's verdicts as answers to the three questions: {id: {stance: (M, C, W) or None}}."""
    from estimates import cases as old
    out = {}
    for cid, make in old.CASES.items():
        scene = make()
        out[cid] = {}
        for st in ("start", "end"):
            t, _ = scene.tokens(st)
            out[cid][st] = None if "unfixed" in t else ("manipulation" in t, False, bool(t & {"coercion", "tie", "alteration"}))
    return out


def key(v):
    return (tuple(v["M"]), v["I"], v["C"], tuple(v["W"]))


def nonlinear():
    """A calibrated estimate re-expressed by a map that is not affine.  X is 1/2 with probability
    3/4 (signal B) and otherwise 1 three times in four, else 0 (signal A).  The adviser sends the signal;
    it could have sent X.  Her estimate is E[X | signal]; re-expressed, the quantity is X^2 and
    her estimate its square."""
    prior = {("B", F(1, 2)): F(3, 4), ("A", F(0)): F(1, 16), ("A", F(1)): F(3, 16)}

    def scene(power):
        def respond(t, o):
            e = F(9, 16) if o is None else (F(1, 2) if o == "B" else (F(3, 4) if o == "A" else F(o)))
            return {"e": {"X": e ** power}}
        return Scene(prior, {"actual": lambda s: s[0], "full": lambda s: s[1], "none": const(None)}, respond,
                     Y=lambda q, s, act: s[1] ** power)
    a, b = scene(1).judge("start"), scene(2).judge("start")
    return {"as X": a["M"], "as X squared": b["M"], "before, after as X squared":
            [str(scene(2).measure(None, "start")[("e", "X")]), str(scene(2).measure("actual", "start")[("e", "X")])],
            "holds": a["M"] == [] and b["M"] == ["belief"]}


def main():
    failures = []
    pre = load()
    if not pre:
        return 2, {"failures": ["rerun/PREDICTIONS.md parsed to no cases"]}
    scenes = dict(cases.CASES)
    scenes.update(cases.EXTRA)
    for cid in sorted(set(pre) - set(scenes)):
        failures.append("predicted case %s has no scene" % cid)
    for cid in sorted(set(scenes) - set(pre)):
        failures.append("scene %s has no prediction" % cid)
    old = sixth()
    for cid in sorted(set(cases.CASES) ^ set(old)):
        failures.append("case %s is not in both the bank's scenes and this pass's" % cid)
    rows, diverging = [], set()
    groups = {"bank": [c for c in pre if c in cases.CASES], "review": [c for c in pre if c.startswith("R")],
              "new": [c for c in pre if c.startswith("W")]}
    tally = {}
    perq = {}

    def add_q(label, ev, m, c, w):
        t = perq.setdefault(label, {q: [0, 0] for q in "MCW"})
        for q, ok in by_question(ev, m, c, w).items():
            t[q][0] += ok
            t[q][1] += 1
    variants = {k: [] for k in ("any conduct", "return to before", "informed at the estimate", "one faculty per kind",
                                "every quantity counted")}
    split, learning_alone, own_split = [], [], []
    clause = {"clause 1 holds somewhere": [], "clause 2 decides": [], "one conduct only": []}
    for cid, p in pre.items():
        if cid not in scenes:
            continue
        scene = scenes[cid]()
        group = "bank" if cid in cases.CASES else ("review" if cid.startswith("R") else "new")
        verdicts = {}
        for cand in CANDS:
            v = scene.judge(cand)
            verdicts[cand] = v
            add_q({"bank": "", "review": "review-", "new": "new-"}[group] + cand, p["evident"], bool(v["M"]), v["C"], bool(v["W"]))
            if key(v) != key(p["prediction"][cand]):
                diverging.add((cid, cand))
            for table, ev in (("primary", p["evident"]), ("strict", strict_evident(cid, p["evident"]))):
                st, missed = score(ev, bool(v["M"]), v["C"], bool(v["W"]))
                tally.setdefault((group, cand, table), {"right": [], "wrong": [], "not counted": []})[st].append(cid)
            rows.append({"case": cid, "candidate": cand, "M": v["M"], "degree": {k: str(d) for k, d in v["degree"].items()},
                         "I": v["I"], "C": v["C"], "W": v["W"], "clause 1": v["clause1"], "unanswered": v["unanswered"],
                         "left worse in fact": v["left_worse"], "own": {k: str(x) for k, x in v["own"].items()} if isinstance(v["own"], dict) else v["own"],
                         "standing": score(p["evident"], bool(v["M"]), v["C"], bool(v["W"]))})
        if len({key(v) for v in verdicts.values()}) > 1:
            split.append(cid)
            if key(verdicts["learning"]) not in (key(verdicts["start"]), key(verdicts["end"])):
                learning_alone.append(cid)
        if not scene.adviser and len({str(v["own"]) for v in verdicts.values()}) > 1:
            own_split.append(cid)
        if scene.adviser:
            v = verdicts["start"]
            if any(verdicts[c]["clause1"] for c in CANDS):
                clause["clause 1 holds somewhere"].append(cid)
            if any(verdicts[c]["unanswered"] for c in CANDS):
                clause["clause 2 decides"].append(cid)
            if len(scene.conducts) == 1:
                clause["one conduct only"].append(cid)
            for name, kw in (("any conduct", {"any_conduct": True}), ("return to before", {"strict": True}),
                             ("informed at the estimate", {"informed": "est"}), ("one faculty per kind", {"pool": True}),
                             ("every quantity counted", {"broad": True})):
                for cand in CANDS:
                    alt = scene.judge(cand, **kw)
                    if alt["M"] != verdicts[cand]["M"]:
                        variants[name].append("%s (%s): %s -> %s" % (cid, cand, verdicts[cand]["M"] or "none", alt["M"] or "none"))
    # the sixth follow-up's verdicts against the same evident characters
    for st in ("start", "end"):
        for table in ("primary", "strict"):
            t = tally.setdefault(("sixth", st, table), {"right": [], "wrong": [], "not counted": []})
            for cid in groups["bank"]:
                ev = pre[cid]["evident"] if table == "primary" else strict_evident(cid, pre[cid]["evident"])
                if old.get(cid, {}).get(st) is None:
                    t["wrong" if score(ev, False, False, False)[0] != "not counted" else "not counted"].append(cid)
                else:
                    t[score(ev, *old[cid][st])[0]].append(cid)
                if table == "primary":
                    add_q("sixth-" + st, ev, *(old[cid][st] or (None, None, None)))
    # units: per quantity the verdict cannot move (each comparison is within one quantity);
    # with one faculty per kind it does
    units = {"per quantity": [], "one faculty per kind": []}
    for cid, make in scenes.items():
        scene = make()
        if not scene.adviser:
            continue
        qs = sorted({k[1] for k in scene.measure("actual", "start") if k[0] == "e"})
        for q in qs:
            for factor in (F(1, 3), F(2), F(7)):
                for pool, name in ((False, "per quantity"), (True, "one faculty per kind")):
                    if scene.judge("start", pool=pool, scale={q: factor})["M"] != scene.judge("start", pool=pool)["M"]:
                        units[name].append("%s: %s x %s" % (cid, q, factor))
    nl = nonlinear()
    alt = {}
    for cid, (what, make, expect) in cases.ALT.items():
        v = make().judge("start")
        alt[cid] = {"changed": what, "M": v["M"], "C": v["C"], "bank": scenes[cid]().judge("start")["M"]}
        if v["M"] != expect:
            failures.append("the changed-detail scene for %s gives %s, stated %s" % (cid, v["M"], expect))
    if units["per quantity"]:
        failures.append("a verdict moved with the units of one quantity: %s" % units["per quantity"])
    if not nl["holds"]:
        failures.append("the re-expression example does not come out as RESULTS.md states")
    listed = set()
    path = HERE / "DIVERGENCES.md"
    for cid, cand in LISTED.findall(path.read_text(encoding="utf-8") if path.exists() else ""):
        listed |= {(cid, c) for c in (CANDS if cand == "all" else (cand,))}
    for cid, cand in sorted(diverging - listed):
        failures.append("%s (%s) diverges from its prediction and is not listed in DIVERGENCES.md" % (cid, cand))
    for cid, cand in sorted(listed - diverging):
        failures.append("DIVERGENCES.md lists %s (%s), which does not diverge" % (cid, cand))
    rpath = HERE / "RESULTS.md"
    results = rpath.read_text(encoding="utf-8") if rpath.exists() else ""
    names = {"bank": "", "sixth": "sixth-", "review": "review-", "new": "new-"}
    stated = {(m[0], m[1]): tuple(int(x) for x in m[2:]) for m in COUNT.findall(results)}
    stated_wrong = {(m[0], m[1]): sorted(m[2].split()) for m in WRONG.findall(results)}
    for (group, cand, table), t in tally.items():
        label = (names[group] + cand, table)
        have = tuple(len(t[k]) for k in ("right", "wrong", "not counted"))
        if stated.get(label) != have:
            failures.append("RESULTS.md's COUNT line for %s %s is %s; computed %s" % (label[0], table, stated.get(label), have))
        if stated_wrong.get(label) != sorted(t["wrong"]):
            failures.append("RESULTS.md's WRONG line for %s %s is %s; computed %s" % (label[0], table, stated_wrong.get(label), sorted(t["wrong"])))
    stated_q = {m[0]: tuple(int(x) for x in m[1:]) for m in QUESTION.findall(results)}
    for label, t in perq.items():
        have = tuple(x for q in "MCW" for x in t[q])
        if stated_q.get(label) != have:
            failures.append("RESULTS.md's QUESTION line for %s is %s; computed %s" % (label, stated_q.get(label), have))
    return (1 if failures else 0), {"by question": perq,
        "verdicts": rows, "tally": {"%s%s %s" % (names[g], c, tb): t for (g, c, tb), t in tally.items()},
        "diverging": sorted(diverging), "variants": variants, "split by candidate": split,
        "learning differs from both": learning_alone, "her own shortfall splits": own_split, "clause": clause,
        "units": units, "re-expression": nl, "changed details": alt, "failures": failures}


def render(report):
    out = ["case  candidate  M  I  C  W  standing"]
    for r in report.get("verdicts", []):
        out.append("%-5s %-8s M=%-22s I=%-3s C=%-3s W=%-12s %s%s%s" % (
            r["case"], r["candidate"], ",".join("%s %s" % (m, r["degree"][m]) for m in r["M"]) or "none",
            "yes" if r["I"] else "no", "yes" if r["C"] else "no", ",".join(r["W"]) or "none",
            r["standing"][0] + (" on " + ",".join(r["standing"][1]) if r["standing"][1] else ""),
            "  [clause 2 unanswered: %s]" % ",".join(r["unanswered"]) if r["unanswered"] else "",
            "  [left worse in fact: %s]" % ",".join(r["left worse in fact"]) if r["left worse in fact"] else ""))
    out.append("")
    for label, t in report.get("tally", {}).items():
        out.append("COUNT %s: right %d, wrong %d, not counted %d" % (label, len(t["right"]), len(t["wrong"]), len(t["not counted"])))
        out.append("WRONG %s: %s" % (label, " ".join(sorted(t["wrong"]))))
    for label, t in report.get("by question", {}).items():
        out.append("QUESTION %s: M %d/%d, C %d/%d, W %d/%d" % (label, *t["M"], *t["C"], *t["W"]))
    out.append("")
    out.append("diverging from predictions: %s" % ["%s (%s)" % d for d in report.get("diverging", [])])
    for name, items in report.get("variants", {}).items():
        out.append("variant, %s: %s" % (name, "; ".join(items) or "no change"))
    for k in ("split by candidate", "learning differs from both", "her own shortfall splits", "clause", "units", "re-expression", "changed details"):
        out.append("%s: %s" % (k, report.get(k)))
    out.append("")
    out.append("OK" if not report["failures"] else "FAILURES:\n  " + "\n  ".join(report["failures"]))
    return "\n".join(out)


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(HERE.parent))
    code, rep = main()
    print(render(rep))
    sys.exit(code)
