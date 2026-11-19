"""The checks behind THEOREMS.md.  Each returns {'supports': status, ...facts}; the status is
computed from the facts, and run.py compares it with the one THEOREMS.md states."""
from __future__ import annotations

import itertools
from fractions import Fraction as F
from functools import lru_cache

from decomposition import scenes as S
from decomposition import theorems as DT
from decomposition.model import classify, measures, merge, profiles, run_step

from . import bank
from . import cases as K
from . import scene as C
from . import weights as W

BAD = K.BAD
BASE = {"null": C.NULL, "teach": C.TEACH, **C.INPUTS}
NEG = F(1, 2 ** 40)
HOLDS, REFUTED = "holds on the stated domain", "refuted"


def key(a):
    return W.key(a)


@lru_cache(maxsize=None)
def cand(principal, goal, purposes, tie=False):
    return C.chainr(purposes, goal, principal, tie=tie)


@lru_cache(maxsize=None)
def kinds_of(principal, goal, purposes, akey, ckey, world, tie=False):
    return frozenset(classify(cand(principal, goal, purposes, tie), world, [dict(akey)], [dict(ckey)])[0])


def bad(principal, goal, purposes, a, c, world, tie=False):
    return frozenset(k for k in kinds_of(principal, goal, purposes, key(a), key(c), world, tie) if k[0] in BAD)


def by_explanation(weighted):
    """(goal, purposes) -> total weight, over the rows that share them."""
    out = {}
    for row, w in weighted:
        k = (row["goal"], row["purposes"])
        out[k] = out.get(k, F(0)) + w
    return out


def weight_where(principal, weighted, pred):
    """The weight of the explanations satisfying pred(goal, purposes); those below 2^-40 are
    not evaluated and their total is returned beside it."""
    total, skipped = F(0), F(0)
    for (goal, purposes), w in by_explanation(weighted).items():
        if w < NEG:
            skipped += w
        elif pred(goal, purposes):
            total += w
    return total, skipped


# --- statement 1 ----------------------------------------------------------------------

CHEATS = {
    "every purpose its mechanism, as a rule": ("true", ("mech", "mech", "mech"), ("bare",)),
    "every purpose its mechanism, as a table": ("true", ("const", "const", "const"), ("patched",)),
    "the opposite goal pursued badly": ("opp", ("anti", "anti", "anti"), W.POLICIES),
    "the goal whatever she does": ("does", ("mech", "mech", "mech"), ("bare",)),
    "the goal whatever she does, parts for it": ("does", ("acc", "world", "world"), W.POLICIES),
    "stated, altered at belief": ("true", ("mech", "world", "world"), W.POLICIES),
    "stated, altered at judge": ("true", ("acc", "mech", "world"), W.POLICIES),
    "stated, altered at act": ("true", ("acc", "world", "mech"), W.POLICIES),
    "the stated purposes with the exceptions that serve them best": ("true", ("acc", "world", "world"), W.POLICIES),
    "the stated candidate, no exceptions": ("true", ("acc", "world", "world"), ("bare",)),
}


def signature(principal, goal, purposes):
    """(action, world) -> the harms, subversions and forces of each adviser input against silence."""
    return {(a, w): bad(principal, goal, purposes, C.INPUTS[a], C.NULL, w) for a in C.INPUTS for w in C.WORLDS}


_SUMMARIES = {}


def summary(principal, drop=None, **cfg):
    k = (principal, drop, tuple(sorted(cfg.items())))
    if k not in _SUMMARIES:
        _SUMMARIES[k] = _summary(principal, drop, **cfg)
    return _SUMMARIES[k]


def _summary(principal, drop=None, **cfg):
    rows = W.table(principal, **cfg)
    wd = W.weigh(rows, drop)
    hv = W.heavy(wd)
    top = W.bits(wd[0][0], drop)
    tied = [W.name(r) for r, _ in wd if W.bits(r, drop) == top]
    purposes = {p: sorted({r["purposes"][i] for r, _ in hv}) for i, p in enumerate(C.PARTS)}
    share = {p: {} for p in C.PARTS}
    goals, says = {}, {}
    for r, w in wd:
        for i, p in enumerate(C.PARTS):
            share[p][r["purposes"][i]] = share[p].get(r["purposes"][i], F(0)) + w
        goals[r["goal"]] = goals.get(r["goal"], F(0)) + w
        says[r["say"]] = says.get(r["say"], F(0)) + w
    gps = sorted({(r["goal"], r["purposes"]) for r, _ in hv})
    sigs = [signature(principal, g, pu) for g, pu in gps]
    split = sorted({a for a in C.INPUTS for w in C.WORLDS if len({bool(s[(a, w)]) for s in sigs}) > 1})
    split_kinds = sorted({a for a in C.INPUTS for w in C.WORLDS if len({s[(a, w)] for s in sigs}) > 1})
    private = sum(w for r, w in wd if "mech" in r["purposes"] or (r["goal"] == "does" and
                  any(W.goal_dependent(p, pu) for p, pu in zip(C.PARTS, r["purposes"]))))
    return {"class": len(rows), "top bits": top, "tied at the top": tied,
            "mass on the top 1, 3, 10": [W.dec(sum(w for _, w in wd[:k])) for k in (1, 3, 10)],
            "exact mass on the top 10": sum(w for _, w in wd[:10]),
            "heavy": len(hv), "heavy purposes": purposes, "heavy goals": sorted({r["goal"] for r, _ in hv}),
            "heavy says": sorted({r["say"] for r, _ in hv}),
            "share by purpose": {p: {k: W.dec(v, 4) for k, v in sorted(d.items(), key=lambda kv: -kv[1])} for p, d in share.items()},
            "share by goal": {k: W.dec(v, 4) for k, v in sorted(goals.items(), key=lambda kv: -kv[1])},
            "share by say": {k: W.dec(v, 4) for k, v in says.items()},
            "exact shares": {"purpose": share, "goal": goals, "say": says},
            "weight on a candidate with a private term": W.dec(private, 4), "exact private": private,
            "heavy split on whether an input is illegitimate": split,
            "heavy split on its kinds": split_kinds,
            "agree": all(len(v) == 1 for v in purposes.values()) and not split_kinds}


def brief(s):
    return {k: s[k] for k in ("tied at the top", "mass on the top 1, 3, 10", "heavy", "heavy purposes", "heavy goals",
                              "heavy split on whether an input is illegitimate")}


def cheats(principal):
    rows = W.table(principal)
    top = min(rows, key=W.bits)
    out = {}
    for label, (goal, purposes, policies) in CHEATS.items():
        pick = [r for r in rows if r["goal"] == goal and r["purposes"] == purposes and r["policy"] in policies]
        if not pick:        # the same term reached under another policy name
            pick = [r for r in rows if r["goal"] == goal and r["purposes"] == purposes]
            if policies == ("bare",):
                pick = [r for r in pick if r["entries"] == 0]
        if policies == ("bare",):
            pick = [r for r in pick if r["say"] == "avow" or goal == "does"]
        r = min(pick, key=W.bits)
        first = r["parsimony"] + r["fit1"] + r["handles1"]
        out[label] = {"bits above the heaviest": W.bits(r) - W.bits(top),
                      "of which parsimony, fit, handles": [r[k] - top[k] for k in ("parsimony", "fit", "handles")],
                      "intersubjectivity (bits it adds to this candidate)": W.bits(r) - first,
                      "exceptions": r["entries"], "say": r["say"]}
        if policies == ("bare",):
            assert r["entries"] == 0
    return out


def check_1():
    out, agree = {}, True
    for pr in C.PRINCIPALS:
        s = summary(pr)
        agree &= s["agree"]
        ablations = {v: brief(summary(pr, drop=v)) for v in W.VIRTUES}
        out[pr] = {**{k: v for k, v in s.items() if not k.startswith("exact")},
                   "cheats": cheats(pr), "ablations": ablations,
                   "language B": brief(summary(pr, lang="B")),
                   "the other reading of what a purpose predicts (view-best)": {
                       **brief(summary(pr, reading="view-best")),
                       "share by purpose": summary(pr, reading="view-best")["share by purpose"],
                       "share by goal": summary(pr, reading="view-best")["share by goal"]},
                   "view-best, language B": brief(summary(pr, reading="view-best", lang="B")),
                   "history 160, 320, 640": {N: brief(summary(pr, N=N))["tied at the top"][:2] for N in (160, 320, 640)},
                   "probes counted 2, 4": {r: brief(summary(pr, r=r))["tied at the top"][:2] for r in (2, 4)},
                   "the four changes alone": brief(summary(pr, families=tuple(C.CHANGES))),
                   "a missed move at 4 and at 16 bits": {m: brief(summary(pr, lang="A-miss%d" % m))["tied at the top"][:2] for m in (4, 16)}}
    return {"supports": HOLDS if agree else REFUTED, "by principal": out,
            "a model of five parts with crossed purposes": "not reached"}


# --- statement 2 ----------------------------------------------------------------------

FACTS = {"belief": ("acc", "acc_theta"), "judge": ("world",), "act": ("world",)}
HANDED = {"belief": ("handed",), "judge": ("local",), "act": ("local",)}


def check_2():
    out, ok = {}, True
    for reading in W.READINGS:
        table = {}
        for pr in ("corrector", "non-corrector"):
            sh = summary(pr, reading=reading)["exact shares"]["purpose"]
            table[pr] = {p: {"by the facts": sum(sh[p].get(x, F(0)) for x in FACTS[p]),
                             "by what it was handed": sum(sh[p].get(x, F(0)) for x in HANDED[p])} for p in C.PARTS}
        verdicts = {p: (table["corrector"][p]["by the facts"] > table["corrector"][p]["by what it was handed"],
                        table["non-corrector"][p]["by what it was handed"] > table["non-corrector"][p]["by the facts"])
                    for p in C.PARTS}
        out[reading] = {"weights": {pr: {p: {k: W.dec(v, 4) for k, v in d.items()} for p, d in t.items()} for pr, t in table.items()},
                        "facts ahead under the corrector; handed ahead under the non-corrector": verdicts}
        if reading == "serves":
            ok = all(a and b for a, b in verdicts.values())
    # the misses behind it: the belief part, by probe family
    misses = {}
    for pr in ("corrector", "non-corrector"):
        for purpose in ("acc", "handed"):
            for reading in W.READINGS:
                o = W.option(pr, "belief", purpose, None, "bare", "A", 80, 1, W.FAMILIES, reading)
                misses["%s, %s, %s" % (pr, purpose, reading)] = {"history": o["fit"], **{f: v for f, v in o["families"].items() if v}}
    return {"supports": HOLDS if ok else REFUTED, "by reading": out, "belief, bits of missed moves with no exception": misses}


# --- statement 3 ----------------------------------------------------------------------

def check_3():
    lies = {"about what she will act on, where she would otherwise be right": (C.INPUTS["lie"], C.NULL, [w for w in C.WORLDS if w[1] != "misleading"]),
            "about a matter nothing reads": (C.INPUTS["false_reason"], C.TEACH, C.WORLDS),
            "to someone already wrong": (C.INPUTS["lie"], C.NULL, [w for w in C.WORLDS if w[1] == "misleading"])}
    out, exact = {}, {}
    for reading in W.READINGS:
        for pr in C.PRINCIPALS:
            wd = W.weigh(W.table(pr, reading=reading))
            for label, (a, c, worlds) in lies.items():
                total, skipped = weight_where(pr, wd, lambda g, pu: any(bad(pr, g, pu, a, c, w) for w in worlds))
                out.setdefault(reading, {}).setdefault(pr, {})[label] = W.dec(total, 4)
                exact[(reading, pr, label)] = total
    by_world = {}
    for reading in W.READINGS:
        for pr in C.PRINCIPALS:
            wd = W.weigh(W.table(pr, reading=reading))
            for e in ("clear", "hard"):
                total, skipped = weight_where(pr, wd, lambda g, pu: any(bad(pr, g, pu, C.INPUTS["lie"], C.NULL, w)
                                                                         for w in C.WORLDS if w[1] == e))
                by_world.setdefault(reading, {}).setdefault(pr, {})[e] = [W.dec(total, 6), "not evaluated: " + W.dec(skipped, 12)]
    first = "about what she will act on, where she would otherwise be right"
    ok = all(exact[("serves", pr, first)] >= F(99, 100) for pr in C.PRINCIPALS)
    stated = {label: any(bad("corrector", "true", C.STATED[0], a, c, w) for w in worlds) for label, (a, c, worlds) in lies.items()}
    return {"supports": HOLDS if ok else REFUTED, "weight of illegitimacy": out,
            "the lie she will act on, by kind of world": by_world, "under the stated candidate": stated}


# --- statement 4 ----------------------------------------------------------------------

# The executor's reading of each case's evident character: I, an influence that should be
# illegitimate; L, one that should not; O, left open or reported; R, a reported case the third
# follow-up counted as matching; W, a case about weights, matched by its banked prediction.
EVIDENT = {
    "I": "D1 D2 D3 D4 D5 D9 D10 D15 D16 D17 D18 D22 P1 P3 P4 P5 P8 P10 P12 P13 B1 B2 B3 B5 T1 T3 T4 T5 T6 T7 T8 T10 "
         "T11 N1 N3 N4 N7 N9 N14 X2 X3 X4 Y4 Y5 Y7 Y8",
    "L": "D6 D7 D8 D11 D12 D13 D14 D19 D20 D21 D24 P2 P6 P7 P9 P11 P14 P15 B4 B6 T2 T9 T12 T13 N2 N5 N6 N10 N12 N13 "
         "X5 X6 X7 Y2 Y6 Y9 Y10",
    "O": "N8 N11 X1", "R": "D23", "W": "Y1 Y3",
}
THIRD = {"over-counts": "P7 Y6 X7 D14 Y9 D13", "misses": "N14 T7 N9 Y4 X3 P10 Y5 Y1 Y3", "mislabelled": "Y7",
         "left open": "N8 N11 X1 D9 P13 T1 D15"}
ADDED = {"Z1": "L", "Z2": "I", "Z3": "L", "Z4": "I", "Z5": "I"}
PRIMARY = {"D16": "D16a", "Y7": "Y7a", "P7": None}       # the variant a case is read by; None: every variant


def bank_results():
    rows = K.all_rows()
    ev = bank.evaluate(rows)
    pre = bank.load()
    others = {rid: s for rid, (v, s) in ev.items()}
    out = {}
    for bid, pred in pre.items():
        for r in rows:
            if r.id == bid or (r.id[:-1] == bid and r.id[-1] in "abc"):
                v, s = ev[r.id]
                out[r.id] = {"row": r, "prediction": pred, "verdict": v, "shown": s, "match": bank.matches(pred, v, s, others)}
    return out


def evident_match(cid, results):
    kind = next(k for k, ids in {**EVIDENT}.items() if cid in ids.split()) if cid not in ADDED else ADDED[cid]
    rows = [r for rid, r in results.items() if rid == cid or (rid[:-1] == cid and rid[-1] in "abc")]
    if cid in PRIMARY and PRIMARY[cid]:
        rows = [results[PRIMARY[cid]]]
    if kind == "O":
        return kind, None
    if kind == "R":
        return kind, True
    if kind == "W":
        return kind, all(r["match"] for r in rows)
    want = kind == "I"
    return kind, all(r["verdict"]["illegitimate"] == want for r in rows)


_ROW_ILLEGIT = {}


def chain_weights():
    """For each Chain row: the weight of illegitimacy under each principal, under the account's
    reading of what a purpose predicts and under the other."""
    out = {}
    for row in K.all_rows():
        if not row.chain or row.aim in ("constant", "none"):
            continue
        cell = {}
        for reading in W.READINGS:
            for pr in C.PRINCIPALS:
                def pred(goal, purposes):
                    k = (row.id, pr, goal, purposes)
                    if k not in _ROW_ILLEGIT:
                        r = K.Row(row.id, row.title, row.chain(purposes, goal, pr), row.aim, alt=row.alt)
                        _ROW_ILLEGIT[k] = K.verdict(r)["illegitimate"]
                    return _ROW_ILLEGIT[k]
                total, _ = weight_where(pr, W.weigh(W.table(pr, reading=reading)), pred)
                cell["%s, %s" % (pr, reading)] = W.dec(total, 4)
        out[row.id] = cell
    return out


def check_4():
    results = bank_results()
    ids = [c for ids in EVIDENT.values() for c in ids.split()]
    table = {cid: evident_match(cid, results) for cid in ids}
    matched = sorted(c for c, (k, m) in table.items() if m)
    missed = sorted(c for c, (k, m) in table.items() if m is False)
    open_ = sorted(c for c, (k, m) in table.items() if m is None)
    third = {label: {c: {"evident": table[c][0], "now": "; ".join(r["shown"] for rid, r in results.items()
                                                                  if rid == c or (rid[:-1] == c and rid[-1] in "abc")),
                         "matches now": table[c][1]} for c in group.split()} for label, group in THIRD.items()}
    third_nonmatching = {c for g in THIRD.values() for c in g.split()}
    broke = sorted(c for c in ids if c not in third_nonmatching and table[c][1] is False)
    added = {c: evident_match(c, results) for c in ADDED}
    # the own-purpose clause: rows whose verdict it changes
    clause = sorted(rid for rid, r in results.items() if r["row"].aim == "own" and
                    any(k in BAD for k, _ in r["verdict"]["kinds"]) and not r["verdict"]["illegitimate"])
    ok = len(ids) == 89 and len(matched) >= 66
    return {"supports": HOLDS if ok else REFUTED, "cases": len(ids), "matching": len(matched), "not matching": missed,
            "open": open_, "the third follow-up's non-matching cases": third,
            "matched then and not now": broke, "added cases": {c: {"evident": k, "matches": m} for c, (k, m) in added.items()},
            "rows where the own-purpose clause changes the verdict": clause,
            "weight of illegitimacy, Chain rows": chain_weights(),
            "predictions matching": sum(1 for r in results.values() if r["match"] and r["prediction"] != "report"),
            "predictions": sum(1 for r in results.values() if r["prediction"] != "report")}


# --- statement 5 ----------------------------------------------------------------------

def legit(principal, goal, purposes, a, other, world, tie=False):
    """No part is harmed, subverted or forced by `a` against the other aim's action."""
    return a == other or not bad(principal, goal, purposes, a, other, world, tie)


def choice(principal, a, world, tie=False):
    c = cand(principal, "true", C.STATED[0], tie)
    return run_step(c, world, a, {}, dict(c.mech)).moves["act"]


def pairs(principal, goal, purposes, tie=False):
    """Over worlds and ordered pairs of base actions: mutually legitimate pairs after which her
    choice differs; and one-sidedly legitimate ones after which it differs and the judging
    part scores her verdict no higher."""
    mutual, one_sided, lower = [], [], []
    c = cand(principal, goal, purposes, tie)
    for w in C.WORLDS:
        ctxs = {n: run_step(c, w, a, {}, dict(c.mech)) for n, a in BASE.items()}
        for n1, n2 in itertools.permutations(BASE, 2):
            x1, x2 = ctxs[n1].moves["act"], ctxs[n2].moves["act"]
            if x1 == x2 or not legit(principal, goal, purposes, BASE[n1], BASE[n2], w, tie):
                continue
            one_sided.append((n1, n2, w))
            if legit(principal, goal, purposes, BASE[n2], BASE[n1], w, tie):
                mutual.append((n1, n2, w))
            Gt = C.goal_true(tie)
            if Gt(ctxs[n1]) < Gt(ctxs[n2]):
                lower.append((n1, n2, w))
    return {"mutually legitimate, her choice differs": len(mutual), "an example": mutual[:1],
            "legitimate one way, her choice differs": len(one_sided),
            "of which her goal is lower under the legitimate action": len(lower), "an example of that": lower[:1]}


def check_5():
    pr, (pu, g) = "corrector", C.STATED
    prior = C.PRIOR
    # (a) teaching only what favours its aim
    sel = lambda aim, w: C.TEACH if w[0] == aim else C.NULL
    selective = {}
    for aim in (0, 1):
        ill = [w for w in C.WORLDS if not legit(pr, g, pu, sel(aim, w), sel(1 - aim, w), w)]
        selective[aim] = {"illegitimate at": ill,
                          "probability she chooses 1": sum(prior[w] * choice(pr, sel(aim, w), w) for w in C.WORLDS),
                          "probability she chooses 1 and the history is legitimate":
                              sum(prior[w] * choice(pr, sel(aim, w), w) for w in C.WORLDS if w not in ill)}
    teach_all = sum(prior[w] * choice(pr, C.TEACH, w) for w in C.WORLDS)
    # (b) the added threat
    old = S.chain()
    base_pol = {w: DT.best_action(old, w, {}) for w in C.WORLDS}
    threat_pol = dict(base_pol)
    threat_pol[(0, "clear")] = C.INPUTS["threat"]
    threat_ill = [w for w in C.WORLDS if not legit(pr, g, pu, threat_pol[w], base_pol[w], w)]
    threat = {"illegitimate at": threat_ill, "kinds there": sorted(bad(pr, g, pu, threat_pol[w], base_pol[w], w) for w in threat_ill),
              "probability she chooses 1: baseline, with the threat":
                  [sum(prior[w] * choice(pr, p[w], w) for w in C.WORLDS) for p in (base_pol, threat_pol)],
              "with the threat, and the history is legitimate":
                  sum(prior[w] * choice(pr, threat_pol[w], w) for w in C.WORLDS if w not in threat_ill)}
    # (c) the statement over pairs of actions
    stated = pairs(pr, g, pu)
    tie = pairs(pr, g, pu, tie=True)
    handed = pairs("non-corrector", "true", ("handed", "local", "local"))
    heavy = {}
    for p in C.PRINCIPALS:
        for reading in W.READINGS:
            wd = W.weigh(W.table(p, reading=reading))
            top = W.bits(wd[0][0])
            tied = sorted({(r["goal"], r["purposes"]) for r, _ in wd if W.bits(r) == top})
            for g2, pu2 in tied:
                heavy["%s, %s: %s; %s" % (p, reading, g2, ", ".join(pu2))] = pairs(p, g2, pu2)
    # (d) against aim-freedom
    c = cand(pr, g, pu)
    x = lambda a, w, t=False: choice(pr, a, w, t)
    w0 = (0, "clear")
    relation = {
        "aim-free (one action at every aim) and illegitimate": False,
        "legitimate at both aims, action and her choice differ by aim (framing between equals)":
            legit(pr, g, pu, C.INPUTS["trick"], C.NULL, w0, True) and legit(pr, g, pu, C.NULL, C.INPUTS["trick"], w0, True)
            and x(C.INPUTS["trick"], w0, True) != x(C.NULL, w0, True),
        "her choice the same at both aims, illegitimate at one (a false reason for a true statement)":
            x(C.INPUTS["false_reason"], w0) == x(C.TEACH, w0) and not legit(pr, g, pu, C.INPUTS["false_reason"], C.TEACH, w0),
        "legitimate at one aim only, her choice differs, the legitimate action a truthful one (Z5)":
            legit(pr, g, pu, C.TEACH, C.NULL, (1, "misleading")) and x(C.TEACH, (1, "misleading")) != x(C.NULL, (1, "misleading")),
    }
    no_gain = (stated["mutually legitimate, her choice differs"] == 0 and tie["mutually legitimate, her choice differs"] == 0
               and all(v["mutually legitimate, her choice differs"] == 0 for v in heavy.values()))
    return {"supports": HOLDS if no_gain else REFUTED,
            "teaching only what favours its aim, by aim": selective, "teaching at every world": teach_all,
            "the least-gap baseline with a threat at (0, clear)": threat,
            "pairs, the stated candidate": stated, "pairs, her goal not reading the option (tie)": tie,
            "pairs, every part scored by what it was handed": handed, "pairs, the heaviest candidate": heavy,
            "against aim-freedom": relation}


# --- statement 6 ----------------------------------------------------------------------

def tv(a, b):
    ka = {r["ident"]: w for r, w in a}
    kb = {r["ident"]: w for r, w in b}
    return sum(abs(ka.get(k, F(0)) - kb.get(k, F(0))) for k in set(ka) | set(kb)) / 2


def check_6():
    out, closer = {}, True
    for reading in W.READINGS:
        for pr in C.PRINCIPALS:
            A, B = W.table(pr, lang="A", reading=reading), W.table(pr, lang="B", reading=reading)
            with_, without = tv(W.weigh(A), W.weigh(B)), tv(W.weigh(A, "intersubjectivity"), W.weigh(B, "intersubjectivity"))
            gp = lambda rows, drop=None: sorted({(r["goal"], r["purposes"]) for r, _ in W.heavy(W.weigh(rows, drop))})
            out["%s, %s" % (pr, reading)] = {
                "distance between the weights under A and under B, with": W.dec(with_, 4), "without": W.dec(without, 4),
                "heaviest under A, B": [W.name(W.weigh(t)[0][0]) for t in (A, B)],
                "heaviest without it under A, B": [W.name(W.weigh(t, "intersubjectivity")[0][0]) for t in (A, B)],
                "heavy explanations shared by A and B, of A's": "%d of %d" % (len(set(gp(A)) & set(gp(B))), len(gp(A)))}
            if reading == "serves":
                closer &= with_ < without
    private = {}
    for pr in C.PRINCIPALS:
        for drop in (None, "intersubjectivity"):
            wd = W.weigh(W.table(pr), drop)
            top = W.bits(wd[0][0], drop)
            tied = [r for r, _ in wd if W.bits(r, drop) == top]
            private["%s%s" % (pr, ", intersubjectivity removed" if drop else "")] = {
                "tied at the top": len(tied),
                "of which with a private term": sum(1 for r in tied if "mech" in r["purposes"] or r["goal"] == "does"),
                "weight on candidates with a private term": W.dec(summary(pr, drop=drop)["exact private"], 4)}
    sizes = {"%s, %s" % (pr, reading): [len(W.table(pr, lang=l, reading=reading)) for l in ("A", "B")]
             for pr in C.PRINCIPALS for reading in W.READINGS}
    return {"supports": HOLDS if closer else REFUTED, "by principal and reading": out,
            "private terms": private, "terms in the class under A, B": sizes}


# --- statement 7 ----------------------------------------------------------------------

def check_7():
    out = {}
    for reading in W.READINGS:
        for pr in C.PRINCIPALS:
            s = summary(pr, reading=reading)
            out["%s, %s" % (pr, reading)] = {"share by goal": s["share by goal"], "share by say": s["share by say"],
                                             "judge": s["share by purpose"]["judge"], "act": s["share by purpose"]["act"]}
    sd = summary("divided")
    ok = sd["heavy goals"] == ["ease"] and sd["heavy says"] == ["please"]
    rows = W.table("divided")
    best = lambda goal, say: min((r for r in rows if r["goal"] == goal and r["say"] == say), key=W.bits)
    grid = {"%s, %s" % (g, s): {k: best(g, s)[k] for k in ("parsimony", "fit", "handles")} for g in ("true", "ease") for s in W.SAYS}
    return {"supports": HOLDS if ok else REFUTED, "by principal and reading": out,
            "divided: the shortest candidate by goal and by what say is for": grid}


# --- statement 8 ----------------------------------------------------------------------

def oppositions(c, world, action):
    """(q, p): q serves, and another move of q would leave p a higher best or a smaller gap."""
    ctx = run_step(c, world, action, {}, dict(c.mech))
    m0 = measures(c, ctx)
    found = set()
    for q in c.parts:
        if m0[q.name][2] != 0:
            continue
        for mv in q.moves(ctx):
            if mv == ctx.moves[q.name]:
                continue
            alt = measures(c, run_step(c, world, merge(action, {"force": {q.name: mv}}), {}, dict(c.mech)))
            for p in c.parts:
                if p.name != q.name and (alt[p.name][0] > m0[p.name][0] or alt[p.name][2] < m0[p.name][2]):
                    found.add((q.name, p.name))
    return found


def together(c, world, action):
    """Reading 4 at one situation: (the parts' maxima can be had together, and then give the goal its maximum)."""
    ctx = run_step(c, world, action, {}, dict(c.mech))
    profs = list(profiles(c, ctx))
    tops = {p.name: max(p.goal(x, x.moves[p.name]) for x in profs) for p in c.parts}
    gmax = max(c.goal(x) for x in profs)
    full = [x for x in profs if all(p.goal(x, x.moves[p.name]) == tops[p.name] for p in c.parts)]
    return bool(full), bool(full) and all(c.goal(x) == gmax for x in full)


@lru_cache(maxsize=None)
def reading4(principal, goal, purposes):
    c = cand(principal, goal, purposes)
    return all(all(together(c, w, a)) for w, a, n in W.history(80))


def reading3(principal, row):
    c = cand(principal, row["goal"], row["purposes"])
    for k in row["normal"]:
        world = dict(k)["world"]
        action = {kk: vv for kk, vv in k if kk != "world"}
        if oppositions(c, world, action):
            return False
    return True


def check_8():
    stated = cand("corrector", *reversed(C.STATED))
    tumour = [(th, "tumour") for th in (0, 1)]
    d23 = {"opposed pairs at the tumour worlds (reading 3)": sorted(set().union(*[oppositions(stated, w, {}) for w in tumour])),
           "the parts' maxima had together, and then her goal's (reading 4)": [together(stated, w, {}) for w in tumour],
           "a gap there": any(g for w in tumour for *_, g in measures(stated, run_step(stated, w, {}, {}, dict(stated.mech))).values())}
    expressed = bool(d23["opposed pairs at the tumour worlds (reading 3)"])
    out = {}
    for reading in W.READINGS:
        for pr in C.PRINCIPALS:
            wd = W.weigh(W.table(pr, reading=reading))
            no_normal = sum(w for row, w in wd if not row["normal"])
            keep = {"reading 3": [], "reading 4": [], "both": []}
            mass = {k: F(0) for k in keep}
            skipped = F(0)
            for row, w in wd:
                if w < NEG:
                    skipped += w
                    continue
                r3, r4 = reading3(pr, row), reading4(pr, row["goal"], row["purposes"])
                for label, ok in (("reading 3", r3), ("reading 4", r4), ("both", r3 and r4)):
                    if ok:
                        keep[label].append((row, w))
                        mass[label] += w
            out["%s, %s" % (pr, reading)] = {
                "heaviest": W.name(wd[0][0]),
                "weight on candidates with no normal condition in the history": W.dec(no_normal, 10),
                "weight meeting reading 3, reading 4, both": [W.dec(mass[k], 4) for k in ("reading 3", "reading 4", "both")],
                "heaviest meeting reading 3": W.name(keep["reading 3"][0][0]) if keep["reading 3"] else None,
                "heaviest meeting reading 4": W.name(keep["reading 4"][0][0]) if keep["reading 4"] else None,
                "heaviest meeting both": W.name(keep["both"][0][0]) if keep["both"] else None,
                "bits the heaviest meeting both is above the heaviest":
                    (W.bits(keep["both"][0][0]) - W.bits(wd[0][0])) if keep["both"] else None,
                "weight not evaluated": W.dec(skipped, 12)}
    stated_row = next(r for r in W.table("corrector") if r["goal"] == "true" and r["purposes"] == C.STATED[0] and r["policy"] == "bare")
    cw = cand("corrector", "true", ("const", "world", "world"))
    return {"supports": HOLDS if expressed else REFUTED, "D23 under the stated candidate": d23,
            "a part with the purpose const opposing others (const, world, world at (0, hard))": sorted(oppositions(cw, (0, "hard"), {})),
            "the stated candidate meets reading 3, reading 4 on the history":
                [reading3("corrector", stated_row), reading4("corrector", "true", C.STATED[0])],
            "by principal and reading": out}


# --- statement 9 ----------------------------------------------------------------------

def check_9():
    delta, lam = F(1), F(3)
    Gt = C.goal_true()
    out, ok = {}, True
    for pr in C.PRINCIPALS:
        gw = {k: w for k, w in by_explanation(W.weigh(W.table(pr))).items() if w >= NEG}
        covered = sum(gw.values())
        decision = {}
        for name, a in BASE.items():
            u = v = F(0)
            for (goal, purposes), wt in gw.items():
                c = cand(pr, goal, purposes)
                for w in C.WORLDS:
                    is_legit = legit(pr, goal, purposes, a, C.NULL, w)
                    val = Gt(run_step(c, w, a, {}, dict(c.mech))) / 3 if is_legit else -delta / 2
                    ok &= (0 <= val <= 1) if is_legit else (-delta <= val < 0)
                    n = 0 if is_legit else 1
                    u += C.PRIOR[w] * wt * (val - lam * n)
                    v += C.PRIOR[w] * wt * n
            decision[name] = {"U": W.dec(u / covered, 4), "weight of illegitimacy v": W.dec(v / covered, 4), "exact v": v / covered}
        ok &= decision["null"]["exact v"] == 0
        # three steps of the lie: the running sum of the weight of illegitimacy against cut-offs
        per_step = decision["lie"]["exact v"]
        running = [per_step * (t + 1) for t in range(3)]
        at_clear = sum(wt for (goal, purposes), wt in gw.items()
                       if not legit(pr, goal, purposes, C.INPUTS["lie"], C.NULL, (0, "clear"))) / covered
        positive = {name: decision[name]["exact v"] > 0 for name in BASE}
        out[pr] = {"a lie at (0, clear), its weight of illegitimacy": W.dec(at_clear, 6),
                   "actions with positive weight of illegitimacy among the candidates evaluated": sorted(n for n, x in positive.items() if x),
                   "decision": {k: {kk: vv for kk, vv in d.items() if kk != "exact v"} for k, d in decision.items()},
                   "weight covered": W.dec(covered, 6),
                   "three lies, running sum": [W.dec(x, 4) for x in running],
                   "first step at which it exceeds 1/2, 1, 2": [next((t for t, x in enumerate(running) if x > c), None) for c in (F(1, 2), 1, 2)]}
    drift = next(r for r in K.all_rows() if r.id == "D16a")
    v = K.verdict(drift)
    return {"supports": HOLDS if ok else REFUTED, "by principal": out,
            "slow drift (D16a, the stated candidate): steps illegitimate": sorted(v["illegit_steps"]),
            "step at which its running count first exceeds a cut-off of 0, 1, 2, 3":
                [next((t for t in range(v["steps"]) if len([x for x in v["illegit_steps"] if x <= t]) > c), None) for c in (0, 1, 2, 3)],
            "V within the Scoring's bounds, and the null action respecting": ok}


CHECKS = {"1": check_1, "2": check_2, "3": check_3, "4": check_4, "5": check_5, "6": check_6, "7": check_7,
          "8": check_8, "9": check_9}
