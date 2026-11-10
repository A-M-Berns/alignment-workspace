"""The checks behind C1–C8.  Each returns a status — holds, refuted or open —
and the data THEOREMS.md reports.  DEFINITIONS.md §3 states what is tested."""
from __future__ import annotations

from itertools import product

from fixture.cases import t1, t2

from . import value
from .cases import x_common_fault, x_gift, x_threat_welcome
from .model import Evaluated, attainable, delta, from_first_pass


def c1():
    a, b = value.c1a(), value.c1b()
    return {"status": "holds" if a["holds"] and b["holds"] else "refuted", "a": a, "b": b}


def c2():
    r = value.c2()
    return {"status": "holds" if r["a_holds"] and r["b_holds"] else "refuted", "check": r}


def _goal_space(goods, weights):
    return [dict(zip(goods, ws)) for ws in product(weights, repeat=len(goods))]


def _deltas(scene, policy, goods, weights):
    return [(g, delta(scene, g, policy)) for g in _goal_space(goods, weights)]


def c3():
    T1 = from_first_pass(t1.build()).scenes[0]
    T2 = from_first_pass(t2.build()).scenes[0]
    gift = x_gift.build().scenes[0]
    rows = {}
    for label, scene, policy, goods in (("T2 offer", T2, "Offer", ("money", "goods", "house")),
                                        ("T1 threat", T1, "Threaten", ("money", "house")),
                                        ("X-gift", gift, "Gift", ("money", "house"))):
        ev = Evaluated(scene)
        l0_holds = not ev.work[(None, policy)]["options"]
        row = {"L0 holds": l0_holds}
        for gname, weights in (("G", (-1, 0, 1)), ("G+", (0, 1))):
            ds = _deltas(scene, policy, goods, weights)
            row[gname] = {"goals": len(ds), "falls": sum(d < 0 for _, d in ds),
                          "rises": sum(d > 0 for _, d in ds),
                          "criterion (ΔAV ≥ 0 for every g)": all(d >= 0 for _, d in ds)}
        rows[label] = row
    welcome = x_threat_welcome.build().scenes[0]
    g = x_threat_welcome.GOAL
    cx = {"goal": g, "AV under the threat": attainable(welcome, g, "Threaten"),
          "AV at the baseline": attainable(welcome, g, None)}
    a = rows["T2 offer"]["G"]["falls"] == 0
    b = rows["T1 threat"]["G"]["falls"] > 0 and rows["T1 threat"]["G"]["rises"] == 0
    agree = {gname: {label: rows[label][gname]["criterion (ΔAV ≥ 0 for every g)"] == rows[label]["L0 holds"]
                     for label in rows} for gname in ("G", "G+")}
    return {"status": "holds" if a and b else "refuted", "a_holds": a, "b_holds": b,
            "rows": rows, "threat_counterexample": cx, "criterion_agrees_with_L0": agree}


def c4():
    r = value.c4()
    t = r["table"]
    conditioned = all(t[(d, f)]["weak"] for d in ("full", "one bit", "baseline") for f in ("opposed", "all"))
    full_unconditional = all(t[("full", f)]["weak"] for f in ("opposed", "aligned", "all"))
    strict = all(t[(d, f)]["strict"] for d in ("full", "one bit", "baseline") for f in ("opposed", "all"))
    fails_aligned = not t[("one bit", "aligned")]["weak"]
    ok = conditioned and full_unconditional and strict and fails_aligned
    return {"status": "holds" if ok else "refuted", "check": r,
            "holds_when_U_contains_an_opposed_aim": conditioned and strict,
            "full_driver_needs_no_condition": full_unconditional,
            "fails_for_one_bit_driver_and_aligned_U": fails_aligned}


def _variants(cases):
    rows = []
    for case in cases:
        for scene in case.scenes:
            ev = Evaluated(scene)
            v = ev.verdicts()
            fp = ev.first_pass()
            rows.append({"id": case.id if len(case.scenes) == 1 else "%s/%s" % (case.id, scene.name),
                         "L": fp["category"] == "legitimate", "L1": fp["l1"],
                         "R": ev.replay_form(), "AL": v["al"] != "steered", "FA": v["fa"] != "steered",
                         "D": ev.decisions_invariant(), "adviser": ev.adviser_side(),
                         "all_working": not v["nonworking"], "fa_verdict": v["fa"], "ev": ev})
    return rows


def _implications(rows, keys):
    out = {}
    for p in keys:
        for q in keys:
            if p != q:
                out["%s => %s" % (p, q)] = [r["id"] for r in rows if r[p] and not r[q]]
    return out


def c5(rows):
    a_fwd = [r["id"] for r in rows if r["FA"] and not r["D"]]
    a_back = [r["id"] for r in rows if r["D"] and not r["FA"]]
    c = value.c5c()
    return {"status": "holds" if not a_fwd and not a_back else "refuted",
            "FA => decisions invariant, counterexamples": a_fwd,
            "decisions invariant => FA, counterexamples": a_back,
            "implications": _implications(rows, ("FA", "L1", "R")), "c": c}


def c6(rows):
    imp = _implications(rows, ("L", "R", "AL", "FA"))
    ok = not imp["FA => AL"] and bool(imp["AL => FA"])
    extra = _variants([x_common_fault.build()])
    for r in extra:
        r.pop("ev")
    outside = _implications(extra, ("L", "R", "AL", "FA"))
    return {"status": "holds" if ok else "refuted", "implications": imp, "variants": len(rows),
            "separated outside the bank by X-fault": sorted(k for k, v in outside.items() if v),
            "X-fault": {k: extra[0][k] for k in ("L", "R", "AL", "FA", "fa_verdict")}}


def c7(new_cases, rows):
    by = {r["id"].split("/")[0]: r for r in reversed(rows)}
    table, quad = {}, {}
    for case in new_cases:
        scene = case.scenes[0]
        d = delta(scene, None, "own")
        steered = by[case.id]["fa_verdict"] == "steered"
        table[case.id] = {"faithful-adviser": by[case.id]["fa_verdict"], "ΔAV(seed aim, own)": d}
        if d != 0:
            quad.setdefault((steered, d > 0), []).append(case.id)
    working_steered = [r["id"] for r in rows if r["fa_verdict"] == "steered" and r["all_working"]
                       and r["id"].startswith("N")]
    broken = [r["id"] for r in rows if r["fa_verdict"] == "broken, not steered" and r["id"].startswith("N")]
    ok = all(quad.get(k) for k in ((True, True), (True, False), (False, True), (False, False)))
    ok = ok and bool(working_steered) and bool(broken)
    return {"status": "holds" if ok else "refuted", "table": table,
            "steered, value rises": quad.get((True, True), []),
            "steered, value falls": quad.get((True, False), []),
            "not steered, value rises": quad.get((False, True), []),
            "not steered, value falls": quad.get((False, False), []),
            "steered with every part working": working_steered,
            "broken, not steered": broken}


def c8(rows):
    def without_free(ev):
        from .model import adviser_output
        return all(len({tuple(x for x in adviser_output(s) if x[1] != "free")
                        for s in ev.built[w][1].values()}) == 1 for w in ev.scene.W)
    as_defined = [r["id"] for r in rows if r["adviser"]]
    modulo = {r["id"]: without_free(r["ev"]) for r in rows}
    return {"status": "open", "holds as defined on": as_defined,
            "holds with writes Z does not read set aside on": [k for k, v in modulo.items() if v],
            "T12 as defined": next(r["adviser"] for r in rows if r["id"] == "T12"),
            "T12 with writes Z does not read set aside": modulo["T12"],
            "her-side verdict agrees with the adviser-side condition (set aside form) except on":
                [r["id"] for r in rows if modulo[r["id"]] != (r["fa_verdict"] != "steered")]}


def run_all(cases, new_cases):
    rows = _variants(cases)
    out = {"C1": c1(), "C2": c2(), "C3": c3(), "C4": c4(), "C5": c5(rows), "C6": c6(rows),
           "C7": c7(new_cases, rows), "C8": c8(rows)}
    for r in rows:
        r.pop("ev")
    out["variants"] = rows
    return out
