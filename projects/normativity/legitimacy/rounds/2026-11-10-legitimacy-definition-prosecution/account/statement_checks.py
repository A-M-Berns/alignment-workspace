"""The twelve formal items of STATEMENT_CHECKS.md on the statement of STATEMENT.md, each an
instance in exact rationals or a seeded search; spec_run.py does the computing.
Run: python3 -m account.statement_checks (from the round directory)."""
from __future__ import annotations

import pathlib
import random
import re
from fractions import Fraction as F

from . import spec_run as sr

HERE = pathlib.Path(__file__).resolve().parent
T = lambda n: str(F(n, 20))


def scene(policies, actual, nu, states=None, absent=None):
    """A specification with one option; policies: name -> (R_now of its future, later valuing
    as {thing: twentieths} or {state: {...}}, optional gain)."""
    states = states or {"w": "1"}
    futures, pols = {}, {}
    for name, v in policies.items():
        R, later = v[0], v[1]
        futures["f_" + name] = None if R is None else str(F(R))
        if all(isinstance(x, dict) for x in later.values()):
            lat = {s: [{k: str(F(x)) for k, x in d.items()}] for s, d in later.items()}
        else:
            lat = {"*": [{k: str(F(x)) for k, x in later.items()}]}
        pols[name] = {"does": name, "outcome": {"*": {"go": "f_" + name}}, "r": "Rs", "takes": "top",
                      "later": lat, "gain": str(v[2]) if len(v) > 2 else "0"}
    while len(pols) < 4:
        k = "pad%d" % len(pols)
        pols[k] = dict(pols[nu], does="as the baseline")
    return {"id": "x", "states": states, "options": ["go"], "futures": futures, "policies": pols,
            "actual": actual, "nu": nu, "absent": absent or nu, "fixed": [], "order": []}


def l3(raw, delta, setting="E"):
    return sr.compute(sr.Spec(raw), F(delta), setting)["l3"]


def tenth_l3(raw, delta):
    """The tenth follow-up's line 3 in this setting: best within delta of nu less best within delta of pi*."""
    S = sr.Spec(raw)
    R = {n: sr.R_policy(S, n, "E") for n in S.pol}
    near = lambda a: [n for n in S.pol if all(sr.dist(S, n, a, s) <= delta for s in S.states)]
    return max(R[n] for n in near(S.nu)) - max(R[n] for n in near(S.actual))


H = F(1, 20)


def item1():
    # one set of ratings, two bookings: a fact she is wrong about, or part of her valuing
    base = {"id": "x", "states": {"w": "1"}, "options": ["take", "leave"],
            "futures": {"took": T(5), "left": T(10)},
            "policies": {n: {"does": n, "outcome": {"*": {"take": "took", "leave": "left"}},
                             "r": {"o": {"take": T(16), "leave": T(10)}}, "takes": "top",
                             "later": {"*": [{"it": T(5)}]}, "gain": "0"} for n in ("a", "b", "c", "d")},
            "actual": "a", "nu": "b", "absent": "b", "fixed": [], "order": []}
    as_valuing = sr.compute(sr.Spec(base), F(0), "E")
    as_fact = dict(base, facts={"she_will_find_it_good": {"w": "0"}})
    as_fact["policies"] = {n: dict(p, xhat={"o": {"she_will_find_it_good": "9/10"}}) for n, p in base["policies"].items()}
    f = sr.compute(sr.Spec(as_fact), F(0), "E")
    # the fact priced as a bet in both: an option whose informed rating is the fact's value
    def with_bet(raw):
        raw = dict(raw, options=raw["options"] + ["bet"], futures=dict(raw["futures"], bet_lost="0"))
        raw["policies"] = {n: dict(p, outcome={"*": dict(p["outcome"]["*"], bet="bet_lost")},
                                   r={"o": dict(p["r"]["o"], bet="9/10")}, takes={"o": "take"})
                           for n, p in raw["policies"].items()}
        return raw
    v2, f2 = sr.compute(sr.Spec(with_bet(base)), F(0), "E"), sr.compute(sr.Spec(with_bet(as_fact)), F(0), "E")
    # what looks like a redescription and is not: her informed rating of the thing differs
    other = dict(base, futures={"took": T(16), "left": T(10)})
    o = sr.compute(sr.Spec(other), F(0), "E")
    ok = (as_valuing["l1"] == F(121, 400) and f["l1"] == F(81, 100) and (as_valuing["l2"], as_valuing["l3"]) == (f["l2"], f["l3"])
          and v2["l1"] == f2["l1"] == F(81, 100) and o["l1"] == 0 and as_valuing["l1"] != o["l1"])
    return ("holds with a stated condition" if ok else "FAILS",
            {"l1 as valuing": as_valuing["l1"], "l1 as fact": f["l1"], "l1 with the bet, both": (v2["l1"], f2["l1"]),
             "l1 with R changed": o["l1"]})


def item2():
    # Jeffrey-Bolker: atoms with chance P and utility u; rotate; preferences over events and
    # yardstick numbers unchanged; the probability of a fact she cares about changed.
    ub, uw = F(1), F(0)
    atoms = {"x1": (F(3, 10), F(4, 5)), "x0": (F(3, 10), F(1, 5))}
    grid = [F(k, 10) for k in range(11)]
    for qv in grid:
        atoms[("best", qv)] = (F(4, 110) * qv, ub)
        atoms[("worst", qv)] = (F(4, 110) * (1 - qv), uw)
    assert sum(p for p, _ in atoms.values()) == 1
    events = {"X=1": ["x1"], "X=0": ["x0"]}
    for qv in grid:
        events["G%s" % qv] = [("best", qv), ("worst", qv)]
    def V(ev, at):
        tot = sum(at[a][0] for a in ev)
        return sum(at[a][0] * at[a][1] for a in ev) / tot
    VT = sum(p * u for p, u in atoms.values())
    c = F(1, 2)
    d = 1 - c * VT
    rot = {a: (p * (c * u + d), u / (c * u + d)) for a, (p, u) in atoms.items()}
    assert sum(p for p, _ in rot.values()) == 1 and all(p >= 0 for p, _ in rot.values())
    names = list(events)
    same_order = all((V(events[a], atoms) < V(events[b], atoms)) == (V(events[a], rot) < V(events[b], rot))
                     and (V(events[a], atoms) == V(events[b], atoms)) == (V(events[a], rot) == V(events[b], rot))
                     for a in names for b in names)
    # yardstick number of X=1: the grid gamble she is indifferent to
    yard = lambda at: [qv for qv in grid if V(events["G%s" % qv], at) == V(events["X=1"], at)]
    p_before, p_after = atoms["x1"][0], rot["x1"][0]
    chance_in_device = rot[("best", F(1, 2))][0] / (rot[("best", F(1, 2))][0] + rot[("worst", F(1, 2))][0])
    ok = same_order and yard(atoms) == yard(rot) == [F(4, 5)] and p_before != p_after and chance_in_device != F(1, 2)
    return ("holds" if ok else "FAILS",
            {"P(X=1)": (p_before, p_after), "yardstick number of X=1": yard(rot),
             "her rotated probability that a 1/2-chance device gives the best": chance_in_device})


def item3():
    A = [(F(1), F(3, 8))]
    B = [(F(1, 2), F(1, 5)), (F(1, 2), F(3, 5))]
    e = (sr.rate(A, "E"), sr.rate(B, "E"))
    b = (sr.rate(A, "bare"), sr.rate(B, "bare"))
    above = [(F(9, 10), F(3, 5)), (F(1, 10), F(1, 5))]
    # the sign of line 3 under an increasing rescaling: classes fixed, and classes recomputed
    raw = scene({"star": (F(4, 20), {"x": F(4, 5)}), "nu": (F(10, 20), {"x": F(1, 5)}),
                 "near": (F(12, 20), {"x": F(9, 10)}), "mid": (F(11, 20), {"x": F(1, 2)})}, "star", "nu")
    sq = lambda v: v * v
    raw2 = scene({"star": (sq(F(4, 20)), {"x": sq(F(4, 5))}), "nu": (sq(F(10, 20)), {"x": sq(F(1, 5))}),
                  "near": (sq(F(12, 20)), {"x": sq(F(9, 10))}), "mid": (sq(F(11, 20)), {"x": sq(F(1, 2))})}, "star", "nu")
    d = F(1, 10)
    before, after = l3(raw, d), l3(raw2, d)
    fixed_classes = sq(F(12, 20)) - sq(F(12, 20))     # with "near" kept in pi*'s class the difference stays 0
    raw0, raw02 = l3(raw, 0), l3(raw2, 0)
    ok = e[1] > e[0] and b[1] < b[0] and sr.rate(above, "bare") > sr.rate(above, "E") \
        and before == 0 and after > 0 and raw0 > 0 and raw02 > 0 and raw0 != raw02
    return ("holds, the rescaling leaving the classes alone" if ok else "FAILS",
            {"E ranks": e, "her ratings": b, "line 3 before and after squaring, classes recomputed at 1/10": (before, after),
             "at tolerance 0": (raw0, raw02), "a gamble she rates above its average": (sr.rate(above, "bare"), sr.rate(above, "E"))})


def item4():
    alpha, v = F(1, 2), F(3, 4)
    worth = lambda qv: F(1) if qv == 1 else alpha * qv
    grid = [F(k, 1000) for k in range(1001)]
    none = all(worth(qv) != v for qv in grid) and all(worth(qv) < v for qv in grid if qv < 1) and worth(F(1)) > v
    return ("holds" if none else "FAILS", {"the sure future": v, "the best a gamble short of certainty is worth": alpha})


def item5():
    rng = random.Random(20261117)
    worst_gap, n = None, 0
    for _ in range(400):
        names = ["nu", "star"] + ["p%d" % i for i in range(rng.randint(2, 5))]
        pol = {nm: (F(rng.randint(0, 20), 20), {"x": F(rng.randint(0, 20), 20), "y": F(rng.randint(0, 20), 20)}) for nm in names}
        raw = scene(pol, "star", "nu")
        for d in sr.DELTAS:
            a, t = l3(raw, d), tenth_l3(raw, d)
            if a < 0 or a < t:
                return "FAILS", {"scene": pol, "delta": d}
            n += 1
            worst_gap = a - t if worst_gap is None else min(worst_gap, a - t)
        same = dict(pol)
        raw = scene(same, "nu", "nu")
        if any(l3(raw, d) != 0 for d in sr.DELTAS):
            return "FAILS", {"scene": pol, "pi* = nu": True}
    return "holds", {"scenes x tolerances": n, "least excess over the tenth follow-up's line 3": worst_gap}


def item6():
    out = {}
    # a: an unwelcome change with separable help
    a = scene({"change_and_help": (F(9, 20), {"x": F(4, 20)}), "nothing": (F(10, 20), {"x": F(14, 20)}),
               "help_only": (F(15, 20), {"x": F(14, 20)}), "change_only": (F(4, 20), {"x": F(4, 20)})}, "change_and_help", "nothing")
    out["a"] = [l3(a, d) for d in (0, F(1, 20), F(1, 4), F(9, 20), F(1, 2))]
    # b: an unwelcome change with a separable welcome change
    b = scene({"both": (F(7, 20), {"x": F(16, 20), "y": F(4, 20)}), "nothing": (F(10, 20), {"x": F(10, 20), "y": F(14, 20)}),
               "welcome_only": (F(13, 20), {"x": F(16, 20), "y": F(14, 20)}), "unwelcome_only": (F(4, 20), {"x": F(10, 20), "y": F(4, 20)})}, "both", "nothing")
    out["b"] = [l3(b, d) for d in (0, F(1, 20), F(1, 4), F(9, 20), F(1, 2))]
    # c: twenty nudges of 1/40 each, as one rule and one at a time
    course = {"k%d" % k: (F(12, 20) - k * F(6, 400), {"x": F(1, 4) + k * F(1, 40)}) for k in range(21)}
    out["c rule"] = l3(scene(course, "k20", "k0"), F(1, 20))
    singles = []
    for k in range(20):
        one = {"stop": (F(12, 20), {"x": F(1, 4) + k * F(1, 40)}), "one_more": (F(12, 20) - F(6, 400), {"x": F(1, 4) + (k + 1) * F(1, 40)})}
        singles.append(l3(scene(one, "one_more", "stop"), F(1, 20)))
    out["c singles"] = (min(singles), max(singles))
    # d: a welcome change by an adviser that helps little
    dd = {"change": (F(13, 20), {"x": F(16, 20)}), "nothing": (F(10, 20), {"x": F(10, 20)}),
          "help_only": (F(18, 20), {"x": F(10, 20)}), "change_and_help": (F(1), {"x": F(16, 20)})}
    out["d combinable"] = l3(scene(dd, "change", "nothing"), F(1, 20))
    del dd["change_and_help"]
    out["d not combinable"] = l3(scene(dd, "change", "nothing"), F(1, 20))
    # e: more of a welcome change than she would like
    e = scene({"much": (F(11, 20), {"x": F(1)}), "nothing": (F(10, 20), {"x": F(1, 2)}), "some": (F(14, 20), {"x": F(3, 4)})}, "much", "nothing")
    out["e"] = l3(e, F(1, 20))
    ok = (out["a"] == [F(3, 10)] * 4 + [0] and out["b"] == [F(3, 10)] * 4 + [0] and out["c rule"] > 0
          and out["c singles"] == (0, 0) and out["d combinable"] == 0 and out["d not combinable"] == F(1, 4) and out["e"] == F(3, 20))
    return ("holds, the fourth with a stated hypothesis" if ok else "FAILS", out)


def item7():
    p = {"pair": (F(9, 20), {"x": F(10, 20)}), "nothing": (F(10, 20), {"x": F(10, 20)}),
         "welcome_alone": (F(15, 20), {"x": F(16, 20)}), "unwelcome_alone": (F(4, 20), {"x": F(4, 20)})}
    vals = [l3(scene(p, "pair", "nothing"), d) for d in sr.DELTAS[:3]]
    out_below = sr.compute(sr.Spec(scene(p, "pair", "nothing")), F(1, 20), "E")["verdict"]
    p["pair"] = (F(1, 20), {"x": F(10, 20)})
    worse = l3(scene(p, "pair", "nothing"), F(1, 20))
    p["pair"] = (F(10, 20), {"x": F(10, 20)})
    out_equal = sr.compute(sr.Spec(scene(p, "pair", "nothing")), F(1, 20), "E")["verdict"]
    ok = vals == [0, 0, 0] and worse == 0 and out_below == "another wrong outside (coercion)" and out_equal == "none"
    return ("holds" if ok else "FAILS", {"line 3 of the pair": vals, "with the pair rated 1/20": worse,
                                         "verdict with the pair rated below doing nothing": out_below, "rated the same": out_equal})


def item8():
    d = F(1, 10)
    pol = {"star": (F(0), {"x": F(16, 20)}), "nu": (F(0), {"x": F(10, 20)}), "nu2": (F(0), {"x": F(10, 20) - d}),
           "edge": (F(1), {"x": F(10, 20) - 2 * d})}
    a, b = l3(scene(pol, "star", "nu"), d), l3(scene(pol, "star", "nu2"), d)
    pol["edge"] = (F(1), {"x": F(10, 20) - 3 * d})
    c1, c2 = l3(scene(pol, "star", "nu"), d), l3(scene(pol, "star", "nu2"), d)
    ok = (a, b) == (0, 1) and c1 == c2
    return ("no bound without a condition on the policies" if ok else "FAILS", {"line 3 under the two baselines": (a, b), "with no policy near the edge": (c1, c2)})


def item9():
    # her valuing at moment k rates j further nudges at 12/20 - j*(6/400); judged as a rule and singly
    rule, single = [], []
    for k in range(20):
        left = 20 - k
        course = {"j%d" % j: (F(12, 20) - j * F(6, 400), {"x": F(1, 4) + (k + j) * F(1, 40)}) for j in range(left + 1)}
        rule.append(l3(scene(course, "j%d" % left, "j0"), F(1, 20)))
        one = {"j0": course["j0"], "j1": course["j1"]}
        single.append(l3(scene(one, "j1", "j0"), F(1, 20)))
    ok = rule[0] > 0 and max(single) == 0
    return ("holds" if ok else "FAILS", {"as a rule, at the first moment": rule[0], "moments flagged as a rule": sum(1 for x in rule if x > 0),
                                         "one nudge at a time": (min(single), max(single))})


def item10():
    # her later self as under nu rates what happens in the world; two policies with one world
    # outcome and different effects on her valuing score the same
    nu_self = {"outcome_a": F(15, 20), "outcome_b": F(14, 20)}
    world = {"A_changes_her": "outcome_a", "A_leaves_her": "outcome_a", "B": "outcome_b", "nothing": "outcome_b"}
    score = {p: nu_self[o] for p, o in world.items()}
    pol = {"A_changes_her": (F(8, 20), {"x": F(4, 20)}), "B": (F(14, 20), {"x": F(14, 20)}),
           "nothing": (F(14, 20), {"x": F(14, 20)}), "A_leaves_her": (F(15, 20), {"x": F(14, 20)})}
    same = score["A_changes_her"] == score["A_leaves_her"]
    # where A can be had only with the change, the scored adviser takes it
    del pol["A_leaves_her"]
    best = max((p for p in pol), key=lambda p: score[p])
    val = l3(scene(pol, best, "nothing"), F(1, 20))
    ok = same and best == "A_changes_her" and val == F(3, 10)
    return ("holds" if ok else "FAILS", {"scores": (score["A_changes_her"], score["A_leaves_her"]), "the scored adviser takes": best, "line 3": val})


def item11():
    # (i) a foreseen chain: three requests, each rated a step up by the self that makes it,
    # the end rated below staying by the first self.  Her rating of the first request as
    # things stand, if it is what her observations support, is her rating of the end.
    stay, end = F(12, 20), F(6, 20)
    foreseen = {"id": "x", "states": {"w": "1"}, "options": ["ask", "stay"],
                "futures": {"end_of_chain": str(end), "stayed": str(stay)},
                "policies": {n: {"does": n, "outcome": {"*": {"ask": "end_of_chain", "stay": "stayed"}},
                                 "r": "Rs", "takes": "top", "later": {"*": [{"x": "1/2"}]}, "gain": "0"} for n in "abcd"},
                "actual": "a", "nu": "a", "absent": "a", "fixed": [], "order": []}
    S = sr.Spec(foreseen)
    takes_foreseen = S.takes("a", "o", "E")
    myopic = dict(foreseen)
    myopic["policies"] = {n: dict(p, r={"o": {"ask": T(13), "stay": T(12)}}) for n, p in foreseen["policies"].items()}
    m = sr.compute(sr.Spec(myopic), F(0), "E")
    # (ii) with chance: nine in ten like her stop after one step, one in ten go on to the end
    chance = dict(foreseen, states={"stops": "9/10", "goes_on": "1/10"},
                  futures={"one_step": T(14), "end_of_chain": T(2), "stayed": T(12)})
    chance["policies"] = {n: dict(p, outcome={"stops": {"ask": "one_step", "stay": "stayed"}, "goes_on": {"ask": "end_of_chain", "stay": "stayed"}})
                          for n, p in foreseen["policies"].items()}
    out = {}
    for setting in sr.SETTINGS:
        Sc = sr.Spec(chance)
        c = sr.compute(Sc, F(0), setting)
        out[setting] = (Sc.takes("a", "o", setting), c["l1"], c["l2"], Sc.Rs("a", "o", "ask", setting))
    # the second moment, in the state where she goes on: her valuing has changed, she asks for
    # the next step rating it rightly, and the adviser does as asked, which is now the baseline
    second = {"id": "x", "states": {"w": "1"}, "options": ["ask_again", "stop"],
              "futures": {"went_on": T(15), "stopped_here": T(10)},
              "policies": {n: {"does": n, "outcome": {"*": {"ask_again": "went_on", "stop": "stopped_here"}},
                               "r": "Rs", "takes": "top", "later": {"*": [{"x": lat}]}, "gain": "0"}
                           for n, lat in (("as_asked", "1/5"), ("refuse", "1/2"), ("half", "7/20"), ("delay", "1/5"))},
              "actual": "as_asked", "nu": "as_asked", "absent": "refuse", "fixed": [], "order": []}
    s2 = sr.compute(sr.Spec(second), F(0), "E")
    out["second moment (line 1, line 2, line 3, verdict)"] = (s2["l1"], s2["l2"], s2["l3"], s2["verdict"])
    ok = takes_foreseen == "stay" and m["l1"] == F(49, 400) and out["E"][0] == "ask" and out["E"][1:3] == (0, 0) \
        and (s2["l1"], s2["l2"], s2["l3"], s2["verdict"]) == (0, 0, 0, "none")
    return ("no instance for a foreseen chain; an instance where chance is involved" if ok else "FAILS",
            {"foreseen, she": takes_foreseen, "asking while rating only the next step: line 1": m["l1"],
             "with chance (takes, line 1, line 2, R^s of asking)": out})


def _listener(policies, actual):
    pols = {}
    for name, (obs, r, gain) in policies.items():
        pols[name] = {"does": name,
                      "outcome": {"good": {"act": "acted_good", "pass": "passed"}, "bad": {"act": "acted_bad", "pass": "passed"}},
                      "obs": obs, "r": r, "takes": "top", "later": {"*": [{"x": "1/2"}]}, "gain": gain}
    return {"id": "x", "states": {"good": "1/2", "bad": "1/2"}, "options": ["act", "pass"],
            "futures": {"acted_good": T(16), "acted_bad": T(4), "passed": T(11)},
            "policies": pols, "actual": actual, "nu": "silence", "absent": "silence", "fixed": [], "order": []}


def item12():
    told = {"good": "told_good", "bad": "told_bad"}
    welfare = {"good": {"act": "16/20", "pass": "11/20"}, "bad": {"act": "4/20", "pass": "11/20"}}
    under = {"told_good": {"act": T(13), "pass": T(11)}, "told_bad": {"act": T(7), "pass": T(11)}}
    honest = _listener({"tell": (told, under, welfare), "silence": ({}, "Rs", welfare),
                        "tell_once": (told, "Rs", welfare), "tell_twice": (told, "Rs", welfare)}, "tell")
    h = sr.compute(sr.Spec(honest), F(0), "E")
    sale = {"*": {"act": "1", "pass": "0"}}
    slant = _listener({"slant": ({}, {"o": {"act": T(14), "pass": T(11)}}, sale), "silence": ({}, "Rs", sale),
                       "honest": (told, "Rs", sale), "honest_twice": (told, "Rs", sale)}, "slant")
    s = sr.compute(sr.Spec(slant), F(0), "E")
    fee = {"*": {"act": "3/2", "pass": "1"}}
    script = _listener({"script": ({}, {"o": {"act": T(14), "pass": T(11)}}, fee), "silence": ({}, "Rs", sale),
                        "honest": (told, "Rs", sale), "honest_twice": (told, "Rs", sale)}, "script")
    sc = sr.compute(sr.Spec(script), F(0), "E")
    # a shop that says nothing false to a customer who overrates the product whoever sells it
    over = {"o": {"act": T(14), "pass": T(11)}}
    none = {"*": {"act": "0", "pass": "0"}}
    shop = _listener({"open": ({}, over, sale), "silence": ({}, over, none),
                      "close_early": ({}, over, none), "refer_elsewhere": ({}, over, none)}, "open")
    sh = sr.compute(sr.Spec(shop), F(0), "E")
    ok = (h["l1"] > h["l1_absent"] and not h["induced"] and s["induced"] and sc["mistake"] and not sc["induced"]
          and sh["induced"] and sh["l1"] == sh["l1_absent"])
    return ("holds; the test is wrong on two instances" if ok else "FAILS",
            {"honest, under-used: line 1 under telling and under silence, induced": (h["l1"], h["l1_absent"], h["induced"]),
             "slant: induced": s["induced"], "paid script: line 1, G, G unmistaken, induced": (sc["l1"], sc["G"], sc["G0"], sc["induced"]),
             "shop: line 1 open and absent, induced": (sh["l1"], sh["l1_absent"], sh["induced"])})


ITEMS = (item1, item2, item3, item4, item5, item6, item7, item8, item9, item10, item11, item12)


def run_all():
    return {str(i + 1): f() for i, f in enumerate(ITEMS)}


def report():
    computed = run_all()
    text = (HERE / "STATEMENT_CHECKS.md").read_text(encoding="utf-8") if (HERE / "STATEMENT_CHECKS.md").exists() else ""
    stated = dict(re.findall(r"^\| (\d+) \| (.*?) \|$", text, re.M))
    failures = []
    if len(stated) != len(ITEMS):
        failures.append("STATEMENT_CHECKS.md states %d items, the checks cover %d" % (len(stated), len(ITEMS)))
    for k, (status, _) in computed.items():
        if status == "FAILS":
            failures.append("item %s: the instance does not compute as written" % k)
        elif stated.get(k) != status:
            failures.append("item %s: STATEMENT_CHECKS.md says %r, computed %r" % (k, stated.get(k), status))
    return {"summary": ["item %s: %s" % (k, s) for k, (s, _) in computed.items()], "failures": failures}


if __name__ == "__main__":
    import sys
    for k, (status, detail) in run_all().items():
        print("item %s: %s" % (k, status))
        for a, b in detail.items():
            print("    %s: %s" % (a, b))
    rep = report()
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    sys.exit(1 if rep["failures"] else 0)
