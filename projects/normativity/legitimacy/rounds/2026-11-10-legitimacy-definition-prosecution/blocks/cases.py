"""The cases of CASE_BANK.md as scenes.  Each function returns (tokens, facts); `scene_*`
functions return the Scene so that results.py can reuse it."""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction as F

from .model import (NULL, Act, Part, Scene, best_on_menu, choice, classify, condition, fit, gap, opposition,
                    optval, rest, total, whole_gaps)

H2 = F(1, 2)


def is_h(theta, act=None):
    return F(1 if theta == "H" else 0)


def believer(on_null=H2, on_h=F(1)):
    def mech(theta, act, moves):
        return {None: on_null, "H": on_h, "L": F(0)}[act.signal]
    return mech


def listen(mech, target=is_h):
    return Part("listen", "estimate", mech, target=target)


# ---- belief ------------------------------------------------------------------------------

def scene_1(with_act=False):
    parts = [listen(believer())]
    if with_act:
        parts.append(Part("act", "choice", lambda th, a, mv: "treat" if mv["listen"] > H2 else "skip",
                          moves=("treat", "skip"), util=lambda th, a, m, mv: 1 if m == "treat" else 0))
    return Scene([("H", H2), ("L", H2)], parts, rule=lambda k: Act("H"), actions=(Act("H"), Act("L"), NULL))


def scene_3():
    table = {"eH": F(1), "eL": F(0), "hH": F(3, 4), "hL": F(3, 4), None: H2}
    return Scene([("eH", F(3, 8)), ("eL", F(3, 8)), ("hH", F(3, 16)), ("hL", F(1, 16))],
                 [listen(lambda th, a, mv: table[a.signal], target=lambda th, a: F(1 if th.endswith("H") else 0))],
                 rule=lambda k: Act(k), actions=tuple(Act(s) for s in ("eH", "eL", "hH", "hL")) + (NULL,))


def scene_4(on_h=F(1)):
    return Scene([("H", H2), ("L", F(9, 20)), ("T", F(1, 20))], [listen(believer(on_h=on_h))],
                 rule=lambda k: Act("H" if k in ("H", "T") else "L"), actions=(Act("H"), Act("L"), NULL))


def two_valued(on_null):
    return Part("listen", "choice", lambda th, a, mv: {None: on_null, "H": "bH", "L": "bL"}[a.signal],
                moves=("bH", "bL"), util=lambda th, a, m, mv: 1 if (m == "bH") == (th == "H") else 0)


def scene_4b():
    s = scene_4()
    return replace(s, parts=[two_valued("bH")])


def scene_4c():
    states = [((t, q), F(1, 4) * pr) for t in (1, 2, 3, 4) for q, pr in (("H", F(2, 5)), ("L", F(3, 5)))]
    part = Part("listen", "choice", lambda th, a, mv: {None: "bL", "H": "bH", "L": "bL"}[a.signal],
                moves=("bH", "bL"), util=lambda th, a, m, mv: 1 if (m == "bH") == (th[1] == "H") else 0)
    return Scene(states, [part], rule=lambda k: Act(k[1] if k[0] < 4 else "H"), grain=lambda th: th[0],
                 actions=(Act("H"), Act("L"), NULL))


def scene_env(p_right):
    """No adviser: a signal built into the state, naming it with probability p_right."""
    states = [((q, s), H2 * (p_right if s == q else 1 - p_right)) for q in "HL" for s in "HL"]
    return Scene(states, [listen(lambda th, a, mv: F(1 if th[1] == "H" else 0), target=lambda th, a: is_h(th[0]))])


def scene_7(shown="clear"):
    def mech(th, a, mv):
        return is_h(th) if a.signal in ("clear", "front") else H2
    return Scene([("H", H2), ("L", H2)], [listen(mech)], rule=lambda k: Act(shown),
                 actions=(Act("clear"), Act("subtle"), NULL) if shown == "clear" else (Act("front"), Act("appendix"), NULL))


def scene_8(on_item=F(2, 3)):
    def mech(th, a, mv):
        if a.signal == "truth":
            return is_h(th)
        return on_item if a.signal == "item" else F(0)
    return Scene([("H", H2), ("Lf", F(1, 4)), ("Ln", F(1, 4))], [listen(mech)],
                 rule=lambda k: Act("item") if k in ("H", "Lf") else NULL, actions=(Act("truth"), Act("item"), NULL))


def scene_25():
    states = [((q, r), H2 * (F(3, 4) if r == q else F(1, 4))) for q in "HL" for r in "HL"]
    return Scene(states, [listen(believer(), target=lambda th, a: is_h(th[0]))], know=lambda th: th[1],
                 rule=lambda k: Act(k), actions=(Act("H"), Act("L"), NULL))


def scene_27(on_hard=F(3, 4)):
    states = [(("H", "c"), H2), (("H", "n"), F(1, 4)), (("L", "c"), F(1, 6)), (("L", "n"), F(1, 12))]

    def mech(th, a, mv):
        if a.signal is None:
            return is_h(th[0]) if th[1] == "c" else F(3, 4)
        return on_hard
    return Scene(states, [listen(mech, target=lambda th, a: is_h(th[0]))], know=lambda th: th[0],
                 rule=lambda k: Act("hard-" + k), actions=(Act("hard-H"), Act("hard-L"), NULL))


def scene_30():
    acc = F(3, 4)
    states = [((q, s1, s2), H2 * (acc if s1 == q else 1 - acc) * (acc if s2 == q else 1 - acc))
              for q in "HL" for s1 in "HL" for s2 in "HL"]
    parts = [Part("listen%d" % i, "estimate", (lambda i: lambda th, a, mv: acc if th[i] == "H" else 1 - acc)(i),
                  target=lambda th, a: is_h(th[0])) for i in (1, 2)]
    return Scene(states, parts)


# ---- options -----------------------------------------------------------------------------

def payoff(th, a, m, mv):
    if a.conseq == "threat" and m == "refuse":
        return -1
    if a.conseq == "offer" and m == "comply":
        return 2
    return {"comply": 0, "refuse": 1}[m]


def scene_10(act=Act(conseq="threat")):
    part = Part("act", "choice", lambda th, a, mv: max(("comply", "refuse"), key=lambda m: payoff(th, a, m, mv)),
                moves=("comply", "refuse"), util=payoff)
    return Scene([("w", F(1))], [part], rule=lambda k: act)


def scene_11b():
    danger = lambda th, a=None: F(1 if th == "danger" else 0)
    part_l = listen(lambda th, a, mv: {None: H2, "danger": F(1), "safe": F(0)}[a.signal], target=danger)
    part_a = Part("act", "choice", lambda th, a, mv: "comply" if mv["listen"] > H2 else "refuse",
                  moves=("comply", "refuse"),
                  util=lambda th, a, m, mv: 0 if m == "comply" else (-1 if th == "danger" else 1))
    return Scene([("danger", F(1, 4)), ("safe", F(3, 4))], [part_l, part_a], rule=lambda k: Act(k))


def scene_14():
    part = Part("act", "choice", lambda th, a, mv: "y" if a.signal == "y-first" else "x", moves=("x", "y"),
                util=lambda th, a, m, mv: 1)
    aims = {"x": lambda k: Act("x-first"), "y": lambda k: Act("y-first")}
    return Scene([("w", F(1))], [part], rule=aims["x"], aims=aims)


def scene_28():
    nourishing = lambda th, a=None: F(1 if th == "N" else 0)
    crave = Part("crave", "choice", lambda th, a, mv: "take" if th == "N" or (a.signal and a.signal[0]) else "leave",
                 moves=("take", "leave"),
                 util=lambda th, a, m, mv: 0 if m == "leave" else (1 if th == "N" else -1))
    hear = listen(lambda th, a, mv: H2 if a.signal is None else F(1 if a.signal[1] == "N" else 0), target=nourishing)
    return Scene([("N", F(1, 4)), ("E", F(3, 4))], [hear, crave], rule=lambda k: Act((k == "E", k)))


# ---- ends --------------------------------------------------------------------------------

OTHER = {"s": 1, "g": 2, "b": 0}
TASTES = {"keep": {"s": 2}, "like-g": {"g": 3}, "like-b": {"b": 3}}


def scene_15(arranged_from=None, steps=1, adviser=True):
    """States (step, what is around).  The adviser exposes her to b where b is around, from step
    `arranged_from` on (None: at every step)."""
    states = [((t, w), F(1, steps) * pr) for t in range(1, steps + 1) for w, pr in (("G", F(1, 4)), ("B", F(3, 4)))]

    def X(th):
        return ["s", "g"] if th[1] == "G" else ["s", "b"]

    def mech(th, a, mv):
        if th[1] == "G":
            return "like-g"
        return "like-b" if a.signal == "expose-b" else "keep"

    def util(th, a, m, mv):
        return fit("taste", TASTES[m], {"other": OTHER, "taste": TASTES["keep"]}, X(th))

    def rule(k):
        rigged = k[1] == "B" and (arranged_from is None or k[0] >= arranged_from)
        return Act("expose-b") if rigged else NULL
    part = Part("revise", "choice", mech, moves=tuple(TASTES), util=util)
    return Scene(states, [part], rule=rule if adviser else None, grain=lambda th: th[0])


LAW = {"career": {"law": 2}, "joy": {"music": 1}, "friends": {"music": 1}, "income": {"law": 1, "music": H2}}
LAW_MENU = {"keep": {"law": 2}, "music": {"music": 2}}


def verdict_pairs(ends0, endsT, outcomes, W):
    """[(probability, V_0, V_T)] for her verdict on the final outcome, the verdict part in range."""
    return [(pr, total(ends0, x) / W, total(endsT, x) / W) for x, pr in outcomes]


def change_tokens(legit):
    return {"change: legitimate" if legit else "change: illegitimate"}


def scene_17():
    X = ["law", "music"]
    part = Part("revise", "choice", lambda th, a, mv: "music", moves=tuple(LAW_MENU),
                util=lambda th, a, m, mv: fit("career", LAW_MENU[m], LAW, X))
    return Scene([("w", F(1))], [part])


def case_17():
    X = ["law", "music"]
    tokens, facts = classify(scene_17())
    top, scores = best_on_menu("career", LAW_MENU, LAW, X)
    after = {**LAW, "career": LAW_MENU["music"]}
    x0, xT = choice(LAW, X), choice(after, X)
    shift, g0, gT = whole_gaps(verdict_pairs(LAW, after, [(xT, F(1))], F(9, 2)))
    if "in-range" in tokens and "music" in top:
        tokens.add("change: legitimate")
    facts.update({"fit on the menu": scores, "choice before": x0, "choice after": xT, "verdict shift": shift,
                  "g_0": g0, "g_T": gT})
    return tokens, facts


def case_18():
    states = [(F(1), H2), (H2, H2)]
    menu = {"depressed": lambda th, a, mv: th / 2, "sound": lambda th, a, mv: th}

    def scene(name):
        return Scene(states, [Part("verdict", "estimate", menu[name], target=lambda th, a: th)])
    scores = {}
    for name in menu:
        s = scene(name)
        C = condition(s)
        scores[name] = (gap(s, s.parts[0], C), sum(pr * s.parts[0].u(th, a, mv["verdict"], mv) for th, pr, a, mv in C))
    shift, g0, gT = whole_gaps([(pr, th / 2, th) for th, pr in states])
    tokens = {"not adviser's"} | change_tokens(scores["sound"][1] == max(v[1] for v in scores.values()))
    if shift != 0:
        tokens.add("shift")
    if g0 > 0 and gT > 0:
        tokens.add("whole-gap")
    return tokens, {"gap before": scores["depressed"][0], "gap after": scores["sound"][0], "verdict shift": shift,
                    "g_0": g0, "g_T": gT, "shift² ≤ min(g_0, g_T)": shift ** 2 <= min(g0, gT)}


def case_19():
    X = ["x", "y"]
    ends = {"A": {"x": 2}, "B": {"y": 1}, "C": {"y": 1}, "D": {"y": 1}}
    top, scores = best_on_menu("A", {"keep": {"x": 2}, "new": {"y": 2}}, ends, X)
    return {"not adviser's"} | change_tokens("new" in top), {"fit on the menu": scores}


CONV = {"A": {"x": 1}, "B": {"x": 1}, "C": {"x": 1}, "D": {"x": 2}}


def case_20():
    X = ["x", "z"]
    changed = ("A", "B", "C")
    after = {**CONV, **{j: {"z": 1} for j in changed}}
    legit, scores = True, {}
    for j in changed:
        top, sc = best_on_menu(j, {"keep": {"x": 1}, "new": {"z": 1}}, after, X, changed=changed)
        scores[j] = sc
        legit = legit and "new" in top
    # afterwards: revising D, judged by the rest as it then is
    top_d, sc_d = best_on_menu("D", {"keep": {"x": 2}, "new": {"z": 1}}, after, X)
    return ({"not adviser's"} | change_tokens(legit),
            {"fit on the menu, each replaced end": scores, "choice after": choice(after, X),
             "afterwards, fit of revising D": sc_d, "afterwards, greatest fit for D": top_d})


def scene_22():
    asker = Part("act", "choice", lambda th, a, mv: "ask", moves=("ask", "not"), util=lambda th, a, m, mv: 3)
    end_a = Part("A", "choice", lambda th, a, mv: "x2", moves=("x2", "y2"), util=lambda th, a, m, mv: 0,
                 installs={"y2": lambda th, a, mv: "y2"})
    return Scene([("w", F(1))], [asker, end_a], rule=lambda k: Act(alter=(("A", "y2"),)),
                 requests=lambda mv: {("alteration", "A")} if mv["act"] == "ask" else set(), requester="act")


def case_23():
    taste = Part("taste", "choice", lambda th, a, mv: "s2", moves=("s2", "liking"), util=lambda th, a, m, mv: 0,
                 installs={"liking": lambda th, a, mv: "liking"})
    s = Scene([("y1", H2), ("y2", H2)], [taste], rule=lambda k: Act(alter=(("taste", "liking"),)))
    tokens, facts = classify(s)
    other = {"s": 1, "y1": 1, "y2": H2}
    pairs = []
    for y, pr in s.states:
        before, after = {"taste": {"s": 2}, "other": other}, {"taste": {y: 3}, "other": other}
        assert choice(after, ["s", y]) == y and choice(before, ["s", y]) == "s"
        pairs.append((pr, total(before, y) / 4, total(after, y) / 4))
    shift, g0, gT = whole_gaps(pairs)
    if shift != 0 and shift ** 2 <= min(g0, gT):
        tokens.add("bound")
    facts.update({"verdict shift": shift, "g_0": g0, "g_T": gT})
    return tokens, facts


def ends_tokens(ends, X):
    """Ends with *act*, which takes her choice and is for the outcome's value by her ends."""
    act = Part("act", "choice", lambda th, a, mv: choice(ends, X), moves=tuple(X),
               util=lambda th, a, m, mv: total(ends, m))
    tokens, facts = classify(Scene([("w", F(1))], [act]))
    opp = {j: opposition(v, rest(ends, (j,)), X) for j, v in ends.items()}
    tokens.add("fits" if all(o == 0 for o in opp.values()) else "opposition")
    facts.update({"choice": choice(ends, X), "opposition": opp})
    return tokens, facts


HIJACK = {"A": {"w": 3, "x": 2}, "B": {"x": 3}, "C": {"z": 1}}
HIJACK_X = ["x", "z", "w"]
HIJACK_STEPS = (("A", {"keep": {"w": 3, "x": 2}, "drop": {}}, "drop"), ("B", {"keep": {"x": 3}, "new": {"z": 1}}, "new"))


def run_chain(ends, X, steps, **kw):
    """Apply each (end, menu, taken) in turn; report each step's fit and whether the move taken
    is the menu's one best."""
    log, ends = [], dict(ends)
    for j, menu, taken in steps:
        top, scores = best_on_menu(j, menu, ends, X, **kw)
        log.append({"end": j, "fit": scores, "greatest": top, "taken": taken, "choice before": choice(ends, X)})
        ends[j] = menu[taken]
    return ends, log


def scene_29():
    """The chain as a scene: the adviser's signal gives each revising part its occasion in turn; a
    revising part with no occasion keeps.  Each is scored by fit against her ends as they then are."""
    (ja, menu_a, taken_a), (jb, menu_b, taken_b) = HIJACK_STEPS

    def after_a(mv):
        return {**HIJACK, ja: menu_a[mv["revise-A"]]}
    part_a = Part("revise-A", "choice", lambda th, a, mv: taken_a if a.signal else "keep", moves=tuple(menu_a),
                  util=lambda th, a, m, mv: fit(ja, menu_a[m], HIJACK, HIJACK_X))
    part_b = Part("revise-B", "choice", lambda th, a, mv: taken_b if a.signal else "keep", moves=tuple(menu_b),
                  util=lambda th, a, m, mv: fit(jb, menu_b[m], after_a(mv), HIJACK_X))
    return Scene([("w", F(1))], [part_a, part_b], rule=lambda k: Act("A's occasion, then B's"))


def case_29():
    tokens, facts = classify(scene_29())
    ends, log = run_chain(HIJACK, HIJACK_X, HIJACK_STEPS)
    final = choice(ends, HIJACK_X)
    if final == min(HIJACK_X, key=lambda x: total(HIJACK, x)):
        tokens.add("worst-by-start")
    facts.update({"steps": log, "final choice": final, "starting totals": {x: total(HIJACK, x) for x in HIJACK_X}})
    return tokens, facts


def case_30():
    s = scene_30()
    tokens, facts = classify(s)
    C = condition(s)
    whole = Part("whole", "estimate", lambda th, a, mv: max(mv["listen1"], mv["listen2"]), target=lambda th, a: is_h(th[0]))
    s2 = replace(s, parts=s.parts + [whole])
    C2 = condition(s2)
    g = gap(s2, whole, C2)
    if g > 0:
        tokens.add("whole-out")
    facts["whole"] = {"gap": g, "mean verdict": sum(pr * mv["whole"] for _, pr, _, mv in C2), "mean target": H2}
    return tokens, facts


def case_33(standing):
    """The threat of case 10 where the consequence is the adviser's own later act.  Under the
    second null (the adviser's rule with the announcement nulled) the consequence without the
    announcement is the same act when the practice is standing, and nothing when it is not."""
    s = scene_10()
    tokens, facts = classify(s)
    C = condition(s)
    part = s.parts[0]
    silent = "threat" if standing else None
    o = optval(s, part, C)
    o_second = sum(max(pr * part.u(th, replace(a, conseq=silent), m, mv) for m in part.moves) for th, pr, a, mv in C)
    facts["act"]["most obtainable, the adviser's rule with no announcement"] = o_second
    facts["harm under the second null"] = o < o_second
    return tokens, facts


def plain(scene):
    return lambda: classify(scene())


def with_change(scene):
    def run():
        tokens, facts = classify(scene())
        if "in-range" in tokens and not any(t.startswith("force") for t in tokens):
            tokens.add("change: legitimate")
        return tokens, facts
    return run


SCENES = {
    "1": scene_1,
    "2": lambda: scene_1(with_act=True),
    "3": scene_3,
    "4": scene_4,
    "5": lambda: scene_env(H2),
    "6": lambda: scene_env(F(1, 4)),
    "7": scene_7,
    "8": scene_8,
    "9": lambda: scene_8(on_item=F(1)),
    "10": scene_10,
    "11a": lambda: scene_10(Act(conseq="offer")),
    "11b": scene_11b,
    "12": lambda: scene_10(Act(force=(("act", "comply"),))),
    "13": lambda: scene_7("appendix"),
    "14": scene_14,
    "15": scene_15,
    "21": lambda: scene_15(arranged_from=2, steps=3),
    "22": scene_22,
    "25": scene_25,
    "27": scene_27,
    "28": scene_28,
    "4b": scene_4b,
    "4c": scene_4c,
    "27b": lambda: scene_27(on_hard=F(1, 4)),
    "31": lambda: scene_4(on_h=F(10, 11)),
}

CASES = {
    "1": plain(SCENES["1"]),
    "2": plain(SCENES["2"]),
    "3": plain(SCENES["3"]),
    "4": plain(SCENES["4"]),
    "5": plain(SCENES["5"]),
    "6": plain(SCENES["6"]),
    "7": plain(SCENES["7"]),
    "8": plain(SCENES["8"]),
    "9": plain(SCENES["9"]),
    "10": plain(SCENES["10"]),
    "11a": plain(SCENES["11a"]),
    "11b": plain(SCENES["11b"]),
    "12": plain(SCENES["12"]),
    "13": plain(SCENES["13"]),
    "14": plain(SCENES["14"]),
    "15": plain(SCENES["15"]),
    "16": with_change(lambda: scene_15(adviser=False)),
    "17": case_17,
    "18": case_18,
    "19": case_19,
    "20": case_20,
    "21": plain(SCENES["21"]),
    "22": plain(SCENES["22"]),
    "23": case_23,
    "24": lambda: ends_tokens({"A": {"c": 1}, "B": {"c": 1}, "C": {"c": 1}}, ["c", "o"]),
    "25": plain(SCENES["25"]),
    "26": lambda: ends_tokens({"A": {"x": 5}, "B": {"y": 1}, "C": {"y": 1}}, ["x", "y"]),
    "27": plain(SCENES["27"]),
    "28": plain(SCENES["28"]),
    "4b": plain(SCENES["4b"]),
    "4c": plain(SCENES["4c"]),
    "27b": plain(SCENES["27b"]),
    "29": case_29,
    "30": case_30,
    "31": plain(SCENES["31"]),
    "33a": lambda: case_33(False),
    "33b": lambda: case_33(True),
}
