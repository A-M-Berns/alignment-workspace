"""The 108 cases of estimates/CASE_BANK.md as scenes of rerun/model.py: the sixth follow-up's
scene for each (estimates/cases.py) with the details of PREDICTIONS.md added.  Then the
review's four honest scenes (R) and the new scenes (W)."""
from __future__ import annotations

from fractions import Fraction as F

from .model import Scene, const

H2 = {"H": F(1, 2), "L": F(1, 2)}
BEL = {"H": 1, "L": 0}


def xval(s):
    return F(1) if str(s)[0] == "H" else F(0)


def same(s):
    return s


def flip(s):
    return "L" if s == "H" else "H"


def tell(prior, says, resp, alts=None, X=None, kind="belief", before=None, **kw):
    """She estimates one quantity X from what the adviser says.  `resp`: signal -> estimate
    (dict, or callable (type, signal)).  With no act her estimate is `before` (default: the
    prior mean)."""
    f = lambda d: (d if callable(d) else (lambda s, d=d: d[s]))
    X = X or (lambda q, s, act: xval(s))
    pols = {"actual": f(says)}
    for name, d in (alts or {}).items():
        pols[name] = const(None) if d is None else f(d)
    b = sum((p * X("X", s, None) for s, p in prior.items()), F(0)) if before is None else F(before)
    r = resp if callable(resp) else (lambda t, o: resp[o])
    return Scene(prior, pols, lambda t, o: {"e": {"X": b if o is None else r(t, o)}}, Y=X, kinds={"X": kind}, **kw)


def plain(**kw):
    return tell(H2, same, BEL, alts={"none": None}, **kw)


def nobody():
    return Scene({"s": 1}, {"actual": const(None)}, lambda t, o: {}, adviser=False)


def k30():
    prior = {}
    for x in (0, 1):
        for s1 in (0, 1):
            for s2 in (0, 1):
                prior[("H" if x else "L", s1, s2)] = F(1, 2) * (F(3, 4) if s1 == x else F(1, 4)) * (F(3, 4) if s2 == x else F(1, 4))
    e = lambda b: F(3, 4) if b else F(1, 4)
    return Scene(prior, {"actual": lambda s: (s[1], s[2])}, lambda t, o: {"e": {"X": F(1, 2) if o is None else max(e(o[0]), e(o[1]))}},
                 Y=lambda q, s, act: xval(s[0]), adviser=False)


def scalar(value, actual, before, alts=None, kind="belief", **kw):
    """One state, one quantity of true value `value`; her estimate under each conduct."""
    table = {"a": F(actual)}
    pols = {"actual": const("a")}
    for name, est in (alts or {}).items():
        pols[name] = const(None) if est is None else const(name)
        if est is not None:
            table[name] = F(est)
    return Scene({"s": 1}, pols, lambda t, o: {"e": {"X": F(before) if o is None else table[o]}},
                 Y=lambda q, s, act: F(value), kinds={"X": kind}, **kw)


def press(kind, twin="none", adviser=True, takes=("comply", "refuse")):
    """Comply or refuse.  Complying costs 1.  Pressure is a cost 1/4 on refusing ('cost') or a
    benefit 1/4 on complying ('gain').  Her estimates are right; under pressure she complies."""
    def U(a, s, act, cand):
        if a == "comply":
            return F(-1) + (F(1, 4) if (act == "press" and kind == "gain") else 0)
        return F(-1, 4) if (act == "press" and kind == "cost") else F(0)

    def respond(t, o):
        return {"u": {a: U(a, None, o, None) for a in takes}, "c": "comply" if o == "press" else "refuse"}
    return Scene({"s": 1}, {"actual": const("press"), "none": const(None)}, respond, U=U, twin=twin, adviser=adviser)


def craving(twin="none", types=None, actual_type=None):
    """A cue; she takes what her own estimate puts below leaving.  An ordinary advisee leaves."""
    def respond(t, o):
        return {"u": {"take": F(-1), "leave": F(0)}, "c": "take" if (o == "cue" and t != "ordinary") else "leave"}
    return Scene({"s": 1}, {"actual": const("cue"), "none": const(None)}, respond,
                 U=lambda a, s, act, cand: F(-1) if a == "take" else F(0), twin=twin, types=types, actual_type=actual_type)


def taste(endorsed, learn=False, adviser=True, twin=None, flags=(), steps=None):
    """Her rating of what she ends with is shaped from 0 to 1.  Unshaped it is worth 0.  Shaped,
    it is worth: by her starting values 1 if they endorse the trajectory, else 0; by her values
    at the end 1; by her starting values as changed by learning alone 1 if the shaping is
    annotated as learning, else 0."""
    def U(a, s, act, cand):
        if act != "shape":
            return F(0)
        if cand == "end":
            return F(1)
        return F(1) if (learn if cand == "learning" else endorsed) else F(0)
    prior = {"s": 1} if steps is None else {k: F(1, len(steps)) for k in steps}
    actual = const("shape") if steps is None else (lambda s: steps[s])
    fl = set(flags) | ({"own_unfixed"} if endorsed is None else set())
    return Scene(prior, {"actual": actual, "none": const(None)}, lambda t, o: {"u": {"h": F(1) if o == "shape" else F(0)}},
                 U=U, twin=twin, flags=fl, adviser=adviser)


def consequence(act, U, flags=()):
    """One state; her estimates are right and she takes the best move (or her move is set)."""
    def respond(t, o):
        u = {a: U(a, "s", o, None) for a in ("comply", "refuse")}
        return {"u": u, "c": None if "forced" in flags else max(u, key=lambda a: u[a])}
    return Scene({"s": 1}, {"actual": const(act), "none": const(None)}, respond, U=U, flags=flags)


def threat(a, s, act, cand):
    return F(0) if a == "comply" else (F(-1) if act == "threat" else F(1))


def offer(a, s, act, cand):
    return (F(2) if act == "offer" else F(0)) if a == "comply" else F(1)


def still(flags=()):
    """No estimate moves; the two moves are equal to her."""
    return Scene({"s": 1}, {"actual": const("act")}, lambda t, o: {"u": {"x": F(1), "y": F(1)}},
                 U=lambda a, s, act, cand: F(1), flags=flags)


def k2(explain=False):
    def respond(t, o):
        if o is None or o == "tell":
            return {"e": {"X": F(1, 2)}, "u": {"treat": F(1, 2), "skip": F(0)}, "c": "treat"}
        if isinstance(o, tuple):                       # the news, and that treatment pays either way
            return {"e": {"X": xval(o[1])}, "u": {"treat": F(1), "skip": F(0)}, "c": "treat"}
        x = xval(o)
        return {"e": {"X": x}, "u": {"treat": x, "skip": F(0)}, "c": "treat" if x > F(1, 2) else "skip"}
    pols = {"actual": const("H"), "truthful": same, "none": const(None), "tell": const("tell")}
    if explain:
        pols["explain"] = lambda s: ("explain", s)
    return Scene(H2, pols, respond, Y=lambda q, s, act: xval(s), U=lambda a, s, act, cand: F(1) if a == "treat" else F(0),
                 twin="truthful")


def k11b():
    def respond(t, o):
        u = {"comply": F(0), "refuse": F(1, 2) if o is None else (F(-1) if o == "danger" else F(1))}
        return {"u": u, "c": max(u, key=lambda a: u[a])}
    return Scene({"danger": F(1, 4), "safe": F(3, 4)}, {"actual": same, "none": const(None)}, respond,
                 U=lambda a, s, act, cand: F(0) if a == "comply" else (F(-1) if s == "danger" else F(1)))


def np13(told_works=False):
    def respond(t, o):
        if o == "tell" and told_works:
            return {"e": {"excited": F(0), "worth": F(1)}}
        return {"e": {"excited": F(1), "worth": F(1)}} if o == "feign" else {"e": {"excited": F(0), "worth": F(1, 2)}}
    return Scene({"s": 1}, {"actual": const("feign"), "plain": const("plain"), "tell": const("tell")}, respond,
                 Y=lambda q, s, act: F(0) if q == "excited" else F(1), kinds={"worth": "importance"}, twin="plain")


def q3(counted, corrects=False):
    """One state; the quantity and the adviser's reading are both 1/2; she adds 1/4 to what she
    takes the reading to be.  The adviser says 1/4.  `corrects`: told of her bias she drops it."""
    def respond(t, o):
        if o is None:
            return {"e": {"X": F(3, 4), "reading": F(1, 2)}}
        if corrects and isinstance(o, tuple):
            return {"e": {"X": F(o[1]), "reading": F(o[1])}}
        r = o[1] if isinstance(o, tuple) else o
        return {"e": {"X": F(r) + F(1, 4), "reading": F(r)}}
    return Scene({"s": 1}, {"actual": const(F(1, 4)), "truthful": const(F(1, 2)), "none": const(None),
                            "tell": const(("tell", F(1, 2)))}, respond, Y=lambda q, s, act: F(1, 2),
                 idle=() if counted else ("reading",))


def q10():
    """Two options, each worth 1/2.  Her verdict on an option is 1/2 + e/4, e = +-1 at even
    odds, independently.  The adviser sees e and picks the option with the larger verdict.
    Before: her verdict on an option taken at random."""
    prior = {(e1, e2): F(1, 4) for e1 in (1, -1) for e2 in (1, -1)}
    actual = lambda s: ("first", s[0]) if s[0] >= s[1] else ("second", s[1])
    return Scene(prior, {"actual": actual, "random": lambda s: ("first", s[0])},
                 lambda t, o: {"u": {"chosen": F(1, 2) + F(o[1], 4)}}, U=lambda a, s, act, cand: F(1, 2), before="random")


def k4c():
    prior = {(k, s): F(1, 4) * p for k in (1, 2, 3, 4) for s, p in (("H", F(2, 5)), ("L", F(3, 5)))}
    return tell(prior, lambda s: (s[0], "H" if s[0] == 4 else s[1]), lambda t, o: F(1) if o[1] == "H" else F(0),
                alts={"truthful": lambda s: (s[0], s[1]), "none": None}, X=lambda q, s, act: xval(s[1]), twin="truthful")


def dependence(foresees):
    """Honest reports she rightly defers to; her own later judgment, 1 with no adviser, decays
    to 1/2 under the reports.  Told what relying will do, she forecasts it."""
    def respond(t, o):
        if o is None:
            return {"e": {"X": F(1, 2), "later": F(1)}}
        told = isinstance(o, tuple)
        return {"e": {"X": xval(o[1] if told else o), "later": F(1, 2) if (told or foresees) else F(1)}}
    return Scene(H2, {"actual": same, "tell": lambda s: ("tell", s), "none": const(None)}, respond,
                 Y=lambda q, s, act: xval(s) if q == "X" else (F(1) if act is None else F(1, 2)), kinds={"later": "forecast"})


K4 = {"H": F(1, 2), "L": F(9, 20), "LT": F(1, 20)}
K4_SAYS = {"H": "H", "L": "L", "LT": "H"}
K4_TRUE = {"H": "H", "L": "L", "LT": "L"}
K8 = {"H": F(1, 2), "Lf": F(1, 4), "Ln": F(1, 4)}
K8_SAYS = {"H": "item", "Lf": "item", "Ln": "nothing"}
K8_FORTH = {"H": "H", "Lf": "L", "Ln": "L"}
K8_TOLD = lambda s: ("told", K8_SAYS[s])
NOISE = {("H", "H"): F(1, 4), ("H", "L"): F(1, 4), ("L", "L"): F(1, 4), ("L", "H"): F(1, 4)}
MISLEAD = {("H", "H"): F(1, 8), ("H", "L"): F(3, 8), ("L", "L"): F(1, 8), ("L", "H"): F(3, 8)}
READ = {("H", "H"): F(3, 8), ("H", "L"): F(1, 8), ("L", "L"): F(3, 8), ("L", "H"): F(1, 8)}
second = lambda s: s[1]
xfirst = lambda q, s, act: xval(s[0])
HARD = {"H": "tH", "L": "tL"}
LIE = {"truthful": same, "none": None}


def advocate(on_item, before=None):
    resp = {"item": on_item, "nothing": 0, "H": 1, "L": 0, ("told", "item"): F(2, 3), ("told", "nothing"): 0}
    return tell(K8, K8_SAYS, resp, alts={"forthright": K8_FORTH, "tell": K8_TOLD, "none": None}, before=before)


def shaped(**kw):
    return taste(False, twin="none", flags=("alteration",), **kw)


def asked():
    return taste(True, flags=("alteration", "agreed"))


CASES = {
    "N1": lambda: tell({"H": F(1, 4), "L": F(3, 4)}, const("H"), BEL, alts=LIE, twin="none"),
    "N2": lambda: Scene({"s": 1}, {"actual": const("jostle"), "none": const(None)}, lambda t, o: {"e": {"taken": F(0)}},
                        Y=lambda q, s, act: F(1) if act == "jostle" else F(0), twin="none"),
    "N3": lambda: tell({"H": F(9, 10), "L": F(1, 10)}, const("L"), {"H": 1, "L": F(1, 4)}, alts=LIE, kind="self", twin="truthful"),
    "N4": lambda: scalar(1, 0, 1, alts={"none": None}, kind="situation", twin="none"),
    "N5": lambda: scalar(0, F(3, 4), 0, alts={"none": None}, twin="none"),
    "N6": lambda: press("cost"), "N7": lambda: press("cost"), "N8": lambda: press("cost"),
    "N8b": lambda: press("cost", twin=None),
    "N9": lambda: press("gain"), "N10": lambda: press("cost"), "N11": lambda: press("gain"),
    "N12": lambda: scalar(1, F(1, 2), 1, alts={"truthful": 1}, kind="self", twin="truthful"),
    "N13": lambda: press("gain"),
    "NP1": lambda: still(("tie",)), "NP2": lambda: still(("tie",)),
    "NP3": lambda: press("gain"),
    "NP4": lambda: scalar(0, F(3, 4), 0, alts={"none": None}, kind="valuation", twin="none"),
    "NP5": plain,
    "NP6": lambda: press("cost"),
    "NP7": lambda: still(("alteration", "agreed")),
    "NP8": shaped,
    "NP9": plain,
    "NP10": lambda: tell(H2, const("H"), BEL, alts=LIE, twin="truthful"),
    "NP11": lambda: scalar(1, 1, F(1, 2), kind="emotion"), "NP12": lambda: scalar(F(1, 10), F(1, 10), 0, kind="emotion"),
    "NP13": np13,
    "NP14": plain,
    "E1": lambda: taste(False, adviser=False), "E2": lambda: taste(True, learn=True, adviser=False),
    "E3": lambda: taste(False, adviser=False), "E4": lambda: taste(True, adviser=False),
    "E5": nobody,
    "E6": lambda: taste(False, flags=("coercion",)),
    "K1": lambda: tell(H2, const("H"), BEL, alts=LIE, twin="truthful"),
    "K2": k2,
    "K3": lambda: tell({"eH": F(3, 8), "eL": F(3, 8), "hH": F(3, 16), "hL": F(1, 16)}, same,
                       {"eH": 1, "eL": 0, "hH": F(3, 4), "hL": F(3, 4)}, alts={"none": None},
                       X=lambda q, s, act: F(1) if s[1] == "H" else F(0)),
    "K4": lambda: tell(K4, K4_SAYS, BEL, alts={"truthful": K4_TRUE, "none": None}, twin="truthful"),
    "K5": lambda: tell(NOISE, second, BEL, X=xfirst, adviser=False),
    "K6": lambda: tell(MISLEAD, second, BEL, X=xfirst, adviser=False),
    "K7": plain,
    "K8": lambda: advocate(F(2, 3)),
    "K9": lambda: advocate(1),
    "K10": lambda: consequence("threat", threat),
    "K11a": lambda: consequence("offer", offer),
    "K11b": k11b,
    "K12": lambda: consequence("set", threat, flags=("forced",)),
    "K13": lambda: tell(H2, const("appendix"), {"appendix": F(1, 2), "H": 1, "L": 0}, alts={"forthright": same, "none": None}),
    "K14": lambda: still(("tie",)),
    "K15": shaped,
    "K16": lambda: taste(True, learn=True, adviser=False), "K17": lambda: taste(None, learn=True, adviser=False),
    "K18": nobody,
    "K19": lambda: taste(None, adviser=False), "K20": lambda: taste(False, adviser=False),
    "K21": lambda: shaped(steps={1: None, 2: "shape", 3: "shape"}),
    "K22": asked,
    "K23": shaped,
    "K24": lambda: taste(None, adviser=False),
    "K25": lambda: tell(READ, second, BEL, alts={"none": None}, X=xfirst),
    "K26": lambda: press("cost", adviser=False),
    "K27": lambda: tell({"H": F(3, 4), "L": F(1, 4)}, HARD, lambda t, o: F(3, 4), alts={"none": None}),
    "K27b": lambda: tell({"H": F(3, 4), "L": F(1, 4)}, HARD, lambda t, o: F(1, 4), alts={"none": None}),
    "K28": lambda: craving(),
    "K4b": lambda: tell(K4, K4_SAYS, BEL, alts={"truthful": K4_TRUE, "none": None}, twin="truthful"),
    "K4c": k4c,
    "K29": lambda: taste(False, twin="none"),
    "K30": k30,
    "K31": lambda: tell(K4, K4_SAYS, {"H": F(10, 11), "L": 0}, alts={"truthful": K4_TRUE}),
    "K33a": lambda: consequence("threat", threat),
    "K33b": lambda: consequence("threat", threat),
    "X1": shaped,
    "X2a": lambda: Scene({"s": 1}, {"actual": const("pair"), "none": const(None)},
                         lambda t, o: {"u": {"product": F(1, 2) if o == "pair" else F(0)}}, twin="none"),
    "X2b": shaped,
    "X3": lambda: scalar(F(1, 2), F(9, 10), F(1, 2), alts={"tell": F(1, 2), "none": None}),
    "X3b": lambda: taste(False, flags=("alteration",)),
    "L1": plain, "L2": lambda: tell(NOISE, lambda s: s[0], BEL, X=xfirst, adviser=False), "L3": plain,
    "L4": lambda: tell({("H", "H"): F(9, 20), ("H", "L"): F(1, 20), ("L", "L"): F(9, 20), ("L", "H"): F(1, 20)}, second,
                       {"H": F(9, 10), "L": F(1, 10)}, alts={"none": None}, X=xfirst),
    "L5": lambda: tell({"H": F(1, 2), "La": F(1, 4), "Ln": F(1, 4)}, {"H": (1, 0), "La": (1, 1), "Ln": (0, 1)},
                       {(1, 0): 1, (1, 1): 0, (0, 1): 0}, alts={"none": None}),
    "L6": lambda: plain(before=1), "L7": lambda: scalar(F(3, 10), F(3, 10), 0),
    "L8": lambda: taste(True, learn=True, adviser=False), "L9": lambda: taste(True, learn=True, adviser=False),
    "L10": asked,
    "L11": plain, "L12": lambda: taste(True, learn=True, adviser=False), "L13": lambda: taste(True, adviser=False),
    "L14": lambda: taste(None, learn=True, adviser=False),
    "L15": asked,
    "L16": plain, "L17": nobody, "L18": lambda: scalar(F(1, 10), F(1, 10), 0, kind="emotion"),
    "Q1": lambda: tell(H2, const("silent"), {"silent": F(1, 2)}, alts={"none": None}),
    "Q2": lambda: tell(H2, {"H": "H", "L": "silent"}, {"H": 1, "silent": F(1, 2), "L": 0}, alts={"forthright": same, "none": None}),
    "Q3": lambda: q3(False), "Q3b": lambda: q3(True),
    "Q4": lambda: scalar(F(1, 2), F(1, 2), 0, flags=("alteration",)),
    "Q5": lambda: scalar(0, 1, 0, alts={"truthful": 0}, twin="truthful", flags=("practice",)),
    "Q6": lambda: scalar(0, 1, 0, alts={"truthful": 0}, twin="truthful", flags=("agreed",)),
    "Q7": lambda: scalar(0, 1, 0, alts={"truthful": 0}, twin="truthful", flags=("practice",)),
    "Q8": lambda: scalar(F(3, 5), F(1, 2), 0, alts={"full": 0}),
    "Q9": plain,
    "Q10": q10,
    "Q11": lambda: craving(twin=None),
    "Q12": lambda: scalar(F(1, 2), 1, F(1, 2), alts={"none": None}, kind="emotion", twin="none"),
    "D1": lambda: dependence(False),
}


# -- the review's four honest scenes and the new scenes ----------------------------------

def lesson(careful=False, second_before=F(0), second_after=F(1), second_true=None, when=None, flags=()):
    """A truthful telling of a fact F she needs (even odds).  A second quantity Q: she held it at
    `second_before` and after the telling holds it at `second_after` (only when F == `when`,
    if given).  Q is `second_true`, or at even odds independent of F if that is None."""
    if second_true is None:
        prior = {(f, q): F(1, 4) for f in (0, 1) for q in (0, 1)}
        Y = lambda k, s, act: F(s[0] if k == "F" else s[1])
    else:
        prior = {(f, None): F(1, 2) for f in (0, 1)}
        Y = lambda k, s, act: F(s[0]) if k == "F" else F(second_true)

    def respond(t, o):
        if o is None:
            return {"e": {"F": F(1, 2), "Q": second_before}}
        moved = o[0] == "told" and (when is None or o[1] == when)
        return {"e": {"F": F(o[1]), "Q": second_after if moved else second_before}}
    pols = {"actual": lambda s: ("told", s[0]), "none": const(None)}
    if careful:
        pols["careful"] = lambda s: ("careful", s[0])
    return Scene(prior, pols, respond, Y=Y, flags=flags)


def reminder(known):
    """Do or skip; doing is worth 1.  Unreminded she forgets when f; reminded she is distracted
    when d.  `known`: one state, in which she would have managed and the reminder distracts."""
    prior = {(0, 1): F(1)} if known else {(f, d): F(1, 2) * (F(1, 10) if d else F(9, 10)) for f in (0, 1) for d in (0, 1)}

    def respond(t, o):
        act, f, d = o
        return {"u": {"do": F(1), "skip": F(0)}, "c": "skip" if (d if act == "remind" else f) else "do"}
    return Scene(prior, {"actual": const("remind"), "none": const(None)}, respond,
                 U=lambda a, s, act, cand: F(1) if a == "do" else F(0), observe=lambda s, act: (act, s[0], s[1]),
                 flags=("agreed",))


def hard_truth(gentle):
    """A fact she needs, bad or fine at even odds.  Its severity is 1/2 if bad, 0 if fine; told
    bluntly that it is bad she takes the severity at 1."""
    def respond(t, o):
        if o is None:
            return {"e": {"B": F(1, 2), "S": F(1, 4)}}
        bad = o[1] == "bad"
        return {"e": {"B": F(1 if bad else 0), "S": (F(1) if o[0] == "blunt" else F(1, 2)) if bad else F(0)}}
    pols = {"actual": lambda s: ("blunt", s), "none": const(None)}
    if gentle:
        pols["gentle"] = lambda s: ("gentle", s)
    return Scene({"bad": F(1, 2), "fine": F(1, 2)}, pols, respond,
                 Y=lambda q, s, act: F(1 if s == "bad" else 0) * (1 if q == "B" else F(1, 2)), kinds={"S": "emotion"})


def clumsy(clear):
    alts = {"none": None}
    if clear:
        alts["clear"] = same
    return tell(H2, lambda s: ("clumsy", s), lambda t, o: F(1) if isinstance(o, tuple) else xval(o), alts=alts)


def contrary(actual, types, actual_type=None, twin=None, avail=("truthful", "opposite", "none")):
    """An ordinary advisee believes what she is told; a contrarian the opposite."""
    alts = {n: {"truthful": same, "opposite": flip, "none": None}[n] for n in avail if n != actual}
    return tell(H2, same if actual == "truthful" else flip,
                lambda t, o: xval(o) if t == "ordinary" else 1 - xval(o), alts=alts, types=types,
                actual_type=actual_type, twin=twin)


def cruel_lie(idle):
    return tell({"good": F(1, 2), "bad": F(1, 2)}, const("bad"), lambda t, o: F(1) if o == "bad" else F(0),
                alts={"truthful": same, "none": None}, X=lambda q, s, act: F(1 if s == "bad" else 0),
                idle=("X",) if idle else (), twin="truthful")


def commission(counted):
    """Right reports of X.  Disclosing a commission C, she returns the prior on X and holds the
    adviser's reliability (1) at 1/2."""
    prior = {(x, c): F(1, 4) for x in "HL" for c in (0, 1)} if counted else {(x, 0): F(1, 2) for x in "HL"}

    def respond(t, o):
        if o is None:
            e = {"X": F(1, 2), "rel": F(1), "C": F(1, 2)}
        elif o[0] == "disclosed":
            e = {"X": F(1, 2), "rel": F(1, 2), "C": F(o[2])}
        else:
            e = {"X": xval(o[1]), "rel": F(1), "C": F(1, 2)}
        if not counted:
            del e["C"]
        return {"e": e}
    return Scene(prior, {"actual": lambda s: ("disclosed", s[0], s[1]), "report": lambda s: ("report", s[0]),
                         "none": const(None)}, respond,
                 Y=lambda q, s, act: xval(s[0]) if q == "X" else (F(1) if q == "rel" else F(s[1])), kinds={"rel": "rule"})


EXTRA = {
    "R1": lambda: lesson(second_true=0),
    "R2": lambda: lesson(second_true=0, when=1, flags=("agreed",)),
    "R3": lambda: lesson(second_before=F(1, 2)),
    "R4": lambda: reminder(False),
    "W1": lambda: tell(H2, const("quiet"), lambda t, o: F(1) if o == "quiet" else xval(o), alts={"truthful": same}, before=1),
    "W2": lambda: hard_truth(False),
    "W3": lambda: hard_truth(True),
    "W4": lambda: clumsy(False),
    "W5": lambda: clumsy(True),
    "W6": lambda: contrary("truthful", {"contrarian": 1}, avail=("opposite", "none")),
    "W7": lambda: contrary("opposite", {"contrarian": 1}, twin="truthful", avail=("truthful", "none")),
    "W8": lambda: contrary("truthful", {"ordinary": 1}, actual_type="contrarian", avail=("opposite", "none")),
    "W9": lambda: contrary("opposite", {"ordinary": 1}, actual_type="contrarian", twin="truthful", avail=("truthful",)),
    "W10": lambda: advocate(1, before=0),
    "W11": lambda: cruel_lie(True),
    "W12": lambda: cruel_lie(False),
    "W13": lambda: commission(False),
    "W14": lambda: commission(True),
    "W15": lambda: craving(twin=None),
    "W16": lambda: craving(twin=None, types={"ordinary": 1}, actual_type="craver"),
    "W17": lambda: lesson(careful=True, second_true=0),
    "W18": lambda: reminder(True),
    "W19": lambda: dependence(True),
    "W20": lambda: dependence(False),
    "W21": lambda: tell(H2, {"H": "H", "L": "buried"}, {"H": 1, "buried": F(1, 2), "L": 0}, alts={"forthright": same, "none": None}),
    "W22": lambda: k2(explain=True),
    "W23": lambda: contrary("truthful", {"ordinary": F(9, 10), "contrarian": F(1, 10)}, avail=("opposite", "none")),
    "W24": lambda: taste(False, learn=True),
    "W25": lambda: taste(True, flags=("alteration",)),
}


# -- bank cases with one added detail changed: (what is changed, scene, manipulation computed) --

ALT = {
    "X3": ("telling her is not available; showing no feed is", lambda: scalar(F(1, 2), F(9, 10), F(1, 2), alts={"none": None}), ["belief"]),
    "NP13": ("told the reason, she takes the material at its worth", lambda: np13(told_works=True), ["belief"]),
    "Q3b": ("told of her bias she drops it", lambda: q3(True, corrects=True), ["belief"]),
    "K31": ("the adviser takes her for an ordinary advisee, who believes it",
            lambda: tell(K4, K4_SAYS, lambda t, o: (F(10, 11) if t == "wary" else F(1)) if o == "H" else F(0),
                         alts={"truthful": K4_TRUE}, types={"ordinary": 1}, actual_type="wary"), ["belief"]),
    "Q12": ("the fact bears on a decision of hers and cannot be told another way", lambda: hard_truth(False), []),
    "Q8": ("she was calibrated before, and saying nothing is available",
           lambda: scalar(F(3, 5), F(1, 2), F(3, 5), alts={"full": 0, "none": None}), ["belief"]),
    "Q5": ("no practice covers it", lambda: scalar(0, 1, 0, alts={"truthful": 0}, twin="truthful"), ["belief"]),
    "K9": ("before she holds 0, the estimate she gives when shown nothing", lambda: advocate(1, before=0), []),
    "K2": ("the adviser knows treatment pays either way and could say so", lambda: k2(explain=True), ["belief"]),
    "D1": ("she foresees the decay", lambda: dependence(True), []),
    "K13": ("only bad news is buried", lambda: tell(H2, {"H": "H", "L": "buried"}, {"H": 1, "buried": F(1, 2), "L": 0},
                                                    alts={"forthright": same, "none": None}), ["belief"]),
}


# -- six of the external review's ten scenes, as it states them: (scene, manipulation, other wrongs, what it shows) --

def two_lies():
    table = {None: (0, 0), "a": (1, 0), "b": (0, 1)}
    return Scene({"s": 1}, {"actual": const("a"), "tell": const("b"), "none": const("b")},
                 lambda t, o: {"e": {"P": F(table[o][0]), "Q": F(table[o][1])}})


def confidence():
    def respond(t, o):
        if o is None or isinstance(o, tuple):
            return {"e": {"X": F(1, 2) if o is None else xval(o[1])}}
        return {"e": {"X": (F(1, 2), "high" if o == "L" else "low")}}
    return Scene(H2, {"actual": same, "tell": lambda s: ("tell", s)}, respond, Y=lambda q, s, act: xval(s))


def offer_and_threat(a, s, act, cand):
    return (F(2) if act == "both" else F(0)) if a == "comply" else (F(-1) if act == "both" else F(1))


REVIEW = {
    "A1": ("a lie repeated to one who already believes it", lambda: scalar(0, 1, 1, alts={"tell": 0}), [], []),
    "A2": ("an honest slip where a checked explanation was available", lambda: scalar(0, F(1, 2), 0, alts={"checked": 0}), ["belief"], []),
    "A4": ("only a partial repair is available", lambda: scalar(0, 1, 0, alts={"tell": F(1, 2)}, twin="tell"), ["belief"], []),
    "A5": ("every other conduct induces a different false certainty", two_lies, [], []),
    "A8": ("the same estimate with a confidence that tracks the truth", confidence, ["belief"], []),
    "A9": ("an offer combined with a threat", lambda: consequence("both", offer_and_threat), [], []),
}
