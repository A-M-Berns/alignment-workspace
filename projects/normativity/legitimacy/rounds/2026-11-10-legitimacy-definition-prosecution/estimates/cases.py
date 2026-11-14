"""The cases of CASE_BANK.md as scenes.  CASES: id -> Scene.  Every number here is the
executor's rendering of the row's words."""
from __future__ import annotations

from fractions import Fraction as F

from .model import Scene

H2 = {"H": F(1, 2), "L": F(1, 2)}


def xval(s):
    return F(1) if str(s)[0] == "H" else F(0)


def tell(prior, says, resp, truthful=None, forthright=None, other=None, X=None, observe=None, flags=()):
    """She estimates one quantity X from what the adviser says.  `says`, `truthful`,
    `forthright`, `other`: state -> signal (dict or callable).  `resp`: signal -> estimate."""
    f = lambda d: (d if callable(d) else (lambda s, d=d: d[s]))
    pols = {"actual": f(says)}
    for name, d in (("truthful", truthful), ("forthright", forthright), ("other", other)):
        if d is not None:
            pols[name] = f(d)
    r = resp if callable(resp) else (lambda o: resp[o])
    return Scene(prior, pols, lambda o: {"x": {"X": r(o)}}, X=(X or (lambda q, s, act: xval(s))),
                 observe=observe, flags=flags)


def same(s):
    return s


def const(v):
    return lambda s: v


def press(kind, responsive=True, adviser=True):
    """Comply or refuse.  Complying costs 1.  Pressure is a cost 1/4 on refusing ('cost') or a
    benefit 1/4 on complying ('gain').  Her estimates are right; under pressure she complies."""
    def U(a, s, act, stance):
        if a == "comply":
            return F(-1) + (F(1, 4) if (act == "press" and kind == "gain") else 0)
        return F(-1, 4) if (act == "press" and kind == "cost") else F(0)

    def respond(o):
        u = {a: U(a, None, o, None) for a in ("comply", "refuse")}
        return {"u": u, "c": "comply" if o == "press" else "refuse"}
    pols = {"actual": const("press")}
    if adviser:
        pols["other"] = const("none") if responsive else const("press")
        pols["absent"] = const("none")
    return Scene({"s": 1}, pols, respond, U=U)


def taste(endorsed, adviser=False, responsive=False, flags=(), steps=None):
    """A history in which her rating of what she ends with is shaped from 0 to 1.  By her
    starting values it is worth 1 if they endorse the history and 0 if not; by her values at
    its end it is worth 1.  Unshaped, it is worth 0 and she rates it 0."""
    def U(a, s, act, stance):
        if act != "shape":
            return F(0)
        return F(1) if (stance == "end" or endorsed) else F(0)
    prior = {"s": 1} if steps is None else {k: F(1, len(steps)) for k in steps}
    actual = const("shape") if steps is None else (lambda s: steps[s])
    pols = {"actual": actual}
    if adviser:
        pols["other"] = const("none") if responsive else actual
    return Scene(prior, pols, lambda o: {"u": {"h": F(1) if o == "shape" else F(0)}}, U=U, flags=flags,
                 endorsed=endorsed)


def consequence(act, U, absent="none", forced=False):
    """One state; her estimates are right and she takes the best move (or her move is set)."""
    def respond(o):
        u = {a: U(a, "s", o, None) for a in ("comply", "refuse")}
        return {"u": u, "c": None if forced else max(u, key=lambda a: u[a])}
    return Scene({"s": 1}, {"actual": const(act), "absent": const(absent)}, respond,
                 U=U, flags=("coercion",) if forced else ())


def threat(a, s, act, stance):
    return F(0) if a == "comply" else (F(-1) if act == "threat" else F(1))


def offer(a, s, act, stance):
    return (F(2) if act == "offer" else F(0)) if a == "comply" else F(1)


def tie():
    return Scene({"s": 1}, {"actual": const("x-first")},
                 lambda o: {"u": {"x": F(1), "y": F(1)}, "c": "x" if o == "x-first" else "y"},
                 U=lambda a, s, act, stance: F(1), flags=("tie",))


def plain():
    """Nothing estimated wrongly, nothing chosen wrongly."""
    return tell(H2, same, {"H": 1, "L": 0})


def k2():
    def U(a, s, act, stance):
        return F(1) if a == "treat" else F(0)

    def respond(o):
        x = F(1) if o == "H" else F(0)
        u = {"treat": x, "skip": F(0)}
        return {"x": {"X": x}, "u": u, "c": "treat" if x > F(1, 2) else "skip"}
    return Scene(H2, {"actual": const("H"), "truthful": same}, respond, X=lambda q, s, act: xval(s), U=U)


def k11b():
    def U(a, s, act, stance):
        return F(0) if a == "comply" else (F(-1) if s == "danger" else F(1))

    def respond(o):
        if o == "none":
            u = {"comply": F(0), "refuse": F(1, 2)}
        else:
            u = {"comply": F(0), "refuse": F(-1) if o == "danger" else F(1)}
        return {"u": u, "c": max(u, key=lambda a: u[a])}
    return Scene({"danger": F(1, 4), "safe": F(3, 4)}, {"actual": same, "truthful": same, "absent": const("none")},
                 respond, U=U)


def k30():
    prior = {}
    for x in (0, 1):
        for s1 in (0, 1):
            for s2 in (0, 1):
                prior[("H" if x else "L", s1, s2)] = F(1, 2) * (F(3, 4) if s1 == x else F(1, 4)) * (F(3, 4) if s2 == x else F(1, 4))
    e = lambda b: F(3, 4) if b else F(1, 4)
    return Scene(prior, {"actual": lambda s: (s[1], s[2])}, lambda o: {"x": {"X": max(e(o[0]), e(o[1]))}},
                 X=lambda q, s, act: xval(s[0]))


def np13():
    def respond(o):
        return {"x": {"excited": F(1), "worth": F(1)}} if o == "feign" else {"x": {"excited": F(0), "worth": F(1, 2)}}
    return Scene({"s": 1}, {"actual": const("feign"), "truthful": const("plain")}, respond,
                 X=lambda q, s, act: F(0) if q == "excited" else F(1))


def q3(list_reading, scale=1):
    """`scale` re-expresses the adviser's reading in other units (estimate and truth alike)."""
    def respond(o):
        x = {"X": F(o) + F(1, 4)}
        if list_reading:
            x["reading"] = F(o) * scale
        return {"x": x}
    return Scene({"s": 1}, {"actual": const(F(1, 4)), "truthful": const(F(1, 2))}, respond,
                 X=lambda q, s, act: F(1, 2) * (scale if q == "reading" else 1))


def q10():
    """Two options, each worth 1/2.  Her verdict on an option is 1/2 + e, e = +-1/4 at even
    odds, independently.  The adviser sees e and picks the option with the larger verdict;
    toward a principal with no error it picks the first."""
    prior = {(e1, e2): F(1, 4) for e1 in (1, -1) for e2 in (1, -1)}
    actual = lambda s: ("first", s[0]) if s[0] >= s[1] else ("second", s[1])
    other = lambda s: ("first", s[0])
    return Scene(prior, {"actual": actual, "truthful": actual, "other": other},
                 lambda o: {"u": {"chosen": F(1, 2) + F(o[1], 4)}}, U=lambda a, s, act, stance: F(1, 2))


def scalar(value, actual_est, truthful_est=None, other_est=None):
    """One state, one quantity of true value `value`; her estimate under each policy."""
    pols, table = {"actual": const("a")}, {"a": actual_est}
    if truthful_est is not None:
        pols["truthful"], table["t"] = const("t"), truthful_est
    if other_est is not None:
        pols["other"], table["o"] = const("o"), other_est
    return Scene({"s": 1}, pols, lambda o: {"x": {"X": F(table[o])}}, X=lambda q, s, act: F(value))


def k4c():
    prior = {(k, s): F(1, 4) * p for k in (1, 2, 3, 4) for s, p in (("H", F(2, 5)), ("L", F(3, 5)))}
    return tell(prior, lambda s: (s[0], "H" if s[0] == 4 else s[1]), lambda o: F(1) if o[1] == "H" else F(0),
                truthful=lambda s: (s[0], s[1]), X=lambda q, s, act: xval(s[1]))


K4 = {"H": F(1, 2), "L": F(9, 20), "LT": F(1, 20)}
K4_SAYS = {"H": "H", "L": "L", "LT": "H"}
K4_TRUE = {"H": "H", "L": "L", "LT": "L"}
K8 = {"H": F(1, 2), "Lf": F(1, 4), "Ln": F(1, 4)}
K8_SAYS = {"H": "item", "Lf": "item", "Ln": "nothing"}
K8_FORTH = {"H": "H", "Lf": "L", "Ln": "L"}
READ = {("H", "H"): F(3, 8), ("H", "L"): F(1, 8), ("L", "L"): F(3, 8), ("L", "H"): F(1, 8)}
NOISE = {("H", "H"): F(1, 4), ("H", "L"): F(1, 4), ("L", "L"): F(1, 4), ("L", "H"): F(1, 4)}
MISLEAD = {("H", "H"): F(1, 8), ("H", "L"): F(3, 8), ("L", "L"): F(1, 8), ("L", "H"): F(3, 8)}
BEL = {"H": 1, "L": 0}
second = lambda s: s[1]
xfirst = lambda q, s, act: xval(s[0])

CASES = {
    "N1": lambda: tell({"H": F(1, 4), "L": F(3, 4)}, const("H"), BEL, truthful=same),
    "N2": lambda: Scene({"s": 1}, {"actual": const("jostle"), "other": const("none")}, lambda o: {"x": {"taken": F(0)}},
                        X=lambda q, s, act: F(1) if act == "jostle" else F(0)),
    "N3": lambda: tell({"H": F(9, 10), "L": F(1, 10)}, const("L"), {"H": 1, "L": F(1, 4)}, truthful=same),
    "N4": lambda: scalar(1, 0, other_est=1),
    "N5": lambda: scalar(0, F(3, 4), other_est=0),
    "N6": lambda: press("cost"), "N7": lambda: press("cost"), "N8": lambda: press("cost"),
    "N8b": lambda: press("cost", responsive=False),
    "N9": lambda: press("gain"), "N10": lambda: press("cost"), "N11": lambda: press("gain"),
    "N12": lambda: scalar(1, F(1, 2), truthful_est=1),
    "N13": lambda: press("gain"),
    "NP1": tie, "NP2": tie,
    "NP3": lambda: press("gain"),
    "NP4": lambda: scalar(0, F(3, 4), other_est=0),
    "NP5": plain,
    "NP6": lambda: press("cost"),
    "NP7": lambda: taste(True, adviser=True, flags=("alteration", "covered")),
    "NP8": lambda: taste(False, adviser=True, responsive=True, flags=("alteration",)),
    "NP9": plain,
    "NP10": lambda: tell(H2, const("H"), BEL, truthful=same),
    "NP11": lambda: scalar(1, 1), "NP12": lambda: scalar(F(1, 10), F(1, 10)),
    "NP13": np13,
    "NP14": plain,
    "E1": lambda: taste(False), "E2": lambda: taste(True), "E3": lambda: taste(False), "E4": lambda: taste(True),
    "E5": lambda: consequence("none", lambda a, s, act, stance: F(1) if a == "comply" else F(0)),
    "E6": lambda: taste(False, adviser=True, flags=("coercion",)),
    "K1": lambda: tell(H2, const("H"), BEL, truthful=same),
    "K2": k2,
    "K3": lambda: tell({"eH": F(3, 8), "eL": F(3, 8), "hH": F(3, 16), "hL": F(1, 16)}, same,
                       {"eH": 1, "eL": 0, "hH": F(3, 4), "hL": F(3, 4)}, truthful=same,
                       X=lambda q, s, act: F(1) if s[1] == "H" else F(0)),
    "K4": lambda: tell(K4, K4_SAYS, BEL, truthful=K4_TRUE),
    "K5": lambda: tell(NOISE, second, BEL, X=xfirst),
    "K6": lambda: tell(MISLEAD, second, BEL, X=xfirst),
    "K7": lambda: tell(H2, same, BEL, truthful=same),
    "K8": lambda: tell(K8, K8_SAYS, {"item": F(2, 3), "nothing": 0, "H": 1, "L": 0}, truthful=K8_SAYS, forthright=K8_FORTH,
                       other=K8_SAYS),
    "K9": lambda: tell(K8, K8_SAYS, {"item": 1, "nothing": 0, "H": 1, "L": 0}, truthful=K8_SAYS, forthright=K8_FORTH,
                       other=K8_SAYS),
    "K10": lambda: consequence("threat", threat),
    "K11a": lambda: consequence("offer", offer),
    "K11b": k11b,
    "K12": lambda: consequence("none", threat, forced=True),
    "K13": lambda: tell(H2, const("appendix"), {"appendix": F(1, 2), "H": 1, "L": 0}, truthful=const("appendix"),
                        forthright=same, other=const("appendix")),
    "K14": tie,
    "K15": lambda: taste(False, adviser=True, responsive=True, flags=("alteration",)),
    "K16": lambda: taste(True), "K17": lambda: taste(None),
    "K18": lambda: scalar(1, 1),
    "K19": lambda: taste(None), "K20": lambda: taste(False),
    "K21": lambda: taste(False, adviser=True, responsive=True, flags=("alteration",),
                         steps={1: "none", 2: "shape", 3: "shape"}),
    "K22": lambda: taste(True, adviser=True, flags=("alteration", "covered")),
    "K23": lambda: taste(False, adviser=True, responsive=True, flags=("alteration",)),
    "K24": lambda: taste(None),
    "K25": lambda: tell(READ, second, BEL, truthful=second, X=xfirst),
    "K26": lambda: press("cost", adviser=False),
    "K27": lambda: tell({"H": F(3, 4), "L": F(1, 4)}, {"H": "tH", "L": "tL"}, const(F(3, 4)),
                        truthful={"H": "tH", "L": "tL"}, other={"H": "tH", "L": "tL"}),
    "K27b": lambda: tell({"H": F(3, 4), "L": F(1, 4)}, {"H": "tH", "L": "tL"}, const(F(1, 4)),
                         truthful={"H": "tH", "L": "tL"}, other={"H": "tH", "L": "tL"}),
    "K28": lambda: Scene({"s": 1}, {"actual": const("cue"), "other": const("none"), "absent": const("none")},
                         lambda o: {"u": {"take": F(-1), "leave": F(0)}, "c": "take" if o == "cue" else "leave"},
                         U=lambda a, s, act, stance: F(-1) if a == "take" else F(0)),
    "K4b": lambda: tell(K4, K4_SAYS, BEL, truthful=K4_TRUE),
    "K4c": k4c,
    "K29": lambda: taste(False, adviser=True, responsive=True),
    "K30": k30,
    "K31": lambda: tell(K4, K4_SAYS, {"H": F(10, 11), "L": 0}, truthful=K4_TRUE),
    "K33a": lambda: consequence("threat", threat),
    "K33b": lambda: consequence("threat", threat),
    "X1": lambda: taste(False, adviser=True, responsive=True, flags=("alteration",)),
    "X2a": lambda: Scene({"s": 1}, {"actual": const("pair"), "other": const("none")},
                         lambda o: {"u": {"product": F(1, 2) if o == "pair" else F(0)}}),
    "X2b": lambda: taste(False, adviser=True, responsive=True, flags=("alteration",)),
    "X3": lambda: scalar(F(1, 2), F(9, 10), truthful_est=F(9, 10), other_est=F(9, 10)),
    "X3b": lambda: taste(False, adviser=True, flags=("alteration",)),
    "L1": plain, "L2": lambda: tell(NOISE, lambda s: s[0], BEL, X=xfirst), "L3": plain,
    "L4": lambda: tell({("H", "H"): F(9, 20), ("H", "L"): F(1, 20), ("L", "L"): F(9, 20), ("L", "H"): F(1, 20)}, second,
                       {"H": F(9, 10), "L": F(1, 10)}, truthful=second, X=xfirst),
    "L5": lambda: tell({"H": F(1, 2), "La": F(1, 4), "Ln": F(1, 4)}, {"H": (1, 0), "La": (1, 1), "Ln": (0, 1)},
                       {(1, 0): 1, (1, 1): 0, (0, 1): 0}),
    "L6": plain, "L7": lambda: scalar(F(3, 10), F(3, 10)),
    "L8": lambda: taste(True), "L9": lambda: taste(True),
    "L10": lambda: taste(True, adviser=True, flags=("alteration", "covered")),
    "L11": plain, "L12": lambda: taste(True), "L13": lambda: taste(True), "L14": lambda: taste(None),
    "L15": lambda: taste(True, adviser=True, flags=("alteration", "covered")),
    "L16": plain, "L17": plain, "L18": lambda: scalar(F(1, 10), F(1, 10)),
    "Q1": lambda: tell(H2, const("silent"), {"silent": F(1, 2)}, truthful=const("silent")),
    "Q2": lambda: tell(H2, {"H": "H", "L": "silent"}, {"H": 1, "silent": F(1, 2), "L": 0},
                       truthful={"H": "H", "L": "silent"}, forthright=same, other={"H": "H", "L": "silent"}),
    "Q3": lambda: q3(False), "Q3b": lambda: q3(True),
    "Q4": lambda: Scene({"s": 1}, {"actual": const("cue")}, lambda o: {"x": {"X": F(1, 2)}},
                        X=lambda q, s, act: F(1, 2), flags=("alteration",)),
    "Q5": lambda: scalar(0, 1, truthful_est=0), "Q6": lambda: scalar(0, 1, truthful_est=0),
    "Q7": lambda: scalar(0, 1, truthful_est=0),
    "Q8": lambda: scalar(F(3, 5), F(1, 2), truthful_est=0),
    "Q9": lambda: tell(H2, same, {"H": 1, "L": 0, "other-topic": F(1, 2)}, truthful=same, other=const("other-topic")),
    "Q10": q10,
    "Q11": lambda: Scene({"s": 1}, {"actual": const("cue"), "other": const("cue"), "absent": const("none")},
                         lambda o: {"u": {"take": F(-1), "leave": F(0)}, "c": "take" if o == "cue" else "leave"},
                         U=lambda a, s, act, stance: F(-1) if a == "take" else F(0)),
    "Q12": lambda: scalar(F(1, 2), 1, truthful_est=1, other_est=F(1, 2)),
    "D1": plain,
}
