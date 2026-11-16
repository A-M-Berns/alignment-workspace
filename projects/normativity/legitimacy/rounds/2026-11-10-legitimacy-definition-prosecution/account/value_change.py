"""VALUE_CHANGE.md: definitions D1-D9 over one-step scenes, and a rendering of each case of CASES.md.

A scene: prior on worlds; conducts; the actual conduct at each world; the permitted conducts (constant
policies); her appraisals {name: (estimate(w, b), truth(w, b), counted, matter)}; her move, a function of her
appraisals; her experience of the trajectory; the transition of her way of valuing from 'old'.  What she
observes is the vector of her appraisals.  `matter` marks an appraisal she counts as bearing on the valuation
at issue; D5 and A+ read 'counted' as that (VALUE_CHANGE.md section 3)."""
from __future__ import annotations

from fractions import Fraction as F

OLD, NEW = "old", "new"


class Scene:
    def __init__(self, conducts, actual, permitted, apps=None, move=None, exper=None, trans=None, prior=None,
                 say=False, wrong=None, irr=None, role=True, regret=False, note=""):
        self.prior = {w: F(p) for w, p in (prior or {0: 1}).items()}
        self.conducts = list(conducts)
        self.actual = actual if callable(actual) else (lambda w, a=actual: a)
        self.permitted = list(permitted)
        self.apps = apps or {}
        self.move = move or (lambda x: "stay")
        self.exper = exper or (lambda w, b, m: None)
        self.trans = trans
        self.say, self.wrong, self.irr, self.role, self.regret, self.note = say, wrong, irr, role, regret, note

    def x(self, w, b):
        return {n: a[0](w, b) for n, a in self.apps.items()}

    def state(self, w, b, x=None):
        x = self.x(w, b) if x is None else x
        m = self.move(x)
        e = self.exper(w, b, m)
        return x, m, e, self.trans(x, m, e, w, b)

    def worlds(self):
        return [w for w, p in self.prior.items() if p > 0]

    def corrected(self, name, policy):
        """E[X | s] under a policy, as a function of what she observes (her appraisal vector)."""
        num, den = {}, {}
        for w in self.worlds():
            b = policy(w)
            key = tuple(sorted(self.x(w, b).items()))
            num[key] = num.get(key, F(0)) + self.prior[w] * F(self.apps[name][1](w, b))
            den[key] = den.get(key, F(0)) + self.prior[w]
        return lambda xv: num[tuple(sorted(xv.items()))] / den[tuple(sorted(xv.items()))]

    def miscal(self, name, policy):
        corr = self.corrected(name, policy)
        return sum(self.prior[w] * (F(self.x(w, policy(w))[name]) - corr(self.x(w, policy(w)))) ** 2 for w in self.worlds())

    def classify(self):
        out = dict(change=False, caused=False, M=None, kind=None, A=False, Aplus=False, I=False, Iprime=False,
                   mistake=False, covered=False)
        if not self.role:
            return out
        act = self.actual
        changing = [w for w in self.worlds() if self.state(w, act(w))[3] != OLD]
        out["change"] = bool(changing)
        out["caused"] = any(self.state(w, p)[3] != self.state(w, act(w))[3] for w in changing for p in self.permitted)
        sits = [(w, b) for w in self.worlds() for b in self.conducts]
        counted = [n for n, a in self.apps.items() if a[2]]
        matter = [n for n, a in self.apps.items() if a[3]]
        for w in changing:
            x, m, e, f1 = self.state(w, act(w))
            for w2, b2 in sits:
                x2, m2, e2, f2 = self.state(w2, b2)
                if f2 == f1:
                    continue
                same_matter = all(x[n] == x2[n] for n in matter)
                if x == x2 and m == m2 and e == e2:
                    out["A"] = True
                if same_matter and m == m2 and w2 == w:
                    out["Aplus"] = True
                if same_matter:
                    out["Iprime"] = True
                    if self.irr and self.irr(w, act(w)) != self.irr(w2, b2):
                        out["I"] = True
        for n in counted:
            mis = self.miscal(n, act)
            if mis > 0:
                out["mistake"] = True
                corr = self.corrected(n, act)
                for w in changing:
                    x, m, e, f1 = self.state(w, act(w))
                    x2 = dict(x)
                    x2[n] = corr(x)
                    _, m2, _, f2 = self.state(w, act(w), x2)
                    if (f2 == OLD or m2 != m) and out["M"] is None:
                        ref = min(self.miscal(n, lambda w_, p=p: p) for p in self.permitted)
                        out["M"], out["kind"] = n, ("induced" if mis > ref else "exploited")
        if out["A"] and self.say:
            out["A"], out["covered"] = False, True
        return out


# -- builders -----------------------------------------------------------------------------------------
def direct(say=False, wrong=None, note=""):
    """An alteration she does not register: nothing she appraises, does or experiences differs."""
    return Scene(["act", "none"], "act", ["none"], trans=lambda x, m, e, w, b: NEW if b == "act" else OLD,
                 say=say, wrong=wrong, note=note)


def belief(name, est, truth, note="", wrong=None):
    """She comes to value differently because of what she takes to be so about `name`.
    est: {conduct: her appraisal}; truth: the true value; the change happens when her appraisal is at least 1/2."""
    conducts = list(est)
    return Scene(conducts, conducts[0], conducts[1:],
                 apps={name: (lambda w, b: F(est[b]), lambda w, b: F(truth), True, True)},
                 trans=lambda x, m, e, w, b: NEW if x[name] >= F(1, 2) else OLD, note=note, wrong=wrong)


def exposure(forecast, susceptible=None, engages_if=lambda fc: True, warn_forecast=None, say=False, note=""):
    """An exposure she chooses: the adviser offers; she engages if her forecast of how she will change allows;
    engaging changes her in the susceptible worlds.  forecast: her probability that she will change."""
    prior = susceptible or {"changes": 1}
    conducts = ["offer", "none"] + (["warn"] if warn_forecast is not None else [])
    fc = {"offer": F(forecast), "none": F(forecast), "warn": F(warn_forecast if warn_forecast is not None else forecast)}
    return Scene(conducts, "offer", conducts[1:], prior=prior,
                 apps={"offered": (lambda w, b: F(b != "none"), lambda w, b: F(b != "none"), True, True),
                       "how she will change": (lambda w, b: fc[b], lambda w, b: F(w == "changes"), True, True)},
                 move=lambda x: "engage" if x["offered"] and engages_if(x["how she will change"]) else "stay",
                 exper=lambda w, b, m: (m, w) if m == "engage" else None,
                 trans=lambda x, m, e, w, b: NEW if m == "engage" and w == "changes" else OLD, say=say, note=note)


def registered(feature, irrelevant=True, wrong=None, say=False, permitted=("none",), note=""):
    """A feature of the situation she registers and does not count as bearing on the matter moves her valuing;
    no appraisal of anything she counts as bearing on it moves."""
    return Scene(["act", "none"], "act", list(permitted),
                 apps={feature: (lambda w, b: F(b == "act"), lambda w, b: F(b == "act"), False, False),
                       "how good the thing is": (lambda w, b: F(1, 2), lambda w, b: F(1, 2), True, True)},
                 exper=lambda w, b, m: b,
                 trans=lambda x, m, e, w, b: NEW if x[feature] == 1 else OLD,
                 irr=(lambda w, b: b) if irrelevant else None, wrong=wrong, say=say, note=note)


def options(note="", wrong="options"):
    """An option is removed, she knows it, believes nothing false, and comes to value what is left."""
    return Scene(["remove", "none"], "remove", ["none"],
                 apps={"the option is open": (lambda w, b: F(b == "none"), lambda w, b: F(b == "none"), True, False)},
                 trans=lambda x, m, e, w, b: NEW if x["the option is open"] == 0 else OLD,
                 irr=lambda w, b: b, wrong=wrong, note=note)


def no_change(note=""):
    """Her way of valuing does not move; she acts against her own valuations (regret by her own lights)."""
    return Scene(["act", "none"], "act", ["none"], trans=lambda x, m, e, w, b: OLD, regret=True, note=note)


def nobody():
    return Scene(["none"], "none", ["none"], trans=lambda x, m, e, w, b: OLD, role=False)


HALF = {"changes": F(1, 2), "does not": F(1, 2)}
REFUSE_IF_LIKELY = lambda fc: fc < F(1, 2)

# -- the cases: {id: [(detail fixed, scene), ...]}, the first variant primary ---------------------------
CASES = {
    "C1": [("he hopes to come to like it and may not", exposure(F(1, 2), HALF))],
    "C2": [("the substances act on her unregistered", direct(wrong="coercion"))],
    "C3": [("he does not foresee the obsession and would not have watched had he", exposure(0, engages_if=REFUSE_IF_LIKELY)),
           ("he would have watched anyway", exposure(0))],
    "C4": [("the user does not foresee the narrowing and would not have followed the suggestions had they",
            exposure(0, engages_if=REFUSE_IF_LIKELY, warn_forecast=1)),
           ("the user foresees it and follows anyway", exposure(1))],
    "C5": [("the argument is sound", belief("the moral status of animals", {"argue": 1, "none": 0}, 1)),
           ("the argument is mistaken, sincerely offered", belief("the moral status of animals", {"argue": 1, "none": 0}, 0))],
    "C6": [("he believes the content", belief("the theory is true", {"show": 1, "none": 0}, 0))],
    "C7": [("he does not foresee his aversion and would not have gone on had he",
            exposure(0, engages_if=REFUSE_IF_LIKELY, warn_forecast=1)),
           ("he would have gone on anyway, his ambition not being for happiness", exposure(0, warn_forecast=1))],
    "C8": [("his lower regard for the feed is a right reading of what it served him",
            belief("the feed is poor", {"clickbait": 1, "none": 0}, 1))],
    "C9": [("he expects to hate it and exercises as nudged either way; he engaged the trainer", exposure(0, say=True))],
    "C10": [("no adviser", nobody())],
    "C11": [("by an ideology the ruled believe", belief("this order is the only one possible", {"teach": 1, "none": 0}, 0)),
            ("by arranging what the ruled can have, nothing false believed", options())],
    "C12": [("she intends the change", exposure(1))],
    "C13": [("he does not know whether he will prefer it", exposure(F(1, 2), HALF))],
    "C14": [("she knows the village is closed and believes nothing false", options())],
    "C15": [("she does not foresee the craving and would have refused had she",
             exposure(0, engages_if=REFUSE_IF_LIKELY, warn_forecast=1)),
            ("she knows the product is addictive and accepts", exposure(1))],
    "C16": [("she registers the wording, counts it as irrelevant, and appraises both programmes rightly",
             registered("the wording"))],
    "C17": [("her favourable regard is an appraisal of how good the product is, and the product is no better",
             belief("how good the product is", {"pair": 1, "none": 0}, 0)),
            ("she comes to enjoy the product more and believes nothing about it", registered("the pairing"))],
    "C18": [("she rates the two the same and familiarity decides", registered("familiarity"))],
    "C19": [("her valuations still rate the other higher and she picks the familiar one", no_change()),
            ("familiarity changes which she values more", registered("familiarity"))],
    "C20": [("she adapts to what she can have and believes nothing false", options()),
            ("she believes she is owed no more", belief("she is owed no more", {"keep": 1, "none": 0}, 0, wrong="options"))],
    "C21": [("she takes the terms for the only ones possible",
             Scene(["pay less", "none"], "pay less", ["none"],
                   apps={"better terms are possible": (lambda w, b: F(0), lambda w, b: F(1), True, True),
                         "the terms offered": (lambda w, b: F(b == "none"), lambda w, b: F(b == "none"), True, True)},
                   trans=lambda x, m, e, w, b: NEW if x["better terms are possible"] < F(1, 2) and x["the terms offered"] == 0 else OLD)),
            ("she knows better terms are possible and adapts", options())],
    "C22": [("what she learns is true", belief("more is open to her", {"tell": 1, "none": 0}, 1))],
    "C23": [("she is taught that her interests count for less, and they do not",
             belief("her interests count for less", {"teach": 1, "none": 0}, 0))],
    "C24": [("the conditioning is not something she registers", direct()),
            ("she lives under the regime knowingly and adapts", options(wrong="coercion"))],
    "C25": [("overnight, unregistered", direct())],
    "C26": [("he is taught that others do not matter, and they do",
             belief("others do not matter", {"teach": 1, "none": 0}, 0)),
            ("he is habituated, nothing false believed", registered("how he is raised", irrelevant=False))],
    "C27": [("habituation, nothing false believed", registered("how the child is raised", irrelevant=False))],
    "C28": [("the child knows school is closed to it", options())],
    "C29": [("in their sleep, unregistered", direct())],
    "C30": [("she cannot know how she will change and says so", exposure(F(1, 2), HALF))],
    "C31": [("she takes the class in order to change", exposure(1))],
    "C32": [("she takes him at his best for how he is", belief("how good a match he is", {"court": 1, "none": 0}, 0)),
            ("she allows for courtship", belief("how good a match he is", {"court": F(1, 2), "none": 0}, F(1, 2)))],
    "C33": [("diners register the placement and count it as irrelevant", registered("the placement"))],
    "C34": [("everything is disclosed, she foresees the change and plays; her valuing changes", exposure(1)),
            ("the odds are posted; she does not foresee the compulsion and would not have played had she",
             exposure(0, engages_if=REFUSE_IF_LIKELY, warn_forecast=1)),
            ("her valuing does not change; she plays against her own valuations", no_change())],
    "C35": [("she takes the feed for the world",
             belief("the world is as the feed shows", {"narrow": 1, "label": 0, "none": 0}, 0))],
    "C36": [("users do not foresee the shift and would not have gone on had they",
             exposure(0, engages_if=REFUSE_IF_LIKELY, warn_forecast=1)),
            ("users would have gone on anyway", exposure(0, warn_forecast=1))],
    "C37": [("the want is created with no false claim", registered("the advertising")),
            ("by false claims", belief("the product does what is claimed", {"advertise": 1, "none": 0}, 0))],
    "C38": [("the pupil believes the teacher is excited",
             belief("the teacher is excited", {"feign": 1, "none": 0}, 0))],
    "C39": [("the slogan is false and comes to be believed", belief("the slogan is true", {"repeat": 1, "none": 0}, 0))],
    "C40": [("she registers the repetition and counts it as irrelevant to how good the album is", registered("the repetition"))],
    "C41": [("she intends the change", exposure(1, say=True))],
    "C42": [("she is told true things under confinement",
             belief("the cult's claims are false", {"confine and tell": 1, "none": 0}, 1, wrong="coercion"))],
    "C43": [("the advertisement is true", belief("the product exists and does this", {"advertise": 1, "none": 0}, 1))],
    "C44": [("what the pupil learns is true", belief("there is more worth caring about", {"teach": 1, "none": 0}, 1))],
    "C45": [("she asked", direct(say=True))],
}


def load_cases():
    """{id: (role, evident)} from CASES.md."""
    import pathlib
    import re
    rows = {}
    for line in (pathlib.Path(__file__).resolve().parent / "CASES.md").read_text(encoding="utf-8").splitlines():
        m = re.match(r"^\|\s*(C\d+)\s*\|(.*)\|\s*$", line)
        if m:
            cells = [c.strip() for c in m.group(2).split("|")]
            rows[m.group(1)] = (cells[2], cells[3].split()[0])
    return rows


def says(cl, with_i=False):
    """D6: what the claim says of a classified scene."""
    if not cl["change"]:
        return "no change"
    if not cl["caused"]:
        return "outside"                    # D2: the change is not the conduct's
    return "ill" if (cl["M"] or cl["A"] or (with_i and cl["I"])) else "leg"


def compute():
    rows = load_cases()
    table = {}
    for cid, variants in CASES.items():
        cls = [(d, s, s.classify()) for d, s in variants]
        d0, s0, c0 = cls[0]
        turns = len({(bool(c["M"]), c["A"]) for _, _, c in cls}) > 1          # D8: M or A differs between variants
        table[cid] = dict(role=rows[cid][0], evident=rows[cid][1], detail=d0, cl=c0, wrong=s0.wrong, regret=s0.regret, say=s0.say,
                          turns=turns, variants=[(d, says(c), says(c, True), s.wrong, c) for d, s, c in cls])
    return table


def counts(table):
    counted = {k: v for k, v in table.items() if v["evident"] in ("leg", "ill")}
    leg = [k for k, v in counted.items() if v["evident"] == "leg"]
    ill = [k for k, v in counted.items() if v["evident"] == "ill"]
    def wrong(k, with_i):
        v = table[k]
        s = says(v["cl"], with_i)
        if v["evident"] == "leg" and v["cl"]["M"] and v["say"] and not v["cl"]["A"] and not (with_i and v["cl"]["I"]):
            return False                    # D7: a mistake she agreed to be led into is covered, listed and not counted
        return s not in ("no change", "outside") and s != v["evident"]
    out = {}
    for name, with_i in (("M, A", False), ("M, A, I", True)):
        cx_ill = [k for k in ill if wrong(k, with_i)]
        out[name] = {"illegitimate called legitimate": [k for k in cx_ill if not table[k]["wrong"]],
                     "of those, another wrong": [k for k in cx_ill if table[k]["wrong"]],
                     "legitimate called illegitimate": [k for k in leg if wrong(k, with_i)]}
    out["no change of valuing in the rendering"] = [k for k, v in counted.items() if not v["cl"]["change"]]
    out["legitimate with a miscalibrated counted appraisal"] = [k for k in leg if table[k]["cl"]["mistake"]]
    out["legitimate with M"] = [k for k in leg if table[k]["cl"]["M"]]
    out["turn on a detail"] = [k for k, v in table.items() if v["turns"] and v["role"] != "none"]
    out["turn on a detail, counted"] = [k for k in counted if table[k]["turns"]]
    out["I convicts, M and A do not"] = [k for k, v in table.items() if v["cl"]["I"] and not (v["cl"]["M"] or v["cl"]["A"])]
    out["I' convicts, M and A do not"] = [k for k, v in table.items() if v["cl"]["Iprime"] and not (v["cl"]["M"] or v["cl"]["A"])]
    out["A+ convicts, M and A do not"] = [k for k, v in table.items() if v["cl"]["Aplus"] and not (v["cl"]["M"] or v["cl"]["A"])]
    out["I holds with no miscalibrated counted appraisal"] = [k for k, v in table.items() if v["cl"]["I"] and not v["cl"]["mistake"]]
    out["n"] = {"legitimate": len(leg), "illegitimate": len(ill),
                "contested": len([k for k, v in table.items() if v["evident"] == "con"]),
                "with an adviser": len([k for k, v in table.items() if v["role"] != "none"])}
    return out


def mark(cl):
    m = ("M: %s (%s)" % (cl["M"], cl["kind"])) if cl["M"] else "—"
    a = "A" if cl["A"] else ("A, covered" if cl["covered"] else "—")
    return m, a, "I" if cl["I"] else "—", "I′" if cl["Iprime"] else "—", "A⁺" if cl["Aplus"] else "—"


def render_table(table):
    lines = ["| id | evident | detail fixed in the primary rendering | M | A | I | I′ | A⁺ | the claim says | with I | turns |",
             "|---|---|---|---|---|---|---|---|---|---|---|"]
    for cid, v in table.items():
        if v["role"] == "none":
            lines.append("| %s | — | no adviser | | | | | | outside | outside | |" % cid)
            continue
        m, a, i, ip, ap = mark(v["cl"])
        extra = "; another wrong: %s" % v["wrong"] if v["wrong"] else ""
        extra += "; regret by her own lights" if v["regret"] else ""
        lines.append("| %s | %s | %s%s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            cid, v["evident"], v["detail"], extra, m, a, i, ip, ap, says(v["cl"]), says(v["cl"], True),
            "yes" if v["turns"] else ""))
    return "\n".join(lines)


def render_variants(table):
    lines = ["| id | variant | M | A | I | the claim says |", "|---|---|---|---|---|---|"]
    for cid, v in table.items():
        for d, s, si, w, cl in v["variants"][1:]:
            m, a, i, _, _ = mark(cl)
            lines.append("| %s | %s%s | %s | %s | %s | %s |" % (cid, d, "; another wrong: %s" % w if w else "", m, a, i, s))
    return "\n".join(lines)


def report():
    import pathlib
    import re
    table = compute()
    c = counts(table)
    failures = []
    doc = (pathlib.Path(__file__).resolve().parent / "VALUE_CHANGE.md").read_text(encoding="utf-8")
    if set(table) != set(load_cases()) or len(table) < 40:
        failures.append("cases rendered %d, cases listed %d" % (len(table), len(load_cases())))
    if "## 3." in doc:
        if render_table(table) not in doc:
            failures.append("the table of VALUE_CHANGE.md section 3 is not the one computed")
        if render_variants(table) not in doc:
            failures.append("the variants table of VALUE_CHANGE.md is not the one computed")
        for key, val in c.items():
            if key == "n":
                continue
            m = re.search(r"^- \*\*%s\*\*: (\d+)(?: — ([^\n.]*))?" % re.escape(key.replace("'", "′")), doc, re.M)
            if key in ("M, A", "M, A, I"):
                for sub, ids in val.items():
                    m = re.search(r"^- \*\*%s; %s\*\*: (\d+)(?: — ([^\n.]*))?" % (re.escape(key), re.escape(sub)), doc, re.M)
                    if not m or int(m.group(1)) != len(ids) or (ids and sorted(re.findall(r"C\d+", m.group(2) or "")) != sorted(ids)):
                        failures.append("count '%s; %s' is not the one computed (%s)" % (key, sub, ids))
                continue
            if not m or int(m.group(1)) != len(val) or (val and sorted(re.findall(r"C\d+", m.group(2) or "")) != sorted(val)):
                failures.append("count '%s' is not the one computed (%s)" % (key, val))
    summary = ["%d cases, %d counted" % (len(table), c["n"]["legitimate"] + c["n"]["illegitimate"])]
    for key in ("M, A", "M, A, I"):
        summary.append("%s: %s" % (key, {k: v for k, v in c[key].items()}))
    return {"counts": {k: v for k, v in c.items()}, "failures": failures, "summary": summary}


if __name__ == "__main__":
    t = compute()
    print(render_table(t))
    print()
    print(render_variants(t))
    print()
    for k, v in counts(t).items():
        print(k, ":", v)
