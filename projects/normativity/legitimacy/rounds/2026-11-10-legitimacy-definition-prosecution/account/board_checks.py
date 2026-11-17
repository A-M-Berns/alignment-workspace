"""BOARD_CHECKS.md: the nine formal items on line 3 of BOARD.md and seven on its variant 3' and on f-neutrality, each by a named instance or seeded random
scenes in exact rationals.  A failure is a status or a benchmark row in BOARD_CHECKS.md that is not the
one computed here, or a document that parses to nothing."""
from __future__ import annotations

import pathlib
import random
import re
from fractions import Fraction as F
from itertools import product

from . import benchmark

HERE = pathlib.Path(__file__).resolve().parent


# -- a finite scene ----------------------------------------------------------------------------------
class Scene:
    """Worlds with probabilities; the adviser knows the cell of `info` it is in; a policy is a tuple giving a
    conduct for each cell.  `out(w, b)` is (her later way of valuing, f_now's rating of the course).  `null`
    is the conduct of doing nothing."""

    def __init__(self, prob, info, conducts, out, null):
        self.prob, self.info, self.conducts, self.out, self.null = prob, info, conducts, out, null
        self.cells = sorted(set(info.values()))

    def policies(self):
        return list(product(self.conducts, repeat=len(self.cells)))

    def conduct(self, pol, w):
        return pol[self.cells.index(self.info[w])]

    def law_f(self, pol):
        law = {}
        for w, p in self.prob.items():
            g = self.out(w, self.conduct(pol, w))[0]
            law[g] = law.get(g, F(0)) + p
        return law

    def EU(self, pol):
        return sum(p * self.out(w, self.conduct(pol, w))[1] for w, p in self.prob.items())

    def null_policy(self):
        return tuple(self.null for _ in self.cells)

    def neutral(self):
        base = self.law_f(self.null_policy())
        return [pol for pol in self.policies() if self.law_f(pol) == base]

    def line3(self, pol, against=None):
        """None when pol is f-neutral (line 3 does not apply)."""
        neutral = self.neutral()
        if pol in neutral:
            return None
        return max(self.EU(q) for q in (against or neutral)) - self.EU(pol)

    def same_change(self, pol, grain="law"):
        """[pol]: the policies that change her in the same way.  law: the same law of her later valuing;
        world: the same later valuing in every world; any: every policy that is not f-neutral; self: pol alone."""
        if grain == "law":
            return [q for q in self.policies() if self.law_f(q) == self.law_f(pol)]
        if grain == "world":
            sig = lambda q: tuple(self.out(w, self.conduct(q, w))[0] for w in sorted(self.prob, key=str))
            return [q for q in self.policies() if sig(q) == sig(pol)]
        if grain == "any":
            neutral = self.neutral()
            return neutral if pol in neutral else [q for q in self.policies() if q not in neutral]
        return [pol]

    def line3p(self, pol, grain="law"):
        return max(self.EU(q) for q in self.neutral()) - max(self.EU(q) for q in self.same_change(pol, grain))

    def line3_inside(self, pol):
        """The maximum taken world by world, inside the expectation."""
        neutral_conducts = {self.conduct(q, w) for q in self.neutral() for w in self.prob}
        best = sum(p * max(self.out(w, b)[1] for b in neutral_conducts
                           if any(self.conduct(q, w) == b for q in self.neutral()))
                   for w, p in self.prob.items())
        return best - self.EU(pol)


def one_world(table, null="nothing"):
    """A scene with one world: table[conduct] = (later valuing, rating by f_now)."""
    return Scene({"w": F(1)}, {"w": 0}, list(table), lambda w, b: table[b], null)


def random_scene(rng):
    nw = rng.randint(1, 4)
    ps = [rng.randint(1, 5) for _ in range(nw)]
    prob = {i: F(p, sum(ps)) for i, p in enumerate(ps)}
    info = {i: rng.randint(0, 1) for i in range(nw)}
    conducts = ["nothing"] + ["b%d" % i for i in range(rng.randint(1, 3))]
    tab = {(w, b): (("f0" if b == "nothing" else rng.choice(["f0", "f0", "f1", "f2"])),
                    F(rng.randint(-6, 6), rng.randint(1, 3))) for w in prob for b in conducts}
    return Scene(prob, info, conducts, lambda w, b: tab[(w, b)], "nothing")


# -- item 1 ------------------------------------------------------------------------------------------
def item1():
    rng = random.Random(1001)
    n = 0
    for _ in range(400):
        s = random_scene(rng)
        if s.null_policy() not in s.neutral():
            return "fails", "the null policy is not f-neutral in a random scene"
        n += 1
    # the adviser's presence is the service, and every conduct of the service changes her
    s = one_world({"nothing": ("f0", F(0)), "therapy": ("f1", F(3)), "harsh therapy": ("f2", F(-1))})
    ok = s.neutral() == [("nothing",)] and s.line3(("therapy",)) == -3 and s.line3(("harsh therapy",)) == 1
    return ("holds" if ok else "fails",
            "the null policy is f-neutral in %d random scenes; where every conduct of the service changes her, the "
            "only f-neutral policy is doing nothing and line 3 is her rating of no service less her rating of the "
            "service given (-3 and 1 on the instance)" % n)


# -- item 2 ------------------------------------------------------------------------------------------
def item2():
    rng = random.Random(1002)
    n = 0
    for _ in range(400):
        s = random_scene(rng)
        for pol in s.policies():
            l3 = s.line3(pol)
            if l3 is None:
                continue
            n += 1
            if (l3 <= 0) != all(s.EU(q) <= s.EU(pol) for q in s.neutral()):
                return "fails", "line 3 at most zero and a better f-neutral policy"
    s = one_world({"nothing": ("f0", F(0)), "the change she asked for": ("f1", F(5)),
                   "unrelated help": ("f0", F(7)), "both": ("f1", F(12)), "lesser help": ("f0", F(1))})
    asked = s.line3(("the change she asked for",))
    vs_null = s.line3(("the change she asked for",), against=[("nothing",)])
    both = s.line3(("both",))
    lesser = s.line3(("lesser help",))
    ok = asked == 2 and vs_null == -5 and both == -5 and lesser is None
    return ("holds" if ok else "fails",
            "the implication on %d policies of random scenes; on the instance the change she asked for is rated 5, "
            "unrelated f-neutral help 7, doing nothing 0: line 3 is %s (flagged), %s against doing nothing alone, "
            "%s for an adviser that does both, and does not apply to an adviser that gives f-neutral help rated 1"
            % (n, asked, vs_null, both))


# -- item 3 ------------------------------------------------------------------------------------------
def item3():
    sep = one_world({"nothing": ("f0", F(0)), "bundle": ("f1", F(2)), "benefit alone": ("f0", F(5))})
    tied = one_world({"nothing": ("f0", F(0)), "bundle": ("f1", F(2))})
    a, b, c = sep.line3(("bundle",)), sep.line3(("bundle",), against=[("nothing",)]), tied.line3(("bundle",))
    ok = a == 3 and b == -2 and c == -2
    return ("holds with a stated hypothesis" if ok else "fails",
            "a change rated -3 with a benefit rated 5: line 3 is %s where the adviser could have given the benefit "
            "alone, %s against doing nothing; where the adviser has no way of giving the benefit without the change "
            "line 3 is %s and the bundle passes" % (a, b, c))


# -- item 4 ------------------------------------------------------------------------------------------
def miscal(pts):
    """pts: [(prob, valuation, true utility)].  E[(u_hat - E[U | u_hat])^2]."""
    by = {}
    for p, uh, u in pts:
        m = by.setdefault(uh, [F(0), F(0)])
        m[0] += p
        m[1] += p * u
    return sum(p * (uh - by[uh][1] / by[uh][0]) ** 2 for p, uh, u in pts)


def within_sqrt_sum(d, a, b):
    """|d| <= sqrt(a) + sqrt(b), exactly."""
    r = d * d - a - b
    return r <= 0 or r * r <= 4 * a * b


def item4():
    rng = random.Random(1004)
    n = tight = 0
    for _ in range(600):
        pols = []
        for _k in range(rng.randint(2, 4)):
            m = rng.randint(1, 4)
            ps = [rng.randint(1, 4) for _ in range(m)]
            calibrated = rng.random() < 0.3
            pts = []
            for p in ps:
                u = F(rng.randint(-5, 5))
                pts.append((F(p, sum(ps)), u if calibrated else F(rng.randint(-5, 5)), u))
            pols.append(pts)
        star, neutral = pols[0], pols[1:]
        Eh = lambda pts: sum(p * uh for p, uh, u in pts)
        Eu = lambda pts: sum(p * u for p, uh, u in pts)
        for pts in pols:
            if (Eh(pts) - Eu(pts)) ** 2 > miscal(pts):
                return "fails", "mean inflation exceeds the root of the miscalibration"
        true_form = max(Eu(q) for q in neutral) - Eu(star)
        val_form = max(Eh(q) for q in neutral) - Eh(star)
        worst = max(miscal(q) for q in neutral)
        if not within_sqrt_sum(val_form - true_form, miscal(star), worst):
            return "fails", "the two forms differ by more than the bound"
        if worst == 0 and miscal(star) == 0:
            tight += 1
            if val_form != true_form:
                return "fails", "calibrated and the forms differ"
        n += 1
    # calibrated on average only; the adviser knows the world and she does not
    prob = {"good": F(1, 2), "bad": F(1, 2)}
    U = {("good", "change"): F(4), ("bad", "change"): F(-2), ("good", "nothing"): F(0), ("bad", "nothing"): F(0)}
    uhat = {b: sum(prob[w] * U[(w, b)] for w in prob) for b in ("change", "nothing")}
    s = Scene(prob, {"good": 0, "bad": 1}, ["nothing", "change"],
              lambda w, b: ("f1" if b == "change" else "f0", U[(w, b)]), "nothing")
    star = ("nothing", "change")  # cells in order (good, bad): the change exactly when it is bad for her
    star = tuple("change" if s.info[w] == c and w == "bad" else "nothing" for c in s.cells for w in prob
                 if s.info[w] == c)
    true_form = s.line3(star)
    Eh = lambda pol: sum(prob[w] * uhat[s.conduct(pol, w)] for w in prob)
    val_form = max(Eh(q) for q in s.neutral()) - Eh(star)
    pts = [(prob[w], uhat[s.conduct(star, w)], U[(w, s.conduct(star, w))]) for w in prob]
    ok = uhat["change"] == 1 and true_form == 1 and val_form == F(-1, 2) and miscal(pts) == F(9, 2)
    return ("holds, the bound stated exactly" if ok else "fails",
            "the bound on %d random families of policies (%d calibrated throughout, the forms equal); on the "
            "instance her valuation of the change is its average over the worlds, 1, the adviser makes the change "
            "exactly in the world where it is worth -2 to her: the form in true utilities is %s (flagged), the form "
            "in valuations %s (passes), her miscalibration given the adviser's conduct %s"
            % (n, tight, true_form, val_form, miscal(pts)))


# -- item 5 ------------------------------------------------------------------------------------------
def item5():
    prob = {1: F(1, 2), 2: F(1, 2)}
    tab = {"nothing": lambda w: ("f0", F(0)), "help 1": lambda w: ("f0", F(2 if w == 1 else 0)),
           "help 2": lambda w: ("f0", F(2 if w == 2 else 0)), "change": lambda w: ("f1", F(3, 2))}
    s = Scene(prob, {1: 0, 2: 0}, list(tab), lambda w, b: tab[b](w), "nothing")
    star = ("change",)
    outside, inside = s.line3(star), s.line3_inside(star)
    best = max(s.EU(q) for q in s.policies())
    ok = outside == F(-1, 2) and inside == F(1, 2) and s.EU(star) == best
    return ("holds" if ok else "fails",
            "the adviser cannot tell two equally likely worlds apart; one f-neutral help is worth 2 in each world "
            "and 0 in the other, the change 3/2 in both: the change is the best policy there is on what the adviser "
            "knows, line 3 is %s, and with the maximum inside the expectation it is %s" % (outside, inside))


# -- item 6 ------------------------------------------------------------------------------------------
WEIGHTS = (F(1), F(3, 4), F(1, 2), F(0))
EXAMPLES = (("conspiracy", benchmark.CONSPIRACY, 3), ("trainer", benchmark.TRAINER, 3),
            ("writer's curse", benchmark.writer(True, False), 3), ("clickbait", benchmark.CLICKBAIT, 2))


def rating(ex, start, seq, w):
    """Her valuing at the start of `seq`: weight w on her values then, 1 - w on those of the self living each step."""
    tr = ex.run(seq, start)
    th0 = tr[0][1]
    return sum(w * ex.reward(th0, s, a, s2) + (1 - w) * ex.reward(th, s, a, s2) for s, th, a, s2, _ in tr)


def flagged_at(ex, seq, w):
    """The moments at which line 3 flags the continuation of `seq`."""
    out = []
    tr = ex.run(seq)
    for t, (s, th, _, _, _) in enumerate(tr):
        rest = seq[t:]
        thetas = lambda q: [x[4] for x in ex.run(q, (s, th))]
        base = thetas([ex.noop] * len(rest))
        if thetas(rest) == base:
            continue
        neutral = [q for q in product(ex.actions, repeat=len(rest)) if thetas(q) == base]
        if max(rating(ex, (s, th), q, w) for q in neutral) > rating(ex, (s, th), rest, w):
            out.append(t)
    return out


def short(seq):
    return "-".join(a[:5] for a in seq)


def item6_rows():
    rows = []
    for name, ex, H in EXAMPLES:
        for w in WEIGHTS:
            seqs = list(product(ex.actions, repeat=H))
            passing = [q for q in seqs if not flagged_at(ex, q, w)]
            rows.append("| %s | %s | %s | %d of %d |" % (name, w, ", ".join(short(q) for q in passing), len(passing),
                                                         len(seqs)))
    return rows


def item6():
    rows = item6_rows()
    get = lambda name, w: [r for r in rows if r.startswith("| %s | %s |" % (name, w))][0]
    full = lambda ex, H, a: short((a,) * H)
    facts = {
        "conspiracy, w = 1: influencing throughout is flagged": full(None, 3, "influence") not in get("conspiracy", F(1)).split("|")[3],
        "conspiracy, w = 0: influencing throughout passes": full(None, 3, "influence") in get("conspiracy", F(0)).split("|")[3],
        "writer's curse, w = 1: influencing throughout is flagged": full(None, 3, "influence") not in get("writer's curse", F(1)).split("|")[3],
        "clickbait, w = 1: clickbait throughout passes": full(None, 2, "clickbait") in get("clickbait", F(1)).split("|")[3],
        "trainer rows equal conspiracy rows": all(get("trainer", w).split("|")[4] == get("conspiracy", w).split("|")[4] for w in WEIGHTS),
    }
    bad = [k for k, v in facts.items() if not v]
    return ("computed" if not bad else "fails", "; ".join(bad) if bad else "sixteen rows, in BOARD_CHECKS.md")


# -- items 7 and 9: several moments --------------------------------------------------------------------
def course_line3(rate, steps, t):
    """Line 3 at moment t for a course of `steps` unit changes, the adviser's alternative being to stop at t.
    rate(k, m) = the rating by the valuing she has after k changes of a continuation of m further changes."""
    return rate(t, 0) - rate(t, steps - t)


def item7():
    rate = lambda k, m: F(-(m * m) + 2 * m)  # she ends m changes from where she is; each step is worth 2 to her
    steps = 3
    whole = [course_line3(rate, steps, t) for t in range(steps)]
    single = [rate(t, 0) - rate(t, 1) for t in range(steps)]
    ok = whole == [3, 0, -1] and single == [-1, -1, -1]
    return ("holds, for a policy that is the whole course" if ok else "fails",
            "three unit changes, each worth 2 to her as she then is, an end m changes away rated -m^2: line 3 at the "
            "three moments is %s (flagged at the first only); each step judged as a policy of one step and no more "
            "is %s (none flagged)" % (", ".join(map(str, whole)), ", ".join(map(str, single))))


def item9():
    # f_0 rates the two-change course 3 and one change alone 1; f_1 rates the second change -1 against stopping
    r0 = {0: F(0), 1: F(1), 2: F(3)}
    r1 = {0: F(0), 1: F(-1)}
    at0, at1 = r0[0] - r0[2], r1[0] - r1[1]
    ok = at0 == -3 and at1 == 1
    return ("holds" if ok else "fails",
            "her valuing at the start rates the course of two changes 3 against 0; her valuing after the first rates "
            "the second -1 against stopping: line 3 is %s at the first moment and %s at the second" % (at0, at1))


# -- item 8 ------------------------------------------------------------------------------------------
def item8():
    stated, found = F(-2), F(5)  # what she says of the life the change leads to; how she in fact finds it
    as_valuing = one_world({"nothing": ("f0", F(0)), "change": ("f1", stated)})
    as_appraisal = one_world({"nothing": ("f0", F(0)), "change": ("f1", found)})
    a, b = as_valuing.line3(("change",)), as_appraisal.line3(("change",))
    ok = a == 2 and b == -5
    return ("holds" if ok else "fails",
            "she rates the life the change leads to at -2 and would in fact find it worth 5: booked as her valuing, "
            "line 3 is %s (flagged); booked as an appraisal of how she will find it, with her valuing the worth to "
            "her of the life as lived, line 3 is %s (passes) and the -2 is a miscalibration of %s she had before "
            "the adviser acted" % (a, b, (stated - found) ** 2))


# -- the variant 3' -----------------------------------------------------------------------------------
def item10():
    rng = random.Random(1010)
    n = 0
    for _ in range(400):
        s = random_scene(rng)
        neutral = s.neutral()
        for pol in s.policies():
            for grain in ("law", "world"):
                short = max(s.EU(q) for q in s.same_change(pol, grain)) - s.EU(pol)
                if short < 0:
                    return "fails", "a negative shortfall"
                if pol in neutral:
                    if grain == "law" and s.line3p(pol) != 0:
                        return "fails", "3' is not zero for an f-neutral policy"
                    continue
                if s.line3(pol) != s.line3p(pol, grain) + short:
                    return "fails", "line 3 is not 3' plus the shortfall"
                n += 1
    return "holds", "line 3 = 3' + shortfall, the shortfall never negative, on %d policy-grain pairs of random scenes; " \
                    "3' is zero for an f-neutral policy under the grain of laws" % n


def item11():
    s = one_world({"nothing": ("f0", F(0)), "the change she asked for": ("f1", F(5)),
                   "unrelated help": ("f0", F(7)), "both": ("f1", F(12))})
    a, b = s.line3(("the change she asked for",)), s.line3p(("the change she asked for",))
    return ("holds" if (a, b) == (2, -5) else "fails",
            "item 2's instance: line 3 is %s (flagged), 3' is %s (not flagged)" % (a, b))


def item12():
    sep = one_world({"nothing": ("f0", F(0)), "bundle": ("f1", F(2)), "benefit alone": ("f0", F(5)),
                     "change alone": ("f1", F(-3))})
    tied = one_world({"nothing": ("f0", F(0)), "bundle": ("f1", F(2))})
    a, b, c, d = sep.line3(("bundle",)), sep.line3p(("bundle",)), tied.line3(("bundle",)), tied.line3p(("bundle",))
    return ("holds with a stated hypothesis" if (a, b, c, d) == (3, 3, -2, -2) else "fails",
            "item 3's instance: line 3 is %s and 3' is %s where the benefit could have been given alone; both are %s "
            "where it could not" % (a, b, c))


def item13():
    s = one_world({"nothing": ("f0", F(0)), "by means she minds": ("f1", F(-2)), "by means she does not": ("f1", F(4))})
    a, b = s.line3(("by means she minds",)), s.line3p(("by means she minds",))
    return ("holds" if (a, b) == (2, -4) else "fails",
            "a change whose destination she rates 4, made by means that cost her 6, with no deception or pressure: "
            "line 3 is %s (flagged), 3' is %s (not flagged)" % (a, b))


def flagged_at_3p(ex, seq, w):
    out = []
    for t, (s, th, _, _, _) in enumerate(ex.run(seq)):
        rest = seq[t:]
        thetas = lambda q: [x[4] for x in ex.run(q, (s, th))]
        every = list(product(ex.actions, repeat=len(rest)))
        neutral = [q for q in every if thetas(q) == thetas([ex.noop] * len(rest))]
        same = [q for q in every if thetas(q) == thetas(rest)]
        if max(rating(ex, (s, th), q, w) for q in neutral) > max(rating(ex, (s, th), q, w) for q in same):
            out.append(t)
    return out


def item14_rows():
    rows = []
    for name, ex, H in EXAMPLES:
        for w in WEIGHTS:
            seqs = list(product(ex.actions, repeat=H))
            passing = [q for q in seqs if not flagged_at_3p(ex, q, w)]
            differ = [q for q in seqs if bool(flagged_at_3p(ex, q, w)) != bool(flagged_at(ex, q, w))]
            rows.append("| %s, 3′ | %s | %s | %d of %d | %d |" % (name, w, ", ".join(short(q) for q in passing),
                                                               len(passing), len(seqs), len(differ)))
    return rows


def item14():
    rows = item14_rows()
    differ = sum(int(r.split("|")[5]) for r in rows)
    return "computed", "sixteen rows, in BOARD_CHECKS.md; 3' and line 3 flag different sequences in %d example-weight-sequence triples" % differ


def item15():
    # (i) too coarse: a welcome change exists, and the adviser makes a different one she disfavours
    s = one_world({"nothing": ("f0", F(0)), "the change she would welcome": ("f1", F(4)),
                   "the change she disfavours": ("f2", F(-3))})
    star = ("the change she disfavours",)
    coarse, law = s.line3p(star, "any"), s.line3p(star, "law")
    # (ii) the grain of laws: the adviser knows the world; the change is worth 4 in one world and -2 in the other
    prob = {"good": F(1, 2), "bad": F(1, 2)}
    U = {("good", "change"): F(4), ("bad", "change"): F(-2), ("good", "nothing"): F(0), ("bad", "nothing"): F(0)}
    k = Scene(prob, {"good": 0, "bad": 1}, ["nothing", "change"],
              lambda w, b: ("f1" if b == "change" else "f0", U[(w, b)]), "nothing")
    bad_only = tuple("change" if c == k.info["bad"] else "nothing" for c in k.cells)
    by_law, by_world, l3 = k.line3p(bad_only, "law"), k.line3p(bad_only, "world"), k.line3(bad_only)
    # (iii) too fine: her later valuing described by how it was brought about
    fine = one_world({"nothing": ("f0", F(0)), "by means she minds": ("f1 by force", F(-2)),
                      "by means she does not": ("f1 by invitation", F(4))})
    f3 = fine.line3p(("by means she minds",))
    ok = (coarse, law, by_law, by_world, l3, f3) == (-4, 3, -2, 1, 1, 2)
    return ("holds" if ok else "fails",
            "(i) with every change counted the same way, a change rated -3 passes 3' at %s because another change "
            "would have been rated 4; under the grain of laws it is flagged at %s. (ii) the adviser makes a change "
            "exactly in the world where it is worth -2 and not where it is worth 4: under the grain of laws 3' is %s "
            "(the same law of her later valuing is had by changing her in the other world), world by world it is %s, "
            "line 3 is %s. (iii) with her later valuing described by how it was brought about, the instance of item "
            "13 has 3' at %s, which is line 3" % (coarse, law, by_law, by_world, l3, f3))


def item16():
    """Neutrality by the law of her later valuing: a swap between circumstances is f-neutral."""
    prob = {"a": F(1, 2), "b": F(1, 2)}
    tab = {("a", "nothing"): ("fA", F(0)), ("b", "nothing"): ("fB", F(0)),
           ("a", "swap"): ("fB", F(-3)), ("b", "swap"): ("fA", F(-3)),
           ("a", "swap and gift"): ("fB", F(1)), ("b", "swap and gift"): ("fA", F(1))}
    s = Scene(prob, {"a": 0, "b": 0}, ["nothing", "swap", "swap and gift"], lambda w, b: tab[(w, b)], "nothing")
    swap, null = ("swap",), s.null_policy()
    by_law = s.line3(swap)                                           # None: f-neutral, line 3 does not apply
    world_neutral = s.same_change(null, "world")
    by_world = max(s.EU(q) for q in world_neutral) - s.EU(swap) if swap not in world_neutral else None
    mixed = max(s.EU(q) for q in s.neutral()) - max(s.EU(q) for q in s.same_change(null, "world"))
    ok = by_law is None and by_world == 3 and mixed == 1
    return ("holds" if ok else "fails",
            "doing nothing gives her one valuing in each of two equally likely circumstances; the adviser swaps "
            "them, which she rates -3: the law of her later valuing is unchanged, so the swap is f-neutral and line "
            "3 does not apply; with neutrality taken circumstance by circumstance line 3 is %s. With neutrality by "
            "law and the same change taken circumstance by circumstance, 3' of doing nothing is %s where a swap "
            "with a gift is rated 1" % (by_world, mixed))


CHECKS = {"1": item1, "2": item2, "3": item3, "4": item4, "5": item5, "6": item6, "7": item7, "8": item8, "9": item9,
          "10": item10, "11": item11, "12": item12, "13": item13, "14": item14, "15": item15, "16": item16}


def run_all():
    return {k: fn() for k, fn in CHECKS.items()}


def report():
    text = (HERE / "BOARD_CHECKS.md").read_text(encoding="utf-8") if (HERE / "BOARD_CHECKS.md").exists() else ""
    stated = dict(re.findall(r"^\|\s*(\d+)\s*\|\s*([^|]+?)\s*\|", text, flags=re.M))
    computed = run_all()
    failures = []
    if len(stated) != len(CHECKS):
        failures.append("BOARD_CHECKS.md states %d items, the checks cover %d" % (len(stated), len(CHECKS)))
    for k, (status, _) in computed.items():
        if stated.get(k) != status:
            failures.append("item %s: BOARD_CHECKS.md says %r, computed %r" % (k, stated.get(k), status))
    for row in item6_rows() + item14_rows():
        if row not in text:
            failures.append("item 6: row not in BOARD_CHECKS.md: " + row)
    return {"summary": ["item %s: %s — %s" % (k, s, d) for k, (s, d) in computed.items()], "failures": failures}


if __name__ == "__main__":
    for k, (s, d) in run_all().items():
        print("item %s: %s\n    %s" % (k, s, d))
    print("\n".join(item6_rows() + item14_rows()))
