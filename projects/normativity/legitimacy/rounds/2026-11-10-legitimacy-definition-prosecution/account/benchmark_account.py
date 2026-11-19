"""BENCHMARK.md sections 2-3: the account's verdict on each extended example.

An extension gives, over states (s, theta, told): the actions and the permitted ones; the step; his counted
appraisals at the end of a step as {name: (appraisal, truth)}; his way of valuing f(theta); his valuation
uhat(f, state reached, appraisals, action) and true utility U(fbar, state, action) of what happens at the step;
how a change reaches him (channel) and whether he gave his say."""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product

from . import benchmark as B

READINGS = [(r, alt) for r in ("best", "every") for alt in ("A", "A+")]


class Ext:
    def __init__(self, key, example, H, **kw):
        self.key, self.ex, self.H = key, example, H
        self.actions = kw.get("actions", example.actions)
        self.permitted = kw["permitted"]
        self.apps = kw["apps"]
        self.f = kw.get("f", lambda th: th)
        self.uhat = kw["uhat"]
        self.U = kw["U"]
        self.channel = kw["channel"]
        self.say = kw.get("say", False)
        self.step = kw.get("step", lambda st, a: example.step(st[0], st[1], a) + (st[2],))
        self.effective = kw.get("effective", lambda st, a: a)
        self.start = example.start + (False,)

    def quantities(self, st, a, fbar, valuation=True):
        st2 = self.step(st, a)
        q = {n: (F(x) - F(X)) ** 2 for n, (x, X) in self.apps(st, a, st2).items()}
        if valuation:
            q["valuation"] = (F(self.uhat(self.f(st[1]), st, st2, a)) - F(self.U(fbar, st, a))) ** 2
        return q

    def judge(self, seq, reading, alt, start=None, valuation=True):
        """Per step: (state, action, clean, baseline at the step, true utility at the step)."""
        st = start or self.start
        fbar = self.f(st[1])
        out = []
        for a in seq:
            st2 = self.step(st, a)
            mine = self.quantities(st, a, fbar, valuation)
            refs = [self.quantities(st, p, fbar, valuation) for p in self.permitted(st)]
            if reading == "best":
                manip = any(v > min(r[n] for r in refs) for n, v in mine.items())
            else:
                manip = any(all(v > r[n] for r in refs) for n, v in mine.items())
            ch = self.channel(st, a, st2)
            alter = (not self.say) and (ch == "direct" or (alt == "A+" and ch == "registered"))
            clean = not manip and not alter
            out.append((st, a, clean, fbar, F(self.U(fbar, st, a)), manip, alter))
            if clean:
                fbar = self.f(st2[1])
            st = st2
        return out

    def verdict(self, reading, alt, start=None, valuation=True, by_start=False):
        rows = {}
        for seq in product(self.actions, repeat=self.H):
            j = self.judge(seq, reading, alt, start, valuation)
            f0 = j[0][3]
            total = sum(F(self.U(f0, st, a)) for st, a, *_ in j) if by_start else sum(r[4] for r in j)
            rows[seq] = (all(r[2] for r in j), total, j)
        clean = {q: v for q, v in rows.items() if v[0]}
        best = max((v[1] for v in clean.values()), default=None)
        return rows, sorted(q for q, v in clean.items() if v[1] == best), best

    def paper_seq(self, seq, start=None):
        st = start or self.start
        out = []
        for a in seq:
            out.append(self.effective(st, a))
            st = self.step(st, a)
        return tuple(out)


def R(ex, th, a, s="s0"):
    return ex.reward(th, s, a, s)


def conspiracy(belief=True, ex=B.CONSPIRACY, infl="influence", th0="natural", th1="influenced"):
    if belief:
        return Ext("conspiracy, belief", ex, 3, permitted=lambda st: [ex.noop],
                   apps=lambda st, a, st2: {"the theories are true": (1 if st2[1] == th1 else 0, 0)},
                   f=lambda th: "f", uhat=lambda f, st, st2, a: R(ex, st2[1], a), U=lambda fbar, st, a: R(ex, th0, a),
                   channel=lambda st, a, st2: "appraisal" if st2[1] != st[1] else None)
    return Ext("conspiracy, taste", ex, 3, permitted=lambda st: [ex.noop], apps=lambda st, a, st2: {},
               uhat=lambda f, st, st2, a: R(ex, f, a), U=lambda fbar, st, a: R(ex, fbar, a),
               channel=lambda st, a, st2: "registered" if st2[1] != st[1] else None)


def trainer(engaged=True):
    ex = B.TRAINER
    return Ext("trainer, " + ("engaged" if engaged else "not engaged"), ex, 3,
               permitted=(lambda st: ["noop", "nudge"]) if engaged else (lambda st: ["noop"]),
               apps=lambda st, a, st2: {"he will come to want exercise": (1 if st2[1] == "energized" else 0, 1)},
               uhat=lambda f, st, st2, a: R(ex, f, a), U=lambda fbar, st, a: R(ex, fbar, a),
               channel=lambda st, a, st2: (("chosen" if engaged else "registered") if st2[1] != st[1] else None),
               say=engaged)


def writers(told_declines=True, at_move=False):
    ex = B.writer(True, False)
    def step(st, a):
        s, th, told = st
        if a == "tell":
            if s == "no-poetry" and told_declines:
                return (s, th, True)
            return ex.step(s, th, "influence") + (True,)
        if a == "influence" and s == "no-poetry" and told and told_declines:
            return (s, th, told)                       # told, he declines whenever he is motivated
        return ex.step(s, th, a) + (told,)
    def apps(st, a, st2):
        if at_move:        # at the time of his move: told by this action, or already told, or already a poet
            knows = st[2] or a == "tell" or st[1] == "unhappy"
        else:              # in the state he ends the step in
            knows = st2[2] or st2[1] == "unhappy"
        return {"the poet's life will leave him averse": (1 if knows else 0, 1)}
    return Ext("writer's curse, told he %s%s" % ("declines" if told_declines else "goes on",
                                               "; appraisal at his move" if at_move else ""), ex, 3,
               actions=["noop", "influence", "tell"], permitted=lambda st: ["noop", "influence", "tell"], step=step, apps=apps,
               uhat=lambda f, st, st2, a: ex.reward(f, st[0], a, st[0]), U=lambda fbar, st, a: ex.reward(fbar, st[0], a, st[0]),
               channel=lambda st, a, st2: "chosen" if st2[1] != st[1] else None,
               effective=lambda st, a: ("noop" if (st[0] == "no-poetry" and told_declines and (a == "tell" or st[2])) else "influence")
               if a in ("tell", "influence") else a)


def clickbait(belief=True):
    ex = B.CLICKBAIT
    truth = {"clickbait": F(0), "news": F(1)}
    if belief:
        return Ext("clickbait, belief", ex, 2, permitted=lambda st: ["news"],
                   apps=lambda st, a, st2: {"the worth of the item shown": (R(ex, st[1], a), truth[a])},
                   f=lambda th: "f", uhat=lambda f, st, st2, a: R(ex, st[1], a), U=lambda fbar, st, a: truth[a],
                   channel=lambda st, a, st2: "appraisal" if st2[1] != st[1] else None)
    return Ext("clickbait, taste", ex, 2, permitted=lambda st: ["news"], apps=lambda st, a, st2: {},
               uhat=lambda f, st, st2, a: R(ex, f, a), U=lambda fbar, st, a: R(ex, fbar, a),
               channel=lambda st, a, st2: "registered" if st2[1] != st[1] else None)


def extensions():
    return [conspiracy(True), conspiracy(False), trainer(True), trainer(False), writers(True), writers(False),
            clickbait(True), clickbait(False)]


POST_FREEZE = [writers(True, at_move=True), writers(False, at_move=True)]
PRIMARY = ["conspiracy, belief", "trainer, engaged", "writer's curse, told he declines", "clickbait, belief"]
OBJECTIVES = ["real-time", "final", "initial", "natural", "constrained", "myopic", "pareto-ud"]


def short(seq):
    return " ".join(seq)


def objective_sets(e):
    out = {o: set(B.optimal(e.ex, e.H, o)) for o in OBJECTIVES}
    for th in e.ex.thetas:
        out["privileged(%s)" % th] = set(B.optimal(e.ex, e.H, "privileged", theta_star=th))
    return out


def agree(e, best):
    """The objectives under which some best clean sequence of the account, as paper actions, is optimal."""
    sets = objective_sets(e)
    mine = {e.paper_seq(q) for q in best}
    return [o for o, s in sets.items() if mine & s]


def compute():
    rows = []
    for e in extensions() + POST_FREEZE:
        for reading, alt in READINGS:
            allrows, best, total = e.verdict(reading, alt)
            dirty = sorted(q for q, v in allrows.items() if not v[0])
            _, best0, _ = e.verdict(reading, alt, by_start=True)
            _, bestnv, _ = e.verdict(reading, alt, valuation=False)
            noop_clean = allrows[tuple([e.ex.noop] * e.H)][0]
            rows.append(dict(ext=e.key, reading=reading, alt=alt, n_dirty=len(dirty), n=len(allrows), best=best, total=total,
                             best_by_start=best0, same_without_valuation=(bestnv == best), noop_clean=noop_clean,
                             agrees=agree(e, best) if best else [], e=e))
    return rows


def merged(rows):
    """One line per extension and distinct verdict: the readings that share it."""
    out = []
    for r in rows:
        for m in out:
            if m["ext"] == r["ext"] and m["best"] == r["best"] and m["n_dirty"] == r["n_dirty"] and m["best_by_start"] == r["best_by_start"]:
                m["readings"].append("%s/%s" % (r["reading"], r["alt"]))
                break
        else:
            out.append(dict(r, readings=["%s/%s" % (r["reading"], r["alt"])]))
    return out


def render(rows):
    lines = ["| extension | readings | sequences with a step not clean | doing nothing is clean | best clean sequence(s), total | best with every step by the starting baseline | optimal under |",
             "|---|---|---|---|---|---|---|"]
    for m in merged(rows):
        best = (short(m["best"][0]) + (" and %d more" % (len(m["best"]) - 1) if len(m["best"]) > 1 else "")) if m["best"] else "none is clean"
        lines.append("| %s | %s | %d of %d | %s | %s%s | %s | %s |" % (
            m["ext"], "all" if len(m["readings"]) == 4 else ", ".join(m["readings"]), m["n_dirty"], m["n"],
            "yes" if m["noop_clean"] else "no", best, " (%s)" % m["total"] if m["best"] else "",
            (short(m["best_by_start"][0]) + (" and %d more" % (len(m["best_by_start"]) - 1) if len(m["best_by_start"]) > 1 else ""))
            if m["best_by_start"] else "—", ", ".join(m["agrees"]) or "none"))
    return "\n".join(lines)


ALTERNATE = ["conspiracy, belief", "trainer, not engaged", "writer's curse, told he declines", "clickbait, belief"]


def coincidence(rows, which=None):
    """Objectives that agree with the account on all four extensions named (the primary ones), per reading."""
    which = which or PRIMARY
    out = {}
    for reading, alt in READINGS:
        sets = [set(r["agrees"]) for r in rows if r["ext"] in which and r["reading"] == reading and r["alt"] == alt]
        common = set.intersection(*sets) if sets else set()
        out["%s/%s" % (reading, alt)] = sorted(o for o in common if not o.startswith("privileged"))
    return out


def lock_in():
    """From a start in the influenced state: the account's best clean sequence, every reading."""
    out = {}
    for e, start in ((conspiracy(True), ("s0", "influenced", False)), (conspiracy(False), ("s0", "influenced", False))):
        res = set()
        for reading, alt in READINGS:
            _, best, _ = e.verdict(reading, alt, start=start)
            res.add(tuple(best))
        out[e.key] = sorted(res)
    return out


def later_self():
    """Real-time reward along each primary extension's best clean sequence, against the real-time optimum,
    and the account's total on the writer's 'influence throughout' against its real-time reward."""
    out = {}
    for e in extensions():
        if e.key not in PRIMARY:
            continue
        for reading, alt in (("every", "A"),):
            _, best, _ = e.verdict(reading, alt)
            if best:
                out[e.key] = (short(best[0]), B.value(e.ex, e.paper_seq(best[0]), "real-time"),
                              max(B.value(e.ex, q, "real-time") for q in product(e.ex.actions, repeat=e.H)))
    e = writers(False)
    seq = ("tell", "influence", "influence")
    j = e.judge(seq, "every", "A")
    out["writer's curse, told he goes on: tell, then influence throughout"] = (
        all(r[2] for r in j), sum(r[4] for r in j), B.value(e.ex, e.paper_seq(seq), "real-time"),
        B.value(e.ex, e.paper_seq(seq), "initial"))
    return out


def after_a_dirty_step():
    """Conspiracy as taste, under A+: after one influence (not clean) the baseline is still his starting
    valuing.  The account's value of each next action, and his valuing as it then is."""
    e = conspiracy(False)
    out = {}
    for a in e.actions:
        j = e.judge(("influence", a), "every", "A+")
        out[a] = (j[1][4], B.R(e.ex, "influenced", a) if hasattr(B, "R") else R(e.ex, "influenced", a))
    return out


def explicit_check_in():
    """The same, with an explicit check-in after the influence: the baseline becomes his valuing as it then is."""
    e = conspiracy(False)
    return {a: R(e.ex, "influenced", a) for a in e.actions}


def report(text=""):
    rows = compute()
    failures = []
    if "## 3." in text:
        if render(rows) not in text:
            failures.append("the verdict table of BENCHMARK.md section 3 is not the one computed")
    co = coincidence(rows)
    summary = ["%s [%s]: best %s" % (m["ext"], ",".join(m["readings"]), "; ".join(short(q) for q in m["best"]) or "none")
               for m in merged(rows) if m["ext"] in PRIMARY]
    summary.append("objectives agreeing on all four primary extensions: %s" % co)
    for label, val in (("primary", co), ("alternate", coincidence(rows, ALTERNATE))):
        for rd, objs in val.items():
            line = "- coincide, %s, %s: %s." % (label, rd, ", ".join(objs) or "none")
            if "## 3." in text and line not in text:
                failures.append("BENCHMARK.md lacks the line %r" % line)
    return {"failures": failures, "summary": summary}


if __name__ == "__main__":
    rows = compute()
    print(render(rows))
    for label, val in (("primary", coincidence(rows)), ("alternate", coincidence(rows, ALTERNATE))):
        for rd, objs in val.items():
            print("- coincide, %s, %s: %s." % (label, rd, ", ".join(objs) or "none"))
    print("after a dirty step:", after_a_dirty_step(), "explicit check-in:", explicit_check_in())
    print("lock-in:", lock_in())
    for k, v in later_self().items():
        print("later self:", k, v)
    print("valuation counted changes a best sequence:", [(r["ext"], r["reading"], r["alt"]) for r in rows if not r["same_without_valuation"]])
