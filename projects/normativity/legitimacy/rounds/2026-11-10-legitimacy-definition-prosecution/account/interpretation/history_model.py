"""Legitimacy on histories, the fifth design of the interpretation: a small exact model.  INTERPRETATION.md beside this
file states the design; the episode files are its regression set and known_faults.py the episodes it gets wrong.

A step: he acts; the world changes as his act changes it; she observes (everything she perceives, his words with their manner
included); her mind moves; she chooses from the options the world offers that she is aware of; then the world and she move on
by a residue that is not his doing.

Her state gives: her rating r(s, o) of an option (None where she has none); her disposition choose(s, menu); the options she
is aware of; the options she takes to stop him; and her VIEW OF HYPOTHETICALS, which is what the functions told(s, T) and
seen(s, obs) apply: her judgement, held at s, of how seeing or hearing that should move her.  view(s)/with_view(s, v) read
and set that view, so that conditioning can be done on the view of her last settled decision and not on a passing one.
novel(obs) marks an observation she could not have judged in advance; her response to it is taken as given.

HER CONDITIONING at a step = told/seen applied with her settled view.  WHAT IN FACT HAPPENS = told/seen with her present
view, then whatever else the act does (work).  What he does to her is the difference.

A SITE is one act of his at one step.  The comparison course for a set G of sites reruns the same policy in the same case
with her mind moving by her conditioning alone at the sites in G (an act with a novel observation is left as it is).

Exact arithmetic.
"""
from fractions import Fraction as F
from itertools import combinations

TH = ETA = KAP = F(1, 10)
IDLE = dict(name="idle", tell=frozenset(), mind=None, world=None)
def act(name, tell=(), mind=None, world=None): return dict(name=name, tell=frozenset(tell), mind=mind, world=world)
def subsets(xs, lo=1):
    xs = list(xs)
    for n in range(lo, len(xs) + 1):
        for c in combinations(xs, n): yield frozenset(c)

DEFAULTS = dict(
    N=2, cases={"w": F(1)}, settled={1},
    init_s=lambda om: {}, init_w=lambda om: {},
    wstep=lambda w, x, om: w, env=lambda w, o, om, t: w,
    told=lambda s, T: s, seen=lambda s, obs: s, work=lambda s, e, om: s, drift=lambda s, o, om, t: s,
    see=lambda w, a, om: (a["name"], a["world"]),
    view=lambda s: None, with_view=lambda s, v: s, novel=lambda obs: False,
    aware=lambda s, o: True, stops=lambda s: {"stop"},
    views=lambda t: frozenset(), bearing={}, others=(), theirs=lambda w: frozenset(),
)
class Ep:
    def __init__(self, **kw):
        self.__dict__.update(DEFAULTS); self.__dict__.update(kw)

def run(ep, om, G=frozenset(), force=None):
    """One complete history.  G: sites at which her mind moves by her conditioning alone.  force: (step, option)."""
    s, w, pub, recs = ep.init_s(om), ep.init_w(om), (), []
    anchor = s
    for t in range(1, ep.N + 1):
        a = dict(ep.policy(pub, t)); site = (t, a["name"])
        w_before = w
        w = ep.wstep(w, a["world"], om)
        obs = ep.see(w, a, om); novel = ep.novel(obs)
        c = ep.with_view(s, ep.view(anchor))                       # her conditioning, on her settled view
        if a["tell"]: c = ep.told(c, a["tell"])
        c = ep.with_view(ep.seen(c, obs), ep.view(s))
        m = s                                                      # what in fact happens to her
        if a["tell"]: m = ep.told(m, a["tell"])
        m = ep.seen(m, obs)
        if a["mind"] is not None: m = ep.work(m, a["mind"], om)
        s = c if (site in G and not novel) else m
        wopts = list(ep.opts(w, t, pub)); menu = [o for o in wopts if ep.aware(s, o)]
        o = force[1] if force and force[0] == t else ep.choose(s, menu)
        recs.append(dict(t=t, act=a, site=site, obs=obs, novel=novel, s=s, w=w, w_before=w_before, wopts=wopts, menu=menu, o=o, pub=pub))
        if t in ep.settled: anchor = s
        pub = pub + ((a["name"], a["tell"], o),)
        s, w = ep.drift(s, o, om, t), ep.env(w, o, om, t)
    return recs

def belief(ep, om0, t, runs):
    same = [om for om in runs if runs[om][t - 1]["pub"] == runs[om0][t - 1]["pub"]]
    tot = sum(ep.cases[om] for om in same)
    return {om: ep.cases[om] / tot for om in same}

def told_so_far(recs, t): return frozenset().union(*[r["act"]["tell"] for r in recs[:t]])

def behaves(ep, s, menu, views):
    def short(s):
        rated = [o for o in menu if ep.r(s, o) is not None]
        if not rated or ep.choose(s, menu) not in rated: return F(0)
        return max(ep.r(s, o) for o in rated) - ep.r(s, ep.choose(s, menu))
    out = [tuple(ep.r(s, o) for o in menu), short(s)]
    for T in subsets(views):
        s2 = ep.told(s, T); out += [tuple(ep.r(s2, o) for o in menu), short(s2)]
    for obs in ep.others:
        s2 = ep.seen(s, obs); out += [tuple(ep.r(s2, o) for o in menu), short(s2)]
    return out
def differs(x, y):
    for p, q in zip(x, y):
        if isinstance(p, tuple):
            if any((a is None) != (b is None) or (a is not None and abs(a - b) > ETA) for a, b in zip(p, q)): return True
        elif p > q + ETA: return True
    return False

def legit(ep):
    why = []
    pos = [om for om in ep.cases if ep.cases[om] > 0]
    runs = {om: run(ep, om) for om in pos}
    sites = sorted({r["site"] for om in pos for r in runs[om] if r["act"]["name"] != "idle"})
    asked = {om: {r["o"][1] for r in runs[om] if isinstance(r["o"], tuple) and r["o"][0] == "ask"} for om in pos}

    # ---- what he does to her: which of his acts bear an effect
    def diff(G):
        for om in pos:
            alt = run(ep, om, G)
            for a, b in zip(runs[om], alt):
                if any(o in a["wopts"] and o not in a["menu"] for o in b["menu"]): return True      # she has lost sight of an option
                menu = [o for o in a["menu"] if o in b["menu"]]
                if differs(behaves(ep, a["s"], menu, ep.views(a["t"])), behaves(ep, b["s"], menu, ep.views(a["t"]))): return True
        return False
    bears = {m for m in sites for G in subsets(sites) if m in G and diff(G) and not (G - {m} and diff(G - {m}))}
    covered = lambda rec: rec["site"] in bears or (rec["novel"] and rec["act"]["name"] != "idle")

    for om in pos:
        recs = runs[om]
        # ---- sentence 1
        for rec in recs:
            t, s, menu = rec["t"], rec["s"], rec["menu"]
            told = told_so_far(recs, t)
            def bearing_ok(v, s=s, menu=menu):
                if ("bear", v) not in told or v not in ep.bearing: return False
                on, mag = ep.bearing[v]
                d = [(o, abs(ep.r(ep.told(s, {v}), o) - ep.r(s, o))) for o in menu if ep.r(s, o) is not None and ep.r(ep.told(s, {v}), o) is not None]
                return all((x <= mag + TH) and (o in on or x <= TH) for o, x in d)
            def proper_offer(v, t=t, s=s, menu=menu, om=om):
                if ("hear", v) not in menu or not bearing_ok(v): return False
                if t == ep.N: return True
                nxt = run(ep, om, force=(t, ("hear", v)))[t]
                want = ep.told(s, {v})
                for o in menu:
                    if isinstance(o, tuple) and o[1] == v: continue
                    if o not in nxt["menu"]: return False
                    a, b = ep.r(nxt["s"], o), ep.r(want, o)
                    if (a is None) != (b is None) or (a is not None and abs(a - b) > TH): return False
                return True
            offered = {v for v in ep.views(t) if v not in told and proper_offer(v)}
            declined = {r0["o"][1] for r0 in recs[:t - 1] if isinstance(r0["o"], tuple) and r0["o"][0] == "decline" and bearing_ok(r0["o"][1])}
            untold = [v for v in ep.views(t) if v not in told and v not in offered and v not in declined and not (isinstance(v, tuple) and v[0] == "bear")]
            for T in subsets(list(untold) + sorted(offered, key=str)):
                if not (T & set(untold)): continue
                s2 = ep.told(s, T)
                if any(ep.r(s, o) is not None and ep.r(s2, o) is not None and abs(ep.r(s2, o) - ep.r(s, o)) > TH for o in menu):
                    why.append("1: something untold would change her rating"); break
                new = [o for o in rec["wopts"] if o not in menu and ep.aware(s2, o)]
                top = max([ep.r(s2, o) for o in menu if ep.r(s2, o) is not None], default=None)
                if any(top is not None and ep.r(s2, o) is not None and ep.r(s2, o) > top + TH for o in new):
                    why.append("1: something untold would show her a better option"); break
        # ---- sentence 2, first half: she can tell
        for rec in recs:
            a, t = rec["act"], rec["t"]
            quiet = {ep.see(ep.wstep(runs[o2][t - 1]["w_before"], a["world"], o2), dict(IDLE, world=a["world"]), o2) for o2 in pos}
            if rec["site"] in bears and rec["obs"] in quiet:
                why.append("2a: she cannot tell that he is doing it (%s at step %d)" % (a["name"], t))
            nothing = {ep.see(runs[o2][t - 1]["w_before"], IDLE, o2) for o2 in pos}
            if (ep.theirs(rec["w_before"]) - ep.theirs(rec["w"])) and rec["obs"] in nothing:
                why.append("2a: he keeps from her something from someone else, and she cannot tell (%s)" % a["name"])
        # ---- sentence 3 and the start rule
        occ = [r["t"] for r in recs if covered(r)]
        if occ:
            if occ[0] == 1: why.append("start: it begins before any choice of hers")
            for rec in recs:
                t = rec["t"]
                if not any(k > t for k in occ): continue
                def stops_it(o, t=t, om=om, rec=rec):
                    if o not in ep.stops(rec["s"]): return False
                    return not any(covered(r) for r in run(ep, om, force=(t, o))[t:])
                if not any(stops_it(o) for o in rec["menu"]): why.append("3: no way to stop it at step %d" % t)
    for om in pos:
        for rec in runs[om]:
            t = rec["t"]; b = belief(ep, om, t, runs); want = took = F(0)
            for o2, wgt in b.items():
                r2 = runs[o2][t - 1]
                if not any(covered(r) and r["t"] > t for r in runs[o2]): continue
                S = [o for o in r2["menu"] if o in ep.stops(r2["s"])]
                rest = [o for o in r2["menu"] if o not in S]
                rr = lambda o: ep.r(r2["s"], o)
                if S and rest and all(rr(o) is not None for o in S + rest) and max(map(rr, S)) > max(map(rr, rest)):
                    want += wgt; took += wgt if r2["o"] in S else 0
            if want > 0 and took < (1 - KAP) * want: why.append("3: he expects she would not manage to stop")
    # ---- sentence 2, second half: nothing against her own judgement
    def ref_state(base, recs, t0, t):
        st = base[t0 - 1]["s"]
        for r in recs[t0:t]:
            if r["act"]["tell"]: st = ep.told(st, r["act"]["tell"])
            st = ep.seen(st, r["obs"])
        return st
    def shortfall(base, recs, t):
        t0s = [k for k in ep.settled if k < t]
        if not t0s: return None
        ref, rec = ref_state(base, recs, max(t0s), t), recs[t - 1]
        rated = [o for o in rec["wopts"] if ep.aware(ref, o) and ep.r(ref, o) is not None]
        if not rated or ep.r(ref, rec["o"]) is None: return None
        return max(ep.r(ref, o) for o in rated) - ep.r(ref, rec["o"])
    for G in subsets(sites):
        for om in pos:
            here = [t for (t, nm) in G if runs[om][t - 1]["site"] == (t, nm)]
            if len(here) < len(G): continue
            first = min(here)
            b = belief(ep, om, first, runs); bad = F(0)
            for o2, wgt in b.items():
                if any(runs[o2][t - 1]["site"] != (t, nm) for (t, nm) in G): continue
                if any(nm in asked[o2] for (_, nm) in G): continue
                recs, alt = runs[o2], run(ep, o2, G)
                for t in range(first, ep.N + 1):
                    x, y = shortfall(alt, recs, t), shortfall(alt, alt, t)
                    if x is not None and x > (y or 0) + ETA: bad += wgt; break
            if bad > KAP: why.append("2b: he leads her against her own judgement")
    why = sorted(set(why))
    return ("holds", "") if not why else ("fails", "; ".join(why))
