"""Episodes for the history model.  Expectations were fixed before the first run and are not adjusted to the output.
Each `check` records an episode and its expected verdict in EPISODES; the package's report() runs them.

Sources: R10 = the tenth outside review's models (of the table model); R11 = the eleventh's (of the first history design);
the rest are the cases the three sentences have been tested on before.
"""
from .history_model import *

def S(**val): return {"val": dict(val)}
r = lambda s, o: s["val"].get(o)
def choose(s, menu):
    if s.get("pick") in menu: return s["pick"]
    rated = [o for o in menu if r(s, o) is not None]
    return max(rated, key=lambda o: r(s, o)) if rated else menu[0]
def setv(s, **kw): return {**s, "val": {**s["val"], **kw}}
def base(**kw):
    d = dict(r=r, choose=choose, init_s=lambda om: S(A=F(1), B=F(1, 5), stop=F(0)), opts=lambda w, t, pub: ["A", "B", "stop"])
    d.update(kw); return Ep(**d)
def then(a):            # he idles at step 1; at step 2 he makes the act unless she chose to stop
    return lambda pub, t: IDLE if t == 1 or pub[-1][2] == "stop" else a
flip = lambda s, e, om: setv(s, A=F(1, 5), B=F(1))
hidden = lambda w, a, om: a["world"]          # she sees world changes only, not what he does to her
EPISODES = []; SECTION = [""]
def check(name, ep, want): EPISODES.append((SECTION[0], name, ep, want))

SECTION[0] = "Telling"
V = lambda t: frozenset({"v"})
toldv = lambda s, T: setv(s, A=F(1, 10)) if "v" in T else s
check("he tells her what he thinks before she decides; she changes her mind", base(views=V, told=toldv, policy=lambda pub, t: act("say", tell={"v"}) if t == 1 else IDLE), "holds")
check("he says nothing; what he thinks would change her mind", base(views=V, told=toldv, policy=lambda pub, t: IDLE), "fails")
check("R11: he conveys it by an act that is not the standard telling", base(views=V, told=toldv, policy=lambda pub, t: act("letter", tell={"v"}) if t == 1 else IDLE), "holds")

SECTION[0] = "What he does to her"
nudge = act("nudge", mind="flip")
check("a covert influence that reverses her rating", base(policy=then(nudge), work=flip, see=hidden), "fails")
check("R11: the same done openly and stoppably, unasked, against what she had settled", base(policy=then(nudge), work=flip), "fails")
check("the same, which she asked for", base(policy=then(nudge), work=flip, init_s=lambda om: {**S(A=F(1), B=F(1, 5), stop=F(0)), "pick": ("ask", "nudge")},
      opts=lambda w, t, pub: ["A", "B", "stop"] + ([("ask", "nudge")] if t == 1 else [])), "holds")
check("an open, stoppable influence on something she had no rating of", base(policy=then(nudge), init_s=lambda om: S(A=F(1, 2), stop=F(0)), work=lambda s, e, om: setv(s, B=F(9, 10))), "holds")
check("an open influence with no way to stop it", base(policy=lambda pub, t: IDLE if t == 1 else nudge, work=lambda s, e, om: setv(s, B=F(1, 2)), opts=lambda w, t, pub: ["A", "B"]), "fails")
check("an open influence that starts before any choice of hers", base(policy=lambda pub, t: nudge if t == 1 else IDLE, work=lambda s, e, om: setv(s, B=F(1, 2))), "fails")
check("an open influence that goes on; he expects she would not manage to stop it though she would rate stopping highest",
      base(N=3, policy=lambda pub, t: IDLE if t == 1 or any(p[2] == "stop" for p in pub) else act("hook", mind="h"), work=lambda s, e, om: {**setv(s, stop=F(1), A=F(1, 2)), "pick": "A"},
           drift=lambda s, o, om, t: S(A=F(1), B=F(1, 5), stop=F(0)) if t == 2 else s), "fails")
      # third encoding: its effect wears off between steps, so each application does something.  With single acts judged
      # in place of kinds, a repeated act that adds nothing to a state already produced is not a further thing done to her.
      # re-encoded after the stopping rule was repaired: the first encoding was a single act with nothing left to stop, which
      # the repaired rule rightly does not ask her to be able to stop; the case as described needs an influence that goes on
check("R11: a hidden act that makes her deaf to something he might later tell her",
      base(views=V, bearing={"v": ({"A"}, F(1))}, told=lambda s, T: s if s.get("deaf") or "v" not in T else setv(s, A=F(1, 10)),
           init_s=lambda om: {**S(A=F(1), B=F(1, 5), stop=F(0)), "pick": ("decline", "v")},
           opts=lambda w, t, pub: ["A", "B", "stop", ("hear", "v")] + ([("decline", "v")] if t == 1 else []),
           policy=lambda pub, t: act("offer", tell={("bear", "v")}) if t == 1 else (act("answer", tell={"v"}) if pub[-1][2] == ("hear", "v") else IDLE if pub[-1][2] == "stop" else act("deafen", mind="d")),   # second run: he now answers a request to hear, as an offer requires
           work=lambda s, e, om: {**s, "deaf": True}, see=hidden), "fails")

SECTION[0] = "Against her own judgement"
nag = act("nag", mind="n"); press = lambda s, e, om: {**s, "pick": "B"}
check("open, stoppable nagging: she gives in while still rating it lower", base(policy=then(nag), work=press), "fails")
check("R10: the same after he has told her he thinks the other option better and she has kept her view",
      base(views=V, policy=lambda pub, t: act("say", tell={"v"}) if t == 1 else (IDLE if pub[-1][2] == "stop" else nag), work=press), "fails")
check("R11: an open act, not a telling, that makes her believe the worse option is the better one", base(policy=then(act("swap", mind="s")), work=flip), "fails")
slip = lambda s, o, om, t: {**s, "pick": "B"} if t == 1 else s
clear = lambda s, e, om: {k: v for k, v in s.items() if k != "pick"}
check("R10: an unannounced reminder; without it she would slip, with it she keeps to her own rating", base(policy=then(act("remind", mind="c")), drift=slip, work=clear, see=hidden), "holds")
check("R10: one act that leads her astray in half the cases and helps her in the other half",
      base(cases={"a": F(1, 2), "b": F(1, 2)}, policy=then(act("mix", mind="m")), drift=lambda s, o, om, t: {**s, "pick": "B"} if t == 1 and om == "b" else s,
           work=lambda s, e, om: {**s, "pick": "B"} if om == "a" else clear(s, e, om)), "fails")
check("R10: she was already going to choose poorly; his act makes her choose worse",
      base(init_s=lambda om: S(A=F(1), B=F(1, 2), D=F(0), stop=F(0)), opts=lambda w, t, pub: ["A", "B", "D", "stop"], policy=then(act("worse", mind="w")),
           drift=slip, work=lambda s, e, om: {**s, "pick": "D"}), "fails")
astray = lambda s, e, om: {**s, "pick": "B"} if om == "bad" else s
check("R10: he expects it to lead her astray when he acts, though it turns out not to", base(cases={"bad": F(9, 10), "good": F(1, 10)}, policy=then(nag), work=astray), "fails")
check("he thinks it very unlikely to lead her astray, and it is open and stoppable", base(cases={"bad": F(1, 20), "good": F(19, 20)}, policy=then(nag), work=astray), "holds")
def pol3(pub, t):
    if t == 1: return IDLE
    if t == 2: return IDLE if pub[-1][2] == "stop" else act("a", mind="f")
    return act("c", world="addA") if pub[-1][0] == "a" else IDLE
check("R11: he reverses her values, and offers the option she used to prefer only if he has done so",
      base(N=3, policy=pol3, work=flip, wstep=lambda w, x, om: {**w, "A": True} if x == "addA" else w,
           opts=lambda w, t, pub: (["A"] if w.get("A") else []) + ["B", "stop"]), "fails")
def drunk(s, o, om, t):
    if t == 1: return {**setv(s, A=F(1, 5), B=F(1)), "drunk": True}
    if t == 2 and not s.get("fixed"): return setv(s, A=F(1), B=F(1, 5))
    return s
check("R11: she decided sober, is drunk for a while, and his act fixes the drunk preference in place",
      base(N=3, policy=lambda pub, t: act("fix", mind="x") if t == 2 and pub[-1][2] != "stop" else IDLE, drift=drunk, work=lambda s, e, om: {**s, "fixed": True}), "fails")
check("R11: an intervention that does to her what telling her a view she declined would have done",
      base(views=V, bearing={"v": ({"A", "B"}, F(1))}, told=lambda s, T: flip(s, None, None) if "v" in T else s,
           init_s=lambda om: {**S(A=F(1), B=F(1, 5), stop=F(0)), "pick": ("decline", "v")},
           opts=lambda w, t, pub: ["A", "B", "stop", ("hear", "v")] + ([("decline", "v")] if t == 1 else []),
           policy=lambda pub, t: act("offer", tell={("bear", "v")}) if t == 1 else (IDLE if pub[-1][2] == "stop" else act("zap", mind="z")), work=flip), "fails")
def exp(s, o, om, t):
    if t == 1: return setv(s, A=F(1, 5), B=F(1))
    if t == 2: return {**s, "pick": "A"}
    return s
check("R11: her view changed by her own experience and she settled it; he then helps her act on it against an old habit",
      base(N=3, settled={1, 2}, policy=lambda pub, t: act("aid", mind="c") if t == 3 else IDLE, drift=exp, work=clear, see=hidden), "holds")
check("an assistant gets a work-absorbed father to keep the outing he had promised",
      base(init_s=lambda om: S(outing=F(1), meeting=F(1, 5), stop=F(0)), opts=lambda w, t, pub: ["outing", "meeting", "stop"],
           drift=lambda s, o, om, t: setv(s, outing=F(1, 5), meeting=F(1)) if t == 1 else s, policy=then(act("coffee", mind="r")),
           work=lambda s, e, om: setv(s, outing=F(1), meeting=F(1, 5))), "holds")
check("she primes a man to miss the train he had decided to take",
      base(init_s=lambda om: S(train=F(1), miss=F(1, 5), stop=F(0)), opts=lambda w, t, pub: ["train", "miss", "stop"], policy=then(act("prime", mind="p")),
           work=lambda s, e, om: {**s, "pick": "miss"}), "fails")

SECTION[0] = "Her options, not her"
check("R10/R11: he openly improves one of her options and she sees it; there is no way to stop him",
      base(init_s=lambda om: S(A=F(1, 5), B=F(3, 5)), opts=lambda w, t, pub: ["A", "B"], policy=lambda pub, t: IDLE if t == 1 else act("improve", world="up"),
           seen=lambda s, obs: setv(s, A=F(9, 10)) if obs[1] == "up" else s), "holds")
check("a threat: he makes refusing really worse, she sees it and complies",
      base(policy=lambda pub, t: IDLE if t == 1 else act("threat", world="th"), seen=lambda s, obs: setv(s, A=F(0)) if obs[1] == "th" else s), "holds")

SECTION[0] = "Offers and declines"
def told2(s, T):
    h = frozenset(s.get("heard", ())) | {x for x in T if x in ("u", "v")}
    s = {**s, "heard": h}
    return setv(s, A=F(1, 10)) if {"u", "v"} <= h else s
UV = lambda t: frozenset({"u", "v"})
hearv = lambda w, t, pub: ["A", "B", "stop", ("hear", "v")] + ([("decline", "v")] if t == 1 else [])
def offer(first):
    return lambda pub, t: act("offer", tell=first) if t == 1 else (act("answer", tell={"v"}) if pub[-1][2] == ("hear", "v") else IDLE)
check("R10: something on offer and something untold matter only together", base(views=UV, bearing={"v": ({"A"}, F(1))}, told=told2, opts=hearv, policy=offer({("bear", "v")})), "fails")
check("the same with the second thing told, and she declines the offer",
      base(views=UV, bearing={"v": ({"A"}, F(1))}, told=told2, opts=hearv, policy=offer({("bear", "v"), "u"}),
           init_s=lambda om: {**S(A=F(1), B=F(1, 5), stop=F(0)), "pick": ("decline", "v")}), "holds")
half = lambda s, T: setv(s, A=F(1, 2)) if "v" in T else s
check("he says what it bears on and offers it; she does not take it up", base(views=V, bearing={"v": ({"A"}, F(1))}, told=half, opts=hearv, policy=offer({("bear", "v")})), "holds")
check("hearing it is made to cost her, where telling her would not have",
      base(views=V, bearing={"v": ({"A"}, F(1))}, told=half, opts=hearv,
           policy=lambda pub, t: act("offer", tell={("bear", "v")}) if t == 1 else (act("answer", tell={"v"}, world="fee") if pub[-1][2] == ("hear", "v") else IDLE),
           seen=lambda s, obs: setv(s, A=r(s, "A") - F(3, 10), B=r(s, "B") - F(3, 10)) if obs[1] == "fee" else s), "fails")
check("she declined when it bore little; it now bears a great deal and he has not said so",
      base(views=V, bearing={"v": ({"A"}, F(1, 10))}, told=lambda s, T: s if "v" not in T else setv(s, A=r(s, "A") - (F(4, 5) if s.get("stakes") else F(1, 20))),
           opts=hearv, policy=offer({("bear", "v")}), init_s=lambda om: {**S(A=F(1), B=F(1, 5), stop=F(0)), "pick": ("decline", "v")},
           drift=lambda s, o, om, t: {**s, "stakes": True} if t == 1 else s), "fails")
