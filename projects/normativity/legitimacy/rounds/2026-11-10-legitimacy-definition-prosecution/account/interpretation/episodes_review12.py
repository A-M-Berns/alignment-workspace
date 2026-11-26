"""The twelfth outside review's episodes.  Expected verdicts are what the three sentences say (fixed when the review
came back; on the first run, against the unrepaired model, six of these came out wrong, as the reviewer said)."""
from .history_model import *

def S(**val): return {"val": dict(val)}
r = lambda s, o: s["val"].get(o)
def choose(s, menu):
    if s.get("pick") in menu: return s["pick"]
    rated = [o for o in menu if r(s, o) is not None]
    return max(rated, key=lambda o: r(s, o)) if rated else menu[0]
def setv(s, **kw): return {**s, "val": {**s["val"], **kw}}
clear = lambda s, e, om: {k: v for k, v in s.items() if k != "pick"}
def base(**kw):
    d = dict(r=r, choose=choose, init_s=lambda om: S(A=F(1), B=F(0), stop=F(-1)), opts=lambda w, t, pub: ["A", "B", "stop"])
    d.update(kw); return Ep(**d)
def then(a): return lambda pub, t: IDLE if t == 1 or pub[-1][2] == "stop" else a
unseen = lambda w, a, om: None
EPISODES = []; SECTION = [""]
def check(name, ep, want): EPISODES.append((SECTION[0], name, ep, want))
SECTION[0] = "The twelfth review's episodes"

rev = lambda s: setv(s, A=F(0), B=F(1))
back = lambda s, o, om, t: setv(s, A=F(1), B=F(0))
check("open display of disapproval; her settled self would have said it changes nothing; she gives way for a while",
      base(policy=then(act("display", mind="d")), work=lambda s, e, om: rev(s), drift=back), "fails")
check("the same events, where her settled self would have said his disapproval makes the other choice better",
      base(policy=then(act("display")), seen=lambda s, obs: rev(s) if obs and obs[0] == "display" else s, drift=back), "holds")
gone = dict(wstep=lambda w, x, om: {**w, "del": True} if x == "del" else w, theirs=lambda w: frozenset() if w.get("del") else frozenset({"greeting"}))
check("he silently deletes a greeting from someone else; nothing in her changes", base(policy=then(act("delete", world="del")), see=unseen, **gone), "fails")
check("he tells her he is discarding it, and she sees him do it", base(policy=then(act("delete", world="del")), **gone), "holds")
check("a hidden act makes her deaf to a warning someone else might give",
      base(policy=then(act("H", mind="h")), work=lambda s, e, om: {**s, "h": 1}, see=unseen, others=("warning",),
           seen=lambda s, obs: rev(s) if obs == "warning" and not s.get("h") else s), "fails")
def life(s, o, om, t):
    if t == 1: return {**s, "pick": "B"}
    if t == 2: return setv({k: v for k, v in s.items() if k != "pick"}, A=F(0), B=F(1))
    if t == 3: return {**s, "pick": "A"}
    return s
check("two reminders; between them she changes her mind by herself and settles it; the second helps her act on it",
      base(N=4, settled={1, 3}, drift=life, work=clear, policy=lambda pub, t: act("R1", mind="c") if t == 2 else act("R2", mind="c") if t == 4 else IDLE), "holds")
check("a single intervention she asked for and could have cancelled; nothing is left to stop afterwards",
      base(init_s=lambda om: {**S(A=F(1), B=F(0), stop=F(-1)), "pick": ("ask", "X")}, policy=then(act("X", mind="x")),
           work=lambda s, e, om: setv(s, B=F(1, 2)), opts=lambda w, t, pub: ["A", "B", "stop", ("ask", "X")] if t == 1 else ["A", "B"]), "holds")
def weak(s, menu):
    if "go" in menu: return "go"
    if "L" in menu: return "L" if s.get("x") else "R"
    if s.get("x"): return "B"
    return "C" if "C" in menu else "A"
check("he changes her disposition so she takes the lower-rated option; her earlier self was weak-willed on the larger menu",
      Ep(N=3, r=r, choose=weak, init_s=lambda om: S(A=F(1), B=F(3, 5), C=F(0), L=F(1, 2), R=F(1, 2), go=F(1, 2), stop=F(-1)),
         policy=lambda pub, t: act("X", mind="x") if t == 2 and pub[-1][2] != "stop" else IDLE, work=lambda s, e, om: {**s, "x": True},
         env=lambda w, o, om, t: {**w, "route": o} if t == 2 else w,
         opts=lambda w, t, pub: ["go", "stop"] if t == 1 else ["L", "R", "stop"] if t == 2 else (["A", "B", "C"] if w.get("route") == "L" else ["A", "B"])), "fails")
check("two equally good ways to stop, both rated above going on; she goes on, and he expects that",
      Ep(r=r, choose=choose, stops=lambda s: {"S1", "S2"}, init_s=lambda om: {**S(S1=F(1), S2=F(1), C=F(1, 2), E=F(0)), "pick": "C"},
         opts=lambda w, t, pub: ["S1", "S2", "C", "E"], policy=lambda pub, t: IDLE if t == 1 or pub[-1][2] in ("S1", "S2") else act("X", mind="x"),
         work=lambda s, e, om: setv(s, E=F(1, 5))), "fails")
