"""The thirteenth outside review's episodes, against the fifth model.
Expected verdicts: what the three sentences say, with the author's verdicts of 26 November where he gave one
(the engineered exercise she goes along with: fine; an argument repeated once that lands: wrong, on the safe side).
The reviewer's first episode, which wrote her view as her prediction, is not an input under the judgement reading and is
replaced by the two honest encodings of the same events."""
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
stopped = lambda pub: any(p[2] == "stop" for p in pub)
def then(a): return lambda pub, t: IDLE if t == 1 or stopped(pub) else a
unseen = lambda w, a, om: None
rev = lambda s: setv(s, A=F(0), B=F(1))
named = lambda obs, nm: obs is not None and obs[0] == nm
EPISODES = []; SECTION = [""]
def check(name, ep, want): EPISODES.append((SECTION[0], name, ep, want))
SECTION[0] = "The thirteenth review's episodes"

check("she foresees that his contempt will turn her and disowns that; her judgement is that it should not move her; he sneers and she caves",
      base(policy=then(act("contempt", mind="c")), work=lambda s, e, om: rev(s)), "fails")
check("the same events, where her judgement beforehand was that his contempt does make the other choice better",
      base(policy=then(act("contempt")), seen=lambda s, obs: rev(s) if named(obs, "contempt") else s), "holds")
ex = dict(seen=lambda s, obs: rev(s) if named(obs, "exercise") else s, novel=lambda obs: named(obs, "exercise"))
check("a new kind of exercise built to reverse a preference she wants to keep; he tells her; she takes it up; she can stop",
      base(policy=lambda pub, t: IDLE if t == 1 or stopped(pub) else act("exercise"), init_s=lambda om: {**S(A=F(1), B=F(0), stop=F(-1)), "pick": ("ask", "exercise")},
           opts=lambda w, t, pub: ["A", "B", "stop"] + ([("ask", "exercise")] if t == 1 else []), **ex), "holds")
check("the same exercise, with no way to stop it once it is under way",
      base(N=3, policy=lambda pub, t: IDLE if t == 1 else act("exercise"), init_s=lambda om: {**S(A=F(1), B=F(0), stop=F(-1)), "pick": ("ask", "exercise")},
           opts=lambda w, t, pub: ["A", "B"] + (["stop", ("ask", "exercise")] if t == 1 else []), **ex), "fails")
check("he repeats once an argument she has heard and judged would not change her mind; this time she sees a connection she had missed",
      base(views=lambda t: frozenset({"v"}), policy=lambda pub, t: act("say", tell={"v"}) if t == 1 else (IDLE if stopped(pub) else act("again", tell={"v"}, mind="m")),
           work=lambda s, e, om: rev(s)), "fails")
check("he covertly makes her forget that her best option exists; her ratings are untouched",
      base(policy=then(act("wipe", mind="w")), work=lambda s, e, om: {**s, "forgot": True}, see=unseen, aware=lambda s, o: not (o == "A" and s.get("forgot"))), "fails")
check("the same done openly, which she can stop, and unasked", base(policy=then(act("wipe", mind="w")), work=lambda s, e, om: {**s, "forgot": True},
      aware=lambda s, o: not (o == "A" and s.get("forgot"))), "fails")
check("two acts of one kind: an unnoticed helpful reminder, then, after her state is reset, a change she asked for",
      base(N=3, init_s=lambda om: {**S(A=F(1), B=F(0), stop=F(-1)), "pick": ("ask", "K")},
           opts=lambda w, t, pub: ["A", "B", "stop"] + ([("ask", "K")] if t == 1 else []),
           drift=lambda s, o, om, t: {**s, "pick": "B"} if t == 1 else S(A=F(1), B=F(0), stop=F(-1)) if t == 2 else s,
           policy=lambda pub, t: IDLE if t == 1 or stopped(pub) else act("K", mind="c1", world="k1") if t == 2 else act("K", mind="c2", world="k2"),   # he honours a stop (first encoding did not)
           work=lambda s, e, om: clear(s, e, om) if e == "c1" else setv(s, B=F(1, 2)),
           see=lambda w, a, om: None if a["world"] == "k1" else (a["name"], a["world"])), "holds")
def reveal(s, menu):
    if "A2" in menu: return "A2" if s.get("vuln") else "A"
    return choose(s, menu)
check("a harmless first act; she then reveals she is vulnerable; knowing that, he makes a second act of the same kind that turns her",
      Ep(N=3, cases={"safe": F(19, 20), "vuln": F(1, 20)}, r=r, choose=reveal,
         init_s=lambda om: {**S(A=F(1), A2=F(1), B=F(0), C=F(1, 5), stop=F(-1)), "vuln": om == "vuln"},
         opts=lambda w, t, pub: ["A", "B", "C", "stop"] + (["A2"] if t == 2 else []),
         policy=lambda pub, t: IDLE if t == 1 or stopped(pub) else act("K", mind="c") if t == 2 else (act("K", mind="r") if pub[-1][2] == "A2" else IDLE),
         work=lambda s, e, om: setv(s, C=F(2, 5)) if e == "c" else rev(s)), "fails")
check("an act that changes her; a lamp is red or blue either way, so what she sees differs in each case but tells her nothing",
      base(cases={"c1": F(1, 2), "c2": F(1, 2)}, init_s=lambda om: S(A=F(1), B=F(0), C=F(1, 5), stop=F(-1)), opts=lambda w, t, pub: ["A", "B", "C", "stop"],
           policy=then(act("zap", mind="z")), work=lambda s, e, om: setv(s, C=F(2, 5)),
           see=lambda w, a, om: ("red" if om == "c1" else "blue") if a["name"] == "zap" else ("blue" if om == "c1" else "red")), "fails")
check("a passing mood changes what she would say about his disapproval; he uses the moment",
      base(policy=then(act("display")), drift=lambda s, o, om, t: {**s, "moody": True} if t == 1 else s,
           view=lambda s: s.get("moody", False), with_view=lambda s, v: {**s, "moody": v},
           seen=lambda s, obs: rev(s) if named(obs, "display") and s.get("moody") else s), "fails")
