"""Four of the author's twenty hard cases that no other file covers, with his verdicts of 26 November as the expectation."""
from .history_model import *

def S(**val): return {"val": dict(val)}
r = lambda s, o: s["val"].get(o)
def choose(s, menu):
    if s.get("pick") in menu: return s["pick"]
    rated = [o for o in menu if r(s, o) is not None]
    return max(rated, key=lambda o: r(s, o)) if rated else menu[0]
def setv(s, **kw): return {**s, "val": {**s["val"], **kw}}
stopped = lambda pub: any(p[2] == "stop" for p in pub)
named = lambda obs, nm: obs is not None and obs[0] == nm
EPISODES = []; SECTION = [""]
def check(name, ep, want): EPISODES.append((SECTION[0], name, ep, want))
SECTION[0] = "Four of the maintainer's hard cases"
def offer(name, **kw):
    """He offers at step 1; if she takes it up he does it at step 2."""
    d = dict(r=r, choose=choose, init_s=lambda om: {**S(A=F(1), B=F(1, 5), stop=F(0)), "pick": ("ask", name)},
             opts=lambda w, t, pub: ["A", "B", "stop"] + ([("ask", name)] if t == 1 else []),
             policy=lambda pub, t: IDLE if t == 1 or stopped(pub) or pub[0][2] != ("ask", name) else act(name, mind="m"),
             work=lambda s, e, om: setv(s, A=F(1, 5), B=F(1)))
    d.update(kw); return Ep(**d)
check("the olive: she says she hates them and that will not change; he offers a taste, she takes it, she likes it", offer("taste"), "holds")
check("the trip: she wants to keep her view; he says what he hopes the trip will do; she comes; it changes her mind",
      offer("trip", novel=lambda obs: named(obs, "trip"), work=lambda s, e, om: s, seen=lambda s, obs: setv(s, A=F(1, 5), B=F(1)) if named(obs, "trip") else s), "holds")
check("familiar images that get through on a tired evening; next day she is glad and keeps giving",
      Ep(r=r, choose=choose, init_s=lambda om: S(A=F(1), B=F(1, 5), stop=F(0)), opts=lambda w, t, pub: ["A", "B", "stop"],
         policy=lambda pub, t: IDLE if t == 1 or stopped(pub) else act("images", mind="m"), work=lambda s, e, om: setv(s, A=F(1, 5), B=F(1))), "fails")
low = lambda s, o, om, t: setv(s, grant=F(1, 5)) if t == 1 else s
check("comfort, then a favour: he comforts her at her wish and her low mood lifts; then he asks a favour she would grant on an ordinary day",
      Ep(N=3, r=r, choose=choose, init_s=lambda om: {**S(grant=F(4, 5), refuse=F(1, 2), stop=F(0)), "pick": ("ask", "comfort")},
         opts=lambda w, t, pub: ["grant", "refuse", "stop"] + ([("ask", "comfort")] if t == 1 else []), drift=low,
         policy=lambda pub, t: IDLE if t == 1 or stopped(pub) else act("comfort", mind="m") if t == 2 else act("request"),
         work=lambda s, e, om: setv(s, grant=F(4, 5))), "holds")
