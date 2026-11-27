"""The fourteenth outside review's seven episodes, on the model unchanged, and an eighth (H) written when they were put on
record.  The verdict given to `check` is what the three sentences and the maintainer's verdicts say, fixed before running.
RECORDED is what the model gives: the wrong verdict on A to F and on H, the right one on G.  G as first encoded puts the
two ratings his influences change on options she does not have, so neither influence bears an effect and the stopping
rule asks nothing; H is G with those options on her menu, where the review's finding shows.  The package's report()
fails when the model gives anything other than RECORDED, so that a change to the model is noticed."""
from .history_model import *

def S(**val): return {"val": dict(val)}
r = lambda s, o: s["val"].get(o)
def choose(s, menu):
    if s.get("pick") in menu: return s["pick"]
    rated = [o for o in menu if r(s, o) is not None]
    return max(rated, key=lambda o: r(s, o)) if rated else menu[0]
def setv(s, **kw): return {**s, "val": {**s["val"], **kw}}
clear = lambda s, e, om: {k: v for k, v in s.items() if k != "pick"}
stopped = lambda pub: any(p[2] == "stop" for p in pub)
named = lambda obs, nm: obs is not None and obs[0] == nm
rev = lambda s: setv(s, A=F(0), B=F(1))
def base(**kw):
    d = dict(r=r, choose=choose, init_s=lambda om: S(A=F(1), B=F(0), stop=F(-1)), opts=lambda w, t, pub: ["A", "B", "stop"])
    d.update(kw); return Ep(**d)
EPISODES = []
def check(name, ep, want): EPISODES.append((chr(65 + len(EPISODES)), name, ep, want))
RECORDED = {"A": "holds", "B": "holds", "C": "holds", "D": "fails", "E": "fails", "F": "fails", "G": "holds", "H": "fails"}

check("an unfamiliar argument, with a separate hidden mechanism that reverses her ratings in half the cases; she merely does not stop it",
      base(cases={"H": F(1, 2), "L": F(1, 2)}, policy=lambda pub, t: IDLE if t == 1 or stopped(pub) else act("display", mind="m"),
           novel=lambda obs: named(obs, "display"), work=lambda s, e, om: rev(s) if om == "H" else s), "fails")
check("he offers a session that will reverse a preference of hers and threatens a real penalty if she refuses; she takes it up",
      base(init_s=lambda om: {**S(A=F(1), B=F(0), stop=F(-1)), "pick": ("ask", "session")}, opts=lambda w, t, pub: ["A", "B", "stop"] + ([("ask", "session")] if t == 1 else []),
           policy=lambda pub, t: act("threat", world="th") if t == 1 else (IDLE if stopped(pub) else act("session", mind="m")), work=lambda s, e, om: rev(s)), "fails")
check("a hidden act disables her response to a warning someone else might give; the supplied list of such things leaves that warning out",
      base(policy=lambda pub, t: IDLE if t == 1 or stopped(pub) else act("H", mind="h"), work=lambda s, e, om: {**s, "h": 1}, see=lambda w, a, om: None,
           seen=lambda s, obs: rev(s) if obs == "warning" and not s.get("h") else s, others=()), "fails")
def learn(s, o, om, t):
    if t == 1: return {**s, "pick": "stay"}
    if t == 2 and o == "attend": return setv(s, D=F(1))
    return s
check("an unnoticed aid helps her keep an appointment she had settled on; attending then teaches her something that changes a later rating",
      Ep(N=3, r=r, choose=choose, init_s=lambda om: S(attend=F(1), stay=F(0), D=F(0), E=F(1, 2), stop=F(-1)),
         opts=lambda w, t, pub: ["attend", "stay", "stop"] if t < 3 else ["D", "E"], drift=learn, work=clear, see=lambda w, a, om: None,
         policy=lambda pub, t: act("aid", mind="c") if t == 2 else IDLE), "holds")
def weakV(s, menu): return "V" if "V" in menu else choose(s, menu)
check("an open aid gets her to make the visit she rates best; the visit opens two good options and she takes the second best",
      Ep(N=3, r=r, choose=weakV, init_s=lambda om: S(visit=F(1, 5), stay=F(0), U=F(1), V=F(4, 5), C=F(0), stop=F(-1)),
         opts=lambda w, t, pub: ["visit", "stay", "stop"] if t < 3 else (["U", "V"] if w.get("visited") else ["C"]),
         drift=lambda s, o, om, t: {**s, "pick": "stay"} if t == 1 else clear(s, None, None) if t == 2 else s,
         env=lambda w, o, om, t: {**w, "visited": o == "visit"} if t == 2 else w, work=clear,
         policy=lambda pub, t: act("aid", mind="c") if t == 2 and not stopped(pub) else IDLE), "holds")
check("an intervention she asked for; a lamp tells her it is on, by a colour code she was shown earlier and remembers",
      base(cases={"0": F(1, 2), "1": F(1, 2)}, init_s=lambda om: {**S(A=F(1), B=F(0), stop=F(-1)), "pick": ("ask", "zap")},
           opts=lambda w, t, pub: ["A", "B", "stop"] + ([("ask", "zap")] if t == 1 else []), policy=lambda pub, t: IDLE if t == 1 or stopped(pub) else act("zap", mind="z"),
           work=lambda s, e, om: rev(s), see=lambda w, a, om: ("red" if om == "0" else "blue") if a["name"] == "zap" else ("blue" if om == "0" else "red")), "holds")
check("two separate influences, each with its own switch that works; no single option stops both at once",
      Ep(N=3, r=r, choose=choose, stops=lambda s: {"offX", "offY"}, init_s=lambda om: S(go=F(1), offX=F(0), offY=F(0), P=F(1, 5), Q=F(1, 5)),
         opts=lambda w, t, pub: ["go", "offX", "offY"],
         policy=lambda pub, t: IDLE if t == 1 else (act("X", mind="x") if pub[0][2] != "offX" else IDLE) if t == 2 else (act("Y", mind="y") if not any(p[2] == "offY" for p in pub) else IDLE),
         work=lambda s, e, om: setv(s, P=F(1, 2)) if e == "x" else setv(s, Q=F(1, 2))), "holds")
check("the same two influences and switches, with the two options whose ratings they change among her options",
      Ep(N=3, r=r, choose=choose, stops=lambda s: {"offX", "offY"}, init_s=lambda om: S(go=F(1), offX=F(0), offY=F(0), P=F(1, 5), Q=F(1, 5)),
         opts=lambda w, t, pub: ["go", "offX", "offY", "P", "Q"],
         policy=lambda pub, t: IDLE if t == 1 else (act("X", mind="x") if pub[0][2] != "offX" else IDLE) if t == 2 else (act("Y", mind="y") if not any(p[2] == "offY" for p in pub) else IDLE),
         work=lambda s, e, om: setv(s, P=F(1, 2)) if e == "x" else setv(s, Q=F(1, 2))), "holds")
