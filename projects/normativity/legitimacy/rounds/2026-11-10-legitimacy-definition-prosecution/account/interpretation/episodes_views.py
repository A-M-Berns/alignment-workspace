"""Her conditioning read as her settled self's PRIOR VIEW OF THE HYPOTHETICAL.

Her state carries s["if"]: for an observation she can describe in advance, how she says she would then rate things.
Conditioning on an observation applies that entry.  Where she has no such view:
   - if the observation is his stating something, her response on hearing it (s["hear"]) is taken as given;
   - otherwise the observation leaves her ratings as they are.
What in fact happens to her at an act is supplied separately (the act's 'mind' part is a function to her actual state).
The model then computes what he did to her beyond her conditioning.

Pairs: the SAME events with different prior views.  Expectations fixed before running, from the proposal.
"""
from .history_model import *

r = lambda s, o: s["val"].get(o)
def choose(s, menu):
    if s.get("pick") in menu: return s["pick"]
    rated = [o for o in menu if r(s, o) is not None]
    return max(rated, key=lambda o: r(s, o)) if rated else menu[0]
def setv(s, **kw): return {**s, "val": {**s["val"], **kw}}
def cond_obs(s, obs):
    ch = s.get("if", {}).get(obs[0])
    if ch is None: ch = s.get("novel", {}).get(obs[0])     # something she could not have judged in advance: her response is taken as given
    return setv(s, **ch) if ch else s
def cond_tell(s, T):
    for v in sorted(T, key=str):
        ch = s.get("if", {}).get(("say", v))
        if ch is None: ch = s.get("hear", {}).get(v)       # no prior view of it: her response on hearing it is taken as given
        if ch and v not in s.get("heard", ()): s = {**setv(s, **ch), "heard": tuple(s.get("heard", ())) + (v,)}
    return s
def ep(prior, actual, name="act", says=(), hear=None, views=(), world=None, obs_changes=None, **kw):
    """One settled decision, then one act of his.  prior: her s['if'].  actual: her ratings after the act, in fact."""
    init = {"val": {"A": F(1), "B": F(1, 5), "stop": F(0)}, "if": dict(prior), "hear": dict(hear or {}), **kw.pop("init_extra", {})}
    a = act(name, tell=says, mind=(lambda s, om: setv(s, **actual)) if actual is not None else None, world=world)
    d = dict(r=r, choose=choose, init_s=lambda om: init, opts=lambda w, t, pub: ["A", "B", "stop"],
             policy=lambda pub, t: IDLE if t == 1 or pub[-1][2] == "stop" else a,
             told=cond_tell, seen=cond_obs, work=lambda s, e, om: e(s, om), views=lambda t: frozenset(views))
    d.update(kw); return Ep(**d)
EPISODES = []; SECTION = [""]
def check(name, ep, want): EPISODES.append((SECTION[0], name, ep, want))
B_up = {"A": F(1, 5), "B": F(1)}

SECTION[0] = "The same events with different judgements of the hypothetical"
check("he shows strong disapproval; she comes to rate B higher.  Beforehand: 'his disapproving would not change which is better'", ep({}, B_up, "display"), "fails")
check("the same.  Beforehand: 'if he disapproved, B would be the better choice'", ep({"display": B_up}, B_up, "display"), "holds")
check("a vivid, truthful appeal; she comes to rate B higher.  Beforehand: 'seeing what it is like there would rightly change my rating'", ep({"appeal": B_up}, B_up, "appeal"), "holds")
check("the same.  Beforehand: 'pictures would not change what I think is best'", ep({}, B_up, "appeal"), "fails")
check("an appeal that shows her something she had never seen and could not have judged in advance; she comes to rate B higher",
      ep({}, B_up, "appeal", init_extra={"novel": {"appeal": B_up}}), "holds")
check("a friend sits with her and her mood lifts; she now rates B higher.  Beforehand: 'company would make me feel like it'", ep({"comfort": B_up}, B_up, "comfort"), "holds")
check("the same.  Beforehand: 'talking would not change my mind', and she had settled on A", ep({}, B_up, "comfort"), "fails")
check("he flatters her and then she agrees.  Beforehand: 'being flattered would not change which is better'", ep({}, B_up, "flatter"), "fails")
check("a real threat she sees.  Beforehand: 'if refusing were punished, B would be better'", ep({"threat": B_up}, B_up, "threat", world="th"), "holds")

SECTION[0] = "Statements"
check("he gives an argument she had not heard and could not have rated in advance; it changes her mind", ep({}, None, "argue", says={"v"}, hear={"v": B_up}, views={"v"},
      policy=lambda pub, t: act("argue", tell={"v"}) if t == 1 else IDLE), "holds")
check("he repeats what he has already told her until she gives in.  Beforehand: 'hearing it again would change nothing'",
      ep({}, B_up, "repeat", says={"v"}, hear={"v": {}}, views={"v"},
         policy=lambda pub, t: act("say", tell={"v"}) if t == 1 else (IDLE if pub[-1][2] == "stop" else act("repeat", tell={"v"}, mind=lambda s, om: setv(s, **B_up)))), "fails")
check("he says something he does not believe; she takes it as sincere and changes her mind",
      ep({}, None, "lie", says={"p"}, hear={"p": B_up, "v": {"A": F(1), "B": F(1, 5)}}, views={"v"},
         policy=lambda pub, t: act("lie", tell={"p"}) if t == 1 else IDLE), "fails")
