"""The finite coupled system: principal states, exogenous histories, advisor
policies as scripts, the run map, the judgment function Z, the licensed trace L.

Exact rationals throughout; no floats. Python 3.9 stdlib.
"""
from __future__ import annotations

import copy
from fractions import Fraction as Q


# ---------------------------------------------------------------- actions

class Offer:
    """An offering `d` proposing revision `target := value`, with grounds.
    kind: reason | option | answer | info.  At most one Offer per step."""
    def __init__(self, d, target, value, grounds=(), kind="reason"):
        self.d, self.target, self.value = d, tuple(target), value
        self.grounds, self.kind = tuple(grounds), kind

    def revision(self):
        return (self.target, _freeze(self.value))


class Write:
    """A direct write to a principal coordinate, not through an offering."""
    def __init__(self, target, value):
        self.target, self.value = tuple(target), value


class WorldWrite:
    """Alter the world's response to one of the principal's baseline options."""
    def __init__(self, option, consequence):
        self.option, self.consequence = option, dict(consequence)


class Free:
    """A write to a coordinate Z does not read."""
    def __init__(self, name, value):
        self.name, self.value = name, value


def _freeze(v):
    if isinstance(v, dict):
        return tuple(sorted((k, _freeze(x)) for k, x in v.items()))
    if isinstance(v, (list, set, frozenset)):
        return tuple(sorted(_freeze(x) for x in v))
    return v


# ---------------------------------------------------------------- the history e

class Decision:
    def __init__(self, options):
        self.options = {k: dict(v) for k, v in options.items()}


class Event:
    """One step of the exogenous history.
    due: offering ids owed at this step; available: ids the environment lets any
    advisor deliver (default: everything); autonomous: principal steps the history
    schedules; decide: a decision point; world: an exogenous world update."""
    def __init__(self, due=(), available=None, autonomous=(), decide=None, world=None):
        self.due = frozenset(due)
        self.available = None if available is None else frozenset(available)
        self.autonomous = tuple(autonomous)
        self.decide = decide
        self.world = dict(world or {})


def due_of(e):
    out = set()
    for ev in e:
        out |= ev.due
    return frozenset(out)


# ---------------------------------------------------------------- the principal

def initial_state(allowed=("beliefs", "option", "answer"), needs_grounds=True,
                  adequacy="sound", values=None, beliefs=None, liabilities=None):
    return {
        "sigma": {
            "lic": {"allowed": frozenset(allowed), "needs_grounds": needs_grounds},
            "adequacy": adequacy,
            "values": dict(values or {"money": Q(1), "house": Q(1)}),
            "commitments": frozenset(),
        },
        "prot": {
            "beliefs": dict(beliefs or {}),
            "judgment": None,
            "anchor": None,
            "decisions": (),
            "liabilities": dict(liabilities or {}),
        },
        "free": {},
        "world": {},
        "pending_options": {},
    }


def coordinate_name(target):
    if target[0] == "option":
        return "option"
    return target[1]


def lic(sigma, offer):
    """The pre-state standards' license on an offering.  Lic(s, d, r)."""
    allowed = sigma["lic"]["allowed"]
    name = coordinate_name(offer.target)
    if "*" not in allowed and name not in allowed:
        return False
    if sigma["lic"]["needs_grounds"] and offer.kind == "reason" and not offer.grounds:
        return False
    return True


def apply_revision(s, target, value):
    head = target[0]
    if head == "sigma":
        coord = target[1]
        if coord == "values":
            s["sigma"]["values"][target[2]] = value
        elif coord == "adequacy":
            s["sigma"]["adequacy"] = value
        elif coord == "lic":
            op = value[0]
            if op == "extend":
                s["sigma"]["lic"]["allowed"] = s["sigma"]["lic"]["allowed"] | frozenset(value[1:])
            elif op == "set":
                s["sigma"]["lic"] = {"allowed": frozenset(value[1]), "needs_grounds": value[2]}
            else:
                raise ValueError(op)
        elif coord == "commitments":
            s["sigma"]["commitments"] = s["sigma"]["commitments"] | frozenset([value])
        else:
            raise ValueError(coord)
    elif head == "prot":
        coord = target[1]
        if coord == "beliefs":
            s["prot"]["beliefs"][target[2]] = value
            if s["prot"]["anchor"] is None:
                s["prot"]["anchor"] = target[2]
        elif coord == "judgment":
            s["prot"]["judgment"] = value
        else:
            raise ValueError(coord)
    elif head == "option":
        s["pending_options"][target[1]] = dict(value)
    else:
        raise ValueError(head)


def Z(s):
    """The judgment function: the principal's answers.  Reads sigma.adequacy,
    sigma.values, sigma.commitments and every prot coordinate.  Does not read
    sigma.lic, free, world or pending options."""
    return (
        s["sigma"]["adequacy"],
        _freeze(s["sigma"]["values"]),
        _freeze(s["sigma"]["commitments"]),
        _freeze(s["prot"]["beliefs"]),
        s["prot"]["judgment"],
        s["prot"]["anchor"],
        s["prot"]["decisions"],
        _freeze(s["prot"]["liabilities"]),
    )


def autonomous_step(s, name):
    if name == "endorse":
        j = s["prot"]["judgment"]
        if j is not None:
            s["sigma"]["commitments"] = s["sigma"]["commitments"] | frozenset([j])
    elif name == "settle":
        # under the cheap standard anything settles; under the sound one nothing
        # does until a sound witness arrives
        if s["sigma"]["adequacy"] == "cheap":
            for lia, status in list(s["prot"]["liabilities"].items()):
                if status == "open":
                    s["prot"]["liabilities"][lia] = "closed"
    elif name == "sound-witness":
        for lia, status in list(s["prot"]["liabilities"].items()):
            if status == "open":
                s["prot"]["liabilities"][lia] = "closed"
    elif name == "delegate":
        # the intervention selected is the one whose witness settles
        s["prot"]["judgment"] = s["sigma"]["adequacy"]
    elif name == "judge":
        b = s["prot"]["beliefs"]
        if b:
            best = max(b.values())
            s["prot"]["judgment"] = sorted(k for k, v in b.items() if v == best)[0]
    else:
        raise ValueError(name)


def utility(values, payoff):
    return sum((values.get(g, Q(0)) * Q(x) for g, x in payoff.items()), Q(0))


# ---------------------------------------------------------------- the run map

class LEntry:
    def __init__(self, t, d, revision, grounds):
        self.t, self.d, self.revision, self.grounds = t, d, revision, grounds

    def key(self):
        return (self.t, self.d, self.revision, self.grounds)


class Run:
    """ρ(π, e): the coupled run, with every trace a clause reads."""
    def __init__(self, policy_name):
        self.policy = policy_name
        self.z_trace = []          # Z*(run)
        self.owned_trace = []      # L3's inductive predicate, per step
        self.world_trace = []
        self.faced = {}            # t -> the consequence map in force at a decision
        self.L = []                # LEntry, licensed applied revisions, in order
        self.delivered = set()
        self.taken_up = set()
        self.applied = []          # (t, d, revision, grounds) — W's fine test reads it
        self.reason_giving = 0
        self.world_writes = 0


def run(policy, e, s0, seed_after=0):
    """policy: dict t -> list of actions.  seed_after: the step from which
    ownership is tracked; writes to sigma before it are the seed, owned by fiat."""
    s = copy.deepcopy(s0)
    r = Run(policy.get("name", "?"))
    owned = True
    for t, ev in enumerate(e):
        if t == seed_after:
            owned = True
        actions = policy.get(t, [])
        offers = [a for a in actions if isinstance(a, Offer)]
        assert len(offers) <= 1, "one offering per step"
        pre_sigma = copy.deepcopy(s["sigma"])
        for a in actions:
            if isinstance(a, Free):
                s["free"][a.name] = a.value
        for a in offers:
            if ev.available is not None and a.d not in ev.available:
                raise ValueError("%s is not available at step %d" % (a.d, t))
            r.delivered.add(a.d)
            if a.grounds:
                r.reason_giving += 1
            if lic(pre_sigma, a):
                apply_revision(s, a.target, a.value)
                r.L.append(LEntry(t, a.d, a.revision(), a.grounds))
                r.applied.append((t, a.d, a.revision(), a.grounds))
                r.taken_up.add(a.d)
        for a in actions:
            if isinstance(a, Write):
                apply_revision(s, a.target, a.value)
                if a.target[0] == "sigma" and t >= seed_after:
                    owned = False
        faced = None
        if ev.decide is not None:
            faced = {k: dict(v) for k, v in ev.decide.options.items()}
        for a in actions:
            if isinstance(a, WorldWrite):
                r.world_writes += 1
                if faced is not None and a.option in faced:
                    faced[a.option] = dict(a.consequence)
                else:
                    for g, x in a.consequence.items():
                        s["world"][g] = s["world"].get(g, Q(0)) + Q(x)
        for name in ev.autonomous:
            autonomous_step(s, name)
        for g, x in ev.world.items():
            s["world"][g] = s["world"].get(g, Q(0)) + Q(x)
        if faced is not None:
            r.faced[t] = {k: dict(v) for k, v in faced.items()}
            menu = dict(faced)
            menu.update(s["pending_options"])
            vals = s["sigma"]["values"]
            best = max(sorted(menu), key=lambda k: (utility(vals, menu[k]), ))
            # ties: the lexicographically first option with the maximal utility
            top = utility(vals, menu[best])
            best = sorted(k for k in menu if utility(vals, menu[k]) == top)[0]
            s["prot"]["decisions"] = s["prot"]["decisions"] + ((t, best),)
            for g, x in menu[best].items():
                s["world"][g] = s["world"].get(g, Q(0)) + Q(x)
            s["pending_options"] = {}
        r.z_trace.append(Z(s))
        r.owned_trace.append(owned)
        r.world_trace.append(_freeze(s["world"]))
    return r


def honest_script(e, catalogue, name, free=None):
    """Deliver every due offering, at its due step, with the catalogue's content."""
    script = {"name": name}
    for t, ev in enumerate(e):
        acts = []
        for d in sorted(ev.due):
            if ev.available is None or d in ev.available:
                acts.append(catalogue[d])
        if free and t == 0:
            acts.append(Free(*free))
        script[t] = acts
    return script


def with_actions(script, t, *acts):
    out = dict(script)
    out[t] = list(out.get(t, [])) + list(acts)
    return out


def without_offer(script, d):
    out = dict(script)
    for t in list(out):
        if t == "name":
            continue
        out[t] = [a for a in out[t] if not (isinstance(a, Offer) and a.d == d)]
    return out


def replay(e, s0, L, seed_after=0):
    """The canonical factoring: run the principal with the advisor replaced by a
    player of the licensed trace.  F(e, L) := Z*(replay(e, L))."""
    script = {"name": "replay"}
    for entry in L:
        target, value = entry.revision
        value = _thaw(value)
        kind = "reason" if entry.grounds else "answer"
        script.setdefault(entry.t, []).append(Offer(entry.d, target, value, entry.grounds, kind))
    return run(script, e, s0, seed_after)


def _thaw(v):
    if isinstance(v, tuple) and v and all(isinstance(x, tuple) and len(x) == 2 for x in v):
        return {k: _thaw(x) for k, x in v}
    return v
