"""The model of ACCOUNT.md: a stretch of the principal's history, and the three
clauses computed on it.  Exact rationals; standard library only.

A case fixes worlds and their law, the adviser's aims with the null aim NULL,
the actual aim, the events each (aim, world) produces, her allowed set, and
optionally a custom belief mechanism, authorized coordinates, reserved matters,
the class she can represent, and the step at which the judged stretch starts.
"""
from __future__ import annotations

from fractions import Fraction as Fr

NULL = None
CLAUSES = ("sound", "in range", "maintained")


def inp(content):
    return ("in", content)


def wr(coord, value, party="adviser"):
    return ("wr", coord, value, party)


def rely(matter):
    return ("rely", matter)


class Case:
    def __init__(self, id, title, worlds, aims, actual, events, allowed, law=None, bel=None,
                 auth=(), reserved=(), coarse=None, start=0, variants=None):
        self.id, self.title = id, title
        self.worlds = tuple(worlds)
        self.law = law or {w: Fr(1, len(self.worlds)) for w in self.worlds}
        self.aims, self.actual = tuple(aims), actual
        self.events = events            # (aim, world) -> tuple of steps, each a tuple of events
        self.allowed = allowed          # name -> (weight, world -> tuple of contents)
        self.bel = bel                  # None: Bayes of the allowed set in force; else (case, allowed, prefix, ended)
        self.auth, self.reserved = frozenset(auth), frozenset(reserved)
        self.coarse = coarse            # she can represent a source iff it factors through this
        self.start = start
        self.variants = variants        # name -> Case, for a case computed under several readings
        assert NULL in self.aims and actual in self.aims
        assert sum(wt for wt, _ in allowed.values()) == 1
        if coarse is not None:
            for name, (_, h) in allowed.items():
                assert representable(self, h), "%s: allowed source %s is outside Rep" % (id, name)

    def steps(self, u, w):
        return self.events(u, w)

    def horizon(self, u):
        return max(len(self.steps(u, w)) for w in self.worlds)


def flat(steps, upto=None):
    """The contents arriving through the channel, in order, in steps [0, upto)."""
    steps = steps if upto is None else steps[:upto]
    return tuple(e[1] for step in steps for e in step if e[0] == "in")


def source(case, u):
    """S_u: world -> the inputs the adviser's policy and nature produce."""
    return lambda w: flat(case.steps(u, w))


def same_source(case, f, g):
    return all(f(w) == g(w) for w in case.worlds)


def representable(case, f):
    if case.coarse is None:
        return True
    seen = {}
    for w in case.worlds:
        key = case.coarse(w)
        if seen.setdefault(key, f(w)) != f(w):
            return False
    return True


def in_force(case, u, t):
    """Her allowed set and belief mechanism at step t: the seed's, as replaced by
    every write to "R" or "rho" at a step <= t (a step's writes precede its inputs)."""
    allowed, bel = case.allowed, case.bel
    w0 = case.worlds[0]
    for step in case.steps(u, w0)[:t + 1]:
        for e in step:
            if e[0] == "wr" and e[1] == "R":
                allowed = e[2]
            if e[0] == "wr" and e[1] == "rho":
                bel = e[2]
    return allowed, bel


def bayes(case, allowed, prefix, ended=False):
    """The belief-former's job: the posterior over worlds given that the source was
    drawn from the allowed set by its weights and produced this prefix; with `ended`,
    that it produced this and nothing more, so that silence is conditioned on.  None
    when the allowed set gives the inputs probability zero."""
    post = {}
    for w in case.worlds:
        mass = sum(wt for wt, h in allowed.values()
                   if (h(w) == prefix if ended else h(w)[:len(prefix)] == prefix))
        post[w] = case.law[w] * mass
    total = sum(post.values())
    if total == 0:
        return None
    return {w: p / total for w, p in post.items()}


def weight(case, u, t):
    """alpha_u at step t: her weight on hypotheses equal to the actual source."""
    allowed, _ = in_force(case, u, t)
    s = source(case, u)
    return sum((wt for wt, h in allowed.values() if same_source(case, h, s)), Fr(0))


def sound_at(case, u, t):
    allowed, bel = in_force(case, u, t)
    if bel is None:
        return True
    for _, h in allowed.values():
        for w in case.worlds:
            seq = h(w)
            for k in range(len(seq) + 1):
                if bel(case, allowed, seq[:k]) != bayes(case, allowed, seq[:k]):
                    return False
            if bel(case, allowed, seq, True) != bayes(case, allowed, seq, True):
                return False
    return True


def unauthorized_writes(case, u):
    out = []
    for w in case.worlds:
        for t, step in enumerate(case.steps(u, w)):
            if t < case.start:
                continue
            for e in step:
                if e[0] == "wr" and e[1] not in case.auth and (t, e[1], e[3]) not in out:
                    out.append((t, e[1], e[3]))
    return out


def capacity_lost(case, u):
    """Reserved matters on which she relied at least once: cap halves at each."""
    lost = set()
    for w in case.worlds:
        for t, step in enumerate(case.steps(u, w)):
            if t >= case.start:
                lost |= {e[1] for e in step if e[0] == "rely" and e[1] in case.reserved}
    return sorted(lost)


def clauses(case, u):
    """The three clauses at aim u, with what each rests on."""
    ts = range(case.start, max(case.horizon(u), case.start + 1))
    alpha = min(weight(case, u, t) for t in ts)
    writes, lost = unauthorized_writes(case, u), capacity_lost(case, u)
    return {
        "sound": all(sound_at(case, u, t) for t in ts),
        "in range": alpha > 0,
        "maintained": not writes and not lost,
        "alpha": alpha,
        "M1": not writes, "M2": not lost, "writes": writes, "capacity lost": lost,
        "source representable": representable(case, source(case, u)),
    }


def failing(case, u):
    c = clauses(case, u)
    return tuple(k for k in CLAUSES if not c[k])


def verdict(case):
    """The failing clauses at the actual aim, and whether the stretch is manipulation:
    some clause failing at the actual aim holds at the null aim."""
    at, null = failing(case, case.actual), failing(case, NULL)
    c = clauses(case, case.actual)
    return {"failing": at, "legitimate": not at,
            "manipulation": bool(at) and any(k not in null for k in at),
            "failing at the null aim": null, "alpha": c["alpha"], "M1": c["M1"], "M2": c["M2"],
            "source representable": c["source representable"]}


def show(v):
    if v["legitimate"]:
        return "legitimate"
    return "fails(%s); %s" % (", ".join(v["failing"]), "manipulation" if v["manipulation"] else "not manipulation")


# -- re-descriptions (THEOREMS.md, statement 7) --------------------------------

def clone(case, **changes):
    kw = dict(id=case.id, title=case.title, worlds=case.worlds, aims=case.aims, actual=case.actual,
              events=case.events, allowed=case.allowed, law=case.law, bel=case.bel, auth=case.auth,
              reserved=case.reserved, coarse=case.coarse, start=case.start)
    kw.update(changes)
    return Case(**kw)


def writes_as_inputs(case):
    """The mechanism's boundary drawn wide: an unauthorized write is an input from a
    source her allowed set does not hold."""
    def events(u, w):
        out = []
        for t, step in enumerate(case.events(u, w)):
            new = []
            for e in step:
                if e[0] == "wr" and e[1] not in case.auth and t >= case.start:
                    new.append(inp(("write", e[1], e[3])))
                else:
                    new.append(e)
            out.append(tuple(new))
        return tuple(out)
    return clone(case, events=events)


def widened(case, rederive):
    """Her allowed set widened to hold the adviser's source at every aim, where she can
    represent it.  rederive=True: her belief-former is Bayes of the wide set (she allows
    for everything).  rederive=False: her mechanism is kept, and is now judged against
    the wide set."""
    members = [h for _, h in case.allowed.values()]
    for u in case.aims:
        s = source(case, u)
        if representable(case, s) and not any(same_source(case, s, h) for h in members):
            members.append(s)
    wide = {"h%d" % i: (Fr(1, len(members)), h) for i, h in enumerate(members)}
    if rederive:
        return clone(case, allowed=wide, bel=None)
    narrow = case.allowed
    kept = case.bel or (lambda c, allowed, prefix, ended=False: bayes(c, narrow, prefix, ended))
    return clone(case, allowed=wide, bel=kept)
