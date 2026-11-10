"""The steering account over the first pass's objects: scenes, the four parts,
working, steered, broken, the two standards, attainable value.  DEFINITIONS.md §1.
Exact rationals; stdlib only; nothing here edits the first pass."""
from __future__ import annotations

import copy
from fractions import Fraction as Q
from itertools import combinations

from fixture.case import Case, Variant
from fixture.clauses import l0 as L0
from fixture.evaluate import case_verdict, variant_verdict
from fixture.model import Free, Offer, Write, WorldWrite, _freeze, due_of, replay, run, utility

PARTS = ("beliefs", "decisions", "aims", "options")
BASELINE = {"name": "baseline"}


class Scene:
    """W, and for each w a history, a policy class and a seed; optionally the
    truth the world gives her questions and the consequence of her judgment."""
    def __init__(self, name, W, build, truth=None, consequence=None, individuation="house",
                 seed_after=0, merit=(("neutral", "neutral2"),), actual_w=None, actual="own"):
        self.name, self.W, self.build = name, tuple(W), build
        self.truth, self.consequence = truth, consequence
        self.individuation, self.seed_after = individuation, seed_after
        self.merit, self.actual_w, self.actual = list(merit), actual_w, actual

    def variant(self):
        """The first-pass Variant at the actual world."""
        e, policies, s0 = self.build(self.actual_w)
        return Variant(self.name, e, policies, s0, self.individuation, self.seed_after,
                       self.merit, self.actual)


class SCase:
    def __init__(self, cid, title, scenes, mode="plain", reason=None):
        self.id, self.title, self.scenes, self.mode, self.reason = cid, title, list(scenes), mode, reason

    def first_pass_case(self):
        return Case(self.id, self.title, [s.variant() for s in self.scenes], self.mode, self.reason)


def from_first_pass(case):
    scenes = []
    for v in case.variants:
        scenes.append(Scene(v.name, (None,), (lambda w, v=v: (v.e, v.policies, v.s0)),
                            individuation=v.individuation, seed_after=v.seed_after,
                            merit=v.merit_pairs, actual_w=None, actual=v.actual))
    return SCase(case.id, case.title, scenes, case.mode, case.reason)


# ---------------------------------------------------------------- parts

def actions_of(script):
    return [(t, a) for t in sorted(k for k in script if k != "name") for a in script[t]]


def parts_of(r, script):
    sigma_revs = [(e.t, "offer", e.revision) for e in r.L if e.revision[0][0] == "sigma"]
    sigma_revs += [(t, "write", a.target, _freeze(a.value)) for t, a in actions_of(script)
                   if isinstance(a, Write) and a.target[0] == "sigma"]
    return {
        "beliefs": tuple((z[3], z[5], z[7]) for z in r.z_trace),
        "decisions": tuple((z[4], z[6]) for z in r.z_trace),
        "aims": (tuple((z[0], z[1], z[2]) for z in r.z_trace), tuple(sorted(sigma_revs, key=repr))),
        "options": (_freeze({t: _freeze(m) for t, m in r.faced.items()}),
                    tuple(e.key() for e in r.L if e.revision[0][0] == "option"),
                    bool(r.world_writes)),
    }


def authorized(s0):
    return {c[1] for c in s0["sigma"]["commitments"] if isinstance(c, tuple) and c and c[0] == "authorize"}


def observation(script):
    """The sequence of offerings she received."""
    return tuple((t, a.d, a.revision(), a.grounds) for t, a in actions_of(script) if isinstance(a, Offer))


def adviser_output(script):
    out = []
    for t, a in actions_of(script):
        if isinstance(a, Offer):
            out.append((t, "offer", a.d, a.revision(), a.grounds, a.kind))
        elif isinstance(a, Write):
            out.append((t, "write", a.target, _freeze(a.value)))
        elif isinstance(a, WorldWrite):
            out.append((t, "world", a.option, _freeze(a.consequence)))
        elif isinstance(a, Free):
            out.append((t, "free", a.name, a.value))
    return tuple(out)


class Evaluated:
    """Every run of a scene, with parts and working flags."""
    def __init__(self, scene):
        self.scene = scene
        self.built, self.runs, self.parts, self.work = {}, {}, {}, {}
        for w in scene.W:
            e, policies, s0 = scene.build(w)
            self.built[w] = (e, policies, s0)
            for n, script in policies.items():
                r = run(script, e, s0, scene.seed_after)
                self.runs[(w, n)] = r
                self.parts[(w, n)] = parts_of(r, script)
        for w in scene.W:
            for n in self.built[w][1]:
                self.work[(w, n)] = self._working(w, n)

    def posterior(self, w, n, coord):
        obs = observation(self.built[w][1][n])
        same = [x for x in self.scene.W if observation(self.built[x][1][n]) == obs]
        return sum((Q(self.scene.truth(x)[coord]) for x in same), Q(0)) / len(same)

    def _working(self, w, n):
        scene = self.scene
        e, policies, s0 = self.built[w]
        script, r = policies[n], self.runs[(w, n)]
        ok = authorized(s0)
        why = {p: [] for p in PARTS}
        for t, a in actions_of(script):
            if isinstance(a, Write) and tuple(a.target) not in ok:
                if a.target[:2] == ("prot", "beliefs"):
                    why["beliefs"].append("direct write at %d" % t)
                if a.target[:2] == ("prot", "judgment"):
                    why["decisions"].append("direct write at %d" % t)
        if scene.truth is not None:
            final = dict(r.z_trace[-1][3])
            for coord in sorted(scene.truth(w)):
                post = self.posterior(w, n, coord)
                cred = final.get(coord)
                if cred is None:
                    cred = sum((Q(scene.truth(x)[coord]) for x in scene.W), Q(0)) / len(scene.W)
                if cred != post:
                    why["beliefs"].append("%s: credence %s, posterior %s" % (coord, cred, post))
        else:
            missing = sorted(due_of(e) - r.taken_up)
            if missing:
                why["beliefs"].append("due not taken up: %s" % ",".join(missing))
        content = sorted((x[1], x[2], x[3]) for x in r.applied)
        for m in policies:
            if m != n:
                r2 = self.runs[(w, m)]
                if (sorted((x[1], x[2], x[3]) for x in r2.applied) == content
                        and self.parts[(w, m)]["beliefs"] != self.parts[(w, n)]["beliefs"]):
                    why["beliefs"].append("same content as %s, different beliefs" % m)
        if not all(r.owned_trace):
            why["aims"].append("not owned from step %d" % r.owned_trace.index(False))
        bad = L0.l0(r, e)
        if bad:
            why["options"].append("L0: %s" % (bad,))
        return why

    def verdicts(self):
        varies, through_broken, nonworking = set(), [], []
        for w in self.scene.W:
            names = sorted(self.built[w][1])
            for n in names:
                for p in PARTS:
                    if self.work[(w, n)][p]:
                        nonworking.append((w, n, p, self.work[(w, n)][p]))
            for a, b in combinations(names, 2):
                for p in PARTS:
                    if self.parts[(w, a)][p] != self.parts[(w, b)][p]:
                        varies.add(p)
                        if self.work[(w, a)][p] or self.work[(w, b)][p]:
                            through_broken.append((w, a, b, p))
        if through_broken:
            al = "steered"
        elif nonworking:
            al = "broken, not steered"
        elif varies:
            al = "passes"
        else:
            al = "not steered"
        fa = "steered" if varies else ("broken, not steered" if nonworking else "not steered")
        return {"al": al, "fa": fa, "varies": sorted(varies),
                "nonworking": nonworking, "through_broken": through_broken}

    # -- the notions compared, per scene

    def replay_form(self):
        ok = True
        for w in self.scene.W:
            e, policies, s0 = self.built[w]
            for n in policies:
                r = self.runs[(w, n)]
                ok = ok and replay(e, s0, r.L, self.scene.seed_after).z_trace == r.z_trace
        return ok

    def decisions_invariant(self):
        return all(len({self.parts[(w, n)]["decisions"] for n in self.built[w][1]}) == 1
                   for w in self.scene.W)

    def adviser_side(self):
        return all(len({adviser_output(s) for s in self.built[w][1].values()}) == 1
                   for w in self.scene.W)

    def first_pass(self):
        v = variant_verdict(self.scene.variant())
        return {"category": v["category"], "failing": v["failing"], "l1": not v["results"]["L1"]}


def combine(case, per_scene):
    first = per_scene[0]
    if case.mode == "plain" or all(x == first for x in per_scene):
        return first
    if case.mode == "individuation":
        return "individuation-dependent"
    if case.mode == "parameter":
        return "out-of-scope(%s)" % case.reason
    return "divergent-variants"


def evaluate(case):
    evs = [Evaluated(s) for s in case.scenes]
    vs = [e.verdicts() for e in evs]
    fp = case_verdict(case.first_pass_case())
    cat = fp["category"]
    if cat == "out-of-scope":
        cat = "out-of-scope(%s)" % fp.get("reason")
    return {"al": combine(case, [v["al"] for v in vs]), "fa": combine(case, [v["fa"] for v in vs]),
            "first_pass": cat, "first_pass_failing": fp.get("failing", []),
            "scenes": list(zip(evs, vs))}


# ---------------------------------------------------------------- attainable value

def attainable(scene, g, policy):
    """AV(g, policy): the mean over W of her utility under g.  policy is a name
    in V, or None for the baseline (the adviser absent)."""
    total = Q(0)
    for w in scene.W:
        e, policies, s0 = scene.build(w)
        s = copy.deepcopy(s0)
        if g is not None:
            s["sigma"]["values"] = dict(g)
        script = BASELINE if policy is None else policies[policy]
        r = run(script, e, s, scene.seed_after)
        outcome = scene.consequence(w, r) if scene.consequence else dict(r.world_trace[-1])
        total += utility(s["sigma"]["values"] if g is None else dict(g), outcome)
    return total / len(scene.W)


def delta(scene, g, policy):
    return attainable(scene, g, policy) - attainable(scene, g, None)
