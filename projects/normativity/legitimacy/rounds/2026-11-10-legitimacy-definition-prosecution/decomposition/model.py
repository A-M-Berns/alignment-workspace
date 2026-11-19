"""The model of ACCOUNT.md: candidates, running, best/got/gap, the four kinds, whose gap,
and the admissibility constraints.  Exact rationals throughout."""
from __future__ import annotations

import itertools
from fractions import Fraction as F

KINDS = ("help", "harm", "subversion", "force")


class Ctx:
    """What a goal function or a view may read at a step."""

    def __init__(self, world, action, state, step):
        self.world, self.action, self.step = world, action, step
        self.state = state          # carried state, mutated as parts move
        self.start = dict(state)    # carried state at the start of the step
        self.pre = {}               # part -> carried state just before its move
        self.moves = {}             # part -> move
        self.views = {}             # part -> what it saw

    def with_move(self, part, move):
        c = Ctx.__new__(Ctx)
        c.__dict__.update(self.__dict__)
        c.moves = dict(self.moves)
        c.moves[part] = move
        return c


class Part:
    def __init__(self, name, moves, see, goal, apply=None, reads=()):
        self.name, self.moves, self.see, self.goal = name, moves, see, goal
        self.apply = apply          # (state, move, ctx) -> None: an alteration
        self.reads = tuple(reads)   # parts whose moves its view reads


class Candidate:
    """A goal, ordered parts, their mechanisms, and the carried state at the start."""

    def __init__(self, name, parts, mech, goal, init=None, tags=None):
        self.name = name
        self.parts = list(parts)
        self.part = {p.name: p for p in parts}
        self.mech = dict(mech)      # part -> (view -> move)
        self.goal = goal            # Ctx (after the step's moves) -> Fraction
        self.init = init or (lambda world: {})
        self.tags = tags or {}

    def order(self, action):
        names = [p.name for p in self.parts]
        given = action.get("order")
        return names if not given else [n for n in names if n not in given] + list(given)


def run_step(cand, world, action, state, mechs, step=0, forced_keys=None):
    """One step.  `action` may carry `force` {part: move}, `setmech` {part: fn(state, mechs)}
    and `order`.  Returns the context; `state` and `mechs` are advanced in place."""
    ctx = Ctx(world, action, state, step)
    for name, setter in action.get("setmech", {}).items():
        setter(state, mechs)
    ctx.start = dict(state)
    for name in cand.order(action):
        p = cand.part[name]
        ctx.pre[name] = dict(state)
        ctx.views[name] = p.see(ctx)
        if name in action.get("force", {}):
            move = action["force"][name]
        else:
            move = mechs[name](ctx.views[name])
        ctx.moves[name] = move
        if p.apply:
            p.apply(state, move, ctx)
    ctx.end = dict(state)
    return ctx


def measures(cand, ctx):
    """part -> (best, got, gap), the other parts' moves as they are."""
    out = {}
    for p in cand.parts:
        got = p.goal(ctx, ctx.moves[p.name])
        best = max([p.goal(ctx, m) for m in p.moves(ctx)] + [got])
        out[p.name] = (best, got, best - got)
    return out


def forced_parts(adv):
    return set(adv.get("force", {})) | set(adv.get("setmech", {}))


def classify(cand, world, actions, comps, bases=None, cutoff=F(0), mechs0=None):
    """The verdict of `actions` against `comps`, step by step (per-step comparison).
    `bases[t]` is what nature does at step t, present under both.  Returns
    (set of (kind, part), list of per-step detail)."""
    bases = bases or [{}] * len(actions)
    state, mechs = cand.init(world), dict(mechs0 or cand.mech)
    kinds, detail = set(), []
    for t, (a, c) in enumerate(zip(actions, comps)):
        st_c, me_c = dict(state), dict(mechs)
        ctx_c = run_step(cand, world, merge(bases[t], c), st_c, me_c, t)
        ctx_a = run_step(cand, world, merge(bases[t], a), state, mechs, t)
        ma, mc = measures(cand, ctx_a), measures(cand, ctx_c)
        forced = forced_parts(a)
        row = {"step": t, "forced": sorted(forced), "taste": (ctx_a.start.get("taste"), ctx_a.end.get("taste")),
               "parts": {}}
        for p in cand.parts:
            n = p.name
            dbest, dgap = ma[n][0] - mc[n][0], ma[n][2] - mc[n][2]
            ks = []
            if n in forced:
                ks.append("force")
            else:
                if dbest > 0 or dgap < 0:
                    ks.append("help")
                if dbest < 0:
                    ks.append("harm")
                if dgap > cutoff:
                    ks.append("subversion")
            for k in ks:
                kinds.add((k, n))
            row["parts"][n] = {"best": ma[n][0], "gap": ma[n][2], "dbest": dbest, "dgap": dgap, "kinds": ks,
                               "move": ctx_a.moves[n]}
        row["action"] = ctx_a.moves.get(cand.parts[-1].name)
        detail.append(row)
    return kinds, detail


def merge(base, adv):
    out = dict(base)
    for k, v in adv.items():
        if k in ("force", "setmech") and k in out:
            d = dict(out[k])
            d.update(v)
            out[k] = d
        else:
            out[k] = v
    return out


# --- whose gap ------------------------------------------------------------------------

def gap_owner(cand, scope, part, world, action, mechs0=None):
    """'hers' or 'nobody' for the gap of `part` at (world, action); None when it serves.
    `scope` is a list of (world, action, weight): the situations of S with their ν-weight."""
    p = cand.part[part]

    def at(w, a):
        ctx = run_step(cand, w, a, cand.init(w), dict(mechs0 or cand.mech))
        return ctx

    here = at(world, action)
    got = p.goal(here, here.moves[part])
    moves = list(p.moves(here))
    better = [m for m in moves if p.goal(here, m) > got]
    if not better:
        return None
    view = here.views[part]
    sits = [(at(w, a), nu) for (w, a, nu) in scope]
    same = [(c, nu) for (c, nu) in sits if c.views[part] == view]
    # (A) a strictly higher ν-expected score: per view the choice is free, so only this view matters
    base_nu = sum(nu * p.goal(c, c.moves[part]) for c, nu in same)
    for m in better:
        if sum(nu * p.goal(c, m) for c, nu in same) > base_nu:
            return "hers"
    # (B) an equal ν-expected score, and at least as much at every situation with this view
    for m in better:
        if sum(nu * p.goal(c, m) for c, nu in same) == base_nu:
            if all(p.goal(c, m) >= p.goal(c, c.moves[part]) for c, _ in same):
                return "hers"
    return "nobody"


# --- admissibility --------------------------------------------------------------------

CONSTRAINTS = ("fit", "nothing left over", "never opposed", "mostly serving", "independent", "carriable")


def profiles(cand, ctx):
    names = [p.name for p in cand.parts]
    for combo in itertools.product(*[cand.part[n].moves(ctx) for n in names]):
        c = Ctx.__new__(Ctx)
        c.__dict__.update(ctx.__dict__)
        c.moves = dict(zip(names, combo))
        yield c


def admissibility(cand, scope, behaviour, tau=F(9, 10), fit_on="scope", nlo_on="scope",
                  strong_independent=False, strict_carriable=False):
    """Which constraints of ACCOUNT.md §4 the single-step candidate fails.
    `scope`: list of (world, action, ν-weight).  `behaviour(world, action)`: the action she takes."""
    fails, info = set(), {"vacuous": 0, "serving": {}}
    ctxs = [(run_step(cand, w, a, cand.init(w), dict(cand.mech)), w, a, nu) for (w, a, nu) in scope]
    last = cand.parts[-1].name
    total = sum(nu for *_, nu in ctxs)
    # fit, and nothing left over, each on the scope and on the usual situations only
    info["fit"] = {"scope": True, "usual": True}
    info["nlo"] = {"scope": True, "usual": True}
    for ctx, w, a, nu in ctxs:
        if cand.tags.get("her_action", lambda c: c.moves[last])(ctx) != behaviour(w, a):
            info["fit"]["scope"] = False
            if nu > 0:
                info["fit"]["usual"] = False
        profs = list(profiles(cand, ctx))
        tops = {p.name: max(p.goal(c, c.moves[p.name]) for c in profs) for p in cand.parts}
        gmax = max(cand.goal(c) for c in profs)
        full = [c for c in profs if all(p.goal(c, c.moves[p.name]) == tops[p.name] for p in cand.parts)]
        if not full:
            info["vacuous"] += 1
        elif any(cand.goal(c) < gmax for c in full):
            info["nlo"]["scope"] = False
            if nu > 0:
                info["nlo"]["usual"] = False
    if not info["fit"]["scope" if fit_on == "scope" else "usual"]:
        fails.add("fit")
    if not info["nlo"]["scope" if nlo_on == "scope" else "usual"]:
        fails.add("nothing left over")
    # never opposed, on the support of ν
    for ctx, w, a, nu in ctxs:
        if nu == 0:
            continue
        g0 = cand.goal(ctx)
        for p in cand.parts:
            got = p.goal(ctx, ctx.moves[p.name])
            for m in p.moves(ctx):
                if p.goal(ctx, m) > got:
                    alt = run_step(cand, w, merge(a, {"force": {p.name: m}}), cand.init(w), dict(cand.mech))
                    if cand.goal(alt) < g0:
                        fails.add("never opposed")
    # the pairwise reading: a move the part's goal function ranks higher never leaves her goal lower
    info["pairwise opposed at"] = set()
    for ctx, w, a, nu in ctxs:
        if nu == 0:
            continue
        for p in cand.parts:
            ms = list(p.moves(ctx))
            down = [cand.goal(run_step(cand, w, merge(a, {"force": {p.name: m}}), cand.init(w), dict(cand.mech)))
                    for m in ms]
            score = [p.goal(ctx, m) for m in ms]
            if any(score[i] > score[j] and down[i] < down[j] for i in range(len(ms)) for j in range(len(ms))):
                info["pairwise opposed at"].add(w)
    # mostly serving; independent; carriable
    for p in cand.parts:
        rate = sum(nu for ctx, w, a, nu in ctxs if measures(cand, ctx)[p.name][2] == 0) / total
        info["serving"][p.name] = rate
        if rate < tau:
            fails.add("mostly serving")
        constant = all(len({p.goal(ctx, m) for m in p.moves(ctx)}) == 1 for ctx, *_ in ctxs)
        info.setdefault("constant", {})[p.name] = constant
        if constant or cand.tags.get("reads_mechanism", {}).get(p.name):
            fails.add("independent")
        info.setdefault("optimal everywhere", {})[p.name] = all(
            measures(cand, ctx)[p.name][2] == 0 for ctx, w, a, nu in ctxs if p.name not in forced_parts(a))
        if strong_independent and info["optimal everywhere"][p.name]:
            fails.add("independent")
        # carriable: the best a mechanism on the view can do, view by view
        by_view = {}
        for ctx, w, a, nu in ctxs:
            if nu > 0:
                by_view.setdefault(ctx.views[p.name], []).append((ctx, nu))
        carried = F(0)
        for view, group in by_view.items():
            best_rate = F(0)
            for m in p.moves(group[0][0]):
                r = sum(nu for ctx, nu in group
                        if p.goal(ctx, m) == max(p.goal(ctx, mm) for mm in p.moves(ctx)))
                best_rate = max(best_rate, r)
            carried += best_rate
        carried /= total
        if carried < (1 if strict_carriable else tau):
            fails.add("carriable")
    return fails, info
