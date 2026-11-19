"""Explanations, their code lengths and their weights (ACCOUNT.md §2-§5, §9).

A candidate's code length is a sum over its parts, since each part's move is predicted with
the other parts' moves as they were.  So the class is assembled from per-part options."""
from __future__ import annotations

import itertools
from fractions import Fraction as F
from functools import lru_cache

from decomposition.model import run_step

from . import scene as C

LANGS = {
    "A": {"atom": 4, "goal": {"true": 1, "opp": 2, "ease": 2, "does": 1},
          "belief": {"acc": 2, "acc_theta": 1, "handed": 2, "anti": 3, "const": 1, "mech": 1},
          "judge": {"world": 1, "local": 2, "anti": 2, "const": 1, "mech": 1},
          "act": {"world": 1, "local": 1, "anti": 2, "const": 1, "mech": 1},
          "say": {"avow": 0, "please": 1}, "entry": 9, "miss": 8},
    "B": {"atom": 5, "goal": {"true": 2, "opp": 3, "ease": 2, "does": 1},
          "belief": {"acc": 3, "acc_theta": 2, "handed": 1, "anti": 4, "const": 1, "mech": 1},
          "judge": {"world": 2, "local": 1, "anti": 3, "const": 1, "mech": 1},
          "act": {"world": 2, "local": 1, "anti": 3, "const": 1, "mech": 1},
          "say": {"avow": 1, "please": 0}, "entry": 6, "miss": 8},
}
for _name, _miss in (("A-miss4", 4), ("A-miss16", 16)):
    LANGS[_name] = {**LANGS["A"], "miss": _miss}
SAYS = ("avow", "please")
POLICIES = ("bare", "patched", "best", "alt")
FAMILIES = tuple(C.PROBES)
VIRTUES = ("parsimony", "fit", "handles", "intersubjectivity")


def log2ceil(n):
    return (n - 1).bit_length()


def history(N):
    """[(world, action, count)]: N steps by the prior, silent or teaching at 1/2 each."""
    out = []
    for w in C.WORLDS:
        for a in (C.NULL, C.TEACH):
            n = F(N) * C.PRIOR[w] / 2
            if n.denominator != 1:
                raise ValueError("history length %s gives a fractional count" % N)
            out.append((w, a, int(n)))
    return out


def probes(families=FAMILIES):
    return [(w, C.PROBES[f], f) for f in families for w in C.WORLDS]


@lru_cache(maxsize=None)
def record(principal, world, action_key):
    """Her record at one situation: (ctx, the Candidate used to run it)."""
    action = dict(action_key)
    cand = C.chainr(principal=principal)
    return run_step(cand, world, action, {}, dict(cand.mech))


def key(action):
    return tuple(sorted(action.items()))


def goal_dependent(part, purpose):
    return part in ("judge", "act") and purpose in ("world", "anti")


@lru_cache(maxsize=None)
def scorer(principal, part, purpose, goal):
    """The part's goal function under (purpose, goal), first-person."""
    purposes = {"belief": (purpose, "const", "const"), "judge": ("const", purpose, "const"),
                "act": ("const", "const", purpose)}[part]
    return C.chainr(purposes, goal or "true", principal).part[part]


READINGS = ("serves", "view-best")


@lru_cache(maxsize=None)
def reference(principal, part, N):
    """For the view-best reading: view -> [(ctx, weight)], the history's situations with that view
    where it has any, and otherwise the probes with it, each by its world's prior."""
    hist, rest = {}, {}
    for w, a, n in history(N):
        ctx = record(principal, w, key(a))
        hist.setdefault(ctx.views[part], []).append((ctx, F(n)))
    for w, a, f in probes():
        ctx = record(principal, w, key(a))
        rest.setdefault(ctx.views[part], []).append((ctx, C.PRIOR[w]))
    return {**rest, **hist}


def predicted(principal, part, purpose, goal, ctx, second, reading="serves", N=80):
    """The set of moves the purpose predicts at the situation; every move for a private term
    read by the second predictor.  `serves`: the best moves at the situation as it is.
    `view-best`: the best moves in expectation over the situations with the part's view."""
    p = scorer(principal, part, purpose, goal)
    moves = list(p.moves(ctx))
    if second and (purpose in C.PRIVATE or (goal_dependent(part, purpose) and goal == "does")):
        return frozenset(moves)
    if reading == "serves":
        scores = {m: p.goal(ctx, m) for m in moves}
    else:
        group = reference(principal, part, N).get(ctx.views[part]) or [(ctx, F(1))]
        scores = {m: sum(wt * p.goal(c, m) for c, wt in group) for m in moves}
    top = max(scores.values())
    return frozenset(m for m in moves if scores[m] == top)


@lru_cache(maxsize=None)
def option(principal, part, purpose, goal, policy, lang, N, r, families, reading):
    """One part's contribution: (entries, DL of entries, fit, handles, fit and handles first-person,
    handles by probe family, the views that are normal on the history)."""
    L = LANGS[lang]
    hist = [(record(principal, w, key(a)), n) for w, a, n in history(N)]
    prb = [(record(principal, w, key(a)), f) for w, a, f in probes(families)]
    memo = {}

    def B(ctx, second):
        k = (id(ctx), second)
        if k not in memo:
            memo[k] = predicted(principal, part, purpose, goal, ctx, second, reading, N)
        return memo[k]
    B2 = lambda ctx: B(ctx, True)
    B1 = lambda ctx: B(ctx, False)
    by_view = {}
    for ctx, n in hist:
        by_view.setdefault(ctx.views[part], []).append((ctx, n))
    alt = C.belief_mech(principal, alt=True) if (policy == "alt" and part == "belief") else None

    def miss(B, move):
        return log2ceil(len(B)) if move in B else L["miss"]

    entries = {}
    if policy != "bare":
        for view, group in by_view.items():
            claimed = alt(view) if alt else group[0][0].moves[part]
            if any(B2(ctx) != frozenset([claimed]) for ctx, _ in group):
                entries[view] = claimed
    if policy == "best":
        kept = {}
        for view, move in entries.items():
            without = sum(n * miss(B2(ctx), ctx.moves[part]) for ctx, n in by_view[view])
            without += r * sum(miss(B2(ctx), ctx.moves[part]) for ctx, _ in prb if ctx.views[part] == view)
            if without > L["entry"]:
                kept[view] = move
        entries = kept

    def cost(ctx, B):
        if part == "belief" and ctx.action.get("deg"):
            return 0        # the degraded part's move is the change itself, not her response to it
        view = ctx.views[part]
        if view in entries:
            return 0 if entries[view] == ctx.moves[part] else L["miss"]
        return miss(B(ctx), ctx.moves[part])

    fit2 = sum(n * cost(ctx, B2) for ctx, n in hist)
    fit1 = sum(n * cost(ctx, B1) for ctx, n in hist)
    fam2, fam1 = {}, {}
    for ctx, f in prb:
        fam2[f] = fam2.get(f, 0) + r * cost(ctx, B2)
        fam1[f] = fam1.get(f, 0) + r * cost(ctx, B1)
    normal = frozenset(key(ctx.action) + (("world", ctx.world),) for ctx, n in hist
                       if ctx.views[part] not in entries and ctx.moves[part] in B1(ctx))
    return {"entries": tuple(sorted(entries.items(), key=str)), "dl": L["entry"] * len(entries),
            "fit": fit2, "hand": sum(fam2.values()), "fit1": fit1, "hand1": sum(fam1.values()),
            "families": fam2, "normal": normal}


def say_cost(goal, say, lang, N):
    """Her statements of her aim: N/8 occasions, each `true`."""
    return 0 if (say == "please" or goal == "true") else LANGS[lang]["miss"] * (N // 8)


@lru_cache(maxsize=None)
def table(principal, lang="A", N=80, r=1, families=FAMILIES, reading="serves"):
    """The class with its code lengths: one row per distinct explanation."""
    L = LANGS[lang]
    rows, seen = [], set()
    for goal in C.GOALS:
        for purposes in itertools.product(*[C.PURPOSES[p] for p in C.PARTS]):
            for policy in POLICIES:
                opts = [option(principal, part, purpose, goal if goal_dependent(part, purpose) else None,
                               policy, lang, N, r, families, reading) for part, purpose in zip(C.PARTS, purposes)]
                for say in SAYS:
                    ident = (goal, purposes, say, tuple(o["entries"] for o in opts))
                    if ident in seen:
                        continue
                    seen.add(ident)
                    dl = L["atom"] * (L["goal"][goal] + L["say"][say] + sum(L[part][pu] for part, pu in zip(C.PARTS, purposes)))
                    dl += sum(o["dl"] for o in opts)
                    sc = say_cost(goal, say, lang, N)
                    fams = {f: sum(o["families"].get(f, 0) for o in opts) for f in families}
                    rows.append({"goal": goal, "purposes": purposes, "say": say, "policy": policy,
                                 "entries": sum(len(o["entries"]) for o in opts), "ident": ident,
                                 "parsimony": dl, "fit": sum(o["fit"] for o in opts) + sc,
                                 "handles": sum(o["hand"] for o in opts),
                                 "fit1": sum(o["fit1"] for o in opts) + sc, "handles1": sum(o["hand1"] for o in opts),
                                 "families": fams,
                                 "normal": frozenset.intersection(*[o["normal"] for o in opts])})
    return rows


def bits(row, drop=None):
    """The code length; `drop` removes one virtue (ACCOUNT.md §3, ablations)."""
    first = drop == "intersubjectivity"
    total = 0
    if drop != "parsimony":
        total += row["parsimony"]
    if drop != "fit":
        total += row["fit1" if first else "fit"]
    if drop != "handles":
        total += row["handles1" if first else "handles"]
    return total


def weigh(rows, drop=None):
    """[(row, weight)] by decreasing weight, the weights exact and summing to 1; ties in the order
    of the class."""
    bs = [bits(r, drop) for r in rows]
    top = max(bs)
    raw = [1 << (top - b) for b in bs]
    total = sum(raw)
    order = sorted(range(len(rows)), key=lambda i: (bs[i], i))
    return [(rows[i], F(raw[i], total)) for i in order]


def heavy(weighted, share=F(99, 100)):
    out, acc = [], F(0)
    for row, w in weighted:
        if acc >= share:
            break
        out.append((row, w))
        acc += w
    return out


def name(row):
    s = "%s; %s; %s" % (row["goal"], ", ".join(row["purposes"]), row["say"])
    return s + ("" if not row["entries"] else "; %d exception%s" % (row["entries"], "" if row["entries"] == 1 else "s"))


def dec(x, places=6):
    """A Fraction as a decimal string, truncated; display only."""
    x = F(x)
    scaled = (abs(x.numerator) * 10 ** places) // x.denominator
    s = str(scaled).rjust(places + 1, "0")
    return ("-" if x < 0 else "") + s[:-places] + "." + s[-places:]
