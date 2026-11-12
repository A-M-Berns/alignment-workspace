"""Computations for the two addenda: pairs of a mechanism and a subgoal it is for
(TWO_DECOMPOSITIONS.md), and the adviser taken as one of her parts (ADVISER_AS_PART.md).
Facts only; no statement of THEOREMS.md rests on this module."""
from __future__ import annotations

import itertools
from fractions import Fraction as F

from . import scenes as S
from .model import forced_parts, merge, run_step
from .theorems import INPUTS, PRIOR, TAU, WORLDS, comparisons

MECHS = ("belief", "judge", "act")
BASE = S.chain()
G = S.chain_goal()

SUBGOALS = {
    "A": lambda ctx: F(int(ctx.moves["belief"][0] == ctx.world[0])),            # she is right about θ
    "Phi": lambda ctx: F(int(ctx.moves["belief"][1] == 0)),                      # she is right about φ
    "E": lambda ctx: F(int(ctx.moves["belief"] == S.belief_mech(ctx.views["belief"]))),   # she believes what she was told
    "V": lambda ctx: G(ctx, x=ctx.moves["judge"]),                               # her verdict is right
    "X": lambda ctx: G(ctx),                                                     # her action is right
}


def run(world, action, forced=None):
    a = merge(action, {"force": forced}) if forced else action
    return run_step(BASE, world, a, {}, dict(BASE.mech))


def pair_measure(world, action, mech, sub):
    """(best, got) of the pair: the subgoal's score over the mechanism's moves, the later
    mechanisms responding."""
    ctx = run(world, action)
    got = SUBGOALS[sub](ctx)
    best = max(SUBGOALS[sub](run(world, action, {mech: m})) for m in BASE.part[mech].moves(ctx))
    return best, got


SCOPE = [(w, a, nu) for (w, a, nu) in S.chain_scope() if not forced_parts(a) and not a.get("order")]


def effective():
    """The pairs (mechanism, subgoal) such that some move of the mechanism changes the subgoal's score somewhere."""
    out = set()
    for mech in MECHS:
        for sub in SUBGOALS:
            for w, a, nu in SCOPE:
                ctx = run(w, a)
                if len({SUBGOALS[sub](run(w, a, {mech: m})) for m in BASE.part[mech].moves(ctx)}) > 1:
                    out.add((mech, sub))
                    break
    return out


def pair_admissible(relation):
    """Adding up on the scope, mostly serving per pair, each mechanism in some pair."""
    if {m for m, _ in relation} != set(MECHS):
        return False
    total = sum(nu for _, _, nu in SCOPE)
    for mech, sub in relation:
        rate = sum(nu for w, a, nu in SCOPE if nu > 0 and (lambda bg: bg[0] == bg[1])(pair_measure(w, a, mech, sub))) / total
        if rate < TAU:
            return False
    subs = {s for _, s in relation}
    for w, a, nu in SCOPE:
        ctx = run(w, a)
        profs = [run(w, a, dict(zip(MECHS, combo)))
                 for combo in itertools.product(*[BASE.part[m].moves(ctx) for m in MECHS])]
        tops = {s: max(SUBGOALS[s](c) for c in profs) for s in subs}
        gmax = max(G(c) for c in profs)
        full = [c for c in profs if all(SUBGOALS[s](c) == tops[s] for s in subs)]
        if any(G(c) < gmax for c in full):
            return False
    return True


def pair_subverted(relation, action, world):
    """The pairs whose gap the action widens against null."""
    out = set()
    for mech, sub in relation:
        b1, g1 = pair_measure(world, S.CHAIN_ACTIONS[action], mech, sub)
        b0, g0 = pair_measure(world, {}, mech, sub)
        if (b1 - g1) > (b0 - g0):
            out.add((mech, sub))
    return out


def two_decompositions():
    eff = sorted(effective())
    closed, free = [], []
    names = sorted(SUBGOALS)
    for r in range(1, len(names) + 1):
        for subs in itertools.combinations(names, r):
            rel = frozenset(p for p in eff if p[1] in subs)
            if {s for _, s in rel} == set(subs) and pair_admissible(rel):
                closed.append(rel)
    for r in range(1, len(eff) + 1):
        for rel in itertools.combinations(eff, r):
            if pair_admissible(frozenset(rel)):
                free.append(frozenset(rel))

    def splits(rels, pointwise):
        out = []
        for a in INPUTS:
            if pointwise:
                seen = {tuple(bool(pair_subverted(rel, a, w)) for w in WORLDS) for rel in rels}
            else:
                seen = {any(pair_subverted(rel, a, w) for w in WORLDS) for rel in rels}
            if len(seen) > 1:
                out.append(a)
        return out

    right = [w for w in WORLDS if w[1] != "misleading"]
    lie_spared_at_belief = {
        "free": sum(1 for rel in free if not any(m == "belief" for w in right for m, _ in pair_subverted(rel, "lie", w))),
        "closed": sum(1 for rel in closed if not any(m == "belief" for w in right for m, _ in pair_subverted(rel, "lie", w)))}
    echo = [rel for rel in free if ("belief", "E") in rel and ("belief", "A") not in rel]
    by_crossings = {}
    for rel in echo:
        k = sum(1 for m, s in rel if m == "belief" and s in ("V", "X"))
        spared = not any(m == "belief" for w in right for m, _ in pair_subverted(rel, "lie", w))
        row = by_crossings.setdefault(k, [0, 0])
        row[0] += 1
        row[1] += int(spared)
    hard = (0, "hard")
    y8 = sorted(pair_subverted(frozenset(eff), "lie", hard))
    y8_help = sorted((m, s) for m, s in eff
                     if (lambda a, b: (a[0] - a[1]) < (b[0] - b[1]))(pair_measure(hard, S.CHAIN_ACTIONS["lie"], m, s),
                                                                     pair_measure(hard, {}, m, s)))
    return {"effective pairs": eff,
            "closed relations admissible": len(closed), "their subgoal sets": sorted(sorted({s for _, s in r}) for r in closed),
            "closed: actions split on whether they subvert": splits(closed, False), "closed: split at some world": splits(closed, True),
            "free relations admissible": len(free),
            "free: actions split on whether they subvert": splits(free, False), "free: split at some world": splits(free, True),
            "relations under which a lie subverts no pair of belief": lie_spared_at_belief,
            "belief for E and not A, by number of pairs of belief with V or X: (relations, of which the lie is spared at belief)": by_crossings,
            "all effective pairs, lie at a hard world: pairs widened": y8, "pairs narrowed": y8_help}


# --- the adviser as a part ------------------------------------------------------------

def adviser_as_part():
    acts = ["null"] + INPUTS
    down = lambda w, a: G(run(w, S.CHAIN_ACTIONS[a]))
    purposes = {
        "her goal, her mechanisms responding": down,
        "say nothing false": lambda w, a: F(int(a not in ("lie", "false_reason"))),
        "whatever it does (null and teach)": lambda w, a: F(int(a in ("null", "teach"))),
    }
    usual = [(w, a, PRIOR[w] / 2) for w in WORLDS for a in ("null", "teach")]
    serving = {name: sum(nu for w, a, nu in usual if g(w, a) == max(g(w, b) for b in acts))
               for name, g in purposes.items()}
    # its best move by the first purpose, as the comparison action
    table = comparisons()
    silence = {c for c, r in table.items() if r["silence"]}
    arm = {c for c, r in table.items() if r["honest arm"]}
    best = {c for c, r in table.items() if r["best available"]}
    # manipulation as the adviser part's own gap, and as opposition
    gap = {a: sum(PRIOR[w] * (max(down(w, b) for b in acts) - down(w, a)) for w in WORLDS) for a in acts}
    truthful_opposed = [(w, a) for w in WORLDS for a in ("hard_truth",) if down(w, a) < down(w, "null")]
    # correction: an adviser whose view has θ reversed, judged by its own view
    flip = lambda w: (1 - w[0], w[1])
    in_view = {name: sum(PRIOR[w] * G(run(flip(w), {"m": flip(w)[0]} if name == "keeps teaching" else {})) for w in WORLDS)
               for name in ("keeps teaching", "accepts the correction (silent)")}
    in_fact = {name: sum(PRIOR[w] * G(run(w, {"m": flip(w)[0]} if name == "keeps teaching" else {})) for w in WORLDS)
               for name in ("keeps teaching", "accepts the correction (silent)")}
    return {"serving on the usual situations, by purpose given to the adviser": serving,
            "admissible at 9/10": sorted(n for n, r in serving.items() if r >= TAU),
            "bank cases convicted: against silence, the honest arm, the adviser's best move": [len(silence), len(arm), len(best)],
            "convicted against silence and not against its best move": sorted(silence - best),
            "convicted against its best move only": sorted(best - silence - arm),
            "the adviser part's expected gap, by action": gap,
            "worlds where a true statement leaves her worse than silence": truthful_opposed,
            "the mistaken adviser, by its own view": in_view, "in fact": in_fact}


FACTS = {"two decompositions": two_decompositions, "adviser as a part": adviser_as_part}
