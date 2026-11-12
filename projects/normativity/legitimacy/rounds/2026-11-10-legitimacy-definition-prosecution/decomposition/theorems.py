"""The checks behind THEOREMS.md.  Each returns {'supports': status, ...facts}; the status is
computed from the facts, and run.py compares it with the one THEOREMS.md states."""
from __future__ import annotations

import itertools
from fractions import Fraction as F
from functools import lru_cache

from . import scenes as S
from .cases import all_cases, verdict
from .model import (Candidate, admissibility, classify, forced_parts, measures, merge, profiles,
                    run_step)

H = F(1, 2)
WORLDS = [w for w, _ in S.chain_worlds()]
PRIOR = dict(S.chain_worlds())
INPUTS = [a for a in S.CHAIN_INPUTS if a != "null"]
TAU = F(9, 10)


# --- the class of statement 1 ---------------------------------------------------------

def chain_class():
    for goal in ("true", "opp", "does"):
        for purposes in itertools.product(*[S.CHAIN_PURPOSES[p] for p in ("belief", "judge", "act")]):
            for mechs in itertools.product(("actual", "alt"), repeat=3):
                yield S.chain(purposes, mechs, goal)


CHEATS = {
    "every part's purpose equal to its mechanism": (("mech", "mech", "mech"), "true"),
    "the opposite goal pursued badly": (("anti", "anti", "anti"), "opp"),
    "the goal equal to whatever she does": (("mech", "mech", "mech"), "does"),
    "honest, altered at belief only": (("mech", "world", "world"), "true"),
    "honest, altered at judge only": (("acc", "mech", "world"), "true"),
    "honest, altered at act only": (("acc", "world", "mech"), "true"),
}


def signature(cand):
    """(action, world) -> frozenset of (kind, part), against null, for every adviser input."""
    sig = {}
    for a in INPUTS + ["force", "tempt_early", "write_belief"]:
        for w in WORLDS:
            kinds, _ = classify(cand, w, [S.CHAIN_ACTIONS[a]], [{}])
            sig[(a, w)] = frozenset(kinds)
    return sig


@lru_cache(maxsize=None)
def survey():
    """Every candidate of the class with what it fails under each reading of the constraints."""
    scope, behave = S.chain_scope(), S.chain_behaviour()
    rows = []
    for cand in chain_class():
        base, info = admissibility(cand, scope, behave, tau=F(0))
        base -= {"fit", "nothing left over", "independent"}
        wide = base | (set() if info["fit"]["scope"] else {"fit"}) | (set() if info["nlo"]["scope"] else {"nothing left over"})
        narrow = base | (set() if info["fit"]["usual"] else {"fit"}) | (set() if info["nlo"]["usual"] else {"nothing left over"})
        rows.append({"cand": cand, "tags": cand.tags, "wide": wide, "narrow": narrow,
                     "constant": any(info["constant"].values()),
                     "reads": any(cand.tags["reads_mechanism"].values()),
                     "strong": any(info["optimal everywhere"].values()), "serving": info["serving"],
                     "vacuous": info["vacuous"], "pairwise": info["pairwise opposed at"]})
    return rows


READINGS = ("table", "stated", "strong")


def admissible(rows, tau=TAU, scope="wide", reading="stated", pairwise=None, attainable=False):
    """`reading` of *independent*: "table" (a goal function that is the mechanism's table written
    out counts as independent), "stated" (it does not: ACCOUNT.md §4), "strong" (also, the
    mechanism is not optimal everywhere).  `pairwise`: None, or the world events left out of the
    usual situations when *never opposed* is read pairwise.  `attainable`: the parts' maxima can be
    had together at every situation."""
    out = []
    for r in rows:
        fails = set(r[scope])
        if any(rate < tau for rate in r["serving"].values()):
            fails.add("mostly serving")
        if r["constant"] or (reading != "table" and r["reads"]) or (reading == "strong" and r["strong"]):
            fails.add("independent")
        if pairwise is not None and any(w[1] not in pairwise for w in r["pairwise"]):
            fails.add("never opposed")
        if attainable and r["vacuous"]:
            fails.add("nothing left over")
        if not fails:
            out.append(r)
    return out


def subverts(sig, action, worlds=WORLDS):
    return any(k == "subversion" for w in worlds for k, _ in sig[(action, w)])


def agreement(rows):
    sigs = [signature(r["cand"]) for r in rows]
    purposes = {p: sorted({r["tags"]["purposes"][i] for r in rows}) for i, p in enumerate(("belief", "judge", "act"))}
    split = [a for a in INPUTS if len({subverts(s, a) for s in sigs}) > 1]
    split_pointwise = [a for a in INPUTS if len({tuple(subverts(s, a, [w]) for w in WORLDS) for s in sigs}) > 1]
    return {"count": len(rows), "purposes": purposes, "distinct signatures": len({tuple(sorted(s.items())) for s in sigs}),
            "actions split on whether they subvert": split, "split at some world": split_pointwise}


def dependence():
    """Which goal functions rank a part's moves as her goal does with the later mechanisms
    responding, on the usual situations, and where two that do part company."""
    out = {}
    scope = S.chain_scope()
    for i, part in enumerate(("belief", "judge", "act")):
        ok = {}
        for purpose in S.CHAIN_PURPOSES[part]:
            ps = ["acc", "world", "world"]
            ps[i] = purpose
            cand = S.chain(tuple(ps))
            p = cand.part[part]
            agree_usual, differ_off = True, []
            for w, a, nu in scope:
                ctx = run_step(cand, w, a, {}, dict(cand.mech))
                if part in forced_parts(a):
                    continue
                top = lambda f: {m for m in p.moves(ctx) if f(m) == max(f(mm) for mm in p.moves(ctx))}
                down = top(lambda m: cand.goal(run_step(cand, w, merge(a, {"force": {part: m}}), {}, dict(cand.mech))))
                mine = top(lambda m: p.goal(ctx, m))
                if nu > 0 and mine != down:
                    agree_usual = False
                if nu == 0 and mine != down:
                    differ_off.append((w, [k for k, v in S.CHAIN_ACTIONS.items() if v is a][0]))
            ok[purpose] = {"on usual": agree_usual, "parts from it off usual at": len(differ_off)}
        out[part] = ok
    return out


def names(rows):
    return sorted(r["cand"].name.replace("|actual/actual/actual", "") for r in rows)


def check_1():
    rows = survey()
    fixed = admissible(rows)
    ag = agreement(fixed)
    grid = {}
    for tau in (F(1, 40), H, F(3, 4), F(9, 10), F(19, 20), F(1)):
        for scope in ("wide", "narrow"):
            for reading in READINGS:
                sel = admissible(rows, tau, scope, reading)
                a = agreement(sel) if sel else {"count": 0}
                grid["tau=%s, %s, %s" % (tau, "scope" if scope == "wide" else "usual only", reading)] = {
                    "count": a["count"], "purposes": a.get("purposes"),
                    "split": a.get("actions split on whether they subvert"),
                    "split at some world": a.get("split at some world")}
    cheats = {}
    for name, (purposes, goal) in CHEATS.items():
        r = next(r for r in rows if r["tags"]["purposes"] == purposes and r["tags"]["goal"] == goal
                 and r["tags"]["mechs"] == ("actual",) * 3)
        serving = {"mostly serving"} if any(x < TAU for x in r["serving"].values()) else set()
        cheats[name] = {"table": sorted(set(r["wide"]) | serving),
                        "stated": sorted(set(r["wide"]) | serving | ({"independent"} if r["reads"] else set())),
                        "table, usual only": sorted(set(r["narrow"]) | serving)}
    simple = min(sum(p in ("local", "mech") for p in r["tags"]["purposes"]) for r in fixed)
    simplest = [r for r in fixed if sum(p in ("local", "mech") for p in r["tags"]["purposes"]) == simple]
    variants = {
        "table": admissible(rows, reading="table"),
        "strong": admissible(rows, reading="strong"),
        "stated, never opposed pairwise": admissible(rows, pairwise=()),
        "table, never opposed pairwise": admissible(rows, reading="table", pairwise=()),
        "stated, never opposed pairwise, hard worlds not usual": admissible(rows, pairwise=("hard",)),
        "stated, maxima jointly attainable": admissible(rows, attainable=True),
        "table, maxima jointly attainable": admissible(rows, reading="table", attainable=True),
    }
    # the decision rule over the admissible set
    decisions = {}
    sigs = [signature(r["cand"]) for r in fixed]
    ref = S.chain()
    for a in INPUTS:
        subs = [subverts(s, a) for s in sigs]
        good = sum(PRIOR[w] * (S.chain_goal()(run_step(ref, w, S.CHAIN_ACTIONS[a], {}, dict(ref.mech)))
                               - S.chain_goal()(run_step(ref, w, {}, {}, dict(ref.mech)))) for w in WORLDS) >= 0
        decisions[a] = "refuse" if all(subs) else ("act" if (good and not any(subs)) else ("ask" if any(subs) else "do not act"))
    determinate = len(fixed) >= 1 and all(len(v) == 1 for v in ag["purposes"].values()) and not ag["split at some world"]
    return {"supports": "holds on the stated domain" if determinate else "refuted",
            "class size": len(rows), "at the fixed parameters": ag, "admissible at the fixed parameters": names(fixed),
            "variants": {k: {"candidates": names(v), **(agreement(v) if v else {"count": 0})} for k, v in variants.items()},
            "simplest": {"candidates": names(simplest), **agreement(simplest)},
            "grid": grid, "cheats": cheats, "dependence": dependence(), "decision rule": decisions}


# --- statement 2 ----------------------------------------------------------------------

def check_2():
    rows = survey()
    fixed, table = admissible(rows), admissible(rows, reading="table")

    def spared(sel, action, worlds):
        """Candidates under which the action widens no gap at any of the worlds."""
        return names(r for r in sel if not subverts(signature(r["cand"]), action, worlds))

    right = [w for w in WORLDS if w[1] != "misleading"]      # she is right about θ under null
    facts = {
        "lie, worlds where null leaves her right: candidates with no gap widened (fixed)": spared(fixed, "lie", right),
        "the same, table reading": spared(table, "lie", right),
        "the same, table reading, hard worlds only": spared(table, "lie", [w for w in WORLDS if w[1] == "hard"]),
        "lie, misleading worlds: candidates with no gap widened (fixed)": len(spared(fixed, "lie", [w for w in WORLDS if w[1] == "misleading"])),
        "fixed, count": len(fixed),
        "false_reason at clear worlds: candidates with no gap widened (fixed)": spared(fixed, "false_reason", [w for w in WORLDS if w[1] == "clear"]),
    }
    # the relation to Blackwell: the best any mechanism on the view can score, against what hers scores
    cand = S.chain()
    p = cand.part["belief"]
    channels = {"teach": {"m": "truth"}, "lie": {"m": "false"}, "constant claim": {"m": 1}, "null": {}}
    table = {}
    for name, a in channels.items():
        by_view, got, best = {}, F(0), F(0)
        for w in WORLDS:
            ctx = run_step(cand, w, a, {}, dict(cand.mech))
            by_view.setdefault(ctx.views["belief"], []).append((ctx, PRIOR[w]))
            got += PRIOR[w] * p.goal(ctx, ctx.moves["belief"])
            best += PRIOR[w] * max(p.goal(ctx, m) for m in p.moves(ctx))
        info_best = sum(max(sum(pw * p.goal(c, m) for c, pw in group) for m in p.moves(group[0][0]))
                        for group in by_view.values())
        table[name] = {"best by the facts": best, "best any mechanism on the view can do": info_best, "hers": got}
    facts["belief, expected scores by channel"] = table
    holds = not facts["lie, worlds where null leaves her right: candidates with no gap widened (fixed)"] and \
        not facts["false_reason at clear worlds: candidates with no gap widened (fixed)"] and \
        facts["lie, misleading worlds: candidates with no gap widened (fixed)"] == 0
    return {"supports": "holds on the stated domain" if holds else "refuted", **facts}


# --- statement 3 ----------------------------------------------------------------------

def check_3():
    cand = S.chain()
    combos, witnesses, from_zero, from_positive = {}, {}, 0, 0
    for a in INPUTS:
        for w in WORLDS:
            _, detail = classify(cand, w, [S.CHAIN_ACTIONS[a]], [{}])
            for part, d in detail[0]["parts"].items():
                key = "+".join(d["kinds"]) or "nothing"
                combos[key] = combos.get(key, 0) + 1
                witnesses.setdefault(key, "%s at %s, %s" % (a, w, part))
                if "subversion" in d["kinds"]:
                    if d["gap"] - d["dgap"] == 0:
                        from_zero += 1
                    else:
                        from_positive += 1
    # also the bank
    bank_multi = sorted({c.id for c in all_cases() for s in c.variants.values() if s.mode == "kinds"
                         and {"help", "subversion"} <= {k for k, _ in verdict(s)["kinds"]}})
    pool = S.pool()
    graded = [0, 0]
    for w, _ in S.POOL_WORLDS:
        _, d = classify(pool, w, [{"display": "planner"}], [{"display": "neutral"}])
        j = d[0]["parts"]["judge"]
        if "subversion" in j["kinds"]:
            graded[int(j["gap"] - j["dgap"] > 0)] += 1
    # a redescription that keeps every part's ranking of its own moves at every situation
    base = S.chain()
    judge = base.part["judge"]
    old = judge.goal
    scaled = S.chain()
    scaled.part["judge"].goal = lambda ctx, v: old(ctx, v) * (3 if ctx.action.get("k") else 1)
    w = (0, "clear")
    before = sorted(k for k, n in classify(base, w, [S.CHAIN_ACTIONS["threat"]], [{}])[0] if n == "judge")
    after = sorted(k for k, n in classify(scaled, w, [S.CHAIN_ACTIONS["threat"]], [{}])[0] if n == "judge")
    same_serving = all(
        (measures(base, run_step(base, ww, S.CHAIN_ACTIONS[a], {}, dict(base.mech)))["judge"][2] == 0)
        == (measures(scaled, run_step(scaled, ww, S.CHAIN_ACTIONS[a], {}, dict(scaled.mech)))["judge"][2] == 0)
        for a in S.CHAIN_INPUTS for ww in WORLDS)
    exclusive = all("+" not in k for k in combos)
    invariant = before == after
    return {"supports": "holds on the stated domain" if exclusive and invariant else "refuted",
            "kinds at (action, world, part) on Chain": combos, "a witness of each": witnesses,
            "subversion from a zero gap": from_zero, "subversion from a positive gap": from_positive,
            "bank cases with help and subversion together": bank_multi,
            "Pool, planner against neutral: subversion from a zero gap, from a positive gap": graded,
            "threat at (0, clear), judge, before the redescription": before, "after": after,
            "serving unchanged by the redescription": same_serving}


# --- statement 4 ----------------------------------------------------------------------

def check_4():
    names = ("null", "lie_X", "expose_X", "partial_X")
    worse, caught, missed = 0, 0, []
    for flawed in (False, True):
        for know in (0, 1):
            cand = S.values(flawed=flawed)
            for n in (1, 2):
                for seq in itertools.product(names, repeat=n):
                    for q in ("X", "Y"):
                        acts = [S.VALUES[a] for a in seq]
                        base = [{"know": know}] * n
                        kinds, detail = classify(cand, q, acts, [{}] * n, base)
                        _, ref = classify(cand, q, [{}] * n, [{}] * n, base)
                        if detail[-1]["action"] != q and ref[-1]["action"] == q:
                            worse += 1
                            if any(k == "subversion" for k, _ in kinds):
                                caught += 1
                            else:
                                missed.append((flawed, know, seq, q))
    # the bank's changes in what she pursues
    by_id = {c.id: c for c in all_cases()}
    bank = {}
    for cid in ("D16", "D17", "D18", "T4", "Y4", "Y9"):
        for name, spec in by_id[cid].variants.items():
            v = verdict(spec)
            bank[cid + ("" if name == "v" else name)] = sorted({k for k, _ in v["kinds"] if k in ("subversion", "force")}) or ["nothing"]
    # a fall in her goal with no gap widened
    stuck = verdict(by_id["Y7"].variants["v"])["kinds"]
    cand = S.stuck()
    g = lambda sig: cand.goal(run_step(cand, "hi", {"signal": sig} if sig else {}, {}, dict(cand.mech)))
    # drift: the habit part's widening per step, and what a cut-off sees
    drift = S.values(k=1)
    _, detail = classify(drift, "Y", [S.VALUES["expose_X"]] * 4, [{}] * 4)
    steps = [row["parts"]["habit"]["dgap"] for row in detail]
    flips = [t for t, row in enumerate(detail) if "subversion" in row["parts"]["act"]["kinds"]]
    cut = F(1, 4)
    reported, last, cum = [], F(0), F(0)
    for t, d in enumerate(steps):
        cum += d
        if cum - last >= cut:
            reported.append(t)
            last = cum
    no_gap_fall = not any(k == "subversion" for k, _ in stuck) and g("lo") < g(None)
    return {"supports": "refuted" if missed else "holds on the stated domain",
            "outside the statement: her goal falls with no gap widened (Stuck)": no_gap_fall,
            "Values: sequences after which her pursuit is worse than under null": worse,
            "of which some part is subverted": caught, "not": missed,
            "the bank's changes": bank,
            "Stuck, signal lo at convention hi: her goal": [g(None), g("lo")], "its kinds": sorted(stuck),
            "drift, habit's widening per step": steps, "total": sum(steps),
            "steps passing a per-step cut-off of 1/4 at habit": sum(1 for d in steps if d <= cut),
            "steps at which the acting part is subverted": flips,
            "steps at which a cumulative cut-off of 1/4 reports": reported}


# --- statement 5 ----------------------------------------------------------------------

def check_5():
    G = S.chain_goal()

    def over(cand):
        zero, zero_bad, bound_fail, n, worst = 0, 0, 0, 0, F(0)
        for w, a, nu in S.chain_scope():
            if forced_parts(a) & {"belief", "judge"} or a.get("order"):
                continue
            ctx = run_step(cand, w, a, {}, dict(cand.mech))
            m = measures(cand, ctx)
            loss = max(G(ctx, x=v) for v in (0, 1)) - G(ctx, x=ctx.moves["judge"])
            n += 1
            if m["belief"][2] == 0 and m["judge"][2] == 0:
                zero += 1
                zero_bad += int(loss != 0)
            bound_fail += int(loss > m["belief"][2] + m["judge"][2])
            worst = max(worst, loss)
        return {"situations": n, "zero gaps in belief and judge": zero, "of which the verdict is not best": zero_bad,
                "loss above the sum of the two gaps": bound_fail, "largest loss": worst}

    rows = survey()
    fixed = {r["cand"].name.replace("|actual/actual/actual", ""): over(r["cand"]) for r in admissible(rows)}
    table = {r["cand"].name.replace("|actual/actual/actual", ""): over(r["cand"]) for r in admissible(rows, reading="table")}
    fails_table = sorted(k for k, v in table.items() if v["of which the verdict is not best"])
    # a verdict that stands and is wrong: silence against silence at a hard world
    cand = S.chain()
    ctx = run_step(cand, (0, "hard"), {}, {}, dict(cand.mech))
    standing_wrong = (not classify(cand, (0, "hard"), [{}], [{}])[0]) and ctx.moves["judge"] != 0
    ok = all(v["of which the verdict is not best"] == 0 and v["loss above the sum of the two gaps"] == 0 for v in fixed.values())
    return {"supports": "holds on the stated domain" if ok else "refuted", "by admissible candidate": fixed,
            "table reading: candidates under which zero gaps leave a wrong verdict": fails_table,
            "a standing verdict that is wrong (null at (0, hard))": standing_wrong}


# --- statement 6 ----------------------------------------------------------------------

AVAILABLE = {
    "chain": [S.CHAIN_ACTIONS[a] for a in S.CHAIN_INPUTS],
    "shop": [S.SHOP[k] for k in ("silence", "truthful", "lie_B", "A_only", "B_only", "claim_B", "remark")],
    "pool": [{"display": d} for d in (None, "neutral", "planner", "all", "careful")],
    "values": [S.VALUES[k] for k in ("null", "lie_X", "expose_X", "partial_X")],
    "stuck": [{}, {"signal": "hi"}, {"signal": "lo"}],
}


def best_action(cand, world, base, by="gaps"):
    """The available action leaving her parts the least total gap, or the most by her goal;
    the first in the list among equals."""
    scene = cand.name.split("[")[0]

    def total_gap(a):
        ctx = run_step(cand, world, merge(base, a), cand.init(world), dict(cand.mech))
        return sum(g for _, _, g in measures(cand, ctx).values()) if by == "gaps" else -cand.goal(ctx)
    return min(AVAILABLE[scene], key=total_gap)


def comparisons():
    """Each single-step adviser case of the bank under three comparison actions."""
    table = {}
    for case in all_cases():
        for name, spec in case.variants.items():
            if spec.mode != "kinds" or spec.view or len(spec.act(spec.worlds[0])) != 1:
                continue
            if any(forced_parts(spec.act(w)[0]) or spec.act(w)[0].get("offer") for w in spec.worlds):
                continue
            row = {}
            for label, comp in (("silence", lambda w: {}), ("honest arm", lambda w: spec.comp(w)[0]),
                                ("least total gap", lambda w: best_action(spec.cand, w, spec.base(w)[0])),
                                ("best for her goal", lambda w: best_action(spec.cand, w, spec.base(w)[0], "goal"))):
                kinds = set()
                for w in spec.worlds:
                    ks, _ = classify(spec.cand, w, spec.act(w), [comp(w)], spec.base(w))
                    kinds |= ks
                row[label] = any(k == "subversion" for k, _ in kinds)
            table[case.id + ("" if name == "v" else name)] = row
    return table


def legit(cand, world, action, comparison=None, cutoff=F(0)):
    """No part her action depends on is forced, or subverted beyond the cut-off, against the comparison."""
    kinds, _ = classify(cand, world, [action], [comparison or {}], cutoff=cutoff)
    return not any(k in ("subversion", "force") for k, _ in kinds)


def check_6():
    table = comparisons()
    labels = ("silence", "honest arm", "least total gap", "best for her goal")
    counts = {label: sum(r[label] for r in table.values()) for label in labels}
    nested = {"silence inside least total gap": sorted(c for c, r in table.items() if r["silence"] and not r["least total gap"]),
              "silence inside best for her goal": sorted(c for c, r in table.items() if r["silence"] and not r["best for her goal"])}
    moved = {cid: r for cid, r in table.items() if len(set(r.values())) > 1}
    # the Scoring: V in [0,1] on Legit, a window value in [-δ, 0) otherwise
    delta, lam = F(1), F(3)
    rows = admissible(survey())
    G = S.chain_goal()
    bounds_ok = True

    def V(cand, w, a):
        ctx = run_step(cand, w, a, {}, dict(cand.mech))
        return G(ctx) / 3 if legit(cand, w, a) else -delta / 2

    def N(cand, w, a):          # her action, taken as reserved: settled by force, or by a verdict that does not stand
        return 0 if legit(cand, w, a) else 1

    decision = {}
    for name in S.CHAIN_INPUTS + ("force",):
        a = S.CHAIN_ACTIONS[name]
        u = v = F(0)
        for r in rows:
            for w in WORLDS:
                weight = PRIOR[w] / len(rows)
                val = V(r["cand"], w, a)
                bounds_ok &= (0 <= val <= 1) if legit(r["cand"], w, a) else (-delta <= val < 0)
                u += weight * (val - lam * N(r["cand"], w, a))
                v += weight * N(r["cand"], w, a)
        decision[name] = {"U": u, "v": v}
    respects = decision["null"]["v"] == 0
    # aim-independence against widening no gap
    cand = S.chain()
    aim_free_widens = any(not legit(cand, w, S.CHAIN_ACTIONS["lie"]) for w in WORLDS)
    selective = lambda aim, w: S.CHAIN_ACTIONS["teach"] if w[0] == aim else {}
    widens_none = all(not any(k == "subversion" for k, _ in classify(cand, w, [selective(aim, w)], [{}])[0])
                      for aim in (0, 1) for w in WORLDS)
    chosen = {aim: sum(PRIOR[w] * run_step(cand, w, selective(aim, w), {}, dict(cand.mech)).moves["act"] for w in WORLDS)
              for aim in (0, 1)}
    # against the least-total-gap baseline itself: follow it, except threaten at (0, clear)
    base_pol = {w: best_action(cand, w, {}) for w in WORLDS}
    threat_pol = dict(base_pol)
    threat_pol[(0, "clear")] = S.CHAIN_ACTIONS["threat"]
    threat_widens = any(k == "subversion" for w in WORLDS for k, _ in classify(cand, w, [threat_pol[w]], [base_pol[w]])[0])
    x_of = lambda pol: sum(PRIOR[w] * run_step(cand, w, pol[w], {}, dict(cand.mech)).moves["act"] for w in WORLDS)
    g_of = lambda pol: sum(PRIOR[w] * G(run_step(cand, w, pol[w], {}, dict(cand.mech))) for w in WORLDS)
    ok = bounds_ok and respects
    return {"supports": "holds on the stated domain" if ok else "refuted",
            "bank cases compared": len(table), "of which subversion, by comparison": counts, "cases that move": moved,
            "convicted against silence and not against": nested,
            "the baseline with a threat at (0, clear): widens a gap against the baseline": threat_widens,
            "probability she chooses 1: baseline, with the threat": [x_of(base_pol), x_of(threat_pol)],
            "her expected goal: baseline, with the threat": [g_of(base_pol), g_of(threat_pol)],
            "V within the Scoring's bounds": bounds_ok, "the null action respects": respects, "decision": decision,
            "admissible candidates weighted": len(rows),
            "aim-free and widens a gap (lie at every aim)": aim_free_widens,
            "aim-dependent and widens none (teaches only what favours its aim)": widens_none,
            "probability she chooses 1, by the adviser's aim": chosen}


# --- statement 7 ----------------------------------------------------------------------

def checker(view):          # a maintained belief mechanism: a message against her own signal is not taken
    n, m, r = view
    if n == "garbled":
        return (m if m is not None else 0, r)
    return (n if (m is not None and m != n) else (m if m is not None else n), r)


def check_7():
    # (a) maintenance: she is seen to replace her belief mechanism by `checker`
    mix = [({}, H), (S.CHAIN_ACTIONS["teach"], F(3, 10)), (S.CHAIN_ACTIONS["lie"], F(2, 10))]
    maintenance = {}
    for purpose in ("acc", "acc_theta", "mech"):
        cand = S.chain((purpose, "world", "world"))
        p = cand.part["belief"]
        score = {}
        for label, mech in (("before", S.belief_mech), ("after", checker)):
            total = F(0)
            for w in WORLDS:
                for a, pa in mix:
                    ctx = run_step(cand, w, a, {}, dict(cand.mech))
                    total += PRIOR[w] * pa * p.goal(ctx, mech(ctx.views["belief"]))
            score[label] = total
        maintenance[purpose] = {**score, "coherent": score["after"] >= score["before"]}
    rows = admissible(survey(), reading="table")
    excluded = names(r for r in rows if not maintenance[r["tags"]["purposes"][0]]["coherent"])
    left = [r for r in rows if maintenance[r["tags"]["purposes"][0]]["coherent"]]
    left_ag = agreement(left)
    # (b) taking back: after the adviser's hidden inputs are withdrawn and told, does her action change?
    cand = S.chain()
    open_keys = ("k", "c", "hard")
    table, agree, n = {}, 0, 0
    for name in INPUTS:
        a = S.CHAIN_ACTIONS[name]
        told = {k: v for k, v in a.items() if k in open_keys}
        for w in WORLDS:
            x1 = run_step(cand, w, a, {}, dict(cand.mech)).moves["act"]
            x2 = run_step(cand, w, told, {}, dict(cand.mech)).moves["act"]
            sub = any(k == "subversion" for k, _ in classify(cand, w, [a], [{}])[0])
            n += 1
            agree += int(sub == (x1 != x2))
            if sub != (x1 != x2):
                table.setdefault(name, []).append((w, "subverted, not taken back" if sub else "taken back, not subverted"))
    # passive histories: two admissible candidates with the same mechanisms disagree
    passive = agreement(rows)["split at some world"]
    none_separates = bool(passive) and bool(left_ag["split at some world"]) and agree < n
    return {"supports": "holds on the stated domain" if none_separates else "refuted",
            "histories alone: actions the admissible candidates (table reading) split on": passive,
            "maintenance": maintenance, "admissible candidates it excludes": excluded,
            "left": left_ag["count"], "purposes left": left_ag["purposes"], "actions the rest still split on": left_ag["split at some world"],
            "taking back agrees with subversion at": "%d of %d" % (agree, n), "where it does not": table}


# --- statement 8 ----------------------------------------------------------------------

def opposition(cand, world, action, part):
    """What her goal loses when `part` plays a best move by its own goal function, the later
    mechanisms responding, against the best her goal could get from any move of `part`."""
    ctx = run_step(cand, world, action, cand.init(world), dict(cand.mech))
    p = cand.part[part]
    down = {m: cand.goal(run_step(cand, world, merge(action, {"force": {part: m}}), cand.init(world), dict(cand.mech)))
            for m in p.moves(ctx)}
    top = max(p.goal(ctx, m) for m in p.moves(ctx))
    return max(down.values()) - max(down[m] for m in p.moves(ctx) if p.goal(ctx, m) == top)


def check_8():
    cand = S.chain()
    found = {}
    for w, a, nu in S.chain_scope(extra=("storm", "tumour")):
        if forced_parts(a) or a.get("order"):
            continue
        name = [k for k, v in S.CHAIN_ACTIONS.items() if v is a][0]
        for part in ("belief", "judge", "act"):
            o = opposition(cand, w, a, part)
            if o > 0:
                found.setdefault(part, []).append((w, name, o, "usual" if nu > 0 else "not usual"))
    fails, _ = admissibility(cand, S.chain_scope(), S.chain_behaviour())
    usual = sorted({(w[1], n) for rows in found.values() for (w, n, o, u) in rows if u == "usual"})
    events = sorted({w[1] for rows in found.values() for (w, n, o, u) in rows})
    # does it reduce to whether the part's own move is right?  It reads no mechanism of the part:
    alt = S.chain(mechs=("alt", "actual", "actual"))
    same = all(opposition(cand, w, a, "belief") == opposition(alt, w, a, "belief")
               for w, a, nu in S.chain_scope(extra=("storm", "tumour")) if not forced_parts(a) and not a.get("order"))
    return {"supports": "holds on the stated domain" if same and found else "refuted",
            "parts opposed somewhere": {k: len(v) for k, v in found.items()},
            "world events at which some part is opposed": events, "among usual situations": usual,
            "the stated candidate fails": sorted(fails),
            "unchanged when the part's own mechanism is replaced": same,
            "examples": {k: v[:3] for k, v in found.items()}}


# --- statement 9 ----------------------------------------------------------------------

def nlo_forms(cand, world, action):
    ctx = run_step(cand, world, action, cand.init(world), dict(cand.mech))
    profs = list(profiles(cand, ctx))
    tops = {p.name: max(p.goal(c, c.moves[p.name]) for c in profs) for p in cand.parts}
    gmax = max(cand.goal(c) for c in profs)
    full = [c for c in profs if all(p.goal(c, c.moves[p.name]) == tops[p.name] for p in cand.parts)]
    settled = [c for c in profs if all(g == 0 for _, _, g in measures(cand, c).values())]
    return {"adopted": "vacuous" if not full else all(cand.goal(c) == gmax for c in full),
            "equilibrium": all(cand.goal(c) == gmax for c in settled), "settled profiles": len(settled)}


def check_9():
    rows = survey()
    cheat = next(r for r in rows if r["tags"]["purposes"] == ("mech", "mech", "mech") and r["tags"]["goal"] == "true"
                 and r["tags"]["mechs"] == ("actual",) * 3)
    always_serving_fails = all(x == 1 for x in cheat["serving"].values()) and "nothing left over" in cheat["wide"]
    deaf = S.chain(mechs=("actual", "deaf", "actual"))
    deaf_fails, deaf_info = admissibility(deaf, S.chain_scope(), S.chain_behaviour())
    holds_without_serving = "nothing left over" not in deaf_fails and deaf_info["serving"]["judge"] < TAU
    fifteen = admissible(rows, reading="table")
    vac = {"table reading: candidates with a vacuous situation": sum(1 for r in fifteen if r["vacuous"]),
           "stated reading": sum(1 for r in admissible(rows) if r["vacuous"])}
    st = S.stuck()
    stuck_forms = nlo_forms(st, "lo", {})
    tumour = nlo_forms(S.chain(), (1, "tumour"), {})
    resolve = sorted(classify(st, "lo", [{"signal": "hi"}], [{}])[0])
    at_stuck = measures(st, run_step(st, "lo", {}, {}, dict(st.mech)))
    ok = always_serving_fails and stuck_forms["adopted"] is True and stuck_forms["equilibrium"] is False
    return {"supports": "holds on the stated domain" if ok else "refuted",
            "every part always serving, nothing left over failing (purposes equal to mechanisms)": always_serving_fails,
            "nothing left over holding with a part serving on less than 9/10 (the deaf judge)": holds_without_serving,
            "joint attainability": vac,
            "Stuck at (lo, lo): gaps": {k: v[2] for k, v in at_stuck.items()}, "Stuck, the two forms": stuck_forms,
            "the signal hi at the stuck point": resolve,
            "Chain, tumour: the two forms": tumour,
            "situations of Chain's scope where the adopted form is vacuous (stated candidate)": next(
                r for r in rows if r["tags"]["purposes"] == ("acc", "world", "world") and r["tags"]["goal"] == "true"
                and r["tags"]["mechs"] == ("actual",) * 3)["vacuous"]}


CHECKS = {"1": check_1, "2": check_2, "3": check_3, "4": check_4, "5": check_5, "6": check_6, "7": check_7,
          "8": check_8, "9": check_9}
