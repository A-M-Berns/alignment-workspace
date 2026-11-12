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
        base -= {"fit", "nothing left over"}
        wide = base | ({"fit"} - {"fit"} if info["fit"]["scope"] else {"fit"}) | (set() if info["nlo"]["scope"] else {"nothing left over"})
        narrow = base | (set() if info["fit"]["usual"] else {"fit"}) | (set() if info["nlo"]["usual"] else {"nothing left over"})
        rows.append({"cand": cand, "tags": cand.tags, "wide": wide, "narrow": narrow,
                     "strong": any(info["optimal everywhere"].values()), "serving": info["serving"],
                     "vacuous": info["vacuous"]})
    return rows


def admissible(rows, tau=TAU, scope="wide", strong=False):
    out = []
    for r in rows:
        fails = set(r[scope])
        if any(rate < tau for rate in r["serving"].values()):
            fails.add("mostly serving")
        if strong and r["strong"]:
            fails.add("independent")
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


def check_1():
    rows = survey()
    fixed = admissible(rows)
    ag = agreement(fixed)
    grid = {}
    for tau in (F(1, 40), H, F(3, 4), F(9, 10), F(19, 20), F(1)):
        for scope in ("wide", "narrow"):
            for strong in (False, True):
                sel = admissible(rows, tau, scope, strong)
                a = agreement(sel) if sel else {"count": 0}
                grid["tau=%s, %s, %s" % (tau, "scope" if scope == "wide" else "usual only",
                                         "strong independent" if strong else "independent")] = {
                    "count": a["count"], "purposes": a.get("purposes"),
                    "split": a.get("actions split on whether they subvert"),
                    "split at some world": a.get("split at some world")}
    cheats = {}
    for name, (purposes, goal) in CHEATS.items():
        r = next(r for r in rows if r["tags"]["purposes"] == purposes and r["tags"]["goal"] == goal
                 and r["tags"]["mechs"] == ("actual",) * 3)
        fails = set(r["wide"]) | ({"mostly serving"} if any(x < TAU for x in r["serving"].values()) else set())
        cheats[name] = {"fails": sorted(fails), "fails with strong independent": sorted(fails | ({"independent"} if r["strong"] else set())),
                        "fails on usual only": sorted(set(r["narrow"]) | ({"mostly serving"} if any(x < TAU for x in r["serving"].values()) else set()))}
    simple = min(sum(p in ("local", "mech") for p in r["tags"]["purposes"]) for r in fixed)
    simplest = [r for r in fixed if sum(p in ("local", "mech") for p in r["tags"]["purposes"]) == simple]
    strong = admissible(rows, strong=True)
    # the decision rule over the admissible set
    decisions = {}
    sigs = [signature(r["cand"]) for r in fixed]
    for a in INPUTS:
        subs = [any(k == "subversion" for w in WORLDS for k, _ in s[(a, w)]) for s in sigs]
        good = sum(PRIOR[w] * (S.chain_goal()(run_step(S.chain(), w, S.CHAIN_ACTIONS[a], {}, dict(S.chain().mech)))
                               - S.chain_goal()(run_step(S.chain(), w, {}, {}, dict(S.chain().mech)))) for w in WORLDS) >= 0
        decisions[a] = "refuse" if all(subs) else ("act" if (good and not any(subs)) else ("ask" if any(subs) else "do not act"))
    determinate = len(fixed) >= 1 and all(len(v) == 1 for v in ag["purposes"].values()) and not ag["split at some world"]
    return {"supports": "holds on the stated domain" if determinate else "refuted",
            "class size": len(rows), "at the fixed parameters": ag,
            "admissible at the fixed parameters": sorted(r["cand"].name for r in fixed),
            "with strong independent": agreement(strong), "admissible with strong independent": sorted(r["cand"].name for r in strong),
            "simplest": {"count": len(simplest), **{k: v for k, v in agreement(simplest).items() if k != "count"}},
            "grid": grid, "cheats": cheats, "dependence": dependence(), "decision rule": decisions}


# --- statement 2 ----------------------------------------------------------------------

def check_2():
    rows = survey()
    fixed, strong = admissible(rows), admissible(rows, strong=True)

    def spared(sel, action, worlds):
        """Candidates under which the action widens no gap at any of the worlds."""
        return sorted(r["cand"].name for r in sel if not subverts(signature(r["cand"]), action, worlds))

    right = [w for w in WORLDS if w[1] != "misleading"]      # she is right about θ under null
    facts = {
        "lie, worlds where null leaves her right: candidates with no gap widened (fixed)": spared(fixed, "lie", right),
        "the same, at hard worlds only": spared(fixed, "lie", [w for w in WORLDS if w[1] == "hard"]),
        "the same, strong independent": spared(strong, "lie", right),
        "lie, misleading worlds, strong independent: candidates with no gap widened": len(spared(strong, "lie", [w for w in WORLDS if w[1] == "misleading"])),
        "strong independent, count": len(strong),
        "false_reason at clear worlds, strong independent: candidates with no gap widened": spared(strong, "false_reason", [w for w in WORLDS if w[1] == "clear"]),
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
        not facts["false_reason at clear worlds, strong independent: candidates with no gap widened"]
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
    refuted = bool(missed) or no_gap_fall or bank.get("Y4") == ["nothing"]
    return {"supports": "refuted" if refuted else "holds on the stated domain",
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
    cand = S.chain(("acc_theta", "local", "world"))
    G = S.chain_goal()
    zero, zero_bad, bound_fail, n, worst = 0, 0, [], 0, F(0)
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
        if loss > m["belief"][2] + m["judge"][2]:
            bound_fail.append((w, a))
        worst = max(worst, loss)
    ok = zero_bad == 0 and not bound_fail
    return {"supports": "holds on the stated domain" if ok else "refuted", "situations": n,
            "with zero gaps in belief and judge": zero, "of which the verdict is not best": zero_bad,
            "situations where the loss exceeds the sum of the two gaps": bound_fail, "largest loss": worst}


# --- statement 6 ----------------------------------------------------------------------

AVAILABLE = {
    "chain": [S.CHAIN_ACTIONS[a] for a in S.CHAIN_INPUTS],
    "shop": [S.SHOP[k] for k in ("silence", "truthful", "lie_B", "A_only", "B_only", "claim_B", "remark")],
    "pool": [{"display": d} for d in (None, "neutral", "planner", "all", "careful")],
    "values": [S.VALUES[k] for k in ("null", "lie_X", "expose_X", "partial_X")],
    "stuck": [{}, {"signal": "hi"}, {"signal": "lo"}],
}


def best_action(cand, world, base):
    scene = cand.name.split("[")[0]

    def total_gap(a):
        ctx = run_step(cand, world, merge(base, a), cand.init(world), dict(cand.mech))
        return sum(g for _, _, g in measures(cand, ctx).values())
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
                                ("best available", lambda w: best_action(spec.cand, w, spec.base(w)[0]))):
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
    counts = {label: sum(r[label] for r in table.values()) for label in ("silence", "honest arm", "best available")}
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
    ok = bounds_ok and respects
    return {"supports": "holds on the stated domain" if ok else "refuted",
            "bank cases compared": len(table), "of which subversion, by comparison": counts, "cases that move": moved,
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
    rows = admissible(survey())
    excluded = sorted(r["cand"].name for r in rows if not maintenance[r["tags"]["purposes"][0]]["coherent"])
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
    passive = left_ag["split at some world"]
    separates = not passive and all(len(v) == 1 for v in left_ag["purposes"].values()) and agree == n
    return {"supports": "refuted" if separates else "holds on the stated domain",
            "maintenance": maintenance, "admissible candidates it excludes": excluded,
            "left": left_ag["count"], "purposes left": left_ag["purposes"], "actions the rest still split on": passive,
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
    broken = next(r for r in rows if r["tags"]["purposes"] == ("acc", "world", "world") and r["tags"]["goal"] == "true"
                  and r["tags"]["mechs"] == ("alt", "alt", "alt"))
    holds_without_fit = "nothing left over" not in broken["wide"] and "fit" in broken["wide"]
    st = S.stuck()
    stuck_forms = nlo_forms(st, "lo", {})
    tumour = nlo_forms(S.chain(), (1, "tumour"), {})
    resolve = sorted(classify(st, "lo", [{"signal": "hi"}], [{}])[0])
    at_stuck = measures(st, run_step(st, "lo", {}, {}, dict(st.mech)))
    ok = always_serving_fails and stuck_forms["adopted"] is True and stuck_forms["equilibrium"] is False
    return {"supports": "holds on the stated domain" if ok else "refuted",
            "every part always serving, nothing left over failing (purposes equal to mechanisms)": always_serving_fails,
            "nothing left over holding with fit failing": holds_without_fit,
            "Stuck at (lo, lo): gaps": {k: v[2] for k, v in at_stuck.items()}, "Stuck, the two forms": stuck_forms,
            "the signal hi at the stuck point": resolve,
            "Chain, tumour: the two forms": tumour,
            "situations of Chain's scope where the adopted form is vacuous (stated candidate)": next(
                r for r in rows if r["tags"]["purposes"] == ("acc", "world", "world") and r["tags"]["goal"] == "true"
                and r["tags"]["mechs"] == ("actual",) * 3)["vacuous"]}


CHECKS = {"1": check_1, "2": check_2, "3": check_3, "4": check_4, "5": check_5, "6": check_6, "7": check_7,
          "8": check_8, "9": check_9}
