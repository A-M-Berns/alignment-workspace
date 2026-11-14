"""The checks behind RESULTS.md.  Each returns {"supports": status, ...numbers}.  For a statement
marked proved the proof is in RESULTS.md and the check runs the instances named there; for one
marked refuted the check exhibits the counterexample."""
from __future__ import annotations

import itertools
from dataclasses import replace
from fractions import Fraction as F

from . import cases as c
from .model import (NULL, Act, Part, Scene, action_grain, best_on_menu, choice, classify, condition, fit, gap,
                    knowledge_grain, no_grain, opposition, realized, rest, score, total, whole_gaps)

H2 = F(1, 2)
PROVED, HOLDS, REFUTED = "proved", "holds on the stated example", "refuted"

BELIEF = {"1": c.scene_1, "3": c.scene_3, "4": c.scene_4, "8": c.scene_8, "9": lambda: c.scene_8(on_item=F(1)),
          "13": lambda: c.scene_7("appendix"), "25": c.scene_25, "27": c.scene_27,
          "27b": lambda: c.scene_27(on_hard=F(1, 4)), "31": lambda: c.scene_4(on_h=F(10, 11)),
          "4b": c.scene_4b, "4c": c.scene_4c}


def grains(s, p):
    C = condition(s)
    return {"none": gap(s, p, C, no_grain(s)), "scene": gap(s, p, C), "action": gap(s, p, C, action_grain(s)),
            "knowledge": gap(s, p, C, knowledge_grain(s))}


def table():
    return {cid: grains(make(), make().parts[0]) for cid, make in BELIEF.items()}


def check(ok, status, **facts):
    return {"supports": status if ok else "CHECK FAILED", **facts}


# ---- question 1 --------------------------------------------------------------------------

def s_1_1():
    """Two scenes with the same state, move and utility at every state, and so the same gaps: in
    the first the adviser's action is a signal the acting part follows, in the second a force.  The
    actions differ; with their type forgotten nothing else does."""
    follow = Part("act", "choice", lambda th, a, mv: "comply" if a.signal == "go" else "refuse",
                  moves=("comply", "refuse"), util=lambda th, a, m, mv: {"comply": 0, "refuse": 1}[m])
    still = replace(follow, mech=lambda th, a, mv: "refuse")
    sig = Scene([("w", F(1))], [follow], rule=lambda k: Act("go"))
    frc = Scene([("w", F(1))], [still], rule=lambda k: Act(force=(("act", "comply"),)))
    same = ([(th, pr, mv) for th, pr, _, mv in condition(sig)] == [(th, pr, mv) for th, pr, _, mv in condition(frc)]
            and gap(sig, follow, condition(sig)) == gap(frc, still, condition(frc)))
    t1, t2 = classify(sig)[0], classify(frc)[0]
    return check(same and t2 - t1 == {"force(act)"} and t1 <= t2, HOLDS, signal=sorted(t1), force=sorted(t2))


def s_1_4():
    """A request must be made beforehand: case 22 with a requester that would not ask, forced by the
    adviser to ask while it alters A, is not covered."""
    s = c.scene_22()
    s.parts[0].mech = lambda th, a, mv: "not"
    forced = replace(s, rule=lambda k: Act(force=(("act", "ask"),), alter=(("A", "y2"),)),
                     requests=lambda mv: {("alteration", "A"), ("force", "act")} if mv["act"] == "ask" else set())
    tokens = classify(forced)[0]
    return check("covered" not in tokens and "illegitimate" in tokens and "covered" in classify(c.scene_22())[0],
                 HOLDS, forced_request=sorted(tokens))


def s_1_2():
    """What a view would add: the gap when the re-reading may use the adviser's action."""
    t = table()
    wider = {cid: (g["scene"], g["action"]) for cid, g in t.items() if g["action"] > g["scene"]}
    ok = (set(wider) >= {"3", "27"} and "4b" not in wider and "8" not in wider
          and t["13"]["action"] == 0 < t["13"]["knowledge"])
    return check(ok, HOLDS, wider=wider, buried=t["13"])


def s_1_3():
    """Subversion read with no comparison (a part out of range whose move the adviser's action
    changes somewhere): the rows whose verdict changes."""
    changed = {}
    for cid, make in c.SCENES.items():
        s = make()
        if s.rule is None:
            continue
        C, C0 = condition(s), condition(s, None)
        alt = any(gap(s, p, C) > 0 and any(m1[p.name] != m0[p.name] for (*_, m1), (*_, m0) in zip(C, C0))
                  for p in s.parts)
        tokens, _ = classify(s)
        if alt and "illegitimate" not in tokens:
            changed[cid] = "illegitimate under the alternative"
    s9 = c.scene_8(on_item=F(1))
    p = s9.parts[0]
    return check(set(changed) == {"9"}, HOLDS, changed=changed, gap_9=gap(s9, p, condition(s9)),
                 gap_9_null=gap(s9, p, condition(s9, None)))


# ---- question 2 --------------------------------------------------------------------------

def s_2_1():
    t = table()
    ok = all(0 <= g["none"] <= g["scene"] <= g["action"] <= g["knowledge"] for g in t.values())
    return check(ok, PROVED, table=t)


def s_2_2():
    """(E[w (e − q)])² ≤ E[w²] · gap at the grain, for w an indicator of a set of grain values."""
    n = 0
    for cid, make in BELIEF.items():
        s = make()
        p = s.parts[0]
        if p.form != "estimate":
            continue
        C = condition(s)
        for key in (no_grain(s), knowledge_grain(s)):
            g = gap(s, p, C, key)
            values = sorted({repr(key(th, a)) for th, _, a, _ in C})
            for r in range(1, len(values) + 1):
                for E in itertools.combinations(values, r):
                    lhs = sum(pr * (mv[p.name] - p.target(th, a)) for th, pr, a, mv in C if repr(key(th, a)) in E)
                    mass = sum(pr for th, pr, a, _ in C if repr(key(th, a)) in E)
                    if lhs ** 2 > mass * g:
                        return check(False, PROVED, case=cid, E=E)
                    n += 1
    return check(True, PROVED, instances=n)


def s_2_3():
    t = table()
    ok = (t["4b"]["action"] == 0 < t["4b"]["knowledge"]
          and all(t[k]["scene"] == 0 < t[k]["knowledge"] for k in ("3", "8", "27", "31"))
          and t["4c"]["none"] == 0 < t["4c"]["scene"])
    return check(ok, HOLDS, table={k: t[k] for k in ("3", "4", "4b", "4c", "8", "27", "27b", "31")})


def s_2_4():
    t = table()
    pool = {k: t[k]["knowledge"] - t[k]["action"] for k in t}
    ok = (t["4b"]["action"] == 0 < pool["4b"] and t["8"]["action"] == 0 < pool["8"]
          and pool["27"] == 0 < t["27"]["action"] and pool["3"] == 0 < t["3"]["action"])
    return check(ok, HOLDS, pooled={k: pool[k] for k in ("3", "4b", "8", "27")},
                 action={k: t[k]["action"] for k in ("3", "4b", "8", "27")})


def s_2_5():
    """Refuted: some grain of the four puts the believed rare lie with a two-valued move (4b) out of
    range and leaves honest difficulty (3, 27) in."""
    t = table()
    some = [g for g in ("none", "scene", "action", "knowledge")
            if t["4b"][g] > 0 and t["3"][g] == 0 and t["27"][g] == 0]
    return check(not some, REFUTED, per_grain={g: (t["4b"][g], t["3"][g], t["27"][g])
                                               for g in ("none", "scene", "action", "knowledge")})


def s_2_6():
    s = c.scene_4()
    p = s.parts[0]
    C = condition(s)
    g = gap(s, p, C)
    shift = sum(pr * (mv["listen"] - p.target(th, a)) for th, pr, a, mv in C)
    eta = F(1, 20)
    return check(g == eta ** 2 / (H2 + eta) and shift == eta and shift ** 2 <= g, HOLDS, gap=g, shift=shift)


# ---- question 3 --------------------------------------------------------------------------

def cal_gap(rows, i_v, i_q):
    groups = {}
    for row in rows:
        groups.setdefault(row[i_v], []).append((row[0], row[i_q]))
    return sum(sum(pr for pr, _ in g) * (v - sum(pr * q for pr, q in g) / sum(pr for pr, _ in g)) ** 2
               for v, g in groups.items())


def three_terms(rows):
    """rows: [(pr, V0, VT, q0, qT)].  |D − Δq| ≤ √g0 + √gT, checked without square roots."""
    D = sum(pr * (vT - v0) for pr, v0, vT, _, _ in rows)
    dq = sum(pr * (qT - q0) for pr, _, _, q0, qT in rows)
    g0, gT = cal_gap(rows, 1, 3), cal_gap(rows, 2, 4)
    a = (D - dq) ** 2 - g0 - gT
    return (a <= 0 or a ** 2 <= 4 * g0 * gT), D, dq, g0, gT


def s_3_1():
    grid = (F(0), H2, F(1))
    n = 0
    for vals in itertools.product(grid, repeat=8):
        rows = [(H2, vals[0], vals[1], vals[2], vals[3]), (H2, vals[4], vals[5], vals[6], vals[7])]
        if not three_terms(rows)[0]:
            return check(False, PROVED, rows=rows)
        n += 1
    dep = three_terms([(H2, H2, F(1), F(1), F(1)), (H2, F(1, 4), H2, H2, H2)])
    return check(dep[0], PROVED, instances=n, depression={"D": dep[1], "Δq": dep[2], "g_0": dep[3], "g_T": dep[4]})


WORTH = [(F(1), H2), (H2, H2)]


def mech_stats(mu):
    """mu: {worth: verdict}.  (loss, calibration gap, bias)."""
    rows = [(pr, mu[w], w) for w, pr in WORTH]
    return (sum(pr * (v - q) ** 2 for pr, v, q in rows), cal_gap(rows, 1, 2), sum(pr * (v - q) for pr, v, q in rows))


def recal(mu):
    out = {}
    for w, _ in WORTH:
        same = [(pr, w2) for w2, pr in WORTH if mu[w2] == mu[w]]
        out[w] = sum(pr * w2 for pr, w2 in same) / sum(pr for pr, _ in same)
    return out


def s_3_2():
    """A maintaining part in range whose menu is closed under re-reading installs a mechanism in range."""
    grid = (H2, F(3, 4), F(1))
    mechs = [dict(zip((F(1), H2), v)) for v in itertools.product(grid, repeat=2)]
    key = lambda mu: tuple(sorted(mu.items()))
    n = 0
    for r in range(1, len(mechs) + 1):
        for menu in itertools.combinations(mechs, r):
            keys = {key(mu) for mu in menu}
            if any(key(recal(mu)) not in keys for mu in menu):
                continue
            best = min(mech_stats(mu)[0] for mu in menu)
            if any(mech_stats(mu)[0] == best and mech_stats(mu)[1] != 0 for mu in menu):
                return check(False, PROVED, menu=menu)
            n += 1
    flat, tilted = {F(1): F(3, 4), H2: F(3, 4)}, {F(1): F(7, 8), H2: F(3, 8)}
    return check(mech_stats(tilted)[0] < mech_stats(flat)[0] and mech_stats(tilted)[1] > 0, PROVED, closed_menus=n,
                 unclosed={"flat": mech_stats(flat), "tilted": mech_stats(tilted)})


def s_3_3():
    """Refuted: every foreseeable shift traces to a mechanism altered by something out of range or
    by the adviser.  (a) nobody's alteration; (b) a maintaining part in range with an unclosed menu;
    (c) an end revised by a part in range."""
    a = three_terms([(H2, F(1), H2, F(1), F(1)), (H2, H2, F(1, 4), H2, H2)])
    tilted = {F(1): F(7, 8), H2: F(3, 8)}
    b = mech_stats(tilted)
    t17, f17 = c.case_17()
    ok = a[1] != 0 and b[2] != 0 and "in-range" in t17 and f17["verdict shift"] != 0
    return check(ok, REFUTED, nobody={"D": a[1]}, unclosed={"bias": b[2], "gap": b[1]},
                 law_to_music={"D": f17["verdict shift"]})


def s_3_4():
    tokens, facts = c.case_18()
    ok = {"shift", "whole-gap", "change: legitimate", "not adviser's"} <= tokens and facts["gap before"] > 0 == facts["gap after"]
    return check(ok, HOLDS, **facts)


# ---- question 4 --------------------------------------------------------------------------

def s_4_1():
    gaps = {}
    for name in (None, "threat", "offer"):
        s = c.scene_10(Act(conseq=name))
        gaps[str(name)] = gap(s, s.parts[0], condition(s))
    return check(all(g == 0 for g in gaps.values()), PROVED, gaps=gaps)


def s_4_2():
    t10, t11a, t11b = (c.CASES[k]()[0] for k in ("10", "11a", "11b"))
    ok = ("harm(act)" in t10 and "help(act)" in t11a
          and not any(t.startswith(("harm", "help")) for t in t11b) and "better-off(act)" in t11b)
    return check(ok, HOLDS, threat=sorted(t10), offer=sorted(t11a), warning=sorted(t11b))


def s_4_3():
    # 33a and 33b are one scene by construction; they differ in a supplied fact about the branch
    # not taken, which only the second null reads
    (ta, fa), (tb, fb) = c.case_33(False), c.case_33(True)
    ok = ta == tb and fa["harm under the second null"] and not fb["harm under the second null"]
    return check(ok, HOLDS, absence_null=sorted(ta), second_null={"33a": fa["harm under the second null"],
                                                                   "33b": fb["harm under the second null"]})


# ---- question 5 --------------------------------------------------------------------------

def s_5_1():
    X = ["a", "b", "c"]
    grid = (0, 1, 2)
    n = 0
    for r in itertools.product(grid, repeat=3):
        R = {"rest": dict(zip(X, r))}
        top = max(r)
        for v in itertools.product(grid, repeat=3):
            new = dict(zip(X, v))
            ends = {**R, "j": {}}
            f = fit("j", new, ends, X)
            x = choice({**ends, "j": new}, X)
            best_new = [y for y in X if new[y] == max(v)]
            meets = total(R, x) == top and any(total(R, y) == top for y in best_new)
            if f > top or (f == top) != meets or fit("j", {}, ends, X) != top:
                return check(False, PROVED, rest=r, new=v)
            n += 1
    return check(True, PROVED, instances=n)


def s_5_2():
    menu = {**c.LAW_MENU, "drop": {}, "joy": {"music": 1}, "half": {"music": H2}}
    top, scores = best_on_menu("career", menu, c.LAW, ["law", "music"])
    return check(len(top) >= 3, HOLDS, greatest=top, fit=scores)


def s_5_3():
    X = ["x", "y"]
    ends = {"A": {"x": 3}, "B": {"y": 2}}
    top_a, sa = best_on_menu("A", {"keep": {"x": 3}, "as-B": {"y": 3}}, ends, X)
    top_b, sb = best_on_menu("B", {"keep": {"y": 2}, "as-A": {"x": 2}}, ends, X)
    xa, xb = choice({**ends, "A": {"y": 3}}, X), choice({**ends, "B": {"x": 2}}, X)
    ok = top_a == ["as-B"] and top_b == ["as-A"] and xa != xb and total(ends, xa) != total(ends, xb)
    return check(ok, HOLDS, revise_A=sa, revise_B=sb, outcomes=(xa, xb),
                 starting_totals={x: total(ends, x) for x in X})


def fit_all(j, v_new, ends, X):
    """Fit judged by all her ends, the one under revision included."""
    x = choice({**ends, j: v_new}, X)
    return total(ends, x) - opposition(v_new, ends, X)


def s_5_4():
    """Refuted: if every step of a chain is legitimate, her starting ends value the final choice at
    least as much as the starting one."""
    tokens, facts = c.case_29()
    start = facts["starting totals"]
    x0 = choice(c.HIJACK, c.HIJACK_X)
    ok = "in-range" in tokens and start[facts["final choice"]] < start[x0]
    # the same chain judged by all her ends
    ends = dict(c.HIJACK)
    blocked = None
    for j, menu, taken in c.HIJACK_STEPS:
        scores = {name: fit_all(j, v, ends, c.HIJACK_X) for name, v in menu.items()}
        if scores[taken] < max(scores.values()):
            blocked = (j, scores)
            break
        ends[j] = menu[taken]
    # and by what the rest attains alone
    _, log_att = c.run_chain(c.HIJACK, c.HIJACK_X, c.HIJACK_STEPS, attained_only=True)
    return check(ok and blocked is not None and blocked[0] == "B", REFUTED, start=start, final=facts["final choice"],
                 steps=[(s["end"], s["fit"]) for s in facts["steps"]], judged_by_all_blocked_at=blocked,
                 attained_alone=[(s["end"], s["fit"], s["greatest"]) for s in log_att])


def s_5_5():
    _, facts = c.case_20()
    return check(facts["afterwards, greatest fit for D"] == ["new"], HOLDS, fit=facts["afterwards, fit of revising D"])


def tie_scene(with_b):
    """The adviser's aim decides which of two equally fitting replacements A's revising part
    installs.  With `with_b`, B's revising part is among the parts and takes its menu's best."""
    menu = {"keep": {"w": 3, "x": 2}, "drop": {}, "as-B": {"x": 3}}
    menu_b = c.HIJACK_STEPS[1][1]

    def after_a(mv):
        return {**c.HIJACK, "A": menu[mv["revise-A"]]}
    parts = [Part("revise-A", "choice", lambda th, a, mv: a.signal or "keep", moves=tuple(menu),
                  util=lambda th, a, m, mv: fit("A", menu[m], c.HIJACK, c.HIJACK_X))]
    if with_b:
        parts.append(Part("revise-B", "choice",
                          lambda th, a, mv: best_on_menu("B", menu_b, after_a(mv), c.HIJACK_X)[0][0],
                          moves=tuple(menu_b), util=lambda th, a, m, mv: fit("B", menu_b[m], after_a(mv), c.HIJACK_X)))
    aims = {"z": lambda k: Act("drop"), "x": lambda k: Act("as-B")}
    return Scene([("w", F(1))], parts, rule=aims["z"], aims=aims)


def s_5_6():
    from .model import breaks_tie
    menu = {"keep": {"w": 3, "x": 2}, "drop": {}, "as-B": {"x": 3}}
    top, scores = best_on_menu("A", menu, c.HIJACK, c.HIJACK_X)
    finals = {}
    for name in top:
        ends, _ = c.run_chain(c.HIJACK, c.HIJACK_X, (("A", menu, name),))
        topb, _ = best_on_menu("B", c.HIJACK_STEPS[1][1], ends, c.HIJACK_X)
        ends["B"] = c.HIJACK_STEPS[1][1][topb[0]]
        finals[name] = choice(ends, c.HIJACK_X)
    alone, both = tie_scene(False), tie_scene(True)
    scores_b = {aim: score(both, both.parts[1], condition(both, rule)) for aim, rule in both.aims.items()}
    ok = (sorted(top) == ["as-B", "drop"] and finals["drop"] != finals["as-B"]
          and breaks_tie(alone) and not breaks_tie(both) and "illegitimate" not in classify(both)[0])
    return check(ok, HOLDS, fit=scores, finals=finals, tie_with_A_alone=breaks_tie(alone),
                 tie_with_B_listed=breaks_tie(both), B_utility_by_aim=scores_b, tokens_with_B=sorted(classify(both)[0]))


def s_5_7():
    (t17, f17), (t23, f23) = c.case_17(), c.case_23()
    ok = all(f["verdict shift"] != 0 and f["g_0"] > 0 and f["g_T"] > 0 and f["verdict shift"] ** 2 <= min(f["g_0"], f["g_T"])
             for f in (f17, f23))
    return check(ok and "illegitimate" in t23 and "change: legitimate" in t17, HOLDS,
                 law_to_music=(f17["verdict shift"], f17["g_0"], f17["g_T"]),
                 made_to_like=(f23["verdict shift"], f23["g_0"], f23["g_T"]))


# ---- question 6 --------------------------------------------------------------------------

def aggregate(fn):
    s = c.scene_30()
    whole = Part("whole", "estimate", fn, target=lambda th, a: c.is_h(th[0]))
    s2 = replace(s, parts=s.parts + [whole])
    C = condition(s2)
    return gap(s2, whole, C), sum(pr * mv["whole"] for _, pr, _, mv in C), [gap(s2, p, C) for p in s.parts]


def posterior(th, a, mv):
    like = {("H", "H"): F(9, 10), ("H", "L"): H2, ("L", "H"): H2, ("L", "L"): F(1, 10)}
    return like[(th[1], th[2])]


def s_6_1():
    g, mean, parts = aggregate(posterior)
    return check(g == 0 and mean == H2, PROVED, gap=g)


def s_6_2():
    """Refuted: every part in range gives a verdict that is a function of their moves in range."""
    g, mean, parts = aggregate(lambda th, a, mv: max(mv["listen1"], mv["listen2"]))
    return check(all(x == 0 for x in parts) and g > 0 and mean != H2, REFUTED, gap=g, mean_verdict=mean, mean_target=H2)


def s_6_3():
    s = c.scene_1()
    flat = Part("verdict", "estimate", lambda th, a, mv: H2, target=c.is_h)
    s2 = replace(s, parts=s.parts + [flat])
    C = condition(s2)
    gl, gv = gap(s2, s2.parts[0], C), gap(s2, flat, C)
    return check(gl > 0 and gv == 0, HOLDS, listen=gl, verdict=gv)


def s_6_4():
    g, mean, parts = aggregate(lambda th, a, mv: (mv["listen1"] + mv["listen2"]) / 2)
    return check(mean == H2 and g > 0, PROVED, gap=g, mean_verdict=mean)


# ---- question 7 --------------------------------------------------------------------------

def paths(K, p_next):
    out = [((), F(1))]
    for _ in range(K):
        out = [(h + (x,), pr * (p_next(h) if x else 1 - p_next(h))) for h, pr in out for x in (1, 0)]
    return out


def excess_moments(K, p_next, estimate):
    m1 = m2 = F(0)
    for h, pr in paths(K, p_next):
        e = sum(estimate(h[:k]) - h[k] for k in range(K)) / K
        m1 += pr * e
        m2 += pr * e * e
    return m1, m2


def s_7_1():
    """An estimator of the score in range at the grain of the history: E[excess_K] = 0 and
    E[excess_K²] = (1/K²) Σ E[(U_k − S_k)²] ≤ 1/(4K), for scores in {0, 1}."""
    p_next = lambda h: H2 if not h else F(1, 4) + H2 * h[-1]
    out = {}
    for K in (1, 2, 3, 4, 5):
        m1, m2 = excess_moments(K, p_next, p_next)
        var = sum(pr * p_next(h[:k]) * (1 - p_next(h[:k])) for h, pr in paths(K, p_next) for k in range(K)) / K ** 2
        if m1 != 0 or m2 != var or m2 > F(1, 4 * K):
            return check(False, PROVED, K=K)
        out[K] = m2
    return check(True, PROVED, second_moment=out)


def s_7_2():
    """Refuted: in range with no conditioning on the history gives the same.  One coin, scored at
    every step; the estimate 1/2 is calibrated at each step taken alone."""
    p_next = lambda h: H2 if not h else F(h[-1])
    out = {K: excess_moments(K, p_next, lambda h: H2)[1] for K in (1, 2, 3, 4, 5)}
    return check(all(v == F(1, 4) for v in out.values()), REFUTED, second_moment=out)


def realizes(s, part):
    """`Realizes β x f κ D` of TransparentChannel.lean with q an aim, z a state, x the signal, f the
    part's move and κ the part's own mechanism."""
    p = s.part(part)
    for rule in s.aims.values():
        for th, _ in s.states:
            a = rule(s.know(th))
            if realized(s, th, a)[part] != p.mech(th, Act(signal=a.signal), {}):
                return False
    return True


def blind(s, part):
    return all(len({realized(s, th, rule(s.know(th)))[part] for rule in s.aims.values()}) == 1 for th, _ in s.states)


def s_7_3():
    s14 = c.scene_14()
    forced = replace(s14, aims={"x": lambda k: Act(force=(("act", "y"),)), "y": lambda k: NULL})
    const = replace(s14, aims={"x": lambda k: Act("x-first"), "y": lambda k: Act("x-first")})
    # the reviewer's counterexample: no force, no alteration, one signal, a mechanism that reads
    # the consequence component, which varies with the aim
    reads = Part("act", "choice", lambda th, a, mv: "y" if a.conseq else "x", moves=("x", "y"),
                 util=lambda th, a, m, mv: 1)
    conseq = replace(s14, parts=[reads], aims={"x": lambda k: Act(conseq=0), "y": lambda k: Act(conseq=1)})
    # and a force that happens to set the move the mechanism would have made
    idle = replace(s14, aims={"x": lambda k: Act("x-first", force=(("act", "x"),)), "y": lambda k: Act("x-first")})
    rows = {"signal by aim (14)": (realizes(s14, "act"), False, blind(s14, "act")),
            "force by aim": (realizes(forced, "act"), True, blind(forced, "act")),
            "one signal at every aim": (realizes(const, "act"), True, blind(const, "act")),
            "a mechanism reading the consequence": (realizes(conseq, "act"), True, blind(conseq, "act")),
            "a force that sets the move the mechanism makes": (realizes(idle, "act"), True, blind(idle, "act"))}
    ok = (rows["signal by aim (14)"] == (True, False, False) and rows["force by aim"][0] is False
          and rows["one signal at every aim"] == (True, True, True)
          and rows["a mechanism reading the consequence"] == (False, True, False)
          and rows["a force that sets the move the mechanism makes"] == (True, True, True))
    return check(ok, HOLDS, rows={k: {"Realizes": v[0], "signal the same at every aim": v[1], "move the same at every aim": v[2]}
                                  for k, v in rows.items()})


def s_7_4():
    """Legit is not a function of the realized history: one history under two rules."""
    liar = c.scene_4()
    honest = replace(liar, rule=lambda k: Act("H" if k == "H" else "L"))
    h1 = [(th, a, mv) for th, _, a, mv in condition(liar) if th == "H"]
    h2 = [(th, a, mv) for th, _, a, mv in condition(honest) if th == "H"]
    t1, t2 = classify(liar)[0], classify(honest)[0]
    return check(h1 == h2 and "illegitimate" in t1 and "illegitimate" not in t2, HOLDS)


CHECKS = {"1.1": s_1_1, "1.2": s_1_2, "1.3": s_1_3, "1.4": s_1_4,
          "2.1": s_2_1, "2.2": s_2_2, "2.3": s_2_3, "2.4": s_2_4, "2.5": s_2_5, "2.6": s_2_6,
          "3.1": s_3_1, "3.2": s_3_2, "3.3": s_3_3, "3.4": s_3_4,
          "4.1": s_4_1, "4.2": s_4_2, "4.3": s_4_3,
          "5.1": s_5_1, "5.2": s_5_2, "5.3": s_5_3, "5.4": s_5_4, "5.5": s_5_5, "5.6": s_5_6, "5.7": s_5_7,
          "6.1": s_6_1, "6.2": s_6_2, "6.3": s_6_3, "6.4": s_6_4,
          "7.1": s_7_1, "7.2": s_7_2, "7.3": s_7_3, "7.4": s_7_4}
