"""The checks behind THEOREMS.md, statements 1-8.  Each returns a dict whose "supports"
is the status the checks support; run.py compares it with the status THEOREMS.md gives."""
from __future__ import annotations

from fractions import Fraction as Fr
from itertools import combinations, product

from . import cases as C
from .model import (NULL, Case, bayes, clauses, flat, in_force, inp, representable, same_source, source, verdict,
                    show, widened, wr, writes_as_inputs)

W2 = (0, 1)
KERNELS = tuple(product((0, 1), repeat=2))       # a deterministic source W2 -> {0, 1}, as (k(0), k(1))
LAWS = ({0: Fr(1, 2), 1: Fr(1, 2)}, {0: Fr(1, 3), 1: Fr(2, 3)})


def subsets(xs):
    return [s for n in range(1, len(xs) + 1) for s in combinations(xs, n)]


def posterior(law, R, m):
    """Her posterior over W2 on message m when the source is uniform over R; None at probability zero."""
    post = {w: law[w] * sum(1 for k in R if k[w] == m) for w in W2}
    total = sum(post.values())
    return None if total == 0 else {w: p / total for w, p in post.items()}


def best(u, belief):
    return max(range(len(u)), key=lambda o: (sum(belief[w] * u[o][w] for w in W2), -o))


# -- 1. her later judgment -----------------------------------------------------

def s1_expectations():
    tables = [tuple(tuple(t[2 * o:2 * o + 2]) for o in range(2)) for t in product((0, 1, 2), repeat=4)]
    tables += [tuple(tuple(t[2 * o:2 * o + 2]) for o in range(3)) for t in product((0, 1), repeat=6)]
    n = by_her_lights_worse = in_fact_worse = bound_broken = 0
    tightest, worst_outside, witness = None, Fr(0), None
    for law in LAWS:
        for R in subsets(KERNELS):
            for u in tables:
                n += 1
                a0 = best(u, law)
                act = {m: (best(u, posterior(law, R, m)) if posterior(law, R, m) else a0) for m in (0, 1)}
                gain = {k: sum(law[w] * (u[act[k[w]]][w] - u[a0][w]) for w in W2) for k in KERNELS}
                if sum(gain[k] for k in R) < 0:          # her own expectation, the source uniform over R
                    by_her_lights_worse += 1
                D = max(max(r) for r in u) - min(min(r) for r in u)
                alpha = Fr(1, len(R))
                for k in KERNELS:
                    if k in R:
                        if gain[k] < 0:
                            in_fact_worse += 1
                            witness = witness or {"law": law, "allowed": R, "true source": k, "utility": u,
                                                  "gain in fact": gain[k]}
                        if gain[k] < -D * (1 - alpha) / alpha:
                            bound_broken += 1
                        if alpha < 1 and D > 0:
                            ratio = -gain[k] / (D * (1 - alpha) / alpha)
                            tightest = ratio if tightest is None else max(tightest, ratio)
                    elif D > 0:
                        worst_outside = max(worst_outside, -gain[k] / D)
    ok = by_her_lights_worse == 0 and bound_broken == 0 and in_fact_worse > 0
    return {"supports": "proved" if ok else "open", "instances": n,
            "worse by her own lights": by_her_lights_worse,
            "worse in fact with the true source in range": in_fact_worse, "first such instance": witness,
            "instances breaking the bound -D(1-alpha)/alpha": bound_broken,
            "largest loss as a share of the bound": tightest,
            "largest loss out of range, as a share of D": worst_outside}


def s1_values():
    case = C.x_value_drift()
    v = verdict(case)
    after = C.VALUES_BEFORE
    for content in source(case, NULL)(case.worlds[0]):
        after = C.takes_up_the_last(after, content)
    choice0 = max(C.VALUES_BEFORE, key=C.VALUES_BEFORE.get)
    choiceT = max(after, key=after.get)
    refuted = v["legitimate"] and C.VALUES_BEFORE[choiceT] < C.VALUES_BEFORE[choice0]
    # one-step value rules: two options, two equiprobable messages, values in {0, 1, 2}
    grid = list(product((0, 1, 2), repeat=2))
    n = mart = mart_fail_start = mart_fail_expected = non_fail_expected = 0
    for v0, va, vb in product(grid, repeat=3):
        n += 1
        ends = (va, vb)
        pick = [max((0, 1), key=lambda o: (e[o], -o)) for e in ends]
        by_start = sum(Fr(1, 2) * v0[p] for p in pick) >= max(v0)
        by_expected_end = sum(Fr(1, 2) * e[p] for e, p in zip(ends, pick)) >= max(v0)
        if all(2 * v0[o] == va[o] + vb[o] for o in (0, 1)):
            mart += 1
            mart_fail_start += not by_start
            mart_fail_expected += not by_expected_end
        else:
            non_fail_expected += not by_expected_end
    ok = refuted and mart_fail_expected == 0 and mart_fail_start > 0 and non_fail_expected > 0
    return {"supports": "refuted" if ok else "open", "counterexample": case.id, "its verdict": show(v),
            "values before": C.VALUES_BEFORE, "values after": after, "choice before": choice0, "choice after": choiceT,
            "value rules enumerated": n, "martingale rules": mart,
            "martingale rules where deferring is worse by her starting values": mart_fail_start,
            "martingale rules where deferring is worse by her expected later values": mart_fail_expected,
            "other rules where deferring is worse by her expected later values": non_fail_expected}


# -- 2. trust is not manufactured ----------------------------------------------

def evaluation(case, u, w, event=lambda w: w[1]):
    """Her credence in `event` at the end of the stretch: her mechanism on the inputs,
    unless a write to "b" set it."""
    steps = case.steps(u, w)
    allowed, bel = in_force(case, u, len(steps) - 1)
    post = (bel or bayes)(case, allowed, flat(steps), True) or case.law
    e = sum(p for x, p in post.items() if event(x))
    for step in steps:
        for ev in step:
            if ev[0] == "wr" and ev[1] == "b":
                e = ev[2]
    return e


def uniform_in_range(case):
    """One hypothesis of hers is the source at every aim: the class-level form."""
    s0 = source(case, NULL)
    return all(same_source(case, source(case, u), s0) for u in case.aims) and \
        all(clauses(case, u)["in range"] for u in case.aims)


def s2():
    law = LAWS[0]
    n = weak = weak_varies = uniform = uniform_varies = uniform_unsound_varies = 0
    for s0, s1 in product(KERNELS, repeat=2):
        for R in subsets(KERNELS):
            n += 1
            if s0 not in R or s1 not in R:
                continue
            weak += 1
            varies = any(posterior(law, R, s0[w]) != posterior(law, R, s1[w]) for w in W2)
            weak_varies += varies
            if s0 == s1:
                uniform += 1
                uniform_varies += varies
                for e in product((0, 1), repeat=2):      # any evaluation of the message, sound or not
                    uniform_unsound_varies += any(e[s0[w]] != e[s1[w]] for w in W2)
    x3 = C.X3()
    both = (1, 1)
    eA, eB = evaluation(x3, "A", both), evaluation(x3, "B", both)
    legit_at = {u: not any(not clauses(x3, u)[k] for k in ("sound", "in range", "maintained")) for u in ("A", "B")}
    mean = {u: sum(x3.law[w] * evaluation(x3, u, w) for w in x3.worlds) for u in ("A", "B")}
    written = C.shop("x_write_by_aim", "", lambda u, w: C.steps(*C.truthful(w)) + (() if u is NULL else ((wr("b", Fr(1)),),)))
    write_varies = evaluation(written, "B", (0, 0)) != evaluation(written, NULL, (0, 0))
    ok = weak_varies > 0 and uniform_varies == 0 and uniform_unsound_varies == 0 and eA != eB and all(legit_at.values())
    return {"supports": "refuted" if ok else "open", "adviser maps x allowed sets": n,
            "legitimate at both aims (in range as alpha > 0)": weak, "of those, her evaluation varies with the aim": weak_varies,
            "uniformly in range": uniform, "of those, her evaluation varies": uniform_varies,
            "of those, with any evaluation rule in place of Bayes, varies": uniform_unsound_varies,
            "X3 at the world (A sound, B sound): her credence in B under aim A, under aim B": (eA, eB),
            "X3 legitimate at aim A, at aim B": (legit_at["A"], legit_at["B"]),
            "X3 her mean credence in B under aim A, under aim B (its truth: 1/2)": (mean["A"], mean["B"]),
            "uniformly in range with a write by the aim: evaluation varies": write_varies}


# -- 3. what the gate needs ----------------------------------------------------

def first_looks_better(case, allowed, prefix, ended=False):
    """An unsound belief-former: a quarter of the credence that the first-reported item is
    unsound moves to its being sound."""
    post = bayes(case, allowed, prefix, ended)
    if post is None or not prefix:
        return post
    i = "AB".index(prefix[0][1])
    out = {w: Fr(0) for w in case.worlds}
    for w, p in post.items():
        if w[i] == 0:
            up = (1, w[1]) if i == 0 else (w[0], 1)
            out[w] += p * Fr(3, 4)
            out[up] += p * Fr(1, 4)
        else:
            out[w] += p
    return out


def moves():
    """The AI's ways of presenting its work B, each a stretch at aim "B".  The benchmark
    is `honest`: truthful reports to a principal who pictures truthful reports."""
    deaf = {"truthful": (Fr(1, 10), C.truthful),
            "always reports B unsound": (Fr(9, 10), lambda w: (C.rep("A", w[0]), C.rep("B", 0)))}
    def rewritten(u, w):
        return C.steps(*C.truthful(w)) if u is NULL else ((wr("R", deaf),),) + C.steps(*C.truthful(w))
    def written(u, w):
        return C.steps(*C.truthful(w)) + (() if u is NULL else ((wr("b", Fr(1)),),))
    third = Fr(1, 3)
    sides = {"truthful": (third, C.truthful), "for A": (third, C.advocate("A")), "for B": (third, C.advocate("B"))}
    x1 = C.X1()
    return {
        "honest": C.shop("honest", "", C.const(C.truthful)),
        "lie": C.shop("lie", "", C.by_aim(C.liar, C.truthful)),
        "write her credence": C.shop("write her credence", "", written),
        "rewrite her allowed set": C.shop("rewrite her allowed set", "", rewritten),
        "take a side she has not been told of": C.shop("take a side", "", C.by_aim(C.advocate("B"), C.truthful), sides),
        "choose the order, her mechanism unsound": C.shop("choose the order", "", C.by_aim(C.b_first, C.truthful),
                                                          C.BOTH_ORDERS, bel=first_looks_better),
        "choose the order, her mechanism sound": C.shop("choose the order (sound)", "", C.by_aim(C.b_first, C.truthful),
                                                        C.BOTH_ORDERS),
        "persuade by a signal she knows": x1,
    }


READINGS = ("alpha > 0", "alpha = 1", "uniform")
KINDS = ("credence", "verdict")


def legit_under(case, u, reading, drop=None):
    c = clauses(case, u)
    in_range = {"alpha > 0": c["in range"], "alpha = 1": c["alpha"] == 1}.get(reading)
    if reading == "uniform":
        in_range = uniform_in_range(case)
    held = {"sound": c["sound"], "maintained": c["maintained"], "in range": in_range}
    return all(v for k, v in held.items() if k != drop)


def her_evaluation(case, u, w, kind):
    """Her credence that B is sound, or her verdict on it: accept iff that credence is at least 1/2."""
    e = evaluation(case, u, w)
    return e if kind == "credence" else Fr(int(e >= Fr(1, 2)))


def gate_score(case, u, reading, drop, window, kind="credence"):
    if legit_under(case, u, reading, drop):
        return sum(case.law[w] * her_evaluation(case, u, w, kind) for w in case.worlds)
    return window


def s3():
    table, windows, ms = {}, (Fr(-1), Fr(-1, 2), Fr(-1, 100)), moves()
    for reading in READINGS:
        for kind in KINDS:
            for drop in (None, "sound", "in range", "maintained"):
                gains = {}
                for name, case in ms.items():
                    g = max(gate_score(case, "B", reading, drop, win, kind)
                            - gate_score(ms["honest"], "B", reading, drop, win, kind) for win in windows)
                    if g > 0:
                        gains[name] = g
                table["%s; %s%s" % (reading, kind, "" if drop is None else "; without " + drop)] = gains
    needed = {r: {c: any(set(table["%s; %s; without %s" % (r, k, c)]) - set(table["%s; %s" % (r, k)]) for k in KINDS)
                  for c in ("sound", "in range", "maintained")} for r in READINGS}
    refuted = bool(table["alpha > 0; credence"])
    ok = (refuted and not table["alpha = 1; credence"] and bool(table["alpha = 1; verdict"])
          and not table["uniform; credence"] and not table["uniform; verdict"]
          and needed["uniform"]["in range"] and needed["uniform"]["maintained"])
    return {"supports": "refuted" if ok else "open", "moves that gain over honest, by reading of legitimate": table,
            "clause needed (some move gains only without it)": needed}


# -- 4. shortfall --------------------------------------------------------------

def s4():
    n = broken = 0
    tight = None
    pool_cases = [c for c in C.all_cases() if not c.variants and c.worlds == C.SHOP] + list(moves().values())
    for case in pool_cases:
        u = case.actual
        defect = Fr(0)
        for w in case.worlds:
            a, r = case.steps(u, w), case.steps(NULL, w)
            allowed, bel = in_force(case, u, len(a) - 1)
            off_job = bel is not None and bel(case, allowed, flat(a), True) != bayes(case, allowed, flat(a), True)
            if a != r or off_job:
                defect += case.law[w]
        diff = abs(sum(case.law[w] * (evaluation(case, u, w) - evaluation(case, NULL, w)) for w in case.worlds))
        n += 1
        broken += diff > defect
        if defect > 0:
            tight = diff / defect if tight is None else max(tight, diff / defect)
    # a defect measured as the size of a change to her rule: her verdict is "accept iff credence >= theta"
    credence, theta = Fr(1, 2), Fr(1, 2)
    losses = {str(eta): int(credence >= theta) - int(credence >= theta + eta) for eta in (Fr(1, 10), Fr(1, 1000), Fr(1, 10 ** 9))}
    ok = broken == 0 and all(v == 1 for v in losses.values())
    return {"supports": "proved" if ok else "open", "stretches checked": n, "bound broken": broken,
            "largest |difference in mean evaluation| / defect mass": tight,
            "loss in her verdict when her threshold is written up by eta": losses}


# -- 5. the adviser's side -----------------------------------------------------

def s5():
    def principal(k, coarse=None):
        return lambda sigma: Case("p", "", W2, (NULL,), NULL, lambda u, w: C.steps(("m", sigma[w])),
                                  C.only(lambda w: (("m", k[w]),)), coarse=coarse)
    legit = {s: [k for k in KERNELS if verdict(principal(k)(s))["legitimate"]] for s in KERNELS}
    one_for_all = [s for s in KERNELS if len(legit[s]) == len(KERNELS)]
    one_for_two = [s for s in KERNELS if len(legit[s]) >= 2]
    indexed = all(verdict(principal(k)(k))["legitimate"] for k in KERNELS)
    # a principal who can represent only constant sources, and takes a declared source into her
    # allowed set when she can represent it
    consts = [k for k in KERNELS if k[0] == k[1]]
    def responsive(seed, declared, sigma):
        k = declared if declared in consts else seed
        return verdict(principal(k, coarse=lambda w: 0)(sigma))["legitimate"]
    declare_and_realize = {s: responsive(consts[0], s, s) for s in KERNELS}
    ok = not one_for_all and not one_for_two and indexed and \
        all(declare_and_realize[s] == (s in consts) for s in KERNELS)
    return {"supports": "proved" if ok else "open",
            "behaviours legitimate for every principal": one_for_all,
            "behaviours legitimate for two principals with different allowed sets": one_for_two,
            "realizing the source she pictures is legitimate for every principal": indexed,
            "declare-and-realize, a principal who represents constant sources only": declare_and_realize}


# -- 6. the disclosure limit ---------------------------------------------------

def s6():
    def run(reacts):
        case, value = C.x_frame_reader(reacts)
        law_of_inputs = {}
        mean = {}
        for u in case.aims:
            dist = {}
            for w in case.worlds:
                m = source(case, u)(w)
                dist[m] = dist.get(m, Fr(0)) + case.law[w]
            law_of_inputs[u] = dist
            mean[u] = sum(case.law[w] * value(w, source(case, u)(w)[0][1]) for w in case.worlds)
        c = clauses(case, "X")
        return {"in range at X": c["in range"], "source representable at X": c["source representable"],
                "law of her inputs the same at every aim": len({tuple(sorted(d.items())) for d in law_of_inputs.values()}) == 1,
                "her mean value at each aim": mean}
    reacts, ignores = run(True), run(False)
    # inside Rep and disclosed: every deterministic source on four worlds, her allowed set that source
    worlds = tuple(product((0, 1), repeat=2))
    n = biased = 0
    for table in product((0, 1), repeat=4):
        sigma = dict(zip(worlds, table))
        case = Case("d", "", worlds, (NULL,), NULL, lambda u, w, s=sigma: C.steps(("m", s[w])),
                    C.only(lambda w, s=sigma: (("m", s[w]),)))
        for i in (0, 1):
            n += 1
            bias = sum(case.law[w] * (evaluation(case, NULL, w, event=lambda x: x[i]) - w[i]) for w in worlds)
            biased += bias != 0
    x3 = C.X3()
    bias_x3 = sum(x3.law[w] * (evaluation(x3, "B", w) - w[1]) for w in x3.worlds)
    steered = len(set(reacts["her mean value at each aim"].values())) > 1
    ok = (not reacts["in range at X"] and not reacts["source representable at X"] and steered
          and reacts["law of her inputs the same at every aim"] and biased == 0
          and len(set(ignores["her mean value at each aim"].values())) == 1)
    return {"supports": "holds on the stated domain" if ok else "open",
            "outside Rep, her value-former reacts to her frame": reacts,
            "outside Rep, her value-former ignores her frame": ignores,
            "inside Rep and disclosed: (source, event) pairs": n, "of those with a biased mean credence": biased,
            "X3 (alpha = 1/2): bias of her mean credence in B": bias_x3}


# -- 7. well-definedness -------------------------------------------------------

def flat_bank():
    out = []
    for c in C.all_cases():
        out += list(c.variants.values()) if c.variants else [c]
    return out


def s7():
    bank = flat_bank()
    base = {c.id: verdict(c) for c in bank}
    legit = sorted(i for i, v in base.items() if v["legitimate"])
    def compare(redescribe):
        moved = {"legitimacy": [], "clauses": [], "manipulation": []}
        for c in bank:
            v, b = verdict(redescribe(c)), base[c.id]
            if v["legitimate"] != b["legitimate"]:
                moved["legitimacy"].append(c.id)
            if v["failing"] != b["failing"]:
                moved["clauses"].append("%s: %s -> %s" % (c.id, ", ".join(b["failing"]) or "none", ", ".join(v["failing"]) or "none"))
            if v["manipulation"] != b["manipulation"]:
                moved["manipulation"].append(c.id)
        return moved
    a1 = compare(writes_as_inputs)
    a2 = compare(lambda c: widened(c, rederive=False))
    c3 = compare(lambda c: widened(c, rederive=True))
    in_range_failures = sorted(i for i, v in base.items() if "in range" in v["failing"])
    flipped = [i for i in c3["legitimacy"] if i in in_range_failures]
    ok = (not a1["legitimacy"] and a1["clauses"] and (a2["legitimacy"] or a2["manipulation"]) and flipped
          and legit and len(legit) < len(bank))
    return {"supports": "refuted" if ok else "open", "stretches": len(bank), "legitimate": len(legit),
            "not legitimate": len(bank) - len(legit),
            "writes read as inputs": a1, "allowed set widened, her mechanism kept": a2,
            "allowed set widened, her mechanism Bayes of it": c3,
            "in-range failures": in_range_failures, "of those, legitimate once she allows for every aim": flipped,
            "of those, still failing": sorted(set(in_range_failures) - set(flipped))}


# -- 8. what Legit then is -----------------------------------------------------

def s8():
    delta, lam, window = Fr(1), Fr(3), Fr(-1, 2)
    acts = dict(moves())
    omega = tuple(product((0, 1), (0, 1), (0, 1, 2)))            # one state space for every action
    at = lambda case, o: o if len(case.worlds) == len(omega) else o[:2]
    hist = {}
    for name, case in acts.items():
        ok = legit_under(case, "B", "uniform")
        for o in omega:
            hist[(name, o)] = {"Legit": ok, "N": 0, "V": evaluation(case, "B", at(case, o)) if ok else window}
    for o in omega:                                   # the AI settles a reserved matter itself
        hist[("bypass", o)] = {"Legit": False, "N": 1, "V": window}
    S = lambda h: h["V"] - lam * h["N"]
    bounds = all((0 <= h["V"] <= 1) if h["Legit"] else (-delta <= h["V"] < 0) for h in hist.values())
    t1 = all((S(h) <= 1 - lam if h["N"] >= 1 else True) and
             (-delta <= S(h) < 0 if h["N"] == 0 and not h["Legit"] else True) and
             (0 <= S(h) <= 1 if h["N"] == 0 and h["Legit"] else True) for h in hist.values()) and 1 - lam < -delta
    mu = Fr(1, len(omega))
    U = lambda a: sum(mu * S(hist[(a, o)]) for o in omega)
    v = lambda a: sum(mu * int(hist[(a, o)]["N"] >= 1) for o in omega)
    kappa = lambda a, s: sum(mu * (S(hist[(a, o)]) - S(hist[(s, o)])) * int(hist[(a, o)]["N"] == 0) for o in omega)
    names = list(acts) + ["bypass"]
    t2b = all(U("honest") - U(a) >= (lam - (1 + delta)) * v(a) - kappa(a, "honest") for a in names)
    best_act = max(names, key=U)
    ok = bounds and t1 and t2b and U(best_act) == U("honest")
    return {"supports": "holds on the stated domain" if ok else "open", "histories": len(hist),
            "V within the bounds Scoring asks": bounds, "Theorem 1's three ranges": t1, "Theorem 2(b)": t2b,
            "U by action": {a: U(a) for a in names}, "an action maximizing U": best_act}


CHECKS = {"1E": s1_expectations, "1V": s1_values, "2": s2, "3": s3, "4": s4, "5": s5, "6": s6, "7": s7, "8": s8}
