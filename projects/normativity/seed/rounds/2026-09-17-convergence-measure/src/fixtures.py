"""Fixtures for the convergence measure.  Every number exact.  The seed round's model and
fixtures are loaded by path and not modified."""

from __future__ import annotations

from fractions import Fraction

from .profile import (Reasoner, S, lp, fm, seedfix, blocked_hull, discord_certificate, transport_seed_keeping_forms,
                      discord_graph, hull, intervals, merged_certificate, merged_feasible,
                      naive_hull, profile, uniform)

F = Fraction
QUIET = S.QUIET


def prem(coord, c, port, label=""):
    return S.SubItem(S.Form("premise", (coord,), F(c)), port, label)


def negprem(coord, c, port, label=""):
    return S.SubItem(seedfix.NegPremise(coord, F(c)), port, label)


def two(frag, sub1, sub2, str_=None, W1=None, W2=None, st1=QUIET, st2=QUIET):
    str_ = str_ or []
    R1 = Reasoner("R1", S.Seed(list(sub1), list(str_)), list(W1 or []), st1)
    R2 = Reasoner("R2", S.Seed(list(sub2), list(str_)), list(W2 or []), st2)
    return R1, R2


def run(reasoners, Fset, d, Phi, w=None):
    I, refuted = intervals(reasoners, Fset, d, Phi)
    return {"I": I, "refuted": refuted, **(profile(I, Phi, w) if I else {})}


# --- 1. inequalities and the touching refutation ---------------------------------------------

def touching():
    frag = S.Fragment(["phi"])
    R1, R2 = two(frag, [negprem(0, F(1, 2), 0, "P(phi)<=1/2")], [prem(0, F(1, 2), 1, "P(phi)>=1/2")])
    return run([R1, R2], S.Settlement(), 1, [0])


# --- 2. gameability ------------------------------------------------------------------------------

def dilution():
    """Adding pinned coordinates to Φ under uniform weights drives the naive average
    down; the blocked average is unchanged."""
    frag = S.Fragment(["phi", "p1", "p2", "p3"])
    R1, R2 = two(frag, [prem(0, F(1, 5), 0)], [negprem(0, F(1, 5), 1)])
    Fs = S.Settlement({1: True, 2: False, 3: True})       # p1, p2, p3 pinned by the world
    I, _ = intervals([R1, R2], Fs, 4, [0, 1, 2, 3])
    return {"naive_small": naive_hull(I, [0]), "naive_diluted": naive_hull(I, [0, 1, 2, 3]),
            "blocked_small": blocked_hull(I, [0]), "blocked_diluted": blocked_hull(I, [0, 1, 2, 3]),
            "hulls": {phi: hull(I, phi) for phi in range(4)}}


def splitting():
    """`p` refined into `p1, p2` (exclusive, `p = p1 + p2`).  Over the declared fragment
    `{p}` the hull is unchanged by the refinement; over the refined fragment with the
    inherited half-weights it is not."""
    old = S.Fragment(["p"])
    R1, R2 = two(old, [prem(0, F(3, 5), 0)], [negprem(0, F(3, 5), 1)])   # [3/5,1] vs [0,2/5]
    before = run([R1, R2], S.Settlement(), 1, [0])
    new = S.Fragment(["p", "p1", "p2"])
    coh = S.equality_rows(new, {"p": 1, "p1": -1, "p2": -1}, 0, "coherence", 10, "p=p1+p2")
    rho = {0: 0}
    T1 = Reasoner("R1", transport_seed_keeping_forms(rho, R1.seed, 3), [], QUIET)
    T2 = Reasoner("R2", transport_seed_keeping_forms(rho, R2.seed, 3), [], QUIET)
    T1.seed.str_ += coh
    T2.seed.str_ += coh
    declared = run([T1, T2], S.Settlement(), 3, [0])
    refined = run([T1, T2], S.Settlement(), 3, [1, 2], {1: F(1, 2), 2: F(1, 2)})
    return {"before": before["hull"], "declared_after": declared["hull"],
            "refined_after": refined["hull"], "refined_hulls": refined["hulls"],
            "declared_discord": declared["discord"], "refined_discord": refined["discord"]}


def hiding():
    """A reasoner holding only wide intervals is never in discord; the trade-off between
    hull and discord."""
    frag = S.Fragment(["phi"])
    wide, _ = two(frag, [], [])
    narrow1, narrow2 = two(frag, [prem(0, F(4, 5), 0)], [negprem(0, F(4, 5), 1)])
    return {"wide_vs_narrow": run([wide, narrow2], S.Settlement(), 1, [0]),
            "narrow_vs_narrow": run([narrow1, narrow2], S.Settlement(), 1, [0])}


def weight_capture():
    """With reasoner-chosen weights discord mass can be made arbitrarily small; with
    positive declared weights it is positive whenever some coordinate is in discord."""
    frag = S.Fragment(["phi", "psi"])
    R1, R2 = two(frag, [prem(0, F(4, 5), 0)], [negprem(0, F(4, 5), 1)])
    I, _ = intervals([R1, R2], S.Settlement(), 2, [0, 1])
    out = {}
    for eps in (F(1, 2), F(1, 10), F(1, 1000)):
        out[eps] = profile(I, [0, 1], {0: eps, 1: 1 - eps})["discord"]
    out["uniform"] = profile(I, [0, 1])["discord"]
    return out


# --- 3. dynamics ----------------------------------------------------------------------------------

def private_learning():
    """R1 = [0, 2/5] by an item; R2 = [3/10, 1] by an item.  R2 privately learns
    `P(phi) >= 3/5`: discord.  Sharing that warrant with R1 refutes R1 rather than
    dissolving the discord; only a defeater on the new warrant dissolves it."""
    frag = S.Fragment(["phi"])
    w = prem(0, F(3, 5), 7, "w: P(phi)>=3/5")
    R1, R2 = two(frag, [negprem(0, F(3, 5), 0, "P(phi)<=2/5")], [prem(0, F(3, 10), 1, "P(phi)>=3/10")])
    step0 = run([R1, R2], S.Settlement(), 1, [0])
    R2p = Reasoner("R2", R2.seed, [w], QUIET)
    step1 = run([R1, R2p], S.Settlement(), 1, [0])
    cert = discord_certificate(R1, R2p, S.Settlement(), 1, 0)
    R1s = Reasoner("R1", R1.seed, [w], QUIET)                 # shared
    step2 = run([R1s, R2p], S.Settlement(), 1, [0])
    R2d = Reasoner("R2", R2.seed, [], QUIET)                  # w defeated on R2's docket
    step3 = run([R1, R2d], S.Settlement(), 1, [0])
    return {"before": step0, "private": step1, "certificate": cert, "shared": step2,
            "defeated": step3}


def oscillation_two():
    """The seed round's oscillation witness on R1 while R2 holds `P(phi) >= 3/10`: R1
    alternates `[1/2, 1]` and `[0, 1]`, so the hull width alternates `7/10` and `1`."""
    frag = S.Fragment(["phi"])
    R2 = Reasoner("R2", S.Seed([prem(0, F(3, 10), 99)], []), [], QUIET)
    seq = []
    sub = []
    st = QUIET
    for t in range(1, 9):
        if t % 2 == 1:
            sub = sub + [prem(0, F(1, 2), t, f"w_{t}")]
        else:
            st = S.DocketState(defeated=st.defeated | {t - 1})
        R1 = Reasoner("R1", S.Seed(list(sub), []), [], st)
        seq.append(run([R1, R2], S.Settlement(), 1, [0])["hull"])
    return {"hull_sequence": seq}


def persistent_discord():
    """S1 = {P(phi) >= 4/5}, S2 = {P(phi) <= 2/5}; settlement on an unrelated `psi`
    along a chain.  Discord on `phi` at every step with the same certificate support."""
    frag = S.Fragment(["phi", "psi"])
    R1, R2 = two(frag, [prem(0, F(4, 5), 0, "P(phi)>=4/5")], [negprem(0, F(3, 5), 1, "P(phi)<=2/5")])
    chain = [S.Settlement(), S.Settlement({1: True})]
    steps = []
    for Fs in chain:
        p = run([R1, R2], Fs, 2, [0, 1])
        c = discord_certificate(R1, R2, Fs, 2, 0)
        steps.append({"profile": (p["hull"], p["overlap"], p["discord"]), "delta": p["delta"],
                      "support": (c["support_lower"], c["support_upper"]),
                      "mis": c["minimal_infeasible_subset"], "gap": c["gap"]})
    return {"steps": steps}


def lock():
    """R1 carries a locked strength selection (its candidate fixed at 9/10); R2 selects
    the strongest feasible candidate against a shared presumption.  Along the chain
    (`E` settled) the hull is eventually constant; the lock sits as width, and as discord
    only against an opposing substantive item."""
    frag = S.Fragment(["V", "R", "E"])
    str_ = [S.StrItem(frag.row({"V": 1, "R": 1}, 1), "dominance", 0, "supremacy V+R<=1"),
            S.StrItem(frag.row({"V": -1, "R": -1, "E": 1}, 0), "dominance", 1, "power V>=E-R")]
    locked = prem(1, F(9, 10), 0, "locked right 9/10")
    cands = [F(6, 10), F(7, 10), F(8, 10)]
    shared = prem(0, F(1, 20), 50, "shared presumption P(V)>=1/20")
    chain = [S.Settlement(), S.Settlement({2: True})]
    out = []
    for Fs in chain:
        R1 = Reasoner("R1", S.Seed([locked], str_), [shared], QUIET)
        pick = None
        for c in reversed(cands):
            trial = Reasoner("R2", S.Seed([prem(1, c, 1, f"right {c}")], str_), [shared], QUIET)
            if trial.feasible(Fs, 3):
                pick = c
                break
        R2 = Reasoner("R2", S.Seed([prem(1, pick, 1, f"right {pick}")], str_), [shared], QUIET)
        p = run([R1, R2], Fs, 3, [0, 1])
        out.append({"R2_pick": pick, "profile": (p["hull"], p["overlap"], p["discord"]),
                    "hulls": p["hulls"], "I": p["I"], "refuted": p["refuted"]})
    R1 = Reasoner("R1", S.Seed([locked], str_), [], QUIET)
    R2 = Reasoner("R2", S.Seed([prem(1, F(6, 10), 1, "right 6/10"), prem(0, F(3, 10), 2, "presumption 3/10")], str_), [], QUIET)
    Fs = S.Settlement({2: True})
    p = run([R1, R2], Fs, 3, [0, 1])
    cert = discord_certificate(R1, R2, Fs, 3, 0)
    return {"chain": out, "opposed": {"profile": (p["hull"], p["overlap"], p["discord"]),
                                     "delta": p["delta"], "certificate": cert}}


def consensus():
    """Disjoint dockets, identical intervals; then a defeater on R1's docket alone."""
    frag = S.Fragment(["X", "Z", "phi"])
    Fs = S.Settlement({0: True, 1: True})
    R1 = Reasoner("R1", S.Seed([], []), [S.SubItem(S.Form("premise", (0,), F(9, 10)), 0, "P(X)>=0.9"),
                                          S.SubItem(S.Form("applicability", (0, 2), F(2, 3)), 1, "P(phi)>=2/3 P(X)")], QUIET)
    R2 = Reasoner("R2", S.Seed([], []), [S.SubItem(S.Form("premise", (1,), F(9, 10)), 2, "P(Z)>=0.9"),
                                          S.SubItem(S.Form("applicability", (1, 2), F(2, 3)), 3, "P(phi)>=2/3 P(Z)")], QUIET)
    agree = run([R1, R2], Fs, 3, [2])
    R1d = Reasoner("R1", S.Seed([], []), [it for it in R1.W if it.port != 1], QUIET)
    fragile = run([R1d, R2], Fs, 3, [2])
    return {"agree": agree, "after_one_sided_defeater": fragile,
            "disjoint_dockets": {it.port for it in R1.W}.isdisjoint({it.port for it in R2.W})}


# --- 4. many reasoners ----------------------------------------------------------------------------

def hidden_discord():
    """All items substantive.  Two reasoners with every common interval nonempty and an
    infeasible merge: R1 holds `y ≥ (9/10)·x` and `x ≥ (9/10)·y` (humble near-equality),
    R2 holds `x ≥ 4/5` and `y ≤ 3/10`.  Three reasoners pairwise compatible, jointly
    not, with no coordinate discord: `x ≥ 3/5`, `y ≥ 3/5`, `y ≤ 1 − (9/10)·x`."""
    frag = S.Fragment(["x", "y"])
    R1 = Reasoner("R1", S.Seed([S.SubItem(S.Form("applicability", (0, 1), F(9, 10)), 0, "y>=0.9x"),
                                 S.SubItem(S.Form("applicability", (1, 0), F(9, 10)), 1, "x>=0.9y")], []), [], QUIET)
    R2 = Reasoner("R2", S.Seed([prem(0, F(4, 5), 2, "x>=4/5"), negprem(1, F(7, 10), 3, "y<=3/10")], []), [], QUIET)
    p2 = run([R1, R2], S.Settlement(), 2, [0, 1])
    m2 = merged_feasible([R1, R2], S.Settlement(), 2)
    c2 = merged_certificate([R1, R2], S.Settlement(), 2)
    A = Reasoner("A", S.Seed([prem(0, F(3, 5), 0, "x>=3/5")], []), [], QUIET)
    B = Reasoner("B", S.Seed([prem(1, F(3, 5), 1, "y>=3/5")], []), [], QUIET)
    Cc = Reasoner("C", S.Seed([S.SubItem(NegApplic(0, 1, F(9, 10)), 5, "y<=1-0.9x")], []), [], QUIET)
    p3 = run([A, B, Cc], S.Settlement(), 2, [0, 1])
    pairs = {pair: merged_feasible([a, b], S.Settlement(), 2) for pair, (a, b) in
             {"AB": (A, B), "AC": (A, Cc), "BC": (B, Cc)}.items()}
    c3 = merged_certificate([A, B, Cc], S.Settlement(), 2)
    return {"two": {"profile": (p2["hull"], p2["overlap"], p2["discord"]), "commons": p2["commons"],
                    "merged_feasible": m2, "certificate": c2},
            "three": {"profile": (p3["hull"], p3["overlap"], p3["discord"]), "commons": p3["commons"],
                      "pairwise_feasible": pairs, "merged_feasible": merged_feasible([A, B, Cc], S.Settlement(), 2),
                      "certificate": c3, "graph": discord_graph(p3["I"], [0, 1])}}


# --- 5. the moral fixture -------------------------------------------------------------------------

OUT4 = {"a": (3, 1), "b": (1, 3), "c": (2, 2), "e": (3, 3)}


def moral_two(c=F(9, 10), cp=F(4, 5), cs=F(4, 5)):
    """Four outcomes; the seed round's valence/dominance/impartiality/coherence seed.
    The welfare-comparison antecedents are settled along a chain — nothing, individual 1,
    both — and a valence warrant is live exactly when its antecedent is settled true (the
    applicability row `P(g) ≥ c·P(ant)` is vacuous while `ant` is unsettled, since `ant`
    occurs in no other row, and specializes to `P(g) ≥ c` once settled true).  R1 adds a
    humble prioritarian item (`c ≻ a`), R2 a humble sum item (`a ~ c`), both on `(a, c)`."""
    pairs = [(o, o2) for o in OUT4 for o2 in OUT4 if o != o2]
    names = []
    for o, o2 in pairs:
        names += [f"g1({o},{o2})", f"g2({o},{o2})", f"g12({o},{o2})", f"r({o},{o2})"]
    frag = S.Fragment(names)
    d = frag.d

    def valence(settled_individuals):
        sub = []
        port = 0
        for o, o2 in pairs:
            for i in (1, 2):
                port += 1
                if i not in settled_individuals:
                    continue
                g = frag.index(f"g{i}({o},{o2})")
                if OUT4[o][i - 1] >= OUT4[o2][i - 1]:
                    sub.append(prem(g, c, port, f"g{i}({o},{o2})>={c}"))
                else:
                    sub.append(negprem(g, c, port, f"not g{i}({o},{o2})>={c}"))
        return sub

    str_ = []
    sid = 0
    for o, o2 in pairs:
        str_.append(S.StrItem(frag.row({f"g12({o},{o2})": 1, f"r({o},{o2})": -1}, 0), "dominance", sid, f"r>=g12({o},{o2})"))
        sid += 1
        fr = S.frechet_rows(frag, f"g12({o},{o2})", [f"g1({o},{o2})", f"g2({o},{o2})"], sid)
        str_ += fr
        sid += len(fr)
    for o, o2 in pairs:
        if o < o2:
            str_.append(S.StrItem(frag.row({f"r({o},{o2})": -1, f"r({o2},{o})": -1}, -1), "coherence", sid, f"complete({o},{o2})"))
            sid += 1
    for x in OUT4:
        for y in OUT4:
            for z in OUT4:
                if len({x, y, z}) == 3:
                    str_.append(S.StrItem(frag.row({f"r({x},{y})": 1, f"r({y},{z})": 1, f"r({x},{z})": -1}, 1), "coherence", sid, f"trans({x},{y},{z})"))
                    sid += 1
    mirror = {"a": "b", "b": "a", "c": "c", "e": "e"}
    seen = set()
    for o, o2 in pairs:
        m = (mirror[o], mirror[o2])
        if m != (o, o2) and (o, o2) not in seen and m not in seen:
            seen.add((o, o2))
            str_ += S.equality_rows(frag, {f"r({o},{o2})": 1, f"r({m[0]},{m[1]})": -1}, 0, "impartiality", sid, f"r({o},{o2})=r{m}")
            sid += 2
    rac, rca = frag.index("r(a,c)"), frag.index("r(c,a)")
    prior = [negprem(rac, cp, 100, "prioritarian: not r(a,c)"), prem(rca, cp, 101, "prioritarian: r(c,a)")]
    summ = [prem(rac, cs, 102, "sum: r(a,c)"), prem(rca, cs, 103, "sum: r(c,a)")]
    ranking = [frag.index(f"r({o},{o2})") for o, o2 in pairs]
    chain = [(), (1,), (1, 2)]
    steps = []
    reasoners = None
    for settled in chain:
        val = valence(settled)
        R1 = Reasoner("R1", S.Seed(val + prior, str_), [], QUIET)
        R2 = Reasoner("R2", S.Seed(val + summ, str_), [], QUIET)
        reasoners = (R1, R2)
        p = run([R1, R2], S.Settlement(), d, ranking)
        steps.append({"settled": settled, "profile": (p["hull"], p["overlap"], p["discord"]),
                      "delta": [frag.names[i] for i in p["delta"]],
                      "hulls": {frag.names[i]: v for i, v in p["hulls"].items()},
                      "refuted": p["refuted"]})
    R1, R2 = reasoners
    cert = discord_certificate(R1, R2, S.Settlement(), d, rac)
    val = valence((1, 2))
    E1 = Reasoner("R1", S.Seed(list(val), str_), [], QUIET)
    E2 = Reasoner("R2", S.Seed(list(val), str_), [], QUIET)
    ref = run([E1, E2], S.Settlement(), d, ranking)
    R1s = Reasoner("R1", R1.seed, [summ[0]], QUIET)
    shared = run([R1s, R2], S.Settlement(), d, ranking)
    wab = prem(frag.index("r(a,b)"), F(7, 10), 200, "shared: r(a,b)>=7/10")
    R1w = Reasoner("R1", R1.seed, [wab], QUIET)
    R2w = Reasoner("R2", R2.seed, [wab], QUIET)
    sharedw = run([R1w, R2w], S.Settlement(), d, ranking)
    return {"names": frag.names, "steps": steps, "certificate": cert,
            "reference_profile": (ref["hull"], ref["overlap"], ref["discord"]),
            "share_conflicting": {"refuted": shared["refuted"]},
            "share_neutral": {"profile": (sharedw["hull"], sharedw["overlap"], sharedw["discord"]),
                              "hull_rab": sharedw["hulls"][frag.index("r(a,b)")],
                              "delta": [frag.names[i] for i in sharedw["delta"]]},
            "d": d}


class NegApplic(S.Form):
    """`P(not Y) >= c P(X)`, i.e. `Y <= 1 - c X` : row  c X + Y <= 1."""

    def __init__(self, X, Y, c):
        object.__setattr__(self, "kind", "negapplic")
        object.__setattr__(self, "coords", (X, Y))
        object.__setattr__(self, "c", F(c))

    def row(self, d):
        a = [F(0)] * d
        a[self.coords[0]] += self.c
        a[self.coords[1]] += F(1)
        return S.Row(a, 1)


def population_private(c=F(4, 5)):
    """On the population fragment: R2 holds P3 (quality) humbly; R1 privately learns P1
    and P2.  Discord on `r(C,A)` created by R1's learning; sharing refutes R2."""
    frag = S.Fragment(["r(B,A)", "r(A,C)", "r(C,B)", "r(B,C)", "r(C,A)", "r(A,B)"])
    from itertools import permutations
    str_ = []
    sid = 0
    for x, y in (("B", "A"), ("A", "C"), ("C", "B")):
        str_.append(S.StrItem(frag.row({f"r({x},{y})": -1, f"r({y},{x})": -1}, -1), "coherence", sid, f"complete({x},{y})"))
        sid += 1
    for x, y, z in permutations("ABC", 3):
        str_.append(S.StrItem(frag.row({f"r({x},{y})": 1, f"r({y},{z})": 1, f"r({x},{z})": -1}, 1), "coherence", sid, f"trans({x},{y},{z})"))
        sid += 1
    P3 = [prem(frag.index("r(A,C)"), c, 10, "P3 quality r(A,C)"), negprem(frag.index("r(C,A)"), c, 11, "P3' not r(C,A)")]
    P12 = [prem(frag.index("r(B,A)"), c, 20, "P1 mere addition r(B,A)"),
           prem(frag.index("r(C,B)"), c, 21, "P2 non-anti-egalitarian r(C,B)"),
           negprem(frag.index("r(B,C)"), c, 22, "P2' not r(B,C)")]
    R1 = Reasoner("R1", S.Seed([], str_), [], QUIET)
    R2 = Reasoner("R2", S.Seed(P3, str_), [], QUIET)
    Phi = list(range(6))
    before = run([R1, R2], S.Settlement(), 6, Phi)
    R1p = Reasoner("R1", S.Seed([], str_), P12, QUIET)
    after = run([R1p, R2], S.Settlement(), 6, Phi)
    cert = discord_certificate(R1p, R2, S.Settlement(), 6, frag.index("r(C,A)"))
    R2s = Reasoner("R2", S.Seed(P3, str_), P12, QUIET)
    shared = run([R1p, R2s], S.Settlement(), 6, Phi)
    return {"names": frag.names, "before": (before["hull"], before["overlap"], before["discord"]),
            "after": (after["hull"], after["overlap"], after["discord"]),
            "delta_after": [frag.names[i] for i in after["delta"]], "certificate": cert,
            "shared_refuted": shared["refuted"]}


# --- 6. the legal fixture -------------------------------------------------------------------------

def legal_two():
    """Two courts, one constitution (the seed round's five clauses), `Φ = {V, V2}`: the
    validity of the conflicting statute and the scope of the enumerated power (the
    second statute's validity).  Court 1 has a locked selection of the right's strength;
    court 2 selects the strongest feasible candidate and holds a presumption of validity."""
    frag = S.Fragment(["V", "R", "RC", "C", "E", "V2", "RC2", "C2", "E2"])
    d = frag.d
    str_ = [S.StrItem(frag.row({"V": 1, "RC": 1}, 1), "dominance", 0, "supremacy"),
            S.StrItem(frag.row({"V2": 1, "RC2": 1}, 1), "dominance", 1, "supremacy(2)")]
    sid = 2
    str_ += S.frechet_rows(frag, "RC", ["R", "C"], sid); sid += 3
    str_ += S.frechet_rows(frag, "RC2", ["R", "C2"], sid); sid += 3
    str_.append(S.StrItem(frag.row({"V": -1, "E": 1, "RC": -1}, 0), "dominance", sid, "power")); sid += 1
    str_.append(S.StrItem(frag.row({"V2": -1, "E2": 1, "RC2": -1}, 0), "dominance", sid, "power(2)")); sid += 1
    R_, V_, V2_ = frag.index("R"), frag.index("V"), frag.index("V2")
    locked = prem(R_, F(9, 10), 0, "locked right 9/10")
    cands = [F(6, 10), F(7, 10), F(95, 100)]
    presumption = prem(V_, F(3, 10), 5, "presumption P(V)>=3/10")
    chain = [S.Settlement({frag.index("C2"): False, frag.index("E2"): False}),
             S.Settlement({frag.index("C2"): False, frag.index("E2"): False, frag.index("C"): True}),
             S.Settlement({frag.index("C2"): False, frag.index("E2"): False, frag.index("C"): True, frag.index("E"): True})]
    steps = []
    for Fs in chain:
        court1 = Reasoner("court1", S.Seed([locked], str_), [], QUIET)
        pick = None
        for c in reversed(cands):
            trial = Reasoner("court2", S.Seed([prem(R_, c, 1, f"right {c}"), presumption], str_), [], QUIET)
            if trial.feasible(Fs, d):
                pick = c
                break
        court2 = Reasoner("court2", S.Seed([prem(R_, pick, 1, f"right {pick}"), presumption], str_), [], QUIET)
        p = run([court1, court2], Fs, d, [V_, V2_])
        cert = discord_certificate(court1, court2, Fs, d, V_) if p["delta"] else None
        steps.append({"court2_pick": pick, "profile": (p["hull"], p["overlap"], p["discord"]),
                      "hulls": {frag.names[i]: v for i, v in p["hulls"].items()},
                      "I": {n: {frag.names[i]: v for i, v in iv.items()} for n, iv in p["I"].items()},
                      "delta": [frag.names[i] for i in p["delta"]], "certificate": cert,
                      "refuted": p["refuted"]})
    return {"steps": steps}
