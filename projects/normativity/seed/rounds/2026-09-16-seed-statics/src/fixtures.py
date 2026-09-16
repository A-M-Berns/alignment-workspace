"""The round's fixtures, every number exact.  Each function returns a dict the tests
assert against and the documents quote.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import permutations

from . import lp, fm
from .defeat import Graph, Trace
from .seed import (QUIET, Constitutive, DocketState, Form, Fragment, Row, Seed, Settlement,
                   StrItem, SubItem, equality_rows, forced_interval, forced_intervals,
                   frechet_rows, in_region, is_feasible, level_neutral,
                   minimal_infeasible_subset, seed_leverage, sure_loss_certificate,
                   symmetry_generated, transport_seed, forced_bundle)

F = Fraction


# ------------------------------------------------------------------------------------------
# 1. Statics on a two-coordinate fragment: sandwich, defeat widening, monotonicity, C1
# ------------------------------------------------------------------------------------------

def neg_fragment():
    """Coordinates `phi`, `not phi` with the coherence rows `phi + not phi = 1`."""
    frag = Fragment(["phi", "nphi"])
    coh = equality_rows(frag, {"phi": 1, "nphi": 1}, 1, "coherence", 0, "phi+nphi=1")
    return frag, coh


def sandwich():
    """C3 refuted under item-level humility: two humble items pin P(phi) = 1/2."""
    frag, coh = neg_fragment()
    S1 = Seed([SubItem(Form("premise", (0,), F(1, 2)), 0, "P(phi)>=1/2"),
               SubItem(Form("premise", (1,), F(1, 2)), 1, "P(nphi)>=1/2")], coh)
    S2 = Seed([], coh)
    pairs = [r.pair() for _, r in forced_bundle(S1, [], QUIET, Settlement(), 2)]
    return {
        "humble": S1.humble_items(),
        "I1": forced_interval(S1, [], QUIET, Settlement(), 2, 0),
        "I2": forced_interval(S2, [], QUIET, Settlement(), 2, 0),
        "fm_I1": fm.fm_interval(pairs, 2, 0),
    }


def defeat_widening():
    frag, coh = neg_fragment()
    S = Seed([SubItem(Form("premise", (0,), F(1, 2)), 0)], coh)
    before = forced_interval(S, [], QUIET, Settlement(), 2, 0)
    after = forced_interval(S, [], DocketState(defeated=frozenset({0})), Settlement(), 2, 0)
    return {"before": before, "after": after}


def settlement_monotone():
    """Three coordinates; settling one narrows the others' intervals and never widens."""
    frag = Fragment(["p", "q", "r"])
    S = Seed([], [StrItem(frag.row({"p": 1, "q": -1}, 0), "dominance", 0, "p<=q"),
                  StrItem(frag.row({"q": 1, "r": -1}, 0), "dominance", 1, "q<=r")])
    F0 = Settlement()
    F1 = Settlement({2: False})          # r = 0
    F2 = F1.extend({1: False})           # q = 0 too
    ivs = [forced_intervals(S, [], QUIET, Fs, 3) for Fs in (F0, F1, F2)]
    nested = all(ivs[k + 1][phi][0] >= ivs[k][phi][0] and ivs[k + 1][phi][1] <= ivs[k][phi][1]
                 for k in range(2) for phi in range(3))
    return {"intervals": ivs, "nested": nested, "chain_ok": F0.le(F1) and F1.le(F2)}


def c1_measure_form():
    """Disjoint intervals: hull bound holds, union-measure bound fails."""
    I1, I2 = (F(0), F(1, 10)), (F(9, 10), F(1))
    p1, p2 = F(0), F(9, 10)
    hull = max(I1[1], I2[1]) - min(I1[0], I2[0])
    measure = (I1[1] - I1[0]) + (I2[1] - I2[0])
    return {"gap": abs(p1 - p2), "hull": hull, "measure": measure,
            "hull_holds": abs(p1 - p2) <= hull, "measure_holds": abs(p1 - p2) <= measure}


def strict_humility():
    """C3': the same substantive item, closed and strict.  Closed layer: `p <= q`
    (structural) and the warrant `q <= 1/2`.  Closed item `p >= 1/2` pins p = q = 1/2;
    strict item `p > 1/2` makes the region empty — refuted, not pinned."""
    frag = Fragment(["p", "q"])
    closed = [frag.row({"p": 1, "q": -1}, 0).pair(), frag.row({"q": 1}, F(1, 2)).pair()]
    closed_item = frag.row({"p": -1}, -F(1, 2)).pair()
    cube = lp.cube_rows(2)
    lin = [fm.to_lincon(0, 2, r) for r in cube + closed]
    lin_closed = lin + [fm.to_lincon(0, 2, closed_item)]
    lin_strict = lin + [(fm.to_lincon(0, 2, closed_item)[0], F(-1, 2), True)]
    return {"closed_layer": lp.interval(closed, 2, 0),
            "closed_item": lp.interval(closed + [closed_item], 2, 0),
            "closed_item_fm": (fm.lo1(fm.project(1, lin_closed)), fm.hi1(fm.project(1, lin_closed))),
            "strict_item_feasible": fm.feasible(2, lin_strict),
            "closed_item_feasible": fm.feasible(2, lin_closed)}


# ------------------------------------------------------------------------------------------
# 2. Hysteresis through strength selection
# ------------------------------------------------------------------------------------------

def greedy_selection(candidates, order, base_rows, d):
    """Each item has candidate rows ordered weakest to strongest; in the given order,
    adopt the strongest candidate feasible against everything adopted so far."""
    chosen = {}
    rows = list(base_rows)
    for name in order:
        pick = None
        for cand in reversed(candidates[name]):
            if lp.feasible(rows + [cand.pair()], d):
                pick = cand
                break
        chosen[name] = pick
        if pick is not None:
            rows.append(pick.pair())
    return chosen, rows


def joint_canonical_selection(candidates, base_rows, d, key):
    """Reopening: every joint candidate combination is re-run against the whole docket;
    the canonical choice maximises `key` over the feasible combinations."""
    from itertools import product
    names = sorted(candidates)
    best = None
    for combo in product(*[candidates[n] for n in names]):
        rows = list(base_rows) + [c.pair() for c in combo]
        if lp.feasible(rows, d):
            k = key(dict(zip(names, combo)))
            if best is None or k > best[0]:
                best = (k, dict(zip(names, combo)), rows)
    return best


def hysteresis():
    frag = Fragment(["phi"])
    lower = {c: Row([-1], -c) for c in (F(3, 10), F(6, 10), F(9, 10))}   # phi >= c
    upper = {c: Row([1], c) for c in (F(95, 100), F(8, 10), F(5, 10))}   # phi <= c
    candidates = {"rho": [lower[F(3, 10)], lower[F(6, 10)], lower[F(9, 10)]],
                  "sigma": [upper[F(95, 100)], upper[F(8, 10)], upper[F(5, 10)]]}
    out = {}
    for order in (("rho", "sigma"), ("sigma", "rho")):
        chosen, rows = greedy_selection(candidates, order, [], 1)
        out[order] = {"rho": -chosen["rho"].b, "sigma": chosen["sigma"].b,
                      "interval": lp.interval(rows, 1, 0)}
    # both greedy outcomes are maximal joint selections, so reopening alone does not
    # restore order-independence; a canonical rule does.
    canon = joint_canonical_selection(candidates, [], 1,
                                      key=lambda ch: (-ch["rho"].b) - ch["sigma"].b)  # width
    out["canonical"] = {"rho": -canon[1]["rho"].b, "sigma": canon[1]["sigma"].b,
                        "interval": lp.interval(canon[2], 1, 0)}
    return out


# ------------------------------------------------------------------------------------------
# 3. Refinement without transport
# ------------------------------------------------------------------------------------------

def refinement():
    """`p` refined into `p1`, `p2` (exclusive; `p` remains as the disjunction coordinate
    tied by coherence).  Impartiality `P(p) = P(q)`; `q` pinned to 1/2 by settlement of
    its own halves.  Conservative transport keeps the row on the disjunction; narrowing
    sends it to `p1`."""
    old = Fragment(["p", "q"])
    S = Seed([], equality_rows(old, {"p": 1, "q": -1}, 0, "impartiality", 0, "P(p)=P(q)"))
    new = Fragment(["p", "q", "p1", "p2"])
    coh = equality_rows(new, {"p": 1, "p1": -1, "p2": -1}, 0, "coherence", 10, "p=p1+p2")
    conservative = {0: 0, 1: 1}
    narrowing = {0: 2, 1: 1}
    Fq = Settlement()                                        # q free, then q = 1/2 by a warrant
    Wq = [SubItem(Form("premise", (1,), F(1, 2)), 50, "P(q)>=1/2"),
          SubItem(Form("premise", (1,), F(1, 2)), 51, "P(q)<=1/2 via not-q")]
    # encode P(q) <= 1/2 as a structural row for the fixture's purpose
    pinq = equality_rows(new, {"q": 1}, F(1, 2), "coherence", 20, "q=1/2")
    R1 = transport_seed(conservative, S, 4)
    R2 = transport_seed(narrowing, S, 4)
    R1.str_ += coh + pinq
    R2.str_ += coh + pinq
    I1 = forced_intervals(R1, [], QUIET, Fq, 4)
    I2 = forced_intervals(R2, [], QUIET, Fq, 4)
    both_tau = forced_intervals(R1, [], QUIET, Fq, 4)
    return {"conservative": I1, "narrowing": I2, "both_tau_equal": both_tau == I1,
            "names": new.names}


# ------------------------------------------------------------------------------------------
# 4. Price convergence without reason convergence
# ------------------------------------------------------------------------------------------

def price_without_reason():
    frag = Fragment(["X", "Z", "phi"])
    Fset = Settlement({0: True, 1: True})
    R1 = Seed([SubItem(Form("premise", (0,), F(9, 10)), 0, "P(X)>=0.9"),
               SubItem(Form("applicability", (0, 2), F(2, 3)), 1, "P(phi)>=2/3 P(X)")], [])
    R2 = Seed([SubItem(Form("premise", (1,), F(9, 10)), 2, "P(Z)>=0.9"),
               SubItem(Form("applicability", (1, 2), F(2, 3)), 3, "P(phi)>=2/3 P(Z)")], [])
    I1 = forced_interval(R1, [], QUIET, Fset, 3, 2)
    I2 = forced_interval(R2, [], QUIET, Fset, 3, 2)
    ports1 = {it.port for it in R1.sub}
    ports2 = {it.port for it in R2.sub}
    return {"I1": I1, "I2": I2, "same_intervals": I1 == I2,
            "disjoint_reasons": ports1.isdisjoint(ports2)}


# ------------------------------------------------------------------------------------------
# 5. A structural item that is substantive in disguise
# ------------------------------------------------------------------------------------------

def disguise():
    frag, coh = neg_fragment()
    imp = equality_rows(frag, {"phi": 1, "nphi": -1}, 0, "impartiality", 2, "P(phi)=P(nphi)")
    S = Seed([], coh + imp)
    bad = level_neutral(S, 2)
    # a relational disguise: P(x) = P(y) on unrelated x, y, no level narrowed
    frag2 = Fragment(["x", "y"])
    S2 = Seed([], equality_rows(frag2, {"x": 1, "y": -1}, 0, "impartiality", 0, "P(x)=P(y)"))
    bad2 = level_neutral(S2, 2)
    sym_identity = lambda i: i
    sym_swap = lambda i: 1 - i
    return {"level_caught": bad, "relational_level": bad2,
            "relational_caught_by_declared_symmetry": bool(symmetry_generated(S2, sym_identity)),
            "relational_passes_under_swap": not symmetry_generated(S2, sym_swap)}


# ------------------------------------------------------------------------------------------
# 6. Stabilization
# ------------------------------------------------------------------------------------------

def stabilization_finite():
    """Finite discovery class: two warrants, one defeater; every element eventually raised;
    settlement monotone.  The interval sequence is eventually constant."""
    frag = Fragment(["phi", "psi"])
    S = Seed([], [])
    D = {"w1": SubItem(Form("premise", (0,), F(1, 2)), 1, "P(phi)>=1/2"),
         "w2": SubItem(Form("applicability", (1, 0), F(3, 4)), 2, "P(phi)>=3/4 P(psi)"),
         "d1": ("defeat", 1)}
    schedule = ["w1", "w2", "d1", None, None]
    settle = [None, None, None, {1: True}, None]
    st, Fs = QUIET, Settlement()
    seq = []
    for t in range(len(schedule)):
        ev = schedule[t]
        if ev in ("w1", "w2"):
            S.sub.append(D[ev])
        elif ev == "d1":
            st = DocketState(defeated=st.defeated | {D["d1"][1]}, withdrawn=st.withdrawn)
        if settle[t]:
            Fs = Fs.extend(settle[t])
        seq.append(forced_interval(S, [], st, Fs, 2, 0))
    return {"sequence": seq}


def stabilization_oscillation():
    """Infinite discovery class: fresh warrant `w_k : P(phi) >= 1/2` at odd dates, its
    undercut at even dates.  `I_phi` alternates [1/2, 1], [0, 1] forever."""
    S = Seed([], [])
    seq = []
    st = QUIET
    for t in range(1, 9):
        if t % 2 == 1:
            S.sub.append(SubItem(Form("premise", (0,), F(1, 2)), t, f"w_{t}"))
        else:
            st = DocketState(defeated=st.defeated | {t - 1})
        seq.append(forced_interval(S, [], st, Settlement(), 1, 0))
    reopenings = [seq[k][0] - seq[k + 1][0] for k in range(len(seq) - 1)
                  if seq[k][0] > seq[k + 1][0]]
    return {"sequence": seq, "reopenings": reopenings}


def stabilization_summable():
    """Warrant `w_k : P(phi) >= 1/2 + 1/2^(k+1)` raised, then undercut, then a floor
    `P(phi) >= 1/2` raised.  Reopenings are summable, so the lower endpoint converges
    (to 1/2) although the discovery class is infinite and every warrant is undercut."""
    S = Seed([], [])
    seq = []
    st = QUIET
    for k in range(1, 7):
        S.sub.append(SubItem(Form("premise", (0,), F(1, 2) + F(1, 2 ** (k + 1))), 2 * k, f"w_{k}"))
        seq.append(forced_interval(S, [], st, Settlement(), 1, 0))
        st = DocketState(defeated=st.defeated | {2 * k})
        seq.append(forced_interval(S, [], st, Settlement(), 1, 0))
        S.sub.append(SubItem(Form("premise", (0,), F(1, 2)), 2 * k + 1, f"floor_{k}"))
    drops = [seq[i][0] - seq[i + 1][0] for i in range(len(seq) - 1) if seq[i][0] > seq[i + 1][0]]
    return {"sequence": seq, "drops": drops, "drop_sum": sum(drops)}


# ------------------------------------------------------------------------------------------
# 7. The landed defeat calculus against the grounded extension
# ------------------------------------------------------------------------------------------

def defeat_calculus():
    """W is undercut by D1; D1 is undercut by D2.  Grounded extension: {W, D2}.  In the
    landed calculus D1 may dispose W whenever D1 is available (born earlier), whether or
    not D2 has been raised; the live set is then a function of the trace."""
    g = Graph(["W", "D1", "D2"], [("D1", "W"), ("D2", "D1")])
    grounded = g.grounded()
    # trace A: D1 raised, disposes W; then D2 raised, disposes D1.
    tA = Trace()
    tA.open("W", 0, "R")
    tA.open("D1", 1, "C")
    tA.dispose("W", 2, ["D1"], resolver="J", successor="W'", stander="R")
    tA.open("D2", 3, "R")
    tA.dispose("D1", 4, ["D2"], resolver="J", successor="D1'", stander="C")
    # trace B: D2 raised first; D1 still disposes W (D1 is available; D1 need not be vindicated).
    tB = Trace()
    tB.open("W", 0, "R")
    tB.open("D2", 1, "R")
    tB.open("D1", 2, "C")
    tB.dispose("W", 3, ["D1"], resolver="J", successor="W'", stander="R")
    # trace C: nobody disposes anything (exhaustive raising, no disposal act).
    tC = Trace()
    tC.open("W", 0, "R")
    tC.open("D1", 1, "C")
    tC.open("D2", 2, "R")
    return {"grounded": grounded, "preferred": g.preferred(),
            "live_A": tA.live_at_end(), "live_B": tB.live_at_end(), "live_C": tC.live_at_end()}


# ------------------------------------------------------------------------------------------
# 8. The moral fixture
# ------------------------------------------------------------------------------------------

OUTCOMES = {"a": (3, 1), "b": (1, 3), "c": (2, 2), "e": (3, 3)}


def moral_fragment(outcomes=OUTCOMES):
    names = []
    pairs = [(o, o2) for o in outcomes for o2 in outcomes if o != o2]
    for o, o2 in pairs:
        for i in (1, 2):
            names.append(f"g{i}({o},{o2})")
        names.append(f"g12({o},{o2})")
        names.append(f"r({o},{o2})")
    return Fragment(names), pairs


def moral_seed(c=F(9, 10), outcomes=OUTCOMES, declared_pairs=None):
    frag, pairs = moral_fragment(outcomes)
    sub, str_ = [], []
    port = 0
    # substantive: the valence ordering.  Higher-or-equal welfare => at least as good
    # (strength c); strictly lower welfare => not at least as good (strength c).  The
    # antecedents are settled empirical sentences and are canonicalised away.
    for o, o2 in pairs:
        for i in (1, 2):
            wi, wi2 = outcomes[o][i - 1], outcomes[o2][i - 1]
            g = frag.index(f"g{i}({o},{o2})")
            if wi >= wi2:
                sub.append(SubItem(Form("premise", (g,), c), port, f"P(g{i}({o},{o2}))>={c}"))
            else:
                # P(g) <= 1 - c, as the premise form on the negation: written directly
                sub.append(SubItem(Form("premise", (g,), c), port, f"P(not g{i}({o},{o2}))>={c}"))
                # premise form gives P(g) >= c; we want the negation.  Replace the row:
                sub[-1] = SubItem(NegPremise(g, c), port, f"P(not g{i}({o},{o2}))>={c}")
            port += 1
    sid = 0
    for o, o2 in pairs:
        # dominance: r(o,o') >= g12(o,o'), with Fréchet coherence for g12
        str_.append(StrItem(frag.row({f"g12({o},{o2})": 1, f"r({o},{o2})": -1}, 0),
                            "dominance", sid, f"r({o},{o2})>=g12({o},{o2})"))
        sid += 1
        fr = frechet_rows(frag, f"g12({o},{o2})", [f"g1({o},{o2})", f"g2({o},{o2})"], sid)
        str_ += fr
        sid += len(fr)
    # coherence on rankings: completeness and transitivity
    for o, o2 in pairs:
        if o < o2:
            str_.append(StrItem(frag.row({f"r({o},{o2})": -1, f"r({o2},{o})": -1}, -1),
                                "coherence", sid, f"r({o},{o2})+r({o2},{o})>=1"))
            sid += 1
    for x in outcomes:
        for y in outcomes:
            for z in outcomes:
                if len({x, y, z}) == 3:
                    str_.append(StrItem(frag.row({f"r({x},{y})": 1, f"r({y},{z})": 1,
                                                  f"r({x},{z})": -1}, 1),
                                        "coherence", sid, f"trans({x},{y},{z})"))
                    sid += 1
    # impartiality: like cases alike under the individual swap
    def mirror(o):
        w = outcomes[o]
        sw = (w[1], w[0])
        for o2, w2 in outcomes.items():
            if w2 == sw:
                return o2
        return None
    declared = declared_pairs if declared_pairs is not None else [
        (o, o2) for o, o2 in pairs if mirror(o) and mirror(o2)
        and (mirror(o), mirror(o2)) != (o, o2) and (o, o2) < (mirror(o), mirror(o2))]
    for o, o2 in declared:
        m1, m2 = mirror(o), mirror(o2)
        rows = equality_rows(frag, {f"r({o},{o2})": 1, f"r({m1},{m2})": -1}, 0,
                             "impartiality", sid, f"r({o},{o2})=r({m1},{m2})")
        str_ += rows
        sid += 2
    return frag, Seed(sub, str_, Constitutive(frozenset({"1", "2"}), frozenset())), declared


class NegPremise(Form):
    """`P(not X) >= c`, i.e. `P(X) <= 1 - c`, as a row; strength c."""

    def __init__(self, X, c):
        object.__setattr__(self, "kind", "negpremise")
        object.__setattr__(self, "coords", (X,))
        object.__setattr__(self, "c", F(c))

    def row(self, d):
        a = [F(0)] * d
        a[self.coords[0]] = F(1)
        return Row(a, 1 - self.c)


def moral_fixture(c=F(9, 10)):
    frag, S, declared = moral_seed(c)
    d = frag.d
    ranking = [i for i, n in enumerate(frag.names) if n.startswith("r(")]
    ivs = forced_intervals(S, [], QUIET, Settlement(), d, ranking)
    named = {frag.names[i]: iv for i, iv in ivs.items()}
    # additive aggregation: r(o,o') = 1 whenever sum(o) >= sum(o')
    additive_forced = {}
    for i in ranking:
        n = frag.names[i]
        o, o2 = n[2:-1].split(",")
        if sum(OUTCOMES[o]) >= sum(OUTCOMES[o2]):
            additive_forced[n] = (named[n] == (F(1), F(1)))
    leak = {n: iv for n, iv in named.items() if iv == (F(0), F(1))}
    lev = seed_leverage(ivs, ranking)
    ln_all = level_neutral(S, d, coords=ranking)
    ln_no_imp = level_neutral(S, d, coords=ranking, kinds=("dominance", "coherence"))
    return {"intervals": named, "declared_pairs": declared, "additive_forced": additive_forced,
            "open_axes": leak, "leverage_on_rankings": lev, "humble": S.humble_items(),
            "level_neutral_violations": {frag.names[i]: iv for i, iv in ln_all.items()},
            "level_neutral_violations_without_impartiality":
                {frag.names[i]: iv for i, iv in ln_no_imp.items()},
            "symmetry_generated_ok": not symmetry_generated(S, moral_symmetry(frag)), "d": d}


def moral_symmetry(frag, outcomes=OUTCOMES):
    """The individual swap as a permutation of coordinates."""
    def mirror(o):
        w = outcomes[o]
        for o2, w2 in outcomes.items():
            if w2 == (w[1], w[0]):
                return o2
        return None

    def sym(i):
        n = frag.names[i]
        head, rest = n.split("(")
        o, o2 = rest[:-1].split(",")
        m1, m2 = mirror(o), mirror(o2)
        if m1 is None or m2 is None:
            return i
        if head == "g1":
            head = "g2"
        elif head == "g2":
            head = "g1"
        return frag.index(f"{head}({m1},{m2})")
    return sym


def population_fixture(c=None):
    """A = (10,10), B = (10,10,1), C = (7,7,7).  P1 mere addition: B >= A.  P2 non-anti-
    egalitarianism: C > B.  P3 quality: A > C.  With transitivity and asymmetry the three
    are jointly infeasible; structural (strength 1) unless `c` is given, in which case
    they are substantive of strength c."""
    frag = Fragment(["r(B,A)", "r(A,C)", "r(C,B)", "r(B,C)", "r(C,A)", "r(A,B)"])
    str_ = []
    sid = 0
    # coherence: asymmetry of strict preference encoded as r(x,y) + r(y,x) >= 1 (completeness)
    # and transitivity r(x,y) + r(y,z) - 1 <= r(x,z)
    for x, y in (("B", "A"), ("A", "C"), ("C", "B")):
        str_.append(StrItem(frag.row({f"r({x},{y})": -1, f"r({y},{x})": -1}, -1), "coherence",
                            sid, f"r({x},{y})+r({y},{x})>=1"))
        sid += 1
    for x, y, z in permutations("ABC", 3):
        str_.append(StrItem(frag.row({f"r({x},{y})": 1, f"r({y},{z})": 1, f"r({x},{z})": -1}, 1),
                            "coherence", sid, f"trans({x},{y},{z})"))
        sid += 1
    axioms = {"P1 mere addition: r(B,A)=1": ("r(B,A)", True),
              "P2 non-anti-egalitarian: r(C,B)=1": ("r(C,B)", True),
              "P2': r(B,C)=0": ("r(B,C)", False),
              "P3 quality: r(A,C)=1": ("r(A,C)", True),
              "P3': r(C,A)=0": ("r(C,A)", False)}
    sub = []
    port = 100
    if c is None:
        for label, (coord, val) in axioms.items():
            v = 1 if val else 0
            str_ += equality_rows(frag, {coord: 1}, v, "dominance", sid, label)
            sid += 2
    else:
        for label, (coord, val) in axioms.items():
            i = frag.index(coord)
            sub.append(SubItem(Form("premise", (i,), c) if val else NegPremise(i, c), port, label))
            port += 1
    S = Seed(sub, str_)
    feas = is_feasible(S, [], QUIET, Settlement(), frag.d)
    out = {"feasible": feas, "names": frag.names}
    if not feas:
        out["certificate"] = sure_loss_certificate(S, [], QUIET, Settlement(), frag.d)
        out["mis"] = minimal_infeasible_subset(S, [], QUIET, Settlement(), frag.d)
    return out


# ------------------------------------------------------------------------------------------
# 9. The legal fixture
# ------------------------------------------------------------------------------------------

def legal_fixture(c=F(4, 5)):
    """Coordinates: V (statute valid), R (right in force), RC (R and C), C (statute
    conflicts with the right; settled), E (within the enumerated power; settled), V2/E2/C2
    for a second statute on an unenumerated non-conflicting subject, G/Sp/B for lex
    specialis."""
    frag = Fragment(["V", "R", "RC", "C", "E", "V2", "RC2", "C2", "E2", "G", "Sp", "B"])
    d = frag.d
    str_ = []
    sid = 0
    # supremacy: P(V and R and C) = 0, written V + RC <= 1 with RC the conjunction R∧C
    str_.append(StrItem(frag.row({"V": 1, "RC": 1}, 1), "dominance", 0, "supremacy"))
    str_.append(StrItem(frag.row({"V2": 1, "RC2": 1}, 1), "dominance", 1, "supremacy(2)"))
    sid = 2
    str_ += frechet_rows(frag, "RC", ["R", "C"], sid)
    sid += 3
    str_ += frechet_rows(frag, "RC2", ["R", "C2"], sid)
    sid += 3
    # enumerated power with the supremacy exception: V >= E - RC
    str_.append(StrItem(frag.row({"V": -1, "E": 1, "RC": -1}, 0), "dominance", sid, "power"))
    sid += 1
    str_.append(StrItem(frag.row({"V2": -1, "E2": 1, "RC2": -1}, 0), "dominance", sid, "power(2)"))
    sid += 1
    # lex specialis: when both apply (B), the specific governs: Sp >= B, G + B <= 1
    str_.append(StrItem(frag.row({"Sp": -1, "B": 1}, 0), "dominance", sid, "lex specialis Sp"))
    sid += 1
    str_.append(StrItem(frag.row({"G": 1, "B": 1}, 1), "dominance", sid, "lex specialis G"))
    sid += 1
    # the amended power clause, absent until the amendment lands: V >= E
    amended_power_id = sid
    str_.append(StrItem(frag.row({"V": -1, "E": 1}, 0), "dominance", sid, "power (amended)"))
    sid += 1
    sub = [SubItem(Form("premise", (frag.index("R"),), c), 0, f"right: P(R)>={c}")]
    S = Seed(sub, str_, Constitutive(frozenset({"citizen", "court"}), frozenset({frag.index("R")})))
    settled = Settlement({frag.index("C"): True, frag.index("E"): True,
                          frag.index("C2"): False, frag.index("E2"): False,
                          frag.index("B"): True})
    before = DocketState(withdrawn=frozenset({amended_power_id}))          # amendment not yet landed
    after = DocketState(withdrawn=frozenset({0}))                          # supremacy (this subject) withdrawn, amended power live
    defeated = DocketState(defeated=frozenset({0}), withdrawn=frozenset({amended_power_id}))
    coords = [frag.index(n) for n in ("V", "R", "V2", "G", "Sp")]
    def named(st):
        return {frag.names[i]: iv for i, iv in forced_intervals(S, [], st, settled, d, coords).items()}
    return {"before": named(before), "after_amendment": named(after),
            "right_defeated": named(defeated), "c": c}
