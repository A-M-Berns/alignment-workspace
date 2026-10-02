"""
examples.py — the battery of concrete decision problems (v2 Definition 5 encodings)
used by the phase-1 notes, as named constructors.  Each constructor returns a
SimpleNamespace with the Problem (`B`), its points, action/observation events, the
payoff function `r`, and the parameters, so tests can name every object.

Conventions
  * Parameters default to sympy symbols with DECLARED open domains encoding v2's
    standing inequalities (0 < x < y; p in (1/2, 1]; L > S > 0 ...), see `P`.
    Pass exact numbers (int / Fraction) to instantiate.
  * Chance edges are 'evented' (EC) wherever the sources treat them so.
  * Every constructor's docstring cites the v2 / phase-1 location it encodes.

Constructors
  mugging(variant)        Prop 6's B_1 / B_2          k_fold_mugging(k, coupling)  verify E1/E2
  decoupled_mugging()     CF-15's decoupling           transparent_newcomb(v, ...) §7.2 / CF-16
  told_you_so()           §7.1 B_P (= prophet_tree)    smoking_lesion_S3(), smoking_lesion_tickle()  §7.3
  amd()                   Prop 5(c)                    self_prediction_miniature()  Remark 4.3
  routing_root()          Remark 3.4                   cx1(), cx2()                adversary-verify R6 / R3
  umbrella_mugging()      CF-11(b)                     look_decide()               CF-13
  parallel_fiber()        adversary-cf ADV-2           scrambled_pair(), beta_pair() CF-23 / CF-14(a)
  sequenced_pair()        FR-10 T_{d,e}, T_{e,d}, T_×  relocated_mugging_direct()  FR-2 (hand-built)
  ping_pong()             FR-3                         fantasy_state(), fr12_tie() fair-repair §3.2–3.3
  single_node_unrealized() adversary-repair A.1
"""
from __future__ import annotations

from fractions import Fraction as F
from types import SimpleNamespace as NS

import sympy as sp

import dp
from dp import (BOT, TOP, Branch, Chance, Decision, Dist, Eq, Leaf, Point, Problem, Procedure, State,
                World as W, chance, sym)

# ---------------------------------------------------------------------------
# default symbolic parameters (declared domains = v2's standing inequalities)
# ---------------------------------------------------------------------------
P = NS(
    x=sym("x", 0, 1), y=sym("y", 1, 2),                 # 0 < x < y            (Prop 6)
    q0=sym("q0", 0, 1),                                 # interior self-credence (Prop 6)
    q=sym("q", 0, 1),                                   # a mixing probability
    p=sym("p", F(1, 2), 1),                             # predictor reliability  (§7.2)
    L=sym("L", 1, 2), S=sym("S", 0, 1),                 # L > S > 0             (§7.2)
    alpha=sym("alpha", 0, 1), beta=sym("beta", 0, 1),   # α, β > 0             (§7.3)
    rho=sym("rho", 0, 1), gamma0=sym("gamma0", 0, F(1, 2)), gamma1=sym("gamma1", F(1, 2), 1),  # γ1 > γ0
)


def _p(v, default):
    return default if v is None else dp.num(v)


# ---------------------------------------------------------------------------
# Counterfactual Mugging (v2 Proposition 6)
# ---------------------------------------------------------------------------
def mugging(variant: int = 1, x=None, y=None, q0=None, name=None):
    """Proposition 6's B_1 (variant=1, Counterfactual Mugging) and B_2 (variant=2,
    heads-branch transfers swapped).  Algebra: coin∈{H,T}, choice∈{pay,refuse,⊥},
    transfer∈{0,1}; r = -x·1[pay] + y·1[transfer]; d = (s, O_T, {pay, refuse}) with
    P_s(T)=1, P_s(transfer=0)=1, P_s(pay)=q0, V_s the conditional payoff.  Chance
    edges evented with coin=H / coin=T."""
    x, y, q0 = _p(x, P.x), _p(y, P.y), _p(q0, P.q0)
    pay, refuse, O_T, O_H = Eq("choice", "pay"), Eq("choice", "refuse"), Eq("coin", "T"), Eq("coin", "H")

    def r(w):
        return (-x if w["choice"] == "pay" else 0) + (y if w["transfer"] == 1 else 0)

    Ps = Dist({W(coin="T", choice="pay", transfer=0): q0, W(coin="T", choice="refuse", transfer=0): 1 - q0})
    s = State.from_payoff(Ps, r, name="s_d")
    d = Point("d", s, O_T, [pay, refuse])

    def leaf(coin, choice, transfer):
        w = W(coin=coin, choice=choice, transfer=transfer)
        return Leaf(w, r(w))

    tp, tr = (1, 0) if variant == 1 else (0, 1)
    root = chance(("H", F(1, 2), Decision(d, {pay: leaf("H", BOT, tp), refuse: leaf("H", BOT, tr)})),
                  ("T", F(1, 2), Decision(d, {pay: leaf("T", "pay", 0), refuse: leaf("T", "refuse", 0)})),
                  events={"H": O_H, "T": O_T})
    B = Problem(root, name=name or f"B{variant}")
    return NS(B=B, d=d, pay=pay, refuse=refuse, O_T=O_T, O_H=O_H, r=r, x=x, y=y, q0=q0)


def decoupled_mugging(x=None, y=None, q0=None):
    """CF-15's decoupled mugging: Omega's coupling deleted, pay·H := (H,⊥,0) with r=0,
    so the H-node's two answers lead to the same leaf (a spurious query)."""
    m = mugging(1, x, y, q0, name="B1-decoupled")

    def leaf(coin, choice, transfer):
        w = W(coin=coin, choice=choice, transfer=transfer)
        return Leaf(w, m.r(w))

    root = chance(("H", F(1, 2), Decision(m.d, {m.pay: leaf("H", BOT, 0), m.refuse: leaf("H", BOT, 0)})),
                  ("T", F(1, 2), Decision(m.d, {m.pay: leaf("T", "pay", 0), m.refuse: leaf("T", "refuse", 0)})),
                  events={"H": m.O_H, "T": m.O_T})
    m.B = Problem(root, name="B1-decoupled")
    return m


def k_fold_mugging(k: int, coupling: str = "linear", x=None, y=None, q0=None):
    """verify-prior-notes E1/E2's k-fold mugging: fair coin; T: one real query of d
    (pay costs x); H: k nested simulation queries of the same point d, then transfer
    y with probability b_j, j = number of paying draws.  coupling: 'linear' b_j = j/k;
    'concave' b_j = 1[j >= 1]; 'convex' b_j = 1[j = k].  k = 1 (linear) is B_1."""
    m = mugging(1, x, y, q0, name=f"mugging_{k}fold_{coupling}")
    d, pay, refuse, r = m.d, m.pay, m.refuse, m.r

    def b(j):
        if coupling == "linear":
            return F(j, k)
        if coupling == "concave":
            return F(1 if j >= 1 else 0)
        if coupling == "convex":
            return F(1 if j == k else 0)
        raise ValueError(coupling)

    def leaf(coin, choice, transfer):
        w = W(coin=coin, choice=choice, transfer=transfer)
        return Leaf(w, r(w))

    def sim(i, j):
        if i == k:
            bj = b(j)
            if bj == 1:
                return leaf("H", BOT, 1)
            if bj == 0:
                return leaf("H", BOT, 0)
            return chance(("1", bj, leaf("H", BOT, 1)), ("0", 1 - bj, leaf("H", BOT, 0)),
                          events={"1": Eq("transfer", 1), "0": Eq("transfer", 0)})
        return Decision(d, {pay: sim(i + 1, j + 1), refuse: sim(i + 1, j)})

    root = chance(("H", F(1, 2), sim(0, 0)),
                  ("T", F(1, 2), Decision(d, {pay: leaf("T", "pay", 0), refuse: leaf("T", "refuse", 0)})),
                  events={"H": m.O_H, "T": m.O_T})
    m.B = Problem(root, name=f"mugging_{k}fold_{coupling}")
    m.k, m.coupling, m.b = k, coupling, b
    return m


def relocated_mugging_direct(x=None, y=None):
    """FR-2's relocated mugging, hand-built (to cross-check dp.relocate): root point
    d̂ with actions pol_d ∈ {pay, refuse}, O = ⊤; pay-branch: coin → (T,pay,0,pol=pay)
    r=-x / (H,⊥,1,pol=pay) r=y; refuse-branch: coin → payoffs 0, 0.  State None
    (to be calibrated)."""
    m = mugging(1, x, y)
    r = m.r
    A_pay, A_ref = Eq("pol_d", "pay"), Eq("pol_d", "refuse")
    dhat = Point("^d", None, TOP, [A_pay, A_ref])

    def leaf(coin, choice, transfer, pol):
        w = W(coin=coin, choice=choice, transfer=transfer, pol_d=pol)
        return Leaf(w, r(w))

    ev = {"H": m.O_H, "T": m.O_T}
    root = Decision(dhat, {
        A_pay: chance(("H", F(1, 2), leaf("H", BOT, 1, "pay")), ("T", F(1, 2), leaf("T", "pay", 0, "pay")), events=ev),
        A_ref: chance(("H", F(1, 2), leaf("H", BOT, 0, "refuse")), ("T", F(1, 2), leaf("T", "refuse", 0, "refuse")), events=ev),
    })
    return NS(B=Problem(root, name="Rel(B1)-direct"), dhat=dhat, A_pay=A_pay, A_ref=A_ref, r=r, x=m.x, y=m.y)


# ---------------------------------------------------------------------------
# Transparent Newcomb V1(p) / V2(p)  (v2 §7.2, Definition-5 encoding of CF-16)
# ---------------------------------------------------------------------------
def transparent_newcomb(variant: int = 1, p=None, L=None, S=None, mF=None, mE=None):
    """§7.2.  Algebra: fill∈{0,1}, act∈{both,large}; seen = F iff fill = 1;
    r = fill·L + S·1[act=both].  Points d_F (O_F = {fill=1}), d_E (O_E = {fill=0}),
    states certain of fill = 1 resp. 0 (their action credences are the free
    parameters mF, mE = P_s(act=large); V the conditional payoff).
    V1(p): query d_F hypothetically, answer x; chance node n_x sends the run to the
      full branch w.p. b1(x) = p if x = large else 1-p; the full branch queries d_F
      (real) and records the act at fill=1, the empty branch queries d_E at fill=0.
    V2(p): query d_F then d_E hypothetically, answers (x, y); one chance node n_xy
      per answer pair, b2 = p iff (x,y) = (large, large) else 1-p; real branches as V1.
    Policy helper: `policy(ns, x, y)` with 1 = large-only, 2 = both."""
    p, L, S = _p(p, P.p), _p(L, P.L), _p(S, P.S)
    mF = sym("mF", 0, 1) if mF is None else dp.num(mF)
    mE = sym("mE", 0, 1) if mE is None else dp.num(mE)
    large, both = Eq("act", "large"), Eq("act", "both")
    O_F, O_E = Eq("fill", 1), Eq("fill", 0)

    def r(w):
        return w["fill"] * L + (S if w["act"] == "both" else 0)

    sF = State.from_payoff(Dist({W(fill=1, act="large"): mF, W(fill=1, act="both"): 1 - mF}), r, name="s_F")
    sE = State.from_payoff(Dist({W(fill=0, act="large"): mE, W(fill=0, act="both"): 1 - mE}), r, name="s_E")
    dF, dE = Point("dF", sF, O_F, [large, both]), Point("dE", sE, O_E, [large, both])

    def real(fill):
        d = dF if fill == 1 else dE
        return Decision(d, {a: Leaf(W(fill=fill, act=a.name.split("=")[1]), r(W(fill=fill, act=a.name.split("=")[1])))
                            for a in (large, both)})

    ev = {"F": O_F, "E": O_E}
    if variant == 1:
        def after(x):
            b1 = p if x == "large" else 1 - p
            return chance(("F", b1, real(1)), ("E", 1 - b1, real(0)), events=ev)
        root = Decision(dF, {large: after("large"), both: after("both")})
    elif variant == 2:
        def after(x, y):
            b2 = p if (x, y) == ("large", "large") else 1 - p
            return chance(("F", b2, real(1)), ("E", 1 - b2, real(0)), events=ev)
        root = Decision(dF, {a: Decision(dE, {c: after(a.name.split("=")[1], c.name.split("=")[1]) for c in (large, both)})
                             for a in (large, both)})
    else:
        raise ValueError("variant must be 1 or 2")
    B = Problem(root, name=f"TN-V{variant}")
    ns = NS(B=B, dF=dF, dE=dE, large=large, both=both, O_F=O_F, O_E=O_E, r=r, p=p, L=L, S=S, mF=mF, mE=mE)

    def policy(x: int, y: int) -> Procedure:
        """(x, y) with 1 = large-only, 2 = both at d_F resp. d_E."""
        code = {1: "large", 2: "both"}
        return Procedure({dF: code[x], dE: code[y]}, name=f"({x},{y})")

    ns.policy = policy
    return ns


# ---------------------------------------------------------------------------
# Told-You-So Five-and-Ten (v2 §7.1); Lemma 2's prophet tree
# ---------------------------------------------------------------------------
def told_you_so():
    """§7.1's B_P.  Algebra n∈{5,10} (announced), m∈{5,10} (taken); r = m.  Points
    d_k = (s_k, {n=k}, {m=5, m=10}), P_{s_k} certain of (k,k), V its value k.
    Tree: root = query d_5: m=5 → (5,5); m=10 → query d_10: m=10 → (10,10); m=5 → (10,5).
    Procedures: C0 (zero-respecting: 5 at d_5, 10 at d_10), Cstar (10 at both),
    take5_both (5 at both — Lemma 2's separation witness)."""
    m5, m10 = Eq("m", 5), Eq("m", 10)
    O5, O10 = Eq("n", 5), Eq("n", 10)

    def r(w):
        return w["m"]

    s5 = State.certain(W(n=5, m=5), 5, name="s_5")
    s10 = State.certain(W(n=10, m=10), 10, name="s_10")
    d5, d10 = Point("d5", s5, O5, [m5, m10]), Point("d10", s10, O10, [m5, m10])

    def leaf(n, m):
        return Leaf(W(n=n, m=m), r(W(n=n, m=m)))

    root = Decision(d5, {m5: leaf(5, 5), m10: Decision(d10, {m10: leaf(10, 10), m5: leaf(10, 5)})})
    B = Problem(root, name="B_P")
    return NS(B=B, d5=d5, d10=d10, m5=m5, m10=m10, O5=O5, O10=O10, r=r,
              C0=Procedure({d5: m5, d10: m10}, name="C0"),
              Cstar=Procedure({d5: m10, d10: m10}, name="C*"),
              take5_both=Procedure({d5: m5, d10: m5}, name="take5both"))


prophet_tree = told_you_so


# ---------------------------------------------------------------------------
# Smoking Lesion (v2 §7.3)
# ---------------------------------------------------------------------------
def smoking_lesion_S3(rho=None, gamma0=None, gamma1=None, alpha=None, beta=None, sigma=None, kappa0=None, kappa1=None):
    """§7.3 instantiation of Σ_SL under (S3): chance ℓ ~ Bern(ρ); query d (O_d = ⊤,
    actions m=1, m=0 — ONE point on both ℓ-branches); chance k ~ Bern(γ_ℓ); leaf
    (ℓ, m, k); r = αm − βk.  The stipulated (S2) state: P_s(ℓ=1)=ρ independent of
    (m,k); P_s(m=1)=σ; P_s(k=1|m=1)=κ1 > κ0 = P_s(k=1|m=0)."""
    rho, gamma0, gamma1 = _p(rho, P.rho), _p(gamma0, P.gamma0), _p(gamma1, P.gamma1)
    alpha, beta = _p(alpha, P.alpha), _p(beta, P.beta)
    sigma = sym("sigma", 0, 1) if sigma is None else dp.num(sigma)
    kappa0 = sym("kappa0", 0, F(1, 2)) if kappa0 is None else dp.num(kappa0)
    kappa1 = sym("kappa1", F(1, 2), 1) if kappa1 is None else dp.num(kappa1)
    m1, m0 = Eq("m", 1), Eq("m", 0)

    def r(w):
        return alpha * w["m"] - beta * w["k"]

    Ps = {}
    for l in (0, 1):
        for m in (0, 1):
            for k in (0, 1):
                pl = rho if l == 1 else 1 - rho
                pm = sigma if m == 1 else 1 - sigma
                kap = kappa1 if m == 1 else kappa0
                pk = kap if k == 1 else 1 - kap
                Ps[W(l=l, m=m, k=k)] = pl * pm * pk
    s = State.from_payoff(Dist(Ps), r, name="s_S2")
    d = Point("d", s, TOP, [m1, m0])

    def after(l, m):
        g = gamma1 if l == 1 else gamma0
        return chance(("1", g, Leaf(W(l=l, m=m, k=1), r(W(l=l, m=m, k=1)))),
                      ("0", 1 - g, Leaf(W(l=l, m=m, k=0), r(W(l=l, m=m, k=0)))),
                      events={"1": Eq("k", 1), "0": Eq("k", 0)})

    root = chance(("1", rho, Decision(d, {m1: after(1, 1), m0: after(1, 0)})),
                  ("0", 1 - rho, Decision(d, {m1: after(0, 1), m0: after(0, 0)})),
                  events={"1": Eq("l", 1), "0": Eq("l", 0)})
    return NS(B=Problem(root, name="SL-S3"), d=d, m1=m1, m0=m0, r=r, rho=rho, gamma0=gamma0, gamma1=gamma1,
              alpha=alpha, beta=beta, sigma=sigma, kappa0=kappa0, kappa1=kappa1)


def smoking_lesion_tickle(rho=None, gamma0=None, gamma1=None, alpha=None, beta=None, states=None):
    """Proposition 12's tickle instantiation: lesion-informative observations
    O ∈ {{ℓ=1}, {ℓ=0}} with DISTINCT points d1, d0 (states None unless given — to be
    calibrated for a procedure with `dp.calibrated_state`)."""
    rho, gamma0, gamma1 = _p(rho, P.rho), _p(gamma0, P.gamma0), _p(gamma1, P.gamma1)
    alpha, beta = _p(alpha, P.alpha), _p(beta, P.beta)
    m1, m0 = Eq("m", 1), Eq("m", 0)

    def r(w):
        return alpha * w["m"] - beta * w["k"]

    states = states or {}
    d1 = Point("d1", states.get("d1"), Eq("l", 1), [m1, m0])
    d0 = Point("d0", states.get("d0"), Eq("l", 0), [m1, m0])

    def after(l, m):
        g = gamma1 if l == 1 else gamma0
        return chance(("1", g, Leaf(W(l=l, m=m, k=1), r(W(l=l, m=m, k=1)))),
                      ("0", 1 - g, Leaf(W(l=l, m=m, k=0), r(W(l=l, m=m, k=0)))),
                      events={"1": Eq("k", 1), "0": Eq("k", 0)})

    root = chance(("1", rho, Decision(d1, {m1: after(1, 1), m0: after(1, 0)})),
                  ("0", 1 - rho, Decision(d0, {m1: after(0, 1), m0: after(0, 0)})),
                  events={"1": Eq("l", 1), "0": Eq("l", 0)})
    return NS(B=Problem(root, name="SL-tickle"), d1=d1, d0=d0, m1=m1, m0=m0, r=r, rho=rho, gamma0=gamma0,
              gamma1=gamma1, alpha=alpha, beta=beta)


# ---------------------------------------------------------------------------
# Absent-minded driver (v2 Proposition 5(c)); CX1 (adversary-verify R6)
# ---------------------------------------------------------------------------
def amd(state=None, point_name="d"):
    """Proposition 5(c): one point d at two nested nodes; first node: a → payoff 0,
    b → second node; second: a → payoff 4, b → payoff 1.  Worlds record the exit
    (exit ∈ {1, 2, 0}; 0 = continued at both).  O_d = ⊤; state optional."""
    a, b = Eq("act", "a"), Eq("act", "b")
    d = Point(point_name, state, TOP, [a, b])
    root = Decision(d, {a: Leaf(W(exit=1), 0), b: Decision(d, {a: Leaf(W(exit=2), 4), b: Leaf(W(exit=0), 1)})})
    return NS(B=Problem(root, name="AMD"), d=d, a=a, b=b)


def cx1(c_rate=F(1, 3)):
    """adversary-verify R6's CX1: root point d (A = {a, b}, O = ⊤); a-edge → an AMD
    gadget on a DIFFERENT point d' (node1: c → 0, e → node2; node2: c → 4, e → 1);
    b-edge → leaf payoff 1.  C(d')(c) = c_rate (1/3 by default)."""
    a, b = Eq("act", "a"), Eq("act", "b")
    c, e = Eq("act2", "c"), Eq("act2", "e")
    d = Point("d", None, TOP, [a, b])
    dp_ = Point("d'", None, TOP, [c, e])
    gadget = Decision(dp_, {c: Leaf(W(act="a", exit=1), 0),
                            e: Decision(dp_, {c: Leaf(W(act="a", exit=2), 4), e: Leaf(W(act="a", exit=0), 1)})})
    root = Decision(d, {a: gadget, b: Leaf(W(act="b", exit=BOT), 1)})
    return NS(B=Problem(root, name="CX1"), d=d, dprime=dp_, a=a, b=b, c=c, e=e, c_rate=dp.num(c_rate))


# ---------------------------------------------------------------------------
# Remark 4.3's self-prediction miniature; Remark 3.4's routing root
# ---------------------------------------------------------------------------
def self_prediction_miniature(q=None):
    """Remark 4.3: one point d with actions {a, b}; a predictor draws an independent
    sample from C(d) (a hypothetical d-node), then the live d-node; the leaf pays 2 on
    (live a, sample b), 1 on (live b, sample a), else 0.  Worlds record (live, sample);
    the action events are {live = a}, {live = b}; O_d = ⊤.  The state supplied is the
    STRICTLY CALIBRATED one for C(d)(a) = q ('the state reports the true mixture')."""
    q = _p(q, P.q)
    a, b = Eq("live", "a"), Eq("live", "b")

    def r(w):
        return 2 if (w["live"], w["sample"]) == ("a", "b") else (1 if (w["live"], w["sample"]) == ("b", "a") else 0)

    Ps = {W(live=l, sample=s_): (q if l == "a" else 1 - q) * (q if s_ == "a" else 1 - q) for l in "ab" for s_ in "ab"}
    s = State.from_payoff(Dist(Ps), r, name="s_cal")
    d = Point("d", s, TOP, [a, b])

    def live(sample):
        return Decision(d, {a: Leaf(W(live="a", sample=sample), r(W(live="a", sample=sample))),
                            b: Leaf(W(live="b", sample=sample), r(W(live="b", sample=sample)))})

    root = Decision(d, {a: live("a"), b: live("b")})  # root = the predictor's sample
    return NS(B=Problem(root, name="self-prediction"), d=d, a=a, b=b, r=r, q=q)


def routing_root(state=None):
    """Remark 3.4's routing root: a root query d whose a-edge alone leads into O-worlds.
    Algebra o∈{0,1}, act∈{a,b}; O_d = {o=1}; a → (o=1, act=a) r=1; b → (o=0, act=b) r=0.
    With C(d) = (1/2, 1/2): ν(a | O) = 1 ≠ 1/2 (selection bias)."""
    a, b = Eq("act", "a"), Eq("act", "b")
    O = Eq("o", 1)
    d = Point("d", state, O, [a, b])
    root = Decision(d, {a: Leaf(W(o=1, act="a"), 1), b: Leaf(W(o=0, act="b"), 0)})
    return NS(B=Problem(root, name="routing-root"), d=d, a=a, b=b, O=O)


# ---------------------------------------------------------------------------
# CX2 (adversary-verify R3): observations are not redundant on fair trees
# ---------------------------------------------------------------------------
def cx2():
    """adversary-verify R3's CX2.  Worlds w1=(c=1,m=a), w2=(1,b), w3=(2,a), w4=(2,b);
    chance root 1/2 on c; branch 1 → q1 carrying d1=(s,O1,A), branch 2 → q2 carrying
    d2=(s,O2,A), A = {m=a, m=b}, the SAME state s: P_s = ½δ_w1 + ½δ_w4, V_s the
    conditional payoff (w1 ↦ 1, w4 ↦ 5).  Leaves: q1: a→(w1,1), b→(w2,0); q2: a→(w3,1),
    b→(w4,5).  O1 = {w1,w2,w4}, O2 = {w1,w3,w4}.  Also `B_merged`: O dropped (d1 = d2)."""
    w1, w2, w3, w4 = W(c=1, m="a"), W(c=1, m="b"), W(c=2, m="a"), W(c=2, m="b")
    a, b = Eq("m", "a"), Eq("m", "b")
    pay = {w1: 1, w2: 0, w3: 1, w4: 5}
    s = State.from_payoff(Dist({w1: F(1, 2), w4: F(1, 2)}), lambda w: pay[w], name="s")
    O1, O2 = dp.Worlds(w1, w2, w4), dp.Worlds(w1, w3, w4)
    O1.name, O2.name = "O1", "O2"
    d1, d2 = Point("d1", s, O1, [a, b]), Point("d2", s, O2, [a, b])
    ev = {"1": Eq("c", 1), "2": Eq("c", 2)}
    root = chance(("1", F(1, 2), Decision(d1, {a: Leaf(w1, 1), b: Leaf(w2, 0)})),
                  ("2", F(1, 2), Decision(d2, {a: Leaf(w3, 1), b: Leaf(w4, 5)})), events=ev)
    # the O-free merge: one point at both nodes
    dm = Point("d", s, TOP, [a, b])
    root_m = chance(("1", F(1, 2), Decision(dm, {a: Leaf(w1, 1), b: Leaf(w2, 0)})),
                    ("2", F(1, 2), Decision(dm, {a: Leaf(w3, 1), b: Leaf(w4, 5)})), events=ev)
    return NS(B=Problem(root, name="CX2"), B_merged=Problem(root_m, name="CX2-merged"), d1=d1, d2=d2, dm=dm,
              a=a, b=b, O1=O1, O2=O2, w1=w1, w2=w2, w3=w3, w4=w4, s=s,
              Cstar=Procedure({d1: a, d2: b}, name="C*"))


# ---------------------------------------------------------------------------
# CF examples: umbrella-mugging (CF-11(b)), look-decide (CF-13), parallel fiber
# (ADV-2), scrambled pair (CF-23), beta-pair (CF-14(a))
# ---------------------------------------------------------------------------
def umbrella_mugging():
    """CF-11(b): point d with A_d = {u, n, u↔r, u↔s} (policy labels, realized as
    pol-events on a coordinate the leaf-worlds do NOT record — as in post 11's C_0 the
    outcomes are just (weather, umbrella)), O_d = rain worlds; root coin r/s; the r-node
    consults d (edges to ur, nr, ur, nr), the s-node consults d too — an outcome-relevant
    simulation (edges to us, ns, ns, us).  Fr = Loc_d = post 11's C_0."""
    acts = [Eq("pol", "u"), Eq("pol", "n"), Eq("pol", "u↔r"), Eq("pol", "u↔s")]
    O_rain = Eq("weather", "r")
    d = Point("d", None, O_rain, acts)

    def leaf(weather, umb):
        return Leaf(W(weather=weather, umb=umb), 0)

    u, n, ur, us = acts
    rnode = Decision(d, {u: leaf("r", "u"), n: leaf("r", "n"), ur: leaf("r", "u"), us: leaf("r", "n")})
    snode = Decision(d, {u: leaf("s", "u"), n: leaf("s", "n"), ur: leaf("s", "n"), us: leaf("s", "u")})
    root = chance(("r", F(1, 2), rnode), ("s", F(1, 2), snode), events={"r": O_rain, "s": Eq("weather", "s")})
    return NS(B=Problem(root, name="umbrella-mugging"), d=d, O_rain=O_rain, acts=acts)


def look_decide():
    """CF-13's look-decision tree: root queries d' (O = ⊤, actions look/leave); leave →
    leaf w_leave ⊭ O_d; look → a d-node (O_d = 'opened', actions p, q → leaves w_p, w_q
    ⊨ O_d).  Strongly fair, veridical, covered, everyday-sequential."""
    look, leave = Eq("act1", "look"), Eq("act1", "leave")
    p_, q_ = Eq("act2", "p"), Eq("act2", "q")
    O_d = Eq("opened", 1)
    d = Point("d", None, O_d, [p_, q_])
    dprime = Point("d'", None, TOP, [look, leave])
    root = Decision(dprime, {leave: Leaf(W(act1="leave", opened=0, act2=BOT), 0),
                             look: Decision(d, {p_: Leaf(W(act1="look", opened=1, act2="p"), 2),
                                                q_: Leaf(W(act1="look", opened=1, act2="q"), 1)})})
    return NS(B=Problem(root, name="look-decide"), d=d, dprime=dprime, O_d=O_d, look=look, leave=leave, p=p_, q=q_)


def parallel_fiber():
    """adversary-cf ADV-2: root chance ½ to q1, q2 both carrying one point d, A_d={a,b};
    q1: a→(w_a,1), b→(w_b,0); q2: a→(w_a',0), b→(w_b',1); four distinct worlds."""
    a, b = Eq("act", "a"), Eq("act", "b")
    d = Point("d", None, TOP, [a, b])
    root = chance(("1", F(1, 2), Decision(d, {a: Leaf(W(side=1, act="a"), 1), b: Leaf(W(side=1, act="b"), 0)})),
                  ("2", F(1, 2), Decision(d, {a: Leaf(W(side=2, act="a"), 0), b: Leaf(W(side=2, act="b"), 1)})),
                  events={"1": Eq("side", 1), "2": Eq("side", 2)})
    return NS(B=Problem(root, name="parallel-fiber"), d=d, a=a, b=b)


def scrambled_pair():
    """CF-23's scrambled-consultation pair.  X: fair coin routing to two d-nodes with
    answer-to-leaf maps swapped (L: a→w1, b→w2; R: a→w2, b→w1).  Z: fair coin with a
    spurious d-query per branch (L: both answers → w1; R: both → w2).  w1 pays 1, w2 pays 0."""
    a, b = Eq("act", "a"), Eq("act", "b")
    d = Point("d", None, TOP, [a, b])
    w1, w2 = W(w=1), W(w=2)
    X = chance(("L", F(1, 2), Decision(d, {a: Leaf(w1, 1), b: Leaf(w2, 0)})),
               ("R", F(1, 2), Decision(d, {a: Leaf(w2, 0), b: Leaf(w1, 1)})))
    Z = chance(("L", F(1, 2), Decision(d, {a: Leaf(w1, 1), b: Leaf(w1, 1)})),
               ("R", F(1, 2), Decision(d, {a: Leaf(w2, 0), b: Leaf(w2, 0)})))
    return NS(X=Problem(X, name="X"), Z=Problem(Z, name="Z"), d=d, a=a, b=b, w1=w1, w2=w2)


def beta_pair():
    """CF-14(a)'s β-pair: two trees P, P' — root coin routes to q1/q2 both carrying d,
    identical subtrees except one interior chance label (β = ½ vs ⅓ at q2 in P');
    leaf labels equal (the upstream coin is not recorded in worlds).  P is strongly
    fair, P' is not, and Fr(P) = Fr(P') identically."""
    a, b = Eq("act", "a"), Eq("act", "b")
    d = Point("d", None, TOP, [a, b])
    wa1, wa2, wb = W(o="a1"), W(o="a2"), W(o="b")

    def sub(beta):
        return Decision(d, {a: chance(("1", beta, Leaf(wa1, 1)), ("2", 1 - beta, Leaf(wa2, 0))), b: Leaf(wb, 0)})

    Pt = chance(("L", F(1, 2), sub(F(1, 2))), ("R", F(1, 2), sub(F(1, 2))))
    Pp = chance(("L", F(1, 2), sub(F(1, 2))), ("R", F(1, 2), sub(F(1, 3))))
    return NS(P=Problem(Pt, name="P"), Pprime=Problem(Pp, name="P'"), d=d)


# ---------------------------------------------------------------------------
# FR-10's T_{d,e} / T_{e,d} / T_×
# ---------------------------------------------------------------------------
def sequenced_pair(v=None, nA: int = 2, nE: int = 2):
    """FR-10: A_d = {1..nA}, A_e = {1..nE}, joint payoff v(a, b), worlds recording
    (pol_d, pol_e).  T_{d,e}: root chooses a (point d), then a per-a point e_a chooses b
    knowing pol_d = a.  T_{e,d}: mirror.  T_×: product root.  Default v: v(1,1)=2,
    v(2,2)=1, off-diagonal 0 (extended by 0 for larger sizes)."""
    if v is None:
        def v(a, b):
            return 2 if (a, b) == (1, 1) else (1 if (a, b) == (2, 2) else 0)
    Ad = [Eq("pol_d", i) for i in range(1, nA + 1)]
    Ae = [Eq("pol_e", j) for j in range(1, nE + 1)]

    def leaf(a, b):
        return Leaf(W(pol_d=a, pol_e=b), v(a, b))

    d = Point("d", None, TOP, Ad)
    Tde = Decision(d, {Ad[a - 1]: Decision(Point(f"e|{a}", None, Eq("pol_d", a), Ae), {Ae[b - 1]: leaf(a, b) for b in range(1, nE + 1)})
                       for a in range(1, nA + 1)})
    e = Point("e", None, TOP, Ae)
    Ted = Decision(e, {Ae[b - 1]: Decision(Point(f"d|{b}", None, Eq("pol_e", b), Ad), {Ad[a - 1]: leaf(a, b) for a in range(1, nA + 1)})
                       for b in range(1, nE + 1)})
    prod_acts = {(a, b): dp.AllOf(Eq("pol_d", a), Eq("pol_e", b)) for a in range(1, nA + 1) for b in range(1, nE + 1)}
    dx = Point("d×e", None, TOP, list(prod_acts.values()))
    Tx = Decision(dx, {ev: leaf(a, b) for (a, b), ev in prod_acts.items()})
    return NS(T_de=Problem(Tde, name="T_de"), T_ed=Problem(Ted, name="T_ed"), T_x=Problem(Tx, name="T_x"), v=v, nA=nA, nE=nE)


# ---------------------------------------------------------------------------
# FR-3's ping-pong witness
# ---------------------------------------------------------------------------
def ping_pong(f=None, g=None):
    """FR-3: A_d = {a1, a2}, A_e = {b1, b2}; root chance ½; Left: d-node, below each
    answer an e-node, leaves f(a, b); Right: e-node, below each answer a d-node, leaves
    g(a, b); generic f, g (distinct payoffs 1..8 by default).  Both fibers unfair and
    entangled; naive per-fiber relocation ping-pongs, joint relocation at the closure
    {d, e} is fair."""
    fv = {("a1", "b1"): 1, ("a1", "b2"): 2, ("a2", "b1"): 3, ("a2", "b2"): 4}
    gv = {("a1", "b1"): 5, ("a1", "b2"): 6, ("a2", "b1"): 7, ("a2", "b2"): 8}
    f = f or (lambda a, b: fv[(a, b)])
    g = g or (lambda a, b: gv[(a, b)])
    a1, a2 = Eq("act_d", "a1"), Eq("act_d", "a2")
    b1, b2 = Eq("act_e", "b1"), Eq("act_e", "b2")
    d, e = Point("d", None, TOP, [a1, a2]), Point("e", None, TOP, [b1, b2])

    def leafL(a, b):
        return Leaf(W(side="L", act_d=a, act_e=b), f(a, b))

    def leafR(a, b):
        return Leaf(W(side="R", act_d=a, act_e=b), g(a, b))

    left = Decision(d, {a1: Decision(e, {b1: leafL("a1", "b1"), b2: leafL("a1", "b2")}),
                        a2: Decision(e, {b1: leafL("a2", "b1"), b2: leafL("a2", "b2")})})
    right = Decision(e, {b1: Decision(d, {a1: leafR("a1", "b1"), a2: leafR("a2", "b1")}),
                         b2: Decision(d, {a1: leafR("a1", "b2"), a2: leafR("a2", "b2")})})
    root = chance(("L", F(1, 2), left), ("R", F(1, 2), right), events={"L": Eq("side", "L"), "R": Eq("side", "R")})
    return NS(B=Problem(root, name="ping-pong"), d=d, e=e, a1=a1, a2=a2, b1=b1, b2=b2)


# ---------------------------------------------------------------------------
# fair-repair §3.2's fantasy-state imperfect equilibrium; FR-12's tie example
# ---------------------------------------------------------------------------
def fantasy_state(payoffs=(0, 4, 1)):
    """fair-repair §3.2: two points; d1 = (s1, ⊤, {out, in}): out → r_out; in → d2 =
    (s2, O2 = {act1 = in}, {x, y}): x → r_x, y → r_y (defaults 0, 4, 1).  Worlds record
    (act1, act2).  s1 is the strictly calibrated state for C = (out, y) (P = δ(out,⊥)),
    s2 the FANTASY state: P half-half on (in,x), (in,y) with V(in,x) = 0, V(in,y) = 5 —
    admissible because ν(O2) = 0 under C.  `fr12_tie()` = payoffs (0, 0, -1)."""
    r_out, r_x, r_y = payoffs
    out, in_ = Eq("act1", "out"), Eq("act1", "in")
    x_, y_ = Eq("act2", "x"), Eq("act2", "y")
    w_out, w_x, w_y = W(act1="out", act2=BOT), W(act1="in", act2="x"), W(act1="in", act2="y")
    s1 = State.certain(w_out, r_out, name="s1")
    s2 = State(Dist({w_x: F(1, 2), w_y: F(1, 2)}), {w_x: 0, w_y: 5}, name="s2-fantasy")
    d1, d2 = Point("d1", s1, TOP, [out, in_]), Point("d2", s2, in_, [x_, y_])
    root = Decision(d1, {out: Leaf(w_out, r_out), in_: Decision(d2, {x_: Leaf(w_x, r_x), y_: Leaf(w_y, r_y)})})
    return NS(B=Problem(root, name="fantasy-state"), d1=d1, d2=d2, out=out, in_=in_, x=x_, y=y_,
              C=Procedure({d1: out, d2: y_}, name="(out,y)"), Copt=Procedure({d1: in_, d2: x_}, name="(in,x)"))


def fr12_tie():
    """FR-12: out → 0; in → x → 0, y → -1.  C = (out, y) is V-optimal (0 = max) but
    tremble-EDT rejects y at d2 at every eps."""
    return fantasy_state(payoffs=(0, 0, -1))


# ---------------------------------------------------------------------------
# adversary-repair A.1's single-node unrealized-observation tree
# ---------------------------------------------------------------------------
def single_node_unrealized():
    """adversary-repair A.1: algebra act∈{a,b,⊥}, coin∈{H,T}; a single decision node
    with d = (s, O_d = {coin = T}, {a, b}); leaves a → (ω_a, 0), b → (ω_b, 1), ω_a ⊨ a∧H,
    ω_b ⊨ b∧H.  No leaf-world satisfies O_d: recording is vacuous for every C, the
    tree is strongly fair, and the state is free at every eps.  s: P = ½ each,
    V(ω_a) = 7, V(ω_b) = 0."""
    a, b = Eq("act", "a"), Eq("act", "b")
    wa, wb = W(act="a", coin="H"), W(act="b", coin="H")
    s = State(Dist({wa: F(1, 2), wb: F(1, 2)}), {wa: 7, wb: 0}, name="s")
    d = Point("d", s, Eq("coin", "T"), [a, b])
    return NS(B=Problem(Decision(d, {a: Leaf(wa, 0), b: Leaf(wb, 1)}), name="A.1"), d=d, a=a, b=b,
              Ca=Procedure({d: a}, name="δ_a"), Cb=Procedure({d: b}, name="δ_b"))


ALL = [mugging, decoupled_mugging, k_fold_mugging, relocated_mugging_direct, transparent_newcomb, told_you_so,
       smoking_lesion_S3, smoking_lesion_tickle, amd, cx1, self_prediction_miniature, routing_root, cx2,
       umbrella_mugging, look_decide, parallel_fiber, scrambled_pair, beta_pair, sequenced_pair, ping_pong,
       fantasy_state, fr12_tie, single_node_unrealized]
