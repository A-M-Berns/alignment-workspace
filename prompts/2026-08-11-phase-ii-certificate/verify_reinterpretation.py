"""Exact-rational check of the Track L restatement of Track C's certificate
under Track K's proposed skeleton-v2 execution layer.

Everything on a verdict path is `fractions.Fraction` or a Python `int`; no float
appears anywhere.  Section 6's enumeration works in scaled integers (credences
have denominator 4, grades and quantities are integers), which is exact; the
rational values are recovered by the divisions written in the comparisons, and
every comparison is cross-multiplied rather than divided.

Run with `python3 verify_reinterpretation.py` from this directory (stdlib only).

Sections:
  1. carriers -- skeleton v1 plus Track K Sec 9.2's execution layer;
  2. Track C's worked case re-run under the v2 strict-protection instantiation;
  3. what survives:  L1, L2, L7 invariant;  L3 and L4's loaded branch refuted;
  4. clause (iii) does not deliver a minority -- a counterexample to Track C
     Theorem C(b)'s gloss;
  5. the Q4 family: certificate fires, bound holds, channel would have blocked;
  6. an exhaustive small-domain enumeration of the restated bounds.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import combinations, product
from typing import Dict, List, Optional, Sequence, Tuple

FAILURES: List[str] = []
BOT = "_|_"


def check(label: str, condition: bool, detail: str = "") -> None:
    if not condition:
        FAILURES.append("{}: {}".format(label, detail))
    print("{:<66} {}{}".format(label, "ok" if condition else "FAIL",
                               ("  " + detail) if detail else ""))


# --------------------------------------------------------------------------
# 1. Carriers: skeleton v1 (Track C's Model) + Track K Sec 9.2's execution layer
# --------------------------------------------------------------------------

class ProtModel:
    """One decision index n over skeleton-v1 carriers with a v2 execution layer.

    The execution layer is instantiated as Track K Proposition 2's canonical
    shape, plus a capability assignment:

        R_n = Pi_n,  iota_n = id,  rho_n = J_n,
        kappa : Pi_n -> subsets of Pi_n + {BOT},  with  r in kappa(r)  (honesty),
        E_n(pi, r) = pi if pi in kappa(r) else BOT       ("clean execution map").

    kappa = {r: full menu} is the free instantiation and reproduces v1 exactly
    (Track K Proposition 2).  kappa = {r: {r, BOT}} is strict protection.

    X_bot : Omega -> Q with |X_bot| <= B is the declared null quantity
    (Track K Sec 9.2's amendment to Sec 1, and its Sec 9.3 first decision).
    """

    def __init__(self, states, P, menu, vplus, vhat, X, B, X_bot=None,
                 kappa=None, cells=None) -> None:
        self.states = list(states)
        self.P = dict(P)
        self.menu = list(menu)
        self.vplus = dict(vplus)
        self.vhat = dict(vhat)
        self.X = dict(X)
        self.B = B
        self.cells = [list(c) for c in cells] if cells else [[s] for s in states]
        self.X_bot = dict(X_bot) if X_bot is not None else {w: Q(0) for w in states}
        # default kappa: free (v1)
        self.kappa = ({r: frozenset(self.menu) | {BOT} for r in self.menu}
                      if kappa is None else {r: frozenset(v) for r, v in kappa.items()})
        assert sum(self.P.values()) == Q(1), "credence must sum to exactly 1"
        for w in self.states:
            assert self.P[w] >= 0
            assert abs(self.X_bot[w]) <= B, "bound B violated at BOT"
            for pi in self.menu:
                for table in (self.vplus, self.vhat, self.X):
                    assert abs(table[(w, pi)]) <= B, "bound B violated"
        for cell in self.cells:
            for pi in self.menu:
                assert len({self.vhat[(w, pi)] for w in cell}) == 1, \
                    "vhat is not t(n)-measurable"
        for r in self.menu:                       # E(iota(r), r) = iota(r)
            assert r in self.kappa[r], "honesty condition E(iota(r),r)=iota(r) fails"

    # --- v1 objects, unchanged -------------------------------------------

    def _least_argmax(self, table, w):
        best = None
        for pi in self.menu:
            if best is None or table[(w, pi)] > table[(w, best)]:
                best = pi
        return best

    def J(self, w):
        return self._least_argmax(self.vplus, w)

    def Jhat(self, w):
        return self._least_argmax(self.vhat, w)

    def eta(self, w) -> Q:
        return max(abs(self.vplus[(w, pi)] - self.vhat[(w, pi)]) for pi in self.menu)

    def epsilon(self) -> Q:
        return sum((self.P[w] * self.eta(w) for w in self.states), Q(0))

    def drift(self, w) -> Q:
        return max(abs(self.X[(w, pi)] - self.vplus[(w, pi)]) for pi in self.menu)

    def M(self, S=None) -> Q:
        dom = self.states if S is None else S
        return sum((self.P[w] * self.drift(w) for w in dom), Q(0))

    def margin_hat(self, w) -> Q:
        j = self.Jhat(w)
        return self.vhat[(w, j)] - max(self.vhat[(w, pi)]
                                       for pi in self.menu if pi != j)

    def certified_set(self, j) -> List[str]:
        return [w for w in self.states if self.Jhat(w) == j]

    def gamma(self, S) -> Q:
        return min(self.margin_hat(w) for w in S)

    def rho(self, S) -> Q:
        return sum((self.P[w] for w in S), Q(0))

    def defect(self, j, S) -> Q:
        return sum((self.P[w] * (self.vplus[(w, self.J(w))] - self.vplus[(w, j)])
                    for w in S), Q(0))

    def Gamma(self, pi) -> Q:
        return (sum((self.P[w] * self.vplus[(w, self.J(w))] for w in self.states), Q(0))
                - sum((self.P[w] * self.vplus[(w, pi)] for w in self.states), Q(0)))

    def Gamma_hat(self, pi) -> Q:
        return sum((self.P[w] * (self.vhat[(w, self.Jhat(w))] - self.vhat[(w, pi)])
                    for w in self.states), Q(0))

    # --- v2 execution layer ----------------------------------------------

    def rho_n(self, w):
        """The actual-report map.  R_n = Pi_n and rho_n = J_n."""
        return self.J(w)

    def realize(self, proposal, w):
        """E_n(alpha(w), rho_n(w)) -- the effect that in fact occurs."""
        pi = proposal(w)
        return pi if pi in self.kappa[self.rho_n(w)] else BOT

    def quantity(self, proposal, w) -> Q:
        e = self.realize(proposal, w)
        return self.X_bot[w] if e == BOT else self.X[(w, e)]

    def V(self, proposal) -> Q:
        return sum((self.P[w] * self.quantity(proposal, w) for w in self.states), Q(0))

    # --- proposals (v2 conducts) ------------------------------------------

    def prop_delegate(self):
        return lambda w: self.J(w)

    def prop_sim(self):
        return lambda w: self.Jhat(w)

    def prop_fixed(self, pi):
        return lambda w: pi

    def prop_act(self, j, S):
        Sset = set(S)
        return lambda w: (j if w in Sset else self.J(w))

    # --- the three-way split of the certified event ------------------------

    def split(self, j, S):
        """S1 = agreement; S2 = override permitted; S3 = proposal blocked."""
        S1 = [w for w in S if self.J(w) == j]
        S2 = [w for w in S if self.J(w) != j and j in self.kappa[self.rho_n(w)]]
        S3 = [w for w in S if self.J(w) != j and j not in self.kappa[self.rho_n(w)]]
        return S1, S2, S3

    def delta_bot(self, S) -> Q:
        """Delta_bot = max over S of the positive part of X_{J} - X_bot."""
        return max([self.X[(w, self.J(w))] - self.X_bot[w] for w in S] + [Q(0)])


def strict(menu):
    return {r: frozenset({r, BOT}) for r in menu}


def free(menu):
    return {r: frozenset(set(menu) | {BOT}) for r in menu}


# --------------------------------------------------------------------------
# the bounds, restated
# --------------------------------------------------------------------------

def bound_override(eps: Q, gamma: Q) -> Optional[Q]:
    """L2, verbatim: P(S and J != j) <= 2 eps / gamma."""
    return None if gamma == 0 else 2 * eps / gamma


def bound_defect(B: Q, eps: Q, gamma: Q) -> Q:
    """L3, verbatim: D_{n,j} <= 4B eps / (2B + gamma)."""
    return 4 * B * eps / (2 * B + gamma)


def kappa_free(B: Q, eps: Q, gamma: Q, M_S: Q) -> Q:
    """Track C L4: min of the settlement-free and the settlement-loaded branch."""
    loaded = bound_defect(B, eps, gamma) + 2 * M_S
    return loaded if gamma == 0 else min(4 * B * eps / gamma, loaded)


def kappa_prot(B: Q, eps: Q, gamma: Q, delta_b: Q) -> Q:
    """Track L: kappa^prot = Delta_bot * min(1, 2 eps / gamma).  The
    settlement-loaded branch is unavailable (Sec 3 below refutes it)."""
    if gamma == 0:
        return delta_b
    return delta_b * min(Q(1), 2 * eps / gamma)


def cert_clauses(m: ProtModel, j, S, theta: Q, eps: Q, kap: Q):
    """(i)-(iv).  (i) is checked by construction of S from Jhat."""
    if not S:
        return False, {}
    g, r = m.gamma(S), m.rho(S)
    c = {"(ii) margin": g > 0,
         "(iii) floor": g * r > 2 * eps,
         "(iv) budget": kap <= theta * r}
    return all(c.values()), c


# --------------------------------------------------------------------------
# 2. Track C's worked case under the v2 strict-protection instantiation
# --------------------------------------------------------------------------

def worked(X_bot_val, kap):
    states = ["w1", "w2", "w3", "w4"]
    P = {"w1": Q(9, 20), "w2": Q(1, 20), "w3": Q(1, 5), "w4": Q(3, 10)}
    menu = ["c", "s"]
    vhat = {("w1", "c"): Q(3, 2), ("w1", "s"): Q(-1, 2),
            ("w2", "c"): Q(3, 2), ("w2", "s"): Q(-1, 2),
            ("w3", "c"): Q(1, 4), ("w3", "s"): Q(1, 2),
            ("w4", "c"): Q(1, 4), ("w4", "s"): Q(1, 2)}
    vplus = {("w1", "c"): Q(3, 2), ("w1", "s"): Q(-1, 2),
             ("w2", "c"): Q(-1, 2), ("w2", "s"): Q(1),
             ("w3", "c"): Q(1, 2), ("w3", "s"): Q(1, 4),
             ("w4", "c"): Q(-1, 12), ("w4", "s"): Q(1, 2)}
    X = {("w1", "c"): Q(1), ("w1", "s"): Q(-1),
         ("w2", "c"): Q(-2), ("w2", "s"): Q(3, 2),
         ("w3", "c"): Q(1, 2), ("w3", "s"): Q(0),
         ("w4", "c"): Q(0), ("w4", "s"): Q(1, 2)}
    return ProtModel(states, P, menu, vplus, vhat, X, Q(2),
                     X_bot={w: X_bot_val for w in states},
                     kappa=kap(menu), cells=[["w1", "w2"], ["w3", "w4"]])


def run_worked() -> None:
    print("\n--- 2. Track C's worked case under the v2 execution layer ---")
    j = "c"

    # (a) the free instantiation reproduces Track C exactly (Track K Prop 2).
    m = worked(Q(0), free)
    S = m.certified_set(j)
    eps, g, r = m.epsilon(), m.gamma(S), m.rho(S)
    check("free instantiation: S = {w1,w2}, eps = 1/4, gamma = 2, rho = 1/2",
          S == ["w1", "w2"] and eps == Q(1, 4) and g == Q(2) and r == Q(1, 2))
    V_del = m.V(m.prop_delegate())
    V_act = m.V(m.prop_act(j, S))
    check("free instantiation: V(DELEGATE) = 31/40, V(ACT[c,S]) = 3/5",
          V_del == Q(31, 40) and V_act == Q(3, 5))
    check("free instantiation: preemption cost = 7/40 (Track C Sec 6.1)",
          V_del - V_act == Q(7, 40))
    check("free instantiation: realized effect at w2 is c, overriding J(w2) = s",
          m.realize(m.prop_act(j, S), "w2") == "c" and m.J("w2") == "s")

    # (b) strict protection, three declarations of X_bot.
    gaps = {}
    for lab, xb in (("X_bot = 0", Q(0)), ("X_bot = -B = -2", Q(-2)),
                    ("X_bot = +B = 2", Q(2))):
        mp = worked(xb, strict)
        Vd, Va = mp.V(mp.prop_delegate()), mp.V(mp.prop_act(j, S))
        gaps[lab] = (Vd, Va, Vd - Va)
        check("strict, {}: realized effect at w2 is BOT, not c".format(lab),
              mp.realize(mp.prop_act(j, S), "w2") == BOT)
    check("strict, X_bot = 0: V(DELEGATE) = 31/40, V(ACT) = 7/10, gap = 3/40",
          gaps["X_bot = 0"] == (Q(31, 40), Q(7, 10), Q(3, 40)),
          str(gaps["X_bot = 0"]))
    check("strict, X_bot = -2: V(ACT) = 3/5 and gap = 7/40 -- IDENTICAL to free",
          gaps["X_bot = -B = -2"] == (Q(31, 40), Q(3, 5), Q(7, 40)),
          str(gaps["X_bot = -B = -2"]))
    check("strict, X_bot = +2: gap = -1/40, i.e. refusal beats delegation",
          gaps["X_bot = +B = 2"][2] == Q(-1, 40), str(gaps["X_bot = +B = 2"][2]))
    print("    [Track K Theorem 9 instantiated inside Track C's own worked case:")
    print("     protection changes the realized effect at w2 from c to BOT and")
    print("     leaves V_n and the preemption cost at exactly 7/40 when X_bot=-B.]")

    # (c) Track K Theorem 8(a) over every proposal, in this model.
    mp = worked(Q(0), strict)
    allowed = 0
    for tup in product(mp.menu, repeat=len(mp.states)):
        alpha = dict(zip(mp.states, tup))
        for w in mp.states:
            e = mp.realize(lambda x: alpha[x], w)
            if e in (mp.J(w), BOT):
                allowed += 1
    check("strict: every one of 2^4 proposals realizes in {J(w), BOT} at all 4 states",
          allowed == 16 * 4, str(allowed))

    # (d) the restated budget clause and Theorem L(a).
    for lab, xb in (("X_bot = 0", Q(0)), ("X_bot = -B", Q(-2))):
        mp = worked(xb, strict)
        d_b = mp.delta_bot(S)
        kp = kappa_prot(mp.B, eps, g, d_b)
        gap = mp.V(mp.prop_delegate()) - mp.V(mp.prop_act(j, S))
        ok, cl = cert_clauses(mp, j, S, Q(2), eps, kp)
        check("strict, {}: Cert^prot(theta=2) fires; gap {} <= kappa^prot {} <= "
              "theta*rho = 1".format(lab, gap, kp),
              ok and gap <= kp <= Q(2) * r, str(cl))


# --------------------------------------------------------------------------
# 3. What survives: L1, L2, L7 invariant; L3 and L4's loaded branch refuted
# --------------------------------------------------------------------------

def q4_family(p: Q, delta: Q, X_bot_val: Q, kap):
    """B = 1.  S = Omega = {u, wstar}, one decision-time cell, Jhat = a with
    margin gamma = 1.  At u the model is exact; at wstar the principal in fact
    recommends b and the per-state quantity gap X_b - X_a is exactly 2B."""
    states = ["u", "wstar"]
    P = {"u": 1 - p, "wstar": p}
    menu = ["a", "b"]
    vhat = {(w, "a"): Q(1, 2) for w in states}
    vhat.update({(w, "b"): Q(-1, 2) for w in states})
    vplus = {("u", "a"): Q(1, 2), ("u", "b"): Q(-1, 2),
             ("wstar", "a"): -delta, ("wstar", "b"): delta}
    X = {("u", "a"): Q(0), ("u", "b"): Q(0),
         ("wstar", "a"): Q(-1), ("wstar", "b"): Q(1)}
    if X_bot_val == "mirror":
        # X_bot(w) := X_{n,pi}(w) for the unique pi != J_n(w).  A legal
        # declaration (Track K Sec 9.2 only requires |X_bot| <= B), and the
        # exact-coincidence case of the V-blindness proposition.
        Jm = {"u": "a", "wstar": "b"}
        X_bot = {w: X[(w, "b" if Jm[w] == "a" else "a")] for w in states}
    else:
        X_bot = {w: X_bot_val for w in states}
    return ProtModel(states, P, menu, vplus, vhat, X, Q(1),
                     X_bot=X_bot, kappa=kap(menu), cells=[states])


def run_survival() -> None:
    print("\n--- 3. which lemmas survive the execution layer ---")
    p, delta = Q(1, 100), Q(1, 4)
    mf = q4_family(p, delta, Q(-1), free)
    mp = q4_family(p, delta, Q(-1), strict)
    S, j = mf.certified_set("a"), "a"
    eps, g = mf.epsilon(), mf.gamma(S)

    # L1, L2, L7 are functions of (vplus, vhat, P) only: identical in both.
    check("L1/L2/L7 inputs are architecture-independent: eta, gamma, eps, "
          "Gamma, Gamma_hat identical under free and strict",
          all(mf.eta(w) == mp.eta(w) for w in mf.states)
          and mf.epsilon() == mp.epsilon() and mf.gamma(S) == mp.gamma(S)
          and all(mf.Gamma(pi) == mp.Gamma(pi) and
                  mf.Gamma_hat(pi) == mp.Gamma_hat(pi) for pi in mf.menu))
    check("L1: gamma_hat(wstar) = 1 > 2*eta(wstar) is FALSE, so L1 is silent "
          "at wstar -- the override event is exactly where L1 does not apply",
          not (mf.margin_hat("wstar") > 2 * mf.eta("wstar")))
    ov = sum((mf.P[w] for w in S if mf.J(w) != j), Q(0))
    check("L2 holds under both: override mass {} <= 2eps/gamma = {}"
          .format(ov, bound_override(eps, g)), ov <= bound_override(eps, g))
    for pi in mf.menu:
        check("L7 holds: |Gamma({}) - Gamma_hat({})| <= 2 eps".format(pi, pi),
              abs(mf.Gamma(pi) - mf.Gamma_hat(pi)) <= 2 * eps)

    # L3's constant survives as arithmetic; its consumer does not.
    D = mf.defect(j, S)
    check("L3 still holds as a statement about D_{n,j}: D = %s <= %s"
          % (D, bound_defect(mf.B, eps, g)), D <= bound_defect(mf.B, eps, g))
    gap_prot = mp.V(mp.prop_delegate()) - mp.V(mp.prop_act(j, S))
    check("L3's bound is NOT a bound on the protected valuation gap: "
          "gap_prot = {} > 4B eps/(2B+gamma) = {}"
          .format(gap_prot, bound_defect(mf.B, eps, g)),
          gap_prot > bound_defect(mf.B, eps, g))
    M_S = mf.M(S)
    loaded = bound_defect(mf.B, eps, g) + 2 * M_S
    check("L4's settlement-loaded branch is not violated in this family (it is "
          "loose here); the refuting witness is the next check",
          gap_prot <= loaded)

    # L4's settlement-loaded branch is FALSE under protection.  Full-support
    # witness, the maximum-slack one in Sec 6's domain.
    st = ["w1", "w2"]
    wit = dict(states=st, P={"w1": Q(1, 4), "w2": Q(3, 4)}, menu=["a", "b"],
               vplus={(w, pi): Q(1) for w in st for pi in ("a", "b")},
               vhat={("w1", "a"): Q(0), ("w1", "b"): Q(1),
                     ("w2", "a"): Q(0), ("w2", "b"): Q(1)},
               X={(w, pi): Q(1) for w in st for pi in ("a", "b")}, B=Q(1))
    wf = ProtModel(X_bot={w: Q(-1) for w in st}, kappa=free(["a", "b"]),
                   cells=[st], **wit)
    wp = ProtModel(X_bot={w: Q(-1) for w in st}, kappa=strict(["a", "b"]),
                   cells=[st], **wit)
    Sw, jw = wf.certified_set("b"), "b"
    ew, gw, Mw = wf.epsilon(), wf.gamma(Sw), wf.M(Sw)
    gpw = wp.V(wp.prop_delegate()) - wp.V(wp.prop_act(jw, Sw))
    loaded_w = bound_defect(wf.B, ew, gw) + 2 * Mw
    check("REFUTING WITNESS (full support): eps = 1, gamma = 1, M_S = 0, "
          "gap_prot = 2 > 4/3 = 4B eps/(2B+gamma) + 2 M_S",
          Sw == st and ew == Q(1) and gw == Q(1) and Mw == Q(0)
          and gpw == Q(2) and loaded_w == Q(4, 3) and gpw > loaded_w,
          "{} {} {} {} {}".format(Sw, ew, gw, gpw, loaded_w))
    check("... while Track L's surviving branch 4B eps/gamma = 4 and the "
          "Delta_bot form Delta_bot*min(1,2eps/gamma) = 2 both hold, the "
          "second exactly attained",
          gpw <= 4 * wf.B * ew / gw
          and kappa_prot(wf.B, ew, gw, wp.delta_bot(Sw)) == Q(2))
    check("L4's settlement-free branch 4B eps/gamma = {} does bound gap_prot"
          .format(4 * mf.B * eps / g), gap_prot <= 4 * mf.B * eps / g)

    # L5's comparator does not survive: FIXED[pi] no longer realizes pi.
    mis = [w for w in mp.states if mp.realize(mp.prop_fixed("b"), w) != "b"]
    check("L5's comparator FIXED[b] does not realize b under strict protection "
          "(it realizes BOT at u)", mis == ["u"], str(mis))

    # L6's constant survives.
    dis = sum((mp.P[w] for w in mp.states if mp.J(w) != mp.Jhat(w)), Q(0))
    check("L6 survives with its constant: V(DEL) - V(SIM) <= 2B P(Jhat != J)",
          mp.V(mp.prop_delegate()) - mp.V(mp.prop_sim()) <= 2 * mp.B * dis)

    # I1 survives protection: vhat = vplus makes SIM and DELEGATE identical
    # in realization as well as in valuation.
    m5 = ProtModel(["w1", "w2"], {"w1": Q(1, 3), "w2": Q(2, 3)}, ["a", "b"],
                   vplus={("w1", "a"): Q(1), ("w1", "b"): Q(-1),
                          ("w2", "a"): Q(-1), ("w2", "b"): Q(1)},
                   vhat={("w1", "a"): Q(1), ("w1", "b"): Q(-1),
                         ("w2", "a"): Q(-1), ("w2", "b"): Q(1)},
                   X={("w1", "a"): Q(1, 2), ("w1", "b"): Q(-1, 3),
                      ("w2", "a"): Q(-1, 5), ("w2", "b"): Q(1, 7)}, B=Q(1),
                   X_bot={"w1": Q(-1), "w2": Q(-1)}, kappa=strict(["a", "b"]),
                   cells=[["w1"], ["w2"]])
    check("I1 survives protection: with vhat = vplus, SIM and DELEGATE have "
          "identical realizations and identical V under strict protection",
          all(m5.realize(m5.prop_sim(), w) == m5.realize(m5.prop_delegate(), w)
              for w in m5.states)
          and m5.V(m5.prop_sim()) == m5.V(m5.prop_delegate()))


# --------------------------------------------------------------------------
# 4. Clause (iii) does not deliver a minority
# --------------------------------------------------------------------------

def run_clause_iii() -> None:
    print("\n--- 4. clause (iii): a majority-override counterexample ---")
    p, delta = Q(3, 5), Q(1, 4)
    m = q4_family(p, delta, Q(0), free)
    S, j = m.certified_set("a"), "a"
    eps, g, r = m.epsilon(), m.gamma(S), m.rho(S)
    M_S = m.M(S)
    kap = kappa_free(m.B, eps, g, M_S)
    theta = kap / r
    ok, cl = cert_clauses(m, j, S, theta, eps, kap)
    ov = sum((m.P[w] for w in S if m.J(w) != j), Q(0))
    check("counterexample: eps = 9/20, gamma = 1, rho = 1, kappa = 9/5",
          eps == Q(9, 20) and g == Q(1) and r == Q(1) and kap == Q(9, 5),
          "{} {} {} {}".format(eps, g, r, kap))
    check("counterexample: all four clauses of Cert hold at theta = 9/5",
          ok and theta == Q(9, 5), str(cl))
    check("counterexample: Theorem C(a)'s bound holds -- gap {} <= theta*rho {}"
          .format(m.V(m.prop_delegate()) - m.V(m.prop_act(j, S)), theta * r),
          m.V(m.prop_delegate()) - m.V(m.prop_act(j, S)) <= theta * r)
    check("counterexample: override mass is 3/5 of rho -- a strict MAJORITY, "
          "so Theorem C(b)'s 'strict minority' gloss is false",
          ov == Q(3, 5) and ov > r / 2)
    check("what clause (iii) does deliver: override mass < rho, i.e. the "
          "certified act executes on positive mass", ov < r)
    check("a genuine majority claim needs gamma*rho > 4 eps, which fails here",
          not (g * r > 4 * eps))


# --------------------------------------------------------------------------
# 5. Why approximate certification cannot replace the protected channel
# --------------------------------------------------------------------------

def run_q4() -> None:
    print("\n--- 5. the certificate's register is blind to the channel ---")
    for eps_t, th_t in ((Q(1, 10), Q(1, 10)), (Q(1, 1000), Q(1, 1000)),
                        (Q(1, 10 ** 6), Q(1, 10 ** 6))):
        delta = Q(1, 4)
        p = min(4 * eps_t / 3, th_t / 3, Q(1, 2))
        mf = q4_family(p, delta, Q(-1), free)
        mp = q4_family(p, delta, Q(-1), strict)
        S, j = mf.certified_set("a"), "a"
        eps, g, r = mf.epsilon(), mf.gamma(S), mf.rho(S)
        kap = kappa_free(mf.B, eps, g, mf.M(S))
        ok, cl = cert_clauses(mf, j, S, th_t, eps, kap)
        gap_f = mf.V(mf.prop_delegate()) - mf.V(mf.prop_act(j, S))
        gap_p = mp.V(mp.prop_delegate()) - mp.V(mp.prop_act(j, S))
        tag = "eps<={}, theta={}".format(eps_t, th_t)
        check("[{}] eps_n = {} <= {}; Cert fires; bound holds: {} <= {}"
              .format(tag, eps, eps_t, gap_f, th_t * r),
              eps <= eps_t and ok and gap_f <= th_t * r, str(cl))
        check("[{}] free realization at wstar is a, overriding J = b, at the "
              "maximal per-state quantity gap 2B = 2".format(tag),
              mf.realize(mf.prop_act(j, S), "wstar") == "a"
              and mf.J("wstar") == "b"
              and mf.X[("wstar", "b")] - mf.X[("wstar", "a")] == 2 * mf.B)
        check("[{}] the channel blocks exactly that effect: strict realization "
              "at wstar is BOT".format(tag),
              mp.realize(mp.prop_act(j, S), "wstar") == BOT)
        check("[{}] the two preemption costs coincide exactly: {} = {}"
              .format(tag, gap_f, gap_p), gap_f == gap_p)
        # exact-coincidence case: X_bot mirrors the non-recommended quantity
        mf2 = q4_family(p, delta, "mirror", free)
        mp2 = q4_family(p, delta, "mirror", strict)
        check("[{}] V_n is blind: with X_bot(w) = X_{{n,pi}}(w) for pi != J(w), "
              "free and strict assign the SAME value to every proposal".format(tag),
              all(mf2.V(lambda w, a=dict(zip(mf2.states, t)): a[w])
                  == mp2.V(lambda w, a=dict(zip(mp2.states, t)): a[w])
                  for t in product(mf2.menu, repeat=len(mf2.states))))
        check("[{}] ... while the realizations differ at wstar: a versus BOT"
              .format(tag),
              mf2.realize(mf2.prop_act(j, S), "wstar") == "a"
              and mp2.realize(mp2.prop_act(j, S), "wstar") == BOT)

    print("    [as eps_n -> 0 the certificate's bound -> 0 and the V_n-difference")
    print("     between the two architectures is 0 at every eps_n, while the")
    print("     per-state realized-effect difference at wstar stays 2B throughout.]")

    # the robust form: the V-difference the channel makes is itself bounded by
    # the certificate's own bound, in every model.
    print("\n    robust form, over a declared grid:")
    worst = Q(0)
    for xb in (Q(-1), Q(-1, 2), Q(0), Q(1, 2), Q(1)):
        for p in (Q(1, 10), Q(1, 4), Q(1, 2)):
            mf = q4_family(p, Q(1, 4), xb, free)
            mp = q4_family(p, Q(1, 4), xb, strict)
            S, j = mf.certified_set("a"), "a"
            eps, g = mf.epsilon(), mf.gamma(S)
            gf = mf.V(mf.prop_delegate()) - mf.V(mf.prop_act(j, S))
            gp = mp.V(mp.prop_delegate()) - mp.V(mp.prop_act(j, S))
            ovm = sum((mf.P[w] for w in S if mf.J(w) != j), Q(0))
            assert abs(gf - gp) <= 2 * mf.B * ovm
            worst = max(worst, abs(gf - gp) - 2 * mf.B * ovm)
    check("|gap_free - gap_prot| <= 2B * P(S and J != j) <= 4B eps/gamma "
          "on the whole grid", worst <= 0, "slack max = {}".format(worst))


# --------------------------------------------------------------------------
# 5b. Genuine coexistence: a non-strict kappa, and what its discretion is
# --------------------------------------------------------------------------

def whitelist_model(p: Q, kind: str):
    """Three interventions, B = 1.  kappa(r) = {r, h, BOT}: the report's own
    designation, a standing safe fallback h, and refusal.  This is the only
    shape in which the authorized menu has two interventions at every state,
    i.e. the only shape in which certified discretion and categorical authority
    coexist at a state rather than partitioning the states between them."""
    states = ["u", "wstar"]
    P = {"u": 1 - p, "wstar": p}
    menu = ["c", "s", "h"]
    vhat = {(w, "c"): Q(-1, 2) for w in states}
    vhat.update({(w, "s"): Q(-1, 2) for w in states})
    vhat.update({(w, "h"): Q(1, 2) for w in states})
    vplus = {("u", "c"): Q(-1, 2), ("u", "s"): Q(-1, 2), ("u", "h"): Q(1, 2),
             ("wstar", "c"): Q(1, 4), ("wstar", "s"): Q(-1, 2),
             ("wstar", "h"): Q(-1, 4)}
    X = {("u", "c"): Q(0), ("u", "s"): Q(0), ("u", "h"): Q(0),
         ("wstar", "c"): Q(1), ("wstar", "s"): Q(0), ("wstar", "h"): Q(-1)}
    if kind == "whitelist":
        kap = {r: frozenset({r, "h", BOT}) for r in menu}
    elif kind == "strict":
        kap = strict(menu)
    else:
        kap = free(menu)
    return ProtModel(states, P, menu, vplus, vhat, X, Q(1),
                     X_bot={w: Q(0) for w in states}, kappa=kap, cells=[states])


def run_whitelist() -> None:
    print("\n--- 5b. a non-strict kappa: where certified discretion lives ---")
    p = Q(1, 10)
    mw = whitelist_model(p, "whitelist")
    ms = whitelist_model(p, "strict")
    mf = whitelist_model(p, "free")
    j, S = "h", mw.certified_set("h")
    eps, g, r = mw.epsilon(), mw.gamma(S), mw.rho(S)
    check("whitelist: S = Omega, Jhat = h with gamma = 1, eps = 3/40, rho = 1",
          S == ["u", "wstar"] and g == Q(1) and eps == Q(3, 40) and r == Q(1),
          "{} {} {}".format(g, eps, r))
    check("whitelist: J(wstar) = c, so wstar is an override state for j = h",
          mw.J("wstar") == "c" and mw.J("u") == "h")
    # Proposition L6: every non-compliant element of the authorized menu is an
    # override.  The whitelist enlarges the menu exactly at the states where
    # taking the whitelisted intervention overrides the principal.
    menus = {w: sorted(mw.kappa[mw.rho_n(w)] - {BOT}) for w in mw.states}
    check("whitelist: the authorized menu is a singleton exactly where the "
          "report already designates h, and has 2 elements elsewhere",
          menus == {"u": ["h"], "wstar": ["c", "h"]}, str(menus))
    # Proposition L6, checked over every capability assignment on this menu
    # that protects and satisfies honesty, and every proposal:
    #   realizing any authorized effect other than iota(rho(w)) changes the
    #   realized effect away from DELEGATE's.  There is no third kind of option.
    bad = 0
    subsets = [frozenset(t) for k in range(len(mw.menu) + 1)
               for t in combinations(mw.menu, k)]
    for assign in product(subsets, repeat=len(mw.menu)):
        kap = {r: assign[i] | {r, BOT} for i, r in enumerate(mw.menu)}
        m = whitelist_model(p, "free")
        m.kappa = {r: frozenset(v) for r, v in kap.items()}
        for w in m.states:
            dele = m.realize(m.prop_delegate(), w)
            for pi in m.kappa[m.rho_n(w)]:
                if pi == BOT:
                    continue
                got = m.realize(lambda x, c=pi: c, w)
                if (got == dele) != (pi == m.J(w)):
                    bad += 1
    check("Proposition L6: over all {} protecting kappa on a 3-element menu, "
          "an authorized effect equals DELEGATE's realization iff it is the "
          "report's own designation -- every other authorized option is an "
          "override".format(len(subsets) ** 3), bad == 0, str(bad))
    check("whitelist: the report-independent menu is exactly {h} -- the "
          "intervention subject to no authority relation",
          sorted(set.intersection(*[set(mw.kappa[rr]) for rr in mw.menu]) - {BOT})
          == ["h"])
    # and a certificate for j = h overrides the principal at wstar
    check("whitelist: ACT[h,S] realizes h at wstar, overriding J = c, at the "
          "maximal per-state quantity gap 2B = 2",
          mw.realize(mw.prop_act(j, S), "wstar") == "h"
          and mw.X[("wstar", "c")] - mw.X[("wstar", "h")] == 2 * mw.B)
    check("whitelist: the same conduct under strict protection realizes BOT",
          ms.realize(ms.prop_act(j, S), "wstar") == BOT)
    gw = mw.V(mw.prop_delegate()) - mw.V(mw.prop_act(j, S))
    gs = ms.V(ms.prop_delegate()) - ms.V(ms.prop_act(j, S))
    gf = mf.V(mf.prop_delegate()) - mf.V(mf.prop_act(j, S))
    check("whitelist: gap under whitelist = gap under NO protection = {} , "
          "twice the strict gap {}".format(gw, gs),
          gw == gf == Q(1, 5) and gs == Q(1, 10))
    check("whitelist: Theorem L(a)'s coarse bound 4B eps/gamma = {} holds for "
          "all three architectures".format(4 * mw.B * eps / g),
          max(gw, gs, gf) <= 4 * mw.B * eps / g)
    print("    [a certificate whose j lies in the report-independent menu is")
    print("     unconstrained by kappa: whitelist protection and no protection")
    print("     give the identical valuation and the identical realization.]")


# --------------------------------------------------------------------------
# 6. Exhaustive small-domain enumeration over the v2 execution layer
# --------------------------------------------------------------------------

def run_enumeration() -> None:
    """Two states, two interventions, F_{t(n)} discrete, B = 1.  Grades over
    {-1,0,1}^4 for both vplus and vhat, X over {-1,1}^4, X_bot constant over
    {-1,0,1}, P over the five simplex points of denominator 4, S over every
    nonempty subset of {Jhat = j}, and both architectures at every point.

    Worked in scaled integers -- credences carry a factor of 4, so every
    valuation numerator is an integer and every comparison is cross-multiplied
    rather than divided.  This is exact arithmetic; no float and no Fraction
    rounding is involved.  (State-dependent X_bot is covered by the grid in
    Section 5; here X_bot is the constant a per-instantiation declaration
    naturally is.)
    """
    print("\n--- 6. exhaustive enumeration over the v2 execution layer ---")
    grades = (-1, 0, 1)
    xs = (-1, 1)
    masses = [(k, 4 - k) for k in range(5)]         # numerators over 4
    B = 1
    models = instances = 0
    f_L2 = f_L3 = f_L4free = f_protfree = f_protdelta = 0
    f_reach = f_split = f_blind = 0
    refute_loaded = 0
    witness = None

    def amax(pair):                                  # least maximizer, 0 < 1
        return 0 if pair[0] >= pair[1] else 1

    for vp in product(grades, repeat=4):
        vpl = ((vp[0], vp[1]), (vp[2], vp[3]))
        Js = (amax(vpl[0]), amax(vpl[1]))
        for vh in product(grades, repeat=4):
            vhl = ((vh[0], vh[1]), (vh[2], vh[3]))
            Jh = (amax(vhl[0]), amax(vhl[1]))
            eta = tuple(max(abs(vpl[i][k] - vhl[i][k]) for k in (0, 1))
                        for i in (0, 1))
            marg = tuple(vhl[i][Jh[i]] - vhl[i][1 - Jh[i]] for i in (0, 1))
            for xv in product(xs, repeat=4):
                Xl = ((xv[0], xv[1]), (xv[2], xv[3]))
                drift = tuple(max(abs(Xl[i][k] - vpl[i][k]) for k in (0, 1))
                              for i in (0, 1))
                for xb in grades:
                    for w0, w1 in masses:
                        models += 1
                        wt = (w0, w1)
                        eps4 = w0 * eta[0] + w1 * eta[1]
                        Vdel4 = wt[0] * Xl[0][Js[0]] + wt[1] * Xl[1][Js[1]]

                        # Track K Theorem 8(a): under strict protection every
                        # proposal realizes in {J(w), BOT}.
                        for t in product((0, 1), repeat=2):
                            for i in (0, 1):
                                eff = t[i] if t[i] == Js[i] else "BOT"
                                if eff != Js[i] and eff != "BOT":
                                    f_reach += 1

                        for j in (0, 1):
                            full = [i for i in (0, 1) if Jh[i] == j]
                            for rr in (1, 2):
                                if rr > len(full):
                                    continue
                                for S in combinations(full, rr):
                                    instances += 1
                                    g = min(marg[i] for i in S)
                                    rho4 = sum(wt[i] for i in S)
                                    MS4 = sum(wt[i] * drift[i] for i in S)
                                    ov4 = sum(wt[i] for i in S if Js[i] != j)
                                    D4 = sum(wt[i] * (vpl[i][Js[i]] - vpl[i][j])
                                             for i in S)

                                    # --- L2 and L3, verbatim ------------------
                                    if g > 0 and ov4 * g > 2 * eps4:
                                        f_L2 += 1
                                    if D4 * (2 * B + g) > 4 * B * eps4:
                                        f_L3 += 1

                                    # --- the two realizations -----------------
                                    Vf4 = Vp4 = 0
                                    for i in (0, 1):
                                        prop = j if i in S else Js[i]
                                        Vf4 += wt[i] * Xl[i][prop]
                                        Vp4 += wt[i] * (Xl[i][prop]
                                                        if prop == Js[i] else xb)
                                    gapf4, gapp4 = Vdel4 - Vf4, Vdel4 - Vp4

                                    # --- Track C L4 under the free layer ------
                                    b1 = (g > 0 and gapf4 * g <= 4 * B * eps4)
                                    b2 = (gapf4 * (2 * B + g)
                                          <= 4 * B * eps4 + 2 * MS4 * (2 * B + g))
                                    if not (b1 or b2):
                                        f_L4free += 1

                                    # --- Track L: settlement-free branch ------
                                    if g > 0 and gapp4 * g > 4 * B * eps4:
                                        f_protfree += 1

                                    # --- Track L: the Delta_bot refinement ----
                                    #   kappa^prot = Delta_bot * min(1, 2 eps/g)
                                    db = max([Xl[i][Js[i]] - xb for i in S] + [0])
                                    if g > 0:
                                        if 2 * eps4 <= 4 * g:        # 2eps/g <= 1
                                            okd = gapp4 * g <= 2 * db * eps4
                                        else:
                                            okd = gapp4 <= 4 * db
                                        if not okd:
                                            f_protdelta += 1

                                    # --- the loaded branch, under protection --
                                    if g > 0 and gapp4 * (2 * B + g) > (
                                            4 * B * eps4 + 2 * MS4 * (2 * B + g)):
                                        refute_loaded += 1
                                        if witness is None:
                                            witness = (vpl, vhl, Xl, xb, wt, j, S,
                                                       g, eps4, MS4, gapp4)

                                    # --- the three-way split ------------------
                                    #   under strict protection S2 is empty and
                                    #   S3 = S and {J != j}
                                    S3 = sum(wt[i] for i in S if Js[i] != j)
                                    if S3 != ov4:
                                        f_split += 1

                                    # --- V-blindness --------------------------
                                    if abs(gapf4 - gapp4) > 2 * B * ov4:
                                        f_blind += 1

    check("enumeration: {} models, {} certified (j,S) instances"
          .format(models, instances), models == 1574640 and instances > 0,
          "{} / {}".format(models, instances))
    check("L2 holds at every instance", f_L2 == 0, str(f_L2))
    check("L3 holds at every instance", f_L3 == 0, str(f_L3))
    check("Track C L4 holds under the free instantiation", f_L4free == 0, str(f_L4free))
    check("Track K Theorem 8(a) holds at every proposal", f_reach == 0, str(f_reach))
    check("Track L (a): gap_prot <= 4B eps/gamma at every instance",
          f_protfree == 0, str(f_protfree))
    check("Track L (a'): gap_prot <= Delta_bot * min(1, 2 eps/gamma)",
          f_protdelta == 0, str(f_protdelta))
    check("strict protection: S2 empty and P(S3) = P(S and J != j) at every instance",
          f_split == 0, str(f_split))
    check("V-blindness: |gap_free - gap_prot| <= 2B * P(S and J != j) everywhere",
          f_blind == 0, str(f_blind))
    check("REFUTED: L4's settlement-loaded branch is not a bound on the "
          "protected gap -- {} violating instances (nonzero is the finding)"
          .format(refute_loaded), refute_loaded > 0, str(refute_loaded))
    if witness is not None:
        print("    first witness (vplus, vhat, X, X_bot, 4P, j, S, gamma, 4eps, "
              "4M_S, 4gap_prot):\n      {}".format(witness))


if __name__ == "__main__":
    run_worked()
    run_survival()
    run_clause_iii()
    run_q4()
    run_whitelist()
    run_enumeration()
    print("\n{} check(s) failed".format(len(FAILURES)))
    for f in FAILURES:
        print("  " + f)
    raise SystemExit(1 if FAILURES else 0)
