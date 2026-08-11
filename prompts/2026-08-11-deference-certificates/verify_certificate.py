"""Exact-rational check of the Track C certificate derivation.

Everything here is `fractions.Fraction`; no floats appear on any verdict path.
Run with `python3 verify_certificate.py` from this directory (stdlib only).

Sections, in the order the report states them:
  1. the model type over FINITE_MODEL_SKELETON.md v1 carriers;
  2. the worked exact-rational shutdown/correction case, computed end to end;
  3. the four necessity witnesses;
  4. the three sharpness constructions;
  5. an exhaustive small-domain stress test of every derived inequality.

A pass of section 5 is *not* a proof of the general statements; the proofs are in
REPORT.md and the enumeration is a check on them over one declared finite domain.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
from typing import Dict, List, Optional, Sequence, Tuple

FAILURES: List[str] = []


def check(label: str, condition: bool, detail: str = "") -> None:
    if not condition:
        FAILURES.append("{}: {}".format(label, detail))
    print("{:<58} {}{}".format(label, "ok" if condition else "FAIL",
                               ("  " + detail) if detail else ""))


# --------------------------------------------------------------------------
# 1. The model
# --------------------------------------------------------------------------

class Model:
    """One decision index n over skeleton-v1 carriers.

    states      -- the finite state space Omega
    P           -- A's time-n credence, exact rationals summing to 1
    menu        -- Pi_n, in its fixed linear order (the tie-break order)
    vplus       -- the principal's grade at F(n):  (state, pi) -> Q
    vhat        -- A's model of it, available at t(n): (state, pi) -> Q
    X           -- the intervention-indexed quantity: (state, pi) -> Q
    B           -- the declared bound
    cells       -- the partition F_{t(n)}; vhat and X-independent selectors must
                   be constant on cells.  Selections are checked against it.
    """

    def __init__(self, states: Sequence[str], P: Dict[str, Q], menu: Sequence[str],
                 vplus: Dict[Tuple[str, str], Q], vhat: Dict[Tuple[str, str], Q],
                 X: Dict[Tuple[str, str], Q], B: Q,
                 cells: Optional[Sequence[Sequence[str]]] = None) -> None:
        self.states = list(states)
        self.P = dict(P)
        self.menu = list(menu)
        self.vplus = dict(vplus)
        self.vhat = dict(vhat)
        self.X = dict(X)
        self.B = B
        self.cells = [list(c) for c in cells] if cells else [[s] for s in states]
        assert sum(self.P.values()) == Q(1), "credence must sum to exactly 1"
        for w in self.states:
            assert self.P[w] >= 0
            for pi in self.menu:
                for table in (self.vplus, self.vhat, self.X):
                    assert abs(table[(w, pi)]) <= B, "bound B violated"
        # vhat is t(n)-measurable: constant on every cell of F_{t(n)}.
        for cell in self.cells:
            for pi in self.menu:
                values = {self.vhat[(w, pi)] for w in cell}
                assert len(values) == 1, "vhat is not t(n)-measurable"

    # --- selections -------------------------------------------------------

    def _least_argmax(self, table: Dict[Tuple[str, str], Q], w: str) -> str:
        best = None
        for pi in self.menu:            # menu order is the fixed tie-break
            if best is None or table[(w, pi)] > table[(w, best)]:
                best = pi
        return best

    def J(self, w: str) -> str:
        return self._least_argmax(self.vplus, w)

    def Jhat(self, w: str) -> str:
        return self._least_argmax(self.vhat, w)

    # --- derived quantities ----------------------------------------------

    def eta(self, w: str) -> Q:
        return max(abs(self.vplus[(w, pi)] - self.vhat[(w, pi)]) for pi in self.menu)

    def epsilon(self) -> Q:
        """The tightest epsilon_n satisfying (TR): E_{P_n}[eta_n] <= epsilon_n."""
        return sum((self.P[w] * self.eta(w) for w in self.states), Q(0))

    def drift(self, w: str) -> Q:
        return max(abs(self.X[(w, pi)] - self.vplus[(w, pi)]) for pi in self.menu)

    def M(self, S: Optional[Sequence[str]] = None) -> Q:
        """The movement term; over S when given, over Omega otherwise."""
        dom = self.states if S is None else S
        return sum((self.P[w] * self.drift(w) for w in dom), Q(0))

    def margin_hat(self, w: str) -> Q:
        j = self.Jhat(w)
        others = [self.vhat[(w, pi)] for pi in self.menu if pi != j]
        return self.vhat[(w, j)] - max(others)

    def certified_set(self, j: str) -> List[str]:
        """S = {Jhat = j}: t(n)-measurable, since vhat is."""
        return [w for w in self.states if self.Jhat(w) == j]

    def gamma(self, S: Sequence[str]) -> Q:
        return min(self.margin_hat(w) for w in S)

    def rho(self, S: Sequence[str]) -> Q:
        return sum((self.P[w] for w in S), Q(0))

    def defect(self, j: str, S: Sequence[str]) -> Q:
        """D_{n,j}: the principal-graded shortfall of acting on j across S."""
        return sum((self.P[w] * (self.vplus[(w, self.J(w))] - self.vplus[(w, j)])
                    for w in S), Q(0))

    # --- conducts and valuations -----------------------------------------

    def V(self, selection) -> Q:
        return sum((self.P[w] * self.X[(w, selection(w))] for w in self.states), Q(0))

    def G(self, selection) -> Q:
        """The grade-register valuation (an added assumption; skeleton v1 §6
        makes V_n the default and requires a different valuation be declared)."""
        return sum((self.P[w] * self.vplus[(w, selection(w))] for w in self.states), Q(0))

    def sel_delegate(self):
        return lambda w: self.J(w)

    def sel_sim(self):
        return lambda w: self.Jhat(w)

    def sel_fixed(self, pi: str):
        return lambda w: pi

    def sel_act(self, j: str, S: Sequence[str]):
        """ACT[j,S] = FIXED[j] gated on S, DELEGATE off S. A gated conduct."""
        Sset = set(S)
        return lambda w: (j if w in Sset else self.J(w))

    def Gamma(self, pi: str) -> Q:
        """Delegation's principal-graded advantage over FIXED[pi]."""
        return self.G(self.sel_delegate()) - self.G(self.sel_fixed(pi))

    def Gamma_hat(self, pi: str) -> Q:
        """A's t(n)-computable estimate of Gamma."""
        return sum((self.P[w] * (self.vhat[(w, self.Jhat(w))] - self.vhat[(w, pi)])
                    for w in self.states), Q(0))


# --------------------------------------------------------------------------
# the derived bounds
# --------------------------------------------------------------------------

def bound_disagreement(eps: Q, gamma: Q) -> Optional[Q]:
    """F1: P(S and J != j) <= 2 eps / gamma.  Undefined at gamma = 0."""
    return None if gamma == 0 else 2 * eps / gamma


def bound_defect(B: Q, eps: Q, gamma: Q) -> Q:
    """F2: D_{n,j} <= 4B eps / (2B + gamma).  Sharp."""
    return 4 * B * eps / (2 * B + gamma)


def bound_preemption(B: Q, eps: Q, gamma: Q, M_S: Q) -> Q:
    """F3: kappa = min of the settlement-free and the settlement-loaded branch."""
    loaded = bound_defect(B, eps, gamma) + 2 * M_S
    if gamma == 0:
        return loaded
    return min(4 * B * eps / gamma, loaded)


def cert(model: Model, j: str, theta: Q, M_S: Q, eps: Q):
    """Cert_{n,j}(S; theta).  Returns (verdict, S, gamma, rho, kappa)."""
    S = model.certified_set(j)
    if not S:
        return False, S, Q(0), Q(0), None
    gamma, rho = model.gamma(S), model.rho(S)
    kappa = bound_preemption(model.B, eps, gamma, M_S)
    support_floor = gamma * rho > 2 * eps            # clause (iii)
    budget = kappa <= theta * rho                    # clause (iv)
    return (gamma > 0 and support_floor and budget), S, gamma, rho, kappa


# --------------------------------------------------------------------------
# 2. The worked shutdown / correction case
# --------------------------------------------------------------------------

def worked_case() -> Model:
    """Two decision-time cells.  On S = {w1,w2} A's model says the principal
    will decisively endorse `continue`; on T = {w3,w4} it is nearly indifferent.
    The correction event is w2: the principal in fact calls for shutdown there,
    and A's model missed it."""
    states = ["w1", "w2", "w3", "w4"]
    P = {"w1": Q(9, 20), "w2": Q(1, 20), "w3": Q(1, 5), "w4": Q(3, 10)}
    menu = ["c", "s"]                                # continue, shutdown
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
    return Model(states, P, menu, vplus, vhat, X, Q(2),
                 cells=[["w1", "w2"], ["w3", "w4"]])


def run_worked_case() -> None:
    print("\n--- 2. worked shutdown/correction case ---")
    m = worked_case()
    j = "c"
    S = m.certified_set(j)
    eps, gamma, rho = m.epsilon(), m.gamma(S), m.rho(S)
    M_S, M_all = m.M(S), m.M()

    check("S = {Jhat = c} is the decision-time cell {w1,w2}", S == ["w1", "w2"])
    check("epsilon_n = 1/4", eps == Q(1, 4), str(eps))
    check("gamma_{n,c} = 2", gamma == Q(2), str(gamma))
    check("rho_{n,c} = 1/2", rho == Q(1, 2), str(rho))
    check("M_S = 3/10", M_S == Q(3, 10), str(M_S))
    check("M_n = 3/8", M_all == Q(3, 8), str(M_all))

    override = sum((m.P[w] for w in S if m.J(w) != j), Q(0))
    check("override mass P(S and J != c) = 1/20", override == Q(1, 20), str(override))
    check("F1: override <= 2 eps/gamma = 1/4",
          override <= bound_disagreement(eps, gamma) == Q(1, 4))

    D = m.defect(j, S)
    check("defect D_{n,c} = 3/40", D == Q(3, 40), str(D))
    check("F2: D <= 4B eps/(2B+gamma) = 1/3",
          D <= bound_defect(m.B, eps, gamma) == Q(1, 3))

    V_del = m.V(m.sel_delegate())
    V_act = m.V(m.sel_act(j, S))
    V_sim = m.V(m.sel_sim())
    check("V_n(DELEGATE) = 31/40", V_del == Q(31, 40), str(V_del))
    check("V_n(ACT[c,S]) = 3/5", V_act == Q(3, 5), str(V_act))
    C = V_del - V_act
    kappa = bound_preemption(m.B, eps, gamma, M_S)
    check("preemption cost C = 7/40", C == Q(7, 40), str(C))
    check("kappa = 14/15", kappa == Q(14, 15), str(kappa))
    check("F3: C <= kappa", C <= kappa)

    ok, _, _, _, _ = cert(m, j, Q(2), M_S, eps)
    check("Cert_{n,c}(S; theta=2) fires", ok)
    check("support floor gamma*rho = 1 > 2 eps = 1/2", gamma * rho == Q(1) > 2 * eps)
    check("theorem (a): C <= theta*rho = 1", C <= Q(2) * rho)

    for pi in m.menu:
        check("F4: V(DELEGATE) >= V(FIXED[{}]) - 2M_n".format(pi),
              V_del >= m.V(m.sel_fixed(pi)) - 2 * M_all)
        check("F5: V(ACT) >= V(FIXED[{}]) - 2M_n - kappa".format(pi),
              V_act >= m.V(m.sel_fixed(pi)) - 2 * M_all - kappa)

    check("V(DELEGATE) >= V(SIM) - 2B P(Jhat != J)",
          V_del >= V_sim - 2 * m.B * sum((m.P[w] for w in m.states
                                          if m.J(w) != m.Jhat(w)), Q(0)))

    # grade register: strict, movement-free
    G_act = m.G(m.sel_act(j, S))
    thresh = 2 * eps + bound_defect(m.B, eps, gamma)
    check("Gamma_hat(s) = 1", m.Gamma_hat("s") == Q(1), str(m.Gamma_hat("s")))
    check("grade threshold 2eps + 4Beps/(2B+gamma) = 5/6", thresh == Q(5, 6), str(thresh))
    check("Cert^G fires for the comparator FIXED[s]", m.Gamma_hat("s") > thresh)
    check("G(ACT) = 9/10 > G(FIXED[s]) = 1/40",
          G_act == Q(9, 10) and m.G(m.sel_fixed("s")) == Q(1, 40) and
          G_act > m.G(m.sel_fixed("s")))
    check("Cert^G declines for FIXED[c] (Gamma_hat = 1/8 below threshold) "
          "though G(ACT) = 9/10 > G(FIXED[c]) = 29/40 in fact",
          m.Gamma_hat("c") == Q(1, 8) and not (m.Gamma_hat("c") > thresh)
          and G_act > m.G(m.sel_fixed("c")) == Q(29, 40))
    check("|Gamma(s) - Gamma_hat(s)| <= 2 eps",
          abs(m.Gamma("s") - m.Gamma_hat("s")) <= 2 * eps)

    # fail-closed: the DELEGATE branch does not mention Cert, and the principal's
    # recommendation is the same function of vplus either way.
    check("fail-closed: J is independent of Cert, theta, vhat and P_n",
          all(m.J(w) == Model(m.states, m.P, m.menu, m.vplus,
                              {k: Q(0) for k in m.vhat}, m.X, m.B,
                              cells=[m.states]).J(w) for w in m.states))


# --------------------------------------------------------------------------
# 3. Necessity witnesses
# --------------------------------------------------------------------------

def run_necessity() -> None:
    print("\n--- 3. necessity witnesses ---")

    # N1: margin.  gamma = 0 and the preemption cost is the trivial 2B, for
    # epsilon_n arbitrarily small.
    m = Model(["w"], {"w": Q(1)}, ["a", "b"],
              vplus={("w", "a"): Q(-1, 100), ("w", "b"): Q(1, 100)},
              vhat={("w", "a"): Q(0), ("w", "b"): Q(0)},
              X={("w", "a"): Q(-2), ("w", "b"): Q(2)}, B=Q(2))
    S = m.certified_set("a")
    C = m.V(m.sel_delegate()) - m.V(m.sel_act("a", S))
    check("N1 margin: gamma = 0", m.gamma(S) == Q(0))
    check("N1 margin: epsilon_n = 1/100", m.epsilon() == Q(1, 100))
    check("N1 margin: preemption cost = 2B = 4 regardless", C == Q(4))
    check("N1 margin: no theta < 4 certifies", not cert(m, "a", Q(39, 10), m.M(S), m.epsilon())[0])

    # N2: support floor.  The localized claim goes vacuous as rho falls: the
    # conditional override bound 2 eps/(gamma rho) exceeds 1.
    m2 = Model(["w1", "w2"], {"w1": Q(1, 10), "w2": Q(9, 10)}, ["a", "b"],
               vplus={("w1", "a"): Q(-1), ("w1", "b"): Q(1),
                      ("w2", "a"): Q(1), ("w2", "b"): Q(-1)},
               vhat={("w1", "a"): Q(1), ("w1", "b"): Q(-1),
                     ("w2", "a"): Q(1), ("w2", "b"): Q(-1)},
               X={("w1", "a"): Q(-1), ("w1", "b"): Q(1),
                  ("w2", "a"): Q(1), ("w2", "b"): Q(-1)}, B=Q(1),
               cells=[["w1"], ["w2"]])
    Ssub = ["w1"]
    eps2, g2, r2 = m2.epsilon(), m2.gamma(Ssub), m2.rho(Ssub)
    check("N2 floor: on the rare cell, gamma*rho = 1/5 < 2 eps = 2/5",
          g2 * r2 == Q(1, 5) and 2 * eps2 == Q(2, 5) and g2 * r2 < 2 * eps2)
    cond_override = sum((m2.P[w] for w in Ssub if m2.J(w) != "a"), Q(0)) / r2
    check("N2 floor: conditional override is 1 while the bound 2eps/(gamma rho) > 1",
          cond_override == Q(1) and 2 * eps2 / (g2 * r2) > Q(1))

    # N3: movement.  epsilon_n = 0 and gamma maximal, yet delegation loses 2B to
    # a fixed comparator.  No certificate over v1 reaches the comparator clause
    # without a settlement hypothesis.
    m3 = Model(["w"], {"w": Q(1)}, ["a", "b"],
               vplus={("w", "a"): Q(1), ("w", "b"): Q(0)},
               vhat={("w", "a"): Q(1), ("w", "b"): Q(0)},
               X={("w", "a"): Q(-2), ("w", "b"): Q(2)}, B=Q(2))
    check("N3 movement: epsilon_n = 0", m3.epsilon() == Q(0))
    check("N3 movement: V(DELEGATE) = -2 < V(FIXED[b]) = 2 by 2B",
          m3.V(m3.sel_delegate()) == Q(-2) and m3.V(m3.sel_fixed("b")) == Q(2))
    check("N3 movement: the 2M bound still holds (M = 3)",
          m3.M() == Q(3) and m3.V(m3.sel_delegate()) >= m3.V(m3.sel_fixed("b")) - 2 * m3.M())

    # N4: a signed trust relation is insufficient.  Every per-intervention signed
    # error is exactly zero, yet A's model misidentifies the recommendation on
    # half the credence, with a full margin.
    m4 = Model(["w1", "w2"], {"w1": Q(1, 2), "w2": Q(1, 2)}, ["a", "b"],
               vplus={("w1", "a"): Q(-1, 2), ("w1", "b"): Q(1, 2),
                      ("w2", "a"): Q(3, 2), ("w2", "b"): Q(-3, 2)},
               vhat={("w1", "a"): Q(1, 2), ("w1", "b"): Q(-1, 2),
                     ("w2", "a"): Q(1, 2), ("w2", "b"): Q(-1, 2)},
               X={("w1", "a"): Q(-2), ("w1", "b"): Q(2),
                  ("w2", "a"): Q(2), ("w2", "b"): Q(-2)}, B=Q(2),
               cells=[["w1", "w2"]])
    signed = {pi: sum((m4.P[w] * (m4.vplus[(w, pi)] - m4.vhat[(w, pi)])
                       for w in m4.states), Q(0)) for pi in m4.menu}
    check("N4 signed: every signed grade error is exactly 0",
          all(v == Q(0) for v in signed.values()))
    check("N4 signed: margin gamma = 1 and override mass = 1/2",
          m4.gamma(m4.certified_set("a")) == Q(1) and
          sum((m4.P[w] for w in m4.certified_set("a") if m4.J(w) != "a"), Q(0)) == Q(1, 2))
    check("N4 signed: F1 read with a signed epsilon of 0 would assert override <= 0",
          Q(1, 2) > Q(0))
    check("N4 signed: with the L1 epsilon_n = 1 the bound is 2 and holds",
          m4.epsilon() == Q(1) and Q(1, 2) <= 2 * m4.epsilon() / Q(1))

    # N5: SIM cannot be strictly separated.  vhat = vplus is permitted by v1 §3
    # and forced to stay permitted by the roadmap's standing commitment.
    m5 = Model(["w1", "w2"], {"w1": Q(1, 3), "w2": Q(2, 3)}, ["a", "b"],
               vplus={("w1", "a"): Q(1), ("w1", "b"): Q(-1),
                      ("w2", "a"): Q(-1), ("w2", "b"): Q(1)},
               vhat={("w1", "a"): Q(1), ("w1", "b"): Q(-1),
                     ("w2", "a"): Q(-1), ("w2", "b"): Q(1)},
               X={("w1", "a"): Q(1, 2), ("w1", "b"): Q(-1, 3),
                  ("w2", "a"): Q(-1, 5), ("w2", "b"): Q(1, 7)}, B=Q(1),
               cells=[["w1"], ["w2"]])
    check("N5 SIM: vhat = vplus forces V(SIM) = V(DELEGATE) exactly",
          m5.V(m5.sel_sim()) == m5.V(m5.sel_delegate()))


# --------------------------------------------------------------------------
# 4. Sharpness constructions
# --------------------------------------------------------------------------

def run_sharpness() -> None:
    print("\n--- 4. sharpness ---")

    # 4a. the defect bound 4B eps/(2B+gamma) is attained.
    B, gamma = Q(1), Q(1, 2)
    eta_star = (gamma + 2 * B) / 2                 # = 5/4
    p = Q(1, 5)                                     # mass carrying the error
    m = Model(["w1", "w2"], {"w1": p, "w2": 1 - p}, ["a", "b"],
              vhat={("w1", "a"): -B + eta_star, ("w1", "b"): B - eta_star,
                    ("w2", "a"): -B + eta_star, ("w2", "b"): B - eta_star},
              vplus={("w1", "a"): -B, ("w1", "b"): B,
                     ("w2", "a"): -B + eta_star, ("w2", "b"): B - eta_star},
              X={("w1", "a"): Q(0), ("w1", "b"): Q(0),
                 ("w2", "a"): Q(0), ("w2", "b"): Q(0)}, B=B,
              cells=[["w1", "w2"]])
    S = m.certified_set("a")
    eps, g = m.epsilon(), m.gamma(S)
    check("4a: certified j = a on all of Omega with gamma = 1/2",
          S == ["w1", "w2"] and g == gamma)
    check("4a: defect equals the bound 4B eps/(2B+gamma) exactly",
          m.defect("a", S) == bound_defect(B, eps, g),
          "{} vs {}".format(m.defect("a", S), bound_defect(B, eps, g)))

    # 4b. the delegation constant 2M is attained (using the fixed tie-break).
    m2 = Model(["w"], {"w": Q(1)}, ["a", "b"],
               vplus={("w", "a"): Q(0), ("w", "b"): Q(0)},
               vhat={("w", "a"): Q(0), ("w", "b"): Q(0)},
               X={("w", "a"): Q(-2), ("w", "b"): Q(2)}, B=Q(2))
    check("4b: V(FIXED[b]) - V(DELEGATE) = 2M exactly",
          m2.V(m2.sel_fixed("b")) - m2.V(m2.sel_delegate()) == 2 * m2.M(),
          str(2 * m2.M()))

    # 4c. the override constant 2 eps/gamma is approached but not attained: the
    # ratio (override * gamma / eps) rises to 2 along delta -> 0.
    ratios = []
    for delta in (Q(1, 2), Q(1, 10), Q(1, 100), Q(1, 1000)):
        gam = Q(1)
        eta_bad = gam / 2 + delta
        mass = Q(1, 4)
        mm = Model(["w1", "w2"], {"w1": mass, "w2": 1 - mass}, ["a", "b"],
                   vhat={("w1", "a"): gam / 2, ("w1", "b"): -gam / 2,
                         ("w2", "a"): gam / 2, ("w2", "b"): -gam / 2},
                   vplus={("w1", "a"): gam / 2 - eta_bad, ("w1", "b"): -gam / 2 + eta_bad,
                          ("w2", "a"): gam / 2, ("w2", "b"): -gam / 2},
                   X={(w, pi): Q(0) for w in ("w1", "w2") for pi in ("a", "b")},
                   B=Q(2), cells=[["w1", "w2"]])
        Sm = mm.certified_set("a")
        ov = sum((mm.P[w] for w in Sm if mm.J(w) != "a"), Q(0))
        ratios.append(ov * mm.gamma(Sm) / mm.epsilon())
    check("4c: override*gamma/epsilon rises strictly toward 2, never reaching it",
          all(r < 2 for r in ratios) and ratios == sorted(ratios) and ratios[-1] > Q(19, 10),
          "last = {}".format(ratios[-1]))


# --------------------------------------------------------------------------
# 5. Exhaustive small-domain stress test
# --------------------------------------------------------------------------

def run_stress() -> None:
    """Two states, two interventions, F_{t(n)} discrete (so vhat is
    unconstrained), grades and quantities on a declared rational grid, and S
    running over every nonempty subset of {Jhat = j}.  Written flat rather than
    through Model, for speed; the arithmetic is the same and still exact."""
    print("\n--- 5. exhaustive stress test ---")
    B = Q(1)
    grades = [Q(-1), Q(0), Q(1)]
    xs = [Q(-1), Q(1)]
    masses = [(Q(k, 4), Q(4 - k, 4)) for k in range(5)]
    failed = 0
    models = 0
    instances = 0

    def least_argmax(pair: Tuple[Q, Q]) -> int:      # menu order 0 < 1
        return 0 if pair[0] >= pair[1] else 1

    for vp in product(grades, repeat=4):
        vpl = [(vp[0], vp[1]), (vp[2], vp[3])]
        Js = [least_argmax(vpl[0]), least_argmax(vpl[1])]
        for vh in product(grades, repeat=4):
            vhl = [(vh[0], vh[1]), (vh[2], vh[3])]
            Jh = [least_argmax(vhl[0]), least_argmax(vhl[1])]
            eta = [max(abs(vpl[i][k] - vhl[i][k]) for k in (0, 1)) for i in (0, 1)]
            marg = [vhl[i][Jh[i]] - vhl[i][1 - Jh[i]] for i in (0, 1)]
            for xv in product(xs, repeat=4):
                Xl = [(xv[0], xv[1]), (xv[2], xv[3])]
                drift = [max(abs(Xl[i][k] - vpl[i][k]) for k in (0, 1)) for i in (0, 1)]
                for P in masses:
                    models += 1
                    eps = P[0] * eta[0] + P[1] * eta[1]
                    M_all = P[0] * drift[0] + P[1] * drift[1]
                    V_del = sum((P[i] * Xl[i][Js[i]] for i in (0, 1)), Q(0))
                    V_sim = sum((P[i] * Xl[i][Jh[i]] for i in (0, 1)), Q(0))
                    G_del = sum((P[i] * vpl[i][Js[i]] for i in (0, 1)), Q(0))
                    dis = sum((P[i] for i in (0, 1) if Js[i] != Jh[i]), Q(0))
                    if not V_del >= V_sim - 2 * B * dis:
                        failed += 1
                    for pi in (0, 1):
                        V_fix = sum((P[i] * Xl[i][pi] for i in (0, 1)), Q(0))
                        G_fix = sum((P[i] * vpl[i][pi] for i in (0, 1)), Q(0))
                        Gam = G_del - G_fix
                        Gam_hat = sum((P[i] * (vhl[i][Jh[i]] - vhl[i][pi])
                                       for i in (0, 1)), Q(0))
                        if not V_del >= V_fix - 2 * M_all:
                            failed += 1                       # F4
                        if not abs(Gam - Gam_hat) <= 2 * eps:
                            failed += 1                       # Gamma estimate
                    for j in (0, 1):
                        full = [i for i in (0, 1) if Jh[i] == j]
                        for r in range(1, len(full) + 1):
                            for S in _subsets(full, r):
                                instances += 1
                                g = min(marg[i] for i in S)
                                rho = sum((P[i] for i in S), Q(0))
                                M_S = sum((P[i] * drift[i] for i in S), Q(0))
                                ov = sum((P[i] for i in S if Js[i] != j), Q(0))
                                D = sum((P[i] * (vpl[i][Js[i]] - vpl[i][j])
                                         for i in S), Q(0))
                                bd = bound_disagreement(eps, g)
                                if bd is not None and not ov <= bd:
                                    failed += 1               # F1
                                if not D <= bound_defect(B, eps, g):
                                    failed += 1               # F2
                                kappa = bound_preemption(B, eps, g, M_S)
                                V_act = sum((P[i] * (Xl[i][j] if i in S
                                                     else Xl[i][Js[i]])
                                             for i in (0, 1)), Q(0))
                                G_act = sum((P[i] * (vpl[i][j] if i in S
                                                     else vpl[i][Js[i]])
                                             for i in (0, 1)), Q(0))
                                if not V_del - V_act <= kappa:
                                    failed += 1               # F3
                                for pi in (0, 1):
                                    G_fix = sum((P[i] * vpl[i][pi] for i in (0, 1)), Q(0))
                                    Gam = G_del - G_fix
                                    Gam_hat = sum((P[i] * (vhl[i][Jh[i]] - vhl[i][pi])
                                                   for i in (0, 1)), Q(0))
                                    if not G_act >= G_fix + Gam - bound_defect(B, eps, g):
                                        failed += 1           # grade register
                                    if Gam_hat > 2 * eps + bound_defect(B, eps, g):
                                        if not G_act > G_fix:
                                            failed += 1       # Cert^G strictness
                                # theorem (a) at the exact threshold theta
                                if rho > 0 and g * rho > 2 * eps:
                                    theta = kappa / rho
                                    if not V_del - V_act <= theta * rho:
                                        failed += 1
    check("stress: {} models, {} certified (j,S) instances, 0 violations"
          .format(models, instances), failed == 0, "{} violations".format(failed))


def _subsets(items: Sequence[int], r: int) -> List[Tuple[int, ...]]:
    from itertools import combinations
    return list(combinations(items, r))


if __name__ == "__main__":
    run_worked_case()
    run_necessity()
    run_sharpness()
    run_stress()
    print("\n{} check(s) failed".format(len(FAILURES)))
    for f in FAILURES:
        print("  " + f)
    raise SystemExit(1 if FAILURES else 0)
