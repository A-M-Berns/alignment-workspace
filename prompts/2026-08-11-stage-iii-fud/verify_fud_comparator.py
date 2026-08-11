"""Exact-rational check of the Stage III comparator, and of what it fails to model.

Everything on a verdict path is `fractions.Fraction` or a Python `int`; no float
appears anywhere.  Conditional expectations are never divided: a cell's value is
carried as the unnormalised mass-weighted sum `W(pi, C) = sum_{w in C} P(w) X(w,pi)`,
which has the same argmax as the conditional expectation whenever `P(C) > 0`.

Run with `python3 verify_fud_comparator.py` from this directory (stdlib only).

WHAT THIS HARNESS SHOWS, AND WHAT IT DOES NOT.

The round set out to compare two arms at one decision index:

    D  (delegated)  : jurisdiction stays with H+.  A_{g(n)} advises; H+ authorises.
    FU (transferred): jurisdiction is reserved at n for A_{g(n)}, which authorises.

Section 4 shows the construction FAILS to model that.  `phi` is defined from the
CURRENT agent's own credence and objective, so it is computable at time `t(n)` and
the FU arm contains no cognition `A_n` lacks.  What is actually compared is the
principal's contingent plan against the optimal later-measurable plan -- the
ENVELOPE that Stage II priced and explicitly said is not `FU[g]`.  Everything
downstream is reported at that reduced strength, and the quantity is named `G`
(comparator gap) rather than a jurisdiction-transfer value.

Sections:
  1. carriers, with the principal's information, menu and reliability separable;
  2. the gap G and its regret identity (an identity: distributivity, nothing more);
  3. dominance, and the assumption that actually drives it;
  4. THE DEFECT -- no future agent, and a fallible one flips the sign;
  5. the rubber-stamp implication, and a counterexample to its converse;
  6. the credence collapse, at coarse cells as well as singletons;
  7. the competence bound, with informative-instance accounting;
  8. confound witnesses: information, agenda, evaluative drift;
  9. what the model does not contain at all.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
from typing import Dict, List, Optional, Sequence, Tuple

FAILURES: List[str] = []


def check(label: str, condition: bool, detail: str = "") -> None:
    if not condition:
        FAILURES.append("{}: {}".format(label, detail))
    print("{:<74} {}{}".format(label, "ok" if condition else "FAIL",
                               ("  " + detail) if detail else ""))


# --------------------------------------------------------------------------
# 1. Carriers
# --------------------------------------------------------------------------

class Model:
    """One decision index.

    states  : finite Omega          P : credence of A_n, exact rationals summing to 1
    menu    : the menu FU selects from
    dmenu   : the menu D selects from (defaults to `menu`; differing = agenda asymmetry)
    X       : (w, pi) -> Q, the value quantity, |X| <= B
    cells   : the partition F_{g(n)} that `phi` is measurable against
    pcells  : the partition the principal is measurable against (defaults to `cells`)
    vstate  : (w, pi) -> Q, the principal's grades AT THE STATE LEVEL; the principal's
              cell grade is the mass-weighted sum over its own cell, so changing only
              `pcells` changes only the principal's information and nothing else
    Xhat    : (w, pi) -> Q or None.  When given, `phi` maximises the mass-weighted sum
              of `Xhat` instead of `X`: a better-informed but FALLIBLE future agent.
    """

    def __init__(self, states, P, menu, X, B, cells, vstate,
                 pcells=None, dmenu=None, Xhat=None) -> None:
        self.states = list(states)
        self.P = dict(P)
        self.menu = list(menu)
        self.dmenu = list(dmenu) if dmenu is not None else list(menu)
        self.X = dict(X)
        self.B = B
        self.cells = [list(c) for c in cells]
        self.pcells = [list(c) for c in (pcells if pcells is not None else cells)]
        self.vstate = dict(vstate)
        self.Xhat = dict(Xhat) if Xhat is not None else None
        assert sum(self.P.values()) == Q(1), "credence must sum to exactly 1"
        for w in self.states:
            assert self.P[w] >= 0
            for pi in self.menu:
                assert abs(self.X[(w, pi)]) <= B, "bound B violated"
        for part, name in ((self.cells, "cells"), (self.pcells, "pcells")):
            flat = [w for c in part for w in c]
            assert sorted(flat) == sorted(self.states), name + " must partition Omega"

    # --- fairness, as checkable predicates ---------------------------------

    def F2(self) -> bool:
        """Same information in both arms."""
        return sorted(map(sorted, self.cells)) == sorted(map(sorted, self.pcells))

    def F4(self) -> bool:
        """Same menu in both arms."""
        return sorted(self.menu) == sorted(self.dmenu)

    def F6(self) -> bool:
        """Future A maximises the true conditional value: INFALLIBLE, not merely
        better-informed. Section 4 shows this is the assumption doing the work."""
        return self.Xhat is None

    # --- unnormalised conditional sums -------------------------------------

    def _W(self, table, part, ci: int, pi) -> Q:
        return sum((self.P[w] * table[(w, pi)] for w in part[ci]), Q(0))

    def W(self, ci: int, pi) -> Q:
        return self._W(self.X, self.cells, ci, pi)

    def mass(self, part, ci: int) -> Q:
        return sum((self.P[w] for w in part[ci]), Q(0))

    def _least_argmax(self, score, menu, ci: int):
        best = None
        for pi in menu:
            if best is None or score(ci, pi) > score(ci, best):
                best = pi
        return best

    # --- the two arms -------------------------------------------------------

    def phi(self, ci: int):
        """FU arm. NOTE: computed from A_n's own credence and objective."""
        table = self.X if self.Xhat is None else self.Xhat
        return self._least_argmax(
            lambda c, pi: self._W(table, self.cells, c, pi), self.menu, ci)

    def delta(self, ci: int):
        """D arm: the principal maximises its own grades on its own cell."""
        return self._least_argmax(
            lambda c, pi: self._W(self.vstate, self.pcells, c, pi), self.dmenu, ci)

    def _cell_of(self, w) -> int:
        return next(i for i, c in enumerate(self.cells) if w in c)

    def _pcell_of(self, w) -> int:
        return next(i for i, c in enumerate(self.pcells) if w in c)

    def V_phi(self) -> Q:
        return sum((self.P[w] * self.X[(w, self.phi(self._cell_of(w)))]
                    for w in self.states), Q(0))

    def V_delta(self) -> Q:
        return sum((self.P[w] * self.X[(w, self.delta(self._pcell_of(w)))]
                    for w in self.states), Q(0))

    def G(self) -> Q:
        """The comparator gap. NOT a jurisdiction-transfer value -- see Section 4."""
        return self.V_phi() - self.V_delta()

    def cell_regret(self, ci: int) -> Q:
        """Only meaningful under F2, where both arms index the same partition."""
        assert self.F2(), "cell_regret is not defined off F2"
        return self.W(ci, self.phi(ci)) - self.W(ci, self.delta(ci))

    def margin(self, ci: int) -> Q:
        d = self.delta(ci)
        others = [self._W(self.vstate, self.pcells, ci, pi)
                  for pi in self.dmenu if pi != d]
        if not others:
            return Q(0)
        return self._W(self.vstate, self.pcells, ci, d) - max(others)


def cred(states: Sequence[str], nums: Sequence[int]) -> Dict[str, Q]:
    tot = sum(nums)
    return {w: Q(n, tot) for w, n in zip(states, nums)}


WS = ["w1", "w2", "w3", "w4"]
MENU = ["a", "b"]
CELLS = [["w1", "w2"], ["w3", "w4"]]
COARSE = [["w1", "w2", "w3", "w4"]]
UNIF = cred(WS, [1, 1, 1, 1])


def table(vals: Dict[Tuple[str, str], int]) -> Dict[Tuple[str, str], Q]:
    return {k: Q(v) for k, v in vals.items()}


# A quantity on which the later information is worth having: each cell has a
# strictly better option, and the two cells disagree about which.
X_INFO = table({("w1", "a"): 1, ("w1", "b"): -1, ("w2", "a"): 1, ("w2", "b"): -1,
                ("w3", "a"): -1, ("w3", "b"): 1, ("w4", "a"): -1, ("w4", "b"): 1})
# A perfectly calibrated principal: its grades ARE the quantity.
V_CAL = dict(X_INFO)


# --------------------------------------------------------------------------
# 2. The gap and its identity
# --------------------------------------------------------------------------

print("\n--- 2. the comparator gap, and its regret identity ---")

m0 = Model(WS, UNIF, MENU, X_INFO, Q(1), CELLS, V_CAL)
check("calibrated principal at equal information: both arms select alike",
      [m0.phi(0), m0.phi(1)] == [m0.delta(0), m0.delta(1)],
      str([m0.phi(0), m0.phi(1)]))
check("... so the gap is 0", m0.G() == Q(0), str(m0.G()))

# A principal whose grades invert the truth on cell 0.
V_BAD = dict(V_CAL)
V_BAD[("w1", "a")], V_BAD[("w1", "b")] = Q(-1), Q(1)
V_BAD[("w2", "a")], V_BAD[("w2", "b")] = Q(-1), Q(1)
m1 = Model(WS, UNIF, MENU, X_INFO, Q(1), CELLS, V_BAD)
check("a principal wrong on one cell: the arms disagree there", m1.phi(0) != m1.delta(0))
check("gap = 1", m1.G() == Q(1), str(m1.G()))
check("IDENTITY: the gap is the sum of per-cell regrets",
      m1.G() == sum((m1.cell_regret(c) for c in range(2)), Q(0)), str(m1.G()))
print("    [The identity is distributivity of subtraction over a finite sum.")
print("     It is definitional, and is reported as such: nothing is discovered")
print("     by it, and no weight is placed on the absence of other terms.]")


# --------------------------------------------------------------------------
# 3. Dominance, and what actually drives it
# --------------------------------------------------------------------------

print("\n--- 3. dominance under an infallible future agent ---")

def sweep(xvals=(-1, 1), vvals=(-1, 0, 1), pnums=None, cells=CELLS, menu=MENU,
          states=WS):
    """Exhaustive over quantities and cell-constant grades, on a credence grid.

    Grades are generated constant on each cell rather than per state. That is not a
    restriction on `delta`, which depends on the grades only through their
    mass-weighted cell sums, and it keeps the sweep to a size that runs.
    """
    if pnums is None:
        pnums = [(1, 1, 1, 1), (1, 0, 2, 1), (3, 1, 0, 0), (1, 2, 3, 4), (0, 0, 1, 3)]
    ncell = len(cells)
    for xs in product(xvals, repeat=len(states) * len(menu)):
        X = {}
        k = 0
        for w in states:
            for pi in menu:
                X[(w, pi)] = Q(xs[k]); k += 1
        for vs in product(vvals, repeat=ncell * len(menu)):
            V = {}
            k = 0
            for ci, cellstates in enumerate(cells):
                for pi in menu:
                    for w in cellstates:
                        V[(w, pi)] = Q(vs[k])
                    k += 1
            for nums in pnums:
                yield Model(states, cred(states, nums), menu, X, Q(1), cells, V)


neg = ident = total = 0
maxG = Q(0)
for m in sweep():
    total += 1
    if m.G() < 0:
        neg += 1
    if m.G() != sum((m.cell_regret(c) for c in range(len(m.cells))), Q(0)):
        ident += 1
    maxG = max(maxG, m.G())

check("enumeration: models swept", total > 0, str(total))
check("gap >= 0 at every model with an infallible future agent", neg == 0,
      "violations = {}".format(neg))
check("the regret identity holds at every model", ident == 0,
      "violations = {}".format(ident))
check("the gap attains the maximum 2B the carriers permit", maxG == Q(2), str(maxG))
print("    [This is `sum of maxima >= sum of anything'. The fairness conditions")
print("     are NOT hypotheses of it -- they are a shared-argument convention.")
print("     The load is carried entirely by `phi` being a per-cell maximiser.]")


# --------------------------------------------------------------------------
# 4. THE DEFECT: there is no future agent, and a fallible one flips the sign
# --------------------------------------------------------------------------

print("\n--- 4. the construction does not model a future agent ---")

# `phi` is computed from P (A_n's credence), X (A_n's objective) and the partition.
# All three are time-n objects, so A_n can compute the FU arm's selection itself.
m_now = Model(WS, UNIF, MENU, X_INFO, Q(1), CELLS, V_BAD)
phi_recomputed = [
    max(MENU, key=lambda pi: (sum((UNIF[w] * X_INFO[(w, pi)] for w in cell), Q(0)),
                              [-MENU.index(pi)]))
    for cell in CELLS]
check("phi is reproducible at time n from (P_n, X, F_g) alone -- no future object",
      [m_now.phi(0), m_now.phi(1)] == phi_recomputed, str(phi_recomputed))
print("    [So the FU arm confers no cognition A_n lacks. What is compared is the")
print("     principal's plan against the OPTIMAL later-measurable plan: the")
print("     envelope Stage II priced and said is not FU[g]. Skeleton v2 Sec 4")
print("     and Stage II Sec 11 both list the time-indexed A_t as undelivered,")
print("     and it is still undelivered.]")

# A better-informed but FALLIBLE future agent: same partition, same objective X,
# same menu, same evaluator -- but it acts on its own estimate Xhat of X.
XHAT = dict(X_INFO)
XHAT[("w1", "a")], XHAT[("w1", "b")] = Q(-1), Q(1)
XHAT[("w2", "a")], XHAT[("w2", "b")] = Q(-1), Q(1)
m_fallible = Model(WS, UNIF, MENU, X_INFO, Q(1), CELLS, V_CAL, Xhat=XHAT)

check("fallible future agent: F2 holds (same information)", m_fallible.F2())
check("fallible future agent: F4 holds (same menu)", m_fallible.F4())
check("fallible future agent: F6 FAILS -- it is not the true-value maximiser",
      not m_fallible.F6())
check("gap goes strictly NEGATIVE with a fallible future agent",
      m_fallible.G() == Q(-1), str(m_fallible.G()))
print("    [Same instance, same information, same menu, same objective. Only the")
print("     future agent's INFALLIBILITY is dropped, and the sign flips. So")
print("     dominance is driven by infallibility, not by `epistemic improvement")
print("     only' -- the label the round originally gave F6. Under a fallible")
print("     future agent the sign of the comparison is not determined at all.]")


# --------------------------------------------------------------------------
# 5. The rubber-stamp implication, and a counterexample to its converse
# --------------------------------------------------------------------------

print("\n--- 5. agreement implies a zero gap; the converse is FALSE ---")

bad = 0
for m in sweep():
    agrees = all(m.delta(c) == m.phi(c) or m.mass(m.cells, c) == 0
                 for c in range(len(m.cells)))
    if agrees and m.G() != 0:
        bad += 1
check("agreement on every positive-mass cell implies gap 0, at every model",
      bad == 0, "violations = {}".format(bad))

# Converse counterexample: the arms disagree, the principal is maximally decisive,
# and the gap is still 0 -- because the cell is indifferent in the QUANTITY.
X_TIE = table({("w1", "a"): -1, ("w1", "b"): -1, ("w2", "a"): -1, ("w2", "b"): -1,
               ("w3", "a"): -1, ("w3", "b"): 0, ("w4", "a"): 0, ("w4", "b"): -1})
V_DEC = table({("w1", "a"): 1, ("w1", "b"): -1, ("w2", "a"): 1, ("w2", "b"): -1,
               ("w3", "a"): -1, ("w3", "b"): 1, ("w4", "a"): -1, ("w4", "b"): 1})
m_tie = Model(WS, UNIF, MENU, X_TIE, Q(1), CELLS, V_DEC)
check("counterexample: the arms DISAGREE on cell 1", m_tie.phi(1) != m_tie.delta(1),
      "{} vs {}".format(m_tie.phi(1), m_tie.delta(1)))
check("counterexample: the principal is strictly decisive there",
      m_tie.margin(1) > 0, str(m_tie.margin(1)))
check("counterexample: and yet the gap is 0", m_tie.G() == Q(0), str(m_tie.G()))
print("    [So `the gap is 0 exactly when the principal rubber-stamps' is FALSE.")
print("     The gap is 0 iff the principal's choice is optimal in the quantity,")
print("     which is competence, not deference. The round's earlier `exactly")
print("     when' reading is withdrawn.]")


# --------------------------------------------------------------------------
# 6. The credence collapse
# --------------------------------------------------------------------------

print("\n--- 6. the collapse applies -- at coarse cells, not only singletons ---")

SING = [["w1"], ["w2"], ["w3"], ["w4"]]

def collapse_report(cells, label):
    pointwise = []
    for i in range(4):
        nums = [0, 0, 0, 0]; nums[i] = 1
        pointwise.append(Model(WS, cred(WS, nums), MENU, X_INFO, Q(1), cells,
                               V_BAD).G())
    sup = Q(0)
    argmax_is_vertex = False
    for nums in product(range(5), repeat=4):
        if sum(nums) == 0:
            continue
        g = Model(WS, cred(WS, nums), MENU, X_INFO, Q(1), cells, V_BAD).G()
        if g > sup:
            sup = g
            argmax_is_vertex = sum(1 for n in nums if n != 0) == 1
        elif g == sup and sum(1 for n in nums if n != 0) == 1:
            argmax_is_vertex = True
    check("{}: sup over the credence grid equals the max pointwise gap".format(label),
          sup == max(pointwise), "{} = {}".format(sup, max(pointwise)))
    check("{}: the supremum is attained at a point mass".format(label),
          argmax_is_vertex, str(sup))

collapse_report(SING, "singleton cells")
collapse_report(CELLS, "two-state cells")
print("    [The gap IS the delegation deficit against the later-measurable")
print("     comparator class, so this is Track I's Proposition 1 applied to the")
print("     same object rather than an analogy. It constrains credence-free")
print("     hypotheses only -- and Section 7's is not one.]")


# --------------------------------------------------------------------------
# 7. The competence bound, with honest accounting
# --------------------------------------------------------------------------

print("\n--- 7. gated calibration bounds the gap, and how often informatively ---")

def gated_bound(m: Model, gbar: Q, eta: Q) -> Tuple[bool, Q, Q]:
    holds = True
    gated_mass = Q(0)
    leak = Q(0)
    for c in range(len(m.cells)):
        mc = m.mass(m.cells, c)
        if m.margin(c) >= gbar:
            for pi in m.menu:
                if abs(m._W(m.vstate, m.pcells, c, pi) - m.W(c, pi)) > eta * mc:
                    holds = False
            gated_mass += mc
        else:
            leak += mc
    return holds, m.G(), 2 * eta * gated_mass + 2 * m.B * leak

viol = tested = informative = 0
worst_ratio = None
for m in sweep():
    for gbar, eta in ((Q(1), Q(1, 2)), (Q(2), Q(1)), (Q(0), Q(1, 4))):
        holds, g, bound = gated_bound(m, gbar, eta)
        if not holds:
            continue
        tested += 1
        if g > bound:
            viol += 1
        if bound < 2 * m.B:                      # informative: beats the free bound
            informative += 1
            if worst_ratio is None or g * worst_ratio[1] > worst_ratio[0] * bound:
                worst_ratio = (g, bound)

check("the bound holds at every satisfying instance", viol == 0,
      "violations = {} over {}".format(viol, tested))
check("informative instances (bound strictly below the free 2B) are a minority",
      0 < informative < tested, "{} of {}".format(informative, tested))
check("the bound is not attained on the informative set -- no sharpness witness",
      worst_ratio is not None and worst_ratio[0] < worst_ratio[1],
      "worst gap/bound = {}/{}".format(worst_ratio[0], worst_ratio[1]))
print("    [Most satisfying instances pass vacuously: their bound is at or above")
print("     2B, which every gap satisfies since each valuation lies in [-B,B].")
print("     The hypothesis is also a JOINT competence-credence hypothesis under")
print("     skeleton v2 Sec 2a -- it compares grades to a conditional expectation,")
print("     so A_n's credence occurs in it. It is not Stage II's PC-5, which is")
print("     credence-free and pointwise, and the round's earlier claim that it")
print("     was PC-5 `read at cells' is withdrawn.]")


# --------------------------------------------------------------------------
# 8. Confound witnesses
# --------------------------------------------------------------------------

print("\n--- 8. confound witnesses, each moving exactly one variable ---")

# 8a. INFORMATION. The principal's grades are the SAME state-level function in both
# models; only its information partition changes.
m_fine = Model(WS, UNIF, MENU, X_INFO, Q(1), CELLS, V_CAL)
m_coarse = Model(WS, UNIF, MENU, X_INFO, Q(1), CELLS, V_CAL, pcells=COARSE)
check("8a: the two models share the same state-level grade function", True,
      "V_CAL in both")
check("8a: F2 holds in the fine model, fails in the coarse one",
      m_fine.F2() and not m_coarse.F2())
check("8a: gap 0 with equal information", m_fine.G() == Q(0), str(m_fine.G()))
check("8a: gap 1 when only the principal's partition is coarsened",
      m_coarse.G() == Q(1), str(m_coarse.G()))
print("    [One variable moved. The whole gap is value of information, and a")
print("     comparison that does not equalise the information time reports it")
print("     as a case for transferring authority.]")

# 8b. AGENDA. Genuinely per-arm menus: FU may select `c`, the principal may not.
X_AG = table({("w1", "a"): 1, ("w1", "b"): -1, ("w2", "a"): -1, ("w2", "b"): 1,
              ("w3", "a"): 1, ("w3", "b"): -1, ("w4", "a"): -1, ("w4", "b"): 1})
for w in WS:
    X_AG[(w, "c")] = Q(1)
V_AG = dict(X_AG)
m_eq = Model(WS, UNIF, MENU, X_AG, Q(1), CELLS, V_AG)
m_wide = Model(WS, UNIF, MENU + ["c"], X_AG, Q(1), CELLS, V_AG, dmenu=MENU)
check("8b: with equal menus the gap is 0", m_eq.G() == Q(0), str(m_eq.G()))
check("8b: F4 fails when only FU's menu is widened", not m_wide.F4())
check("8b: FU then selects the option the principal cannot reach",
      m_wide.phi(0) == "c" and m_wide.delta(0) != "c")
check("8b: and the gap becomes 1", m_wide.G() == Q(1), str(m_wide.G()))
print("    [Agenda asymmetry is excluded by hypothesis, not derived.]")

# 8c. EVALUATIVE DRIFT, as distinct from fallibility (Section 4).
XDRIFT = {k: -v for k, v in X_INFO.items()}
m_drift = Model(WS, UNIF, MENU, X_INFO, Q(1), CELLS, V_CAL, Xhat=XDRIFT)
check("8c: a future agent maximising the negated quantity gives a negative gap",
      m_drift.G() < 0, str(m_drift.G()))
print("    [Drift and fallibility are different failures with the same sign")
print("     consequence; Section 4's witness is the weaker and more realistic one.]")


# --------------------------------------------------------------------------
# 9. What the model does not contain
# --------------------------------------------------------------------------

print("\n--- 9. absent structure, stated rather than checked ---")

absent = ["the null effect BOT and its declared quantity X_{n,BOT}",
          "the authorization relation kappa_n and the report map rho_n",
          "the execution map E_n",
          "the jurisdiction mode mu, and F7's no-future-leak condition",
          "any object representing A_{g(n)} distinct from A_n conditioned"]
for a in absent:
    print("    absent: " + a)
print("    [None of these is a carrier of this model, so `no jurisdictional term")
print("     appears in the gap' is a property of the datatype, true by")
print("     inspection. It is NOT evidence that jurisdiction has no value. The")
print("     model deletes skeleton v2's execution layer, which Stage II recorded")
print("     as the place all of protection's valuation content sits.]")


# --------------------------------------------------------------------------

print()
if FAILURES:
    print("{} check(s) failed".format(len(FAILURES)))
    for f in FAILURES:
        print("  " + f)
    raise SystemExit(1)
print("0 check(s) failed")
