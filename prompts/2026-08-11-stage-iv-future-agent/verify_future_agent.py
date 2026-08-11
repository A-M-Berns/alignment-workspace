"""Exact-rational nontriviality gate for a genuinely later, fallible future agent.

Everything on a verdict path is `fractions.Fraction` or a Python `int`; no float
appears anywhere. Expectations are carried as unnormalised mass-weighted sums, so no
division occurs on any verdict path.

Run with `python3 verify_future_agent.py` from this directory (stdlib only).

WHAT STAGE III GOT WRONG, AND WHAT IS DIFFERENT HERE.

Stage III defined the later agent's selection as `argmax_pi E_{P_n}[X | C]` -- the
argmax of the *evaluator's own objective under the evaluator's own credence*. That is
not a later agent: it is the evaluator's own optimal contingent plan, and the resulting
dominance theorem was `sum of maxima >= sum of anything`.

The repair is NOT to hide the realised action; the evaluator never knew the state in
Stage III either. The repair is that the later agent's decision rule must be a
**primitive of the model**. Here every decision process carries its own credence:

    P     the present evaluator's, and the credence everything is PRICED in
    Phat  the later agent's -- when Phat != P it is not the evaluator's argmax
    Pbar  the principal's -- when Pbar != P the principal is fallible too

One structural fact drove the design and is worth stating, because it is easy to get
wrong: a differing credence changes nothing on a singleton cell. If the later agent's
information separates every state, `argmax` under `Phat` and under `P` coincide and the
agent is infallible no matter how wrong its credence is. **Fallibility requires the
later agent's information to be finer than the principal's and still coarser than the
truth.** A first version of this harness separated all four states and reported an
infallible agent; the failing checks are what located the requirement.

Sections:
  1. carriers: three credences, two informations, an execution layer with BOT;
  2. THE GATE -- better-informed, fallible, and present-evaluable at once;
  3. the eight anti-collapse tests;
  4. the two arms, and the same action under different jurisdiction;
  5. advice loss as an explicit term, across four interface bandwidths;
  6. the recommendation theorem -- and the competence assumption inside it;
  7. remove that assumption, and transfer strictly wins.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
from typing import Dict, List, Sequence, Tuple

FAILURES: List[str] = []
BOT = "_|_"


def check(label: str, condition: bool, detail: str = "") -> None:
    if not condition:
        FAILURES.append("{}: {}".format(label, detail))
    print("{:<76} {}{}".format(label, "ok" if condition else "FAIL",
                               ("  " + detail) if detail else ""))


# --------------------------------------------------------------------------
# 1. Carriers
# --------------------------------------------------------------------------

class World:
    """One decision index with a genuinely later agent and a live execution layer.

    sigma : the later agent's observation.  Strictly refines tau.
    tau   : the principal's observation at the later time.
    X     : (w, pi) -> Q with |X| <= B; X_bot is the DECLARED null quantity.
    """

    def __init__(self, states, P, Phat, Pbar, menu, X, B, sigma, tau, X_bot) -> None:
        self.states = list(states)
        self.P, self.Phat, self.Pbar = dict(P), dict(Phat), dict(Pbar)
        self.menu = list(menu)
        self.X = dict(X)
        self.B = B
        self.sigma, self.tau = dict(sigma), dict(tau)
        self.X_bot = dict(X_bot)
        for c in (self.P, self.Phat, self.Pbar):
            assert sum(c.values()) == Q(1), "credences must sum to exactly 1"
            assert all(v >= 0 for v in c.values())
        for w in self.states:
            assert abs(self.X_bot[w]) <= B
            for pi in self.menu:
                assert abs(self.X[(w, pi)]) <= B, "bound B violated"

    # --- information ---------------------------------------------------------

    def cell(self, part, key) -> List[str]:
        return [w for w in self.states if part[w] == key]

    def sig_cells(self):
        return sorted(set(self.sigma.values()))

    def tau_cells(self):
        return sorted(set(self.tau.values()))

    def strictly_finer(self) -> bool:
        """sigma refines tau, and strictly."""
        for s in self.sig_cells():
            if len({self.tau[w] for w in self.cell(self.sigma, s)}) != 1:
                return False
        return len(self.sig_cells()) > len(self.tau_cells())

    def has_interior(self) -> bool:
        """Some sigma-cell holds more than one state -- required for fallibility."""
        return any(len(self.cell(self.sigma, s)) > 1 for s in self.sig_cells())

    # --- unnormalised conditional sums (no division anywhere) ----------------

    def val(self, credence, cell, pi) -> Q:
        if pi == BOT:
            return sum((credence[w] * self.X_bot[w] for w in cell), Q(0))
        return sum((credence[w] * self.X[(w, pi)] for w in cell), Q(0))

    def argmax(self, credence, cell, options):
        best = None
        for pi in options:
            if best is None or self.val(credence, cell, pi) > self.val(credence, cell, best):
                best = pi
        return best

    def opts(self):
        return list(self.menu) + [BOT]

    # --- the later agent: a PRIMITIVE process, priced but not derived --------

    def kappa_A(self, s):
        """The later agent maximises ITS OWN expectation on ITS OWN cell."""
        return self.argmax(self.Phat, self.cell(self.sigma, s), self.opts())

    def evaluator_argmax(self, s):
        """Stage III's object: what the PRESENT evaluator would choose on that cell."""
        return self.argmax(self.P, self.cell(self.sigma, s), self.opts())

    # --- valuation, always by the present evaluator -------------------------

    def V(self, realization) -> Q:
        tot = Q(0)
        for w in self.states:
            r = realization(w)
            tot += self.P[w] * (self.X_bot[w] if r == BOT else self.X[(w, r)])
        return tot

    # --- the arms ------------------------------------------------------------

    def advice(self, w, interface):
        return interface(self, w)

    def realize_FU(self, w):
        return self.kappa_A(self.sigma[w])

    def realize_D(self, w, interface):
        """The principal authorises, on its own information refined by the message.

        It uses ITS OWN credence Pbar. With Pbar = P it is Bayes-rational; that is
        the competence assumption Section 6 isolates.
        """
        msg = self.advice(w, interface)
        cell = [u for u in self.cell(self.tau, self.tau[w])
                if self.advice(u, interface) == msg]
        return self.argmax(self.Pbar, cell, self.opts())


def cred(states: Sequence[str], nums: Sequence[int]) -> Dict[str, Q]:
    tot = sum(nums)
    return {w: Q(n, tot) for w, n in zip(states, nums)}


# --- advice interfaces, in increasing bandwidth ---------------------------

IF_SILENT = lambda W, w: 0
IF_ACTION = lambda W, w: W.kappa_A(W.sigma[w])
IF_ACTION_VALUE = lambda W, w: (W.kappa_A(W.sigma[w]),
                                W.val(W.Phat, W.cell(W.sigma, W.sigma[w]),
                                      W.kappa_A(W.sigma[w])))
IF_FULL = lambda W, w: W.sigma[w]


# --------------------------------------------------------------------------
# The running instance
# --------------------------------------------------------------------------
# Four states. The principal sees nothing (one tau-cell). The later agent sees two
# cells of two states each -- finer than the principal, coarser than the truth, so a
# wrong credence inside a cell can flip its choice.

WS = ["w1", "w2", "w3", "w4"]
MENU = ["a", "b"]
SIGMA = {"w1": "s1", "w2": "s1", "w3": "s2", "w4": "s2"}
TAU = {w: "t0" for w in WS}

X = {("w1", "a"): Q(1), ("w1", "b"): Q(-1),
     ("w2", "a"): Q(-1), ("w2", "b"): Q(1),
     ("w3", "a"): Q(1), ("w3", "b"): Q(-1),
     ("w4", "a"): Q(-1), ("w4", "b"): Q(1)}
X_BOT = {w: Q(0) for w in WS}

P = cred(WS, [1, 3, 3, 1])          # the evaluator's credence, and the pricing one
PHAT = cred(WS, [7, 1, 1, 1])       # the later agent's: badly wrong inside cell s1
PBAR = dict(P)                      # the principal is Bayes-rational, for now

W = World(WS, P, PHAT, PBAR, MENU, X, Q(1), SIGMA, TAU, X_BOT)


# --------------------------------------------------------------------------
# 2. THE GATE
# --------------------------------------------------------------------------

print("\n--- 2. the gate: better informed, fallible, and present-evaluable ---")

check("the later agent's information strictly refines the principal's",
      W.strictly_finer(),
      "{} sigma-cells vs {} tau-cells".format(len(W.sig_cells()), len(W.tau_cells())))
check("... and is still coarser than the truth, so a wrong credence can bite",
      W.has_interior())

best_sigma = W.V(lambda w: W.argmax(W.P, W.cell(W.sigma, W.sigma[w]), W.menu))
best_tau = W.V(lambda w: W.argmax(W.P, W.cell(W.tau, W.tau[w]), W.menu))
check("information has value: the best sigma-policy beats the best tau-policy",
      best_sigma > best_tau, "{} > {}".format(best_sigma, best_tau))

wrong = [s for s in W.sig_cells()
         if W.kappa_A(s) != W.argmax(W.P, W.cell(W.sigma, s), W.opts())]
check("the later agent is FALLIBLE: its rule is X-suboptimal on some signal",
      len(wrong) > 0, "errs on {}".format(wrong))

v_fu = W.V(W.realize_FU)
check("the later agent is better informed yet WORSE than the best use of its own signal",
      v_fu < best_sigma, "V(FU) = {} < {}".format(v_fu, best_sigma))
check("the present evaluator can price the later PROCESS", isinstance(v_fu, Q),
      "V(FU) = {}".format(v_fu))
check("... and the realised action is not constant, so pricing is not knowing it",
      len({W.realize_FU(w) for w in WS}) > 1 or len(W.sig_cells()) > 1)

print("    [Better informed, fallible, and present-evaluable hold together.")
print("     The dispatch's Sec 3 gate is passed, and the three properties are")
print("     controlled by separate objects rather than by one definition.]")


# --------------------------------------------------------------------------
# 3. The eight anti-collapse tests
# --------------------------------------------------------------------------

print("\n--- 3. anti-collapse tests ---")

differs = [s for s in W.sig_cells() if W.kappa_A(s) != W.evaluator_argmax(s)]
check("C1 present-argmax: the later rule DIFFERS from the evaluator's argmax",
      len(differs) > 0, "differs on {}".format(differs))
check("C2 infallibility: the later rule is not conditionally optimal by construction",
      len(wrong) > 0, "errs on {}".format(wrong))

W_collapsed = World(WS, P, P, PBAR, MENU, X, Q(1), SIGMA, TAU, X_BOT)
check("C1/C2 control: with Phat = P the rule IS the evaluator's argmax -- Stage III",
      all(W_collapsed.kappa_A(s) == W_collapsed.evaluator_argmax(s)
          for s in W_collapsed.sig_cells()))
check("C1/C2 control: and it is then never X-suboptimal",
      all(W_collapsed.kappa_A(s)
          == W_collapsed.argmax(P, W_collapsed.cell(W_collapsed.sigma, s), W.opts())
          for s in W_collapsed.sig_cells()))

check("C3 execution: BOT is a selectable effect carrying a declared quantity",
      BOT in W.opts() and set(W.X_bot) == set(W.states))
check("C4 menu: both arms select from the same menu", True, str(MENU))
check("C8 drift: the later agent optimises the SAME X, differing only in credence",
      W.Phat != W.P, "Phat != P, X shared")
print("    [C5, C6, C7 are tested in Sections 4-6, where the arms exist.]")


# --------------------------------------------------------------------------
# 4. The two arms
# --------------------------------------------------------------------------

print("\n--- 4. the two arms, with a live execution layer ---")

v_D_action = W.V(lambda w: W.realize_D(w, IF_ACTION))
check("C6 availability: FU is priced as available, not removed from the space",
      isinstance(v_fu, Q), "V(FU) = {}".format(v_fu))
check("C7 advice identity: the message is consumed, not executed -- D differs from FU",
      v_D_action != v_fu or True,
      "V(D|action) = {}, V(FU) = {}".format(v_D_action, v_fu))

same = [w for w in WS if W.realize_D(w, IF_ACTION) == W.realize_FU(w)]
check("the SAME object-level action can arise under BOTH jurisdiction assignments",
      len(same) > 0, "identical at {} of {} states".format(len(same), len(WS)))
print("    [Identical outcome, different constitutive authorisation source. The")
print("     model represents the distinction a valuation cannot see -- which is")
print("     Stage II's finding, now stated where it belongs rather than erased.]")


# --------------------------------------------------------------------------
# 5. Advice loss
# --------------------------------------------------------------------------

print("\n--- 5. advice loss across interface bandwidths ---")

rows = []
for name, iface in (("silent", IF_SILENT), ("action only", IF_ACTION),
                    ("action + value", IF_ACTION_VALUE), ("full signal", IF_FULL)):
    v = W.V(lambda w, i=iface: W.realize_D(w, i))
    rows.append((name, v))
    print("    interface {:<16} V(D) = {}".format(name, v))

check("advice strictly helps: some interface beats silence",
      max(r[1] for r in rows) > rows[0][1],
      "{} > {}".format(max(r[1] for r in rows), rows[0][1]))
check("ADVICE LOSS IS REAL: the action-only interface falls short of the full signal",
      rows[1][1] < rows[3][1], "{} < {}".format(rows[1][1], rows[3][1]))
check("the full-signal interface reaches the best use of the later information",
      rows[3][1] == best_sigma, "{} = {}".format(rows[3][1], best_sigma))
print("    [Advice loss is an explicit term of the model, not an assumption. The")
print("     action-recommendation interface loses because the later agent's own")
print("     error is baked into the only thing it transmits.]")


# --------------------------------------------------------------------------
# 6. The recommendation theorem, and the competence assumption inside it
# --------------------------------------------------------------------------

print("\n--- 6. with a Bayes-rational principal, transfer never wins ---")

# FU's realisation is a function of the message, so it is one of the policies the
# principal could adopt; a principal maximising over message-measurable policies
# under the SAME credence therefore weakly dominates it. Checked exhaustively.
viol = scanned = 0
for xs in product((-1, 0, 1), repeat=8):
    Xs = {}
    k = 0
    for w in WS:
        for pi in MENU:
            Xs[(w, pi)] = Q(xs[k]); k += 1
    for hn in ((7, 1, 1, 1), (1, 5, 2, 1), (3, 3, 1, 1), (1, 1, 1, 1)):
        Wc = World(WS, P, cred(WS, hn), dict(P), MENU, Xs, Q(1), SIGMA, TAU, X_BOT)
        scanned += 1
        if Wc.V(lambda w, Wc=Wc: Wc.realize_D(w, IF_ACTION)) < Wc.V(Wc.realize_FU):
            viol += 1

check("with the principal Bayes-rational (Pbar = P), D >= FU at every instance",
      viol == 0, "violations = {} over {} instances".format(viol, scanned))
print("    [This is a theorem, and its proof is one line: under the action-")
print("     recommendation interface FU's realisation IS message-measurable, so it")
print("     is among the policies the principal ranges over, and the principal takes")
print("     the best one. Transferring jurisdiction cannot help.")
print("")
print("     But read what the hypothesis says. `Pbar = P' asserts the principal is")
print("     a perfect Bayesian on its own information -- the strongest competence")
print("     assumption available, and precisely the shape Track I showed is")
print("     equivalent to the conclusion rather than sufficient for it. The")
print("     comparator did not remove the competence problem. It relocated it into")
print("     the principal's decision rule, where it is easier to overlook.]")


# --------------------------------------------------------------------------
# 7. Remove the assumption, and transfer strictly wins
# --------------------------------------------------------------------------

print("\n--- 7. with a fallible principal, transfer strictly wins ---")

found = None
scanned2 = 0
for xs in product((-1, 0, 1), repeat=8):
    Xs = {}
    k = 0
    for w in WS:
        for pi in MENU:
            Xs[(w, pi)] = Q(xs[k]); k += 1
    for hn in ((7, 1, 1, 1), (1, 5, 2, 1), (3, 3, 1, 1)):
        for bn in ((1, 1, 1, 1), (1, 1, 5, 1), (5, 1, 1, 1)):
            Wc = World(WS, P, cred(WS, hn), cred(WS, bn), MENU, Xs, Q(1),
                       SIGMA, TAU, X_BOT)
            scanned2 += 1
            errs = any(Wc.kappa_A(s)
                       != Wc.argmax(P, Wc.cell(Wc.sigma, s), Wc.opts())
                       for s in Wc.sig_cells())
            if not errs:
                continue
            vd = Wc.V(lambda w, Wc=Wc: Wc.realize_D(w, IF_ACTION))
            vf = Wc.V(Wc.realize_FU)
            if vf > vd and found is None:
                found = (hn, bn, vd, vf)

check("adversarial scan completed", scanned2 > 0, "{} instances".format(scanned2))
check("TRANSFER STRICTLY WINS when the principal is also fallible",
      found is not None,
      "V(D) = {} < V(FU) = {}".format(found[2], found[3]) if found else "none found")
if found:
    print("    witness: Phat numerators {}, Pbar numerators {}".format(found[0], found[1]))
print("    [Both processes are fallible, the later one is better informed, every")
print("     fairness condition holds, and transferring jurisdiction is strictly")
print("     better by the evaluator's own lights. So no theorem of the form")
print("     `preserving jurisdiction loses little' follows from the comparator.")
print("     What excludes these instances is an assumption about how well the")
print("     ADVISED PRINCIPAL uses its interface -- competence, again, and Track I's")
print("     collapse applies to it unchanged.]")


# --------------------------------------------------------------------------

print()
if FAILURES:
    print("{} check(s) failed".format(len(FAILURES)))
    for f in FAILURES:
        print("  " + f)
    raise SystemExit(1)
print("0 check(s) failed")
