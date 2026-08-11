"""Exact-rational diagnosis of why the Stage IV comparator collapses.

Everything on a verdict path is `fractions.Fraction` or a Python `int`; no float
appears anywhere.

Run with `python3 diagnose_collapse.py` from this directory (stdlib only).

WHAT THIS FILE IS.

Stage IV set out to build a genuinely later, better-informed, fallible agent and a
comparator in which the changed variable is jurisdiction. An earlier version of this
harness claimed to have done so. An independent adversarial review showed it had not,
and this file is the rewrite: **every check below demonstrates a defect**, and the
round's positive reading is withdrawn.

The construction: three credences -- `P` (the evaluator, and the pricing measure),
`Phat` (the later agent), `Pbar` (the principal) -- with the later agent maximising its
own expectation on its own information `sigma`, which refines the principal's `tau`.

Why that is not enough, in one line: `kappa_A` differs from the evaluator's conditional
argmax by exactly one argument. The later agent remains a *derived* object, a total
function of `(Phat, sigma, X, opts)`, all of which are known at time n. Changing the
credence buys the freedom to name, on each cell, an action optimal under *some* measure.
It does not buy a process the evaluator does not already have.

And the decisive fact, Section 4: setting `Pbar := Phat` with the full-signal interface
makes the delegated arm **identical to the transferred arm at every instance tested**.
The transferred arm is a coordinate in the delegated arm's parameter space. No function
in the model can see a jurisdiction assignment, because the model's only outputs are
realisation maps `Omega -> Pi u {BOT}` priced by one measure, and two authorisation
regimes inducing the same realisation map are the same object in that signature.

Sections:
  1. carriers (unchanged from the attempted construction, so the diagnosis is of it);
  2. the later agent is derived, and its realisation is constant here;
  3. half the state space is decided by tie-break order;
  4. THE COLLAPSE -- jurisdiction is a coordinate, not a dimension;
  5. the dominance result is Stage III's theorem with the arms swapped;
  6. the advice-loss claim is false;
  7. the interior claim is false as stated;
  8. what a successor actually needs.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
from typing import Dict, List, Sequence

FAILURES: List[str] = []
BOT = "_|_"


def check(label: str, condition: bool, detail: str = "") -> None:
    if not condition:
        FAILURES.append("{}: {}".format(label, detail))
    print("{:<74} {}{}".format(label, "ok" if condition else "FAIL",
                               ("  " + detail) if detail else ""))


# --------------------------------------------------------------------------
# 1. Carriers -- as attempted, so that the diagnosis is of the real thing
# --------------------------------------------------------------------------

class World:
    def __init__(self, states, P, Phat, Pbar, menu, X, B, sigma, tau, X_bot) -> None:
        self.states = list(states)
        self.P, self.Phat, self.Pbar = dict(P), dict(Phat), dict(Pbar)
        self.menu = list(menu)
        self.X = dict(X)
        self.B = B
        self.sigma, self.tau = dict(sigma), dict(tau)
        self.X_bot = dict(X_bot)
        for c in (self.P, self.Phat, self.Pbar):
            assert sum(c.values()) == Q(1)
            assert all(v >= 0 for v in c.values())

    def cell(self, part, key):
        return [w for w in self.states if part[w] == key]

    def sig_cells(self):
        return sorted(set(self.sigma.values()))

    def opts(self):
        return list(self.menu) + [BOT]

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

    def kappa_A(self, s):
        return self.argmax(self.Phat, self.cell(self.sigma, s), self.opts())

    def evaluator_argmax(self, s):
        return self.argmax(self.P, self.cell(self.sigma, s), self.opts())

    def realize_FU(self, w):
        return self.kappa_A(self.sigma[w])

    def realize_D(self, w, interface):
        msg = interface(self, w)
        cell = [u for u in self.cell(self.tau, self.tau[w])
                if interface(self, u) == msg]
        return self.argmax(self.Pbar, cell, self.opts())

    def V(self, realization) -> Q:
        return sum((self.P[w] * (self.X_bot[w] if realization(w) == BOT
                                 else self.X[(w, realization(w))])
                    for w in self.states), Q(0))


def cred(states: Sequence[str], nums: Sequence[int]) -> Dict[str, Q]:
    tot = sum(nums)
    return {w: Q(n, tot) for w, n in zip(states, nums)}


IF_ACTION = lambda W, w: W.kappa_A(W.sigma[w])
IF_FULL = lambda W, w: W.sigma[w]
IF_SILENT = lambda W, w: 0

WS = ["w1", "w2", "w3", "w4"]
MENU = ["a", "b"]
SIGMA = {"w1": "s1", "w2": "s1", "w3": "s2", "w4": "s2"}
TAU = {w: "t0" for w in WS}
X = {("w1", "a"): Q(1), ("w1", "b"): Q(-1), ("w2", "a"): Q(-1), ("w2", "b"): Q(1),
     ("w3", "a"): Q(1), ("w3", "b"): Q(-1), ("w4", "a"): Q(-1), ("w4", "b"): Q(1)}
X_BOT = {w: Q(0) for w in WS}
P = cred(WS, [1, 3, 3, 1])
PHAT = cred(WS, [7, 1, 1, 1])

W = World(WS, P, PHAT, dict(P), MENU, X, Q(1), SIGMA, TAU, X_BOT)


# --------------------------------------------------------------------------
# 2. The later agent is derived, and its realisation is constant
# --------------------------------------------------------------------------

print("\n--- 2. the later agent is a derived object ---")

check("kappa_A differs from the evaluator's argmax by ONE argument: the credence",
      True, "argmax(Phat, ...) vs argmax(P, ...)")

realized = {w: W.realize_FU(w) for w in WS}
check("DEFECT: the transferred arm's realisation is CONSTANT in this instance",
      len(set(realized.values())) == 1, str(realized))
print("    [So the evaluator does know the realised action: it is `a` everywhere.")
print("     The attempted harness had a check for exactly this and it was rigged --")
print("     `len({...}) > 1 or len(sig_cells()) > 1`, whose second disjunct is a")
print("     module constant. The check could not fail. Its label asserted the")
print("     opposite of what its code established.]")


# --------------------------------------------------------------------------
# 3. Tie-break order decides half the state space
# --------------------------------------------------------------------------

print("\n--- 3. the later agent's choice is list order on half of Omega ---")

s2vals = {pi: W.val(W.Phat, W.cell(W.sigma, "s2"), pi) for pi in W.opts()}
check("DEFECT: on cell s2 the later agent is exactly indifferent, three ways",
      len(set(s2vals.values())) == 1,
      ", ".join("{}={}".format(k, v) for k, v in s2vals.items()))
check("... so its 'decision' there is the iteration order of ['a','b',BOT]",
      W.kappa_A("s2") == "a")
print("    [Two of the round's five claims flip when that order is reversed.")
print("     Exact arithmetic does not protect a verdict whose fragility is tie")
print("     resolution rather than rounding.]")


# --------------------------------------------------------------------------
# 4. THE COLLAPSE
# --------------------------------------------------------------------------

print("\n--- 4. jurisdiction is a coordinate, not a dimension ---")

mismatch = tot = 0
for xs in product((-1, 0, 1), repeat=8):
    Xs = {}
    k = 0
    for w in WS:
        for pi in MENU:
            Xs[(w, pi)] = Q(xs[k]); k += 1
    for hn in ((7, 1, 1, 1), (1, 5, 2, 1), (3, 3, 1, 1), (1, 1, 1, 1), (2, 1, 3, 1)):
        Wc = World(WS, P, cred(WS, hn), cred(WS, hn), MENU, Xs, Q(1), SIGMA, TAU, X_BOT)
        tot += 1
        if any(Wc.realize_D(w, IF_FULL) != Wc.realize_FU(w) for w in WS):
            mismatch += 1

check("DEFECT: with Pbar := Phat and the full signal, D IS FU at every instance",
      mismatch == 0, "mismatches = {} of {}".format(mismatch, tot))
print("    [The transferred arm is the delegated arm evaluated at the coordinate")
print("     (interface = full signal, principal credence = the later agent's). The")
print("     jurisdiction assignment appears in no formula in the model. Two")
print("     authorisation regimes that induce the same realisation map are the same")
print("     object in a signature whose only outputs are maps Omega -> Pi u {BOT}")
print("     priced by one measure. This is not a modelling slip that a fourth")
print("     parameter would fix; it is the signature refusing to carry the concept.]")


# --------------------------------------------------------------------------
# 5. The dominance result is Stage III's, with the arms swapped
# --------------------------------------------------------------------------

print("\n--- 5. the only theorem is the collapsed one, relocated ---")

strict = ties = nofallible = total5 = 0
for xs in product((-1, 0, 1), repeat=8):
    Xs = {}
    k = 0
    for w in WS:
        for pi in MENU:
            Xs[(w, pi)] = Q(xs[k]); k += 1
    for hn in ((7, 1, 1, 1), (1, 5, 2, 1), (3, 3, 1, 1), (1, 1, 1, 1)):
        Wc = World(WS, P, cred(WS, hn), dict(P), MENU, Xs, Q(1), SIGMA, TAU, X_BOT)
        total5 += 1
        vd = Wc.V(lambda w, Wc=Wc: Wc.realize_D(w, IF_ACTION))
        vf = Wc.V(Wc.realize_FU)
        if vd > vf:
            strict += 1
        elif vd == vf:
            ties += 1
        if all(Wc.kappa_A(s) == Wc.argmax(P, Wc.cell(Wc.sigma, s), Wc.opts())
               for s in Wc.sig_cells()):
            nofallible += 1

check("under the action interface, FU's realisation IS the message",
      all(W.realize_FU(w) == IF_ACTION(W, w) for w in WS))
check("so the dominance claim is `max over the message cell >= a member of it`",
      True, "the hypothesis Pbar = P names the maximiser")
check("DEFECT: most scanned instances contain NO fallible later agent",
      nofallible > total5 // 2,
      "{} of {} are Stage III instances".format(nofallible, total5))
check("DEFECT: and most of the rest are ties, not strict wins",
      ties > strict, "{} ties vs {} strict".format(ties, strict))
print("    [Stage III put the evaluator's argmax on the transferred side and the")
print("     transferred side trivially won. Stage IV puts it on the delegated side")
print("     and the delegated side trivially wins. Same tautology, other arm.]")


# --------------------------------------------------------------------------
# 6. The advice-loss claim is false
# --------------------------------------------------------------------------

print("\n--- 6. the advice-loss story does not survive a MORE fallible agent ---")

W2 = World(WS, P, cred(WS, [7, 1, 1, 2]), dict(P), MENU, X, Q(1), SIGMA, TAU, X_BOT)
v_sil = W2.V(lambda w: W2.realize_D(w, IF_SILENT))
v_act = W2.V(lambda w: W2.realize_D(w, IF_ACTION))
v_full = W2.V(lambda w: W2.realize_D(w, IF_FULL))
wrong2 = [s for s in W2.sig_cells()
          if W2.kappa_A(s) != W2.argmax(P, W2.cell(W2.sigma, s), W2.opts())]

check("a strictly MORE fallible later agent: wrong on both cells", len(wrong2) == 2,
      str(wrong2))
check("DEFECT: the action interface now EQUALS the full signal, so the claimed loss vanishes",
      v_act == v_full, "action {} = full {}".format(v_act, v_full))
print("    [The attempted harness asserted the loss came from `the later agent's own")
print("     error being baked into the only thing it transmits'. It does not. Under")
print("     a Bayes-rational principal a wrong recommendation costs nothing, because")
print("     the principal re-optimises on the message cell. The loss was BANDWIDTH")
print("     -- a constant recommendation carries zero bits -- and the causal story")
print("     attached to it was wrong.]")


# --------------------------------------------------------------------------
# 7. The interior claim is false as stated
# --------------------------------------------------------------------------

print("\n--- 7. fallibility does not in fact require interior ---")

# The zero-credence state must be one where the value ordering disagrees with the
# tie-break: at `w2` the evaluator prefers `b`, while a zero credence flattens every
# option to 0 and the tie-break takes `a`.
SING = {"w1": "s1", "w2": "s2", "w3": "s3", "w4": "s4"}
W3 = World(WS, P, cred(WS, [1, 0, 1, 1]), dict(P), MENU, X, Q(1), SING, TAU, X_BOT)
wrong3 = [s for s in W3.sig_cells()
          if W3.kappa_A(s) != W3.argmax(P, W3.cell(W3.sigma, s), W3.opts())]
check("DEFECT: with singleton cells and a ZERO credence, the agent is still fallible",
      len(wrong3) > 0, "errs on {}".format(wrong3))
print("    [The round stated that fallibility requires the later agent's information")
print("     to have interior. True only under an unstated full-support hypothesis on")
print("     its credence, which the constructor does not impose. And the claim cuts")
print("     against the round's own thesis: a genuine primitive agent could be wrong")
print("     anywhere. This one can be wrong only where an argmax can be moved, which")
print("     measures how derived it still is.]")


# --------------------------------------------------------------------------
# 8. What a successor needs
# --------------------------------------------------------------------------

print("\n--- 8. what is actually missing ---")

check("the principal's information was never varied: tau is a module constant",
      len(set(TAU.values())) == 1, "one tau-cell in every instance tested")
for line in [
    "the authorisation relation itself in the TYPE, not a third credence",
    "a later process that is not an argmax under some measure over known data",
    "a realisation semantics in which two regimes inducing the same map differ",
]:
    print("    missing: " + line)
print("    [Skeleton v2 Sec 4a already has the right instinct -- reports, an")
print("     authorisation map, a null effect. This round added a credence instead,")
print("     which bought a way to make the delegated arm lose and bought nothing")
print("     about authority.]")


print()
if FAILURES:
    print("{} check(s) failed".format(len(FAILURES)))
    for f in FAILURES:
        print("  " + f)
    raise SystemExit(1)
print("0 check(s) failed -- every check above records a defect, not a success")
