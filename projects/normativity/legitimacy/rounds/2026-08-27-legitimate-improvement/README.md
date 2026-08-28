# Legitimate Improvement

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

NO-FREE-EVASION-SURVIVES, for a demonstrated repair — once a repair has been demonstrated on the process's own record, every later diagnosed occasion is LIVE, CONTESTED or SETTLED, and the fourth cell is empty. The result is an accounting statement rather than a second bound: it does not limit how long a process may contest, only that contesting is what it is doing. What connects one retirement event to an unbounded later stream is not counting events, which cannot work, but that the claim is outstanding at each later occasion — 340 diagnosed occasions covered by one opened claim. Three secondary results. The effective mass the online-learning kernel adapts to is neither definition that was proposed for it: the Khot-Ponnuswami reduction forces the inner player's own loss to zero, so AdaNormalHedge's adaptive quantity collapses to the sum of I(t) times the absolute change in incurred loss, which weighs an occasion by how much the repair would actually have altered it rather than by whether it was awake or how much probability it moved. A surgical repair empties the LIVE cell for a structural reason stronger than any regret bound, since the diagnosed action's stationary mass under the fixed point is zero whenever the repair carries weight. And two escapes are real and are not this theorem's to close: retiring a repair before evidence accumulates leaves no demand at all, which is a Coverage boundary, and changing the evaluator so nothing is ever demonstrated is invisible here and needs an independence premise this round does not have.

## The question

Legitimate Evolution is frozen and deliberately claims no learning. The obvious
composition — *legitimacy plus low repair regret gives defect elimination* — has
an obvious counterexample: a process can watch a repair prove itself, then
legitimately retire the repair, and continue the old conduct forever with regret
going to zero because there is no longer anything to compare against.

This round asked whether the combination proves something weaker and true
instead: that a demonstrated improvement cannot be escaped **for free**.

It does, and the shape of the result is worth stating carefully. It is not a
bound on how much a process may go on doing the diagnosed thing. It is that the
diagnosed conduct has only three places to be, and all three are visible.

## What is claimed

```text
LOCAL           Permit, Due, Resolve            frozen, unchanged
                selector I, repair f            predictable
LEARNING        Adv_T(I,f) <= sqrt(3 C_T (ln(1/q) + ...))      anytime
                C_T(I,f) = sum_t I(t) |p^T(M_f - 1)l|  <=  W_T(I)
ADAPTER         D_live <= (B_T + xi)/eps        given a consumer witness
ACCOUNTING      D = D_live + D_contested + D_settled,  D_escaped = 0
```

`LEGITIMATE_IMPROVEMENT.md` has the whole package, the countermodel table and
the literature verdict.

## What the prosecution found

**The effective mass is not what it was assumed to be.** Two definitions were
proposed in advance and both are wrong: counting occasions where the repair is
awake, and counting the probability mass it moves. The reduction actually
produces the loss-weighted form, and `CM9` separates them — a repair that moves
real probability across actions of equal loss scores full under both proposals
and exactly zero under the derived one.

**A surgical repair empties the LIVE cell by construction.** `pi(BAD) = pi(BAD)
M(BAD,BAD)`, so a repair that maps the diagnosed action elsewhere gives it zero
stationary mass the moment it carries any weight. That is stronger than the
bound that was expected to cover it, and it means Theorem B's real content is
for diagnostics a registered repair does not fully eliminate — of which this
round has none.

**The hypothesis that makes regret mean anything is that the process runs the
algorithm.** The first version of the countermodels made the process merely
stubborn, which puts it outside every learning theorem and leaves nothing for
legitimacy to compose with. The second made it play its own fixed point, which
made it adopt the repair and therefore never accumulate evidence for the
improvement it was already making. Evidence has to be **counterfactual**.

**Widening the surface to include designation was a normative choice.** Keying
activation on licence and menu alone let `CM6b` escape outright: stop calling
these occasions learning occasions and 240 diagnosed occasions had no claim of
any kind. Closing it means saying that ceasing to treat a recurring context as a
learning context is itself answerable.

## Contents

- `LEGITIMATE_IMPROVEMENT.md` — verdict, theorems, interfaces, countermodels,
  literature verdict, export property, freeze recommendation.
- `src/regret.py` — Theorem A. Names no legitimacy vocabulary, checked by parsing.
- `src/surface.py` — the comparison surface and the four-cell accounting.
- `src/challenge.py` — the canonical constitution, over frozen `Due`/`Resolve`.
- `src/cases.py` — CM1-CM13.
- `src/consumers.py` — two positive fixtures and the deliberate negative.
- `tests/` — 46 cases. `python3 tests/run.py`.

## What this does not establish

No Lean and no registered claim.

That recurrent defects disappear. They do not: `CM8` contests forever and
satisfies everything here.

Anything about delay. `tau_t = 0` throughout; the anchor is carried so the
delayed deference consumer will not need the types redesigned, and no delayed
bound is claimed.

Anything about evaluator manipulation. `CM5` is invisible to this theorem.

That the canonical activation rule is right. Demonstration-thresholded activation
is one constitution among others, and `CM2` is precisely what it gives up.
