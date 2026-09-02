# Liability and affordability

**Status: open / unregistered**, except where noted. The enforcement layer's three
narrow results are registered and carry `lean-proved`; the affordability theory
built on top of them is current research.

## The question nobody asks first

Suppose you have decided what a reasoner ought to do, and you have a mechanism that
makes it actually do so. There is still a question left, and it is easy to miss:
*what does the making cost?*

Not a metaphor. In the traderized construction, a normative constraint acquires
force by adding a trading position to the market the reasoner's beliefs are priced
in — a position that pushes back whenever the constraint is violated. That position
can lose money. If it loses enough, the reasoner is no longer a good reasoner: the
whole point of the underlying construction is that no cheap trader can systematically
beat it, and an enforcement position bleeding without limit is exactly such a
trader.

So normative authority is not free, and **unbounded authority does not mean
unbounded legitimate expenditure**.

## What force actually emits

This is the interface distinction the program guards most carefully.

The enforcement mechanism gives a **conformance guarantee**: at any price the
market maker will accept, the constraint is violated by no more than a declared
tolerance. That part is kernel-checked.

It does **not** give a safety certificate. What it emits alongside the guarantee is
a **liability obligation** — a quantity that some surrounding layer has to
discharge. A reader who takes the conformance certificate as a promise that the
reasoner survives has misread the interface, and the interface note says so
explicitly.

What discharges the obligation is a bound on the enforcement position's cumulative
value across the worlds settlement has not yet ruled out. Bound it, and the
preservation theorem applies: no efficiently computable trader exploits the
modified market.

> Preservation is **substrate** preservation. It says the learner survives being
> made to obey. It does not say the norm was taken up, and it is not a normative
> result.

## The account is signed, and that matters

A natural simplification is to charge each date its worst-case loss and require
every date to pay for itself. It is wrong, and the program got it wrong once before
correcting it.

The account is **signed and cumulative**. A date that loses can be paid for by a
date that gains, and there are norms every one of whose dates is robustly
loss-making while the running account stays comfortably inside a fixed band. Worst-
case-per-date underwriting is *sufficient* for safety and is strictly, unboundedly,
more conservative than what safety actually requires.

There is a related trap. A reason the reasoner is currently *satisfying* takes a
zero position, and therefore costs nothing at all — however deeply that norm
excludes the worlds still in play. Cheapness of enforcement is a fact about the
reasoner's current conduct, not about the severity of the norm.

## Per-reason, not just in aggregate

If several reasons are being enforced at once, is it enough that the aggregate
account stays healthy?

No, and the counterexample is a single line: two books whose increments are `+1`
and `-1` have an identically zero aggregate account and unbounded values
individually. What makes reason-level safety available is a floor on each row
separately, with the floors summing to something finite; then every group of rows
inherits a uniform ceiling.

There is a second, subtler failure. A policy that respects its per-date spending
limit at every single date can still have an account that falls without bound, if
the limits themselves do not sum. **Local enforcement capacity is not lifetime
safety**, and conflating them is the sort of mistake that looks fine in every finite
check.

## Affordability

Affordability is the schematic question: *can the mechanism meet the normative
demand?* Bounded cumulative liability is one concrete way to certify it — a
realization of the concept, not its definition. The conceptual answerability theory
makes this typing itself, and the program has adopted it unchanged.

The sharp result is a criterion. Enforcing a reason forever, on a finite lifetime
budget, is possible **exactly when** the cost of a fixed unit of enforcement dips
arbitrarily close to zero infinitely often. Not "often enough", not "on average" —
just infinitely often, however rarely. The budget doesn't appear in the criterion;
any positive budget buys unbounded persistence when the criterion holds, and none
buys it when it fails.

Two consequences that are not obvious.

**Persistence does not create competition between reasons.** Every individually
sustainable reason can be sustained simultaneously with all the others. There is no
scarcity condition to check. **Timeliness does**: once deadlines are imposed, the
minimum cost is a definite positive number, budgets add, and reasons genuinely
compete for a finite resource.

**A reasoner deciding in real time loses nothing on the persistence question.** A
simple rule that waits for cheap moments and spends geometrically shrinking amounts
achieves persistence whenever a scheduler with perfect foresight could. It loses
everything on the quantitative question: there is no positive competitive ratio for
*how much* enforcement intensity gets accumulated.

## Where this connects

Affordability is the feasibility side of [Serviceability](Serviceability), and it
is one of the three candidate pillars of [Legitimacy](Legitimacy) — though the
checkpoint argues it is better read as a *side condition* than a conjunct, since a
cheaper norm is not thereby a more legitimate one.

## What is open

Whether bounded liability is **necessary** for preservation or merely sufficient.
Until that is settled, every "unaffordable" verdict in this line means *the known
route to safety no longer applies*, not *no safe policy exists* — a materially
weaker statement than the prose usually suggests.

Whether any of it survives when the cost of enforcing responds to the enforcement.
Every existence result assumes the prices are handed down from outside.

What a scheduler needs to know to operate safely on the signed account. The running
slack is provably not enough, because the world attaining the minimum can itself be
settled away.

---

**Evidence.** The force interface is
[`TRADERIZED_FORCE_INTERFACE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md);
the liability theory is
[`2026-08-30-liability-theory`](https://github.com/A-M-Berns/alignment-workspace/tree/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-30-liability-theory);
the affordability characterization is in
[`SHARP_PERSISTENCE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/SHARP_PERSISTENCE.md).
