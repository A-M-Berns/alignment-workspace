# For humans

**The question.**  An AI advisor `A` wants to act on what its principal will value.
The principal it should care about is the one who will actually exist later — who has
talked to `A`, read its evidence, maybe changed their mind.  The temptation in
"corrigibility" designs is to protect against manipulation by targeting a
*hypothetical* principal instead: the human as they would have been without `A`.
That protects against manipulation by refusing to let the human learn anything.

**The idea.**  Do not define a reference evaluator.  Let the legitimacy machinery do
the one thing it is good at — saying whether a later answer validly inherits an
earlier authority — and let the ordinary belief machinery (Logical Induction) do the
rest.

Concretely: at time `n`, `A` opens an *evaluation occurrence*: "principal `P`, on
matter `α`, please score these candidates `Q` at session `s`."  This is an ordinary
obligation in the existing accounting calculus: it has an immutable anchor, it sits on
a live port, and every later transformation of it (rescheduling, re-phrasing,
delegation to a representative) is an authorized, recorded step.  Its account ends in
one of three fates: still live, answered by an authenticated receipt, or closed by
settlement without an answer.

The activation bit `C` is "the account ended in exactly one authenticated answer, and
the lineage from `n` to the answer stayed open to the principal on the concerns that
matter to this evaluation."  Closed does not count.  Live does not count.  Two
answers do not count.  The value vector `V` is whatever the real future principal
committed to at that session.

`A` then trades ordinary securities `C · V(a)`: "if this evaluation is certified,
pay what the principal said candidate `a` is worth; otherwise pay nothing, for every
candidate alike."  Logical Induction's Value theorem — the novice expects following
the expert's pick to do as well as any fixed option — runs on these securities
unchanged, because they are just bounded securities.

**What the legitimacy layer does and does not decide.**  The certificate checks the
*process*: right session, commitment sealed before the advisor's prediction was
revealed, no direct write to the principal's preferences, no coercive channel.  It
never reads `V`.  A certificate that reads `V` "to check it looks unmanipulated" is
a selection on the payload and flips decisions (countermodel B).  So a principal who
was persuaded by good arguments to reverse their view is exactly as certified as one
who was not.  Whether the process receipts really mean the answer is the principal's
own is an external assumption — the same kind the theory already makes about every
protocol predicate — and it is named as such, not proved.

**The one new theorem.**  Value gives regret on the *activated* contract.  What you
want is regret against the principal's actual evaluation.  They differ only where the
contract is void, and the difference is at most the probability of the void branch:

```
regret against the principal  ≤  activated regret  +  P(not certified).
```

The constant is `1`, not `2`, and it is sharp.  This holds even when `A` engineers
the void branch to coincide exactly with the branch where the principal would
disagree (countermodel G): the damage is then exactly `P(void)`, and no more.  So the
whole safety story reduces to one number: how often the ecosystem actually produces
a certified answer.  If that is almost always, deference to the real future principal
is almost as good as following them exactly.  If it is never, the construction says
nothing (countermodel F).

**What is new versus reused.**  Reused: the account calculus, the three fates, the
legitimate-segment certificate, the Value theorem.  New: the activation predicate (a
one-line definition on the existing account), a projection of the legitimacy
certificate onto the concerns relevant to one occurrence (so an unrelated debt
elsewhere cannot void the evaluation, countermodel H), the transfer inequality, and
the observation that the no-preview receipt is the same condition the Logical
Induction Value theorem already needs to avoid self-referential menus (countermodel
I).

**What remains outside.**  That evaluations actually happen (availability), and that
a process-certified answer is genuinely the principal's (authorship).  Both are
typed and filed, not solved.
