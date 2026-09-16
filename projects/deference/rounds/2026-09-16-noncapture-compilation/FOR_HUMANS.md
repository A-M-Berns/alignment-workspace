# For humans

**The question.**  The last round showed that an agent gains nothing, in a logical
inductor's eyes, by bypassing its principal's authority over effects, beyond three
residual quantities the theory names.  This round asks whether the *other* way of
subverting a principal, shaping what the principal sees rather than acting around it,
has the same shape: an inequality over a declared interface, with a residual for
steering that slipped past the audit, that the inductor learns.

**The answer, in one breath.**  The inequality is the same, literally the same
algebra; it compiles into the same bounded object the last round built, so the
inductor learns it with nothing new proved; and Robust Openness over a declared finite
list of interventions becomes a plain computation once the principal's decision
procedure is committed.  But the residual does *not* shrink to zero just because the
reason interface is complete, authenticated, canonical, covered and live.  There is a
one-line counterexample, and it is not exotic.

**The counterexample.**  Four declared reasons, all true.  One counterreason is
protected, so the audit checks that it is on the table.  Another counterreason is not
protected.  The advisor puts its own reason on the table, someone raises the protected
counterreason on time, and nobody raises the unprotected one.  Everything the thesis asks
for holds: every reason present is true and certified, the principal's program is
committed and reads only declared content, the protected reason is there, nothing is late.
The advisor's candidate is scored a quarter higher than it would have been with the full
picture, and that quarter is exactly the weight of the reason nobody mentioned.  Coverage
protects what is declared protected; liveness says a route exists, not that anyone walked
it.  Neither says a word about a true reason nobody was obliged to raise.

**What removes it.**  Two things, and both are decisions about the ecosystem rather than
facts about the interface.  Protect every declared reason type, so that any omission
voids the evaluation, at the price that every true declared reason must be on the table
before every commitment.  Or oblige someone other than the advisor to raise every true
declared reason before the deadline, which is a supply job with a cost, and the
affordability theory says the cost is of the competing-budget kind because there is a
deadline.

**Why the effect side is different.**  On the effect side the residual is killed by
rewriting the agent's own move: whatever it tried to do gets routed through the
principal.  On the reason side you can rewrite what the advisor wrote (canonicalize its
order, strip its framing, drop its duplicates), and that does kill the form attacks.  You
cannot rewrite what the advisor *did not write*.  An omitted reason is not in its
outputs.  So the reason side has a corrigibilization for form and none for content, and
that is the structural fact behind the whole verdict.

**Three smaller findings.**  Canonicalization is a separate hypothesis, necessary and
cheap: an order-sensitive principal pays exactly the order.  A reason outside the declared
interface, or two facts sharing one declared name, are invisible to every quantity the
theorem can see; they make the comparator wrong rather than the residual large, and
nothing on the log measures them.  And the comparator itself is not canonical: the
log-determined one only neutralizes form, the fully-informed one needs the engine to
settle reasons nobody raised, and the declared-transform one is Robust Openness with its
usual external contract about what the transforms mean.

**Verdict, first pass.**  Non-capture compiles; reason completeness does not carry the
residual.  The two-interface symmetry survives only strengthened by total scope,
ecosystem-supplied liveness and an extensional program, and even then leaves what the
declaration cannot see.

---

## Second pass: turning the leftover into a theorem

**The question.**  The first pass ended with a leftover: the value of the true reasons
nobody put on the table.  The second pass asks when that leftover is small, and whether
"small" can be a theorem rather than a hope.

**What to count.**  Not how many reasons are missing.  A missing reason matters by how
much its presence would have lowered the advisor's score, and that number is a
property of the principal's committed program that can be read off in advance, reason
by reason.  For the ordinary weighted program it is the weight of a counterreason and
zero for anything else.  For a program with defeaters it is subtler, and a per-weight
count gets it wrong; the per-reason "adverse sensitivity" gets it right.  Two lemmas,
checked by machine, say that the advisor's gain from any set of omissions is at most the
sum of those numbers.

**Who supplies, and with what.**  Someone other than the advisor learns that reasons are
true at various moments, and has a limited amount of routing-and-authenticating capacity
in each period before the commitment deadline.  A reason discovered late can only use the
capacity that remains.  The exact statement, and it is exactly Hall's marriage theorem:
everything can be served if and only if, for every moment, what is discovered from that
moment on fits into the capacity left from that moment on.  When it does not fit, the
least you can miss is the largest such overflow, and if you serve the most damaging
reason first whenever you have a free slot you achieve the least possible missed value,
whether or not you can see the future.  With reasons of unequal cost this last part
fails, and the problem is as hard as packing a knapsack; the overflow bound still holds.

**Why this is a theorem and not a promise.**  The supplier's docket, capacities and
schedule are on the log, so "the service loss this round is at most such-and-such" is
a sentence the theory settles, and the previous round's machinery accepts exactly such
sentences.  A short bridge lemma feeds it in, and the result is that the bounded agent
learns it has no advantage from steering beyond the certified service loss, which is
zero whenever the fit condition holds.  What the log cannot settle is which true reasons
nobody discovered at all.  That is the one thing left over, and the theorem says so
rather than hiding it in a comparator.

**Protection is a dial.**  Protecting a reason means the evaluation voids if it is
missing; not protecting it means the advisor gains its value if it is missing.  So the
right thing to protect is what you can afford to serve: the most damaging reasons that
fit.  Protecting everything is right only when everything fits.

**What was wrong before.**  The first pass said reason supply was "the timeliness case
of affordability".  Half right: the existing affordability theory supplies the budget
half, and it has no shared-slot structure and no missed-mass bound.  The capacity half,
where the fit condition lives, is new.  And the first pass silently assumed the advisor
cannot make a counterreason expensive to authenticate; it can, and that becomes an
explicit hypothesis.
