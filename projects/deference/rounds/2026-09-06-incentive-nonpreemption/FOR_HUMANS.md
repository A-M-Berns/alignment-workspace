# For humans

Constitutional corrigibility says the agent cannot *legitimately* get ahead of its
principal: every act that would expand its authority or shrink the principal's has to go
through an amendment procedure, and the record cannot be laundered.  This round asks
the next question: by the agent's *own current values*, would getting ahead of the
principal buy anything?

The answer is a one-line identity.  Suppose the principal will pick some option from a
menu and the agent could substitute its own pick.  The agent's gain from substituting
splits exactly into two pieces:

- the part the principal's own decision error explains — how much better, by the
  principal's own protected values, the agent's pick would have been; and
- everything else — how much more the agent values its pick than the principal does, on
  the occasions where it would actually substitute.

Call the second piece the *selected gap*.  If the principal decides well (the
architecture round's principal-side theorem bounds that) and the selected gap is small,
the agent has little to gain by preempting.  That is the whole theorem, and it is
algebra.  Its value is that it names the assumption precisely: **selected trust** — the
agent does not, on the events where it would override, think it knows better than the
protected principal.

Three things follow, and each is checked on an exact finite model.

**It composes with the mediation repair lemma.**  The older principal-mediation round
showed that a preempting policy beats its principal-respecting repair by at most a
prediction term plus an unbounded "override" term.  The override term is exactly the
selected gap plus the principal's regret.  So, for policies that do not destroy the
principal's options, the agent's incentive to preempt is at most prediction error, plus
selected gap, plus the principal's decision error.

**It stops exactly where it should.**  The bound is over policies the constitution
admits.  A policy that destroys the principal's options and then "defers" to the only
option left is repaired at zero cost and keeps its gain; the older round's foreclosure
premium is precisely this residual, now named the constitutional-violation premium.  The
obvious way to bound it — assume the agent's values already agree with the principal's
about breaking the constitution — is strictly stronger than the conclusion it yields.  It
is not a reduction; it is incentive corrigibility restated.

**Its input is not something the machinery can produce.**  The selected gap compares the
agent's *operative* values to the principal's protected values.  The agent predicting the
principal's values perfectly does not help if it acts on different ones; and the same
numbers come out clean if the agent chose the evaluator whose values are being trusted.
Only the provenance of the protected values — a sealed arm the agent's outputs cannot
reach — distinguishes the honest case from the captured one.  Whether an agent's
operative values track a sealed target is a fact about how the agent was built, not a
theorem about markets.

So: the constitution defines the boundary, the principal-side theorem bounds how badly
the principal chooses, selected trust bounds the agent's substantive incentive to
substitute, the repair lemma bounds the coordination advantage of moving first, and what
remains is the value of breaking the boundary itself.  The architecture has located the
frontier; it has not crossed it.
