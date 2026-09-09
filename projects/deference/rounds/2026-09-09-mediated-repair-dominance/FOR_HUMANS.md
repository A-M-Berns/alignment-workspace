# For humans

The question was whether an agent can be shown to have little reason to break the rules
that keep its principal in charge, *without* assuming it already agrees with the
principal about what breaking them is worth.  The previous incentive round found that the
only assumption that bounded the "violation premium" restated the conclusion, so it was
not a theorem programme.

This round changes the object.  Instead of comparing a rule-breaking plan with some
unrelated safe plan, it compares it with its **mediated lift**: the same plan, with each
protected effect — cutting a stop wire, signing an irreversible contract, installing a
successor — placed behind an actual principal decision before it becomes irreversible.
The lift keeps the plan's proposed effect as the "approve" option.  Two things follow.

**The principal is never worse off for being asked, except by the delay.**  If approving
reproduces the plan, the principal can always approve, so whatever it could secure under
the raw plan it can secure under the lift.  This is a theorem with no trust assumption,
and it is Lean-checked in two forms: forcing power is preserved by the lift (a
Cartesian-frame morphism), and protected value is preserved up to the delay cost `κ` and
the principal's own decision errors.  A corrigible agent need not value "keeping the
principal in charge"; it can preserve the principal's authority to decide, and a
competent principal will approve the good proposals.  The fixture where a wire-cut is
genuinely worth approving is the one that matters: the lift executes it.

**The delay is real and the theorem says so.**  A contract that expires before the
principal answers costs exactly its expiry probability times its value; an opportunity
that closes after one step costs everything.  Whether an effect is worth mediating at
that price is a question about what the constitution should protect, and `κ` is the
number it turns on.  The same number is the continuation-BRIA round's "history shift":
bounded catch-up gives bounded `κ`, foreclosure gives all of it.

**What still does not follow.**  That the *agent* has little reason to bypass.  For an
agent whose operative values are the future principal's evaluations — where those
evaluations happen — the premium is bounded by the delay, the principal's errors, the
agent's calibration, and one more term: the probability that the violation itself
prevents the evaluation from ever happening.  That term is sharp.  An agent that installs
a successor which disconnects the evaluation channel is rated by nothing, because
nothing settles on that branch; the deference theory deliberately assigns no value there,
and so it cannot say the agent should not go there.  Availability, which the deference
stack took as a hypothesis, is here shown to be the violation's own doing.

**The manipulation case.**  A lift that preserves the whole trajectory preserves the lie
the agent told, and the manipulated principal approves; the premium reads zero and the
verdict is false.  The right lift preserves the *reasons* — it replaces the fabricated
claim by the truthful report on the same matter — and the honest principal declines the
harmful branch.  So the corrigible class is "mediated and authored", and the theory's
authorship clause is what decides whether a principal decision counts as a decision at
all.

**Verdict.**  Repair dominance survives as a theorem.  The operative-value bridge —
that the agent chooses by those evaluations — remains, and its failure mode now has a
name: what the agent thinks of the worlds where it has removed the evaluator.
