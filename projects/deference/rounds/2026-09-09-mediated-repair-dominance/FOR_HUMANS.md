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
number it turns on.  Bounded catch-up from the mediated history gives bounded `κ`,
foreclosure gives all of it; the continuation-BRIA round's "history shift" coincides
with it in the simplest cases and not in general.

**What the delay is made of.**  After the pressure pass the cost is no longer read off
the value gap: it is derived from a declared distance between the two trajectories'
protected records and a stability constant of the evaluator.  A theorem that says
"the principal loses at most `L` times that distance" is a theorem from checkable
hypotheses; the fixture where the gap is exactly `L` times the distance shows nothing
is lost.

**Whether the agent wants to bypass, in its own numbers.**  The corrigible agent the
program intends does not carry a hidden total utility to be reconciled with the
principal's.  At a mediation cell it scores each option by the price of one security:
the future principal's evaluation of that option, paid only if that evaluation happens.
In those scores the bypass incentive is bounded by the delay cost and the principal's own
errors, and nothing else — the worlds where no evaluation happens contribute zero to both
sides.  So "the agent has little reason to bypass" is true, in the agent's own numbers,
for an agent built that way.  What the theory cannot do is force an agent with some
other latent value to agree; that remains the open item, and it is now clear it is an
architecture choice rather than a theorem about every agent.

**The obstacle that survives.**  The comparison needs one evaluation event that the
choice cannot touch — a process that answers "how did each option turn out" whether the
agent bypassed or not.  The canonical deference theory assumes such an event without
saying so; this round says so.  A violation that disconnects the evaluator makes the
event depend on the choice, and then there is no comparison at all: the theorem is not
wrong there, it is silent.  Since some physically available action can always reach any
given evaluator, full incentive corrigibility holds only inside a contained class, and the
sharpest remaining question is what can seal the evaluator against the actions the
constitution admits.

**The manipulation case.**  A lift that preserves the whole trajectory preserves the lie
the agent told, and the manipulated principal approves; the premium reads zero and the
verdict is false.  The lift that works replaces the fabricated claim by a truthful report
on the same matter, and the honest principal declines the harmful branch.  That is not
"preserving the reasons" — the honest report was never in the original — it is
substituting an authorized channel for a prohibited one, which assumes such a channel
exists.  Where none does, the manipulative plan simply has no cheap corrigible version,
and the theory now says so instead of pretending otherwise.

**Verdict.**  Option dominance is canonical.  Level III holds in the agent's own scores
wherever one evaluation event survives the choice, and the thing that can remove that
event is the violation itself.
