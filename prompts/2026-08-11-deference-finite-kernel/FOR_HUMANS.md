# What Track B found, in plain language

Generator: this round's orchestrator (Claude Opus 5, Anthropic), from the executing
agent's verification register. The executing agent was blocked by its tooling from
writing files of this kind, and `AGENTS.md` requires every substantive deliverable
to ship both registers, so this one is the orchestrator's text rather than the
executor's. Review status: `ci-only`. Verification register: `REPORT.md`.

The question was: if we want an AI to defer to a human overseer, what has to be true
for deferring to actually be the AI's best option — and can any way of *settling
accounts* make it so?

Three ways of settling were on the table. Score the AI on predicting what the
overseer will say. Score it on how things actually turn out. Or simply charge it a
penalty when it does something the overseer did not endorse.

The first one turns out to buy nothing at all, and the example showing this is as
bad as it can be. Build a case where the AI predicts the overseer's judgment
*perfectly*, where no bet about those judgments could ever have made it money — and
where deferring is still worse for the AI than ignoring the overseer, by the largest
margin the setup allows. Scoring an AI on predicting a person constrains what it
believes that person will say. It says nothing whatever about whether doing what
that person says is any good. Those are different questions, and only the second one
is the one we care about.

The second way of settling makes things *measurable* but not *costly*. Scoring the
AI on real outcomes means we can check afterwards whether deference was a good idea.
It does not give the AI any reason to defer in the first place.

The third way works, and the way it works is the finding. Charge a penalty for
non-conformity and deference becomes optimal — always, for every case, no matter how
competent or incompetent the overseer is, with no assumption about anything. The
required penalty was computed exactly: it is twice the largest stake in play. That
is not epistemic trust. Nobody has shown the overseer is worth listening to. It is a
fine large enough that disobeying stops being worth it, which is a real and useful
thing to know how to build, but it is not what the project set out to find.

There is a genuine positive result underneath. If you *assume* the overseer's
judgments track what actually matters to within some margin, then a clean inequality
follows, with every constant derived rather than guessed: the AI loses by deferring
only when that margin, doubled, exceeds the overseer's own strength of preference,
and it pays that cost only over the cases where the two would actually have chosen
differently. The bound is exactly sharp — examples hit it with equality — and the
part that says the overseer is competent is doing all the work.

And that assumption is imported from outside. It is not a fact about the AI's
reasoning that some no-losing-bets condition could force; it is a claim that the
overseer is good at judging. Nothing in the model produces it. This is the same gap
the project's inherited work already identified as its central one, showing up again
in a much smaller setting, which is some evidence that the gap is structural rather
than an artifact of how the earlier work was written.

One last piece, and it is the one worth remembering. The settlement method that
contributes nothing to the argument — scoring the AI on predicting the overseer — is
exactly the method you need in order to *observe* whether the AI conformed, which is
what the penalty has to be charged against. So the two approaches that fail on their
own are precisely what the approach that works is built out of.
