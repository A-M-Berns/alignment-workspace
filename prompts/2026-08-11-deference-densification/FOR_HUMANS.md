# What Track E found, in plain language

Generator: this round's orchestrator (Claude Opus 5, Anthropic), from the executing
agent's verification register. The executing agent was blocked by its tooling from
writing files of this kind. Review status: `ci-only`. Verification register:
`REPORT.md`.

The setting: an AI can catch a mistake, but it only finds out whether it was right
much later. In between, it is exposed — it has committed to something it cannot yet
confirm. If we cap how much can be outstanding at once, how often can it act?

The answer turns out to be a piece of geometry rather than economics. Each
commitment occupies a stretch of time, from when it is made to when it settles.
Capping outstanding exposure means capping how many of those stretches can overlap.
So the total amount that can ever be committed, up to any deadline, is exactly the
cap multiplied by the largest number of *non-overlapping* stretches that fit before
that deadline. Not approximately — exactly. The bound and the best possible strategy
are two descriptions of the same fact.

Three tempting ways to beat this all fail, and each fails for the same underlying
reason. Being clever about *when* to commit buys nothing: the limit holds even for a
strategy that knows the whole future. Running several commitments at once buys
nothing: the best strategy never has two open. Committing in fractional amounts buys
nothing: the optimum is always a whole number of full-size commitments.

So the question the round was asked — can you keep exposure bounded and still act
infinitely often? — has an easy yes, by a two-line construction, in every delay
regime whatsoever. That makes it the wrong question. The real question is the
*rate*, and the rate is pinned exactly. If delays are short, acting is nearly free.
If delays double each time, the number of opportunities grows like the logarithm of
the deadline. If delays grow exponentially in the step number, it is worse than that
by an amount hard to convey: accumulating five units of confirmed correction would
require waiting about two-to-the-eight-and-a-half-billion steps. Not slow —
unreachable.

Three checks confirm the walls are real rather than artifacts of how the problem was
written. Allowing commitments to cancel each other out on paper appears to beat the
limit by a huge factor, but the cancellation is fake: the two sides settle at
different times for different amounts, so the risk was never actually removed —
legitimate cancellation always cancels the payoff too. Allowing the AI to wait and
act at the last moment before settlement makes the whole problem disappear, which
tells us the difficulty lives entirely in the requirement that spotting a problem
now means committing now. And allowing winnings to be reinvested makes the harvest
grow exponentially, but only by letting exposure grow without bound, which is the
very thing being capped.

That last one is the finding the maintainer needs. The constraint studied here caps
how much is outstanding at any moment. The constraint the underlying theory actually
imposes caps total losses, which is a different thing and permits reinvestment.
Those two give different answers to the question. Until the project says which one it
means, this question has two answers, and the report supplies both.
