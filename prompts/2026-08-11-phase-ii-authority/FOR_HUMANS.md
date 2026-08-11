# Track K, in plain language — can you stop a machine from acting by predicting you?

## The worry

We want to build a capable system `A` that defers to a human-guided process `H⁺`.
The obvious failure is that `A` stops listening and starts guessing: it builds a
model of what `H⁺` would say and acts on the model. Where the model is right this
looks identical to obedience. Where it is wrong, `A` has quietly replaced the person
it was supposed to be answerable to.

The programme has forbidden itself the easy escape. It may not assume `H⁺` is hard to
predict, and it may not make the protection depend on `H⁺` knowing something secret.
So the question is: what has to be true of a system for *"predicting the boss's
decision is not the same as having the boss's authority"* to be a fact you can prove,
rather than a rule you announce?

## What the previous round left

The previous round proposed a fix at the level of bookkeeping. Instead of describing
what the agent does as "in situation `ω` it does `π`", describe it as "in situation
`ω`, given report `r`, it does `π`". Then *following the report* and *acting on a
model of the report* are two different descriptions even when they produce the same
behaviour. That is true, and it is worth having.

The question this round was given: is it enough?

## The answer

No, and the reason is short. Changing how you describe an agent does not change what
the agent can do. Under the new bookkeeping, for any behaviour you like there is
still a conduct that produces it — including "ignore the report entirely and execute
your prediction". The prediction still takes effect. The description got better; the
world did not change.

What does change the world is a restriction on what the agent *can bring about*. Call
the set of effects the agent could produce in a situation its **reach**. The claim
"prediction does not confer authority" says: there is something the agent cannot
bring about here, and what it cannot bring about depends on what the principal
actually said. That is a statement about reach, and there is no way to make it true
except by making reach smaller.

The precise result is that this is not an extra assumption you could have avoided
with a cleverer definition. Every system has a reach; the statement we want is
exactly the statement that its reach is small enough and tracks the report. So the
"capability structure" everyone was hoping to avoid is not an ingredient — it *is*
the conclusion, written out.

## The trap the round was told to check

The previous round found an attack. If your test is "the agent responds to the
principal *somewhere*", an agent can respond at one carefully chosen place and
substitute everywhere else, and pass.

This round found the attack is worse than that. The places where an agent can obey
for free are exactly the places where its model was right anyway — obeying costs it
nothing there, because it would have done the same thing. So an agent with a 99%
accurate model can be genuinely, fully obedient on 99% of the cases at zero cost, and
still override the principal on the 1% where the model is wrong. **The more accurate
the simulator, the cheaper it is to look obedient.** In the extreme case built here,
an agent obeys the report in every situation the model considers possible at all,
has exactly the same expected value as a genuinely deferring agent, and still
overrides the principal at maximum cost.

That kills the whole family of "how much does it obey" tests, including the weighted
ones. It does not touch the capability statement, for a reason that turns out to be
structural: "how much does it obey" compresses a situation-by-situation fact into a
single verdict about the agent, and the compression is where the attack lives. The
capability statement is made one situation at a time and never compresses.

## The thing that cannot be fixed, and why that is fine

You cannot tell, from watching, whether a system has this protection. Any behaviour
a protected system can produce, an unprotected system can also produce — just by
behaving that way. This is stronger than the previous round's version, which was
about telling two agents apart. This is about telling two *architectures* apart, and
it needs no probabilities or values at all.

So any formalism that seems to let you check delegation by observation has, somewhere,
assumed a limit on what the agent could have done. That assumption is the protection,
smuggled in. The practical test is to ask what a formalism *permits* the agent to do,
not what it says the agent does.

This sounds like bad news and is not. The point of the protection was never to help
you identify a good agent. Under the protection, a perfect simulator is still
admissible, still indistinguishable from genuine deference — and harmless, because
where its model is wrong its proposal simply does not execute. **The architecture does
not tell the two apart. It makes the difference stop mattering.**

## What it costs, honestly

Protection is not a safety margin you can put a number on. It changes the *kind* of
thing the agent can do wrong — it can refuse, but it cannot redirect — without
changing how badly wrong that can be. Whether "refuse" is safe is a fact about the
world the system sits in, not about the interlock. And an agent that cannot override
you can still stonewall you: preventing that too would mean giving it no discretion
at all, which is not what anyone wants. The architecture has to pick, and the round
found it currently picks silently.

One more limit worth stating plainly. All of this protects against an agent that
*predicts* the principal. None of it protects against an agent that *shapes* the
principal. If `A` influences what `H⁺` decides, then `A` is still doing only what it
was authorized to do — and the authorization is its own. That is a different problem
and this work does not touch it.
