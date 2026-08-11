# What putting the market back in changed

**Status:** `ci-only`; human register for Stage V. Names are provisional.

The older deference work talked about traders without representing them. It
assumed the inequality a trader was supposed to force and proved consequences of
that inequality. The current dependency now has the missing objects: a market,
trading strategies, cumulative wealth, an exact notion of efficient trader, and
the Logical Induction Criterion saying no efficient trader can become unboundedly
rich with bounded downside.

Stage V connects one deference-relevant case all the way through. A trader buying
one grade contract per day has wealth exactly equal to the accumulated signed
prediction error. If the contract sentences can be emitted efficiently, the
dependency itself proves this trader is admissible. The criterion then rules out
one-sided unbounded signed error when downside is bounded. This is a real use of
the criterion, not a finite analogue or a hypothesis named “forcing.” It does not
give absolute-error accuracy, and it does not remove the need to show bounded
downside.

The faithful-acceleration result was also closer to the real criterion than the
front-door documents suggested. It already uses the dependency's trader and
wealth definitions and really invokes non-exploitability. Its remaining gap is
more specific: the proposed trader contains another process's varying prices, but
the model does not show those values can be emitted within the efficiency budget,
and it has no theorem calibrating one market to another. The market/trader gap
shrunk; the cross-process gap did not close.

Logical Induction does contain a notion of “later” that the finite models erased.
Over FAF's constructed arithmetic logical inductor, the quotation machinery can
efficiently emit a sentence referring to an exact later market price without
evaluating that price while producing the sentence. The inductor can price
statements about a future recommendation or a future person's computable report.
Its self-trust theorems constrain current beliefs about future beliefs.

But the formalization stops one step short of the governing hypothesis. Every
future price is still a total computable value, and the library has no
resource-indexed agent state proving that the present process has not already
computed it. It gives compact present names for later computations, not a theorem
that their results are presently unavailable. It also has no action, proposal,
recommendation, authorization, capability or continuation type. A quoted future
recommendation can be fallible because nothing defines it as correct, but it is a
logical fact about a computation, not yet a future decision-maker.

This makes the self-trust boundary sharp. The strongest self-trust theorem says,
roughly, that current prices must respect certain future prices and future
confidence. Add an independent bit saying who controls execution, and the theorem
is unchanged whichever way the bit is set. Rationally respecting a later belief
therefore does not allocate practical authority. Logical Induction formalizes the
reason to listen; it is silent about who decides.

Stage V also turns the conditional core of the Stage IV jurisdiction observation
into an elementary Lean theorem. If a value sees an architecture only through its price and realized
action map, then two architectures with equal price and realization must receive
equal value. A worked example carries different jurisdiction explicitly and shows
that a value reading jurisdiction can distinguish the pair only by failing that
static factorization. The theorem does not establish unrestricted jurisdiction
invisibility or say jurisdiction is valuable. It says
where jurisdiction must appear if it is to matter: before value has thrown away
authorization, capability or continuation structure.

Foreclosure remains outside the model. The smallest credible successor needs two
times and a state transition: the same immediate action can leave a future human
correction reachable in one branch and remove it in another. Logical Induction
could price computable claims about that structure, but it does not supply the
structure or imply that preserving the option is always better. Commitment can be
valuable, so option value needs ordinary decision-theoretic assumptions.

The constructed philosophical claim is now stronger but still negative:

> Logical Induction can make later cognition rationally worth attending to, while
> remaining formally silent about whether that cognition should control the later
> decision.

The aspiration remains that future cognitive superiority need not imply surrender
of continuing corrective authority. The controlling next question is whether a
minimal resource-indexed process and continuation-capability interface can make
both halves of that sentence coexist in one formal model.
