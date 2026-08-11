# What this round did, in plain terms

The deference research line inherited a body of Lean proofs from an earlier project. Those
proofs cover the *first* half of the programme's picture: a bounded human reasoner H using a
faster reasoner A as an accelerator. An audit of that inherited work found something
important: the proofs establish what *follows from* the theory of deference, but not the
theory's starting points. In particular, the step everyone cares about — "the no-Dutch-book
rule forbids this arbitrage, therefore H must trust A" — was written as an assumption,
because nothing in that development modelled a market, a trader, or money changing hands.

Two things came out of this round.

**First, the inherited results were re-checked here rather than taken on trust.** Six of the
headline statements were transcribed into this repository and re-run through the Lean kernel
against this repository's own compiler and libraries. They all check out. That does not make
them stronger than they were; it removes one layer of "someone else's audit says so."

**Second, the assumed step was partly replaced by a proof.** The dependency this repository
pins does model markets and traders. So the argument was rebuilt on top of it: the trading
rule that the inherited work described in prose is now an actual object in the formal
language, the trader is an actual trader, and its running profit-and-loss is computed exactly.
With that in place, the no-Dutch-book rule is applied rather than assumed.

One assumption stands in the way of calling this finished. The formal rule only applies to
traders that a computer could actually run within a time budget, and proving that our trader
qualifies is a separate piece of bookkeeping that was not done. Until it is, the new theorem
is honest but incomplete, and the report says so rather than rounding up.

Doing the rebuild also turned up four things worth recording, of which two matter:

- The assumed bound was on the wrong quantity. The rule limits a trader's *net worth*, which
  differs from the profit the inherited proof bounded by whatever position the trader still
  has open. When the trader closes each position the next day, that difference is at most one
  unit and nothing breaks. When the trader waits longer — which is the whole point of
  "forecasting H's *future* opinion" — the difference can grow without limit, and then the
  assumption is not something the rule supplies. The pinned dependency's own version of this
  argument carries a condition that prevents exactly that; the inherited statement has no
  such condition.
- The other assumption — that A's forecasts of H's future opinions are unbiased on average —
  cannot be sourced from any existing theorem, and the reason is structural rather than a
  matter of effort. The available theorems are about forecasting facts that eventually get
  settled true or false. H's future *opinion* never settles; it just keeps being an opinion.
  So this is a missing kind of theorem, not a missing lemma. The inherited notes had already
  reached the same conclusion informally; this round confirms it at the level of what the
  formal machinery can even express.

Everything above is machine-checked where it says it is machine-checked, and flagged where it
is a reading of source code rather than a proof. Nobody has reviewed it by hand yet.
