# The Logical-Induction comparison

Declarations cited from the pinned formalization
(`lean/.lake/packages/agentFoundations/LogicalInduction/Properties/`); nothing is
paraphrased into a hypothesis here, and nothing below is used by a proof of this round.

## What Logical Induction gives across two inductors

For any logical inductor `P` over a deductive process `DP` with a plausible world at
every day (`hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)`):

- **`lic_price_convergesTo`** (`Coherence.lean`; paper node `thm:con`): for every
  sentence `φ`, `∃ L, ConvergesTo (fun n => P n φ) L`.  Each inductor's price of every
  sentence converges — to its own limit.
- **`lic_limitCoherence`** (`LimitCoherence.lean`; `thm:lc`): the limiting prices are the
  sentence probabilities of a probability measure concentrated on worlds consistent
  with the completed theory.  **`lic_limitingBelief_theorem`**: a sentence in some
  `DP.D k` has limiting belief `1`; **`lic_disprovable_tendsto_zero`**: a sentence whose
  negation is in every `DP.D n` has price tending to `0`.
- **`lic_limit_pos`, `lic_limit_lt_one`** (`NonDogmatism.lean`; `thm:nd`): a sentence
  that stays consistent with the process has limit strictly inside `(0,1)`.

Across two inductors `P, P'` over the same `DP` this yields: on every sentence the
process settles, both limits are `1` (or both `0`) — agreement in the limit on what
settles.  On a sentence the process never settles, each limit exists and is strictly
inside `(0,1)`, and the two limits are two Gaifman measures' values of one event; nothing
in the cited declarations relates them.  Two inductors may converge to `1/3` and `2/3`
on the same undecidable sentence forever.

## What this round gives

On the unsettled normative fragment — sentences no settlement pins — two reasoners
sharing a structural layer, a settlement chain and a declared `Φ` have a hull mass that
is nonincreasing under settlement and shared narrowing (`hullMass_anti` with
`forcedInterval_nest_of_subset`), converges under summable reopenings
(`hullMass_tendsto_of_summable`), and a discord mass that is positive exactly on
certified incompatibilities (`discordMass_eq_zero_iff`, `discord_certificate`) and is
eventually constant once the live sets coincide (`DYNAMICS.md` H3).  This is a
cross-reasoner property on sentences that never settle, obtained from two mechanisms
Logical Induction does not have: a shared closed layer that both reasoners' regions lie
inside, and exchange of warrants that narrows both.

## What it does not give, exactly

The property is about **forced intervals** — what the compiled bundle admits — relative
to the closed layer and to `Φ`.  It says nothing about any inductor's prices reaching
those intervals; that is the enforcer's, priced by the affordability theory, and the
seed round closed the criterion question as construction-relative.  It does not say the
two reasoners' prices agree; it says their admitted intervals are confined to a hull
that shrinks and whose incompatibilities are certified.

## The one-sentence claim

Logical Induction gives two inductors agreement in the limit on what the deductive
process settles and nothing on what it does not; on the unsettled normative fragment,
two reasoners with a shared structural layer and exhaustive sharing of warrants have
admitted intervals whose hull is nonincreasing and convergent and whose incompatibilities
are exactly the certified ones — a property of the compiled regions relative to the
shared layer and the declared fragment, not of any inductor's prices.
