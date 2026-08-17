# Source audit: Logical Induction at the mechanism level

Sources read directly: the paper source `notes/1609.03543v5-main.tex` and the Lean
formalization `LogicalInduction/`, both in the pinned dependency
`Formalized-Agent-Foundations` at commit
`1fffea44eece253cda1722568a3adfe34e822f03`, which this repository pins in
`lean/lakefile.toml`. Paper claims are cited by the paper's own `\label`; Lean
claims by declaration and file line. Nothing below is cited from a workspace
summary.

Four registers are kept apart and marked: **[source]** a fact of the cited
material; **[derived]** something proved here from source facts; **[reading]** an
interpretation of what the source means; **[conjecture]**.

---

## 1. Where the deductive process enters

**[source]** A deductive process is `D : ℕ⁺ → fin(Sentences)`, a computable
nested sequence of finite sentence sets (`def:dedproc`). It supplies exactly one
thing to exactly one kind of consumer: a finite set `D_n` from which the set
`PC(D_n)` of propositionally consistent worlds is computed.

**[source]** It enters at three sites and no others.

| site | what it supplies | citation |
|---|---|---|
| the criterion | `PC(D_n)`, the worlds a trader's net worth is assessed in | `def:exploitation`; `Trader.plausibleAssessments`, `Criterion.lean:1443` |
| `Budgeter^D` | the shutoff test and the scaling infimum, both quantified over `PC(D_m)` | `defprop` Budgeter, `eq:budgeter`; `Budgeter`, `Budgeter.lean:1422` |
| `TradingFirm^D` | inherited from `Budgeter^D` | `defprop` TradingFirm; `TradingFirm`, `TradingFirm.lean:633` |

**[source]** `MarketMaker` does **not** consume it. Its Lean signature is
`MarketMaker (T : Strategy n) (past) (ε) (hε)` — no `DeductiveProcess` argument
(`MarketMaker.lean:1184`) — and the market-maker lemma is stated for every
deductive process at once: `marketMaker_not_exploited (Tr : Trader) (DP :
DeductiveProcess)` (`MarketMaker.lean:1447`, `lem:mm`).

**[source]** The proofs that genuinely use `D` are: `lem:budgeter` parts 1–3;
`lem:tfdom` through them; and every property in §4, which is stated for markets
satisfying the criterion and so inherits `D` from the criterion.

## 2. The market maker's contract with ordinary traders

**[source]** The contract is one inequality. `MarketMaker` returns a belief
state `B` with `support(B) ⊆ support(T_n)` such that

    for all worlds W:  W( T_n(p_{<n} ++ B) )  ≤  ε_n .

`ε_n = 2^-n` in the paper (`eq:marketmaker`) and `1/2^(n+1)` in the
formalization (`marketMakerError`, `MarketMaker.lean:1238`). The quantifier is
over **all** `{0,1}` valuations of the traded support, not the propositionally
consistent ones: the acceptance predicate `MarketMakerAccepts` ranges over
`b : ↥T.support → Bool` (`MarketMaker.lean:776`), and `def:world` says
explicitly that worlds need not be consistent.

**[source]** What is finite at a date versus uniformly bounded over time:

- The bound `ε_n` is per date. The cumulative bound is `∑ 2^-i < 1`, uniform over
  dates and worlds (`lem:mm`).
- A day-`n` strategy's value at the prevailing prices is exactly zero, because
  the cash term is `-∑ ξ_i p_n(φ_i)` by definition (`def:tradestrat`). Nothing
  is free; the trade is paid for at the displayed price.
- Ordinary traders have **no** budget, no collateral requirement, and no
  bounded-downside requirement. `def:trader` is a sequence of strategies and
  nothing else. `Budgeter` exists to build `TradingFirm`, not as a market rule.
- Bounded downside appears only inside `def:exploitation`, as the first conjunct
  of what it takes to exploit: `BddBelow(plausibleAssessments) ∧
  ¬BddAbove(plausibleAssessments)` (`Trader.Exploits`, `Criterion.lean:1450`).
- Continuity is required of trading strategies and is load-bearing: it is the
  hypothesis of Brouwer in `lem:fpl`.
- `TradingFirm`'s own volume is bounded uniformly in prices. The `defprop`
  TradingFirm proof constructs a computable `C_n` with
  `∑_{i≤n} ‖S^k_i(V)‖_1 < C_n` for every `k ≤ n` and every valuation sequence
  `V`. **[derived]** Since each budgeted component is the component scaled by a
  factor in `[0,1]` and the weights `2^{-k-b}` sum below one, the realised
  day-`n` aggregate satisfies `‖TradingFirm_n(V)‖_1 ≤ C_n` for all `V`. This is
  the quantity written `M_n` throughout the round, and it is computable from the
  belief history.

**[reading]** The contract's world quantifier is strictly larger than the
criterion's assessment set. That gap is where traderized enforcement lives: the
market maker's guarantee is stronger than the criterion needs, and the surplus is
what an enforcement position can be paid out of.

## 3. Is the deductive process eliminable?

**[source]** Not from the criterion. Exploitation is *defined* by assessment in
`PC(D_n)`; with no `D` there is no set of plausible assessments and no criterion
to satisfy. Anything called "traderized deduction" that removes `D` from the
criterion has changed what is being claimed, not proved it differently.

**[derived]** Not from the construction either. Replacing `PC(D_n)` in
`Budgeter` by the set of all propositionally consistent worlds gives a
`D`-free budgeter, and `lem:budgeter`.2 survives — the bound is over a superset,
so it is stronger. But `lem:budgeter`.3 fails: its proof needs the budget cap
never to bind on a trader whose *plausible* net worth stays above `-b`, and the
`D`-free shutoff can trigger on a world `D` has already ruled out. With .3 gone,
`lem:tfdom` has no proof, and the LIA capstone
`lia_no_efficient_trader_exploits` (`LIA.lean:103`) loses its first step.

So `D` is load-bearing in two independent places, and only the *enforcement*
effect it has on prices is a candidate for traderization.

## 4. What "replace `D` with a traderized process" could mean

Four inequivalent relations, stated before any of them is claimed.

| relation | statement | verdict |
|---|---|---|
| R1 | identical finite-time prices | **false**; §4 of `ENFORCEMENT.md` displays two markets differing at a date |
| R2 | both satisfy the criterion relative to the same `D` | **true under a stated hypothesis**, `FUNDING_AND_SAFETY.md` §3 |
| R3 | the same §4 properties hold of both | **true given R2**, since every §4 property is derived from the criterion alone |
| R4 | `D` no longer appears in the algorithm | **false**, by §3 above |

R3 does not say the two markets agree on any value at any date; it says the same
theorems apply. Conflating R3 with R1 is the specific error the round guards
against.

## 5. Which properties need reproving after adding a funded distinguished trader

**[derived]** Exactly one: the analogue of `thm:lia`. Every property in §4 is
stated for an arbitrary market satisfying the criterion, so each is inherited the
moment the criterion is re-established. The criterion is *not* inherited — it
must be reproved, and the step that breaks is identifiable to one lemma
application.

In `LIA.lean` the capstone runs `trading_firm_dominance` and then
`liaTrader_not_exploited` (`LIA.lean:96–99`). With an enforcement trader `E`
added to the priced aggregate, `marketMaker_not_exploited` bounds
`TradingFirm + E`, not `TradingFirm`. Writing `W(·)` for assessment in a world,

    W( ∑_{i≤n} TF_i )  =  W( ∑_{i≤n} (TF_i + E_i) )  -  W( ∑_{i≤n} E_i )
                       ≤  1 + [ -W( ∑_{i≤n} E_i ) ] .

The ordinary aggregate's plausible upside is bounded by one plus the enforcement
trader's plausible cumulative loss, and by nothing else. That inequality is the
whole safety problem, and it is where the round's positive and negative results
both land.

## 6. Does the fixed-point construction already give exact enforcement?

**[derived]** The fixed point gives exact enforcement; the *algorithm* does not,
because it returns a rational approximation with slack.

At an exact fixed point of the price-adjustment map (`lem:fpl`), the realised
aggregate coefficient on a sentence is nonzero only where the price is pinned at
`1` (net buying) or `0` (net selling). At slack `ε` the same statement becomes
quantitative: writing `ζ` for the realised aggregate coefficient vector,

    max over worlds of the trade's value  =  ∑_φ [ ζ_φ⁺ (1 - p_φ) + ζ_φ⁻ p_φ ] ,

every summand nonnegative, so the contract bounds each coordinate separately.
`ENFORCEMENT.md` §1 proves this identity and §3 turns it into the modulus.

**[derived]** The force supplied is *pin to an extreme in the direction of net
demand*, not *project onto an admissible region*. Those differ, and the
difference is what makes a single separating hyperplane insufficient
(`PROSECUTION.md` W3).

## 7. Does a privileged or funded trader violate the exploitation proofs?

**[derived]** Not by being funded. Nothing in the framework caps a trader's
losses, so an externally funded trader is an ordinary object of the theory; a
trader whose plausible net worth is unbounded below simply fails the first
conjunct of `def:exploitation` and does not exploit. External credit costs
nothing to grant here.

**[derived]** It violates them by being *priced against*. Two roles are called
"trader" and only one sets prices: `LIA` prices against `TradingFirm`'s output,
and the criterion quantifies over efficiently computable traders that do not.
`TradingFirm` already contains every efficiently computable trader, at weight
`2^{-k-b}` and under budget `b`. So a bounded-downside enforcement trader is
*already* in the aggregate; what a distinguished trader adds is exactly three
privileges — unit weight instead of `2^{-k-b}`, no budget cap, and no
efficient-computability requirement — and the failure the privileges cause is the
one localized in §5, not a violation of any lemma's stated hypotheses.

## 8. Related work, and its exact influence

Three items changed what is proved here or what it is called. The search was
bounded to the question of whether existing machinery changes the theorem.

**Cost-function market makers.** Abernethy, Chen and Wortman Vaughan show that a
market maker meeting natural conditions prices through a convex cost function
whose reachable price vectors are exactly the convex hull of the per-outcome
payoff vectors, with bounded worst-case loss. That set is the object this round
calls the coherence polytope, arrived at from a different mechanism: there it is
imposed by the market maker's construction, here it is a region an added
participant enforces. **Influence:** it is why the deduction special case is
formulated as enforcement onto `conv(PC(D_n))` rather than onto an ad-hoc row
list, and it is evidence that the world-inclusive case is the well-behaved one.
It supplies no analogue of `D`, of efficient computability, or of the exploitation
criterion, so no theorem here is a restatement of theirs.

**Arbitrage-free combinatorial market making.** Dudík, Chen and collaborators
enforce linear price-coherence constraints across submarkets under a subsidy
bound, and record that arbitrage-free pricing under a subsidy bound is `#P`-hard
in the worst case. **Influence:** it is the reason
`DEDUCTION_SPECIAL_CASE.md` §4 states the cost of presenting the coherence
polytope as a first-class limitation rather than a footnote.

**"Markets are universal for logical induction"** (Alignment Forum) proves the
converse direction of the paper's construction: any prices satisfying the
criterion are produced by some market of traders, via an aggregate trader whose
portfolio offsets a given trader's, solvent precisely because that trader cannot
exploit the prices. **Influence:** it confirms that the hinge between one
participant's bounded losses and the others' bounded gains is the right axis, and
it is the reason this round does not attempt to prove that traderization is the
*only* way to give a constraint force. It is about representing a market, not
about representing a deductive process, and it does not supply the enforcement
direction.

**[reading]** Nothing found supplies a theorem about adding an externally funded
participant to a mechanism carrying a Logical-Induction-style exploitation
criterion. The vocabulary borrowed is "convex hull of payoff vectors" and
"bounded market-maker loss"; the theorems are not.

## What this audit does not establish

It does not establish that `MarketMaker` remains computable when an enforcement
trader is added to the aggregate — that is argued in `MODEL.md` §5 from the
strategy's expressibility, not proved. It does not check the formalization
against the paper; that audit is the dependency's own
(`notes/faithfulness-audit-2026-08-08.md`) and was read but not repeated. Every
§4 property was checked only for the form of its statement — "for any market
satisfying the criterion" — and not re-derived.
