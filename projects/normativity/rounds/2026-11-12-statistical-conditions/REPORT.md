# Statistical conditions on a floor market — report

Round `2026-11-12-statistical-conditions`. Dispatch: `prompts/2026-11-12-statistical-conditions/PROMPT.md`.
Statements of record: `THEOREM.md`. Lean: `StatisticalConditions.lean`,
`StatisticalConditionsVille.lean` under `lean/Workspace/Normativity/Contrib/`.

| | |
|---|---|
| Prompt author | Claude Fable 5.2 (Anthropic), on the maintainer's instruction in conversation on 2026-11-12 |
| Executor | Claude Fable 5.2 (Anthropic), in Claude Code |
| Second opinion | GPT-6 Astra (OpenAI), through `codex` |
| Dates | 2026-11-12 |
| Base | `origin/round/2026-11-10-exact-conditions-capital` at `37f11078` (pull request #146, open) |

## Judgment

**The theorem.** For one floor `c ≤ price(φ_n)` per day on a fresh sentence settled the next
day, the statistical statement that is proved is a dichotomy, not a bound
(`DualCertifiedMarket.bounded_or_buyer_exploits`): if the realized frequency is at least
`c + γ` along the one weighting that reads whether the day's price is within `δ < γ` of the
floor, then either the account is bounded below — so no efficiently computable trader
exploits — or the trader that buys at those prices exploits. With that buyer efficiently
computable, the account is bounded below exactly when no efficiently computable trader
exploits (`accountBounded_iff_unexploited`).

**Its hypothesis.** A frequency along a feature of the market's own prices. It is endogenous:
a sequence of frequency `3/4` priced at the floor on its false days fails it. The hypothesis
item 138 asked to derive, `Bridge.Frequency` on the market's normalized multipliers, is
equivalent under the bridge's other hypotheses to the summability of those multipliers
(`bridge_frequency_iff_summable`); it has no frequency content. What bounds the account is
that the price clears the floor by a margin from some day on
(`accountBounded_of_eventually_slack`), because the multiplier times the clearance is at most
the day's tolerance (`stake_prices_le`).

**Proved.** The exact cost of `R` lost instances, `−U((1 − c)^-(R+1) − 1)` with the open
instance, attained on sequences; its market form, inhabited by a floor market one of whose
instances is false. Unit-stake and market-stake accounts are each bounded without the other;
bounded variation of the stakes carries boundedness across. With outcomes favourable at `c`
given the past, the settled account reaches `−K` with probability at most `U/(U + K)`, with no
margin. The slackness inequality, the slack-floor bound, the dichotomy.

**Refuted.** That bounds on each trader's gain sum to a bound on the firm's: on sequences, a
mixture of finitely supported tables at weights `θ^R` meets the summed ceiling and has an
unbounded account exactly when `θ ≥ 1 − c` (`TableMixture`). That refutes the summation
argument; it is not a market. That the unit-stake equivalence
`WarrantSolvency.Schema.bounded_iff_frequency` survives market stakes. That item 138's
hypothesis was the thing to derive.

**Open.** Which disjunct holds in `FloorSchedule.market` on a truth sequence with infinitely
many false instances, and whether that depends on the firm's enumeration (item 138).
Efficiency of the buyer, and the converse of preservation where the frequency hypothesis fails
(item 139). An assessment driven by random observations (item 140). One trader's normalized
stake as a generable weighting (item 141).

## Matters

1. **The cost of finitely many failures — closed.** `Losses.headroom_le`, `Losses.account_ge`,
   `Losses.prior_ge`; tightness `Losses.compound_prior`, `Losses.compound_ceiling`; market form
   `DualCertifiedMarket.account_ge_of_losses`, `accountBounded_of_finite_losses` (registered
   `statistical.finite-losses-affordable`); witness `finiteLosses_witness`. The constant is
   `U((1 − c)^-(R+1) − 1)` with `R` the lost instances before the open one, and
   `U((1 − c)^-R − 1)` for the settled account. Proved directly, not from `reserve_bound`.
   Reopens if a dual-certified market with at most `R` false instances has an account below
   the bound, which the kernel excludes.
2. **Unit stakes and market stakes — closed as stated, unregistered.**
   `Stakes.unit_bounded_staked_unbounded`, `Stakes.unit_unbounded_staked_bounded`,
   `Stakes.abel_bound`. The property the equivalence needs is bounded variation of the stakes
   and of their reciprocals; `{1, 2}`-valued stakes already break it.
3. **Random outcomes — closed.** `ville_finite`, `ville`,
   `Betting.Fair.headroom_supermartingale`, `Betting.Fair.account_bound` (registered
   `statistical.capital-bound-probability`), `Betting.Fair.ae_bounded_below`; witness
   `Betting.witness`. No `γ`. The structure a market would need is stated in `THEOREM.md` §3
   and filed as item 140.
4. **The deterministic case.**
   (a) *One trader — open.* `Frequency.gain_bddAbove` and `Bridge.bridge` bound one staker's
   gain under a frequency hypothesis on its own weighting. That the normalized stake is a
   `PGenerableWeighting` is not proved; the reading is that division is harmless
   (`EF.safeRecip` is exact on a margin at least one) and the dependence on settled outcomes is
   the one obstacle. Item 141.
   (b) *The mixture — open at the level of the market; a living note at the level of sequences.*
   `TableMixture.stake_eq_tsum`, `table_prior`, `prior_eq`, `ceiling`, `prior_le` (registered
   `statistical.table-mixture-unbounded`), `prior_ge`. Individual bounds do not sum, and
   whether they do turns on the weight ratio against `1 − c`. The claim on record — a truth
   sequence pseudorandom above `c + γ`, an enumeration, and an unbounded account — is neither
   constructed nor excluded. The toy's E5 shows its shape over 32 days in a firm whose weights
   were chosen for it.
   (c) *An unbounded account is not exploitation — closed under the threshold frequency.*
   `stake_prices_le`, `account_ge_slack`, `accountBounded_of_eventually_slack` (registered
   `statistical.slack-floor-bounded`), `thresholdBuyer_exploits`, `bounded_or_buyer_exploits`
   (registered `statistical.bounded-or-buyer-exploits`). The non-circular statement is: a
   floor cleared by a margin from some day on costs a bounded account, whatever the sequence;
   and where the floor is not so cleared while the frequency near it is above `c + γ`, the
   buyer exploits. Under that frequency hypothesis and an efficient buyer, no logical inductor
   has a floor with an unbounded account. Without it, open.
   (d) *Item 139 — narrowed, restated in place.* Under the threshold frequency extraction
   holds and the exploiter is a buyer. What remains: the buyer's efficiency, and the case
   where the frequency near the floor is below the strength, where the candidate is still the
   seller of the multipliers.
5. **The toy — a living note.** `toy/floor_toy.py`, exact rationals, `--check` asserting the
   closed form of E2 and the constant price of E5. Table in `THEOREM.md` §5.
6. **What it means for a warrant.** `THEOREM.md` §6: vacuous is free, kept is credited,
   rebutted and retired are charged `c · mu`, undercut stops later charges and refunds nothing
   already demanded.

## The second opinion

`prompts/2026-11-12-statistical-conditions/REVIEW-astra.md`, on the request beside it. It
reviewed `StatisticalConditions.lean` at `743c5a8b` and ran the toy; it did not build Lean.

| finding | disposition |
|---|---|
| R1, R2, R3, R correct | — |
| R3: expressibility and rank do not give efficiency; `φ` unrestricted | already a hypothesis of the corollary; said in the ledger; item 139 (a) |
| g2: "the right criterion" is the conditional equivalence; `ComputableMarket` is separate | ledger of `THEOREM.md` §4 says so |
| g3 wrong: `Bridge.Frequency` is inhabited wherever the normalized stakes are summable | accepted. `bridge_frequency_iff_summable` added; item 138 restated; the registry note of `exact.conditional-bridge` is unchanged and its last sentence names the one witness given, not a necessity |
| g4: non-summable weights is stronger than "near the floor infinitely often" | wording corrected; the theorems state summability |
| X1: the gloss gave only the non-summable bound | corrected in `THEOREM.md` §4(a) |
| X2: tables are defined from `x`; no uniformly computable family or indexed enumeration | added to the ledger |
| h1 overstated: refutes the summation argument, not every account-bound theorem; no claim about the fixed firm | accepted; the judgment and the registry entry say "on sequences" and "the summation argument" |
| h2 overstated: E3 does not separate exactly the false days; E5 is 32 days; the hash is efficiently computable | accepted; `THEOREM.md` §5 rewritten |
| h3 overstated: no encoding justifies the index estimate; an effective enumeration cannot place the tables of an incompressible sequence at linear index | the estimate is removed from the record. Not accepted as a refutation of enumeration-dependence: a truth sequence settled by a computable deductive process is computable, so its tables are computable from `R` and an effective enumeration can interleave them; that is a reading, unproved, and item 138 (c) asks it |
| most damaging to R: the frequency assumption is endogenous and the exploitation horn remains | accepted; it is the judgment's second paragraph |
| most damaging to X: the stakes are not shown to satisfy the day inequality of the fixed firm | accepted; stated in the ledger and in "Refuted" |

## Statements that changed against the prompt

- Matter 1's constant is `(1 − c)^-(R+1) − 1` with `R` counting the lost instances before
  the open one, as the prompt guessed. A lost instance is one with `x < c`, not one that is
  "applied and false"; for truth values the two agree.
- Matter 1's tightness is on sequences: a staker under the per-day ceiling. It is not shown
  that a dual-certified market's multipliers realize it.
- Matter 3 uses optional stopping (`Submartingale.expected_stoppedValue_mono`) and Markov's
  inequality, not Mathlib's `maximal_ineq`, which is for nonnegative submartingales and bounds
  by the terminal value; the supermartingale form is not in the pinned Mathlib.
- Matter 4(a) is not proved in the dependency's sense. `Frequency.Along` is a new predicate
  on real sequences; nothing derives it from `PseudorandomAbove`.
- Matter 4(b) is decided for sequences and not for the market. No truth sequence
  pseudorandom in the dependency's sense is exhibited, and no enumeration.
- Matter 4's witness with truth values not all one has one false instance, not infinitely many.
- Matter 6's "undercut" is not free for a row already demanded.

## Deviations

1. The prompt says pull requests #145 and #146 both file items 136–138. #146 files 136–139.
   New items are 140 and 141.
2. Two new items are filed, of three allowed.
3. Matter 2's results are not registered: no filed item asks for them.
4. `Stakes` is in Lean over `ℝ` with explicit rational values, not in Python.
5. The second opinion was asked about the strongest result and the strongest refutation in
   one request; one further Lean lemma (`bridge_frequency_iff_summable`) was added after it
   and was not reviewed.
6. `checkers/graph.py` was run with `python3.12`; the machine's `python3` cannot parse it.
7. `state/prs.json` and `state/concepts.json` are not touched.
8. The toy lives in the round directory and is run by no runner.

## What this does not establish

- Any bound on the account of a floor market on a sequence with infinitely many false
  instances.
- That the second disjunct of the dichotomy occurs in a dual-certified market, or that it
  does not.
- That the outcome depends on the firm's enumeration. The sequence-level mixture and a
  32-day toy suggest it; neither is the pinned firm.
- `EfficientlyComputable` of any trader, or `ComputableMarket` of any market.
- Any connection to the pinned dependency's pseudorandomness definitions.
- Anything about conditions other than one floor per day on fresh sentences settled the next
  day.
- The probability bound for a market: `Betting.Fair` is about real-valued processes.
- Matter 6 is a reading of bet values against `settleOutcome`; no declaration relates the
  account to `WarrantEntitlement`.

## New names introduced (provisional)

`Losses.lost`, `Losses.compound`; `truthProcess`, `truthWorld`, `oneLoss`; `Stakes.alt`,
`Stakes.twoOnLoss`; `Frequency.Along`; `TableMixture.table`, `TableMixture.stake`; `clampEF`,
`thresholdFeature`, `thresholdWeight`, `thresholdBuyer`; `Betting.account`, `Betting.Fair`,
`Betting.coin`, `Betting.coinFiltration`, `Betting.coinOutcome`, `Betting.coinStake`. Registry
identifiers `statistical.*`. The namespace `StatisticalConditions.DualCertifiedMarket` holds
theorems about `ExactConditions.DualCertifiedMarket`.

## Items

Restated in place: 138 (which disjunct, from a hypothesis that does not mention the prices),
139 (the buyer's efficiency; the converse where the frequency fails). Filed: 140 (a floor
market driven by random observations), 141 (one trader's normalized stake as a generable
weighting). Registered against 138: `statistical.finite-losses-affordable`,
`statistical.slack-floor-bounded`, `statistical.table-mixture-unbounded`; against 139:
`statistical.bounded-or-buyer-exploits`; against 140:
`statistical.capital-bound-probability`. Decision:
`2026-11-12--statistical-floor-as-threshold-dichotomy`, agent-decided, reversible.

## Gates

Run on the tree at `b5399e2b`, before this section was filled in.

- `~/.claude/scripts/safe-lake.sh build Workspace`, from `lean/`: `Build completed successfully`.
- `python3.12 tests/audit_axioms.py`: `AXIOM AUDIT: 4051 results across 128 files, all within
  ['Classical.choice', 'Quot.sound', 'propext']`.
- `python3.12 tests/run.py`: `ALL GREEN (80 project(s))`. It skips the Lean build unless
  `WORKSPACE_LEAN=1`; the build above is the separate run.
- `python3.12 -m checkers.graph --root .`: `OK 2627 nodes`. `python3 -m checkers.workspace_state
  --check`: valid, 215 modern claims, 153 priorities. `python3.12 -m checkers.run`: 110 entries
  in the normativity registry, schema ok.
- `python3 toy/floor_toy.py --check`: `check: ok`.
- No file under `checkers/`, `tests/`, `.github/` or `graph/policy.yaml` is changed.

## Outstanding maintainer actions

None reserved. The pull request is stacked on #146 and says so; nothing is merged and
auto-merge is off.
