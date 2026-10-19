# Report — 2026-10-20-warrant-enforcement-semantics

| | |
|---|---|
| Prompt author | the maintainer (`prompts/2026-10-20-warrant-enforcement-semantics/PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Lean | `lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean` (one file, 255 declarations audited, three allowed axioms, no `sorry`) |
| Fixture | `src/fixture.py`, `src/licence.py`, `src/record.py`; `tests/run.py` (37 checks, exact rationals) |
| Registrations | `warrant.*` in `projects/normativity/CLAIMS.md`, the chain lemmas against item 56 |
| Filed | `PRIORITIES.md` items 112–116; item 56 narrowed |
| Base | `main` at the merge of PR #128 (`2b7a1453`) |
| Date | 2026-10-20 |

**Verdict.** ONE-DEFEASIBLE-WARRANT-IS-ENTITLED-AT-THE-ODDS-UNDER-EVERY-SETTLEMENT-SEMANTICS-WHILE-A-SLACK-WORLD-IS-LIVE-THE-FORK-COLLAPSES-IN-THE-ACCOUNT-THE-ORPHANED-STRENGTH-ROW-IS-THE-ONE-UNAFFORDABLE-CASE-ITEM-39-IS-WEAK-AND-THE-LICENCE-CHAIN-HOLDS-WITH-BOTH-CONVERSES-FAILING. The gloss is in `README.md`.

**Depends on** `2026-08-16-traderized-enforcement` (the force algebra and the enforcement-preservation composition), `2026-09-07-final-pressure-pass` (the conditional Normative Inductor theorem), and the unmerged `round/2026-09-16-seed-statics` as a *source* (Part 0; not a base, not merged).

## The finding in one paragraph

A warrant with strengths strictly inside `(0, 1)` excludes live worlds as *points* of its region — that is what makes it normative rather than logical — and the enforcer that holds it is exposed at exactly those worlds. The round's result is that this exposure is bounded by the **odds** of the warrant, not by its intensity, its tolerance or how long it is held: the enforcer's assessed net worth at any live world is at least `−(1 + 2) · ρ`, where `1` is the market maker's constant, `2` the trading firm's budget floor, and `ρ` dominates, row by row, every live world's deficit by some live world's surplus (`netWorth_ge_neg_odds`). For the fixture's three rows the least such `ρ` is `max_j c_j/(1 − c_j)`, the largest odds the warrant states. The argument follows one world across dates (the item-40 shape), where the force interface's own certificate `Σ_t (ε_t + C_t) D_t/δ_t` maximizes date by date; that is why the one is a constant and the other a sum. The three settlement semantics of the dispatch are three live-set schedules of one assessment process, and the bankroll is the same under all three as long as a slack world is live. When the slack world dies, two things can happen: the region empties and force is withheld (the premise row guards the chain), or — after the applicability port has been defeated — the region stays nonempty with no slack world, the strength row contraposes, and an efficiently computable buyer drives the enforcer's net worth to `−∞` on a convergent budget. That last case is the round's one refutation, and it is a fact about per-row defeat and linear strength rows, not about any settlement semantics.

## Corrections to the prompt (`AGENTS.md` §8)

1. `GateIsLegitimacy` and `ReasonMediatedAuthorship` are in `lean/Workspace/Deference/Contrib/`, not under Normativity. They are imported and cited only; the deference line's Lean is untouched.
2. `deductive_end_to_end` (`DeductiveEffective.lean`) has **no row or region hypothesis**: its region is `DeductiveRegion.deductiveRegion (DP.D n) (coords n)`, built from the plausible worlds themselves, so a genuine warrant cannot be stated in it at all. The admissibility hypothesis a warrant fails is `hadm` of `compiled_end_to_end` (`NormativeInductorComposition.lean`) and of `Evaluation.deductive_normative_inductor` (`NormativeInductionInterface.lean`): every plausible world's payout lies in the compiled bundle's region. The boundary of the deductive case is that hypothesis (B(i)).
3. B(ii)'s expected outcome — liability unbounded when the evaluation is unconstrained by the warrant — is **refuted**; the bankroll is independent of the evaluation (B(ii) below).
4. B(iii)'s "the enforcer is settled on nothing" is not expressible in the pinned substrate: a `PCWorld` assigns every sentence a truth value, so a security that never settles is one both of whose values stay live forever. That is evaluation settlement at `n_E = ∞`, and the account treats it identically (B(iii)).
5. P1's "the region compiled from `G` contains `v`" is read with a verdict as a **value** for the coordinate (a point in the forced interval), which is what A4's "two verdicts inside `[a, b]`" requires. `Supported` then needs two cited bound certificates plus their attained endpoints, and `Supported → Admissible` is a theorem by rational convexity (`region_convex`), not a projection.
6. The branch distance "96 commits behind `main`" is exact (`git rev-list --count`).

## Part 0 — the port

Ported onto this branch, inside `WarrantEntitlement.lean`, against current `main`: `truth`, `Settlement` (with `Pinned`, `le`, `empty`, `pinRowsAt`, `pinRows`, their satisfaction lemmas), `settledTerm`, `specialize`, `specialize_sat_iff`, `Form` with `Form.c`, `Form.row`, `premise_sat_iff` and two new satisfaction lemmas (`applicability_sat_iff`, `strength_sat_iff`), `SubItem`, `StrKind`, `StrItem`, `Constitutive`, `Seed` with `liveSub`/`liveStr`, `DocketState` with `quiet`, `Cite`, `pinCited`, `forcedBundle`, `forcedRegion` with `forcedRegion_iff_check`, `forcedRegion_iff`, `forcedRegion_anti`, `LowerBound`, `UpperBound`, `IsForcedInterval` with `le`/`unique`/`mono`, `widenSeed`, `defeat_widens`, `allowed_sat`, `BoundCert` with `value`, `sound` and the new `sound_of_pos`, `lowerCert_bound`, `upperCert_bound`. Three small additions the branch did not have: `DecidableEq` on `Form`, `SubItem`, `DocketState`, `Cite` (the licence chain's decidability needs them), a `Decidable` instance for `forcedRegion`, and `BoundCert.sound_of_pos`.

Not ported, deliberately: the elimination section (`forcedInterval` by Fourier–Motzkin), `Pins`, `Refuted`, `leverage`, `SureLoss`, the Farkas support lemma, confinement, seed-independence, transport, stabilization, humility, and every fixture of the branch. The port compiled on the first build against `main`'s `Row`/`Bundle`/`FarkasCert` API with no change to any ported statement. Cost recorded as item 116: when PR #102 lands, these declarations exist twice in two namespaces and one copy must go.

## Part A — the licence chain

`LICENCE_CHAIN.md`. The typed warrant `Occurrence` (identity, `Form`, cited applicability claim, source, defeat set). Verdicts are values. `Admissible`, `Supported` (a `VerdictCert`: lower and upper `BoundCert`s whose positive-multiplier rows are cited by occurrence into the live bundle, with attained endpoints), `Licensed` (supported on the record's grounds and the issuing event authorized). `licensed_supported`, `supported_admissible`, `licence_chain`; `Supported.valid` says a supported certificate's endpoints are valid bounds, so citation is not merely a typing discipline. A3: `Countermodel.admissible_not_supported` — two occurrences with the same row, the region unchanged by defeating one (`region_unchanged`), the stale certificate unsupported, the fresh one supported. A4: `Countermodel.supported_not_licensed` — two verdicts inside `[1/2, 1]`, both supported, one licensed and one not by the record's authorization; `selection_not_transparent` instantiates `GateIsLegitimacy.tiebreak_transparency` on the selection event with two parties and two continuations. Registered against item 56 as `warrant.licence-chain`, `warrant.supported-admissible`, `warrant.admissible-not-supported`, `warrant.supported-not-licensed`, `warrant.selection-not-transparent`.

## Part B — the fork

`SETTLEMENT_FORK.md`. The enforcer is `warrantEnforcer sched : AdaptiveTrader`, the force layer's `enforcementStrategy` on a date-indexed `Presentation`; the realized enforcer plays exactly it (`realizedEnforcer_strat`). `day_value_eq` resolves a day's value at a world into units-weighted signed gaps plus intensity-weighted squared violations. The bankroll theorem `netWorth_ge_neg_odds`, its liability form `liability_of_odds`, and the composition `warrant_normative_inductor` against `Evaluation.conditional_normative_inductor`'s actual signature, with `B = 3ρ`. The world-inclusive case is `netWorth_nonneg_of_inclusive` (`B = 0`). The withheld tail is `netWorth_eq_of_tail_zero`.

The fixture `Fixture`: `X, X∧A, X∧A∧Y, Y`; strengths `c_P, c_A, c_S`; the bridge `toForceRow` from a seed row to a force row with `toForceRow_gap`; `stage`/`dp`/`L` — `X` from `n₁`, the declared evaluation of `Y` from `n_E` (`Y` or `¬Y`); `gap_dominated` at every propositionally consistent world; `liability` (affirming evaluation, every `n₀, n₁, n_E`), `liability_disagree` (disagreeing evaluation, force withheld from `n_E`); `disagree_region_empty` while the applicability row is live; `orphan_region_nonempty` and `orphan_no_slack` after its defeat. The witness `Witness.fixture_liability`: strengths `4/5, 3/4, 2/3`, odds `4, 3, 2`, bankroll `12`, at `n₁ = 3, n₀ = 5, n_E = 8`, intensity `10`.

Per semantics, in one line each (the full table is in `SETTLEMENT_FORK.md`):

- **(i) deductive.** World-inclusive rows cost nothing and are a logical fact wearing a strength (`B = 0`, `hadm`). A genuine warrant fails `hadm` and is affordable at `B = 3ρ` while a slack world is live; `X` settled at `n₁` changes nothing.
- **(ii) evaluation.** `B = 3ρ` whatever the evaluation says. A disagreeing evaluation realizes the deficit, empties the region while the premise and applicability rows are live, and force is withheld; the loss incurred is at most `B`. The only working `B` does **not** presuppose the evaluation satisfies the row.
- **(iii) pegged.** The same object as (ii) at `n_E = ∞`; every clause of the criterion survives with `B = 3ρ`; no clause fails on any trader.
- **(iv) the defeater.** At `n₀` the applicability row leaves (`defeat_widens`); the units already bought stay on the book and pay out at the eventual world — not recovered, absorbed by `B` (its own share is `3 · c_A/(1 − c_A) = 9`); no new liability on that row. The hazard: the defeat removes the chain's guard, and a later refutation of `Y` leaves the strength row an orphan pin with unbounded liability (`COUNTERMODELS.md` §3; `src/fixture.py::harmonic_buyer_run`).
- **(v) item 39.** Weak under all three: the warrant's `K_t` excludes live worlds as points and adds nothing to liveness, which is settlement's. The requested pair of credal sets is exhibited (`same_projection_different_support`: `A` is invisible when `X` is false). Strong would be world-inclusion, i.e. `B = 0`, i.e. the logical case.

## Part C — the record

`RECORD.md`. `MarketRun` (grounds, docket, settlement, certificate events, authorized events, prices), `RecordEntry` (record state, certificate events, enforcer position; no prices), `Record`, `trace`, `positionOf` with `positionOf_eq_position`. On the countermodel: `trace_not_injective`/`trace_not_injOn` (two prices clearing the row, one record), `trace_not_const`/`trace_not_constant` (a defeat shows), `price_not_mediated` and `docket_mediated` (the record mediates the docket, not the price), `decideLicensed_iff`. Stopped there as instructed; items 115 and 116 carry what it made visible.

## The six questions

1. **Under which semantics does a bankroll exist, as a function of what?** Under all three, `B = 3 · max_j c_j/(1 − c_j)` — the market's capital `1 + 2` times the warrant's largest odds — provided a live world clears every enforced row with surplus dominating every live deficit at those odds; for the fixture that is the all-true world while `X∧A∧Y` is not refuted. Intensity, tolerance, `n₀`, `n₁`, `n_E` and the horizon do not enter. Where no slack world is live and the region is nonempty, no `B` exists (the orphan pin).
2. **Does the only working `B` under evaluation settlement presuppose the evaluation satisfies the row?** No. `Fixture.liability_disagree` holds the same `3ρ` when the evaluation says `¬Y`; the enforcer pays out at most `B` and force is withheld on the emptied region. What the bound presupposes is that the agreeing world is *live until the evaluation lands* — that the evaluation is not foreknown — not that it agrees.
3. **Is item 39 strong or weak?** Weak under all three. Strong coincides with world-inclusion and zero liability, the deductive-logical case.
4. **What does `Licensed` need from the record that the region cannot supply?** Two things, and this is the content of item 56: the **citation by occurrence identity** of every positively weighted row of the certificate (the region is unchanged by defeating one of two duplicating occurrences, so no region-only licence can see the defeat — A3), and the **authorization of the issuing and selecting event** (two verdicts in the same interval are both supported; which one is taken is a transparency fact of the record — A4). Both are decidable from the record (`decideLicensed_iff`) and neither from prices.
5. **Which of M1's two forms does each semantics realize?** All three realize the constraint form: a row is a standing position in the priced sentences it names. Under (iii) the same row is a position in a security that never settles, and the account cannot tell the two forms apart — a constraint on a priced sentence *is* a position in that security. Under (iii) nothing is ever answerable to a fact, so the row's only effect is on the market's response (the price); "obligation to respond" is the only coherent reading there. Under (i) and (ii) the row is also a claim that settles.
6. **Reserved to the maintainer.** Below.

## What this round does not establish

- The bankroll theorem's slack hypothesis is checked for the fixture at every propositionally consistent world; for a general presentation it is a hypothesis, and the round does not characterize when a region admits a slack live world.
- The orphan-pin unboundedness is `test-supported`: the harmonic buyer is run against a one-coordinate market maker that zeroes the aggregate, one valid selection under the maker's contract, not the pinned dependency's `MarketMaker`. The Lean proves the preconditions (nonempty region, no slack world, a live deficit world) and not the divergence (item 114).
- `enforcer_netWorth_lt_three` uses the trading firm's floor `−2` from `AssessmentFirm.tradingFirmTrader_netWorth_floor`; the constant `3` is that dependency's, not a property of warrants.
- Nothing here is about efficient computability of the enforcer or computability of the augmented market: `warrant_normative_inductor` keeps `computableMarket` and the uptake certificate as hypotheses, as `conditional_normative_inductor` does.
- The seed statics' real-valued and elimination results were not ported; the forced *interval* of a fixture is stated and proved by hand (`Countermodel.forcedInterval`), not computed.
- The port's one deviation from the branch — `Decidable` instances and `sound_of_pos` — changes no ported statement, and the round did not re-verify the branch's unported theorems against `main`.
- The item-39 pair uses an atom invisible on the fragment; on the four priced sentences themselves no two distinct credal sets share a projection at a point mass, so the weakness exhibited is the fibre-saturation one (`SEMANTIC_PROJECTION.md` §3), and the stronger statement is the point exclusion.

## Items filed

112 (occurrence-level defeat, the orphan pin), 113 (settlement defeat for strength rows: linear rows contrapose), 114 (the pinned-region divergence against the pinned market maker; item 40 narrowed), 115 (`Licensed` transport over record transitions, the rest of item 56), 116 (the record as reason trace: what it mediates, the defect, and the port's duplicate when PR #102 lands). Item 56 carries a dated narrowing.

## Candidate registrations, listed and not registered

All `lean-proved` on `main` at this branch, against item 39 unless noted: `WarrantEntitlement.netWorth_ge_neg_odds`, `liability_of_odds`, `warrant_normative_inductor`, `netWorth_nonneg_of_inclusive`, `Fixture.gap_dominated`, `Fixture.liability`, `Fixture.liability_disagree`, `Fixture.disagree_region_empty`, `Fixture.orphan_region_nonempty`, `Fixture.orphan_no_slack` (item 112), `RecordFixture.trace_not_injOn`, `trace_not_constant`, `price_not_mediated`, `docket_mediated`, `decideLicensed_iff` (item 116). The dispatch registers only the chain lemmas.

## Names, provisional

*settlement semantics* (the fork's parameter), *bankroll schedule* (`B`), *entitlement* (the row may be enforced at bounded liability), *odds bankroll* (`3ρ`), *slack world* (a live world clearing every enforced row strictly), *orphan pin* (a nonempty region with no slack world left by a per-row defeat), *verdict certificate* (`VerdictCert`), *cites live* (`CitesLive`).

## Outstanding maintainer actions

1. **Confirm, amend or strike M1** — `DECISIONS.md`, *Awaiting the author*, the entry of 2026-10-20. The round's reading: the two forms coincide in the account for a never-settled sentence.
2. **Rule on the settlement fork (M2)** — `DECISIONS.md`, *Awaiting the author*, the second entry of 2026-10-20. The round finds the fork collapses in the account; what remains open is whether a *pegged* semantics the substrate cannot express is wanted, and whether linear strength rows that contrapose under settlement are acceptable or the warrant form changes (item 113).
3. **Merge.** Reserved on the pull request, not here.
