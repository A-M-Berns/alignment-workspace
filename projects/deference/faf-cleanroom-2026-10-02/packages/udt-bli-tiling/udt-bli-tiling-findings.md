# `udt-bli-tiling` — findings

Findings about the sources ([STANDARDS](../../STANDARDS.md) §5), each with a severity (blocking the note's conclusion / local error / imprecision / presentation) and a pointer. The mandate's §5 items are F1–F9 below (in its order); F10–F15 are this run's. Where a finding is about what a person meant it is marked ATTRIBUTION-UNVETTED. All Lean names are in `Cleanroom.Bli.UdtBliTiling` (sub-namespaces `GapTiling`, `MuggingTiles`, `SingleCoin`, `FairLayer`, `CorrFullBit`).

## F1 — The program's U9(3) witness is null-mass; the honest failure is `gapPrior` (local error in `bli-program` §3.9 U9(3); core finding F-4 re-cited; proved)

`bli-program` §3.9 U9(3) says: "It **fails without `IndependentPoints`** — witness: two tables of mass ½, policy points perfectly correlated across tables (…), `V(a,b) = 1.5 > 1 = V(b,b)`: the prior strictly prefers precommitting `a` at `T₁`." On that prior the policy `ab` has ex-ante mass `0` (core `Corr.policyMass_ab`), so `V(a,b) = 1.5` is the array formula `sepValue`, not `𝔼[U | pp = ab]`, which is the junk `0`. The sentence is true of the full-support correlated prior `gapPrior` (`aa, bb ↦ 2/5`, `ab, ba ↦ 1/10`): `GapTiling.gap_not_noStrictPrecommitAt` proves `𝔼[U | pp = bb[T₁ ↦ a]] = 3/2 > 1 = 𝔼[U | pp = bb]` with every policy positive, and `gap_hypothesis_audit` that exactly `IndependentPoints` (and the derived `NoCrossBranch`) is what fails there. Severity: local error (the program's witness does not inhabit its own definition); the claim survives on the repaired witness. Pointer: `GapWitness.lean`; core `WitnessGap.lean`, core findings F-4.

## F2 — sist's iterated mugging is parallel, not sequential; the sequential tree is built here (sist finding F17; presentation; built)

`udt-bli-sist`'s `Iter.iterPrior` puts each world at one node with that node's payoff, so `{Ask_k, Rec_k}` is inert at `Ask_k` and the class-cut applies. The single-coin model of bli-soto-a-084 is the *sequential* tree: one coin, every round played, the utility summing every round. `SingleCoin.scPrior` builds it (same index and tables as `Iter`, base `(coin, now)`, utility `payoff(coin) · ∑_k γ_k [π Ask_k] + r₀`); the class `{Ask_k, Rec_k}` is not inert there (the other rounds' points enter every branch), so the verdict is computed by direct product-law algebra (`SingleCoin.EU_diff`), not by `Iter.classInert_node`. Pointer: `SingleCoin.lean` module docstring.

## F3 — Theorem 2's proof supports only the fixed-point form; Policy Coordination "abuses" ties (bli-paper-006/007 flags; [udt-paper-tiling-findings](../udt-paper-tiling/udt-paper-tiling-findings.md); cited, not re-proved)

T5 states the layered form over the run's `PolicyFair` (`layered_oneStep_tiles_of_independent`) and the reduction "procedure-level tiling ⟺ policy-level optimality of the effective behaviour" (`layered_tiles_iff`); it does not re-prove the paper's Theorem 2, whose Lean of record is `udt-paper-tiling`'s `thm2_udt10_tiling` (fixed-point form). Policy Coordination is not used anywhere in this package: over a BLI prior with independent points its role is played by `IndependentPoints ∧ LocalUtility` (the per-point argmax is the global argmax, `Independent.lean`). Severity: presentation. Pointer: `Layered.lean` module docstring.

## F4 — Desideratum 2 as stated is one-level only; T1 is its finite one-level shadow (bli-soto-a-024; imprecision; disclosed)

bli-soto-a-024's "at a node offering an action `a` followed by `k` forced actions implementing a fixed finite policy `b̄` … for late enough `i` the UDT `A` does not strictly prefer `a`" needs a sequential tree and an inductor. `NoStrictPrecommitAt` is the one-level finite form (`Fidelity: weaker` on `oneStep_tiles_of_independent`); the `k` forced actions are the rounds of `SingleCoin.lean`, where the same predicate is evaluated (`refreeze_not_noStrictPrecommitAt`); "late enough `i`" has no counterpart here (no inductor in this package). Pointer: `Defs.lean` (`NoStrictPrecommitAt`), `Independent.lean`.

## F5 — "Tiling iff decisions coincide" is too strong by ties; "D1 holds iff 𝙿 never updates" is true over the model class in a stated reading (bli-soto-a-2-016, bli-soto-b-034; imprecision; proved)

(i) bli-soto-a-2-016 (Soto's conjecture, ATTRIBUTION-UNVETTED as his): "`P` satisfies the tiling desideratum with respect to `P_σ` only if `P_σ`'s decisions coincide with `P`'s on the tree." Over a separable prior (`NDPOLICY ∧ ReflectivePolicy ∧ LocalUtility`), `noStrictPrecommit_iff_updateful_of_separable` proves: no strict preference for precommitment ⟺ the policy's decision is an updateful (= one-step) choice at every positive table, *ties allowed*; `MuggingTiles.tie_witness` exhibits two policies with different decisions (at `Rec`), equal value, both tiling. The tie-aware reading is what the source needs; "coincide" is too strong by exactly the tied tables. (ii) bli-soto-b-034's "D1 holds iff 𝙿 never updates": over the model class `IsRefrozen Σ t` of the single-coin mugging, `SingleCoin.stability_iff` proves "no strict preference for precommitment ⟺ the two-step decisions from `t` on agree with the one-step decision (pay) at every round `k ≥ t`"; with `Σ = {coin}` this is `K ≤ t` (`stability_coin_iff`), with `Σ = ∅` it always holds (`stability_empty`). So "never updates" must be read as "the re-freeze changes no one-step decision at a positive-stake round" — the formalizer's reading, ATTRIBUTION-UNVETTED; under the literal reading "the re-frozen prior differs from the frozen one" the statement is false (`Σ = ∅` re-freezes and tiles; the `{coin}` re-freeze with `K ≤ t` differs as a prior and tiles). Severity: imprecision. Pointer: `Defs.lean`, `MuggingTiles.lean`, `Refreeze.lean`.

## F6 — Don't-outthink-Omega is ill-posed until Omega's read is modelled: the two readings have opposite verdicts (bli-soto-b-2-024's own flag; imprecision; both readings proved)

The slogan "think exactly as long as Omega" is a statement about Omega's read of the agent, which the journal line does not fix. `Omega.lean` builds the minimal instance (depth = the class structure `Σ`, with `Σ = ∅` meaning constancy): under (R1), Omega reads the agent's actual `Ask` point (`muggingPrior r`), and the ex-ante optimum is attained by a constant policy (`Omega.r1_coarse_optimal`) — the slogan holds; under (R2), Omega reads the coarse `Other` point (`Omega.muggingPrior2 r`), and the non-constant "refuse at `Ask`, pay at `Other`" is prior-optimal and strictly beats every constant policy (`Omega.r2_outthink_optimal`) — the slogan is false. Neither reading is attributed to the journal beyond the quoted line (ATTRIBUTION-UNVETTED). Severity: imprecision (the source's). Pointer: `Omega.lean`; mandate T7.

## F7 — D7 "under very weak assumptions" and 023's exploration-safety step are unstated (bli-soto-b-034, bli-soto-a-023; recorded)

Not formalized: no statement exists to formalize. D7 ("LIDT learns to rewrite to UDT") needs an LIDT over FAF's `History`, which no package in this run builds; 023's sketch licenses ε-exploration by catastrophe-freeness without connecting entanglements to exploration safety (the inventory's flag). The one-level observation this package can make (T9): on `SingleCoin.scPrior`, before the coin is decided the one-step (updateful-on-nothing) choice is UDT's (`isOneStepChoice_pay`), after it the coin-conditioned choice is not (`isTwoStepChoice_refuse`) — the dilemma again. Severity: imprecision. Pointer: `SingleCoin.lean`.

## F8 — Attribution: "Soto's impossibility", "Soto's conjecture", "the author's tiling aim" (ATTRIBUTION-UNVETTED; names carry hypothesis classes)

No declaration in this package carries a person's name. `gap_not_noStrictPrecommitAt` is the failure without independence; `refreeze_dilemma` is the two-sided dilemma on the single-coin model; `noStrictPrecommit_iff_updateful_of_separable` is the tie-aware separable characterization. Where a docstring quotes bli-soto-a-2-016/017 it says so and marks the attribution. Pointer: every docstring's `Source:` line.

## F9 — `bli-exactness` (X1) is not built: the Vingean OPEN can only be recorded in prose (mandate §5 item 9; recorded)

Faith in the prior's *own* argmax over a BLI built on an inductor is a reflection statement about 𝙿's large sentences; neither the exact form nor its δ-smoothed asymptotic form can be stated over this run's objects while `bli-exactness` has no `run/wp` directory (2026-10-01). No `sorry` is written for it. The finite half, T6(i), is built in corrected form (F13): Theorem 3's own hypothesis `FaithInJointArgmaxPrior` fails on the mugging prior at the cross table `(Rec, Ask)` (`VingeanMugging.not_faith_rec_ask`). Pointer: mandate T6; `bli-program` §3.9 U9(5); `Vingean.lean`.

## F10 — The mandate's suggested N+ for T5 does not inhabit T1's package (mandate T5; local error in the mandate; repaired)

The mandate's N+ for the layered form is `layerOf fairU` (core). On `layerPrior fairU` only the two constant policies have mass, so `NDPOLICY` fails (`FairLayer.not_in_package`) and so does `IndependentPoints` (the two points are perfectly correlated) — it is not in T1's package. It *is* the N+ of the general layered lemma `layered_tiles_iff` (`FairLayer.fair_layer_tiles`: two procedures of equal `eff`, both tile). The N+ of record for the composition with T1 is the new implementation-bit layer `withBit corrDataFull` / `bitLayer` (`CorrFullBit.tiles`): the full-support independent prior with a fair implementation bit the utility ignores, two implementations `(ab, true)`, `(ab, false)` of the one-step behaviour, fairness proved (`policyFair_bitLayer`), T1's package transferred. Severity: local error (mandate). Pointer: `Layered.lean`.

## F11 — The mandate's instance numbers "45 and 20" do not occur at one re-freeze day (mandate T4 witness; local error in the mandate; corrected)

With `(c, V) = (10, 100)`, `q = 1/2`, `K = 3`, `γ ≡ 1`: `gain = 45` per round (`inst_gain`). Re-freezing from round `t = 1` on (rounds `1, 2` re-frozen) gives the frozen gap `90` and the re-frozen gap `20`; from `t = 2` on, `45` and `10` (`inst_dilemma`). The mandate's pair `(45, 20)` mixes one re-frozen round for the frozen side with two for the re-frozen side. Severity: presentation (mandate). Pointer: `Refreeze.lean`.

## F12 — bli-soto-a-084's inequality names the coin's sides opposite to this model (imprecision; disclosed)

bli-soto-a-084 (as inventoried): "the prior-optimal policy pays forever iff `q·100 > (1−q)·10`". In `SingleCoin`, `q` is the probability of the *asking* branch (coin true ⇒ Omega asks for `c`), so the condition is `V(1−q) > cq`, i.e. `q < V/(V+c) = 10/11` (`gain_pos_iff`), which is `bli-program-desiderata` I10's "`q < 10/11`". The source's inequality is the same statement with `q` the probability of the paying branch. Severity: presentation. Pointer: `SingleCoin.gain`, `gain_pos_iff`.

## F13 — The mandate's T6(i) is false as stated: `FaithInJointArgmaxPrior (muggingPrior r) univ askT askT` holds; the obstruction is at `(Rec, Ask)` (mandate T6(i); local error in the mandate; both proved)

`FaithInJointArgmaxPrior P A' o o'` (paper-tiling) quantifies over positive pair cells `pairMass o o' a a'`. With `o = o' = askT`, the only positive cells are `a = a'`, where `cellEU askT askT a a = EU askT a ≤ EU askT true`: the predicate holds (`VingeanMugging.faith_ask_ask`), and `row_flat_of_fjaPrior` gives only the tautology `cellEU askT askT true true = EU askT true`. The mandate's "the row is not flat: `EU askT true ≠ EU askT false`" confuses the row across actions with the joint cell. Where Faith in Joint Argmax genuinely fails on the mugging is `o = recT`, `o' = askT`: `cellEU recT askT a true = EU askT true = 441/10 + (2/100) r pay` (`cellEU_rec_ask`: the utility reads only the `Ask` point) exceeds every `EU recT b = ½ (EU askT true + EU askT false)` (`EU_rec`) for `|r| ≤ 10`, so no `b` dominates the cell (`VingeanMugging.not_faith_rec_ask`). Severity: local error (mandate). Pointer: `Vingean.lean`; paper-tiling `Vingean.lean` (`FaithInJointArgmaxPrior`), core `Mugging.lean`.

## F14 — The two-step rule at Σ is the one-step rule of the Σ-conditioned prior (new identification; proved)

`conditionOn_EU_eq_twoStepEU`: `(P | sigmaClass Σ Q).EU Q a = twoStepEU P Σ Q a` (shown on the single-coin model at `Σ = {coin}`; the general form over any `P` is the same two-line proof and is a natural API request for `udt-bli-sist`'s `Defs`). This makes mandate §3.4's "the re-frozen agent is the two-step rule" and "the prior re-frozen at 𝒞 is `conditionOn 𝒞`" one object, and is what `refrozen_isOneStepChoice_conditioned` uses. Severity: presentation (a clarification of the sources' vocabulary). Pointer: `SingleCoin.lean`.

## F15 — Per-item disposition of the mandate's sources

| Item | Disposition | Where |
|---|---|---|
| bli-paper-006 (Policy Coordination) | recorded only (not used: independence plays its role over a BLI prior; F3) | `Layered.lean` docstring |
| bli-paper-007 (Theorem 2) | headline (layered form `layered_oneStep_tiles_of_independent`; the paper's own statement cited from `udt-paper-tiling`) | `Layered.lean` |
| bli-paper-050 (the conjecture) | recorded only (its provable form is `bli-witness-lia`'s stretch) | this file |
| bli-soto-a-016 (self-trust) | headline D + L (`SelfTrustAgainst`, `selfTrust_is_refreeze_gap`) | `Defs.lean`, `Refreeze.lean` |
| bli-soto-a-017 (LIDT ↔ UDT outlines) | recorded only (the outline's steps map onto T1's lemmas; the LIDT half needs an inductor) | `Independent.lean` docstring |
| bli-soto-a-023 (Desideratum 1) | recorded only (F7) | this file |
| bli-soto-a-024 (Desideratum 2) | headline (one-level shadow, F4) | `Defs.lean`, `Independent.lean` |
| bli-soto-a-2-016 (Soto's conjecture / tiling aim) | headline (tie-aware separable form; the model-class iff) + finding F5 | `Defs.lean`, `Refreeze.lean` |
| bli-soto-a-2-017 (re-frozen priors) | headline (`refreeze_dilemma`) | `Refreeze.lean` |
| bli-soto-a-084 (single-coin iterated mugging) | headline (the model; `EU_diff`, `gain_pos_iff`) + F12 | `SingleCoin.lean` |
| bli-soto-b-034 (Desiderata 0–8) | D1: headline (`stability_iff`, `stability_coin_iff`, `stability_empty`); D2: core's `good`; D0 "trivial form": the N+ rows of `MuggingTiles` and `SingleCoin`; D7: recorded (F7); the rest recorded | `Refreeze.lean`, `MuggingTiles.lean` |
| bli-soto-b-038 (locks in) | witness (`frozen_prefers_payAll`, `priorOptimal_payAll`) | `Refreeze.lean`, `SingleCoin.lean` |
| bli-soto-b-045 (tiling outline) | lemma map (module docstring of `Independent.lean`) | `Independent.lean` |
| bli-soto-b-2-024 (don't outthink Omega) | headline (stretch): both readings proved with opposite verdicts (F6) | `Omega.lean` |
| bli-soto-b-2-025 (reactables vs seeables) | recorded only: in the dictionary "reactables = `↥𝒟`, seeables = what `EU` reads", (iv)'s tiling requirement on seeables is T2's phenomenon (the one-step rule reacts to its own `EU`, a seeable that is not a reactable, and loses to a precommitment on the correlated prior) | this file |
