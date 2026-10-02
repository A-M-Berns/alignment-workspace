# lit-ddb-facts — ledger

Package `lit-ddb-facts` (faf-cleanroom run, 2026-09-29/30). One row per headline ([STANDARDS](../../STANDARDS.md) §6); supporting lemmas have no row. All declarations live in `Cleanroom.Lit.LitDdbFacts` (witnesses in `.Examples`); files under `Cleanroom/Lit/LitDdbFacts/`. Kinds: P proved · C composition · L plumbing · D definition of record · N+/N− witness · OPEN stated, not proved. Every theorem's only hypothesis beyond its antecedent is `hπ : π ∈ stdSimplex ℝ W` or its nonnegativity half (a); **no (b) or (c) hypotheses anywhere in the package** — the one OPEN statement (`prior_trust_value_all_nested_open`, Target 17) is a conjecture of the package's own, not a hypothesis of anything; the two OPEN rows of rounds 0–1 ("on prior frames Trust ⟹ Value", DDB's paraphrase of Dorst 2020a 7.4) were **false** and are refuted (Target 17, findings F15). Status `proved` means built and gate PASS (see the report's "State of the package"). Rows marked *(r1)* / *(r2)* were added or changed in repair round 1 / 2 (see the report's "Repair round 1" / "Repair round 2").

## Target 1 — Reflection forces immodest candidates (`Reflection.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `selfMass_eq_one_of_reflects` | §1 l. 80, fn 11 | Reflection ⟹ every candidate has `ρ(P = ρ) = 1` | P | exact | — | `Examples.dup3_reflects` (immodest, duplicate rows, N+); `fig3_not_reflects` (frames) | proved |
| `newReflects_of_reflects`, `reflects_iff_newReflects_of_immodest`, `reflects_iff_newReflects_of_immodestFrame` | §1 l. 89, fn 17 | Reflection ⟹ New Reflection; on immodest candidates / frames they coincide | L | exact | — | `dup3_all` | proved |
| `not_reflects_of_modestAt` | §1 l. 80 | a deferrer leaving a modest world open does not reflect | L | exact | — | fig3 | proved |

## Target 2 — New Reflection is Reflection of the informed expert (`Reflection.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `informedCell`, `InformedReflects`, `InformedReflectsSimplex` | §1 l. 97, fn 12 | `[P̂ = σ]`; the informed version over all vectors `σ` / over distributions only | D | exact (all-`σ` reading, see F7) / variant | — | `Examples.not_informedReflects_πneg_dup3`, `not_informedReflectsSimplex_πneg_dup3` (each refuted on `dup3`, N+, r1) | proved |
| `informedCell_informed` | fn 12 | `[P̂ = P̂_ρ] = [P = ρ]` at a positive self-cell | P | exact | — | — | proved |
| `informedReflects_junk_null` | fn 12; item 039 | the informed version forces the junk cell `[P̂ = 0]` `π`-null | P | exact | — | — | proved |
| `informedReflects_iff_newReflects` | §1 ll. 93–99, fn 12 | informed Reflection (all `σ`) ⟺ NR-str | P | exact (all-`σ` reading, made precise by `informedReflects_iff_simplex_and_junk` (r2, P): the all-`σ` reading is the distributions-only reading plus the junk cell `[P̂ = 0]` being `π`-null, nothing else; F7) | — | frames' `fig2_newReflects` (NR-str holds); `Examples.not_informedReflects_πneg_dup3` (fails, r1) | proved |
| `informedReflectsSimplex_iff_newReflectsVac` | item 039 (stretch) | informed Reflection over distributions ⟺ NR-vac | P (r1: was L) | exact (NR-vac reading) | — | `Examples.swap2` (NR-vac, not NR-str); `not_informedReflectsSimplex_πneg_dup3` (fails, r1) | proved |

## Target 3 — Reflection ⟹ Value; ⟺ on immodest frames (`Reflection.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `value_of_reflects` | §1 l. 128, fn 16 | Reflection ⟹ Value, directly by cells (not via the cycle) | P | exact | — | `dup3_all`; fig3 separates (Value without Reflection, frames) | proved |
| `reflects_iff_value_of_immodest`, `reflects_iff_value_of_immodestFrame` | fn 17 | on immodest candidates / frames Reflection ⟺ Value | C | exact | — | `dup3_all`, `dup3_none` | proved |

## Target 4 — Value ⟹ New Reflection by fn 19's bet (`Reflection.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `condBet` | fn 19 | the conditional bet `(1 − t)·𝟙[q ∧ P = ρ] − t·𝟙[¬q ∧ P = ρ]` | D | exact | — | — | proved |
| `newReflectsVac_of_value` | fn 19; item 042 | Value ⟹ NR-vac by the conditional bet against `const 0` | P | exact | — | fig3 (positive), fig2 (NR without Value, frames) | proved |
| `selfMass_pos_of_value` | fn 19 (presupposition) | Value ⟹ every candidate has a positive self-cell (bet `−𝟙[P = ρ]` vs `0`) | P | exact | — | fig3 | proved |
| `newReflects_of_value_direct` | §1 l. 133, fn 19 | Value ⟹ NR-str, both halves as bets | C (r1: was P; it pairs `selfMass_pos_of_value` and `newReflectsVac_of_value`) | exact | — | fig3 | proved |

## Target 5 — the immodest collapse (`Ladder.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `reflects_of_simpleTrust_of_immodest` | §5 l. 390 (r1: was l. 373) | on immodest candidates Simple Trust ⟹ Reflection | P | exact | — | `dup3_all` / `dup3_not_simpleTrust` | proved |
| `tfae_immodest`, `tfae_immodestFrame` | §5 l. 390 (r1: was l. 373); plan extension | on immodest candidates / frames: TFAE [Reflection, New Reflection, Simple Trust, Trust, Total Trust, Value] | C | exact | — | `Examples.dup3_all` (all six hold, N+), `dup3_none` (all six fail, N+) | proved |

## Target 6 — the ladder (`Ladder.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `CondTotalTrust`, `condTotalTrust_of_totalTrust`, `totalTrust_of_condTotalTrust`, `condTotalTrust_iff_totalTrust` | §2 l. 182, fn 36; plan extension (vacuous, findings F6) | conditional Total Trust *is* Total Trust (`q = W`) | D, L, L, L | exact | — | `Examples.not_condTotalTrust_fact21` (fails on Fact 2.1, N+, r1) | proved |
| `selfMass_pos_of_simpleTrust` | §2 l. 150, fn 37 | Simple Trust ⟹ positive self-cells at candidates (symmetric form at `[P = ρ]ᶜ`, `t = 1`) | P | exact | — | fig3 | proved |
| `newReflects_of_trust` | fn 37 | Trust ⟹ New Reflection (NR-str), by `q = {v}` on the cell and summation | P | exact | — | `Examples.fig2_newReflects_not_trust` (NR without Trust, N+) | proved |
| `simpleTrust_of_trust` | §2 l. 154 | Trust ⟹ Simple Trust (`p = W`) | L | exact | — | — | proved |
| `ComparativeTotalTrust`, `comparativeTotalTrust_iff_totalTrust` | fn 29 | comparative form ⟺ Total Trust | D, L | exact | — | `Examples.not_comparativeTotalTrust_fact21` (fails on Fact 2.1, N+, r1) | proved |
| `averagedEvent`, `AveragedTotalTrust`, `averagedTotalTrust_of_totalTrust` | fn 38 | Total Trust ⟹ averaged form (converse E2 not attempted) | D, D, L | exact | — | `Examples.not_averagedTotalTrust_πneg_dup3` (fails at `n = 1` on `dup3`, N+, r1) | proved |

## Target 7 — convexity formulations (`Convexity.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Biconvex`, `memEvent`, `CondIn`, `ReflectsConvex`, `TotalTrustBiconvex`, `condOn` | §2 ll. 217–227 | biconvex sets, `[P ∈ B]`, "`π(· ∣ P ∈ B) ∈ B`" in product form, the two convexity versions, the ratio vector (lemma-level) | D | exact | — | `Examples.not_reflectsConvex_fig3` (`ReflectsConvex` fails on Figure 3, N+, r1) | proved |
| `reflects_iff_reflectsConvex` | §2 l. 221 | Reflection ⟺ its convexity version | P | exact | — | dup3 / fig3 | proved |
| `totalTrust_iff_totalTrustBiconvex` | §2 l. 225, fn 34; item 054 | Total Trust ⟺ its biconvex version (Hahn–Banach on the `B`-rows vs the `Bᶜ`-rows together with `π*`) | P | exact (`Biconvex` takes the complement in `ℝ^W` as the glossary does; the simplex-relative reading gives the same headline, docstring r2) | — | `Examples.fig3_totalTrustBiconvex` (N+), `fact21_not_totalTrustBiconvex` (N+, direct refutation); `Examples.dup3_condIn_lexHalf_compl_of_headline` (r2, N+: the (⇒) direction exercised beyond half-spaces, at the biconvex `(lexHalf 2 0 ¾)ᶜ` on `dup3`, where the conditional `(½, ½, 0)` lies on the boundary hyperplane and is in the set only by the lexicographic clause) | proved |
| `Examples.lexHalf_compl_biconvex`, `lexHalf_compl_ne_closedHalf`, `lexHalf_compl_ne_openHalf`, `dup3_memEvent_lexHalf_compl`, `dup3_condIn_lexHalf_compl_direct`, `dup3_condIn_lexHalf_compl_summary` (r2, audit probe Q2 copied) | §2 l. 219, l. 225 (findings F5) | the complement of a lexicographic half-space is biconvex and neither a closed nor an open half-space; on `dup3` with the uniform deferrer the conditional on `[P ∈ B]` lands in `B`, verified directly and through the headline | L, P, P, L, N+, N+ | n/a | — | itself | proved |
| `biconvex_strong_sep` | fn 34 | finite frames: strong separation of `{P_w ∈ B}` from `{P_w ∉ B}` | P | exact | — | — | proved |
| `biconvex_halfSpace`, `biconvex_empty`, `biconvex_univ` | §2 l. 213, l. 219 (findings F5) | half-spaces, `∅`, `univ` are biconvex (the last two degenerately) | L | n/a | — | — | proved |
| `Examples.lexHalf`, `lexHalf_biconvex`, `lexHalf_ne_closedHalf`, `lexHalf_ne_openHalf`, `lexHalf_not_halfSpace` (r1) | §2 l. 219, fn 34 (findings F5, corrected) | the lexicographic half-space `{x_i > 0} ∪ {x_i = 0 ∧ x_j ≥ c}` is biconvex and is neither a closed nor an open half-space `{t ≤ E(X)}`/`{t < E(X)}` (any `W`, `i ≠ j`, any `c`) | D, P, P, P, N+ | n/a (refutes "biconvex ⟺ one side of a cut") | — | itself | proved |
| `Examples.lexHalf3_nontrivial`, `lexHalf3_ne_closedHalf_simplex`, `lexHalf3_ne_openHalf_simplex` (r1) | §2 l. 219 ("divide probability space"; findings F5) | on three worlds with `c = ½`, `L` contains `(0, ½, ½)` and misses `(0, 0, 1)`, and `L ∩ Δ` is not `{ρ ∈ Δ : t ≤ E(X)}` or `{ρ ∈ Δ : t < E(X)}` for any `X, t` | N+, P, P | n/a (refutes l. 221 as a claim about probability space) | — | itself | proved |

## Target 9 — fixed-option Dutch books (`DutchBook.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `SureLoss`, `AlmostSureLoss`, `ExpectedLoss`, `FixedOptionBook` | fn 20, glossary l. 428, fn 22 | the three loss grades; a book parametrised by its grade | D | exact | — | — | proved |
| `AlmostSureLoss.of_sureLoss`, `ExpectedLoss.of_almostSureLoss`, `ExpectedLoss.of_sureLoss`, `FixedOptionBook.mono` | fns 20–22 | sure ⟹ almost-sure ⟹ expected; books are monotone in the grade | L | n/a | — | — | proved |
| `exists_book_sureLoss_of_not_value` | fn 21 | ¬Value ⟹ a book with sure loss `−ε` | P | exact | — | `Examples.fact21_book` (N+) | proved |
| `not_value_of_book_expectedLoss` | fn 22 | a book with expected loss ⟹ ¬Value | P | exact | — | fact21 | proved |
| `not_value_iff_exists_book_sureLoss`, `_almostSureLoss`, `_expectedLoss`, `value_iff_no_book` | §1 l. 135, fns 20–22, Thm 5.1 | ¬Value ⟺ a book, at each of the three grades; Value ⟺ no book | C | exact | — | fact21 | proved |

## Target 10 — Fact 4.2 (`Geometry.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `reflects_eq_sum_cands` | fn 58 | Reflection ⟹ `ρ = ∑_{C_ρ} ρ(P = σ) σ` | P | exact | — | — | proved |
| `rows_mem_convexHull_immodest` | fn 57 (gap, findings F2) | Fact 4.2's RHS ⟹ every row is a convex combination of immodest rows (Krein–Milman) | P | exact | — | — | proved |
| `reflects_of_mem_convexHull_immodest` | fn 57 | a convex combination of immodest rows reflects | P | exact | — | — | proved |
| `validates_reflects_iff` | §4 l. 339, fns 57–58; item 067 | frame validates Reflection ⟺ each row immodest or in `hull C_i⁻` | P | exact | — | `Examples.dup3_validates_reflects` (N+, r1; every row immodest, so the left disjunct only); `Examples.nullSelf_validates_reflects_modest` (N+, r2: row 0 is modest with a null self-cell and validates through the right disjunct `P_0 ∈ hull {δ₁, δ₂}`); fig3 does not (`P_a` is modest with `P_a(a) > 0`, so `not_reflects_of_modestAt` at `π = P_a`; not stated as a `Validates` negation) | proved |
| `selfMass_eq_zero_or_one_of_validates` | fns 57, 61 | under validated Reflection self-cell masses are `0` or `1` | L | n/a | — | — | proved |

## Target 11 — Fact 4.3 (`Geometry.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `newReflects_eq_sum_informed` | fn 59 (⇒) | New Reflection ⟹ `ρ = ∑_{C_ρ} ρ(P = σ) P̂_σ` | P | exact | — | — | proved |
| `validates_newReflects_iff` | §4 l. 347, fn 59 (its (⇐) is complete but presupposes NR-str, F3 corrected); item 068 | frame validates New Reflection (NR-str) ⟺ each row in `hull {P̂_j : P_j ∈ C_i}` (junk `0` included) | P | exact (NR-str) | — | `Examples.swap2_validates_newReflectsVac_not_hull` (refutes the NR-vac reading, N+); `Examples.dup3_validates_newReflects` (immodest, N+, r1); `Examples.fig2_validates_newReflects` (modest, N+, r1); `Examples.nullSelf_validates_all` (N+, r2: NR-str validated with a null-self-cell row, `P_0 = ½ P̂_1 + ½ P̂_2`) | proved |

## Target 12 — Corollaries 4.4, 4.5 (`Geometry.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ModestlyInformedU`, `modestlyInformedU_iff_weights`, `modestlyInformedU_iff_of_pos`, `modestlyInformedU_iff_of_zero` | fn 54, fn 61 | unguarded modest informedness; λ-form; agrees with the guarded predicate at positive self-cells; at a null self-cell is hull membership over `C_ρ⁻` | D, L, L, L | exact | — | `Examples.swap2_not_modestlyInformedU` (r2, N+: fails at a null self-cell, `δ₁ ∉ hull {δ₀}`) | proved |
| `validates_reflects_iff_extremeWeights` | §4 l. 359, fn 60 | Corollary 4.4: validates Reflection ⟺ λ-form with `λ_ii ∈ {0, 1}` (a whole-frame iff; the per-row reading of `λ_ii` needs validated Reflection, since the weights are indexed by the *set* `{P̂_i} ∪ C_i⁻` — docstring r2, fidelity NB9) | L | exact | — | dup3 (`λ_ii = 1` branch); `Examples.nullSelf_validates_reflects_modest` (r2: the `λ_00 = 0` branch) | proved |
| `validates_totalTrust_iff` | §4 l. 363, fn 61; item 069 | Corollary 4.5: validates Total Trust ⟺ every row unguarded-modestly-informed | C | exact (unguarded; guarded reading refuted) | — | `Examples.nullSelf_validates_totalTrust_not_modestlyInformed` (N+, refutes the guarded reading; obtained through this theorem's (⇐), fidelity NB10); `ExamplesFig5.fig5F1_validates_totalTrust` (N+); `Examples.swap2_not_validates_totalTrust` (r2, N+: a frame failing the right-hand side, hence not validating Total Trust) | proved |

## Target 13 — Figure 5 (`ExamplesFig5.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `fig5F1`, `fig5F1_modestlyInformedU`, `fig5F1_hull`, `fig5F1_totalTrust_value`, `fig5F1_validates_totalTrust` | §4 ll. 313–316, Figure 5 | `F₁`: the hull condition with the mandate's weights (verified), Total Trust and Value for the uniform `π`, and validation | N+ | exact | — | itself | proved |
| `fig5F2_no_totalTrust` | §4 l. 313 | `F₂` is totally trusted by no distribution | C | exact | — | strengthens frames' `fig5F2_not_totalTrust` | proved |

## Target 14 — hereditary deference (`Hereditary.lean`, `Examples.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `totalTrust_cands`, `value_cands`, `reflects_cands` | fn 56; item 071 | Total Trust, Value, Reflection pass to every candidate | C | exact | — | fig3 / dup3 | proved |
| `nonHered4_not_hereditary` | fn 56; item 071 | New Reflection is not hereditary (`W = Fin 4`; refutes both readings) | N+ | n/a | — | itself | proved |

## Target 15 — Theorem 5.1 (`Collected.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `LambdaForm`, `hullAndModestlyInformed_iff_lambdaForm` | §5 l. 375 | the fourth bullet's λ-form | D, L | exact (self-cell positivity stated explicitly at every candidate, which DDB's bullet only presupposes; redundant under the hull clause by `Frame.selfMass_pos_of_hull` — fidelity NB5, r2) | — | — | proved |
| `tfae_thm51` | §5 l. 375; item 075 | TFAE [Value, no Dutch book, Total Trust, biconvex Total Trust, hull condition, λ-form] | C | weaker: epistemic Value (Thm 3.2) omitted, `lit-ddb-accuracy-mm`; the Dutch-book bullet is stated at the sure-loss grade, immaterial by the three-grade iffs | — | `Examples.fig3_thm51_all` (all six hold, N+, r1), `Examples.fact21_thm51_none` (all six fail, N+, r1) | proved |

## Target 16 — positive access (`Hereditary.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `PositiveAccess` | §5 l. 392 (Dorst 2020a Fact 8.2 as paraphrased there; ATTRIBUTION-UNVETTED that it is Dorst's exact statement) | `ρ(q) = 1 → ρ(P(q) = 1) = 1` | D | exact (of the paraphrase) | — | `Examples.not_positiveAccess_δ0_fact21` (fails for `δ_{w₀}` on Fact 2.1, N+, r1) | proved |
| `positiveAccess_of_simpleTrust` | Fact 8.2 as paraphrased at DDB l. 392 (derived, (b) → (a)) | Simple Trust ⟹ positive access | P | exact | — | `Examples.dup3_row0_positiveAccess` (row `(½, ½, 0)`, certain of `{w₀, w₁} ≠ W`: a non-trivial instance, N+, r1); fig3 (rows fully supported, so only the trivial `q = W` instance: N−); `not_simpleTrust_δ0_fact21` (contrapositive, r1) | proved |
| `positiveAccess_of_value` | §5 l. 392; item 078 | Value ⟹ every candidate has positive access (the paper's claim) | C | exact | — | `dup3_row0_positiveAccess` via `dup3_all` (N+, r1); fig3 (N−) | proved |
| `positiveAccess_self_of_value` | §5 l. 392 (variant) | Value ⟹ the deferrer itself has positive access | L | variant: about `π`, not the candidates | — | — | proved |

## Target 17 — prior frames (`Prior.lean`, `ExamplesPrior.lean`)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `PriorFrame`, `PriorFrame.row`, `PriorFrame.toFrame` | fn 25 | prior frames and the induced probability frame `P_w = μ(· ∣ E_w)` (nonempty evidence, which fn 25 presupposes, made explicit — docstring r2) | D | exact | — | — | proved |
| `trust_of_value` | §2 l. 157 (Dorst 2020a Thm 7.2) | Value ⟹ Trust on any frame | L | exact | — | fig3 | proved |
| `ExamplesPrior.prior_trust_value_refuted`, `prior_trust_value_all_refuted`, `cxQ_summary` (r2, audit probe B1 copied) | §2 l. 157, fn 25 (DDB's paraphrase of Dorst 2020a Thm 7.4); findings F15 | **"on prior frames Trust ⟹ Value" is false as stated, in both readings**: `cxQ` (prior `(1/10, 3/10, 3/5)`, evidence `{0}, {0,1}, {1,2}`, factive, not nested) has `Trust μ` (`cxQ_trust`, every `q, p` and real `t`) and `¬ Value μ` (`cxQ_not_value`, from `¬ TotalTrust` at `X = (−6, 3, 0)`, `s = 1`) | N+ | n/a (refutation of the paraphrase) | — | itself | refuted (these were the two OPEN rows `prior_trust_value_open`, `prior_trust_value_all_open` of rounds 0–1, now deleted) |
| `PriorFrame.mass_Ev_le_of_mem_of_simpleTrust` (r2) | fn 25; Target 17(ii)/E1 | Simple Trust of the prior forces mass-monotone evidence: `v ∈ E_w → μ(E_v) ≤ μ(E_w)` | P | n/a (new; findings F14) | — | any prior frame | proved |
| `PriorFrame.Nested`, `PriorFrame.EvClosed` (r2) | none: new (the Geanakoplos-shaped condition the mandate anticipated) | nested evidence (any two evidence sets that meet are comparable); evidence-closed sets of worlds | D | n/a | — | `ExamplesPrior.chainQ_nested`, `diracQ_nested` (nested), `cxQ_not_nested` (not) | proved |
| `PriorFrame.Ev_subset_of_mem_of_nested` (r2) | none: new | on a nested prior frame Simple Trust of the prior makes the evidence transitive: `v ∈ E_w → E_v ⊆ E_w` | P | n/a | — | chainQ | proved |
| `PriorFrame.sum_Ev_eq_mass_mul`, `PriorFrame.totalTrust_of_factive_of_trans_of_nested` (r2) | none: new | factive + transitive + nested evidence ⟹ the prior totally trusts the induced frame (strong induction over evidence-closed sets: `∑_{T ∩ [E(X) ≥ s]} μ_w(X_w − s) ≥ max(0, ∑_T μ_w(X_w − s))`) | L, P | n/a | — | chainQ | proved |
| **`PriorFrame.totalTrust_of_nested_of_simpleTrust`** (r2, headline) | §2 l. 157, fn 25 (Dorst 2020a Thm 7.4 as paraphrased there; ATTRIBUTION-UNVETTED whether Dorst's own hypothesis is nestedness); findings F15 | **on a nested prior frame, Simple Trust of the prior ⟹ Total Trust of the prior** | P | stronger: Simple Trust as antecedent, Total Trust as consequent; restricted to nested evidence, which is exactly where the unrestricted claim fails | — | `ExamplesPrior.chainQ_nested_trust_value` (N+: uniform prior, evidence `{0} ⊂ {0,1} ⊂ W`, rows `δ_0, (½,½,0), (⅓,⅓,⅓)` with row 1 **modest**, so not an instance of the immodest collapse; the prior simply trusts, totally trusts and values); `cxQ_summary` (not nested: Trust without Value, so the hypothesis is not an artifact) | proved |
| `prior_value_of_trust_of_nested`, `PriorFrame.tfae_nested` (r2) | same | on nested prior frames Trust ⟹ Value (the corrected Target 17(ii)); TFAE [Simple Trust, Trust, Total Trust, Value] for the prior | C | variant: restricted to nested evidence / stronger: the whole ladder collapses | — | `chainQ_nested_trust_value`, `diracQ_trust_and_value` (N+) | proved |
| `prior_trust_value_all_nested_open` (r2) | §2 l. 157, fn 25; Dorst 2020a Thm 7.4 (whether Dorst quantifies the deferrer separately is itself unverified) | every deferrer that trusts a **nested** prior frame values it | OPEN | variant (separate deferrer; nested) | the statement is open (proof sketch in the report, E1; the audit's three-world search found no counterexample) | `ExamplesPrior.chainQ_simpleTrust_not_value` (N+: Simple Trust of a separate deferrer is **not** enough — `π = (½, 1/5, 3/10)` on `chainQ` simply trusts, fails Trust at `q = {1}`, `p = {1,2}`, `t = ½`, and does not value); `diracQ_open_all` (N+: holds on the finest partition for every deferrer, by the collapse) | open |
| `no_priorFrame_of_two_full_rows`, `fig2_not_priorFrame`, `fig3_not_priorFrame`, `fact21_not_priorFrame` | fn 25; item 079 | DDB's counterexamples are not prior frames (so they bear on Dorst's theorem neither way; the prior-frame Trust-without-Value witness is `cxQ` — F11 amended r2) | N− | n/a | — | themselves | proved |
| `PriorFrame.mem_Ev_of_subset_of_simpleTrust`, `PriorFrame.mem_Ev_self_of_simpleTrust`, `PriorFrame.mem_Ev_self_of_trust` (r1) | fn 25; Target 17(ii)/E1 (audit r1 NB5) | Simple Trust (hence Trust) of the prior forces factive evidence `w ∈ E_w`, and more: `E_v ⊆ E_w → v ∈ E_w` — a structural constraint fn 25's prior frames do not assume | P, P, C | n/a (new; findings F14) | — | itself (any prior frame); `cxQ` satisfies both and still fails Value, so factivity is not the missing hypothesis (nestedness is) | proved |

## Not done

| Item | Status |
|---|---|
| Target 8 (stretch): proposition-level biconvex sets are rays; the "strongest `π(· ∣ P = ρ) ∈ C`" reading | not attempted (no Lean statement); the imprecision is recorded in the report |
| Target 18 (stretch): uniqueness of recommended strategies on fact21 / fig2 | not attempted |
| E1: Dorst's Theorem 7.4 on finite prior frames | resolved in r2: DDB's paraphrase is **refuted** (`ExamplesPrior.cxQ`); the deferrer-is-the-prior reading is **proved on nested prior frames** (`PriorFrame.totalTrust_of_nested_of_simpleTrust`, from Simple Trust); the separate-deferrer nested reading is the one OPEN row, with a proof sketch (report §E1) and the boundary witness `chainQ_simpleTrust_not_value` |
| E2: `AveragedTotalTrust → TotalTrust` (layer-cake + limit) | not attempted |
| E3: `Trust π21 fact21` | not attempted |
| Lexicographic biconvex set (findings F5) | done in repair round 1 (`Examples.lexHalf*`, rows under Target 7) |
