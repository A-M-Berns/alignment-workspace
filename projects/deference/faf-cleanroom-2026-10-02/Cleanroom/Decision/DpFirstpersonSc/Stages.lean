import Cleanroom.Decision.DpFirstpersonSc.Bridge
import Cleanroom.Udt.UdtSupercondition.DZ

/-!
# The stage instance of the quotient obstruction (AN-22′), AN-21, AN-25 — T9 of
[[dp-firstperson-sc-mandate]]

The general obstruction is `udt-supercondition`'s `compatible_range_subset` (a `Ĉ`-compatible
model forces every `C`-positive shared proposition into the range of `c'`) and its `Fin 2 → Fin 1`
refutation of SC Thm 2.4 (⇐), `thm24_sufficiency_refuted` — **neither is re-proved or re-filed
here** (finding F1 of `udt-supercondition`; dp-cf-105 confirmed). This file re-derives the
**stage instance** against the literal `CommonInfo`/`Compatible`:

* `StageW := Fin 2 × Fin 2` — the pre-computation worlds `(digit, coin)`: digit `0` = "the digit
  is 3" (`X₃`), digit `1` = "the digit is 7" (`X₇`); the later stage `t'` has computed the digit,
  so its worlds are the coin alone, `Fin 2`, embedded by `stageEmbed b := (0, b)`. The common
  information `stageCI := ⟨StageW, id, stageEmbed⟩` has `c' = stageEmbed` **not surjective**: the
  digit-7 atoms are outside its range (AN-21: `𝓔_{t'}` is a *quotient* of `𝓔_{t₀}`, not an SC
  Def 0.5 refinement).
* `stagePrior p` — `P_{t₀}`: digit 3 with probability `p`, fair coin, independent (a rational
  `FinDistr` through the bridge). The posterior `P_{t'}` is the fair coin on `Fin 2`, whose
  pushforward along `stageEmbed` is `P_{t₀}(· | X₃)`.
* **`stage_boundedDensity`**: SC Thm 2.4's hypothesis holds with bound `1/P(X₃)`;
  **`stage_no_compatible_model`**: no `Ĉ`-compatible model exists when `0 < P(X₇) = 1 − p`
  (by `commonInfo_condModel_iff`: the range condition fails at a digit-7 atom);
  **`stage_gap`**: the mass the construction's `p_* μ` falls short by is `P(X₇) = 1 − p` — the
  three cells `½, 9/10, 1/10` at `p = ½, 1/10, 9/10`.
* **AN-25** (`stage_pullback_ne_prior`; `WitnessesAudit.lean`, `mug1_tailsCertain_not_perRun`):
  the counterlogical mugging is the no-doubt mugging under the quotient — the post-computation
  state pulled back along the embedding is `(½, ½, 0, 0)` (`pushDistr_uniform_stageEmbed`),
  which is not the fair prior `ν = (¼)⁴`: the audit's `P`-clause with trivial evidence fails on
  the stage carrier at the digit-7 atoms, as per-run clause 1 fails for the tails-certain state on
  `B₁`. Built here as the stage-carrier inequality; the stage tree and the `AuditPassAt` instance
  are `WitnessesStage.lean` (`stageTree`, `stagePostState_fails_audit`, repair round 1). Nothing
  cross-ontology is established.

Source items: `anticipation.md` AN-21, AN-22′, AN-25; dp-cf-105; dp-cf-2-041 (finite version).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Finset

/-! ## The two stages -/

/-- The pre-computation worlds `(digit, coin)`: digit `0` is `X₃`, digit `1` is `X₇`.
Source: `anticipation.md` AN-22′ (`𝓔_{t₀}` with the digit-7 atoms); mandate T9
Kind: D -/
abbrev StageW : Type := Fin 2 × Fin 2

/-- The digit-7 worlds `X₇` (`= X₃ᶜ`). Source: `anticipation.md` AN-22′. Kind: D -/
def X7 : Finset StageW := Finset.univ.filter fun w => w.1 = 1

/-- **The quotient as a point map**: the later stage's worlds (the coin alone) embedded into the
earlier stage's at digit `3`. Not surjective: the digit-7 atoms have no preimage — the empty
`c'`-fibres of AN-22′.
Source: `anticipation.md` AN-21 ("`c' = π_{t₀,t'}` … in the point picture `W_{t'} ⊆ W_{t₀}`"),
AN-22′ ("its construction's `c'`-fibers over the digit-7 atoms are empty")
Kind: D
Fidelity: exact (the point picture of the deductive quotient) -/
def stageEmbed : Fin 2 → StageW := fun b => (0, b)

/-- **AN-21, stages as common information**: `Ĉ := 𝓔_{t₀}`, `c := id`, `c' := stageEmbed`. A
type-check only: it is a legitimate `CommonInfo`, but a quotient, not a refinement (SC Def 0.5
asks for an inclusion of algebras), and across it no compatible conditioning model runs
(`stage_no_compatible_model`).
Source: `anticipation.md` AN-21 ("stages as a common information structure: a type-check only")
Kind: D
Fidelity: exact -/
abbrev stageCI : CommonInfo StageW (Fin 2) := { C := StageW, c := id, c' := stageEmbed }

/-- The pre-computation prior `P_{t₀}` as a rational distribution: digit 3 with probability `p`,
an independent fair coin.
Source: `anticipation.md` AN-22′ (`P_{t₀}` with `P_{t₀}(X₃) = p`)
Kind: D -/
def stagePriorQ (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinDistr ℚ StageW where
  w w := (if w.1 = 0 then p else 1 - p) / 2
  nonneg w := by split_ifs <;> linarith
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp [Fin.sum_univ_two]

/-- `P_{t₀}` as a `PMF`. Source: `anticipation.md` AN-22′. Kind: D -/
noncomputable def stagePrior (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : PMF StageW :=
  toPMF (stagePriorQ p h0 h1)

/-- The post-computation state `P_{t'}`: the fair coin on the later worlds.
Source: `anticipation.md` AN-22′ (`P_{t₀}(· | X₃)` on the later stage)
Kind: D -/
noncomputable def stagePost : PMF (Fin 2) := toPMF FinDistr.uniform

/-- `C₁ = P_{t₀}` (`c = id`). Source: none: infrastructure. Kind: L -/
theorem stageCI_C₁ (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    stageCI.C₁ (stagePrior p h0 h1) = stagePrior p h0 h1 := PMF.map_id _

/-- The pushforward of the fair coin along the embedding: `½` on each digit-3 world, `0` on the
digit-7 worlds — `P_{t₀}(· | X₃)`.
Source: `anticipation.md` AN-22′
Kind: L -/
theorem pushDistr_uniform_stageEmbed (w : StageW) :
    (pushDistr (FinDistr.uniform : FinDistr ℚ (Fin 2)) stageEmbed).w w =
      if w.1 = 0 then 1 / 2 else 0 := by
  show (∑ b ∈ Finset.univ.filter (fun b => stageEmbed b = w), (FinDistr.uniform : FinDistr ℚ (Fin 2)).w b) = _
  rcases w with ⟨d, b⟩
  fin_cases d <;> fin_cases b <;> simp [stageEmbed, Finset.filter_eq', FinDistr.uniform_w] <;>
    norm_num

/-- `C₂ = (stageEmbed)_* P_{t'}` through the bridge. Source: none: infrastructure. Kind: L -/
theorem stageCI_C₂ : stageCI.C₂ stagePost = toPMF (pushDistr FinDistr.uniform stageEmbed) := by
  show stagePost.map stageEmbed = _
  rw [stagePost, toPMF_map]

/-- **SC Thm 2.4's hypothesis holds at the stage instance**: `C₂ ≪ C₁` with density bounded by
`1/P(X₃) = 1/p`, for `0 < p`.
Source: `anticipation.md` AN-22′ ("Thm 2.4's hypotheses hold (`C' ≪ C`, density
`1/P_{t₀}(X₃)`)")
Kind: P
Fidelity: exact
Hyps: (a) `0 < p ≤ 1` -/
theorem stage_boundedDensity (p : ℚ) (h0 : 0 < p) (h1 : p ≤ 1) :
    BoundedDensity (stageCI.C₂ stagePost) (stageCI.C₁ (stagePrior p h0.le h1))
      (ENNReal.ofReal (p⁻¹ : ℚ)) := by
  rw [stageCI_C₁, stageCI_C₂, stagePrior, boundedDensity_toPMF_iff _ _ _ (inv_nonneg.mpr h0.le)]
  intro w
  rw [pushDistr_uniform_stageEmbed]
  show _ ≤ p⁻¹ * ((if w.1 = 0 then p else 1 - p) / 2)
  split_ifs with hw
  · have hp : p ≠ 0 := h0.ne'
    rw [show p⁻¹ * (p / 2) = 1 / 2 by field_simp]
  · exact mul_nonneg (inv_nonneg.mpr h0.le) (by linarith)

/-- **AN-22′, the stage instance of the quotient obstruction**: although SC Thm 2.4's hypothesis
holds (`stage_boundedDensity`), **no** `stageCI`-compatible conditioning model from `P_{t₀}` to
`P_{t'}` exists when `P(X₇) = 1 − p > 0` — the range condition of `commonInfo_condModel_iff` fails
at a digit-7 atom (`(1, 0)` has prior mass `(1−p)/2 > 0` and is not in the range of `stageEmbed`).
dp-cf-105 confirmed on the stage instance; the general lemma is `udt-supercondition`'s
`compatible_range_subset`.
Source: `anticipation.md` AN-22′ ("no `Ĉ`-compatible model for `(P_{t₀}, P_{t₀}(· | X₃))` unless
`P_{t₀}(X₇) = 0`"); dp-cf-105; `udt-supercondition` F1
Kind: N+
Fidelity: exact (the `Fin 2 × Fin 2 → Fin 2` instance of the general obstruction)
Hyps: (a) `0 < p < 1` -/
theorem stage_no_compatible_model (p : ℚ) (h0 : 0 < p) (h1 : p < 1) :
    ¬ ∃ m : CondModel (stagePrior p h0.le h1.le) stagePost, Compatible m stageCI := by
  rw [commonInfo_condModel_iff]
  rintro ⟨-, hr⟩
  have hpos : 0 < stageCI.C₁ (stagePrior p h0.le h1.le) ((1 : Fin 2), (0 : Fin 2)) := by
    rw [stageCI_C₁, stagePrior, toPMF_apply, ENNReal.ofReal_pos, Rat.cast_pos]
    show (0 : ℚ) < (if ((1 : Fin 2), (0 : Fin 2)).1 = 0 then p else 1 - p) / 2
    simp
    linarith
  obtain ⟨b, hb⟩ := hr _ hpos
  simp [stageEmbed, stageCI] at hb

/-- **The gap**: the mass the construction's `p_* μ` falls short of `P_{t₀}` by is `P(X₇) = 1 − p`
— `½`, `9/10`, `1/10` at `P(X₃) = ½`, `1/10`, `9/10`. Stated as the prior mass of `X₇` (the
complement of the range of `stageEmbed`), the quantity the general obstruction says must vanish.
Source: `anticipation.md` AN-22′ ("`p_* L` falls short of `P_{t₀}` by `P_{t₀}(X₇)` (`½`, `9/10`,
`1/10` at `P_{t₀}(X₃) = ½, 1/10, 9/10`)")
Kind: N+
Fidelity: exact -/
theorem stage_gap (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    mass (stagePrior p h0 h1) (↑X7 : Set StageW) = ENNReal.ofReal ((1 - p : ℚ) : ℝ) := by
  have key : probOf (stagePriorQ p h0 h1) X7 = 1 - p := by
    show (∑ w ∈ X7, (if w.1 = 0 then p else 1 - p) / 2) = 1 - p
    rw [X7, Finset.sum_filter, Fintype.sum_prod_type]
    simp [Fin.sum_univ_two]
  rw [stagePrior, mass_toPMF, key]

/-- The three cells: `P(X₇) = ½, 9/10, 1/10` at `p = ½, 1/10, 9/10`.
Source: `anticipation.md` AN-22′
Kind: N+ -/
theorem stage_gap_cells :
    mass (stagePrior (1/2) (by norm_num) (by norm_num)) (↑X7 : Set StageW) =
        ENNReal.ofReal ((1/2 : ℚ) : ℝ) ∧
    mass (stagePrior (1/10) (by norm_num) (by norm_num)) (↑X7 : Set StageW) =
        ENNReal.ofReal ((9/10 : ℚ) : ℝ) ∧
    mass (stagePrior (9/10) (by norm_num) (by norm_num)) (↑X7 : Set StageW) =
        ENNReal.ofReal ((1/10 : ℚ) : ℝ) := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [stage_gap]; try norm_num)

/-- **The same-ontology update is representable**: within `𝓔_{t₀}` the Bayes update
`P_{t₀} → P_{t₀}(· | X₃)` is a same-ontology conditioning model with density bound `1/p` — the
numbers `2, 10, 10/9` of AN-22′ are *same-ontology* (Level 3) densities, which is where email 3's
"with the prior probability" lives.
Source: `anticipation.md` AN-22′ ("the numbers `2, 10, 10/9` are correct as the same-ontology
(Level 3) Bayes densities")
Kind: L
Fidelity: exact -/
theorem stage_sameOntology_exists (p : ℚ) (h0 : 0 < p) (h1 : p ≤ 1) :
    Nonempty (SameOntologyModel (stagePrior p h0.le h1) (stageCI.C₂ stagePost)) := by
  rw [sameOntology_condModel_iff]
  exact ⟨_, ENNReal.ofReal_ne_top,
    by have := stage_boundedDensity p h0 h1; rwa [stageCI_C₁] at this⟩

/-- **AN-25, the pullback cell**: the post-computation state pulled back to `𝓔_{t₀}` along the
embedding, `(½, ½, 0, 0)`, is not the fair prior `ν = (¼)⁴` (they differ at the digit-7 atom
`(1, 0)`: `0 ≠ ¼`). On the stage carrier with trivial evidence the audit's `P`-clause is
`P = ν`, so this is its failure — the counterlogical mugging is the no-doubt mugging under the
quotient, failing exactly as the tails-certain state fails per-run clause 1 on `B₁`
(`mug1_tailsCertain_not_perRun`, `P(T) = 1 ≠ ½`).
Source: `anticipation.md` AN-25 ("The post-computation state pulled back to `𝓔_{t₀}` is
`(½, ½, 0, 0)` against `ν = (¼)⁴`: Def 13× fails exactly as per-run SSC fails for the
tails-certain state")
Kind: N+
Fidelity: weaker: the pulled-back state against the prior as an inequality of distributions on
the stage carrier (at `p = ½`); the `AuditPassAt` instance on the stage tree, for every `p < 1`,
is `WitnessesStage.lean`'s `stagePostState_fails_audit` -/
theorem stage_pullback_ne_prior :
    pushDistr (FinDistr.uniform : FinDistr ℚ (Fin 2)) stageEmbed ≠
      stagePriorQ (1 / 2) (by norm_num) (by norm_num) := by
  intro h
  have := congrArg (fun P : FinDistr ℚ StageW => P.w ((1 : Fin 2), (0 : Fin 2))) h
  rw [pushDistr_uniform_stageEmbed] at this
  change (if ((1 : Fin 2), (0 : Fin 2)).1 = 0 then (1 : ℚ) / 2 else 0) =
    (if ((1 : Fin 2), (0 : Fin 2)).1 = 0 then (1 / 2 : ℚ) else 1 - 1 / 2) / 2 at this
  rw [if_neg (by decide), if_neg (by decide)] at this
  norm_num at this

end Cleanroom.Decision.DpFirstpersonSc
