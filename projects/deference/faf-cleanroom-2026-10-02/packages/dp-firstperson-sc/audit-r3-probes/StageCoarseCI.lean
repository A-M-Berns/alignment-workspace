import Cleanroom.Decision.DpFirstpersonSc.Stages

/-!
Audit r3 (adversarial) probe for T9, `stage_no_compatible_model`: an impossibility result
must be checked not to be an artifact of the encoding ([[STANDARDS]] §3, non-vacuity of
impossibility results). The obstruction is relative to the common information
`stageCI = ⟨StageW, id, stageEmbed⟩` — the *fine*, pre-computation language, which is what
AN-21/AN-22′ choose (`c' = π` has empty fibres over the digit-7 atoms). Through the *coarse*
common information `⟨Fin 2, Prod.snd, id⟩` — the post-computation language, `c'` the identity,
so no empty fibre — a compatible conditioning model from `P_{t₀}` to `P_{t'}` **exists** for
every `0 < p ≤ 1`, by `commonInfo_condModel_iff` with density `1` (the coin is fair under
both). So the theorem says exactly what AN-22′ says ("no compatible model through a quotient
translation"), not "no conditioning model between these two states at all"; the point is
worth one sentence in the docstring of `stageCI` or `stage_no_compatible_model`.
Not imported by the library.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Finset

/-- The coarse common information: the later stage's language as `C`, `c = Prod.snd` (the coin
coordinate of a pre-computation world), `c' = id`. -/
abbrev probeCoarseCI : CommonInfo StageW (Fin 2) := { C := Fin 2, c := Prod.snd, c' := id }

/-- The pushforward of `P_{t₀}` along the coin coordinate is the fair coin, for every `p`. -/
theorem probe_pushDistr_snd (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Fin 2) :
    (pushDistr (stagePriorQ p h0 h1) Prod.snd).w b = 1 / 2 := by
  show (∑ w ∈ Finset.univ.filter (fun w : StageW => w.2 = b),
    (if w.1 = 0 then p else 1 - p) / 2) = 1 / 2
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  fin_cases b <;> simp [Fin.sum_univ_two] <;> ring

/-- **Through the coarse common information a compatible model exists** (`0 < p ≤ 1`): the
range condition is automatic (`c' = id`) and the density of the fair coin against the fair coin
is `1`. The impossibility `stage_no_compatible_model` is therefore relative to the fine language
`stageCI`, as AN-22′ states it. -/
theorem probe_coarse_compatible_model_exists (p : ℚ) (h0 : 0 < p) (h1 : p ≤ 1) :
    ∃ m : CondModel (stagePrior p h0.le h1) stagePost, Compatible m probeCoarseCI := by
  rw [commonInfo_condModel_iff]
  refine ⟨⟨ENNReal.ofReal ((1 : ℚ) : ℝ), ENNReal.ofReal_ne_top, ?_⟩, fun y _ => ⟨y, rfl⟩⟩
  show BoundedDensity (stagePost.map id) ((stagePrior p h0.le h1).map Prod.snd) _
  rw [PMF.map_id, stagePost, stagePrior, toPMF_map,
    boundedDensity_toPMF_iff _ _ _ (by norm_num)]
  intro b
  rw [probe_pushDistr_snd, FinDistr.uniform_w]
  norm_num

/-- And the same through the fine language is refuted (the package's theorem, restated here so
the two sit side by side): for `0 < p < 1`. -/
theorem probe_fine_no_model (p : ℚ) (h0 : 0 < p) (h1 : p < 1) :
    ¬ ∃ m : CondModel (stagePrior p h0.le h1.le) stagePost, Compatible m stageCI :=
  stage_no_compatible_model p h0 h1

end Cleanroom.Decision.DpFirstpersonSc
