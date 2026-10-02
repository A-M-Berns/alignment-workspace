import Cleanroom.Info.InfoVoiLatents.NaturalLatents

/-!
# info-voi-latents — the `Λ = X₁` instance of the natural-latents theorem (Target 10, N−) and
the A8.4 degenerate check (N+)

Three uniform bits `ω = (b, (n₁, n₂))`; chunks `X₁ = (b, n₁)`, `X₂ = (b, n₂)`; latent `Λ = X₁` (the
post's "`Λ` could be the entire low-level state of one of the two chunks", l. 71); `Λ' = b`.
**Grade N−** (audit r1, fidelity B2 / adversarial B1): with `Λ = X₁` the mediation hypothesis is
`I[X₁ : X₂ | X₁] = 0`, automatic for every pair, and the conclusion `AEFunctionOf X₁ b` is literally
the first redundancy hypothesis — the full hypothesis package is inhabited but the theorem's
content is not exercised. The N+ witness is `NaturalLatentsWitnessFour.lean` (`Λ = (b, d)`).
What is N+ here: the degenerate latent `Λ' = X₁` (A8.4's patch-list latent) violates redundancy
in `X₂`: `H[X₁ | X₂] = log 2 > 0`, so `¬ AEFunctionOf X₂ X₁` (`chunk₁_not_function_of_chunk₂`).

Mandate: Target 10 witness (the mandate's own `Λ = X₁` design); audit r1.
-/

namespace Cleanroom.Info.InfoVoiLatents.NaturalLatents

open MeasureTheory ProbabilityTheory ShannonInformation
open Cleanroom.Info.InfoVoiLatents.Shannon
open _root_.Condensation

noncomputable section

/-- Three bits.
Source: none: infrastructure (witness)
Kind: D
Fidelity: exact -/
abbrev Ω3 : Type := Bool × (Bool × Bool)

/-- The uniform measure on three bits.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def μ3 : Measure Ω3 := uniformOn (Set.univ : Set Ω3)

instance : IsProbabilityMeasure μ3 := by
  unfold μ3
  infer_instance

/-- The first chunk `(b, n₁)`.
Source: [[wentworth-2023-natural-latents-the-math]] l. 65 (two chunks of a gas, in miniature)
Kind: D
Fidelity: exact -/
def chunk₁ : Ω3 → Bool × Bool := fun ω => (ω.1, ω.2.1)

/-- The second chunk `(b, n₂)`.
Source: same
Kind: D
Fidelity: exact -/
def chunk₂ : Ω3 → Bool × Bool := fun ω => (ω.1, ω.2.2)

/-- The shared bit `b` (the "temperature above 50°C" latent `Λ'`).
Source: [[wentworth-2023-natural-latents-the-math]] l. 65
Kind: D
Fidelity: exact -/
def shared : Ω3 → Bool := fun ω => ω.1

/-- `measurable_chunk₁`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_chunk₁ : Measurable chunk₁ := by
  unfold chunk₁
  fun_prop

/-- `measurable_chunk₂`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_chunk₂ : Measurable chunk₂ := by
  unfold chunk₂
  fun_prop

/-- `measurable_shared`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_shared : Measurable shared := by
  unfold shared
  fun_prop

/-- **Mediation for `Λ = X₁`**: `CondIndepFun chunk₁ chunk₂ chunk₁ μ3` — automatic
(`I[X₁ : X₂ | X₁] = 0` for every pair), so this instance does not exercise the hypothesis.
Source: [[wentworth-2023-natural-latents-the-math]] l. 71
Kind: N−
Fidelity: exact (degenerate: conditioning on `X₁` itself; audit r1) -/
theorem witness_mediates : Mediates chunk₁ chunk₁ chunk₂ μ3 :=
  (ShannonInformation.condMutualInfo_eq_zero measurable_chunk₁ measurable_chunk₂
    measurable_chunk₁).1 (condMutualInfo_self_left measurable_chunk₁ measurable_chunk₂)

/-- **Deterministic redundancy of the shared bit**: `b` is a function of each chunk. (At `Λ = X₁`
its first conjunct is the theorem's conclusion; audit r1.)
Source: [[wentworth-2023-natural-latents-the-math]] l. 65
Kind: N−
Fidelity: exact (degenerate at `Λ = X₁`) -/
theorem witness_detRedundant : DetRedundant chunk₁ chunk₂ shared μ3 :=
  ⟨aeFunctionOf_comp (X := chunk₁) (f := (Prod.fst : Bool × Bool → Bool)) measurable_fst,
    aeFunctionOf_comp (X := chunk₂) (f := (Prod.fst : Bool × Bool → Bool)) measurable_fst⟩

/-- **The conclusion at the `Λ = X₁` instance**, from the theorem — but it is also
`witness_detRedundant.1` verbatim, so nothing of the theorem is exercised here (audit r1); the
N+ conclusion is `witness4_conclusion`.
Source: [[wentworth-2023-natural-latents-the-math]] l. 67
Kind: N−
Fidelity: exact (degenerate: the conclusion is a hypothesis at `Λ = X₁`) -/
theorem witness_conclusion : AEFunctionOf chunk₁ shared μ3 :=
  aeFunctionOf_of_mediates_detRedundant measurable_chunk₁ measurable_chunk₂ measurable_chunk₁
    measurable_shared witness_mediates witness_detRedundant

/-- Every atom of `μ3` has mass `1/8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem μ3_singleton (ω : Ω3) : μ3 {ω} = 1 / 8 := by
  rw [μ3, uniformOn_apply Set.finite_univ, Set.univ_inter, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Set.ncard_singleton, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- **Non-constancy of `Λ'`**: `Λ'` takes both values on atoms of positive mass, so it is not a.e.
constant; and `Λ' : Ω3 → Bool` is not `Λ : Ω3 → Bool × Bool` (different types). This rules out the
constant-latent degeneracy only; it does not rule out the `Λ = X₁` degeneracy (audit r1).
Source: Target 10 witness ("`Λ' ≠ Λ` and `Λ'` non-constant")
Kind: N−
Fidelity: exact (partial non-degeneracy check) -/
theorem witness_nondegenerate :
    (∀ ω : Ω3, μ3 {ω} ≠ 0) ∧ shared (true, (false, false)) ≠ shared (false, (false, false)) := by
  refine ⟨fun ω => by rw [μ3_singleton]; norm_num, ?_⟩
  simp [shared]

/-- `chunk₂_preimage`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem chunk₂_preimage (p : Bool × Bool) :
    chunk₂ ⁻¹' {p} = {(p.1, (false, p.2)), (p.1, (true, p.2))} := by
  ext ⟨a, c, d⟩
  simp only [chunk₂, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff, Prod.ext_iff]
  cases c <;> simp

/-- `μ3_chunk₂_preimage`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem μ3_chunk₂_preimage (p : Bool × Bool) : μ3 (chunk₂ ⁻¹' {p}) = 2 / 8 := by
  rw [μ3, uniformOn_apply Set.finite_univ, Set.univ_inter, chunk₂_preimage, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Set.ncard_pair (by simp), Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- `isUniform_chunk₂`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem isUniform_chunk₂ : IsUniform (Set.univ : Set (Bool × Bool)) chunk₂ μ3 where
  eq_of_mem := by
    intro x _ y _
    rw [μ3_chunk₂_preimage, μ3_chunk₂_preimage]
  measure_preimage_compl := by
    rw [Set.compl_univ, Set.preimage_empty, measure_empty]

/-- `H[chunk₂ ; μ3] = log 4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_chunk₂ : H[chunk₂ ; μ3] = Real.log 4 := by
  have h := isUniform_chunk₂.entropy_eq' Set.finite_univ measurable_chunk₂
  rw [h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- `H[⟨chunk₁, chunk₂⟩ ; μ3] = log 8` (an injective image of `id`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_chunks : H[(⟨chunk₁, chunk₂⟩ : Ω3 → (Bool × Bool) × (Bool × Bool)) ; μ3]
    = Real.log 8 := by
  have hu : IsUniform (Set.univ : Set Ω3) id μ3 := isUniform_uniformOn
  have hid := hu.entropy_eq' Set.finite_univ measurable_id
  have hf : Function.Injective (fun ω : Ω3 => ((ω.1, ω.2.1), (ω.1, ω.2.2))) := by
    rintro ⟨a, c, d⟩ ⟨a', c', d'⟩ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, -, rfl⟩
    rfl
  have := entropy_comp_of_injective μ3 measurable_id (fun ω : Ω3 => ((ω.1, ω.2.1), (ω.1, ω.2.2))) hf
  have e : (fun ω : Ω3 => ((ω.1, ω.2.1), (ω.1, ω.2.2))) ∘ id
      = (⟨chunk₁, chunk₂⟩ : Ω3 → (Bool × Bool) × (Bool × Bool)) := funext fun ω => rfl
  rw [e] at this
  rw [this, hid, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_bool]
  norm_num

/-- **The degenerate latent `Λ' = X₁` is not redundant in `X₂`**: `H[chunk₁ | chunk₂] = log 2 > 0`,
hence `¬ AEFunctionOf chunk₂ chunk₁` (A8.4's patch-list latent).
Source: [[generalization-adversary]] A8.4 (the patch-list latent); Target 10 witness ("the
degenerate check")
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem chunk₁_not_function_of_chunk₂ :
    H[chunk₁ | chunk₂ ; μ3] = Real.log 2 ∧ ¬ AEFunctionOf chunk₂ chunk₁ μ3 := by
  have hH : H[chunk₁ | chunk₂ ; μ3] = Real.log 2 := by
    rw [ShannonInformation.chain_rule'' μ3 measurable_chunk₁ measurable_chunk₂, entropy_pair_chunks,
      entropy_chunk₂]
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  refine ⟨hH, fun h => ?_⟩
  have := condEntropy_eq_zero_of_aeFunctionOf measurable_chunk₂ measurable_chunk₁ h
  rw [hH] at this
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' this

end

end Cleanroom.Info.InfoVoiLatents.NaturalLatents
