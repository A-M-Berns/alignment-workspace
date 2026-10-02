import Cleanroom.Info.InfoVoiLatents.Eig
import Cleanroom.Info.InfoVoiLatents.Shannon

/-!
# info-voi-latents — witnesses for the EIG identity (Target 1)

* **Two independent fair bits** (N+): `Ω = Bool × Bool` uniform, `Λ = id` (both bits), `X₁ = bit1`,
  `X₂ = bit2`: `medErr = 0`, `EIG = redErr' = log 2 > 0` — mediation holds, neither redundancy
  direction does, so `Λ` is not `NaturalOver (X₁, X₂)` (`twoBits_*`). Exact, via
  `entropy_comp_of_injective` and the uniform entropies; no decimals.
* **The natural witness** (N+): `Ω = Bool` fair coin, `Λ = X₁ = X₂ = id`: all three errors are `0`
  (`natural_id`), with `H[id] = log 2 > 0` so the variables are not constant.

The coordinate projections are named `bit1`/`bit2` (`fun p => p.1`, `fun p => p.2`): with the bare
`Prod.fst`/`Prod.snd` the `FiniteRange` instance search is stuck on this toolchain (verified
2026-09-30; findings F11).

Mandate: Target 1 witnesses (2-069(b) in miniature).
-/

namespace Cleanroom.Info.InfoVoiLatents.Eig

open MeasureTheory ProbabilityTheory Real
open Cleanroom.Info.InfoVoiLatents.Shannon

noncomputable section

/-! ### Two independent fair bits -/

/-- The uniform measure on two fair bits.
Source: none: infrastructure (witness; the client pattern of FAF's `APITests/Condensation.lean`)
Kind: D
Fidelity: exact -/
def pairMeasure : Measure (Bool × Bool) := uniformOn (Set.univ : Set (Bool × Bool))

instance : IsProbabilityMeasure pairMeasure := by
  unfold pairMeasure
  infer_instance

/-- The first bit.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def bit1 : Bool × Bool → Bool := fun p => p.1

/-- The second bit.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def bit2 : Bool × Bool → Bool := fun p => p.2

/-- `measurable_bit1`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_bit1 : Measurable bit1 := measurable_fst
/-- `measurable_bit2`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_bit2 : Measurable bit2 := measurable_snd

/-- `H[id ; pairMeasure] = log 4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_id_pairMeasure :
    H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] = Real.log 4 := by
  have hu : IsUniform (Set.univ : Set (Bool × Bool)) id pairMeasure := isUniform_uniformOn
  have h := hu.entropy_eq' Set.finite_univ measurable_id
  rw [h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- `pair_preimage_bit1`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pair_preimage_bit1 (x : Bool) :
    (bit1 ⁻¹' {x} : Set (Bool × Bool)) = {(x, false), (x, true)} := by
  ext ⟨a, b⟩
  cases b <;> simp [bit1, eq_comm]

/-- `pair_preimage_bit2`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pair_preimage_bit2 (x : Bool) :
    (bit2 ⁻¹' {x} : Set (Bool × Bool)) = {(false, x), (true, x)} := by
  ext ⟨a, b⟩
  cases a <;> simp [bit2, eq_comm]

/-- `pairMeasure_preimage_bit1`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pairMeasure_preimage_bit1 (x : Bool) : pairMeasure (bit1 ⁻¹' {x}) = 2 / 4 := by
  rw [pairMeasure, uniformOn_apply Set.finite_univ, Set.univ_inter, pair_preimage_bit1,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_univ, Set.ncard_pair (by simp)]
  norm_num

/-- `pairMeasure_preimage_bit2`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pairMeasure_preimage_bit2 (x : Bool) : pairMeasure (bit2 ⁻¹' {x}) = 2 / 4 := by
  rw [pairMeasure, uniformOn_apply Set.finite_univ, Set.univ_inter, pair_preimage_bit2,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_univ, Set.ncard_pair (by simp)]
  norm_num

/-- `isUniform_bit1`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem isUniform_bit1 : IsUniform (Set.univ : Set Bool) bit1 pairMeasure where
  eq_of_mem := by
    intro x _ y _
    rw [pairMeasure_preimage_bit1, pairMeasure_preimage_bit1]
  measure_preimage_compl := by
    rw [Set.compl_univ, Set.preimage_empty, measure_empty]

/-- `isUniform_bit2`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem isUniform_bit2 : IsUniform (Set.univ : Set Bool) bit2 pairMeasure where
  eq_of_mem := by
    intro x _ y _
    rw [pairMeasure_preimage_bit2, pairMeasure_preimage_bit2]
  measure_preimage_compl := by
    rw [Set.compl_univ, Set.preimage_empty, measure_empty]

/-- `H[bit1 ; pairMeasure] = log 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_bit1_pairMeasure : H[bit1 ; pairMeasure] = Real.log 2 := by
  have h := isUniform_bit1.entropy_eq' Set.finite_univ measurable_bit1
  rw [h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool]
  norm_num

/-- `H[bit2 ; pairMeasure] = log 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_bit2_pairMeasure : H[bit2 ; pairMeasure] = Real.log 2 := by
  have h := isUniform_bit2.entropy_eq' Set.finite_univ measurable_bit2
  rw [h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool]
  norm_num

/-- Any injective image of `id` has the entropy of `id` (the pairs used below).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_comp_id_pairMeasure {T : Type} [MeasurableSpace T] [MeasurableSingletonClass T]
    (f : Bool × Bool → T) (hf : Function.Injective f) :
    H[f ∘ (id : Bool × Bool → Bool × Bool) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
  entropy_comp_of_injective pairMeasure measurable_id f hf

/-- `log_four`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- **Mediation holds for the two-bit latent**: `medErr bit1 bit2 id = I[bit1 : bit2 | id] = 0`.
Source: [[generalization-final]] D10 l. 45; item 2-069(b) (Target 1 witness)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem twoBits_medErr : medErr bit1 bit2 (id : Bool × Bool → Bool × Bool) pairMeasure = 0 := by
  unfold medErr
  rw [ShannonInformation.condMutualInfo_eq' measurable_bit1 measurable_bit2 measurable_id
      pairMeasure,
    ShannonInformation.chain_rule'' pairMeasure measurable_bit1 measurable_id,
    ShannonInformation.chain_rule'' pairMeasure measurable_bit1
      (measurable_bit2.prodMk measurable_id)]
  have e1 : H[(⟨bit1, id⟩ : Bool × Bool → Bool × (Bool × Bool)) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
    entropy_comp_id_pairMeasure (fun b => (b.1, b)) (fun a b h => (Prod.mk.inj h).2)
  have e2 : H[(⟨bit1, (⟨bit2, id⟩ : Bool × Bool → Bool × (Bool × Bool))⟩ :
      Bool × Bool → Bool × (Bool × (Bool × Bool))) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
    entropy_comp_id_pairMeasure (fun b => (b.1, (b.2, b)))
      (fun a b h => (Prod.mk.inj (Prod.mk.inj h).2).2)
  have e3 : H[(⟨bit2, id⟩ : Bool × Bool → Bool × (Bool × Bool)) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
    entropy_comp_id_pairMeasure (fun b => (b.2, b)) (fun a b h => (Prod.mk.inj h).2)
  rw [e1, e2, e3]
  ring

/-- **The expected information gain of the second bit is `log 2`**:
`EIG id bit2 bit1 = I[id : bit2 | bit1] = log 2`.
Source: [[generalization-final]] D10 l. 45; item 2-069(b)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem twoBits_EIG : EIG (id : Bool × Bool → Bool × Bool) bit2 bit1 pairMeasure = Real.log 2 := by
  unfold EIG
  rw [ShannonInformation.condMutualInfo_eq' measurable_id measurable_bit2 measurable_bit1
      pairMeasure,
    ShannonInformation.chain_rule'' pairMeasure measurable_id measurable_bit1,
    ShannonInformation.chain_rule'' pairMeasure measurable_id
      (measurable_bit2.prodMk measurable_bit1)]
  have e1 : H[(⟨id, bit1⟩ : Bool × Bool → (Bool × Bool) × Bool) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
    entropy_comp_id_pairMeasure (fun b => (b, b.1)) (fun a b h => (Prod.mk.inj h).1)
  have e2 : H[(⟨id, (⟨bit2, bit1⟩ : Bool × Bool → Bool × Bool)⟩ :
      Bool × Bool → (Bool × Bool) × (Bool × Bool)) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
    entropy_comp_id_pairMeasure (fun b => (b, (b.2, b.1))) (fun a b h => (Prod.mk.inj h).1)
  have e3 : H[(⟨bit2, bit1⟩ : Bool × Bool → Bool × Bool) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
    entropy_comp_id_pairMeasure (fun b => (b.2, b.1)) (fun a b h => by
      have := Prod.mk.inj h
      exact Prod.ext this.2 this.1)
  rw [e1, e2, e3, entropy_id_pairMeasure, entropy_bit1_pairMeasure, log_four]
  ring

/-- **The omitted redundancy direction is also `log 2`**: `redErr' id bit1 bit2 = I[id : bit1 | bit2]
= log 2`.
Source: [[generalization-final]] D10 l. 45; [[generalization-adversary]] A1.2 l. 28
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem twoBits_redErr' : redErr' (id : Bool × Bool → Bool × Bool) bit1 bit2 pairMeasure
    = Real.log 2 := by
  unfold redErr'
  rw [ShannonInformation.condMutualInfo_eq' measurable_id measurable_bit1 measurable_bit2
      pairMeasure,
    ShannonInformation.chain_rule'' pairMeasure measurable_id measurable_bit2,
    ShannonInformation.chain_rule'' pairMeasure measurable_id
      (measurable_bit1.prodMk measurable_bit2)]
  have e1 : H[(⟨id, bit2⟩ : Bool × Bool → (Bool × Bool) × Bool) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
    entropy_comp_id_pairMeasure (fun b => (b, b.2)) (fun a b h => (Prod.mk.inj h).1)
  have e2 : H[(⟨id, (⟨bit1, bit2⟩ : Bool × Bool → Bool × Bool)⟩ :
      Bool × Bool → (Bool × Bool) × (Bool × Bool)) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
    entropy_comp_id_pairMeasure (fun b => (b, (b.1, b.2))) (fun a b h => (Prod.mk.inj h).1)
  have e3 : H[(⟨bit1, bit2⟩ : Bool × Bool → Bool × Bool) ; pairMeasure]
      = H[(id : Bool × Bool → Bool × Bool) ; pairMeasure] :=
    entropy_comp_id_pairMeasure (fun b => (b.1, b.2)) (fun a b h => by
      have := Prod.mk.inj h
      exact Prod.ext this.1 this.2)
  rw [e1, e2, e3, entropy_id_pairMeasure, entropy_bit2_pairMeasure, log_four]
  ring

/-- **The two-bit latent mediates but is not natural**: `medErr = 0`, `EIG > 0`, and
`¬ NaturalOver`.
Source: [[generalization-final]] D9 l. 43, D10 l. 45; findings F1
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem twoBits_not_natural :
    medErr bit1 bit2 (id : Bool × Bool → Bool × Bool) pairMeasure = 0 ∧
    0 < EIG (id : Bool × Bool → Bool × Bool) bit2 bit1 pairMeasure ∧
    ¬ NaturalOver (id : Bool × Bool → Bool × Bool) bit1 bit2 pairMeasure := by
  refine ⟨twoBits_medErr, ?_, ?_⟩
  · rw [twoBits_EIG]
    exact Real.log_pos (by norm_num)
  · intro h
    have := h.2.1
    rw [twoBits_EIG] at this
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' this

/-! ### The natural witness -/

/-- The fair coin.
Source: none: infrastructure (FAF's `APITests/ShannonInformation.lean` l. 131)
Kind: D
Fidelity: exact -/
def coin : Measure Bool := uniformOn (Set.univ : Set Bool)

instance : IsProbabilityMeasure coin := by
  unfold coin
  infer_instance

/-- **A natural instance**: `Λ = X₁ = X₂ = id` on a fair coin is `NaturalOver` (all three errors
`0`), and is non-constant (`H[id] = log 2 > 0`). Degenerate: the three variables coincide, so
each `= 0` is `I[X : X | X] = 0`; it shows only that `NaturalOver` has a non-constant instance
(the mandate asked for exactly this; audit r1). An N+ natural triple is `NaturalLatents`'
four-bit witness (`Λ = (b, d)` mediates `X₁ = (b, n₁)`, `X₂ = (b, n₂)`).
Source: [[generalization-final]] D9 l. 43 (Target 1 witness)
Kind: N−
Fidelity: exact (degenerate: self-identical triple)
Hyps: (a) all -/
theorem natural_id :
    NaturalOver (id : Bool → Bool) id id coin ∧ 0 < H[(id : Bool → Bool) ; coin] := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact condMutualInfo_self_self measurable_id
  · exact condMutualInfo_self_self measurable_id
  · exact condMutualInfo_self_self measurable_id
  · have hu : IsUniform (Set.univ : Set Bool) id coin := isUniform_uniformOn
    have h := hu.entropy_eq' Set.finite_univ measurable_id
    rw [h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool]
    exact Real.log_pos (by norm_num)

end

end Cleanroom.Info.InfoVoiLatents.Eig
