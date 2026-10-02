import Cleanroom.Info.InfoVoiLatents.NaturalLatents

/-!
# info-voi-latents — the natural-latents witness that exercises the theorem (Target 10, N+)

Repair round 1 (audits r1 fidelity B2 / adversarial B1): the three-bit witness of
`NaturalLatentsWitness.lean` takes `Λ = X₁`, at which the conclusion of
`aeFunctionOf_of_mediates_detRedundant` is literally the first redundancy hypothesis and mediation
is `I[X₁ : X₂ | X₁] = 0`, automatic — grade N−. This file is the N+ witness both audits asked for.

Four uniform bits `ω = ((b, d), (n₁, n₂))`; chunks `X₁ = (b, n₁)`, `X₂ = (b, n₂)`; latent
`Λ = (b, d)` (the shared bit plus an independent die, so `Λ` is a function of *neither* chunk);
`Λ' = b`. Then:

* mediation `I[X₁ : X₂ | Λ] = 0` is a genuine computation
  (`log 8 − log 4 − (log 16 − log 8) = 0`, `condMutualInfo_X₁X₂_Λ4`), and it is a real hypothesis in
  this model: for the die alone, `I[X₁ : X₂ | d] = log 2 ≠ 0` (`die4_not_mediates`);
* `Λ` is strictly coarser than neither chunk: `H[Λ | X₁] = H[Λ | X₂] = log 2`, so `Λ` is not
  a.e. a function of either chunk (`Λ4_not_function_of_X₁4`, `Λ4_not_function_of_X₂4`) — the
  conclusion `AEFunctionOf Λ Λ'` is not among the hypotheses and is not `AEFunctionOf.refl`
  (`H[Λ | Λ'] = log 2`, `witness4_nondegenerate`);
* `Λ'` is a function of each chunk (two projections, `witness4_detRedundant`), non-constant
  (`H[Λ'] = log 2`), and the conclusion `AEFunctionOf Λ Λ'` is obtained *from the theorem*
  (`witness4_conclusion`).

Fibre masses are computed by one lemma (`μ4_preimage`), and uniformity of a variable from equal
fibre cardinalities (`isUniform_of_fibre`, `entropy_of_fibre`), the cardinalities themselves by
`decide` on the 16-element space; pair entropies are injective images (`entropy_comp_of_injective`).

Mandate: Target 10 witness; audit r1.
-/

namespace Cleanroom.Info.InfoVoiLatents.NaturalLatents

open MeasureTheory ProbabilityTheory ShannonInformation Finset
open Cleanroom.Info.InfoVoiLatents.Shannon
open _root_.Condensation

noncomputable section

/-- Four bits `((b, d), (n₁, n₂))`.
Source: none: infrastructure (witness)
Kind: D
Fidelity: exact -/
abbrev Ω4 : Type := (Bool × Bool) × (Bool × Bool)

/-- The uniform measure on four bits.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def μ4 : Measure Ω4 := uniformOn (Set.univ : Set Ω4)

instance : IsProbabilityMeasure μ4 := by
  unfold μ4
  infer_instance

/-- The first chunk `(b, n₁)`.
Source: [[wentworth-2023-natural-latents-the-math]] l. 65 (two chunks of a gas, in miniature)
Kind: D
Fidelity: exact -/
def X₁4 : Ω4 → Bool × Bool := fun ω => (ω.1.1, ω.2.1)

/-- The second chunk `(b, n₂)`.
Source: same
Kind: D
Fidelity: exact -/
def X₂4 : Ω4 → Bool × Bool := fun ω => (ω.1.1, ω.2.2)

/-- The latent `Λ = (b, d)`: the shared bit and an independent die — a function of neither chunk.
Source: Target 10 witness; audit r1 (fidelity B2, adversarial B1: "`Λ = (b, d)` for an independent
die `d`")
Kind: D
Fidelity: exact -/
def Λ4 : Ω4 → Bool × Bool := fun ω => ω.1

/-- The shared bit `b` (the "temperature above 50°C" latent `Λ'`).
Source: [[wentworth-2023-natural-latents-the-math]] l. 65
Kind: D
Fidelity: exact -/
def shared4 : Ω4 → Bool := fun ω => ω.1.1

/-- The die `d` alone (a latent for which mediation *fails*).
Source: none: infrastructure (witness)
Kind: D
Fidelity: exact -/
def die4 : Ω4 → Bool := fun ω => ω.1.2

/-- `(b, d, n₁)`: the uniform variable of which `⟨X₁, Λ⟩` is an injective image.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Y₁4 : Ω4 → Bool × Bool × Bool := fun ω => (ω.1.1, ω.1.2, ω.2.1)

/-- `(b, d, n₂)`: the uniform variable of which `⟨X₂, Λ⟩` is an injective image.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Y₂4 : Ω4 → Bool × Bool × Bool := fun ω => (ω.1.1, ω.1.2, ω.2.2)

/-- `measurable_X₁4`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_X₁4 : Measurable X₁4 := by
  unfold X₁4
  fun_prop

/-- `measurable_X₂4`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_X₂4 : Measurable X₂4 := by
  unfold X₂4
  fun_prop

/-- `measurable_Λ4`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_Λ4 : Measurable Λ4 := by
  unfold Λ4
  fun_prop

/-- `measurable_shared4`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_shared4 : Measurable shared4 := by
  unfold shared4
  fun_prop

/-- `measurable_die4`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_die4 : Measurable die4 := by
  unfold die4
  fun_prop

/-- `measurable_Y₁4`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_Y₁4 : Measurable Y₁4 := by
  unfold Y₁4
  fun_prop

/-- `measurable_Y₂4`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurable_Y₂4 : Measurable Y₂4 := by
  unfold Y₂4
  fun_prop

/-! ### Fibre masses and uniform entropies -/

/-- Every atom of `μ4` has mass `1/16`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem μ4_singleton (ω : Ω4) : μ4 {ω} = 1 / 16 := by
  rw [μ4, uniformOn_apply Set.finite_univ, Set.univ_inter, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Set.ncard_singleton, Set.ncard_univ, Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- The mass of a fibre of `X` under `μ4` is its cardinality over `16`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem μ4_preimage {L : Type} [DecidableEq L] (X : Ω4 → L) (x : L) :
    μ4 (X ⁻¹' {x}) = ((univ.filter fun ω => X ω = x).card : ENNReal) / 16 := by
  have hset : X ⁻¹' {x} = ↑(univ.filter fun ω => X ω = x) := by
    ext ω
    simp
  rw [μ4, uniformOn_apply Set.finite_univ, Set.univ_inter, hset, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Set.ncard_coe_finset, Set.ncard_univ, Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- A variable on four uniform bits whose fibres all have the same cardinality is uniform.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem isUniform_of_fibre {L : Type} [Fintype L] [DecidableEq L] [MeasurableSpace L]
    (X : Ω4 → L) (c : ℕ) (hc : ∀ x, (univ.filter fun ω => X ω = x).card = c) :
    IsUniform (Set.univ : Set L) X μ4 where
  eq_of_mem := by
    intro x _ y _
    rw [μ4_preimage, μ4_preimage, hc, hc]
  measure_preimage_compl := by
    rw [Set.compl_univ, Set.preimage_empty, measure_empty]

/-- The entropy of a variable with equal fibres is the log of the size of its range type.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_of_fibre {L : Type} [Fintype L] [DecidableEq L] [MeasurableSpace L]
    [MeasurableSingletonClass L] {X : Ω4 → L} (hX : Measurable X) (c : ℕ)
    (hc : ∀ x, (univ.filter fun ω => X ω = x).card = c) :
    H[X ; μ4] = Real.log (Fintype.card L) := by
  have h := (isUniform_of_fibre X c hc).entropy_eq' Set.finite_univ hX
  rw [h, Set.ncard_univ, Nat.card_eq_fintype_card]

/-- An injective image has the same entropy (restated for rewriting with an explicit equation).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_comp_eq {L L' : Type} [MeasurableSpace L] [MeasurableSpace L'] [Countable L]
    [MeasurableSingletonClass L] [MeasurableSingletonClass L'] {X : Ω4 → L} (hX : Measurable X)
    (Z : Ω4 → L') (f : L → L') (hf : Function.Injective f) (hZ : ∀ ω, Z ω = f (X ω)) :
    H[Z ; μ4] = H[X ; μ4] := by
  rw [show Z = f ∘ X from funext hZ]
  exact entropy_comp_of_injective μ4 hX f hf

/-- `H[Λ ; μ4] = log 4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_Λ4 : H[Λ4 ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre measurable_Λ4 4 (by decide), Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- `H[X₁ ; μ4] = log 4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_X₁4 : H[X₁4 ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre measurable_X₁4 4 (by decide), Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- `H[X₂ ; μ4] = log 4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_X₂4 : H[X₂4 ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre measurable_X₂4 4 (by decide), Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- `H[Λ' ; μ4] = log 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_shared4 : H[shared4 ; μ4] = Real.log 2 := by
  rw [entropy_of_fibre measurable_shared4 8 (by decide), Fintype.card_bool]
  norm_num

/-- `H[d ; μ4] = log 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_die4 : H[die4 ; μ4] = Real.log 2 := by
  rw [entropy_of_fibre measurable_die4 8 (by decide), Fintype.card_bool]
  norm_num

/-- `H[(b, d, n₁) ; μ4] = log 8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_Y₁4 : H[Y₁4 ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre measurable_Y₁4 2 (by decide)]
  simp only [Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- `H[(b, d, n₂) ; μ4] = log 8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_Y₂4 : H[Y₂4 ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre measurable_Y₂4 2 (by decide)]
  simp only [Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- `H[id ; μ4] = log 16`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_id4 : H[(id : Ω4 → Ω4) ; μ4] = Real.log 16 := by
  rw [entropy_of_fibre measurable_id 1 (by decide)]
  simp only [Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- `H[⟨X₁, Λ⟩ ; μ4] = log 8` (an injective image of `(b, d, n₁)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_X₁Λ4 : H[(⟨X₁4, Λ4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) ; μ4]
    = Real.log 8 := by
  rw [entropy_comp_eq measurable_Y₁4 (⟨X₁4, Λ4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool))
    (fun p : Bool × Bool × Bool => ((p.1, p.2.2), (p.1, p.2.1))) (by decide) (fun _ => rfl),
    entropy_Y₁4]

/-- `H[⟨X₂, Λ⟩ ; μ4] = log 8` (an injective image of `(b, d, n₂)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_X₂Λ4 : H[(⟨X₂4, Λ4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) ; μ4]
    = Real.log 8 := by
  rw [entropy_comp_eq measurable_Y₂4 (⟨X₂4, Λ4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool))
    (fun p : Bool × Bool × Bool => ((p.1, p.2.2), (p.1, p.2.1))) (by decide) (fun _ => rfl),
    entropy_Y₂4]

/-- `H[⟨Λ, X₁⟩ ; μ4] = log 8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_ΛX₁4 : H[(⟨Λ4, X₁4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) ; μ4]
    = Real.log 8 := by
  rw [entropy_comp_eq measurable_Y₁4 (⟨Λ4, X₁4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool))
    (fun p : Bool × Bool × Bool => ((p.1, p.2.1), (p.1, p.2.2))) (by decide) (fun _ => rfl),
    entropy_Y₁4]

/-- `H[⟨Λ, X₂⟩ ; μ4] = log 8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_ΛX₂4 : H[(⟨Λ4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) ; μ4]
    = Real.log 8 := by
  rw [entropy_comp_eq measurable_Y₂4 (⟨Λ4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool))
    (fun p : Bool × Bool × Bool => ((p.1, p.2.1), (p.1, p.2.2))) (by decide) (fun _ => rfl),
    entropy_Y₂4]

/-- `H[⟨X₁, ⟨X₂, Λ⟩⟩ ; μ4] = log 16` (an injective image of `id`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_triple_Λ4 :
    H[(⟨X₁4, ⟨X₂4, Λ4⟩⟩ : Ω4 → (Bool × Bool) × ((Bool × Bool) × (Bool × Bool))) ; μ4]
    = Real.log 16 := by
  rw [entropy_comp_eq measurable_id
    (⟨X₁4, ⟨X₂4, Λ4⟩⟩ : Ω4 → (Bool × Bool) × ((Bool × Bool) × (Bool × Bool)))
    (fun ω : Ω4 => ((ω.1.1, ω.2.1), ((ω.1.1, ω.2.2), ω.1))) (by decide) (fun _ => rfl),
    entropy_id4]

/-- `H[⟨X₁, d⟩ ; μ4] = log 8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_X₁die4 : H[(⟨X₁4, die4⟩ : Ω4 → (Bool × Bool) × Bool) ; μ4]
    = Real.log 8 := by
  rw [entropy_comp_eq measurable_Y₁4 (⟨X₁4, die4⟩ : Ω4 → (Bool × Bool) × Bool)
    (fun p : Bool × Bool × Bool => ((p.1, p.2.2), p.2.1)) (by decide) (fun _ => rfl),
    entropy_Y₁4]

/-- `H[⟨X₂, d⟩ ; μ4] = log 8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_X₂die4 : H[(⟨X₂4, die4⟩ : Ω4 → (Bool × Bool) × Bool) ; μ4]
    = Real.log 8 := by
  rw [entropy_comp_eq measurable_Y₂4 (⟨X₂4, die4⟩ : Ω4 → (Bool × Bool) × Bool)
    (fun p : Bool × Bool × Bool => ((p.1, p.2.2), p.2.1)) (by decide) (fun _ => rfl),
    entropy_Y₂4]

/-- `H[⟨X₁, ⟨X₂, d⟩⟩ ; μ4] = log 16`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_triple_die4 :
    H[(⟨X₁4, ⟨X₂4, die4⟩⟩ : Ω4 → (Bool × Bool) × ((Bool × Bool) × Bool)) ; μ4]
    = Real.log 16 := by
  rw [entropy_comp_eq measurable_id
    (⟨X₁4, ⟨X₂4, die4⟩⟩ : Ω4 → (Bool × Bool) × ((Bool × Bool) × Bool))
    (fun ω : Ω4 => ((ω.1.1, ω.2.1), ((ω.1.1, ω.2.2), ω.1.2))) (by decide) (fun _ => rfl),
    entropy_id4]

/-- `H[⟨Λ, Λ'⟩ ; μ4] = log 4` (`Λ'` is a projection of `Λ`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_Λshared4 : H[(⟨Λ4, shared4⟩ : Ω4 → (Bool × Bool) × Bool) ; μ4]
    = Real.log 4 := by
  rw [entropy_comp_eq measurable_Λ4 (⟨Λ4, shared4⟩ : Ω4 → (Bool × Bool) × Bool)
    (fun p : Bool × Bool => (p, p.1)) (by decide) (fun _ => rfl), entropy_Λ4]

/-- `log 8 − log 4 − (log 16 − log 8) = 0`, and its `log 2` relatives, as one arithmetic lemma.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem log_pow_two_facts :
    Real.log 4 = 2 * Real.log 2 ∧ Real.log 8 = 3 * Real.log 2 ∧ Real.log 16 = 4 * Real.log 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  · rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  · rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring

/-! ### The witness -/

/-- **Mediation is a genuine computation**: `I[X₁ : X₂ | Λ ; μ4] = H[X₁ | Λ] − H[X₁ | ⟨X₂, Λ⟩] =
(log 8 − log 4) − (log 16 − log 8) = 0`.
Source: [[wentworth-2023-natural-latents-the-math]] l. 31 (first diagram); Target 10 witness
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem condMutualInfo_X₁X₂_Λ4 : I[X₁4 : X₂4 | Λ4 ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨X₂4, Λ4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) μ4 :=
    finiteEntropyOf_pair measurable_X₂4 measurable_Λ4
  rw [ShannonInformation.condMutualInfo_eq' measurable_X₁4 measurable_X₂4 measurable_Λ4 μ4,
    ShannonInformation.chain_rule'' μ4 measurable_X₁4 measurable_Λ4,
    ShannonInformation.chain_rule'' μ4 measurable_X₁4 (measurable_X₂4.prodMk measurable_Λ4),
    entropy_pair_X₁Λ4, entropy_Λ4, entropy_triple_Λ4, entropy_pair_X₂Λ4]
  obtain ⟨h4, h8, h16⟩ := log_pow_two_facts
  rw [h4, h8, h16]
  ring

/-- **Mediation for `Λ = (b, d)`**: `CondIndepFun X₁ X₂ Λ μ4`, from the computation.
Source: [[wentworth-2023-natural-latents-the-math]] l. 31; Target 10 witness
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem witness4_mediates : Mediates Λ4 X₁4 X₂4 μ4 :=
  (ShannonInformation.condMutualInfo_eq_zero measurable_X₁4 measurable_X₂4 measurable_Λ4).1
    condMutualInfo_X₁X₂_Λ4

/-- **Deterministic redundancy of the shared bit**: `b` is a function of each chunk.
Source: [[wentworth-2023-natural-latents-the-math]] l. 65
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem witness4_detRedundant : DetRedundant X₁4 X₂4 shared4 μ4 :=
  ⟨aeFunctionOf_comp (X := X₁4) (f := (Prod.fst : Bool × Bool → Bool)) measurable_fst,
    aeFunctionOf_comp (X := X₂4) (f := (Prod.fst : Bool × Bool → Bool)) measurable_fst⟩

/-- **The conclusion at the witness, from the theorem**: `AEFunctionOf Λ Λ' μ4` — `b` is a.e. a
function of `(b, d)`. Not among the hypotheses (`Λ4_not_function_of_X₁4`,
`Λ4_not_function_of_X₂4`) and not `AEFunctionOf.refl` (`witness4_nondegenerate`).
Source: [[wentworth-2023-natural-latents-the-math]] l. 67
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem witness4_conclusion : AEFunctionOf Λ4 shared4 μ4 :=
  aeFunctionOf_of_mediates_detRedundant measurable_X₁4 measurable_X₂4 measurable_Λ4
    measurable_shared4 witness4_mediates witness4_detRedundant

/-- **`Λ` is not a function of `X₁`**: `H[Λ | X₁ ; μ4] = log 2 > 0`, so `¬ AEFunctionOf X₁ Λ` —
the conclusion of the theorem at this witness is not its first redundancy hypothesis.
Source: Target 10 witness; audit r1 (fidelity B2)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem Λ4_not_function_of_X₁4 : H[Λ4 | X₁4 ; μ4] = Real.log 2 ∧ ¬ AEFunctionOf X₁4 Λ4 μ4 := by
  have hH : H[Λ4 | X₁4 ; μ4] = Real.log 2 := by
    rw [ShannonInformation.chain_rule'' μ4 measurable_Λ4 measurable_X₁4, entropy_pair_ΛX₁4,
      entropy_X₁4]
    obtain ⟨h4, h8, -⟩ := log_pow_two_facts
    rw [h4, h8]
    ring
  refine ⟨hH, fun h => ?_⟩
  have := condEntropy_eq_zero_of_aeFunctionOf measurable_X₁4 measurable_Λ4 h
  rw [hH] at this
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' this

/-- **`Λ` is not a function of `X₂`**: `H[Λ | X₂ ; μ4] = log 2 > 0`.
Source: Target 10 witness; audit r1 (fidelity B2)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem Λ4_not_function_of_X₂4 : H[Λ4 | X₂4 ; μ4] = Real.log 2 ∧ ¬ AEFunctionOf X₂4 Λ4 μ4 := by
  have hH : H[Λ4 | X₂4 ; μ4] = Real.log 2 := by
    rw [ShannonInformation.chain_rule'' μ4 measurable_Λ4 measurable_X₂4, entropy_pair_ΛX₂4,
      entropy_X₂4]
    obtain ⟨h4, h8, -⟩ := log_pow_two_facts
    rw [h4, h8]
    ring
  refine ⟨hH, fun h => ?_⟩
  have := condEntropy_eq_zero_of_aeFunctionOf measurable_X₂4 measurable_Λ4 h
  rw [hH] at this
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' this

/-- **Mediation is a real hypothesis in this model**: for the die alone,
`I[X₁ : X₂ | d ; μ4] = log 2`, so `d` does not mediate — the chunks still share `b`.
Source: Target 10 witness; audit r1 (adversarial B1: "mediation is a real computation")
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem die4_not_mediates : I[X₁4 : X₂4 | die4 ; μ4] = Real.log 2 ∧ ¬ Mediates die4 X₁4 X₂4 μ4 := by
  haveI : FiniteEntropyOf (⟨X₂4, die4⟩ : Ω4 → (Bool × Bool) × Bool) μ4 :=
    finiteEntropyOf_pair measurable_X₂4 measurable_die4
  have hI : I[X₁4 : X₂4 | die4 ; μ4] = Real.log 2 := by
    rw [ShannonInformation.condMutualInfo_eq' measurable_X₁4 measurable_X₂4 measurable_die4 μ4,
      ShannonInformation.chain_rule'' μ4 measurable_X₁4 measurable_die4,
      ShannonInformation.chain_rule'' μ4 measurable_X₁4 (measurable_X₂4.prodMk measurable_die4),
      entropy_pair_X₁die4, entropy_die4, entropy_triple_die4, entropy_pair_X₂die4]
    obtain ⟨-, h8, h16⟩ := log_pow_two_facts
    rw [h8, h16]
    ring
  refine ⟨hI, fun h => ?_⟩
  have := (ShannonInformation.condMutualInfo_eq_zero measurable_X₁4 measurable_X₂4
    measurable_die4).2 h
  rw [hI] at this
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' this

/-- **Non-degeneracy**: every atom has positive mass; `Λ'` is not a.e. constant (`H[Λ'] = log 2`);
and `Λ` is strictly finer than `Λ'` (`H[Λ | Λ'] = log 2`), so the conclusion `AEFunctionOf Λ Λ'`
is not `AEFunctionOf.refl` and `Λ' ≠ Λ` as variables.
Source: Target 10 witness ("`Λ' ≠ Λ` and `Λ'` non-constant"); audit r1
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem witness4_nondegenerate :
    (∀ ω : Ω4, μ4 {ω} ≠ 0) ∧ H[shared4 ; μ4] = Real.log 2 ∧ H[Λ4 | shared4 ; μ4] = Real.log 2 := by
  refine ⟨fun ω => by rw [μ4_singleton]; norm_num, entropy_shared4, ?_⟩
  rw [ShannonInformation.chain_rule'' μ4 measurable_Λ4 measurable_shared4, entropy_pair_Λshared4,
    entropy_shared4]
  obtain ⟨h4, -, -⟩ := log_pow_two_facts
  rw [h4]
  ring

end

end Cleanroom.Info.InfoVoiLatents.NaturalLatents
