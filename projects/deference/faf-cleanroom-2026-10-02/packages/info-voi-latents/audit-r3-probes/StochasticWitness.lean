import Cleanroom.Info.InfoVoiLatents.NaturalLatentsWitnessFour
import Cleanroom.Info.InfoVoiLatents.NaturalLatentsStochastic

/-!
# info-voi-latents — audit round 3 (adversarial) probe: an N+ witness for the *stochastic*
natural-latents theorem, with strictly stochastic redundancy

Probe file, not imported by the library. Elaborated with `scripts/lean-check`.

The ledger's witness column for `natural_latents_stochastic` says the four-bit witness inhabits
it only through the deterministic reduction, and the report lists "a witness with *strictly*
stochastic redundancy" as not done. This probe builds one on the package's own four bits
`((b, d), (n₁, n₂))`: chunks `X₁ = (b, n₁)`, `X₂ = (b, n₂)` (the library's `X₁4`, `X₂4`), latent
`Λ = b` (`shared4`), and `Λ' = b ⊕ d` — a *noisy* copy of the shared bit (`d` is the noise). Then

* mediation `I[X₁ : X₂ | b] = 0`, both redundancies `I[Λ' : X₁ | X₂] = I[Λ' : X₂ | X₁] = 0`, and
  the third diagram `I[b : Λ' | X] = 0` hold — all genuine computations;
* the conclusion `Λ' ⊥ X | Λ` is obtained *from the theorem* (`stochastic_witness_conclusion`) and
  is also computed directly (`cmi_conclusion_b = 0`);
* redundancy is strictly stochastic: `H[Λ' | X₁] = H[Λ' | X₂] = log 2`, so `Λ'` is a.e. a function
  of neither chunk (`¬ AEFunctionOf X₁4 Lb`, `¬ AEFunctionOf X₂4 Lb`) — the deterministic
  reduction does *not* apply;
* the conclusion is not trivial: `H[Λ' | Λ] = log 2` (`Λ'` is not a function of `Λ`) and
  `H[Λ'] = log 2` (`Λ'` not constant).

So the stochastic theorem has an N+ witness in the package's own model; the repairer may promote
this file.
-/

namespace AuditR3

open MeasureTheory ProbabilityTheory ShannonInformation Finset
open Cleanroom.Info.InfoVoiLatents.Shannon
open Cleanroom.Info.InfoVoiLatents.NaturalLatents
open _root_.Condensation

noncomputable section

/-- `Λ' = b ⊕ d`. -/
def Lb : Ω4 → Bool := fun ω => Bool.xor ω.1.1 ω.1.2
/-- `(b, (n₁, n₂))`, the coordinates that survive when `d` is dropped. -/
def Yb : Ω4 → Bool × (Bool × Bool) := fun ω => (ω.1.1, (ω.2.1, ω.2.2))

theorem measurable_Lb : Measurable Lb := measurable_of_countable _
theorem measurable_Yb : Measurable Yb := measurable_of_countable _

/-! ### Entropies -/

theorem entropy_Lb : H[Lb ; μ4] = Real.log 2 := by
  rw [entropy_of_fibre measurable_Lb 8 (by decide), Fintype.card_bool]; norm_num

theorem entropy_Yb : H[Yb ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre measurable_Yb 2 (by decide), Fintype.card_prod, Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_X₁b : H[(⟨X₁4, shared4⟩ : Ω4 → (Bool × Bool) × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_comp_eq measurable_X₁4 (⟨X₁4, shared4⟩ : Ω4 → (Bool × Bool) × Bool)
    (fun p : Bool × Bool => (p, p.1)) (by decide) (fun _ => rfl), entropy_X₁4]

theorem entropy_X₂b : H[(⟨X₂4, shared4⟩ : Ω4 → (Bool × Bool) × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_comp_eq measurable_X₂4 (⟨X₂4, shared4⟩ : Ω4 → (Bool × Bool) × Bool)
    (fun p : Bool × Bool => (p, p.1)) (by decide) (fun _ => rfl), entropy_X₂4]

theorem entropy_X₁X₂b :
    H[(⟨X₁4, ⟨X₂4, shared4⟩⟩ : Ω4 → (Bool × Bool) × ((Bool × Bool) × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_comp_eq measurable_Yb (⟨X₁4, ⟨X₂4, shared4⟩⟩ : Ω4 → (Bool × Bool) × ((Bool × Bool) × Bool))
    (fun p : Bool × (Bool × Bool) => ((p.1, p.2.1), ((p.1, p.2.2), p.1))) (by decide)
    (fun _ => rfl), entropy_Yb]

theorem entropy_X₁X₂ : H[(⟨X₁4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_comp_eq measurable_Yb (⟨X₁4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool))
    (fun p : Bool × (Bool × Bool) => ((p.1, p.2.1), (p.1, p.2.2))) (by decide)
    (fun _ => rfl), entropy_Yb]

theorem entropy_X₂X₁ : H[(⟨X₂4, X₁4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_comp_eq measurable_Yb (⟨X₂4, X₁4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool))
    (fun p : Bool × (Bool × Bool) => ((p.1, p.2.2), (p.1, p.2.1))) (by decide)
    (fun _ => rfl), entropy_Yb]

theorem entropy_LbX₂ : H[(⟨Lb, X₂4⟩ : Ω4 → Bool × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre (measurable_Lb.prodMk measurable_X₂4) 2 (by decide), Fintype.card_prod,
    Fintype.card_prod, Fintype.card_bool]; norm_num

theorem entropy_LbX₁ : H[(⟨Lb, X₁4⟩ : Ω4 → Bool × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre (measurable_Lb.prodMk measurable_X₁4) 2 (by decide), Fintype.card_prod,
    Fintype.card_prod, Fintype.card_bool]; norm_num

theorem entropy_Lbb : H[(⟨Lb, shared4⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_Lb.prodMk measurable_shared4) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

/-- `(Λ', (X₁, X₂))` determines `ω` (`d = b ⊕ Λ'`): an injective image of `id`. -/
theorem entropy_LbX₁X₂ :
    H[(⟨Lb, ⟨X₁4, X₂4⟩⟩ : Ω4 → Bool × ((Bool × Bool) × (Bool × Bool))) ; μ4] = Real.log 16 := by
  rw [entropy_comp_eq measurable_id (⟨Lb, ⟨X₁4, X₂4⟩⟩ : Ω4 → Bool × ((Bool × Bool) × (Bool × Bool)))
    (fun ω : Ω4 => (Bool.xor ω.1.1 ω.1.2, ((ω.1.1, ω.2.1), (ω.1.1, ω.2.2)))) (by decide)
    (fun _ => rfl), entropy_id4]

theorem entropy_LbX₂X₁ :
    H[(⟨Lb, ⟨X₂4, X₁4⟩⟩ : Ω4 → Bool × ((Bool × Bool) × (Bool × Bool))) ; μ4] = Real.log 16 := by
  rw [entropy_comp_eq measurable_id (⟨Lb, ⟨X₂4, X₁4⟩⟩ : Ω4 → Bool × ((Bool × Bool) × (Bool × Bool)))
    (fun ω : Ω4 => (Bool.xor ω.1.1 ω.1.2, ((ω.1.1, ω.2.2), (ω.1.1, ω.2.1)))) (by decide)
    (fun _ => rfl), entropy_id4]

theorem entropy_bX₁X₂ :
    H[(⟨shared4, ⟨X₁4, X₂4⟩⟩ : Ω4 → Bool × ((Bool × Bool) × (Bool × Bool))) ; μ4] = Real.log 8 := by
  rw [entropy_comp_eq measurable_Yb (⟨shared4, ⟨X₁4, X₂4⟩⟩ : Ω4 → Bool × ((Bool × Bool) × (Bool × Bool)))
    (fun p : Bool × (Bool × Bool) => (p.1, ((p.1, p.2.1), (p.1, p.2.2)))) (by decide)
    (fun _ => rfl), entropy_Yb]

theorem entropy_bLbX₁X₂ :
    H[(⟨shared4, ⟨Lb, ⟨X₁4, X₂4⟩⟩⟩ : Ω4 → Bool × (Bool × ((Bool × Bool) × (Bool × Bool)))) ; μ4]
      = Real.log 16 := by
  rw [entropy_comp_eq measurable_id
    (⟨shared4, ⟨Lb, ⟨X₁4, X₂4⟩⟩⟩ : Ω4 → Bool × (Bool × ((Bool × Bool) × (Bool × Bool))))
    (fun ω : Ω4 => (ω.1.1, (Bool.xor ω.1.1 ω.1.2, ((ω.1.1, ω.2.1), (ω.1.1, ω.2.2))))) (by decide)
    (fun _ => rfl), entropy_id4]

theorem entropy_LbX₁X₂b :
    H[(⟨Lb, ⟨⟨X₁4, X₂4⟩, shared4⟩⟩ : Ω4 → Bool × (((Bool × Bool) × (Bool × Bool)) × Bool)) ; μ4]
      = Real.log 16 := by
  rw [entropy_comp_eq measurable_id
    (⟨Lb, ⟨⟨X₁4, X₂4⟩, shared4⟩⟩ : Ω4 → Bool × (((Bool × Bool) × (Bool × Bool)) × Bool))
    (fun ω : Ω4 => (Bool.xor ω.1.1 ω.1.2, (((ω.1.1, ω.2.1), (ω.1.1, ω.2.2)), ω.1.1))) (by decide)
    (fun _ => rfl), entropy_id4]

theorem entropy_X₁X₂b' :
    H[(⟨⟨X₁4, X₂4⟩, shared4⟩ : Ω4 → ((Bool × Bool) × (Bool × Bool)) × Bool) ; μ4] = Real.log 8 := by
  rw [entropy_comp_eq measurable_Yb (⟨⟨X₁4, X₂4⟩, shared4⟩ : Ω4 → ((Bool × Bool) × (Bool × Bool)) × Bool)
    (fun p : Bool × (Bool × Bool) => (((p.1, p.2.1), (p.1, p.2.2)), p.1)) (by decide)
    (fun _ => rfl), entropy_Yb]

/-! ### The four diagrams -/

theorem cmi_mediation_b : I[X₁4 : X₂4 | shared4 ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨X₂4, shared4⟩ : Ω4 → (Bool × Bool) × Bool) μ4 :=
    finiteEntropyOf_pair measurable_X₂4 measurable_shared4
  rw [ShannonInformation.condMutualInfo_eq' measurable_X₁4 measurable_X₂4 measurable_shared4 μ4,
    ShannonInformation.chain_rule'' μ4 measurable_X₁4 measurable_shared4,
    ShannonInformation.chain_rule'' μ4 measurable_X₁4 (measurable_X₂4.prodMk measurable_shared4),
    entropy_X₁b, entropy_shared4, entropy_X₁X₂b, entropy_X₂b]
  obtain ⟨h4, h8, -⟩ := log_pow_two_facts
  rw [h4, h8]; ring

theorem cmi_red₁_b : I[Lb : X₁4 | X₂4 ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨X₁4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) μ4 :=
    finiteEntropyOf_pair measurable_X₁4 measurable_X₂4
  rw [ShannonInformation.condMutualInfo_eq' measurable_Lb measurable_X₁4 measurable_X₂4 μ4,
    ShannonInformation.chain_rule'' μ4 measurable_Lb measurable_X₂4,
    ShannonInformation.chain_rule'' μ4 measurable_Lb (measurable_X₁4.prodMk measurable_X₂4),
    entropy_LbX₂, entropy_X₂4, entropy_LbX₁X₂, entropy_X₁X₂]
  obtain ⟨h4, h8, h16⟩ := log_pow_two_facts
  rw [h4, h8, h16]; ring

theorem cmi_red₂_b : I[Lb : X₂4 | X₁4 ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨X₂4, X₁4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) μ4 :=
    finiteEntropyOf_pair measurable_X₂4 measurable_X₁4
  rw [ShannonInformation.condMutualInfo_eq' measurable_Lb measurable_X₂4 measurable_X₁4 μ4,
    ShannonInformation.chain_rule'' μ4 measurable_Lb measurable_X₁4,
    ShannonInformation.chain_rule'' μ4 measurable_Lb (measurable_X₂4.prodMk measurable_X₁4),
    entropy_LbX₁, entropy_X₁4, entropy_LbX₂X₁, entropy_X₂X₁]
  obtain ⟨h4, h8, h16⟩ := log_pow_two_facts
  rw [h4, h8, h16]; ring

theorem cmi_third_b : I[shared4 : Lb | (⟨X₁4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨X₁4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) μ4 :=
    finiteEntropyOf_pair measurable_X₁4 measurable_X₂4
  haveI : FiniteEntropyOf (⟨Lb, ⟨X₁4, X₂4⟩⟩ : Ω4 → Bool × ((Bool × Bool) × (Bool × Bool))) μ4 :=
    finiteEntropyOf_pair measurable_Lb (measurable_X₁4.prodMk measurable_X₂4)
  rw [ShannonInformation.condMutualInfo_eq' measurable_shared4 measurable_Lb
      (measurable_X₁4.prodMk measurable_X₂4) μ4,
    ShannonInformation.chain_rule'' μ4 measurable_shared4 (measurable_X₁4.prodMk measurable_X₂4),
    ShannonInformation.chain_rule'' μ4 measurable_shared4
      (measurable_Lb.prodMk (measurable_X₁4.prodMk measurable_X₂4)),
    entropy_bX₁X₂, entropy_X₁X₂, entropy_bLbX₁X₂, entropy_LbX₁X₂]
  ring

theorem cmi_conclusion_b : I[Lb : (⟨X₁4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) | shared4 ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨X₁4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) μ4 :=
    finiteEntropyOf_pair measurable_X₁4 measurable_X₂4
  haveI : FiniteEntropyOf (⟨⟨X₁4, X₂4⟩, shared4⟩ : Ω4 → ((Bool × Bool) × (Bool × Bool)) × Bool) μ4 :=
    finiteEntropyOf_pair (measurable_X₁4.prodMk measurable_X₂4) measurable_shared4
  rw [ShannonInformation.condMutualInfo_eq' measurable_Lb (measurable_X₁4.prodMk measurable_X₂4)
      measurable_shared4 μ4,
    ShannonInformation.chain_rule'' μ4 measurable_Lb measurable_shared4,
    ShannonInformation.chain_rule'' μ4 measurable_Lb
      ((measurable_X₁4.prodMk measurable_X₂4).prodMk measurable_shared4),
    entropy_Lbb, entropy_shared4, entropy_LbX₁X₂b, entropy_X₁X₂b']
  obtain ⟨h4, h8, h16⟩ := log_pow_two_facts
  rw [h4, h8, h16]; ring

/-! ### Strictly stochastic, and the conclusion non-trivial -/

theorem Lb_not_function_of_X₁4 : H[Lb | X₁4 ; μ4] = Real.log 2 ∧ ¬ AEFunctionOf X₁4 Lb μ4 := by
  have hH : H[Lb | X₁4 ; μ4] = Real.log 2 := by
    rw [ShannonInformation.chain_rule'' μ4 measurable_Lb measurable_X₁4, entropy_LbX₁, entropy_X₁4]
    obtain ⟨h4, h8, -⟩ := log_pow_two_facts
    rw [h4, h8]; ring
  refine ⟨hH, fun h => ?_⟩
  have := condEntropy_eq_zero_of_aeFunctionOf measurable_X₁4 measurable_Lb h
  rw [hH] at this
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' this

theorem Lb_not_function_of_X₂4 : H[Lb | X₂4 ; μ4] = Real.log 2 ∧ ¬ AEFunctionOf X₂4 Lb μ4 := by
  have hH : H[Lb | X₂4 ; μ4] = Real.log 2 := by
    rw [ShannonInformation.chain_rule'' μ4 measurable_Lb measurable_X₂4, entropy_LbX₂, entropy_X₂4]
    obtain ⟨h4, h8, -⟩ := log_pow_two_facts
    rw [h4, h8]; ring
  refine ⟨hH, fun h => ?_⟩
  have := condEntropy_eq_zero_of_aeFunctionOf measurable_X₂4 measurable_Lb h
  rw [hH] at this
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' this

theorem Lb_not_function_of_shared4 :
    H[Lb | shared4 ; μ4] = Real.log 2 ∧ ¬ AEFunctionOf shared4 Lb μ4 := by
  have hH : H[Lb | shared4 ; μ4] = Real.log 2 := by
    rw [ShannonInformation.chain_rule'' μ4 measurable_Lb measurable_shared4, entropy_Lbb,
      entropy_shared4]
    obtain ⟨h4, -, -⟩ := log_pow_two_facts
    rw [h4]; ring
  refine ⟨hH, fun h => ?_⟩
  have := condEntropy_eq_zero_of_aeFunctionOf measurable_shared4 measurable_Lb h
  rw [hH] at this
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' this

/-- **The hypothesis package of `natural_latents_stochastic`, inhabited with strictly stochastic
redundancy, and its conclusion obtained from the theorem.** -/
theorem stochastic_witness_conclusion :
    Mediates shared4 X₁4 X₂4 μ4 ∧ StochRedundant X₁4 X₂4 Lb μ4 ∧
    ThirdDiagram X₁4 X₂4 shared4 Lb μ4 ∧
    CondIndepFun Lb (⟨X₁4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) shared4 μ4 := by
  haveI : FiniteEntropyOf (⟨X₁4, X₂4⟩ : Ω4 → (Bool × Bool) × (Bool × Bool)) μ4 :=
    finiteEntropyOf_pair measurable_X₁4 measurable_X₂4
  have hmed : Mediates shared4 X₁4 X₂4 μ4 :=
    (ShannonInformation.condMutualInfo_eq_zero measurable_X₁4 measurable_X₂4
      measurable_shared4).1 cmi_mediation_b
  have hred : StochRedundant X₁4 X₂4 Lb μ4 :=
    ⟨(ShannonInformation.condMutualInfo_eq_zero measurable_Lb measurable_X₁4 measurable_X₂4).1
        cmi_red₁_b,
      (ShannonInformation.condMutualInfo_eq_zero measurable_Lb measurable_X₂4 measurable_X₁4).1
        cmi_red₂_b⟩
  have hthird : ThirdDiagram X₁4 X₂4 shared4 Lb μ4 :=
    (ShannonInformation.condMutualInfo_eq_zero measurable_shared4 measurable_Lb
      (measurable_X₁4.prodMk measurable_X₂4)).1 cmi_third_b
  exact ⟨hmed, hred, hthird,
    natural_latents_stochastic' measurable_X₁4 measurable_X₂4 measurable_shared4 measurable_Lb
      hmed hred hthird⟩

/-- **Non-degeneracy**: `Λ'` is a function of neither chunk (strictly stochastic redundancy), not
a function of `Λ`, and not constant. -/
theorem stochastic_witness_nondegenerate :
    ¬ AEFunctionOf X₁4 Lb μ4 ∧ ¬ AEFunctionOf X₂4 Lb μ4 ∧ ¬ AEFunctionOf shared4 Lb μ4 ∧
    H[Lb ; μ4] = Real.log 2 :=
  ⟨Lb_not_function_of_X₁4.2, Lb_not_function_of_X₂4.2, Lb_not_function_of_shared4.2, entropy_Lb⟩

end

end AuditR3
