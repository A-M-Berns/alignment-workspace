import Cleanroom.Info.InfoVoiLatents.NaturalLatentsWitnessFour
import Cleanroom.Info.InfoVoiLatents.HazardMeans

/-!
# info-voi-latents — audit round 3 (adversarial) probe: a non-trivial-`Z` witness for the
component-hazard chain (Target 9(c), (e))

Probe file, not imported by the library. Elaborated with `scripts/lean-check`.

Target 9's witness ("the D6 parameter set with a non-trivial `Z`") has been "not attempted"
through three rounds; the ledger's row for `condMutualInfo_press_le` says the hypothesis package
is inhabited by constants only. The mandate's trap is that a constant `Z` makes (a)/(c)
unconditional and trivial. This probe supplies the minimal model that escapes the trap, on the
package's four bits `((b, d), (n₁, n₂))`: component `Θ = b`, agent's information `Z = d`, loss
`X = b ⊕ d`. Then

* `I[X : Θ] = 0` — unconditionally the loss is independent of the component (a fair coin xor'd
  with an independent fair coin), so a *constant* `Z` would make (c) read `0 ≤ log 2`;
* `I[X : Θ | Z] = log 2 = H[Θ | Z]` — conditioning on the agent's information creates the
  dependence, and (c) `I[X : Θ | Z] ≤ H[Θ | Z]` is *tight* here;
* at `Z = Θ` both sides vanish (`condMutualInfo_self_left`, `condEntropy_self`);
* an inert, non-constant press for (e): `Pr = n₁` has `I[X : Pr | Z] = 0`, so
  `condMean_eq_of_inert` applies at every positive-mass cell with a press that varies.

Not D6's parameter set (that remains not attempted); a model in which `Z` is load-bearing.
-/

namespace AuditR3

open MeasureTheory ProbabilityTheory ShannonInformation Finset
open Cleanroom.Info.InfoVoiLatents.Shannon
open Cleanroom.Info.InfoVoiLatents.NaturalLatents
open Cleanroom.Info.InfoVoiLatents.Hazard Cleanroom.Info.InfoVoiLatents.Eig
open Cleanroom.Found.LitDdbFrames

noncomputable section

/-- The loss `X = b ⊕ d`. -/
def Xh : Ω4 → Bool := fun ω => Bool.xor ω.1.1 ω.1.2
/-- The press `Pr = n₁` (independent noise). -/
def N₁h : Ω4 → Bool := fun ω => ω.2.1

theorem measurable_Xh : Measurable Xh := measurable_of_countable _
theorem measurable_N₁h : Measurable N₁h := measurable_of_countable _

theorem entropy_Xh : H[Xh ; μ4] = Real.log 2 := by
  rw [entropy_of_fibre measurable_Xh 8 (by decide), Fintype.card_bool]; norm_num

theorem entropy_Xh_die : H[(⟨Xh, die4⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_Xh.prodMk measurable_die4) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_Xh_shared : H[(⟨Xh, shared4⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_Xh.prodMk measurable_shared4) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_shared_die : H[(⟨shared4, die4⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_shared4.prodMk measurable_die4) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

/-- `(X, (Θ, Z))` is an injective image of `(b, d)`. -/
theorem entropy_Xh_shared_die :
    H[(⟨Xh, ⟨shared4, die4⟩⟩ : Ω4 → Bool × (Bool × Bool)) ; μ4] = Real.log 4 := by
  rw [entropy_comp_eq measurable_Λ4 (⟨Xh, ⟨shared4, die4⟩⟩ : Ω4 → Bool × (Bool × Bool))
    (fun p : Bool × Bool => (Bool.xor p.1 p.2, p)) (by decide) (fun _ => rfl), entropy_Λ4]

theorem entropy_N₁h_die : H[(⟨N₁h, die4⟩ : Ω4 → Bool × Bool) ; μ4] = Real.log 4 := by
  rw [entropy_of_fibre (measurable_N₁h.prodMk measurable_die4) 4 (by decide), Fintype.card_prod,
    Fintype.card_bool]; norm_num

theorem entropy_Xh_N₁h_die :
    H[(⟨Xh, ⟨N₁h, die4⟩⟩ : Ω4 → Bool × (Bool × Bool)) ; μ4] = Real.log 8 := by
  rw [entropy_of_fibre (measurable_Xh.prodMk (measurable_N₁h.prodMk measurable_die4)) 2 (by decide),
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]; norm_num

/-- **(c) with a non-trivial `Z`**: `I[X : Θ | Z] = log 2`. -/
theorem cmi_X_Theta_Z : I[Xh : shared4 | die4 ; μ4] = Real.log 2 := by
  haveI : FiniteEntropyOf (⟨shared4, die4⟩ : Ω4 → Bool × Bool) μ4 :=
    finiteEntropyOf_pair measurable_shared4 measurable_die4
  rw [ShannonInformation.condMutualInfo_eq' measurable_Xh measurable_shared4 measurable_die4 μ4,
    ShannonInformation.chain_rule'' μ4 measurable_Xh measurable_die4,
    ShannonInformation.chain_rule'' μ4 measurable_Xh (measurable_shared4.prodMk measurable_die4),
    entropy_Xh_die, entropy_die4, entropy_Xh_shared_die, entropy_shared_die]
  obtain ⟨h4, -, -⟩ := log_pow_two_facts
  rw [h4]; ring

/-- `H[Θ | Z] = log 2`: (c) is tight at this model. -/
theorem condEntropy_Theta_Z : H[shared4 | die4 ; μ4] = Real.log 2 := by
  rw [ShannonInformation.chain_rule'' μ4 measurable_shared4 measurable_die4, entropy_shared_die,
    entropy_die4]
  obtain ⟨h4, -, -⟩ := log_pow_two_facts
  rw [h4]; ring

/-- **`Z` is load-bearing**: unconditionally `I[X : Θ] = 0`. -/
theorem mi_X_Theta : I[Xh : shared4 ; μ4] = 0 := by
  rw [mutualInfo_def, entropy_Xh, entropy_shared4, entropy_Xh_shared]
  obtain ⟨h4, -, -⟩ := log_pow_two_facts
  rw [h4]; ring

/-- At `Z = Θ` both sides of (c) vanish. -/
theorem at_Z_eq_Theta : I[Xh : shared4 | shared4 ; μ4] = 0 ∧ H[shared4 | shared4 ; μ4] = 0 :=
  ⟨by
    rw [condMutualInfo_comm measurable_Xh measurable_shared4 shared4 μ4]
    exact condMutualInfo_self_left measurable_shared4 measurable_Xh,
   condEntropy_self measurable_shared4⟩

/-- **(c) at the model**: `I[X : Θ | Z] = H[Θ | Z] = log 2 > 0 = I[X : Θ]`, and both vanish at
`Z = Θ`. -/
theorem hazard_witness :
    I[Xh : shared4 | die4 ; μ4] = Real.log 2 ∧ H[shared4 | die4 ; μ4] = Real.log 2 ∧
    I[Xh : shared4 ; μ4] = 0 ∧ 0 < Real.log 2 ∧
    I[Xh : shared4 | shared4 ; μ4] = 0 ∧ H[shared4 | shared4 ; μ4] = 0 :=
  ⟨cmi_X_Theta_Z, condEntropy_Theta_Z, mi_X_Theta, Real.log_pos (by norm_num), at_Z_eq_Theta.1,
    at_Z_eq_Theta.2⟩

/-! ### (e): an inert, non-constant press -/

/-- `I[X : n₁ | d] = 0`: the noise press is inert. -/
theorem cmi_press_inert : I[Xh : N₁h | die4 ; μ4] = 0 := by
  haveI : FiniteEntropyOf (⟨N₁h, die4⟩ : Ω4 → Bool × Bool) μ4 :=
    finiteEntropyOf_pair measurable_N₁h measurable_die4
  rw [ShannonInformation.condMutualInfo_eq' measurable_Xh measurable_N₁h measurable_die4 μ4,
    ShannonInformation.chain_rule'' μ4 measurable_Xh measurable_die4,
    ShannonInformation.chain_rule'' μ4 measurable_Xh (measurable_N₁h.prodMk measurable_die4),
    entropy_Xh_die, entropy_die4, entropy_Xh_N₁h_die, entropy_N₁h_die]
  obtain ⟨h4, h8, -⟩ := log_pow_two_facts
  rw [h4, h8]; ring

/-- The press is not constant. -/
theorem press_nonconstant : ∃ ω ω' : Ω4, N₁h ω ≠ N₁h ω' :=
  ⟨((true, true), (true, true)), ((true, true), (false, true)), by decide⟩

/-- **(e) applied with a non-constant press**: conditional means agree at every positive-mass
cell, for every bounded `v`. -/
theorem inert_press_means (v : Bool → ℝ) (z p : Bool) (hpz : pm2 μ4 N₁h die4 p z ≠ 0) :
    E (condLaw2 μ4 Xh N₁h die4 z p) v = E (condLaw μ4 Xh die4 z) v :=
  condMean_eq_of_inert measurable_Xh measurable_N₁h measurable_die4 cmi_press_inert v hpz

end

end AuditR3
