import Cleanroom.Decision.DpDevicesCatalog.Devices
import Cleanroom.Decision.DpDevicesCatalog.Remark314

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T8, the Told-You-So column of the device table (CA-20′)

| device | verdict | declaration |
|---|---|---|
| D1 | `C₀` (rejects `C*` for every state) | `procFiveTen_limitStateEdt`, `procTake10_not_limitStateEdt` (`Remark314.lean`) |
| D2 | `C₀` (rejects `C*` at every `ε`) | `tys_d2_inverts` (`ToldYouSo.lean`) |
| D4 | `C₀` — **for every procedure**: `AdviceEdt ↔ C = C₀` | `tys_adviceEdt_iff` |
| D3 (`ε > 0`) | `C*` | `procTake10_occTrembleEdtConsistent` (`ToldYouSo.lean`) |
| D3⁰ | `C*`, not `C₀` | `procTake10_occEdtConsistent` (`ToldYouSo.lean`) |
| Dev pure / mixed | `C*`, not `C₀` | `procTake10_coherent`, `procFiveTen_not_coherent` |
| `V`-optimal | `C*`, not `C₀` | `procTake10_isOptimal`, `procFiveTen_not_isOptimal` |
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-- `C₀` is not `V`-optimal (`5 < 10`). Source: `calibration.md` CA-20′ (`V`-optimal row).
Kind: N+ -/
theorem procFiveTen_not_isOptimal : ¬ IsOptimal procFiveTen toldYouSo := by
  intro h
  have := h procTake10
  rw [procFiveTen_value, procTake10_value] at this
  norm_num at this

/-- `C₀` is not (mixed) coherent, since not pure-coherent at `d₅`.
Source: `calibration.md` CA-20′ (Dev rows). Kind: L -/
theorem procFiveTen_not_coherent : ¬ Coherent procFiveTen toldYouSo := fun h =>
  procFiveTen_not_coherentPureAt_five (CoherentAt.pure _ _ (h .five (tys_queried .five)))

/-- The tremble-realizability of the four act-within-observation events of `B_P`: `{five} ∧ O₅`,
`{ten} ∧ O₁₀`, `{five} ∧ O₁₀` are realizable, `{ten} ∧ O₅` is not (no leaf-world).
Source: none: infrastructure. Kind: L -/
theorem tys_nuPoly_actObs (C : Proc Five10 (fun _ => Five10) ℚ) :
    nuPoly C toldYouSo (tysActEv .five .five ∩ tysObs .five) ≠ 0 ∧
    nuPoly C toldYouSo (tysActEv .five .ten ∩ tysObs .five) = 0 ∧
    nuPoly C toldYouSo (tysActEv .ten .ten ∩ tysObs .ten) ≠ 0 ∧
    nuPoly C toldYouSo (tysActEv .ten .five ∩ tysObs .ten) ≠ 0 := by
  obtain ⟨⟨a1, -, -⟩, ⟨b1, b2, b3⟩, ⟨-, c2, -⟩, ⟨-, -, d3⟩⟩ := tys_actEv_obs_mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact nuPoly_ne_zero_of_leaf C _ _ ⟨.five, ()⟩ (by simpa [toldYouSo] using a1)
      (by unfold toldYouSo; simp [chanceWeight])
  · apply nuPoly_eq_zero_of_no_leaf
    intro ℓ
    unfold toldYouSo at ℓ
    rcases ℓ with ⟨a, ℓ⟩
    cases a
    · simpa [toldYouSo] using b1
    · rcases ℓ with ⟨b, _⟩
      cases b
      · simpa [toldYouSo] using b3
      · simpa [toldYouSo] using b2
  · exact nuPoly_ne_zero_of_leaf C _ _ ⟨.ten, .ten, ()⟩ (by simpa [toldYouSo] using c2)
      (by unfold toldYouSo; simp [chanceWeight])
  · exact nuPoly_ne_zero_of_leaf C _ _ ⟨.ten, .five, ()⟩ (by simpa [toldYouSo] using d3)
      (by unfold toldYouSo; simp [chanceWeight])

/-- The tremble-limit act values on `B_P`: `5` at `{five} ∧ O₅`, `10` and `5` at `d₁₀`
(constant-payoff events).
Source: `calibration.md` CA-20′ (D4 row). Kind: L -/
theorem tys_limitVal (C : Proc Five10 (fun _ => Five10) ℚ) :
    limitVal C toldYouSo (tysActEv .five .five ∩ tysObs .five) = 5 ∧
    limitVal C toldYouSo (tysActEv .ten .ten ∩ tysObs .ten) = 10 ∧
    limitVal C toldYouSo (tysActEv .ten .five ∩ tysObs .ten) = 5 := by
  obtain ⟨n1, -, n3, n4⟩ := tys_nuPoly_actObs C
  have pay : ∀ ℓ : toldYouSo.Leaves, payoff toldYouSo ℓ = (world toldYouSo ℓ).2.val := by
    intro ℓ; unfold toldYouSo at ℓ ⊢
    rcases ℓ with ⟨a, ℓ⟩
    cases a
    · rfl
    · rcases ℓ with ⟨b, _⟩; cases b <;> rfl
  refine ⟨limitVal_of_const _ _ _ _ (fun ℓ h => ?_) n1, limitVal_of_const _ _ _ _ (fun ℓ h => ?_) n3,
    limitVal_of_const _ _ _ _ (fun ℓ h => ?_) n4⟩ <;>
  · rw [pay]
    simp only [tysActEv, tysObs, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    rw [h.1]; rfl

/-- **D4 on Told-You-So approves exactly `C₀`**, for every procedure: at `d₅` the only
tremble-realizable act event is `five` (so `supp C(d₅) ⊆ {five}`), at `d₁₀` the limit values
are `10` (ten) and `5` (five).
Source: `calibration.md` CA-20′ (D4 row, Told-You-So: "`C₀`")
Kind: P
Fidelity: stronger (every procedure)
Hyps: none -/
theorem tys_adviceEdt_iff (C : Proc Five10 (fun _ => Five10) ℚ) :
    AdviceEdt tysObs tysActEv C toldYouSo ↔ C = procFiveTen := by
  obtain ⟨n1, n2, n3, n4⟩ := tys_nuPoly_actObs C
  obtain ⟨l1, l3, l4⟩ := tys_limitVal C
  constructor
  · intro h
    have h5 : (C .five).w .ten = 0 := by
      by_contra hne
      have hpos : 0 < (C .five).w .ten := lt_of_le_of_ne ((C .five).nonneg _) (Ne.symm hne)
      have := (h .five (tys_queried .five) (tys_nuPoly_obs_five_ne_zero C) ⟨.five, n1⟩ .ten hpos).1
      exact this n2
    have h10 : (C .ten).w .five = 0 := by
      by_contra hne
      have hpos : 0 < (C .ten).w .five := lt_of_le_of_ne ((C .ten).nonneg _) (Ne.symm hne)
      have := (h .ten (tys_queried .ten) (tys_nuPoly_obs_ten_ne_zero C) ⟨.ten, n3⟩ .five hpos).2
        .ten n3
      rw [l3, l4] at this
      norm_num at this
    have h5' : (C .five).w .five = 1 := by
      have := (C .five).sum_one; rw [Five10.sum_univ] at this; linarith
    have h10' : (C .ten).w .ten = 1 := by
      have := (C .ten).sum_one; rw [Five10.sum_univ] at this; linarith
    funext d; apply FinDistr.ext'; intro a
    cases d <;> cases a <;> simp [procFiveTen, h5, h10, h5', h10']
  · rintro rfl
    intro d _ _ _ a ha
    cases d <;> cases a <;> simp [procFiveTen] at ha
    · refine ⟨n1, fun b hb => ?_⟩
      cases b
      · exact le_rfl
      · exact absurd n2 hb
    · refine ⟨n3, fun b _ => ?_⟩
      cases b
      · rw [l3, l4]; norm_num
      · exact le_rfl

end Cleanroom.Decision.DpDevicesCatalog
