import Cleanroom.Decision.DpSmokingLesion.Prop11
import Cleanroom.Decision.DpSmokingLesion.Tickle12

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# Stretch: T17 (E2a's closed forms in `π`) and T19 (the hidden-state action law)

* **T17** (`e2aPi_half`, `e2aPi_smoke`): on E2a with the agent's share `π` a parameter, at
  `C(d) = ½` the two act events have mass `½` each and
  `V(smoke) − V(refrain) = 1000(784π − 783)`, so refrain is the evidential argmax iff
  `π < 783/784`; at `δ_smoke`, `V(smoke) − V(refrain) = 1000(π − 783)/(π + 1) < 0` for every
  `π ≤ 1` — the unplayed act is priced by the reference class.
* **T19** (`slOne_action_law_flat`, `tickle_action_law_depends`): Everitt–Leike–Hutter's
  hidden-state action law — on `slOne`, for **every** procedure (hence every self-model),
  `ν(m ∣ ℓ=1) = ν(m ∣ ℓ=0)` (cross-multiplied): under Definition 6 at a single point the act
  law cannot depend on the hidden state; an `ℓ`-dependent law is realizable only across two
  points, and on the tickle tree it is `ℓ`-dependent iff `q₁ ≠ q₀`.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-! ## T17: E2a with the share `π` as a parameter -/

section e2aPi

variable (π : ℚ) (p0 : 0 ≤ π) (p1 : π ≤ 1)

/-- E2a at S3's lesion, rates and payoffs with the agent's share `π` free.
Source: `sl-defensible-claims.md` S3; dp-sl-2-060 ("E2a's closed forms in `π`")
Kind: D -/
def e2aPi : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 Lesion.fdt.coinL fun i =>
    .chance 2 (FinDistr.coin π p0 p1) ![e2aMe i, e2aOther i]

/-- `e2aPi` is the catalogue tree `e2a` at those parameters. Source: none: infrastructure. Kind: L -/
theorem e2aPi_eq : e2aPi π p0 p1 = e2a π p0 p1 Lesion.fdt RefClass.s3 1000 1000000 := rfl

/-- A sum over the leaves of `e2aPi`. Source: none: infrastructure. Kind: L -/
theorem e2aPi_sum (f : (e2aPi π p0 p1).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ m : Bool, ∑ j : Fin 2, f ⟨i, 0, m, j, ()⟩) +
      ∑ j : Fin 2, ∑ k : Fin 2, f ⟨i, 1, j, k, ()⟩) := by
  unfold e2aPi at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : (e2aMe i).Leaves, f ⟨i, 0, ℓ⟩) + (∑ ℓ : (e2aOther i).Leaves, f ⟨i, 1, ℓ⟩) = _
  congr 1
  · unfold e2aMe kBlock slLeaf
    rw [sum_leaves_decision]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  · unfold e2aOther kBlock slLeaf
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Tree.sum_leaves_leaf _ _ _

/-- The "me" leaf masses of `e2aPi`. Source: Definition 6. Kind: L -/
theorem e2aPi_leafLaw_me (C : Proc Unit (fun _ => Bool) ℚ) (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw C (e2aPi π p0 p1) ⟨i, 0, m, j, ()⟩ =
      (1/2 : ℚ) * π * (C ()).w m *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100)) := by
  unfold e2aPi
  rw [leafLaw_chance, leafLaw_chance]
  show (Lesion.fdt.coinL).w i * ((FinDistr.coin π p0 p1).w 0 * leafLaw C (e2aMe i) ⟨m, j, ()⟩) = _
  unfold e2aMe kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, Lesion.coinL, Lesion.coinK,
    FinDistr.coin, tickleGamma, Lesion.fdt]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The "other" leaf masses of `e2aPi`. Source: Definition 6. Kind: L -/
theorem e2aPi_leafLaw_other (C : Proc Unit (fun _ => Bool) ℚ) (i j k : Fin 2) :
    leafLaw C (e2aPi π p0 p1) ⟨i, 1, j, k, ()⟩ =
      (1/2 : ℚ) * (1 - π) *
        (if i = 0 then (if j = 0 then 9/10 else 1/10) else (if j = 0 then 1/10 else 9/10)) *
        (if i = 0 then (if k = 0 then 99/100 else 1/100) else (if k = 0 then 1/100 else 99/100)) := by
  unfold e2aPi
  rw [leafLaw_chance, leafLaw_chance]
  show (Lesion.fdt.coinL).w i * ((FinDistr.coin π p0 p1).w 1 * leafLaw C (e2aOther i) ⟨j, k, ()⟩) = _
  unfold e2aOther kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_leaf, Lesion.coinL, Lesion.coinK, RefClass.coinM,
    FinDistr.coin, tickleGamma, Lesion.fdt, RefClass.s3]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp <;> ring

/-- The act masses and payoff masses on `e2aPi` as closed forms in `π` and `q = C(d)(smoke)`:
`ν(m=1) = πq − π/2 + ½`, `ν(m=0) = −πq + π/2 + ½`,
`paySum(m=1) = −499 000 πq + 445 500 π − 445 500`, `paySum(m=0) = 500 000 πq − 446 000 π − 54 000`.
Source: dp-sl-2-060; mandate T17
Kind: P
Fidelity: exact -/
theorem e2aPi_values (C : Proc Unit (fun _ => Bool) ℚ) :
    nu C (e2aPi π p0 p1) (evM true) = π * (C ()).w true - π / 2 + 1/2 ∧
    nu C (e2aPi π p0 p1) (evM false) = -(π * (C ()).w true) + π / 2 + 1/2 ∧
    paySum C (e2aPi π p0 p1) (evM true) = -499000 * (π * (C ()).w true) + 445500 * π - 445500 ∧
    paySum C (e2aPi π p0 p1) (evM false) = 500000 * (π * (C ()).w true) - 446000 * π - 54000 := by
  have hw := w_false_eq_one_sub C
  have hnu : ∀ X, nu C (e2aPi π p0 p1) X = ∑ i : Fin 2, ((∑ m : Bool, ∑ j : Fin 2,
      if (decide (i = 0), m, decide (j = 0)) ∈ X then leafLaw C (e2aPi π p0 p1) ⟨i, 0, m, j, ()⟩ else 0) +
      ∑ j : Fin 2, ∑ k : Fin 2, if (decide (i = 0), decide (j = 0), decide (k = 0)) ∈ X then
        leafLaw C (e2aPi π p0 p1) ⟨i, 1, j, k, ()⟩ else 0) := by
    intro X; rw [nu_eq_sum, e2aPi_sum]; rfl
  have hpay : ∀ X, paySum C (e2aPi π p0 p1) X = ∑ i : Fin 2, ((∑ m : Bool, ∑ j : Fin 2,
      if (decide (i = 0), m, decide (j = 0)) ∈ X then
        leafLaw C (e2aPi π p0 p1) ⟨i, 0, m, j, ()⟩ * ticklePay 1000 1000000 (decide (i = 0), m, decide (j = 0))
      else 0) +
      ∑ j : Fin 2, ∑ k : Fin 2, if (decide (i = 0), decide (j = 0), decide (k = 0)) ∈ X then
        leafLaw C (e2aPi π p0 p1) ⟨i, 1, j, k, ()⟩ *
          ticklePay 1000 1000000 (decide (i = 0), decide (j = 0), decide (k = 0)) else 0) := by
    intro X; rw [paySum_eq_sum_ite, e2aPi_sum]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, e2aPi_leafLaw_me, e2aPi_leafLaw_other, mem_evM]
    simp; ring
  · rw [hnu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, e2aPi_leafLaw_me, e2aPi_leafLaw_other, mem_evM]
    simp [hw]; ring
  · rw [hpay]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, e2aPi_leafLaw_me, e2aPi_leafLaw_other, mem_evM,
      ticklePay]
    simp; ring
  · rw [hpay]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, e2aPi_leafLaw_me, e2aPi_leafLaw_other, mem_evM,
      ticklePay]
    simp [hw]; ring

/-- The fair one-point procedure `C(d)(smoke) = ½`. Source: none: infrastructure. Kind: D -/
def procHalf : Proc Unit (fun _ => Bool) ℚ := procBool (1/2) (by norm_num) (by norm_num)

/-- **T17 at `C(d) = ½`**: both act events have mass `½`, and
`V(smoke) − V(refrain) = 1000(784π − 783)`, so refrain is the evidential argmax iff `π < 783/784`.
Source: dp-sl-2-060 ("`V(smk) − V(ref) = 1000(784π − 783)`, refrain iff `π < 783/784`");
mandate T17
Kind: P
Fidelity: exact -/
theorem e2aPi_half :
    nu procHalf (e2aPi π p0 p1) (evM true) = 1/2 ∧ nu procHalf (e2aPi π p0 p1) (evM false) = 1/2 ∧
      paySum procHalf (e2aPi π p0 p1) (evM true) / nu procHalf (e2aPi π p0 p1) (evM true) -
        paySum procHalf (e2aPi π p0 p1) (evM false) / nu procHalf (e2aPi π p0 p1) (evM false) =
          1000 * (784 * π - 783) ∧
      (paySum procHalf (e2aPi π p0 p1) (evM true) / nu procHalf (e2aPi π p0 p1) (evM true) <
        paySum procHalf (e2aPi π p0 p1) (evM false) / nu procHalf (e2aPi π p0 p1) (evM false) ↔
          π < 783/784) := by
  obtain ⟨h1, h2, h3, h4⟩ := e2aPi_values π p0 p1 procHalf
  have hq : (procHalf ()).w true = 1/2 := by simp [procHalf, procBool]
  rw [hq] at h1 h2 h3 h4
  have e1 : nu procHalf (e2aPi π p0 p1) (evM true) = 1/2 := by rw [h1]; ring
  have e2 : nu procHalf (e2aPi π p0 p1) (evM false) = 1/2 := by rw [h2]; ring
  have k : ∀ x : ℚ, x / (1/2) = 2 * x := fun x => by ring
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [e1, e2, h3, h4, k, k]; ring
  · rw [e1, e2, h3, h4, k, k]
    constructor <;> intro h <;> linarith

/-- **T17 at `δ_smoke`**: for `π < 1`, `V(smoke) = −1000(107π + 891)/(π + 1)`,
`V(refrain) = −108 000` and `V(smoke) − V(refrain) = 1000(π − 783)/(π + 1) < 0`: the
deterministic smoker's own act is priced below the unplayed act at every share, and the unplayed
act is priced by the reference class alone. (At `π = 1` the refrain event has mass `0`.)
Source: dp-sl-2-060 ("at `C = δ_smoke`: `1000(π − 783)/(π + 1) < 0` for `π < 1`"); mandate T17
Kind: P
Fidelity: exact
Hyps: `π < 1` (the refrain event needs positive mass) -/
theorem e2aPi_smoke (hπ : π < 1) :
    paySum procSmoke (e2aPi π p0 p1) (evM true) / nu procSmoke (e2aPi π p0 p1) (evM true) =
      -1000 * (107 * π + 891) / (π + 1) ∧
    paySum procSmoke (e2aPi π p0 p1) (evM false) / nu procSmoke (e2aPi π p0 p1) (evM false) =
      -108000 ∧
    paySum procSmoke (e2aPi π p0 p1) (evM true) / nu procSmoke (e2aPi π p0 p1) (evM true) -
        paySum procSmoke (e2aPi π p0 p1) (evM false) / nu procSmoke (e2aPi π p0 p1) (evM false) =
      1000 * (π - 783) / (π + 1) ∧
    paySum procSmoke (e2aPi π p0 p1) (evM true) / nu procSmoke (e2aPi π p0 p1) (evM true) <
      paySum procSmoke (e2aPi π p0 p1) (evM false) / nu procSmoke (e2aPi π p0 p1) (evM false) := by
  obtain ⟨h1, h2, h3, h4⟩ := e2aPi_values π p0 p1 procSmoke
  have hq : (procSmoke ()).w true = 1 := by simp [procSmoke]
  rw [hq] at h1 h2 h3 h4
  have e1 : nu procSmoke (e2aPi π p0 p1) (evM true) = (π + 1) / 2 := by rw [h1]; ring
  have e0 : nu procSmoke (e2aPi π p0 p1) (evM false) = (1 - π) / 2 := by rw [h2]; ring
  have f1 : paySum procSmoke (e2aPi π p0 p1) (evM true) = -500 * (107 * π + 891) := by
    rw [h3]; ring
  have f0 : paySum procSmoke (e2aPi π p0 p1) (evM false) = -54000 * (1 - π) := by rw [h4]; ring
  have d1 : π + 1 ≠ 0 := by intro h; linarith
  have d0 : 1 - π ≠ 0 := by intro h; linarith
  have v1 : paySum procSmoke (e2aPi π p0 p1) (evM true) / nu procSmoke (e2aPi π p0 p1) (evM true) =
      -1000 * (107 * π + 891) / (π + 1) := by
    rw [e1, f1]; field_simp; ring
  have v0 : paySum procSmoke (e2aPi π p0 p1) (evM false) /
      nu procSmoke (e2aPi π p0 p1) (evM false) = -108000 := by
    rw [e0, f0]; field_simp; ring
  have vd : paySum procSmoke (e2aPi π p0 p1) (evM true) / nu procSmoke (e2aPi π p0 p1) (evM true) -
      paySum procSmoke (e2aPi π p0 p1) (evM false) / nu procSmoke (e2aPi π p0 p1) (evM false) =
      1000 * (π - 783) / (π + 1) := by
    rw [v1, v0]; field_simp; ring
  refine ⟨v1, v0, vd, ?_⟩
  have hneg : 1000 * (π - 783) / (π + 1) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by linarith)
  rw [← vd] at hneg
  exact sub_neg.mp hneg

end e2aPi

/-! ## T19: the hidden-state action law -/

/-- The no-lesion event `{ℓ = 0}` (`tickleObs false`). Source: dp-sl-2-057. Kind: D -/
abbrev evL0 : Finset TickleW := tickleObs false

/-- `ν(m ∧ ℓ=0) = (1 − ρ) · C(d)(m)` and `ν(ℓ=0) = 1 − ρ` on `slOne`.
Source: none: infrastructure. Kind: L -/
theorem slOne_nu_l0 (L : Lesion) (α β : ℚ) (C : Proc Unit (fun _ => Bool) ℚ) (m : Bool) :
    nu C (slOne L α β) (evM m ∩ evL0) = (1 - L.ρ) * (C ()).w m ∧
    nu C (slOne L α β) evL0 = 1 - L.ρ := by
  have hw := w_false_eq_one_sub C
  constructor
  · rw [slOne_nu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, Finset.mem_inter, mem_evM, evL0,
      mem_tickleObs]
    cases m <;> simp <;> ring
  · rw [slOne_nu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, evL0, mem_tickleObs]
    simp; rw [hw]; ring

/-- **Everitt–Leike–Hutter's hidden-state action law under Definition 6 at a single point**: on
`slOne`, for **every** procedure (so for every self-model `C[d ↦ m]`), the act law is flat in
the lesion — `ν(m ∧ ℓ=1) · ν(ℓ=0) = ν(m ∧ ℓ=0) · ν(ℓ=1)` — the draw at one point cannot read
the hidden state.
Source: dp-sl-2-057 ("under Definition 6 at a single point, `ν_{C[d↦m]}(m=a ∣ ℓ=1) · … =
ν(m=a ∣ ℓ=0) · …` (flat in `ℓ`) for every self-model, on `slOne`"); mandate T19
Kind: P
Fidelity: exact (cross-multiplied)
Hyps: none -/
theorem slOne_action_law_flat (L : Lesion) (α β : ℚ) (C : Proc Unit (fun _ => Bool) ℚ) (m : Bool) :
    nu C (slOne L α β) (evM m ∩ evL) * nu C (slOne L α β) evL0 =
      nu C (slOne L α β) (evM m ∩ evL0) * nu C (slOne L α β) evL := by
  rw [Finset.inter_comm, slOne_nu_l_m, (slOne_nu_l0 L α β C m).1, (slOne_nu_l0 L α β C m).2,
    slOne_nu_l]
  ring

/-- **The `ℓ`-dependent action law is realizable across two points**: on the tickle tree the act
law given the lesion is `q_ℓ`, so it depends on `ℓ` iff `q₁ ≠ q₀` (with `ρ ∈ (0,1)`):
`ν(m=1 ∧ ℓ=1) · ν(ℓ=0) = ν(m=1 ∧ ℓ=0) · ν(ℓ=1) ↔ q₁ = q₀`.
Source: dp-sl-2-057 ("the `s`-dependent law is realizable only across two points"); mandate T19
Kind: N+
Fidelity: exact -/
theorem tickle_action_law_depends (ρ : ℚ) (r0 : 0 ≤ ρ) (r1 : ρ ≤ 1) (γ₁ : ℚ) (g10 : 0 ≤ γ₁)
    (g11 : γ₁ ≤ 1) (γ₀ : ℚ) (g00 : 0 ≤ γ₀) (g01 : γ₀ ≤ 1) (α β : ℚ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (q₁ : ℚ) (a0 : 0 ≤ q₁) (a1 : q₁ ≤ 1) (q₀ : ℚ) (b0 : 0 ≤ q₀) (b1 : q₀ ≤ 1) :
    nu (procTickle q₁ a0 a1 q₀ b0 b1) (tickle ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β)
          (evM true ∩ tickleObs true) *
        nu (procTickle q₁ a0 a1 q₀ b0 b1) (tickle ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β)
          (tickleObs false) =
      nu (procTickle q₁ a0 a1 q₀ b0 b1) (tickle ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β)
          (evM true ∩ tickleObs false) *
        nu (procTickle q₁ a0 a1 q₀ b0 b1) (tickle ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β)
          (tickleObs true) ↔ q₁ = q₀ := by
  obtain ⟨h1, h2, -, -⟩ := tickle_point_masses ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β
    (procTickle q₁ a0 a1 q₀ b0 b1) true
  obtain ⟨h1', h2', -, -⟩ := tickle_point_masses ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β
    (procTickle q₁ a0 a1 q₀ b0 b1) false
  rw [h2 true, h1', h2' true, h1]
  simp only [lesionRate, procTickle, if_true, Bool.false_eq_true, if_false, FinDistr.bool_true]
  have hρ : 0 < ρ * (1 - ρ) := mul_pos hρ0 (sub_pos.mpr hρ1)
  constructor
  · intro h
    have : ρ * (1 - ρ) * (q₁ - q₀) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hρ.ne'
    · linarith
  · intro h; rw [h]; ring

end Cleanroom.Decision.DpSmokingLesion
