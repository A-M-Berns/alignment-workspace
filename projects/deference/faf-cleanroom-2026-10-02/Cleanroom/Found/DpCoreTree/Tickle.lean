import Cleanroom.Found.DpCoreTree.Catalogue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Corollary 12′: the tickle tree's leaf masses and the identity

T12 of [[dp-core-tree-mandate]] (dp-sl-013). The tickle tree (Catalogue `tickle`): chance
`ℓ ∼ (ρ, 1−ρ)`; at `ℓ = 1` query `d₁`, at `ℓ = 0` query `d₀`; `q_i := C(d_i)(m = 1)`; then
`k ∼ (γ_ℓ, 1−γ_ℓ)`; leaves `(ℓ, m, k)`. The eight masses are proved **from `leafLaw`** (the SL
run's Lean took them as `def`s; closing that gap is the point), then the identity
`ν(k ∩ m=1) · ν(m=0) − ν(k ∩ m=0) · ν(m=1) = (γ₁ − γ₀)(q₁ − q₀) ρ (1 − ρ)` (the cross-multiplied
form of `ν(k ∣ m=1) − ν(k ∣ m=0) = (γ₁−γ₀)(q₁−q₀)ρ(1−ρ) / (ν(m=1) ν(m=0))`), the division form
under explicit nonzero denominators, and `q₁ = q₀ ⇒ 0`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset Catalogue Tree

/-- The mixed action `(q, 1 − q)` on `Bool` (`true ↦ q`).
Source: none: infrastructure
Kind: D -/
def FinDistr.bool (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinDistr ℚ Bool where
  w b := if b then q else 1 - q
  nonneg b := by cases b <;> simp <;> linarith
  sum_one := by simp [Fintype.sum_bool]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.bool_true (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (FinDistr.bool q h0 h1).w true = q := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.bool_false (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (FinDistr.bool q h0 h1).w false = 1 - q := rfl

/-- `decide ((0 : Fin 2) = 0) = true`. Source: none: infrastructure. Kind: L -/
@[simp] theorem decide_fin2_zero : decide ((0 : Fin 2) = 0) = true := rfl

/-- `decide ((1 : Fin 2) = 0) = false`. Source: none: infrastructure. Kind: L -/
@[simp] theorem decide_fin2_one : decide ((1 : Fin 2) = 0) = false := rfl

/-- The two-point tickle procedure: `C(d₁)(m=1) = q₁`, `C(d₀)(m=1) = q₀`.
Source: [[decision-problems-v2]] §7.3 Proposition 12 ("when `C` smokes more at the lesioned
state")
Kind: D -/
def procTickle (q₁ : ℚ) (a0 : 0 ≤ q₁) (a1 : q₁ ≤ 1) (q₀ : ℚ) (b0 : 0 ≤ q₀) (b1 : q₀ ≤ 1) :
    Proc Bool (fun _ => Bool) ℚ :=
  fun ℓ => if ℓ then FinDistr.bool q₁ a0 a1 else FinDistr.bool q₀ b0 b1

section masses

variable (ρ : ℚ) (r0 : 0 ≤ ρ) (r1 : ρ ≤ 1) (γ₁ : ℚ) (g10 : 0 ≤ γ₁) (g11 : γ₁ ≤ 1)
  (γ₀ : ℚ) (g00 : 0 ≤ γ₀) (g01 : γ₀ ≤ 1) (α β : ℚ)
  (q₁ : ℚ) (a0 : 0 ≤ q₁) (a1 : q₁ ≤ 1) (q₀ : ℚ) (b0 : 0 ≤ q₀) (b1 : q₀ ≤ 1)

local notation "T" => tickle ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β
local notation "Cq" => procTickle q₁ a0 a1 q₀ b0 b1

/-- The leaf of the tickle tree with lesion index `i`, act `m`, cancer index `j`.
Source: none: infrastructure
Kind: D -/
def tickleLeaf (i : Fin 2) (m : Bool) (j : Fin 2) : (T).Leaves := ⟨i, ⟨m, ⟨j, ()⟩⟩⟩

/-- **The eight leaf masses from `leafLaw`**: `μ(ℓ, m, k) = P(ℓ) · C(d_ℓ)(m) · P(k ∣ ℓ)`.
Source: `sl-workflow` Corollary 12′ (dp-sl-013: "the eight masses `μ(1,1,1) = ρ q₁ γ₁`, …")
Kind: P
Fidelity: exact -/
theorem tickle_leafLaw (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β i m j) =
      (if i = 0 then ρ else 1 - ρ) *
        (if i = 0 then (if m then q₁ else 1 - q₁) else (if m then q₀ else 1 - q₀)) *
        (if i = 0 then (if j = 0 then γ₁ else 1 - γ₁) else (if j = 0 then γ₀ else 1 - γ₀)) := by
  unfold tickleLeaf tickle
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.coin, tickleGamma]
  fin_cases i <;> fin_cases j <;> cases m <;> simp [procTickle] <;> ring

/-- `μ(1,1,1) = ρ q₁ γ₁`. Source: dp-sl-013. Kind: N+ -/
theorem tickle_mass_111 :
    leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β 0 true 0) = ρ * q₁ * γ₁ := by
  rw [tickle_leafLaw]; simp

/-- `μ(1,1,0) = ρ q₁ (1−γ₁)`. Source: dp-sl-013. Kind: N+ -/
theorem tickle_mass_110 :
    leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β 0 true 1) =
      ρ * q₁ * (1 - γ₁) := by
  rw [tickle_leafLaw]; simp

/-- `μ(1,0,1) = ρ (1−q₁) γ₁`. Source: dp-sl-013. Kind: N+ -/
theorem tickle_mass_101 :
    leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β 0 false 0) =
      ρ * (1 - q₁) * γ₁ := by
  rw [tickle_leafLaw]; simp

/-- `μ(1,0,0) = ρ (1−q₁)(1−γ₁)`. Source: dp-sl-013. Kind: N+ -/
theorem tickle_mass_100 :
    leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β 0 false 1) =
      ρ * (1 - q₁) * (1 - γ₁) := by
  rw [tickle_leafLaw]; simp

/-- `μ(0,1,1) = (1−ρ) q₀ γ₀`. Source: dp-sl-013. Kind: N+ -/
theorem tickle_mass_011 :
    leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β 1 true 0) =
      (1 - ρ) * q₀ * γ₀ := by
  rw [tickle_leafLaw]; simp

/-- `μ(0,1,0) = (1−ρ) q₀ (1−γ₀)`. Source: dp-sl-013. Kind: N+ -/
theorem tickle_mass_010 :
    leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β 1 true 1) =
      (1 - ρ) * q₀ * (1 - γ₀) := by
  rw [tickle_leafLaw]; simp

/-- `μ(0,0,1) = (1−ρ)(1−q₀) γ₀`. Source: dp-sl-013. Kind: N+ -/
theorem tickle_mass_001 :
    leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β 1 false 0) =
      (1 - ρ) * (1 - q₀) * γ₀ := by
  rw [tickle_leafLaw]; simp

/-- `μ(0,0,0) = (1−ρ)(1−q₀)(1−γ₀)`. Source: dp-sl-013. Kind: N+ -/
theorem tickle_mass_000 :
    leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β 1 false 1) =
      (1 - ρ) * (1 - q₀) * (1 - γ₀) := by
  rw [tickle_leafLaw]; simp

/-- `ν` on the tickle tree as an explicit eight-term sum over `(ℓ, m, k)`.
Source: none: infrastructure
Kind: L -/
theorem tickle_nu (X : Finset TickleW) :
    nu Cq T X =
      ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
        if (decide (i = 0), m, decide (j = 0)) ∈ X then
          leafLaw Cq T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β i m j) else 0 := by
  rw [nu_eq_sum]
  unfold tickle
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Tree.sum_leaves_leaf]
  rfl

/-- The event `{m = 1}`. Source: [[decision-problems-v2]] §7.3. Kind: D -/
def evM (m : Bool) : Finset TickleW := Finset.univ.filter fun w => w.2.1 = m

/-- The event `{k = 1}`. Source: [[decision-problems-v2]] §7.3. Kind: D -/
def evK : Finset TickleW := Finset.univ.filter fun w => w.2.2 = true

/-- `ν(m = 1) = ρ q₁ + (1−ρ) q₀`. Source: dp-sl-013. Kind: L -/
theorem tickle_nu_m1 : nu Cq T (evM true) = ρ * q₁ + (1 - ρ) * q₀ := by
  rw [tickle_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, tickle_leafLaw, evM, Finset.mem_filter,
    Finset.mem_univ, true_and]
  simp <;> ring

/-- `ν(m = 0) = ρ (1−q₁) + (1−ρ)(1−q₀)`. Source: dp-sl-013. Kind: L -/
theorem tickle_nu_m0 : nu Cq T (evM false) = ρ * (1 - q₁) + (1 - ρ) * (1 - q₀) := by
  rw [tickle_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, tickle_leafLaw, evM, Finset.mem_filter,
    Finset.mem_univ, true_and]
  simp <;> ring

/-- `ν(k ∩ m = 1) = ρ q₁ γ₁ + (1−ρ) q₀ γ₀`. Source: dp-sl-013. Kind: L -/
theorem tickle_nu_k_m1 : nu Cq T (evK ∩ evM true) = ρ * q₁ * γ₁ + (1 - ρ) * q₀ * γ₀ := by
  rw [tickle_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, tickle_leafLaw, evM, evK, Finset.mem_inter,
    Finset.mem_filter, Finset.mem_univ, true_and]
  simp <;> ring

/-- `ν(k ∩ m = 0) = ρ (1−q₁) γ₁ + (1−ρ)(1−q₀) γ₀`. Source: dp-sl-013. Kind: L -/
theorem tickle_nu_k_m0 :
    nu Cq T (evK ∩ evM false) = ρ * (1 - q₁) * γ₁ + (1 - ρ) * (1 - q₀) * γ₀ := by
  rw [tickle_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, tickle_leafLaw, evM, evK, Finset.mem_inter,
    Finset.mem_filter, Finset.mem_univ, true_and]
  simp <;> ring

/-- **Corollary 12′, cross-multiplied**:
`ν(k ∩ m=1) · ν(m=0) − ν(k ∩ m=0) · ν(m=1) = (γ₁ − γ₀)(q₁ − q₀) ρ (1 − ρ)`.
Source: `sl-workflow` Corollary 12′ (dp-sl-013); [[decision-problems-v2]] Proposition 12
("the population-level correlation `ν(k ∣ m=1) > ν(k ∣ m=0)` can hold when `C` smokes more at
the lesioned state")
Kind: P
Fidelity: exact (cross-multiplied; the division form is `tickle_identity_div`)
Hyps: none -/
theorem tickle_identity :
    nu Cq T (evK ∩ evM true) * nu Cq T (evM false) -
        nu Cq T (evK ∩ evM false) * nu Cq T (evM true) =
      (γ₁ - γ₀) * (q₁ - q₀) * ρ * (1 - ρ) := by
  rw [tickle_nu_k_m1, tickle_nu_m0, tickle_nu_k_m0, tickle_nu_m1]
  ring

/-- **Corollary 12′, division form** with explicit nonzero denominators:
`ν(k ∣ m=1) − ν(k ∣ m=0) = (γ₁−γ₀)(q₁−q₀)ρ(1−ρ) / (ν(m=1) ν(m=0))`.
Source: dp-sl-013
Kind: C -/
theorem tickle_identity_div (h1 : nu Cq T (evM true) ≠ 0) (h0 : nu Cq T (evM false) ≠ 0) :
    nu Cq T (evK ∩ evM true) / nu Cq T (evM true) -
        nu Cq T (evK ∩ evM false) / nu Cq T (evM false) =
      (γ₁ - γ₀) * (q₁ - q₀) * ρ * (1 - ρ) / (nu Cq T (evM true) * nu Cq T (evM false)) := by
  rw [← tickle_identity ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β q₁ a0 a1 q₀ b0 b1]
  field_simp <;> ring

/-- **At equal smoking rates the correlation vanishes**: `q₁ = q₀ ⇒` the difference is `0`.
Source: dp-sl-013 ("`q₁ = q₀ ⇒ 0`")
Kind: C -/
theorem tickle_identity_of_eq (h : q₁ = q₀) :
    nu Cq T (evK ∩ evM true) * nu Cq T (evM false) -
        nu Cq T (evK ∩ evM false) * nu Cq T (evM true) = 0 := by
  rw [tickle_identity, h]; ring

/-- A `norm_num` instance: `ρ = ½`, `γ₁ = ¾`, `γ₀ = ¼`, `q₁ = 1`, `q₀ = 0`: the difference is
`(½)(1)(½)(½) = ⅛`.
Source: dp-sl-013 (a numerical instance)
Kind: N+ -/
theorem tickle_instance :
    nu (procTickle 1 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num))
        (tickle (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num)
          (1/4) (by norm_num) (by norm_num) 1 1) (evK ∩ evM true) *
      nu (procTickle 1 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num))
        (tickle (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num)
          (1/4) (by norm_num) (by norm_num) 1 1) (evM false) -
      nu (procTickle 1 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num))
        (tickle (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num)
          (1/4) (by norm_num) (by norm_num) 1 1) (evK ∩ evM false) *
      nu (procTickle 1 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num))
        (tickle (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num)
          (1/4) (by norm_num) (by norm_num) 1 1) (evM true) = 1/8 := by
  rw [tickle_identity]; norm_num

end masses

end Cleanroom.Found.DpCoreTree
