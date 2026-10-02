import Cleanroom.Found.DpCoreTree.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Preimage

/-!
# The extensional shadow is neither injective nor surjective

T10 of [[dp-core-tree-mandate]] (dp-core-006). `shadow C B` is the joint law of `(λ, r)` under
`μ_{B,C}`, as a mass function on `Ω × K`.

* **Not injective** (`shadow_insertQuery`): inserting a query of `d` whose branches all lead to
  the same subtree leaves the shadow unchanged while `#_d` rises by one on every leaf and
  `occ(d)` becomes everything — so occurrence-conditioned notions are not functions of the
  shadow.
* **Finite dependence** (`not_shadow_of_infinite_family`): with an injective family of points
  `e : ℕ ↪ ι` and a designated action `t d` at every point, the functional "`δ_{(ω,1)}` if `C`
  plays `t` at every `e i`, else `δ_{(ω,0)}`" is the shadow of no tree, because a tree queries
  finitely many points (`queried B`) and its law is a function of `C` there only
  (`leafLaw_congr_queried`). This is v2's "payoff `1` iff `C` two-boxes at every point of an
  infinite family". It is a finite-dependence statement, not Remark 3.1's continuity /
  dialogue-tree claim.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq Ω]

namespace Tree

/-- The extensional shadow `B̂(C)`: the joint law of `(λ, r)` under `μ_{B,C}`, as a mass function.
Source: [[decision-problems-v2]] §3.1 "The extensional shadow" (`B̂(C)`)
Kind: D -/
def shadow (C : Proc ι acts K) (B : Tree Ω ι acts K) : Ω × K → K :=
  fun x => ∑ ℓ, if world B ℓ = x.1 ∧ payoff B ℓ = x.2 then leafLaw C B ℓ else 0

/-- Insert a query of `d` above `B` whose every branch leads to `B`.
Source: [[decision-problems-v2]] §3.1 ("Inserting a query of `d` whose branches lead to
identical subtrees")
Kind: D -/
def insertQuery (d : ι) (B : Tree Ω ι acts K) : Tree Ω ι acts K :=
  decision d fun _ => B

/-- **Non-injectivity**: inserting a query of `d` does not change the shadow.
Source: [[decision-problems-v2]] §3.1 ("leaves `B̂` unchanged")
Kind: P
Fidelity: exact
Hyps: none -/
theorem shadow_insertQuery (C : Proc ι acts K) (d : ι) (B : Tree Ω ι acts K) :
    shadow C (insertQuery d B) = shadow C B := by
  funext x
  unfold shadow insertQuery
  rw [sum_leaves_decision]
  simp only [world_decision, payoff_decision, leafLaw_decision]
  have : ∀ a, (∑ ℓ, if world B ℓ = x.1 ∧ payoff B ℓ = x.2 then (C d).w a * leafLaw C B ℓ else 0)
      = (C d).w a * ∑ ℓ, if world B ℓ = x.1 ∧ payoff B ℓ = x.2 then leafLaw C B ℓ else 0 := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by split_ifs <;> simp
  simp only [this, ← Finset.sum_mul, (C d).sum_one, one_mul]

/-- …while `#_d` rises by one on every leaf.
Source: [[decision-problems-v2]] §3.1 ("while changing `occ(d)` and `#_d`")
Kind: L -/
theorem count_insertQuery [DecidableEq ι] (d : ι) (B : Tree Ω ι acts K) (a : acts d)
    (ℓ : B.Leaves) : count d (insertQuery d B) ⟨a, ℓ⟩ = 1 + count d B ℓ := by
  simp [insertQuery]

/-- …and `occ(d)` becomes every leaf.
Source: [[decision-problems-v2]] §3.1
Kind: L -/
theorem occ_insertQuery [DecidableEq ι] (d : ι) (B : Tree Ω ι acts K) :
    occ d (insertQuery d B) = Finset.univ := by
  ext ⟨a, ℓ⟩
  simp [count_insertQuery]

open Classical in
/-- The infinite-family functional: `δ_{(ω,1)}` if `C` plays the designated action `t` at every
point of the family `e`, else `δ_{(ω,0)}`.
Source: [[decision-problems-v2]] §3.1 ("payoff `1` iff `C` two-boxes at every point of an
infinite family")
Kind: D -/
noncomputable def infiniteFamilyFunctional [DecidableEq K] (e : ℕ → ι) (t : (d : ι) → acts d)
    (ω : Ω) (C : Proc ι acts K) : Ω × K → K :=
  fun x =>
    if (∀ i, C (e i) = FinDistr.pure (t (e i))) then (if x = (ω, 1) then 1 else 0)
    else (if x = (ω, 0) then 1 else 0)

/-- Point masses are injective.
Source: none: infrastructure
Kind: L -/
theorem FinDistr.pure_injective {α : Type} [Fintype α] [DecidableEq α] {a b : α}
    (h : (FinDistr.pure a : FinDistr K α) = FinDistr.pure b) : a = b := by
  have := congrArg (fun p : FinDistr K α => p.w a) h
  simp only [FinDistr.pure_w, if_true] at this
  by_contra hab
  simp [hab] at this

/-- **Finite dependence**: with `e` injective and every point of the family having at least two
actions, the infinite-family functional is the shadow of no tree.
Source: [[decision-problems-v2]] §3.1 ("some extensional functionals are realized by no tree");
mandate T10(ii) (finite dependence, not Remark 3.1's continuity claim)
Kind: P
Fidelity: exact (the family is any injective `ℕ → ι`; "two-boxes" is a designated action `t`)
Hyps: none -/
theorem not_shadow_of_infinite_family [DecidableEq ι] [DecidableEq K] [∀ d, Nonempty (acts d)]
    (e : ℕ → ι) (he : Function.Injective e) (t : (d : ι) → acts d)
    (h2 : ∀ i, 2 ≤ Fintype.card (acts (e i))) (ω : Ω) (B : Tree Ω ι acts K) :
    ¬ ∀ C : Proc ι acts K, shadow C B = infiniteFamilyFunctional e t ω C := by
  intro hshadow
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset ((queried B).preimage e he.injOn)
  rw [Finset.mem_preimage] at hj
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by have := h2 j; omega) (t (e j))
  set C₁ : Proc ι acts K := Proc.ofFun t with hC₁
  set C₂ : Proc ι acts K := C₁.deviatePure (e j) b with hC₂
  have hagree : ∀ d ∈ queried B, C₁ d = C₂ d := by
    intro d hd
    have hne : d ≠ e j := fun h => hj (h ▸ hd)
    simp [hC₂, Proc.deviatePure, Proc.deviate_ne _ _ hne]
  have h1 : infiniteFamilyFunctional e t ω C₁ (ω, 1) = 1 := by
    simp only [infiniteFamilyFunctional]
    rw [if_pos]
    · simp
    · intro i; rfl
  have h2' : infiniteFamilyFunctional e t ω C₂ (ω, 1) = 0 := by
    simp only [infiniteFamilyFunctional]
    rw [if_neg]
    · simp
    · intro hall
      have := hall j
      simp only [hC₂, Proc.deviatePure, Proc.deviate_same] at this
      exact hb (FinDistr.pure_injective this)
  have hs : shadow C₁ B = shadow C₂ B := by
    funext x
    unfold shadow
    exact Finset.sum_congr rfl fun ℓ _ => by rw [leafLaw_congr_queried B hagree ℓ]
  have := congrFun (hshadow C₁) (ω, 1)
  rw [hs, hshadow C₂, h2'] at this
  rw [h1] at this
  exact one_ne_zero this.symm

end Tree

end Cleanroom.Found.DpCoreTree
