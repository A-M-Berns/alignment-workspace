import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Phase IV-E formal mechanism

Small load-bearing lemmas only.  The surrounding English theorems state
precisely which mathematical and interface hypotheses instantiate them.
-/

namespace PhaseIVE

section Leverage

theorem leverage_slack
    (pA pAR pARB pB cP cA cS : ℝ) :
    pB - cP * cA * cS =
      (pB - pARB) + (pARB - cS * pAR) +
      cS * (pAR - cA * pA) + cS * cA * (pA - cP) := by
  ring

theorem leverage_bound
    {pA pAR pARB pB cP cA cS : ℝ}
    (hP : cP ≤ pA)
    (hA : cA * pA ≤ pAR)
    (hS : cS * pAR ≤ pARB)
    (hB : pARB ≤ pB)
    (hcA : 0 ≤ cA) (hcS : 0 ≤ cS) :
    cP * cA * cS ≤ pB := by
  nlinarith [mul_nonneg hcS (sub_nonneg.mpr hA),
    mul_nonneg (mul_nonneg hcS hcA) (sub_nonneg.mpr hP)]

end Leverage

section ConvexCertificates

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem certificateHalfspace_convex (f : E →ₗ[ℝ] ℝ) (b : ℝ) :
    Convex ℝ {x : E | b ≤ f x} :=
  convex_halfSpace_ge f.isLinear b

theorem certificateRegion_convex
    {ι : Type*} (f : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    Convex ℝ (⋂ i, {x : E | b i ≤ f i x}) := by
  apply convex_iInter
  intro i
  exact certificateHalfspace_convex (f i) (b i)

end ConvexCertificates

section OperativeForce

theorem anchored_comparison
    {theta g e eps : ℝ}
    (hvi : theta * g + (1 - theta) * e ≤ eps) :
    theta * g ≤ eps - (1 - theta) * e := by
  linarith

theorem fixedCore_wealth
    {G tolerance kappa s R M : ℝ}
    (hk : 0 ≤ kappa)
    (hstep : G ≤ tolerance - kappa * s)
    (href : -R - M ≤ s) :
    G ≤ tolerance + kappa * (R + M) := by
  have hm : -kappa * s ≤ kappa * (R + M) := by
    nlinarith [mul_nonneg hk (sub_nonneg.mpr href)]
  linarith

end OperativeForce

section PositivePart

def posPart (x : ℝ) : ℝ := max 0 x

theorem posPart_add (x y : ℝ) :
    posPart (x + y) ≤ posPart x + posPart y := by
  unfold posPart
  apply max_le
  · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · exact add_le_add (le_max_right _ _) (le_max_right _ _)

theorem posPart_finset_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    posPart (∑ i ∈ s, f i) ≤ ∑ i ∈ s, posPart (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [posPart]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (posPart_add _ _) (add_le_add (le_refl _) ih)

theorem posPart_minimal {z liability : ℝ}
    (hc : 0 ≤ liability) (hloc : 0 ≤ z + liability) :
    posPart (-z) ≤ liability := by
  unfold posPart
  exact max_le hc (by linarith)

end PositivePart

section Targets

theorem target_remainder (lam : ℝ) : lam + (1 - lam) = 1 := by ring

theorem affine_target_remainder (r0 rStar lam : ℝ) :
    (((1 - lam) * r0 + lam * rStar) - r0) +
      (rStar - ((1 - lam) * r0 + lam * rStar)) = rStar - r0 := by
  ring

theorem not_complete_of_remainder_pos {lam : ℝ} (h : 0 < 1 - lam) : lam ≠ 1 := by
  linarith

end Targets

section Ratification

theorem successorRatification {X : Type*} (F : X → X) :
    ∃ endorse : X → Prop, ∀ x, endorse (F x) := by
  exact ⟨fun _ => True, fun _ => True.intro⟩

end Ratification

section VersionSpace

structure Signature where
  success : Finset Nat
  burden : Finset Nat
deriving DecidableEq

def Dominates (a b : Signature) : Prop :=
  b.success ⊆ a.success ∧
  a.burden ⊆ b.burden ∧
  b.success.card + a.burden.card < a.success.card + b.burden.card

theorem Dominates.irrefl (a : Signature) : ¬ Dominates a a := by
  intro h
  exact (lt_irrefl _ h.2.2)

theorem Dominates.trans {a b c : Signature}
    (hab : Dominates a b) (hbc : Dominates b c) : Dominates a c := by
  refine ⟨hbc.1.trans hab.1, hab.2.1.trans hbc.2.1, ?_⟩
  have hsum :
      (c.success.card + b.burden.card) +
          (b.success.card + a.burden.card) <
        (b.success.card + c.burden.card) +
          (a.success.card + b.burden.card) :=
    Nat.add_lt_add hbc.2.2 hab.2.2
  have hsum' :
      (b.success.card + b.burden.card) +
          (c.success.card + a.burden.card) <
        (b.success.card + b.burden.card) +
          (a.success.card + c.burden.card) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum
  exact Nat.lt_of_add_lt_add_left hsum'

theorem equalSignature_not_dominates {a b : Signature} (h : a = b) :
    ¬ Dominates a b := by
  subst b
  exact Dominates.irrefl a

theorem support_insert_existing (s : Finset Nat) {x : Nat} (hx : x ∈ s) :
    (insert x s).card = s.card := by
  simp [hx]

end VersionSpace

section HistoryAndComposition

theorem append_preserves_mem {τ : Type*} {x : τ} (h₁ h₂ : List τ)
    (hx : x ∈ h₁) : x ∈ h₁ ++ h₂ := by
  exact List.mem_append_left h₂ hx

theorem safe_run {X : Type*} (step : X → X) (Safe : X → Prop)
    (preserves : ∀ x, Safe x → Safe (step x))
    {x : X} (hx : Safe x) : ∀ n, Safe ((step^[n]) x) := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact preserves _ ih

end HistoryAndComposition

section NoTrader

theorem noTrader_twoWorld
    {μ G₁ G₂ R : ℝ}
    (hμ1 : μ < 1)
    (hzero : μ * G₁ + (1 - μ) * G₂ = 0)
    (hRisk : -R ≤ G₂) :
    μ * G₁ ≤ R * (1 - μ) := by
  nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hμ1)) (sub_nonneg.mpr hRisk)]

end NoTrader

end PhaseIVE
