import Cleanroom.Corrigibility.CorrLandscape.BasinToy

/-!
# `corr-landscape` — `TwoRound`: the contraction as a `SupermartStep` on a two-round process (E2(i))

The lift of `BasinToy.phi_step` to `corr-trajectory`'s Layer F on the smallest process where the
conditional structure is real: two rounds of D9′ driven by the product law `prod2 ν ν` on `A × A`
(`corr-trajectory`'s `prod2`), with the filtration `atoms2` (everything at time `0`, the first letter at
time `1`, singletons after). `Φ_0 = d_0 − ρ†`, `Φ_1 = (d_1 − ρ†)/(1−η)`, `Φ_t = (d_2 − ρ†)/(1−η)²` for
`t ≥ 2` (frozen after the second round).

`phi_isSupermart`: **`Φ` is a Layer-F supermartingale** (`IsSupermart`: adapted, and the step
inequality at every `t`) whenever `d_0 < r`, the alphabet's disturbances are bounded and
`η ξ̄ + σ̄* ≤ η r` with `0 < η < 1` — the one-step contraction, conditioned on the first letter through the
product law's factorization (`condSum_atoms2_one`). It is **not** a potential: `Φ` is negative wherever
`d_t < ρ†` (`BasinToy.phi_neg_below_rho`), and the clamp does not repair it (`max_repair_fails`). The
general horizon-`T` lift over `prodLaw`/`prefixAtoms` is not proved (finding F-21); this file is its
two-round instance.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace TwoRound

open BasinToy

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The two-round filtration on `A × A`: everything at `0`, the first letter at `1`, singletons after.
Source: mandate T6(e) (E2(i)); the shape of `corr-trajectory`'s `Margin.preAtoms`
Kind: D
Fidelity: exact -/
def atoms2 : Atoms (A × A) where
  fib t ω := if t = 0 then univ else if t = 1 then univ.filter (fun ω' => ω'.1 = ω.1) else {ω}
  mem_fib t ω := by rcases t with _ | _ | t <;> simp
  fib_eq_of_mem t ω ω' h := by
    rcases t with _ | _ | t
    · rfl
    · simp only [zero_add, one_ne_zero, if_false, if_true, mem_filter, mem_univ, true_and] at h
      simp [h]
    · simp only [Nat.succ_ne_zero, if_false, mem_singleton, Nat.reduceEqDiff] at h
      rw [h]
  fib_succ_subset t ω := by
    rcases t with _ | _ | t
    · intro ω' _; simp
    · intro ω' h
      simp only [Nat.reduceAdd, OfNat.ofNat_ne_zero, if_false, OfNat.ofNat_ne_one, mem_singleton] at h
      simp [h]
    · intro ω' h
      simpa using h

/-- The state after the first round, driven by the first letter.
Source: mandate T6(e). Kind: D. Fidelity: exact -/
noncomputable def st1 (η r : ℝ) (s₀ : ℝ × ℝ) (ξv Δv : A → ℝ) (ω : A × A) : ℝ × ℝ :=
  step η r s₀ (ξv ω.1) (Δv ω.1)

/-- The state after the second round. Source: mandate T6(e). Kind: D. Fidelity: exact -/
noncomputable def st2 (η r : ℝ) (s₀ : ℝ × ℝ) (ξv Δv : A → ℝ) (ω : A × A) : ℝ × ℝ :=
  step η r (st1 η r s₀ ξv Δv ω) (ξv ω.2) (Δv ω.2)

/-- **`Φ_t = (1−η)^{−t}(d_t − ρ†)`** on the two-round process, frozen after round `2`.
Source: mandate T6(e) (E2(i))
Kind: D
Fidelity: exact (two rounds) -/
noncomputable def Phi (η r : ℝ) (s₀ : ℝ × ℝ) (ξv Δv : A → ℝ) (ρ : ℝ) : ℕ → A × A → ℝ
  | 0 => fun _ => (BasinToy.dist s₀ - ρ) / (1 - η) ^ 0
  | 1 => fun ω => (BasinToy.dist (st1 η r s₀ ξv Δv ω) - ρ) / (1 - η) ^ 1
  | _ + 2 => fun ω => (BasinToy.dist (st2 η r s₀ ξv Δv ω) - ρ) / (1 - η) ^ 2

/-- The sum over the time-`1` atom of `ω` is the sum over the second letter.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_fiber_fst (f : A × A → ℝ) (a : A) :
    ∑ ω' ∈ univ.filter (fun ω' : A × A => ω'.1 = a), f ω' = ∑ b, f (a, b) := by
  rw [sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (mem_univ a) h

/-- **The product law's factorization on the time-`1` atom**: `condSum (prod2 ν ν) atoms2 1 X ω =
ν(ω.1) · E_ν[X(ω.1, ·)]`.
Source: none: infrastructure (the two-round case of the prefix-atom factorization)
Kind: L
Fidelity: n/a -/
lemma condSum_atoms2_one (ν : Distr A) (X : A × A → ℝ) (ω : A × A) :
    condSum (prod2 ν ν) atoms2 1 X ω = ν.mass ω.1 * expect ν (fun b => X (ω.1, b)) := by
  unfold condSum expect
  simp only [atoms2, one_ne_zero, if_false, if_true]
  rw [sum_fiber_fst (fun ω' => (prod2 ν ν).mass ω' * X ω') ω.1, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  simp only [prod2_mass]; ring

/-- The time-`0` conditional sum is the expectation.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condSum_atoms2_zero (μ : Distr (A × A)) (X : A × A → ℝ) (ω : A × A) :
    condSum μ atoms2 0 X ω = expect μ X := by
  simp [condSum, expect, atoms2]

/-- **`Φ` is a Layer-F supermartingale on the two-round process**: adapted to `atoms2` and satisfying the
step inequality at every `t`, under `0 < η < 1`, `d_0 < r`, bounded disturbances on the alphabet and
`η ξ̄ + σ̄* ≤ η r` (so the second round starts inside too).
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(b); mandate T6(e) (E2(i))
Kind: C (`BasinToy.phi_step` at `t = 0, 1` through `condSum_atoms2_one`; `step_dist_lt` for the inside)
Fidelity: exact (two rounds; the general horizon is F-21)
Hyps: (a) only -/
theorem phi_isSupermart (η r ξbar σbar : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (ν : Distr A) (ξv Δv : A → ℝ)
    (hξ : ∀ a, |ξv a| ≤ ξbar) (hΔ : ∀ a, |Δv a| ≤ σbar) (hcond : η * ξbar + σbar ≤ η * r) (s₀ : ℝ × ℝ)
    (hs : BasinToy.dist s₀ < r) :
    IsSupermart (prod2 ν ν) atoms2 (Phi η r s₀ ξv Δv (rhoDagger η ν ξv Δv)) := by
  have hin1 : ∀ ω : A × A, BasinToy.dist (st1 η r s₀ ξv Δv ω) < r := fun ω =>
    step_dist_lt η r ξbar σbar hη0 hη1 s₀ _ _ (hξ _) (hΔ _) hcond hs
  constructor
  · -- adapted
    intro t
    rcases t with _ | _ | t
    · intro ω ω' _; rfl
    · intro ω ω' h
      simp only [atoms2, zero_add, one_ne_zero, if_false, if_true, mem_filter, mem_univ, true_and] at h
      simp [Phi, st1, h]
    · intro ω ω' h
      simp only [atoms2, Nat.succ_ne_zero, if_false, mem_singleton, Nat.reduceEqDiff] at h
      rw [h]
  · -- the step inequality
    intro t
    rcases t with _ | _ | t
    · intro ω
      rw [condSum_atoms2_zero, condSum_atoms2_zero]
      have h := phi_step η r hη0 hη1 ν ξv Δv s₀ hs 0
      simp only [Phi, st1]
      rw [expect_prod2_fst ν ν (fun a => (BasinToy.dist (step η r s₀ (ξv a) (Δv a)) - rhoDagger η ν ξv Δv) / (1 - η) ^ 1)]
      rw [Cleanroom.Found.CorrThreeStep.expect_const]
      simpa using h
    · intro ω
      rw [condSum_atoms2_one, condSum_atoms2_one]
      have h := phi_step η r hη0 hη1 ν ξv Δv (st1 η r s₀ ξv Δv ω) (hin1 ω) 1
      have e : expect ν (fun b => Phi η r s₀ ξv Δv (rhoDagger η ν ξv Δv) (0 + 1) (ω.1, b)) =
          Phi η r s₀ ξv Δv (rhoDagger η ν ξv Δv) 1 ω := by
        simp only [zero_add, Phi, st1]
        rw [Cleanroom.Found.CorrThreeStep.expect_const]
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (ν.nonneg _)
      simpa [Phi, st2, st1] using h
    · intro ω
      exact le_of_eq rfl

/-- **Not a potential**: `Φ_0 < 0` whenever `d_0 < ρ†` (and likewise at every `t`), so `IsPotential`
fails for `Φ`; the supermartingale property above is the whole of what the contraction certifies.
Source: mandate T6(e) ("say exactly where nonnegativity fails")
Kind: L
Fidelity: exact -/
theorem phi_not_nonneg (η r : ℝ) (hη1 : η < 1) (s₀ : ℝ × ℝ) (ξv Δv : A → ℝ) (ρ : ℝ) (hd : BasinToy.dist s₀ < ρ)
    (ω : A × A) : Phi η r s₀ ξv Δv ρ 0 ω < 0 :=
  phi_neg_below_rho η ρ (BasinToy.dist s₀) hη1 0 hd

end TwoRound

end Cleanroom.Corrigibility.CorrLandscape
