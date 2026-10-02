import Cleanroom.Corrigibility.CorrLandscape.BasinToy

/-!
# `corr-landscape` — `Horizon`: the contraction's `SupermartStep` over the general horizon (E2(i), OPEN)

The general-horizon form of `TwoRound.phi_isSupermart`: on the product law `prodLaw T ν` of a horizon-`T`
disturbance word with the prefix filtration `prefixAtoms T`, `Φ_t = (1−η)^{−t}(d_t − ρ†)` (`PhiW`) should
satisfy `corr-trajectory`'s `SupermartStep` at every `t < T`. Finding F-21 diagnosed why it was not
proved; audit round 1 (fidelity N6, adversarial N3) asked for the precise statement with a `sorry`, listed
in `corr-landscape-open.txt`. This file is that statement.

* **Proved**: `Φ_t` is adapted to the prefix filtration (`phiW_adapted`): the trajectory at time `t` reads
  only the first `t` letters (`trajW_eq_of_prefix`).
* **OPEN** (`phiW_supermartStep`): the step inequality at `t < T`. The one-step contraction is
  `BasinToy.phi_step` (the inside is forward invariant by `traj_dist_lt`); what is missing is the
  factorization of the conditional sum over a prefix atom of the product law:
  `∑_{ω' ∈ atom_t(ω)} μ(ω') X(ω') = (∏_{i<t} ν(ω_i)) · ∑_a ν(a) X(ω[t ↦ a])` for `X` depending on the first
  `t + 1` letters, which needs a bijection between the atom and `A × (words on the indices > t)`. The
  two-round case is `TwoRound.condSum_atoms2_one`. The steps at `t ≥ T` are the deterministic tail
  (singleton atoms, zero disturbance) and are not part of the open statement.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace Horizon

open BasinToy

variable {A : Type} [Fintype A] [DecidableEq A]

/-- **`Φ_t = (1−η)^{−t}(d_t − ρ)`** on the horizon-`T` word space.
Source: mandate T6(e) (E2(i)); the general form of `TwoRound.Phi`
Kind: D
Fidelity: exact -/
noncomputable def PhiW (η r : ℝ) (s₀ : ℝ × ℝ) (ξv Δv : A → ℝ) (ρ : ℝ) (T : ℕ) (t : ℕ) (ω : Fin T → A) : ℝ :=
  (BasinToy.dist (trajW η r s₀ ξv Δv T ω t) - ρ) / (1 - η) ^ t

/-- The trajectory at time `t` reads only the first `t` letters.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma trajW_eq_of_prefix (η r : ℝ) (s₀ : ℝ × ℝ) (ξv Δv : A → ℝ) (T : ℕ) (ω ω' : Fin T → A) (t : ℕ)
    (h : ∀ i : Fin T, (i : ℕ) < t → ω' i = ω i) :
    trajW η r s₀ ξv Δv T ω' t = trajW η r s₀ ξv Δv T ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h' : ∀ i : Fin T, (i : ℕ) < t → ω' i = ω i := fun i hi => h i (by omega)
    have hl : ∀ v : A → ℝ, letter T ω' v t = letter T ω v t := by
      intro v
      unfold letter
      split_ifs with ht
      · rw [h ⟨t, ht⟩ (by simp)]
      · rfl
    unfold trajW at ih ⊢
    simp only [traj]
    rw [ih h', hl, hl]

/-- **`Φ` is adapted to the prefix filtration** (the `Meas` half of `IsSupermart`).
Source: mandate T6(e) (E2(i))
Kind: L
Fidelity: exact -/
theorem phiW_adapted (η r : ℝ) (s₀ : ℝ × ℝ) (ξv Δv : A → ℝ) (ρ : ℝ) (T t : ℕ) :
    (prefixAtoms T).Meas t (PhiW η r s₀ ξv Δv ρ T t) := by
  intro ω ω' h
  simp only [prefixAtoms, mem_filter, mem_univ, true_and] at h
  simp only [PhiW]
  rw [trajW_eq_of_prefix η r s₀ ξv Δv T ω ω' t h]

/-- **OPEN — the contraction as a `SupermartStep` over the general horizon**: on `prodLaw T ν` with the
prefix filtration, for `0 < η < 1`, `d_0 < r`, bounded disturbances on the alphabet and `η ξ̄ + σ̄* ≤ η r`,
`Φ = (1−η)^{−t}(d_t − ρ†)` satisfies the step inequality at every `t < T`. The two-round case is
`TwoRound.phi_isSupermart`; the obstacle is the prefix-atom factorization of the product law (F-21).
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(b); mandate T6(e) (E2(i)); finding F-21
Kind: OPEN
Fidelity: exact (the statement the mandate asks for)
Hyps: (a) only -/
theorem phiW_supermartStep (η r ξbar σbar : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (ν : Distr A) (ξv Δv : A → ℝ)
    (hξ : ∀ a, |ξv a| ≤ ξbar) (hΔ : ∀ a, |Δv a| ≤ σbar) (hcond : η * ξbar + σbar ≤ η * r) (s₀ : ℝ × ℝ)
    (hs : BasinToy.dist s₀ < r) (T t : ℕ) (ht : t < T) :
    SupermartStep (prodLaw T ν) (prefixAtoms T) (PhiW η r s₀ ξv Δv (rhoDagger η ν ξv Δv) T) t := by
  sorry

end Horizon

end Cleanroom.Corrigibility.CorrLandscape
