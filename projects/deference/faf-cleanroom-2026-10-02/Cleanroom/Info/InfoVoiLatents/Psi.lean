import Cleanroom.Info.InfoVoiLatents.Coverage
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# info-voi-latents — Ψ_t and the withdrawal of Φ_t (Target 11)

* (ii) **Entropy is not monotone under conditioning pointwise** (`posterior_entropy_can_increase`):
  the prior `(9/10, 1/10)` has binary entropy `h₂(1/10) < log 2`, and one observation with
  likelihood ratio `9 : 1` (likelihoods `(1, 9)`) moves the posterior to `(1/2, 1/2)`, whose entropy
  is `log 2`. Exact, via `Real.binEntropy`; the reusable witness for A13(ii).
* (iii) `Ψ`: the cumulative sup-norm disagreement at unlock over a finite execution record
  (bookkeeping, not a potential), with `Ψ_union_eq_iff`: `Ψ` does not grow across a batch of newly
  unlocked actions iff every action in the batch had disagreement `0` at unlock.
* (i) `Φ_t` is withdrawn (A13): recorded only, no definition.

Mandate: Target 11.
-/

namespace Cleanroom.Info.InfoVoiLatents.Psi

open Finset Real Cleanroom.Info.InfoVoiLatents.Coverage

noncomputable section

/-- **Posterior entropy can exceed prior entropy after an observation** (the reusable witness that
`h_t(C_k)` is not monotone in `t`): prior `(9/10, 1/10)`, likelihoods `(1, 9)`: the Bayes posterior
is `(1/2, 1/2)` and `h₂(1/10) < log 2 = h₂(1/2)`.
Source: [[generalization-adversary]] A13(ii) l. 120 ("surprising data can raise posterior
entropy"); [[generalization-final]] l. 97; items 134, 2-077
Kind: N+
Fidelity: exact -/
theorem posterior_entropy_can_increase :
    bayesPost (![9 / 10, 1 / 10] : Fin 2 → ℝ) ![1, 9] = ![1 / 2, 1 / 2] ∧
    Real.binEntropy (1 / 10) < Real.binEntropy (1 / 2) ∧ Real.binEntropy (1 / 2) = Real.log 2 := by
  refine ⟨?_, ?_, ?_⟩
  · funext l
    fin_cases l <;> simp [bayesPost, Fin.sum_univ_two] <;> norm_num
  · rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
    exact Real.binEntropy_lt_log_two.2 (by norm_num)
  · rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]

/-- **`Ψ`**: the cumulative disagreement at unlock over an execution record (pairs of an action and
its sup-norm disagreement at the moment it was first executed).
Source: [[generalization-final]] l. 97 (`Ψ_t := ∑_{k : τ_k ≤ t} dis_{τ_k⁻}(C_k)`);
[[generalization-adversary]] A13 l. 120 ("a bookkeeping of past violations, not a Lyapunov
function")
Kind: D
Fidelity: exact (bookkeeping over a finite record; no potential theorem is claimed) -/
def Ψ {α : Type} (record : Finset (α × ℝ)) : ℝ := ∑ q ∈ record, q.2

/-- **`Ψ` is unchanged across a batch of newly unlocked actions iff every one had disagreement `0`
at unlock** (disagreements are nonnegative).
Source: [[generalization-final]] l. 97; Target 11(iii)
Kind: L
Fidelity: exact -/
theorem Ψ_union_eq_iff {α : Type} [DecidableEq α] {record new : Finset (α × ℝ)}
    (hdisj : Disjoint record new) (hnn : ∀ q ∈ new, 0 ≤ q.2) :
    Ψ (record ∪ new) = Ψ record ↔ ∀ q ∈ new, q.2 = 0 := by
  unfold Ψ
  rw [Finset.sum_union hdisj, add_eq_left]
  exact Finset.sum_eq_zero_iff_of_nonneg hnn

end

end Cleanroom.Info.InfoVoiLatents.Psi
