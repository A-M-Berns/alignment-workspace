import Cleanroom.Corrigibility.CorrTrajectory.Potential
import Cleanroom.Corrigibility.CorrTrajectory.ProductLaw
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# `corr-landscape` — `BasinToy`: S7, the basin as D9′ invariant, contraction, outside, kill (T6, load-bearing 1)

D9′ ([[corr-wf14-inventory]] 119; [[corr-wf14-2-inventory]] 2-052; P5) as a **deterministic recursion
with bounded disturbance sequences**: `θ*_{t+1} = θ*_t + Δ*_t` (`|Δ*_t| ≤ σ̄*`), the offered correction
`θ*_t − θ_t + ξ_t` (`|ξ_t| ≤ ξ̄`) accepted iff `d_t = |θ_t − θ*_t| < r` (`p_out = 0`), gain `η`.

* (a) **Invariant** (`step_dist_lt`, `traj_dist_lt`): `d_t < r ∧ η ξ̄ + σ̄* ≤ η r ⟹ d_{t+1} < r` — for
  `0 < η < 1`. At `η = 1` the source's condition must be strict (`eta_one_boundary` is the counterexample;
  `step_dist_lt_of_strict` is the `η ≤ 1` form). Worked: `9/200 ≤ 1/2`.
* (b) **Contraction** over a finite disturbance law `ν` on an alphabet with maps `ξv, Δv`:
  `E[d_{t+1} ∣ s_t] ≤ (1 − η) d_t + η E|ξ| + E|Δ*|` on the inside (`contraction`); `ρ† := (η E|ξ| + E|Δ*|)/η`;
  `d` is a one-step supermartingale on `{ρ† ≤ d < r}` (`supermart_above_rho`); `Φ_t = (1−η)^{−t}(d_t − ρ†)`
  satisfies the step inequality everywhere inside (`phi_step`) but is negative below `ρ†`
  (`phi_neg_below_rho`), and the `max(·, 0)` repair fails (`max_repair_fails`, one step on the worked
  law). The symmetric three-point law `{−b, 0, b}` with masses `(1/4, 1/2, 1/4)` gives `E|ξ| = ξ̄/2`
  exactly (`expect_abs_threeVal`), reproducing the source's uniform-noise `ρ† = ξ̄/2 + σ̄*/(2η) = 9/200`
  (`rho_worked`) — a (c)-free N+ (the uniform law has no finite shadow; the three-point law is its own
  object with the same first absolute moments).
* (c) **Outside**: `d_t ≥ r ⟹ θ_{t+1} = θ_t` (`step_outside`); the separation pair **against a drifting
  target** (`Δ* ≡ −σ`, `σ > 0`, from `d_0 = r`): D9′ stays frozen with `d_t = r + tσ`, unbounded
  (`traj_outside_drift`, `traj_outside_unbounded`), while D9 from the same data enters `{d < r}` at step 1
  and stays, converging to the lag `σ/η < r` (`trajD9_enters_drift`) — **a basin exists iff acceptance
  depends on distance** (N+). The zero-disturbance pair (`traj_frozen_at_r`, `trajD9_enters`) is the
  deterministic skeleton (N−).
* (d) **Refutation row** — `approval.md` S7/D9: the basin of radius `r` is `{d < r}` with acceptance
  independent of `d`. In D9 the invariance holds for **every** `r` above the noise scale
  (`stepD9_dist_lt`): `r` is a label. Surviving neighbour: D9′ with (c).
* (e) **Bridge**: pointwise forward invariance of a family of events is `corr-trajectory`'s
  `forwardInvariantWithHazard` at hazard `0` for every law and filtration (`forwardInvariant_of_pointwise`),
  and the basin's inside events over the product law of a horizon-`T` disturbance word with the prefix
  filtration are such a family (`basin_forwardInvariant`, kind C). The `SupermartStep` form of the
  contraction on the product space is `TwoRound` (two rounds, where the product structure is
  `prod2`).

Gaussian noise (A7.3, 2-052(b)) has no finite shadow: "no a.s. invariant ball under unbounded noise"
is recorded in the findings as text. The simulation statistics are Monte Carlo and not formalized.
Nothing here is called `Basin`.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace BasinToy

/-! ## The recursion -/

/-- **D9′, one step**: the overseer offers `θ* − θ + ξ`; the agent accepts iff `|θ − θ*| < r` and moves by
gain `η`; the target moves by `Δ*`.
Source: [[corr-wf14-inventory]] 119; [[corr-wf14-2-inventory]] 2-052 / approval-final.md D9′
Kind: D
Fidelity: exact (`p_out = 0`; the disturbances are sequences, the bounds are hypotheses) -/
noncomputable def step (η r : ℝ) (s : ℝ × ℝ) (ξ Δ : ℝ) : ℝ × ℝ :=
  (if |s.1 - s.2| < r then s.1 + η * (s.2 - s.1 + ξ) else s.1, s.2 + Δ)

/-- **D9, one step**: acceptance independent of the distance (the develop's toy, `r = ∞`).
Source: [[corr-wf14-2-inventory]] 2-052 / approval.md D9; approval-adversary.md A7.1
Kind: D
Fidelity: exact -/
def stepD9 (η : ℝ) (s : ℝ × ℝ) (ξ Δ : ℝ) : ℝ × ℝ := (s.1 + η * (s.2 - s.1 + ξ), s.2 + Δ)

/-- `d = |θ − θ*|`. Source: approval-final.md D9′. Kind: D. Fidelity: exact -/
def dist (s : ℝ × ℝ) : ℝ := |s.1 - s.2|

/-- The D9′ trajectory from an initial state and disturbance sequences.
Source: [[corr-wf14-inventory]] 119 / approval-final.md D9′
Kind: D
Fidelity: exact -/
noncomputable def traj (η r : ℝ) (s₀ : ℝ × ℝ) (ξ Δ : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => s₀
  | t + 1 => step η r (traj η r s₀ ξ Δ t) (ξ t) (Δ t)

/-- The D9 trajectory. Source: approval.md D9. Kind: D. Fidelity: exact -/
def trajD9 (η : ℝ) (s₀ : ℝ × ℝ) (ξ Δ : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => s₀
  | t + 1 => stepD9 η (trajD9 η s₀ ξ Δ t) (ξ t) (Δ t)

/-- Inside the ball the error recursion is `(1 − η)(θ − θ*) + η ξ − Δ*` (P5's first line).
Source: [[corr-wf14-inventory]] 119 / approval-final.md P5
Kind: L
Fidelity: exact -/
lemma step_inside_sub (η r : ℝ) (s : ℝ × ℝ) (ξ Δ : ℝ) (hs : dist s < r) :
    (step η r s ξ Δ).1 - (step η r s ξ Δ).2 = (1 - η) * (s.1 - s.2) + η * ξ - Δ := by
  unfold dist at hs
  simp only [step, hs, if_true]; ring

/-- The triangle bound `|(1 − η) x + η ξ − Δ| ≤ (1 − η)|x| + η|ξ| + |Δ|` for `0 ≤ η ≤ 1`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma abs_recursion_le (η x ξ Δ : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    |(1 - η) * x + η * ξ - Δ| ≤ (1 - η) * |x| + η * |ξ| + |Δ| := by
  calc |(1 - η) * x + η * ξ - Δ| ≤ |(1 - η) * x + η * ξ| + |Δ| := abs_sub _ _
    _ ≤ |(1 - η) * x| + |η * ξ| + |Δ| := by gcongr; exact abs_add_le _ _
    _ = (1 - η) * |x| + η * |ξ| + |Δ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - η), abs_of_nonneg hη0]

/-! ## (a) the invariant -/

/-- **P5(a), the exact invariant**: for `0 < η < 1`, bounded disturbances `|ξ| ≤ ξ̄`, `|Δ*| ≤ σ̄*`, and
`η ξ̄ + σ̄* ≤ η r`, the step keeps `d < r`.
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(a), P5(a)
Kind: P
Fidelity: exact for `η < 1`; at `η = 1` the condition must be strict (`eta_one_boundary`)
Hyps: (a) only -/
theorem step_dist_lt (η r ξbar σbar : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (s : ℝ × ℝ) (ξ Δ : ℝ)
    (hξ : |ξ| ≤ ξbar) (hΔ : |Δ| ≤ σbar) (hcond : η * ξbar + σbar ≤ η * r) (hs : dist s < r) :
    dist (step η r s ξ Δ) < r := by
  have hin := step_inside_sub η r s ξ Δ hs
  unfold dist at hs ⊢
  rw [hin]
  have h1 := abs_recursion_le η (s.1 - s.2) ξ Δ hη0.le hη1.le
  nlinarith [mul_lt_mul_of_pos_left hs (by linarith : (0 : ℝ) < 1 - η),
    mul_le_mul_of_nonneg_left hξ hη0.le]

/-- **The `η ≤ 1` form**: with the condition strict, `η ξ̄ + σ̄* < η r`, the invariant holds for every
`0 < η ≤ 1`.
Source: [[corr-wf14-inventory]] 119 / approval-final.md P5(a) (the `η ∈ (0,1]` range of D9′)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem step_dist_lt_of_strict (η r ξbar σbar : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (s : ℝ × ℝ) (ξ Δ : ℝ)
    (hξ : |ξ| ≤ ξbar) (hΔ : |Δ| ≤ σbar) (hcond : η * ξbar + σbar < η * r) (hs : dist s < r) :
    dist (step η r s ξ Δ) < r := by
  have hin := step_inside_sub η r s ξ Δ hs
  unfold dist at hs ⊢
  rw [hin]
  have h1 := abs_recursion_le η (s.1 - s.2) ξ Δ hη0.le hη1
  nlinarith [mul_le_mul_of_nonneg_left hs.le (by linarith : (0 : ℝ) ≤ 1 - η),
    mul_le_mul_of_nonneg_left hξ hη0.le]

/-- **The `η = 1` boundary**: at `η = 1`, `r = 1`, `ξ̄ = σ̄* = 1/2` the source's condition `η ξ̄ + σ̄* ≤ η r`
holds with equality, `d_0 = 0 < r`, and the step with `ξ = 1/2`, `Δ* = −1/2` lands exactly on `d_1 = 1 = r`:
P5(a)'s "`d_{t+1} < r` whenever `η ξ̄ + σ̄* ≤ η r`" silently uses `η < 1`.
Source: [[corr-wf14-inventory]] 119 / approval-final.md P5(a) (finding)
Kind: N− (boundary counterexample)
Fidelity: exact
Hyps: (a) only -/
theorem eta_one_boundary :
    (1 : ℝ) * (1 / 2) + 1 / 2 ≤ 1 * 1 ∧ dist ((0 : ℝ), (0 : ℝ)) < 1 ∧ |(1 / 2 : ℝ)| ≤ 1 / 2 ∧
      |(-(1 / 2) : ℝ)| ≤ 1 / 2 ∧ dist (step 1 1 ((0 : ℝ), (0 : ℝ)) (1 / 2) (-(1 / 2))) = 1 := by
  refine ⟨by norm_num, by simp [dist], by norm_num, by norm_num, ?_⟩
  simp [step, dist]; norm_num

/-- **The invariant along the trajectory**: from `d_0 < r`, with every disturbance bounded, `d_t < r` for
all `t` (`0 < η < 1`).
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(a) ("`200` runs of `5000` steps from `d_0 = 0.5`:
zero exits")
Kind: P
Fidelity: exact (every bounded disturbance sequence, not a sample)
Hyps: (a) only -/
theorem traj_dist_lt (η r ξbar σbar : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (s₀ : ℝ × ℝ) (ξ Δ : ℕ → ℝ)
    (hξ : ∀ t, |ξ t| ≤ ξbar) (hΔ : ∀ t, |Δ t| ≤ σbar) (hcond : η * ξbar + σbar ≤ η * r)
    (hs : dist s₀ < r) : ∀ t, dist (traj η r s₀ ξ Δ t) < r := by
  intro t
  induction t with
  | zero => exact hs
  | succ t ih => exact step_dist_lt η r ξbar σbar hη0 hη1 _ _ _ (hξ t) (hΔ t) hcond ih

/-- The worked condition: `η = 1/2`, `ξ̄ = 1/20`, `σ̄* = 1/50`, `r = 1`: `9/200 ≤ 1/2`.
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(a) ("toy: `0.045 ≤ 0.5`")
Kind: N+
Fidelity: exact -/
theorem worked_condition : (1 / 2 : ℝ) * (1 / 20) + 1 / 50 ≤ 1 / 2 * 1 ∧ (1 / 2 : ℝ) * (1 / 20) + 1 / 50 = 9 / 200 := by
  norm_num

/-! ## (b) the contraction over a finite disturbance law -/

section Contraction

variable {A : Type} [Fintype A]

/-- **P5(b), the contraction**: for a finite law `ν` of the disturbance pair `(ξ, Δ*)`, on the inside
`E[d_{t+1} ∣ s_t] ≤ (1 − η) d_t + η E|ξ| + E|Δ*|`.
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(b), P5(b)
Kind: P
Fidelity: exact (finite law; the source's uniform `E|ξ| = ξ̄/2` is one instance, `expect_abs_threeVal`)
Hyps: (a) only -/
theorem contraction (η r : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (ν : Distr A) (ξv Δv : A → ℝ) (s : ℝ × ℝ)
    (hs : dist s < r) :
    expect ν (fun a => dist (step η r s (ξv a) (Δv a))) ≤
      (1 - η) * dist s + η * expect ν (fun a => |ξv a|) + expect ν (fun a => |Δv a|) := by
  have hpt : ∀ a, dist (step η r s (ξv a) (Δv a)) ≤ (1 - η) * dist s + η * |ξv a| + |Δv a| := by
    intro a
    unfold dist
    rw [step_inside_sub η r s _ _ hs]
    exact abs_recursion_le η _ _ _ hη0.le hη1
  refine le_trans (expect_mono ν hpt) (le_of_eq ?_)
  unfold expect
  simp only [mul_add, sum_add_distrib]
  have h1 : ∑ a, ν.mass a * ((1 - η) * dist s) = (1 - η) * dist s := by
    rw [← sum_mul, ν.sum_eq_one, one_mul]
  have h2 : ∑ a, ν.mass a * (η * |ξv a|) = η * ∑ a, ν.mass a * |ξv a| := by
    rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
  rw [h1, h2]

/-- **`ρ† = (η E|ξ| + E|Δ*|)/η`** for the finite law (the source's `ξ̄/2 + σ̄*/(2η)` is the uniform case).
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(b) ("`ρ† := (η ξ̄/2 + σ̄*/2)/η`")
Kind: D
Fidelity: exact under `0 < η` -/
noncomputable def rhoDagger (η : ℝ) (ν : Distr A) (ξv Δv : A → ℝ) : ℝ :=
  (η * expect ν (fun a => |ξv a|) + expect ν (fun a => |Δv a|)) / η

/-- The contraction in `ρ†` form: `E[d'] ≤ (1 − η) d + η ρ†`.
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(b)
Kind: L
Fidelity: exact -/
theorem contraction_rho (η r : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (ν : Distr A) (ξv Δv : A → ℝ) (s : ℝ × ℝ)
    (hs : dist s < r) :
    expect ν (fun a => dist (step η r s (ξv a) (Δv a))) ≤ (1 - η) * dist s + η * rhoDagger η ν ξv Δv := by
  rw [rhoDagger, mul_div_cancel₀ _ hη0.ne']
  linarith [contraction η r hη0 hη1 ν ξv Δv s hs]

/-- **`d` is a one-step supermartingale on `{ρ† ≤ d < r}`**: the source's "a supermartingale above `ρ†`",
stated exactly.
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(b) ("`d_t` is a supermartingale above `ρ†`")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem supermart_above_rho (η r : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (ν : Distr A) (ξv Δv : A → ℝ)
    (s : ℝ × ℝ) (hs : dist s < r) (hρ : rhoDagger η ν ξv Δv ≤ dist s) :
    expect ν (fun a => dist (step η r s (ξv a) (Δv a))) ≤ dist s := by
  have := contraction_rho η r hη0 hη1 ν ξv Δv s hs
  nlinarith [mul_le_mul_of_nonneg_left hρ hη0.le]

/-- **`Φ_t = (1 − η)^{−t}(d_t − ρ†)` satisfies the step inequality everywhere inside** (`0 < η < 1`):
`E[Φ_{t+1}] ≤ Φ_t` — but `Φ` is not a potential (`phi_neg_below_rho`).
Source: mandate T6(e) (extension E2(i))
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem phi_step (η r : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (ν : Distr A) (ξv Δv : A → ℝ) (s : ℝ × ℝ)
    (hs : dist s < r) (t : ℕ) :
    expect ν (fun a => (dist (step η r s (ξv a) (Δv a)) - rhoDagger η ν ξv Δv) / (1 - η) ^ (t + 1)) ≤
      (dist s - rhoDagger η ν ξv Δv) / (1 - η) ^ t := by
  have hpos : 0 < (1 - η) ^ (t + 1) := pow_pos (by linarith) _
  have hpos' : 0 < (1 - η) ^ t := pow_pos (by linarith) _
  have hc := contraction_rho η r hη0 hη1.le ν ξv Δv s hs
  have e : expect ν (fun a => (dist (step η r s (ξv a) (Δv a)) - rhoDagger η ν ξv Δv) / (1 - η) ^ (t + 1)) =
      (expect ν (fun a => dist (step η r s (ξv a) (Δv a))) - rhoDagger η ν ξv Δv) / (1 - η) ^ (t + 1) := by
    unfold expect
    simp only [div_eq_mul_inv]
    have h1 : ∑ a, ν.mass a * ((dist (step η r s (ξv a) (Δv a)) - rhoDagger η ν ξv Δv) * ((1 - η) ^ (t + 1))⁻¹) =
        (∑ a, ν.mass a * dist (step η r s (ξv a) (Δv a))) * ((1 - η) ^ (t + 1))⁻¹ -
          (∑ a, ν.mass a) * (rhoDagger η ν ξv Δv * ((1 - η) ^ (t + 1))⁻¹) := by
      rw [sum_mul, sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun a _ => by ring
    rw [h1, ν.sum_eq_one, one_mul, sub_mul]
  rw [e, div_le_div_iff₀ hpos hpos', pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right hc hpos'.le, mul_pos hpos' (by linarith : (0 : ℝ) < 1 - η)]

/-- **Nonnegativity fails below `ρ†`**: `Φ_t < 0` whenever `d_t < ρ†`, so `IsPotential` (which needs
`Φ ≥ 0`) does not apply to `Φ`.
Source: mandate T6(e) ("say exactly where nonnegativity fails")
Kind: L
Fidelity: exact -/
theorem phi_neg_below_rho (η ρ d : ℝ) (hη1 : η < 1) (t : ℕ) (hd : d < ρ) : (d - ρ) / (1 - η) ^ t < 0 :=
  div_neg_of_neg_of_pos (by linarith) (pow_pos (by linarith) _)

end Contraction

/-! ### The symmetric three-point law (N+ for (b)) -/

/-- The three-point law `{−b, 0, b}` with masses `(1/4, 1/2, 1/4)`.
Source: mandate T6(b) ("a symmetric three-point law … reproduces `E|ξ| = ξ̄/2` exactly")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def threePoint : Distr (Fin 3) where
  mass i := ![1 / 4, 1 / 2, 1 / 4] i
  nonneg i := by fin_cases i <;> simp
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- The three values `(−b, 0, b)`. Source: mandate T6(b). Kind: D. Fidelity: n/a (witness) -/
def threeVal (b : ℝ) : Fin 3 → ℝ := ![-b, 0, b]

/-- **`E|ξ| = b/2`** under the three-point law (`0 ≤ b`): the source's uniform first absolute moment,
reproduced exactly by a finite law.
Source: [[corr-wf14-inventory]] 119 / approval-final.md P5(b) ("`E|ξ_t| = ξ̄/2`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem expect_abs_threeVal (b : ℝ) (hb : 0 ≤ b) : expect threePoint (fun i => |threeVal b i|) = b / 2 := by
  simp [expect, threePoint, threeVal, Fin.sum_univ_three, abs_of_nonneg hb]
  ring

/-- The joint law of `(ξ, Δ*)`: the product of two three-point laws (`corr-trajectory`'s `prod2`).
Source: mandate T6(b). Kind: D. Fidelity: n/a (witness) -/
noncomputable def jointLaw : Distr (Fin 3 × Fin 3) := prod2 threePoint threePoint

/-- The `ξ` coordinate of the joint alphabet. Source: mandate T6(b). Kind: D. Fidelity: n/a -/
def xiOf (ξbar : ℝ) (a : Fin 3 × Fin 3) : ℝ := threeVal ξbar a.1

/-- The `Δ*` coordinate of the joint alphabet. Source: mandate T6(b). Kind: D. Fidelity: n/a -/
def deltaOf (σbar : ℝ) (a : Fin 3 × Fin 3) : ℝ := threeVal σbar a.2

/-- The joint law's first absolute moments are the marginals': `E|ξ| = ξ̄/2`, `E|Δ*| = σ̄*/2`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma jointLaw_moments (ξbar σbar : ℝ) (hξ : 0 ≤ ξbar) (hσ : 0 ≤ σbar) :
    expect jointLaw (fun a => |xiOf ξbar a|) = ξbar / 2 ∧
      expect jointLaw (fun a => |deltaOf σbar a|) = σbar / 2 := by
  constructor <;>
  · simp [expect, jointLaw, xiOf, deltaOf, threePoint, threeVal, Fintype.sum_prod_type, Fin.sum_univ_three,
      abs_of_nonneg hξ, abs_of_nonneg hσ]
    ring

/-- **The worked `ρ† = 9/200`** (`= 0.045`) at `η = 1/2`, `ξ̄ = 1/20`, `σ̄* = 1/50` on the joint
three-point law, and the bounds `|ξ| ≤ ξ̄`, `|Δ*| ≤ σ̄*` hold on the whole alphabet.
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(b) ("`ρ† … = 0.045`")
Kind: N+
Fidelity: exact (the uniform law's moments, from a finite law)
Hyps: (a) only -/
theorem rho_worked :
    rhoDagger (1 / 2) jointLaw (xiOf (1 / 20)) (deltaOf (1 / 50)) = 9 / 200 ∧
      (∀ a, |xiOf (1 / 20) a| ≤ 1 / 20) ∧ (∀ a, |deltaOf (1 / 50) a| ≤ 1 / 50) := by
  obtain ⟨m1, m2⟩ := jointLaw_moments (1 / 20) (1 / 50) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [rhoDagger, m1, m2]; norm_num
  · rintro ⟨i, j⟩; fin_cases i <;> simp [xiOf, threeVal]
  · rintro ⟨i, j⟩; fin_cases j <;> simp [deltaOf, threeVal]

/-- **The `max(·, 0)` repair fails**: at `d = ρ† = 9/200` (so `Φ_0 = 0`) the one-step expectation of
`max(Φ_1, 0)` on the worked law is positive — `max(Φ, 0)` is not a one-step supermartingale (Jensen goes
the wrong way for a convex clamp).
Source: mandate T6(e) ("whether `max(·,0)` repairs the step")
Kind: N− (counterexample)
Fidelity: exact
Hyps: (a) only -/
theorem max_repair_fails :
    max (((9 : ℝ) / 200 - 9 / 200) / (1 - 1 / 2) ^ 0) 0 <
      expect jointLaw (fun a =>
        max ((dist (step (1 / 2) 1 ((9 / 200 : ℝ), (0 : ℝ)) (xiOf (1 / 20) a) (deltaOf (1 / 50) a)) - 9 / 200) /
          (1 - 1 / 2) ^ 1) 0) := by
  simp only [sub_self, zero_div, max_self]
  unfold expect
  have hnn : ∀ a ∈ (univ : Finset (Fin 3 × Fin 3)), 0 ≤ jointLaw.mass a *
      max ((dist (step (1 / 2) 1 ((9 / 200 : ℝ), (0 : ℝ)) (xiOf (1 / 20) a) (deltaOf (1 / 50) a)) - 9 / 200) /
        (1 - 1 / 2) ^ 1) 0 :=
    fun a _ => mul_nonneg (jointLaw.nonneg a) (le_max_right _ _)
  refine lt_of_lt_of_le ?_ (single_le_sum hnn (mem_univ ((2 : Fin 3), (0 : Fin 3))))
  simp [jointLaw, threePoint, xiOf, deltaOf, threeVal, step, dist]
  norm_num

/-! ## (c) the outside and the separation pair -/

/-- **Outside, the estimate freezes**: `d ≥ r ⟹ θ_{t+1} = θ_t`.
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(c), P5(c)
Kind: L
Fidelity: exact -/
theorem step_outside (η r : ℝ) (s : ℝ × ℝ) (ξ Δ : ℝ) (hs : ¬ dist s < r) : (step η r s ξ Δ).1 = s.1 := by
  unfold dist at hs; simp [step, hs]

/-- **D9′ from `d_0 = r` with `ξ ≡ Δ* ≡ 0` stays at `d_t = r` forever** (`0 ≤ r`): the deterministic
skeleton of the separation (constant disturbance sequences, so N− by STANDARDS §3; the N+ pair with a
drifting target is `traj_outside_drift`/`trajD9_enters_drift` below — audit r1, adversarial B2).
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(c) ("no attraction, re-entry only by chance")
Kind: N− (zero disturbances; the skeleton)
Fidelity: exact
Hyps: (a) only -/
theorem traj_frozen_at_r (η r : ℝ) (hr : 0 ≤ r) (t : ℕ) :
    traj η r (r, 0) (fun _ => 0) (fun _ => 0) t = (r, 0) ∧ dist (traj η r (r, 0) (fun _ => 0) (fun _ => 0) t) = r := by
  induction t with
  | zero => simp [traj, dist, abs_of_nonneg hr]
  | succ t ih =>
    have hout : ¬ dist (r, 0) < r := by simp [dist, abs_of_nonneg hr]
    have : traj η r (r, 0) (fun _ => 0) (fun _ => 0) (t + 1) = (r, 0) := by
      simp only [traj, ih.1]
      ext
      · exact step_outside η r (r, 0) 0 0 hout
      · simp [step]
    exact ⟨this, by rw [this]; simp [dist, abs_of_nonneg hr]⟩

/-- **D9 from the same `d_0 = r`, zero disturbances, enters `{d < r}` at step 1 and stays**:
`d_t = (1 − η)^t r < r` for `t ≥ 1` (`0 < η ≤ 1`, `0 < r`). The skeleton half of the separation (N−, zero
disturbances); the N+ pair against a drifting target is below.
Source: [[corr-wf14-inventory]] 119; [[corr-wf14-2-inventory]] 2-052 / approval-final.md S7 ("a basin
exists in this toy iff the agent's acceptance of corrections depends on its distance")
Kind: N− (zero disturbances; the skeleton)
Fidelity: exact
Hyps: (a) only -/
theorem trajD9_enters (η r : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hr : 0 < r) :
    (∀ t, trajD9 η (r, 0) (fun _ => 0) (fun _ => 0) t = ((1 - η) ^ t * r, 0)) ∧
      ∀ t, 1 ≤ t → dist (trajD9 η (r, 0) (fun _ => 0) (fun _ => 0) t) < r := by
  have h1 : ∀ t, trajD9 η (r, 0) (fun _ => 0) (fun _ => 0) t = ((1 - η) ^ t * r, 0) := by
    intro t
    induction t with
    | zero => simp [trajD9]
    | succ t ih => simp only [trajD9, ih, stepD9]; ext <;> simp; ring
  refine ⟨h1, fun t ht => ?_⟩
  rw [h1, dist]
  simp only [sub_zero]
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (by linarith) _) hr.le)]
  have : (1 - η) ^ t < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  nlinarith

/-! ### The separation pair against a drifting target (N+; audit r1, adversarial B2) -/

/-- **D9′ from `d_0 = r` against a target drifting away at rate `σ ≥ 0`** (`Δ* ≡ −σ`, `ξ ≡ 0`): the
estimate stays frozen at `θ_0 = r` and `d_t = r + t σ` — the outside is not attracted; the error follows
the target's walk (S7(c)).
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(c) ("`θ_t` freezes and `d_t` performs a random
walk … against the drifting target: no attraction")
Kind: N+ (the outside half of the separation, non-zero drift)
Fidelity: exact (a deterministic drift in place of the source's random walk)
Hyps: (a) only -/
theorem traj_outside_drift (η r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 ≤ σ) (t : ℕ) :
    traj η r (r, 0) (fun _ => 0) (fun _ => -σ) t = (r, -(t * σ)) ∧
      dist (traj η r (r, 0) (fun _ => 0) (fun _ => -σ) t) = r + t * σ := by
  induction t with
  | zero => simp [traj, dist, abs_of_nonneg hr]
  | succ t ih =>
    have hout : ¬ dist (r, -(t * σ)) < r := by
      simp only [dist]
      rw [sub_neg_eq_add, abs_of_nonneg (by positivity)]
      nlinarith [mul_nonneg (Nat.cast_nonneg t) hσ]
    have hstep : traj η r (r, 0) (fun _ => 0) (fun _ => -σ) (t + 1) = (r, -((t + 1 : ℕ) * σ)) := by
      simp only [traj, ih.1]
      ext
      · exact step_outside η r (r, -(t * σ)) 0 (-σ) hout
      · simp [step]; push_cast; ring
    refine ⟨hstep, ?_⟩
    rw [hstep]
    simp only [dist]
    rw [sub_neg_eq_add, abs_of_nonneg (by positivity)]

/-- **The outside diverges under D9′** against a target drifting at any rate `σ > 0`: `d_t` exceeds every
bound.
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(c)
Kind: N+ (corollary of `traj_outside_drift`)
Fidelity: exact
Hyps: (a) only -/
theorem traj_outside_unbounded (η r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 < σ) (M : ℝ) :
    ∃ t : ℕ, M < dist (traj η r (r, 0) (fun _ => 0) (fun _ => -σ) t) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (M / σ)
  refine ⟨n, ?_⟩
  rw [(traj_outside_drift η r σ hr hσ.le n).2]
  rw [div_lt_iff₀ hσ] at hn
  linarith

/-- **D9 from the same data is attracted**: against the drift `−σ` with `σ < η r` (`0 < η ≤ 1`, `0 < r`),
D9's error is `d_t = (1 − η)^t (r − σ/η) + σ/η`, strictly inside `{d < r}` for every `t ≥ 1` and
converging to the lag `σ/η < r`. With `traj_outside_drift` this is the N+ for "a basin exists iff
acceptance depends on distance": the same disturbances, the same start, and only the `d`-dependence of
acceptance separates divergence from attraction.
Source: [[corr-wf14-inventory]] 119; [[corr-wf14-2-inventory]] 2-052 / approval-final.md S7
Kind: N+ (the inside half of the separation, non-zero drift)
Fidelity: exact
Hyps: (a) only -/
theorem trajD9_enters_drift (η r σ : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hr : 0 < r) (hσ : 0 ≤ σ)
    (hcond : σ < η * r) :
    (∀ t, (trajD9 η (r, 0) (fun _ => 0) (fun _ => -σ) t).2 = -(t * σ) ∧
      (trajD9 η (r, 0) (fun _ => 0) (fun _ => -σ) t).1 - (trajD9 η (r, 0) (fun _ => 0) (fun _ => -σ) t).2 =
        (1 - η) ^ t * (r - σ / η) + σ / η) ∧
      ∀ t, 1 ≤ t → dist (trajD9 η (r, 0) (fun _ => 0) (fun _ => -σ) t) < r := by
  have hη : η ≠ 0 := hη0.ne'
  have hlag : σ / η < r := by rw [div_lt_iff₀ hη0]; linarith
  have hlag0 : 0 ≤ σ / η := div_nonneg hσ hη0.le
  have h1 : ∀ t, (trajD9 η (r, 0) (fun _ => 0) (fun _ => -σ) t).2 = -(t * σ) ∧
      (trajD9 η (r, 0) (fun _ => 0) (fun _ => -σ) t).1 - (trajD9 η (r, 0) (fun _ => 0) (fun _ => -σ) t).2 =
        (1 - η) ^ t * (r - σ / η) + σ / η := by
    intro t
    induction t with
    | zero => simp [trajD9]
    | succ t ih =>
      obtain ⟨ih2, ihd⟩ := ih
      simp only [trajD9, stepD9]
      constructor
      · rw [ih2]; push_cast; ring
      · have : (trajD9 η (r, 0) (fun _ => 0) (fun _ => -σ) t).1 =
            (1 - η) ^ t * (r - σ / η) + σ / η + (trajD9 η (r, 0) (fun _ => 0) (fun _ => -σ) t).2 := by
          linarith
        rw [this, ih2, pow_succ]
        field_simp
        ring
  refine ⟨h1, fun t ht => ?_⟩
  obtain ⟨-, hd⟩ := h1 t
  unfold dist
  rw [hd]
  have hpos : 0 < r - σ / η := by linarith
  have hpow : (1 - η) ^ t < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hpow0 : 0 ≤ (1 - η) ^ t := pow_nonneg (by linarith) _
  rw [abs_of_nonneg (by positivity)]
  nlinarith

/-! ## (d) the refutation row: in D9 every `r` above the noise scale is "invariant" -/

/-- **A7.1: in D9 the invariance holds for every `r` with `η ξ̄ + σ̄* ≤ η r`** (`0 < η < 1`) — the
transition law never consults `r`, so `r` is a label. The source sentence (`approval.md` D9/S7): "The
'basin' of radius `r` is `{d < r}`", with acceptance independent of `d_t`. Surviving neighbour: D9′ with
`traj_frozen_at_r`/`trajD9_enters`.
Source: [[corr-wf14-2-inventory]] 2-052 / approval.md D9 (l. 45), S7 (l. 71); approval-adversary.md A7.1
Kind: L (the D9 instance of `step_dist_lt`'s triangle bound, quantified over `r`; the refutation is A7.1's
reading, carried jointly with the separation pair — audit r1, fidelity N2)
Fidelity: exact
Hyps: (a) only -/
theorem stepD9_dist_lt (η ξbar σbar : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (s : ℝ × ℝ) (ξ Δ : ℝ)
    (hξ : |ξ| ≤ ξbar) (hΔ : |Δ| ≤ σbar) :
    ∀ r, η * ξbar + σbar ≤ η * r → dist s < r → dist (stepD9 η s ξ Δ) < r := by
  intro r hcond hs
  unfold dist at hs ⊢
  have hin : (stepD9 η s ξ Δ).1 - (stepD9 η s ξ Δ).2 = (1 - η) * (s.1 - s.2) + η * ξ - Δ := by
    simp only [stepD9]; ring
  rw [hin]
  have h1 := abs_recursion_le η (s.1 - s.2) ξ Δ hη0.le hη1.le
  nlinarith [mul_lt_mul_of_pos_left hs (by linarith : (0 : ℝ) < 1 - η),
    mul_le_mul_of_nonneg_left hξ hη0.le]

/-! ## (e) the bridge to `corr-trajectory`'s D4 at hazard `0` -/

/-- **Pointwise forward invariance is D4 at hazard `0`** for every law and every filtration: if
`I_t ⊆ I_{t+1}` pointwise, then `forwardInvariantWithHazard μ A I (fun _ => 0)`.
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(a); corr-trajectory ledger ("the contraction
theorem is `corr-landscape`'s")
Kind: L
Fidelity: exact -/
theorem forwardInvariant_of_pointwise {Ω : Type} [Fintype Ω] [DecidableEq Ω] (μ : Distr Ω) (A : Atoms Ω)
    (I : ℕ → Finset Ω) (h : ∀ t ω, ω ∈ I t → ω ∈ I (t + 1)) :
    forwardInvariantWithHazard μ A I (fun _ => 0) := by
  intro t ω
  have hz : (fun ω' => ind (I t) ω' * (1 - ind (I (t + 1)) ω')) = fun _ => (0 : ℝ) := by
    funext ω'
    unfold ind
    by_cases h1 : ω' ∈ I t
    · simp [h1, h t ω' h1]
    · simp [h1]
  rw [hz, zero_mul]
  simp [condSum]

section Product

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The product law of a horizon-`T` disturbance word.
Source: mandate T6(e) ("`Ω = (alphabet)^T` is finite")
Kind: D
Fidelity: exact -/
noncomputable def prodLaw (T : ℕ) (ν : Distr A) : Distr (Fin T → A) where
  mass ω := ∏ i, ν.mass (ω i)
  nonneg ω := prod_nonneg fun i _ => ν.nonneg _
  sum_eq_one := by
    rw [← Fintype.prod_sum]
    simp [ν.sum_eq_one]

/-- The prefix filtration on words: the atom at time `t` fixes the first `t` letters.
Source: mandate T6(e) ("the natural atoms")
Kind: D
Fidelity: exact -/
def prefixAtoms (T : ℕ) : Atoms (Fin T → A) where
  fib t ω := univ.filter (fun ω' => ∀ i : Fin T, (i : ℕ) < t → ω' i = ω i)
  mem_fib t ω := by simp
  fib_eq_of_mem t ω ω' h := by
    simp only [mem_filter, mem_univ, true_and] at h
    ext ω''
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro H i hi; rw [H i hi, h i hi]
    · intro H i hi; rw [H i hi, h i hi]
  fib_succ_subset t ω := by
    intro ω' h
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    exact fun i hi => h i (by omega)

/-- The `i`-th letter of a word read through `v`, `0` beyond the horizon.
Source: mandate T6(e). Kind: D. Fidelity: exact -/
def letter (T : ℕ) (ω : Fin T → A) (v : A → ℝ) (i : ℕ) : ℝ := if h : i < T then v (ω ⟨i, h⟩) else 0

/-- The D9′ trajectory driven by a word. Source: mandate T6(e). Kind: D. Fidelity: exact -/
noncomputable def trajW (η r : ℝ) (s₀ : ℝ × ℝ) (ξv Δv : A → ℝ) (T : ℕ) (ω : Fin T → A) : ℕ → ℝ × ℝ :=
  traj η r s₀ (letter T ω ξv) (letter T ω Δv)

/-- The inside events `I_t = {ω : d_t(ω) < r}`. Source: mandate T6(e). Kind: D. Fidelity: exact -/
noncomputable def insideEvents (η r : ℝ) (s₀ : ℝ × ℝ) (ξv Δv : A → ℝ) (T : ℕ) (t : ℕ) : Finset (Fin T → A) :=
  univ.filter (fun ω => dist (trajW η r s₀ ξv Δv T ω t) < r)

/-- **The basin is a D4 instance at hazard `0`**: over the product law of a horizon-`T` word with the
prefix filtration, the inside events are forward invariant with hazard `0` whenever the alphabet's
disturbances are bounded and `η ξ̄ + σ̄* ≤ η r` (`0 < η < 1`).
Source: [[corr-wf14-inventory]] 119 / approval-final.md S7(a); mandate T6(e)
Kind: L (`step_dist_lt` relabelled through `forwardInvariant_of_pointwise`: the D4 instance at hazard `0`
carries no conditional content — the integrand is identically `0` for every law and filtration; audit r1
N3)
Fidelity: exact
Hyps: (a) only -/
theorem basin_forwardInvariant (η r ξbar σbar : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hξb : 0 ≤ ξbar)
    (hσb : 0 ≤ σbar) (ν : Distr A) (ξv Δv : A → ℝ) (hξ : ∀ a, |ξv a| ≤ ξbar) (hΔ : ∀ a, |Δv a| ≤ σbar)
    (hcond : η * ξbar + σbar ≤ η * r) (s₀ : ℝ × ℝ) (T : ℕ) :
    forwardInvariantWithHazard (prodLaw T ν) (prefixAtoms T) (insideEvents η r s₀ ξv Δv T) (fun _ => 0) := by
  apply forwardInvariant_of_pointwise
  intro t ω hω
  simp only [insideEvents, mem_filter, mem_univ, true_and] at hω ⊢
  unfold trajW at hω ⊢
  simp only [traj]
  refine step_dist_lt η r ξbar σbar hη0 hη1 _ _ _ ?_ ?_ hcond hω
  · unfold letter; split_ifs
    · exact hξ _
    · simpa using hξb
  · unfold letter; split_ifs
    · exact hΔ _
    · simpa using hσb

end Product

end BasinToy

end Cleanroom.Corrigibility.CorrLandscape
