import Cleanroom.Corrigibility.CorrTrajectory.Potential
import Cleanroom.Corrigibility.CorrTrajectory.Grades
import Cleanroom.Corrigibility.CorrTrajectory.Coverage
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Fin.VecNotation

/-!
# `corr-trajectory` — `Basin`: Statement 10, the basin as a forward-invariant family (T9)

* (a) **the basin as a forward-invariant family with hazard** (`Potential.forwardInvariantWithHazard`,
  D4) — a *label* unless the law depends on the state (the contraction theorem is `corr-landscape`'s).
  Non-label N+: a three-state Markov toy (`Fin 3`, one step) with `B = {0, 1}` forward-invariant at
  hazard `1/10` and `B' = {0}` failing at the same `1/10` — the predicate separates sets
  (`markov_B01_invariant`, `markov_B0_not_invariant`). "Stays in the basin" is a safety property
  (`staysIn_safety`, via `Grades.safetyProp_of_isClosed`).
* (c) **the tracking recursion is a definition** (`track`): C9c (`v = r` freezes `d`), the growth
  lower bound of C9a, and the small theorem "summable drift against a divergent rate reaches the
  target" (`track_reaches_zero`); the withdrawn "coverage persists iff `r_t ≥ v_t`" has no object
  to refer to (refuted row in the ledger).
* (d) **two coverages separated** (2-025): action-relative coverage (`Coverage.covered`) and the
  tracking distance `TV(P, δ_{θ*})`: witness 1 has `d = 1/2` with gap `0`; witness 2 has `d = 0`
  with gap `1/2`. Neither implies the other; Open problem 2 stays open.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect
open Filter Topology

namespace Basin

/-! ### (a) the basin as a forward-invariant family; "stays in the basin" is a safety property -/

/-- **"The trajectory stays in the basin"** `∀ t, s t ∈ B t` is a safety property (D2) for a discrete
state type: a closed set in the product topology.
Source: [[corr-wf14-inventory]] 080 / invariant-final.md Statement 10(a)
Kind: L (via `Grades.safetyProp_of_isClosed`)
Fidelity: exact -/
theorem staysIn_safety {S : Type} [TopologicalSpace S] [DiscreteTopology S] (B : ℕ → Set S) :
    Grades.SafetyProp {s : ℕ → S | ∀ t, s t ∈ B t} := by
  apply Grades.safetyProp_of_isClosed
  have : {s : ℕ → S | ∀ t, s t ∈ B t} = ⋂ t, (fun s : ℕ → S => s t) ⁻¹' B t := by
    ext s; simp
  rw [this]
  exact isClosed_iInter fun t => (isClosed_discrete (B t)).preimage (continuous_apply t)

/-- The three-state kernel: from `0` to `(0, 1, 2)` with `(7/10, 1/5, 1/10)`; from `1` with
`(0, 19/20, 1/20)`; `2` absorbing.
Source: mandate T9(a) (the non-label witness)
Kind: D
Fidelity: n/a (witness) -/
noncomputable def kernel : Fin 3 → Fin 3 → ℝ :=
  ![![7 / 10, 1 / 5, 1 / 10], ![0, 19 / 20, 1 / 20], ![0, 0, 1]]

/-- The one-step law on `(s₀, s₁)` with uniform initial state.
Source: mandate T9(a). Kind: D. Fidelity: n/a (witness) -/
noncomputable def markov : Distr (Fin 3 × Fin 3) where
  mass ω := 1 / 3 * kernel ω.1 ω.2
  nonneg ω := by
    rcases ω with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [kernel] <;> norm_num
  sum_eq_one := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, kernel]; norm_num

/-- The filtration: the initial state at time `0`, everything from time `1`.
Source: mandate T9(a). Kind: D. Fidelity: n/a (witness) -/
def markovAtoms : Atoms (Fin 3 × Fin 3) where
  fib t ω := if t = 0 then univ.filter (fun ω' => ω'.1 = ω.1) else {ω}
  mem_fib t ω := by rcases t with _ | t <;> simp
  fib_eq_of_mem t ω ω' h := by
    rcases t with _ | t
    · simp only [if_true, mem_filter, mem_univ, true_and] at h
      simp [h]
    · simp only [Nat.succ_ne_zero, if_false, mem_singleton] at h
      rw [h]
  fib_succ_subset t ω := by
    rcases t with _ | t
    · intro ω' h
      simp only [Nat.succ_ne_zero, if_false, mem_singleton] at h
      simp [h]
    · simp

/-- The family `B_0 = {s₀ ∈ {0, 1}}`, `B_1 = {s₁ ∈ {0, 1}}`, `B_t = univ` after.
Source: mandate T9(a). Kind: D. Fidelity: n/a (witness) -/
def B01 (t : ℕ) : Finset (Fin 3 × Fin 3) :=
  if t = 0 then univ.filter (fun ω => ω.1 ≠ 2) else if t = 1 then univ.filter (fun ω => ω.2 ≠ 2) else univ

/-- The family `B'_0 = {s₀ = 0}`, `B'_1 = {s₁ = 0}`, `B'_t = univ` after.
Source: mandate T9(a). Kind: D. Fidelity: n/a (witness) -/
def B0 (t : ℕ) : Finset (Fin 3 × Fin 3) :=
  if t = 0 then univ.filter (fun ω => ω.1 = 0) else if t = 1 then univ.filter (fun ω => ω.2 = 0) else univ

/-- **N+ (non-label): `{0, 1}` is forward invariant with hazard `1/10`** on the three-state toy — the
hazard from `0` is exactly `1/10`, from `1` it is `1/20`.
Source: [[corr-wf14-inventory]] 080 / invariant-final.md Statement 10(a), D4; mandate T9(a)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem markov_B01_invariant : forwardInvariantWithHazard markov markovAtoms B01 (fun _ => 1 / 10) := by
  intro t ω
  rcases t with _ | _ | t
  · -- time 0: the atom is the initial state
    unfold condSum
    simp only [markovAtoms, if_true]
    rw [sum_filter, sum_filter]
    rcases ω with ⟨a, b⟩
    fin_cases a <;> simp [Fintype.sum_prod_type, Fin.sum_univ_three, markov, kernel, ind, B01] <;> norm_num
  · -- time 1: singleton atoms, `B_2 = univ`
    have hfib : markovAtoms.fib (0 + 1) ω = {ω} := by simp [markovAtoms]
    unfold condSum
    rw [hfib, sum_singleton, sum_singleton]
    dsimp only
    have : ind (B01 (0 + 1 + 1)) ω = 1 := ind_of_mem (by simp [B01])
    rw [this]
    simp only [sub_self, mul_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg (markov.nonneg ω) (ind_nonneg _ _))
  · have hfib : markovAtoms.fib (t + 1 + 1) ω = {ω} := by simp [markovAtoms]
    unfold condSum
    rw [hfib, sum_singleton, sum_singleton]
    dsimp only
    have : ind (B01 (t + 1 + 1 + 1)) ω = 1 := ind_of_mem (by simp [B01])
    rw [this]
    simp only [sub_self, mul_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg (markov.nonneg ω) (ind_nonneg _ _))

/-- **N+ (non-label): `{0}` is *not* forward invariant with hazard `1/10`** on the same toy — from
`0` the exit probability is `3/10`. The predicate separates sets: it is not a label on this law.
Source: [[corr-wf14-inventory]] 080 / invariant-final.md Statement 10(a); mandate T9(a)
Kind: N+ (separation)
Fidelity: exact
Hyps: (a) only -/
theorem markov_B0_not_invariant : ¬ forwardInvariantWithHazard markov markovAtoms B0 (fun _ => 1 / 10) := by
  intro H
  have h := H 0 (0, 0)
  unfold condSum at h
  simp only [markovAtoms, if_true] at h
  rw [sum_filter, sum_filter] at h
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, markov, kernel, ind, B0] at h
  norm_num at h

/-! ### (c) the tracking recursion is a definition -/

/-- **The clamped tracking recursion** `d_{t+1} = max(0, d_t − r_t + v_t)` — a *definition* of `d`
from the rate `r` and the target speed `v`, not a learning model (adversary item 46).
Source: [[corr-wf14-inventory]] 080, 2-025 / invariant-final.md Statement 10(c); checks.py C9
Kind: D
Fidelity: exact -/
noncomputable def track (d₀ : ℝ) (r v : ℕ → ℝ) : ℕ → ℝ
  | 0 => d₀
  | t + 1 => max 0 (track d₀ r v t - r t + v t)

/-- `track_nonneg` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma track_nonneg (d₀ : ℝ) (r v : ℕ → ℝ) (hd : 0 ≤ d₀) (t : ℕ) : 0 ≤ track d₀ r v t := by
  cases t with
  | zero => exact hd
  | succ t => exact le_max_left _ _

/-- **C9c: `v_t = r_t` freezes the distance** at `d₀ ≥ 0`.
Source: [[corr-wf14-inventory]] 2-080 (C9c) / invariant-final.md Statement 10(c)
Kind: L
Fidelity: exact -/
theorem track_const (d₀ : ℝ) (r v : ℕ → ℝ) (hd : 0 ≤ d₀) (hvr : ∀ t, v t = r t) (t : ℕ) :
    track d₀ r v t = d₀ := by
  induction t with
  | zero => rfl
  | succ t ih => simp [track, ih, hvr, hd]

/-- **The unclamped lower bound** `d_T ≥ d₀ + ∑_{t<T} (v_t − r_t)` — C9a's growth statement
`d_T ≥ 1 + T/10 − ∑_{t<T} 1/(t+2)` is this at `d₀ = 1`, `r_t = 1/(t+2)`, `v = 1/10`.
Source: [[corr-wf14-inventory]] 2-080 (C9a) / invariant-final.md Statement 10(c)
Kind: L
Fidelity: exact (no decimal: `94.5` is not a theorem) -/
theorem track_ge (d₀ : ℝ) (r v : ℕ → ℝ) (T : ℕ) :
    d₀ + ∑ t ∈ range T, (v t - r t) ≤ track d₀ r v T := by
  induction T with
  | zero => simp [track]
  | succ T ih =>
    rw [sum_range_succ]
    calc d₀ + (∑ t ∈ range T, (v t - r t) + (v T - r T))
        = (d₀ + ∑ t ∈ range T, (v t - r t)) - r T + v T := by ring
      _ ≤ track d₀ r v T - r T + v T := by linarith
      _ ≤ max 0 (track d₀ r v T - r T + v T) := le_max_right _ _

/-- C9a: against constant drift `1/10` and the decaying rate `1/(t+2)`, from `d₀ = 1`:
`d_T ≥ 1 + T/10 − ∑_{t<T} 1/(t+2)`.
Source: [[corr-wf14-inventory]] 2-080 (C9a). Kind: L. Fidelity: exact -/
theorem c9a_lower (T : ℕ) :
    1 + (T : ℝ) / 10 - ∑ t ∈ range T, 1 / ((t : ℝ) + 2) ≤
      track 1 (fun t => 1 / ((t : ℝ) + 2)) (fun _ => 1 / 10) T := by
  have := track_ge 1 (fun t => 1 / ((t : ℝ) + 2)) (fun _ => 1 / 10) T
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at this
  linarith

/-- Off the clamp the recursion is affine: while `d` stays positive, `d_T = d₀ + ∑_{t<T} (v_t − r_t)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma track_eq_of_pos (d₀ : ℝ) (r v : ℕ → ℝ) (T : ℕ) (hpos : ∀ t ≤ T, 0 < track d₀ r v t) :
    track d₀ r v T = d₀ + ∑ t ∈ range T, (v t - r t) := by
  induction T with
  | zero => simp [track]
  | succ T ih =>
    have ih' := ih fun t ht => hpos t (ht.trans (Nat.le_succ T))
    have hT := hpos (T + 1) le_rfl
    simp only [track] at hT ⊢
    rw [sum_range_succ, ← add_assoc, ← ih']
    rcases le_or_gt 0 (track d₀ r v T - r T + v T) with h | h
    · rw [max_eq_right h]; ring
    · rw [max_eq_left h.le] at hT; exact absurd hT (lt_irrefl 0)

/-- **Summable drift against a divergent tracking rate reaches the target**: with `r, v ≥ 0`,
`∑ v < ∞` and `∑ r = ∞`, some `d_T = 0`.
Source: [[corr-wf14-inventory]] 2-080 (C9b, generalized) / invariant-final.md Statement 10(c) ("summable drift is tracked")
Kind: P (small)
Fidelity: stronger: the general statement behind C9b
Hyps: (a) only -/
theorem track_reaches_zero (d₀ : ℝ) (r v : ℕ → ℝ) (hd : 0 ≤ d₀) (hr : ∀ t, 0 ≤ r t) (hv : ∀ t, 0 ≤ v t)
    (hvs : Summable v) (hrs : ¬ Summable r) : ∃ T, track d₀ r v T = 0 := by
  by_contra H
  have H' : ∀ t, track d₀ r v t ≠ 0 := fun t h => H ⟨t, h⟩
  have hpos : ∀ t, 0 < track d₀ r v t := fun t => lt_of_le_of_ne (track_nonneg d₀ r v hd t) (H' t).symm
  have hdiv : Tendsto (fun n => ∑ t ∈ range n, r t) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hr).1 hrs
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hdiv) (d₀ + ∑' t, v t + 1)
  have hNle := hN N le_rfl
  have heq := track_eq_of_pos d₀ r v N fun t _ => hpos t
  have hvle : ∑ t ∈ range N, v t ≤ ∑' t, v t := hvs.sum_le_tsum (range N) (fun t _ => hv t)
  have : track d₀ r v N ≤ d₀ + ∑' t, v t - ∑ t ∈ range N, r t := by
    rw [heq, sum_sub_distrib]; linarith
  linarith [hpos N]

/-! ### (d) two coverages separated -/

/-- Total variation on a finite type: `TV(P, Q) = ½ ∑ |P − Q|`.
Source: [[corr-wf14-inventory]] 2-025 / invariant-final.md Statement 10(c) (`d_t = dist(P_t ∘ θ⁻¹, θ*_t)`)
Kind: D
Fidelity: exact (the source's `dist` left unspecified; TV chosen) -/
noncomputable def tv {Θ : Type} [Fintype Θ] (P Q : Distr Θ) : ℝ := 1 / 2 * ∑ θ, |P.mass θ - Q.mass θ|

/-- The credence that the action is wrong: `∑_θ P(θ) 1[wrong under θ]`.
Source: invariant-final.md S4(ii). Kind: D. Fidelity: exact -/
noncomputable def credW {Θ : Type} [Fintype Θ] (P : Distr Θ) (wrongOf : Θ → Bool) : ℝ :=
  ∑ θ, P.mass θ * (if wrongOf θ then 1 else 0)

/-- **Witness 1 (2-025)**: the posterior uniform on `{θ₁, θ₂}`, the target `θ₁`, the action wrong
under both: tracking distance `TV = 1/2`, yet calibrated (`η = 0`: credence `1` = objective `1`).
Source: [[corr-wf14-inventory]] 2-025 / invariant-adversary.md item 46; mandate T9(d)
Kind: N+ (separation)
Fidelity: exact
Hyps: (a) only -/
theorem two_coverages_witness1 :
    tv (twoPoint (1 / 2) ⟨by norm_num, by norm_num⟩) (twoPoint 0 ⟨by norm_num, by norm_num⟩) = 1 / 2 ∧
      Coverage.covered 0 (credW (twoPoint (1 / 2) ⟨by norm_num, by norm_num⟩) (fun _ => true))
        (credW (twoPoint 0 ⟨by norm_num, by norm_num⟩) (fun _ => true)) := by
  constructor
  · simp [tv, World.sum_eq] <;> norm_num
  · simp [Coverage.covered, credW, World.sum_eq]

/-- **Witness 2 (2-025)**: the posterior at the target (`TV = 0`), the objective law of the target
uniform, the action wrong exactly under `θ₂`: credence `0` against objective rate `1/2` — gap `1/2`.
Source: [[corr-wf14-inventory]] 2-025 / invariant-adversary.md item 46; mandate T9(d)
Kind: N+ (separation)
Fidelity: exact
Hyps: (a) only -/
theorem two_coverages_witness2 :
    tv (twoPoint 0 ⟨by norm_num, by norm_num⟩) (twoPoint 0 ⟨by norm_num, by norm_num⟩) = 0 ∧
      credW (twoPoint 0 ⟨by norm_num, by norm_num⟩) (fun θ => decide (θ = World.wrong)) = 0 ∧
      credW (twoPoint (1 / 2) ⟨by norm_num, by norm_num⟩) (fun θ => decide (θ = World.wrong)) = 1 / 2 ∧
      ∀ η < (1 / 2 : ℝ), ¬ Coverage.covered η 0 (1 / 2) := by
  refine ⟨by simp [tv], by simp [credW, World.sum_eq], by simp [credW, World.sum_eq] <;> norm_num, ?_⟩
  intro η hη
  unfold Coverage.covered
  rw [not_le, show (0 : ℝ) - 1 / 2 = -(1 / 2) by norm_num, abs_neg, abs_of_pos (by norm_num)]
  exact hη

end Basin

end Cleanroom.Corrigibility.CorrTrajectory
