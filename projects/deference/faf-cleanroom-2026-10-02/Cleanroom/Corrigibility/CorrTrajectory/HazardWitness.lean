import Cleanroom.Corrigibility.CorrTrajectory.Hazard
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `corr-trajectory` — `HazardWitness`: the first-passage process; harmonic (N−) and geometric (N+)

A genuine `ShutdownProc` with conditionally independent hazards `δ_t`: the **first-passage
process** on `Fin (T+1)`, the pushforward of the product law on `Fin T → Bool` ("the first `true`
absorbing") to the entry time, with the point `T` meaning "no catastrophe within the horizon". At
round `t` the filtration knows whether and when entry happened; off `Cat` the atom is "not yet", on
which the hazard is exactly `δ_t` (`firstPassage_hazardLE`: the bound holds with equality for
`t < T`). Survival through `T` is `∏_{t<T} (1 − δ_t)` (`probOf_catBy`).

* C1, **harmonic** `δ_t = 1/(t+2)`: survival `1/(T+1)`, catastrophe by `T` has probability
  `T/(T+1) → 1` while `δ_t → 0` — **a vanishing hazard certifies nothing** (N−: the union bound
  `∑_{t<T} 1/(t+2)` passes `1` at `T = 3`; the certificate is vacuous exactly where catastrophe is
  becoming certain).
* C2, **geometric** `δ_t = Δ 2^{−(t+1)}`: `∑_{t<T} δ_t = Δ(1 − 2^{−T}) ≤ Δ`, `∑' δ_t = Δ`, and
  catastrophe by any `T` has probability `≤ Δ` through `catBy_le_budget` (N+).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect
open Filter Topology

namespace FirstPassage

/-- Survival through `k` rounds: `∏_{s<k} (1 − δ_s)`.
Source: [[corr-wf14-inventory]] 077, 2-024 / invariant-final.md Statement 7(c), C1
Kind: D
Fidelity: exact -/
noncomputable def surv (δ : ℕ → ℝ) (k : ℕ) : ℝ := ∏ s ∈ range k, (1 - δ s)

/-- `surv_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma surv_zero (δ : ℕ → ℝ) : surv δ 0 = 1 := by simp [surv]

/-- `surv_succ` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma surv_succ (δ : ℕ → ℝ) (k : ℕ) : surv δ (k + 1) = surv δ k * (1 - δ k) := by
  simp [surv, prod_range_succ]

/-- `surv_nonneg` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma surv_nonneg (δ : ℕ → ℝ) (hδ : ∀ t, δ t ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) : 0 ≤ surv δ k :=
  prod_nonneg fun s _ => by linarith [(hδ s).2]

/-- The telescoping identity `∑_{k ∈ [t, t+n)} δ_k surv_k + surv_{t+n} = surv_t`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_Ico_add_surv (δ : ℕ → ℝ) (t : ℕ) :
    ∀ n, ∑ k ∈ Ico t (t + n), δ k * surv δ k + surv δ (t + n) = surv δ t := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right t n), surv_succ]
    linarith

/-- `sum_range_add_surv` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_range_add_surv (δ : ℕ → ℝ) (T : ℕ) :
    ∑ k ∈ range T, δ k * surv δ k + surv δ T = 1 := by
  have := sum_Ico_add_surv δ 0 T
  simpa [surv] using this

/-- The mass of the entry time `k` (as a natural): `δ_k surv_k` for `k < T`, and `surv_T` ("never") at `k = T`.
Source: invariant-final.md Statement 7(c) (the product law, pushed to the entry time)
Kind: D
Fidelity: exact -/
noncomputable def massNat (δ : ℕ → ℝ) (T k : ℕ) : ℝ :=
  if k < T then δ k * surv δ k else surv δ T

/-- `massNat_nonneg` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma massNat_nonneg (δ : ℕ → ℝ) (hδ : ∀ t, δ t ∈ Set.Icc (0 : ℝ) 1) (T k : ℕ) : 0 ≤ massNat δ T k := by
  unfold massNat
  split_ifs
  · exact mul_nonneg (hδ _).1 (surv_nonneg δ hδ _)
  · exact surv_nonneg δ hδ _

/-- `sum_range_massNat` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_range_massNat (δ : ℕ → ℝ) (T : ℕ) : ∑ k ∈ range (T + 1), massNat δ T k = 1 := by
  rw [sum_range_succ]
  have h1 : ∑ k ∈ range T, massNat δ T k = ∑ k ∈ range T, δ k * surv δ k :=
    sum_congr rfl fun k hk => by simp [massNat, mem_range.1 hk]
  have h2 : massNat δ T T = surv δ T := by simp [massNat]
  rw [h1, h2, sum_range_add_surv]

/-- The sum of the masses over `{k ∣ t ≤ k ≤ T}` is `surv_t`: the mass of "not yet by `t`".
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_Ico_massNat (δ : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) :
    ∑ k ∈ Ico t (T + 1), massNat δ T k = surv δ t := by
  rw [Finset.sum_Ico_succ_top ht]
  have h1 : ∑ k ∈ Ico t T, massNat δ T k = ∑ k ∈ Ico t T, δ k * surv δ k :=
    sum_congr rfl fun k hk => by simp [massNat, (mem_Ico.1 hk).2]
  have h2 : massNat δ T T = surv δ T := by simp [massNat]
  rw [h1, h2]
  have := sum_Ico_add_surv δ t (T - t)
  rwa [Nat.add_sub_cancel' ht] at this

/-- **The entry-time law** as a FAF `Distr` on `Fin (T+1)`.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(c), C1
Kind: D
Fidelity: exact -/
noncomputable def law (δ : ℕ → ℝ) (hδ : ∀ t, δ t ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) : Distr (Fin (T + 1)) where
  mass k := massNat δ T k.val
  nonneg k := massNat_nonneg δ hδ T k.val
  sum_eq_one := by
    rw [Fin.sum_univ_eq_sum_range (fun k => massNat δ T k) (T + 1)]
    exact sum_range_massNat δ T

/-- The filtration of the entry-time process: at round `t` the atom of a point that has entered
(`ω < t`) is the singleton, and the atom of "not yet" is `{ω' ∣ t ≤ ω'}`.
Source: invariant-final.md S1 (`𝓕_t` the observable history) on the entry-time process
Kind: D
Fidelity: exact -/
def atoms (T : ℕ) : Atoms (Fin (T + 1)) where
  fib t ω := if ω.val < t then {ω} else univ.filter fun ω' => t ≤ ω'.val
  mem_fib t ω := by
    by_cases h : ω.val < t
    · simp [h]
    · simp only [h, if_false, mem_filter, mem_univ, true_and]; omega
  fib_eq_of_mem t ω ω' h := by
    by_cases h1 : ω.val < t
    · rw [if_pos h1] at h
      rw [mem_singleton.1 h]
    · rw [if_neg h1, mem_filter] at h
      have h2 : ¬ ω'.val < t := by omega
      simp [h1, h2]
  fib_succ_subset t ω := by
    by_cases h1 : ω.val < t
    · have h2 : ω.val < t + 1 := Nat.lt_succ_of_lt h1
      simp [h1, h2]
    · by_cases h2 : ω.val < t + 1
      · rw [if_pos h2, if_neg h1]
        intro ω' hω'
        rw [mem_singleton.1 hω']
        simp only [mem_filter, mem_univ, true_and]; omega
      · rw [if_neg h2, if_neg h1]
        intro ω' hω'
        simp only [mem_filter, mem_univ, true_and] at hω' ⊢; omega

/-- **The first-passage process**: the entry-time law with `Cat_t = {ω < t}` (and `ω = T` never
enters), trivial round observables (no stakes), press never, compliance always.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(c) ("conditionally independent hazards")
Kind: D
Fidelity: exact (the product law's pushforward to the entry time) -/
noncomputable def proc (δ : ℕ → ℝ) (hδ : ∀ t, δ t ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    ShutdownProc (Fin (T + 1)) Unit where
  μ := law δ hδ T
  F := atoms T
  Fpre := atoms T
  post_subset_pre _ _ := subset_rfl
  pre_succ_subset_post t ω := (atoms T).fib_succ_subset t ω
  wrong _ _ := false
  mag _ _ := ()
  hOf _ := 0
  cOf _ := 0
  hOf_nonneg _ := le_rfl
  cOf_nonneg _ := le_rfl
  pressed _ _ := false
  pressed_meas _ _ _ _ := rfl
  kappa _ _ := true
  kappa_meas _ _ _ _ := rfl
  irr _ _ := false
  cat t ω := decide (ω.val < t ∧ ω.val < T)
  cat_absorbing t ω _ h := by
    simp only [decide_eq_true_eq] at h ⊢; omega

/-- `proc_cat` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma proc_cat (δ : ℕ → ℝ) (hδ) (T t : ℕ) (ω : Fin (T + 1)) :
    (proc δ hδ T).cat t ω = decide (ω.val < t ∧ ω.val < T) := rfl

/-- `proc_mass` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma proc_mass (δ : ℕ → ℝ) (hδ) (T : ℕ) (ω : Fin (T + 1)) :
    (proc δ hδ T).μ.mass ω = massNat δ T ω.val := rfl

/-- `Cat_t` is `𝓕_t`-measurable on the first-passage process.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma proc_cat_meas (δ : ℕ → ℝ) (hδ) (T t : ℕ) :
    (proc δ hδ T).F.Meas t (indB ((proc δ hδ T).cat t)) := by
  intro ω ω' h
  show (if (proc δ hδ T).cat t ω' then (1 : ℝ) else 0) = if (proc δ hδ T).cat t ω then 1 else 0
  simp only [proc_cat, decide_eq_true_eq]
  change ω' ∈ (atoms T).fib t ω at h
  by_cases h1 : ω.val < t
  · simp only [atoms, if_pos h1] at h
    rw [mem_singleton.1 h]
  · simp only [atoms, if_neg h1, mem_filter, mem_univ, true_and] at h
    have h2 : ¬ ω'.val < t := by omega
    simp [h1, h2]

/-- **The hazard of the first-passage process is exactly `δ_t`** off `Cat`: `hazardLE δ t` holds
at every `t`, with equality on the "not yet" atom for `t < T`.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(c) ("conditionally independent hazards `δ_t`")
Kind: P (small: the telescoping identity on the "not yet" atom)
Fidelity: exact
Hyps: (a) only -/
theorem proc_hazardLE (δ : ℕ → ℝ) (hδ : ∀ t, δ t ∈ Set.Icc (0 : ℝ) 1) (T t : ℕ) :
    (proc δ hδ T).hazardLE δ t := by
  intro ω
  by_cases h1 : ω.val < t
  · -- already entered (or the never-point past `t`): the atom is `{ω}` and `1 − 𝟙[Cat_t]` kills both sides
    have hfib : (proc δ hδ T).F.fib t ω = {ω} := by simp [proc, atoms, h1]
    simp only [condSum, hfib, sum_singleton]
    by_cases hT : ω.val < T
    · have hc : (proc δ hδ T).cat t ω = true := by simp [proc_cat, h1, hT]
      simp [indB, hc]
    · -- the never-point: `Cat` is never entered
      have hc : (proc δ hδ T).cat (t + 1) ω = false := by simp [proc_cat, hT]
      have h0 : 0 ≤ δ t * ((proc δ hδ T).μ.mass ω * (1 - indB ((proc δ hδ T).cat t) ω)) :=
        mul_nonneg (hδ t).1 (mul_nonneg ((proc δ hδ T).μ.nonneg ω)
          (by linarith [indB_le_one ((proc δ hδ T).cat t) ω]))
      simp only [indB_false hc, mul_zero]
      exact h0
  · -- not yet: the atom is `{ω' ∣ t ≤ ω'}`
    have ht : t ≤ T := by omega
    have hfib : (proc δ hδ T).F.fib t ω = univ.filter fun ω' : Fin (T + 1) => t ≤ ω'.val := by
      simp [proc, atoms, h1]
    simp only [condSum, hfib]
    -- on the atom `Cat_t` is false and `Cat_{t+1}` is `ω' = t ∧ t < T`
    have hL : ∑ ω' ∈ univ.filter (fun ω' : Fin (T + 1) => t ≤ ω'.val),
        (proc δ hδ T).μ.mass ω' * ((1 - indB ((proc δ hδ T).cat t) ω') * indB ((proc δ hδ T).cat (t + 1)) ω') =
        if t < T then δ t * surv δ t else 0 := by
      rw [sum_filter]
      simp only [proc_mass, proc_cat, indB, decide_eq_true_eq]
      refine (Fin.sum_univ_eq_sum_range (fun k : ℕ => if t ≤ k then massNat δ T k *
        ((1 - (if k < t ∧ k < T then (1 : ℝ) else 0)) *
          (if k < t + 1 ∧ k < T then (1 : ℝ) else 0)) else 0) (T + 1)).trans ?_
      rw [Finset.sum_eq_single t]
      · by_cases hT : t < T
        · simp [massNat, hT]
        · simp [hT]
      · intro k _ hk
        by_cases hk1 : t ≤ k
        · have h2 : ¬ (k < t + 1 ∧ k < T) := by omega
          rw [if_pos hk1, if_neg h2]; ring
        · simp [hk1]
      · intro h; exact absurd (mem_range.2 (Nat.lt_succ_of_le ht)) h
    have hR : ∑ ω' ∈ univ.filter (fun ω' : Fin (T + 1) => t ≤ ω'.val),
        (proc δ hδ T).μ.mass ω' * (1 - indB ((proc δ hδ T).cat t) ω') = surv δ t := by
      rw [sum_filter]
      simp only [proc_mass, proc_cat, indB, decide_eq_true_eq]
      refine (Fin.sum_univ_eq_sum_range (fun k : ℕ => if t ≤ k then massNat δ T k *
        (1 - (if k < t ∧ k < T then (1 : ℝ) else 0)) else 0) (T + 1)).trans ?_
      have : ∀ k ∈ range (T + 1), (if t ≤ k then massNat δ T k *
          (1 - (if k < t ∧ k < T then (1 : ℝ) else 0)) else 0) = if t ≤ k then massNat δ T k else 0 := by
        intro k _
        by_cases hk1 : t ≤ k
        · have : ¬ (k < t ∧ k < T) := by omega
          simp [hk1, this]
        · simp [hk1]
      rw [sum_congr rfl this, ← sum_filter]
      have hf : (range (T + 1)).filter (fun k => t ≤ k) = Ico t (T + 1) := by
        ext k; simp only [mem_filter, mem_range, mem_Ico]; omega
      rw [hf, sum_Ico_massNat δ T t ht]
    rw [hL, hR]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hδ t).1 (surv_nonneg δ hδ t)

/-- **Survival**: catastrophe by `T` has probability `1 − ∏_{t<T} (1 − δ_t)`.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(c), C1
Kind: L (a sum identity; relabelled from P, audit r2 fidelity N9)
Fidelity: exact
Hyps: (a) only -/
theorem probOf_catBy (δ : ℕ → ℝ) (hδ : ∀ t, δ t ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    probOf (proc δ hδ T).μ ((proc δ hδ T).catBy T) = 1 - surv δ T := by
  have hset : (proc δ hδ T).catBy T = univ.filter fun ω : Fin (T + 1) => ω.val < T := by
    ext ω
    simp only [ShutdownProc.catBy, ShutdownProc.catAt, mem_biUnion, mem_range, mem_filter, mem_univ,
      true_and, proc_cat, decide_eq_true_eq]
    constructor
    · rintro ⟨t, -, -, h⟩; exact h
    · intro h; exact ⟨T, Nat.lt_succ_self T, h, h⟩
  rw [hset, probOf, sum_filter]
  simp only [proc_mass]
  refine (Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < T then massNat δ T k else 0) (T + 1)).trans ?_
  rw [← sum_filter]
  have hf : (range (T + 1)).filter (fun k => k < T) = range T := by
    ext k; simp only [mem_filter, mem_range]; omega
  rw [hf]
  have h1 : ∑ k ∈ range T, massNat δ T k = ∑ k ∈ range T, δ k * surv δ k :=
    sum_congr rfl fun k hk => by simp [massNat, mem_range.1 hk]
  rw [h1]
  linarith [sum_range_add_surv δ T]

/-- `Cat_0 = ∅` on the first-passage process. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma catAt_zero (δ : ℕ → ℝ) (hδ) (T : ℕ) : probOf (proc δ hδ T).μ ((proc δ hδ T).catAt 0) = 0 := by
  have : (proc δ hδ T).catAt 0 = ∅ := by
    ext ω; simp [ShutdownProc.catAt, proc_cat]
  rw [this]; simp [probOf]

/-! ### C1: the harmonic hazard (N−) -/

/-- The harmonic schedule `δ_t = 1/(t+2)`. Source: invariant-final.md Statement 7(c), C1. Kind: D. Fidelity: exact -/
noncomputable def harmonic (t : ℕ) : ℝ := 1 / ((t : ℝ) + 2)

/-- `harmonic_mem` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma harmonic_mem (t : ℕ) : harmonic t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold harmonic
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]

/-- `∏_{t<T} (1 − 1/(t+2)) = 1/(T+1)` (C1, by induction).
Source: [[corr-wf14-inventory]] 2-024 / invariant-final.md Statement 7(c), C1
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem surv_harmonic (T : ℕ) : surv harmonic T = 1 / ((T : ℝ) + 1) := by
  induction T with
  | zero => simp [surv]
  | succ T ih =>
    rw [surv_succ, ih]
    unfold harmonic
    push_cast
    field_simp
    ring

/-- **C1, "a vanishing hazard certifies nothing" (N−).** On the harmonic first-passage process the
hazard schedule tends to `0`, catastrophe by `T` has probability `T/(T+1)`, which tends to `1`, and
the per-round certificate `∑_{t<T} δ̄_t` already exceeds `1` at `T = 3` (`13/12`): the bound is
vacuous exactly as catastrophe becomes certain.
Source: [[corr-wf14-inventory]] 077, 2-024 / invariant-final.md Statement 7(c), C1
Kind: N−
Fidelity: exact
Hyps: (a) only -/
theorem harmonic_certifies_nothing :
    Tendsto harmonic atTop (𝓝 0) ∧
      (∀ T, probOf (proc harmonic harmonic_mem T).μ ((proc harmonic harmonic_mem T).catBy T) =
        (T : ℝ) / ((T : ℝ) + 1)) ∧
      Tendsto (fun T : ℕ => (T : ℝ) / ((T : ℝ) + 1)) atTop (𝓝 1) ∧
      (1 : ℝ) < ∑ t ∈ range 3, harmonic t := by
  refine ⟨?_, fun T => ?_, ?_, ?_⟩
  · have h : harmonic = fun t : ℕ => 1 / (((t + 1 : ℕ) : ℝ) + 1) := by
      funext t; unfold harmonic; push_cast; ring
    rw [h]
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  · rw [probOf_catBy, surv_harmonic]
    field_simp
    ring
  · have h : (fun T : ℕ => (T : ℝ) / ((T : ℝ) + 1)) = fun T : ℕ => 1 - 1 / ((T : ℝ) + 1) := by
      funext T; field_simp; ring
    rw [h]
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_sub (1 : ℝ)
    simpa using this
  · simp [sum_range_succ, harmonic]; norm_num

/-! ### C2: the geometric hazard (N+) -/

/-- The geometric schedule `δ_t = Δ 2^{−(t+1)}`. Source: invariant-final.md Statement 7(c), C2. Kind: D. Fidelity: exact -/
noncomputable def geometric (Δ : ℝ) (t : ℕ) : ℝ := Δ * (1 / 2 : ℝ) ^ (t + 1)

/-- `geometric_mem` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma geometric_mem (Δ : ℝ) (hΔ : Δ ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) : geometric Δ t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold geometric
  have hp : (1 / 2 : ℝ) ^ (t + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp0 : 0 ≤ (1 / 2 : ℝ) ^ (t + 1) := by positivity
  constructor
  · exact mul_nonneg hΔ.1 hp0
  · calc Δ * (1 / 2 : ℝ) ^ (t + 1) ≤ 1 * 1 := mul_le_mul hΔ.2 hp hp0 zero_le_one
      _ = 1 := one_mul 1

/-- `∑_{t<T} Δ 2^{−(t+1)} = Δ (1 − 2^{−T})`. Source: invariant-final.md C2. Kind: L. Fidelity: exact -/
theorem sum_geometric (Δ : ℝ) (T : ℕ) : ∑ t ∈ range T, geometric Δ t = Δ * (1 - (1 / 2 : ℝ) ^ T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih]
    unfold geometric
    ring

/-- `∑' Δ 2^{−(t+1)} = Δ` (`tsum_geometric_two`). Source: invariant-final.md C2. Kind: L. Fidelity: exact -/
theorem tsum_geometric (Δ : ℝ) : ∑' t, geometric Δ t = Δ := by
  have h : geometric Δ = fun t => (Δ / 2) * (1 / 2 : ℝ) ^ t := by
    funext t; unfold geometric; rw [pow_succ]; ring
  rw [h, tsum_mul_left, tsum_geometric_two]
  ring

/-- **C2, the geometric hazard (N+).** On the geometric first-passage process with budget `Δ ∈ [0, 1]`,
catastrophe by any `T` has probability `≤ ∑_{t<T} δ_t = Δ(1 − 2^{−T}) ≤ Δ`, with the hazard bound
discharged *through* `catBy_le_budget` (the per-round certificate), and the exact value
`1 − ∏(1 − δ_t)` below it.
Source: [[corr-wf14-inventory]] 077, 2-024 / invariant-final.md Statement 7(c), C2
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem geometric_budget (Δ : ℝ) (hΔ : Δ ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    probOf (proc (geometric Δ) (geometric_mem Δ hΔ) T).μ
        ((proc (geometric Δ) (geometric_mem Δ hΔ) T).catBy T) ≤ Δ * (1 - (1 / 2 : ℝ) ^ T) ∧
      Δ * (1 - (1 / 2 : ℝ) ^ T) ≤ Δ := by
  constructor
  · have h := (proc (geometric Δ) (geometric_mem Δ hΔ) T).catBy_le_budget (geometric Δ) T
      (fun t _ => proc_hazardLE _ _ T t) (fun t _ => (geometric_mem Δ hΔ t).1)
    rw [catAt_zero, zero_add, sum_geometric] at h
    exact h
  · have hp0 : 0 ≤ (1 / 2 : ℝ) ^ T := by positivity
    nlinarith [hΔ.1]

/-- The geometric witness at `Δ = 1/10`, `T = 20`: catastrophe by `20` has probability at most `1/10`.
Source: invariant-final.md C2 ("union bound `0.1` … at `T = 20`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem geometric_tenth (hΔ : (1 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    probOf (proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).μ
      ((proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).catBy 20) ≤ 1 / 10 := by
  have h := geometric_budget (1 / 10) hΔ 20
  exact h.1.trans h.2

/-- `geometric_summable` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma geometric_summable (Δ : ℝ) : Summable (geometric Δ) := by
  have h : geometric Δ = fun t => (Δ / 2) * (1 / 2 : ℝ) ^ t := by
    funext t; unfold geometric; rw [pow_succ]; ring
  rw [h]
  exact summable_geometric_two.mul_left (Δ / 2)

/-- **C2 through the barrier certificate (N+; audit r1, fidelity N2 / adversarial N7).** On the geometric
first-passage process at `Δ = 1/10`, `T = 20`, the budget potential `budgetPotInf` is a D5 barrier
(`budgetPotInf_isBarrier`, whose hypotheses `Summable`, `0 ≤ δ̄`, the hazard bound and the measurability of
`Cat_t` are all discharged on the process), `catBy_le_tsum` gives the `n`-uniform `P*(Cat by n) ≤ ∑' δ = 1/10`
for every `n`, and the finite-tail Ville route `catBy_le_budgetPot` gives `P*(Cat by 20) ≤ (1/10)(1 − 2^{−20})` —
the Ville/`barrier_bound` routes, which `geometric_budget` (the per-round route) does not take.
Source: [[corr-wf14-inventory]] 077, 2-024 / invariant-final.md Statement 7(b)–(c), C2
Kind: N+ (witness of `budgetPotInf_isBarrier`, `catBy_le_tsum`, `budgetPot_steps`/`catBy_le_budgetPot`, and through `barrier_bound`/`ville_finite`)
Fidelity: exact
Hyps: (a) only -/
theorem geometric_barrier (hΔ : (1 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    IsBarrier (proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).μ
        (proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).F
        (proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).cat
        ((proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).budgetPotInf (geometric (1 / 10))) ∧
      (∀ n, probOf (proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).μ
        ((proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).catBy n) ≤ 1 / 10) ∧
      probOf (proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).μ
        ((proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).catBy 20) ≤ 1 / 10 * (1 - (1 / 2 : ℝ) ^ 20) := by
  refine ⟨?_, fun n => ?_, ?_⟩
  · exact (proc _ _ 20).budgetPotInf_isBarrier (geometric (1 / 10)) (geometric_summable _)
      (fun t => (geometric_mem _ hΔ t).1) (fun t => proc_hazardLE _ _ 20 t) (fun t => proc_cat_meas _ _ 20 t)
  · have h := (proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).catBy_le_tsum (geometric (1 / 10))
      (geometric_summable _) (fun t => (geometric_mem _ hΔ t).1)
      (fun t => proc_hazardLE (geometric (1 / 10)) (geometric_mem _ hΔ) 20 t)
      (fun t => proc_cat_meas (geometric (1 / 10)) (geometric_mem _ hΔ) 20 t) n
    rw [catAt_zero, tsum_geometric, zero_add] at h
    exact h
  · have h := (proc (geometric (1 / 10)) (geometric_mem _ hΔ) 20).catBy_le_budgetPot (geometric (1 / 10)) 20
      (fun t _ => proc_hazardLE (geometric (1 / 10)) (geometric_mem _ hΔ) 20 t)
      (fun t => (geometric_mem _ hΔ t).1)
      (fun t => proc_cat_meas (geometric (1 / 10)) (geometric_mem _ hΔ) 20 t)
    rw [catAt_zero, zero_add, sum_geometric] at h
    exact h

end FirstPassage

/-! ### `Factor`: an instance of `hazard_factorization` with the factor `< 1`

Audit r1 (adversarial N8) and r2 (adversarial N5): the hypotheses of `hazard_factorization` are
trivially satisfiable (`cat (t+1) ≡ false`), so no witness was forced; this one shows the bound is
ever *active*. One round on `World × Bool` (wrongness, press): `ε = 1/10`, the press rate on wrong
proposals `β = 1/2`, right proposals never pressed, `κ = 1`, `Irr ≡ true`, and `Cat₁ = W ∧ ¬Pr`
(a wrong executed proposal is the catastrophe). Then `P*(Cat₁) = 1/20 = (1 − 1/2) · 1/10`: the
factorization holds with equality and the factor `1 − β^min κ = 1/2 < 1`. -/

namespace Factor

/-- The one-round law: `P(W) = 1/10`; given `W` the press is `Bern(1/2)`; given `¬W` no press.
Source: invariant-final.md S2 step 3 (one round); audit r2 (adversarial N5). Kind: D. Fidelity: exact -/
noncomputable def law : Distr (World × Bool) where
  mass ω := if ω.1 = .wrong then 1 / 20 else if ω.2 then 0 else 9 / 10
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type, World.sum_eq]; norm_num

/-- `𝓕_t^-`: trivial at `0`, discrete after. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def pre : Atoms (World × Bool) where
  fib t ω := if t = 0 then univ else {ω}
  mem_fib t ω := by rcases t with _ | t <;> simp
  fib_eq_of_mem t ω ω' h := by
    rcases t with _ | t
    · rfl
    · simp at h; rw [h]
  fib_succ_subset t ω := by rcases t with _ | t <;> simp

/-- **The one-round process with an endogenous catastrophe**: `Cat₁ = W₀ ∧ ¬Pr₀` (absorbing after),
`Irr ≡ true`, compliance `κ ≡ 1`.
Source: invariant-final.md S2 (`Irr`, `Cat`), Statement 7(d); audit r2 (adversarial N5)
Kind: D
Fidelity: exact (one round) -/
noncomputable def proc : ShutdownProc (World × Bool) Unit where
  μ := law
  F := Atoms.discrete
  Fpre := pre
  post_subset_pre t ω := by rcases t with _ | t <;> simp [Atoms.discrete, pre]
  pre_succ_subset_post t ω := by rcases t with _ | t <;> simp [Atoms.discrete, pre]
  wrong _ ω := decide (ω.1 = .wrong)
  mag _ _ := ()
  hOf _ := 1
  cOf _ := 0
  hOf_nonneg _ := zero_le_one
  cOf_nonneg _ := le_rfl
  pressed _ ω := ω.2
  pressed_meas _ := Atoms.meas_discrete _ _
  kappa _ _ := true
  kappa_meas _ _ _ _ := rfl
  irr _ _ := true
  cat t ω := if t = 0 then false else (decide (ω.1 = .wrong) && !ω.2)
  cat_absorbing t ω _ h := by
    rcases t with _ | t
    · simp at h
    · simpa using h

/-- `proc_μ` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma proc_μ : proc.μ = law := rfl

/-- `condSum_zero` (supporting lemma): the round-`0` pre-press atom is everything.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condSum_zero (X : World × Bool → ℝ) (ω : World × Bool) :
    condSum proc.μ proc.Fpre 0 X ω = ∑ ω', law.mass ω' * X ω' := by
  have hfib : proc.Fpre.fib 0 ω = univ := rfl
  unfold condSum
  rw [hfib]
  rfl

/-- The `Irr` inclusion on the process: on the support, `Cat₁ ⊆ Irr₀ ∧ W₀ ∧ executed₀`.
Source: invariant-final.md S2 (`Irr`); audit r2 (adversarial N5). Kind: L. Fidelity: exact -/
lemma irr_inclusion : ∀ ω', 0 < proc.μ.mass ω' → proc.cat 1 ω' = true →
    proc.irr 0 ω' = true ∧ proc.wrong 0 ω' = true ∧ proc.executed 0 ω' = true := by
  rintro ⟨w, p⟩ _ h
  cases w <;> cases p <;> simp [proc, ShutdownProc.executed] at h ⊢

/-- `(βmin)` on the `Irr ∧ W` event at `β^min = 1/2`.
Source: invariant-final.md Statement 7(d); audit r2 (adversarial N5). Kind: L. Fidelity: exact -/
lemma detection_half (ω : World × Bool) :
    (1 / 2 : ℝ) * condSum proc.μ proc.Fpre 0 (fun ω' => indB (proc.irr 0) ω' * indB (proc.wrong 0) ω') ω ≤
      condSum proc.μ proc.Fpre 0
        (fun ω' => indB (proc.irr 0) ω' * indB (proc.wrong 0) ω' * indB (proc.pressed 0) ω') ω := by
  rw [condSum_zero, condSum_zero]
  simp [Fintype.sum_prod_type, proc, law, indB]

/-- **`hazard_factorization` with the factor `1/2 < 1`, active** (audit r1 N8 / r2 N5): on the
one-round process, `P*(Cat₁) = 1/20`, `P*(Irr₀ ∧ W₀) = 1/10`, the `Irr` inclusion and `(βmin)` at
`1/2` are discharged, the theorem gives `P*(Cat₁) ≤ (1 − (1/2) κ₀) · P*(Irr₀ ∧ W₀)`, and the two
sides are equal: `1/20 = (1/2) · (1/10)`.
Source: [[corr-wf14-inventory]] 077 / invariant-final.md Statement 7(d); audit r2 (adversarial N5)
Kind: N+ (witness of `hazard_factorization`; the factor is strictly below `1` and the bound is tight)
Fidelity: exact
Hyps: (a) only -/
theorem instance_half (ω : World × Bool) :
    condSum proc.μ proc.Fpre 0 (indB (proc.cat 1)) ω = 1 / 20 ∧
      condSum proc.μ proc.Fpre 0 (fun ω' => indB (proc.irr 0) ω' * indB (proc.wrong 0) ω') ω = 1 / 10 ∧
      condSum proc.μ proc.Fpre 0 (indB (proc.cat 1)) ω ≤
        (1 - (1 / 2 : ℝ) * indB (proc.kappa 0) ω) *
          condSum proc.μ proc.Fpre 0 (fun ω' => indB (proc.irr 0) ω' * indB (proc.wrong 0) ω') ω ∧
      (1 - (1 / 2 : ℝ) * indB (proc.kappa 0) ω) = 1 / 2 := by
  refine ⟨?_, ?_, proc.hazard_factorization 0 (fun _ => 1 / 2) ω irr_inclusion (detection_half ω), ?_⟩
  · rw [condSum_zero]
    simp [Fintype.sum_prod_type, proc, law, indB]
  · rw [condSum_zero]
    simp [Fintype.sum_prod_type, proc, law, indB]; norm_num
  · simp [proc, indB]; norm_num

end Factor

end Cleanroom.Corrigibility.CorrTrajectory
