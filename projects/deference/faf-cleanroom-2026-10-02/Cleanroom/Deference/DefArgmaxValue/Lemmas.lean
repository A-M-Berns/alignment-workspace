import Cleanroom.Deference.DefArgmaxValue.Calc

/-!
# `def-argmax-value` · Lemmas: the definitional lemmas around H3 (target 5)

Real sequences and finite frames only (no FAF object beyond `ctsInd`):

* **5a** `perIndex_iff_sequence` (2-020): over a finite index set, "for every fixed `j`, along the
  days with `ε ≤ mass_j`" and "for every index sequence `js`, along the days with
  `ε ≤ mass_{js n}`" are equivalent — a finite union of convergent pieces; "generable" enters
  nowhere. Strictly stronger only if `k` grew with `n`.
* **5b** `sharp_iff_ramp` (2-021(b)): the sharp mass-threshold form and the ramp form are
  equivalent under full quantification over `ε, δ` (bounded `g`). 2-021(a) — the sharp
  threshold set is a discontinuous functional — is `def-lattice`'s `no_generable_hard_indicator`
  (cited, findings).
* **5c** `massWeighted_eq_denomFree_of_ne_zero`, `massWeighted_junk` (2-022): the mass-weighted
  (conditional) form equals the denominator-free form exactly when every mass is nonzero; at a
  zero mass Lean's `x / 0 = 0` makes the conditional form `0` while the denominator-free form is
  not — which is why `CondStableOn` divides nowhere.
* **5d** `cancellation_admitted` (2-024): masses `½, ½` with per-index gaps `+1, −1`: the aggregate
  is `0` (the one-sided aggregate inequality holds) while the per-index conditions fail.
* **5e** the test-case sums (2-023): Death in Damascus as the probe at `s = ½` (`−¼`), as the
  symmetric punishing menu at masses `½` (`−½`), and the clairvoyant/adversarial tie-break pair
  (`+½` admitted, `−½` excluded) as finite arithmetic.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology

noncomputable section

/-! ## 5a — sequence vs per-index -/

/-- **Per-index and index-sequence forms agree over a finite index set** (2-020): the per-index
form ("for each `j`, `gap_j → 0` along the days with `ε ≤ mass_j`") is equivalent to the
sequence form ("for every index sequence `js`, `gap_{js n} → 0` along the days with
`ε ≤ mass_{js n}`"). The pieces `{n | js n = j}` are sets; nothing about generability enters.
Source: 2-020; mandate target 5a
Kind: P
Fidelity: exact (strictly stronger only if the index set grew with `n`)
Hyps: (a) -/
theorem perIndex_iff_sequence {k : ℕ} (mass gap : ℕ → Fin (k + 1) → ℝ) (ε : ℝ) :
    (∀ j, Tendsto (fun n => gap n j) (atTop ⊓ 𝓟 {n | ε ≤ mass n j}) (𝓝 0)) ↔
      (∀ js : ℕ → Fin (k + 1),
        Tendsto (fun n => gap n (js n)) (atTop ⊓ 𝓟 {n | ε ≤ mass n (js n)}) (𝓝 0)) := by
  constructor
  · intro h js
    rw [Metric.tendsto_nhds]
    intro η hη
    rw [Filter.eventually_inf_principal]
    have hall : ∀ j, ∀ᶠ n in atTop, ε ≤ mass n j → dist (gap n j) 0 < η := fun j => by
      have := (Metric.tendsto_nhds.1 (h j)) η hη
      rwa [Filter.eventually_inf_principal] at this
    rw [← Filter.eventually_all] at hall
    exact hall.mono (fun n hn hm => hn (js n) hm)
  · intro h j
    exact h (fun _ => j)

/-! ## 5b — ramp ≡ sharp -/

/-- **Sharp and ramp forms are equivalent under full quantification** (2-021(b)), for bounded
`g`: `(∀ ε > 0, g → 0 along {ε ≤ m})` iff `(∀ ε > 0, ∀ δ > 0, Ind_δ(m > ε) · g → 0)`. Forward:
`Ind_δ(m > ε) ≤ 1[ε ≤ m]`. Backward: on `{ε ≤ m}` the ramp at `ε/2` with width `ε/2` is `1`.
Source: 2-021(b); mandate target 5b
Kind: L
Fidelity: exact
Hyps: (a); `g` bounded -/
theorem sharp_iff_ramp (g m : ℕ → ℝ) {B : ℝ} (hg : ∀ n, |g n| ≤ B) :
    (∀ ε : ℚ, 0 < ε → Tendsto g (atTop ⊓ 𝓟 {n | (ε : ℝ) ≤ m n}) (𝓝 0)) ↔
      (∀ ε δ : ℚ, 0 < ε → 0 < δ → Tendsto (fun n => ctsInd δ (m n) ε * g n) atTop (𝓝 0)) := by
  constructor
  · intro h ε δ hε hδ
    rw [Metric.tendsto_nhds]
    intro η hη
    have hs := (Metric.tendsto_nhds.1 (h ε hε)) η hη
    rw [Filter.eventually_inf_principal] at hs
    filter_upwards [hs] with n hn
    by_cases hc : (ε : ℝ) ≤ m n
    · have := hn hc
      rw [Real.dist_eq, sub_zero] at this ⊢
      rw [abs_mul]
      calc |ctsInd δ (m n) ε| * |g n| ≤ 1 * |g n| :=
            mul_le_mul_of_nonneg_right (by
              rw [abs_of_nonneg (ctsInd_mem_Icc _ _ _).1]; exact (ctsInd_mem_Icc _ _ _).2)
              (abs_nonneg _)
        _ < η := by rw [one_mul]; exact this
    · push Not at hc
      rw [ctsInd_eq_zero_of_le hδ hc.le, zero_mul]
      simpa using hη
  · intro h ε hε
    rw [Metric.tendsto_nhds]
    intro η hη
    rw [Filter.eventually_inf_principal]
    have hr := (Metric.tendsto_nhds.1 (h (ε / 2) (ε / 2) (by positivity) (by positivity))) η hη
    filter_upwards [hr] with n hn hm
    have hone : ctsInd (ε / 2) (m n) ((ε / 2 : ℚ) : ℝ) = 1 := by
      apply ctsInd_eq_one_of_le_sub _ _ _ (by positivity)
      push_cast
      linarith
    rw [hone, one_mul] at hn
    exact hn

/-! ## 5c — mass-weighted ⟺ denominator-free, and the junk value -/

/-- **The conditional form equals the denominator-free form when every mass is nonzero**
(2-022): `Σ_j mass_j (q_j / mass_j − m_j) = Σ_j q_j − Σ_j mass_j m_j`.
Source: 2-022; [[total-trust-implies-value]] §Hypotheses ("each leading product cancels its own
denominator")
Kind: L
Fidelity: exact
Hyps: (a); every mass nonzero -/
theorem massWeighted_eq_denomFree_of_ne_zero {k : ℕ} (mass q m : Fin (k + 1) → ℝ)
    (h : ∀ j, mass j ≠ 0) :
    ∑ j, mass j * (q j / mass j - m j) = ∑ j, q j - ∑ j, mass j * m j := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_sub, mul_div_cancel₀ _ (h j)]

/-- **The junk value** (2-022): at a zero mass with nonzero numerator, Lean's `x / 0 = 0` makes the
conditional form `0` while the denominator-free form is `1` — the reason `CondStableOn` divides
nowhere.
Source: 2-022; mandate target 5c ("a two-line real example")
Kind: N-
Fidelity: exact (a single finite day; the asymptotic forms agree under a positive-mass proviso,
`massWeighted_eq_denomFree_of_pos`)
Hyps: (a) -/
theorem massWeighted_junk :
    (∑ j : Fin 1, (0 : ℝ) * ((1 : ℝ) / (0 : ℝ) - 0)) = 0 ∧
      (∑ j : Fin 1, (1 : ℝ)) - (∑ j : Fin 1, (0 : ℝ) * 0) = 1 := by
  constructor <;> simp

/-- Under a positive-mass proviso the two forms agree on every day (hence asymptotically).
Source: 2-022
Kind: L
Fidelity: exact
Hyps: (a); `c > 0` a uniform mass lower bound -/
theorem massWeighted_eq_denomFree_of_pos {k : ℕ} (mass q m : ℕ → Fin (k + 1) → ℝ) {c : ℝ}
    (hc : 0 < c) (h : ∀ n j, c ≤ mass n j) (n : ℕ) :
    ∑ j, mass n j * (q n j / mass n j - m n j) = ∑ j, q n j - ∑ j, mass n j * m n j :=
  massWeighted_eq_denomFree_of_ne_zero _ _ _ (fun j => ne_of_gt (lt_of_lt_of_le hc (h n j)))

/-! ## 5d — cancellation admitted -/

/-- **Cancellation is admitted by the aggregate form** (2-024): masses `½, ½` with per-index gaps
`+1, −1` give aggregate `0` — the one-sided aggregate inequality `≥ 0` holds — while the
per-index gaps are both nonzero (the two-sided per-index condition fails for both indices) and
one is negative (the one-sided per-index condition fails). The separation of the aggregated form
from the per-index form.
Source: 2-024; [[total-trust-implies-value]] §Hypotheses ("Aggregated over `j`. Individual gaps
may be large provided they cancel")
Kind: N+
Fidelity: exact (a finite frame)
Hyps: (a) -/
theorem cancellation_admitted :
    ∃ mass gap : Fin 2 → ℝ, (∀ j, 0 ≤ mass j) ∧ (∑ j, mass j) = 1 ∧
      0 ≤ ∑ j, mass j * gap j ∧ (∀ j, gap j ≠ 0) ∧ ∃ j, mass j * gap j < 0 := by
  refine ⟨![1 / 2, 1 / 2], ![1, -1], ?_, ?_, ?_, ?_, ⟨1, ?_⟩⟩
  · intro j; fin_cases j <;> norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · simp [Fin.sum_univ_two]
  · intro j; fin_cases j <;> norm_num
  · norm_num

/-! ## 5e — test-case sums -/

/-- **Death in Damascus as the liar probe at `s = ½`**: the H3 deficit is `−s(1−s) = −¼`.
Source: 2-023; [[total-trust-implies-value]] §Necessity ("Death in Damascus scores the same way")
Kind: L
Fidelity: exact (the real number; the LI instance is `Refuted.lean`
`probe_condStable_deficit_tendsto` at `s = ½`)
Hyps: (a) -/
theorem deathInDamascus_probe_sum : -((1 / 2 : ℝ) * (1 - 1 / 2)) = -(1 / 4) := by norm_num

/-- **Death in Damascus as the symmetric `k = 1` punishing menu** with masses `½, ½`:
`−Σ_j p_j(1 − p_j) = −½`.
Source: 2-023(b); [[total-trust-implies-value]] §Necessity ("two options at mass `≈ ½` … the sum
is `≈ −½`")
Kind: L
Fidelity: exact (the real number; the LI identity is `Punishing.lean` `punishing_h3_deficit`)
Hyps: (a) -/
theorem deathInDamascus_punishing_sum :
    -(∑ j : Fin 2, (![1 / 2, 1 / 2] : Fin 2 → ℝ) j * (1 - (![1 / 2, 1 / 2] : Fin 2 → ℝ) j)) =
      -(1 / 2) := by
  simp [Fin.sum_univ_two]
  norm_num

/-- **The tie-break pair** of [[ledger-decided-tie-breaks]] ll. 9–10 as a finite frame: with
masses `½, ½` and conditional-minus-unconditional gaps `+½, +½` (the clairvoyant rule: selection is
good news) the aggregate is `+½ ≥ 0`, admitted; with gaps `−½, −½` (the adversarial rule) it is
`−½ < 0`, excluded — the one-sided form convicts only the adversarial rule.
Source: 2-023(c); [[total-trust-implies-value]] §Hypotheses (one-sidedness); [[ledger-decided-tie-breaks]]
Kind: L
Fidelity: exact (a finite frame)
Hyps: (a) -/
theorem tieBreak_pair :
    0 ≤ ∑ j : Fin 2, (1 / 2 : ℝ) * (1 / 2) ∧ ∑ j : Fin 2, (1 / 2 : ℝ) * (-(1 / 2)) < 0 := by
  constructor <;> simp [Fin.sum_univ_two] <;> norm_num

end

end Cleanroom.Deference.DefArgmaxValue
