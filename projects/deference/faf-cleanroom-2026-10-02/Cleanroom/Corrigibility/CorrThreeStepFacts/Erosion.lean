import Cleanroom.Corrigibility.CorrThreeStepFacts.StopWorld
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.LinearCombination

/-!
# T4: erosion under silence; no erosion for a per-decision hazard

**Fixed fact.** `erode α β ε` is one silent period's Bayes update of the stop-world weight,
`ε(1 − β) / (ε(1 − β) + (1 − ε)(1 − α))`. The odds identity is proved in the division-free
product form (`erode_iter_product`) and then as `odds (e_n) = odds ε · ((1 − β)/(1 − α))^n`
(`erode_iter_odds`). With `α < β ≤ 1` the compliance condition on `twoState (e_n) α β c h`
fails for all large `n` (`erosion_fails_eventually`); the crossing index is characterised by
`(1 − ε)αc(1 − α)^n > εβh(1 − β)^n` (`erode_deltaMinus_neg_iff`), is monotone
(`crossing_succ`), and on the instance `(1/10, 1/20, 9/10, 1, 20)` equals `2`
(`Witnesses`: `w_crossing_isLeast`).

**Per-decision hazard.** On `Bool × Bool` (today's `r`, tomorrow's `r'`) with `r'` drawn afresh
at rate `ε'` independently of `r` and of the press, silence leaves `P(r' = 1 | ¬Pr) = ε'`
(`hazard_silent_posterior`): nothing erodes.

Sources: `soares.md` item 9, T1(b); `filler.md` R4.3; `amendment-1a.md` R9(i)–(ii).
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-! ## The silence update -/

/-- **The silence update.** Bayes on one silent period for a fixed stop-world of weight `ε`,
sensor `α` in-space and `β` at the stop-world: `ε(1 − β) / (ε(1 − β) + (1 − ε)(1 − α))`.
Well-defined (positive denominator) when `0 ≤ ε < 1` and `α < 1`, `β ≤ 1`
(`erode_denom_pos`); the headlines carry those hypotheses.
Source: [[corr-wf13-inventory]] 015 (item 9) / soares.md item 9; [[corr-wf14-inventory]] 008 / filler.md R4.3(a)
Kind: D
Fidelity: exact -/
noncomputable def erode (α β ε : ℝ) : ℝ := ε * (1 - β) / (ε * (1 - β) + (1 - ε) * (1 - α))

/-- The odds `x / (1 − x)`. Source: soares.md item 9. Kind: D. Fidelity: exact -/
noncomputable def odds (x : ℝ) : ℝ := x / (1 - x)

section Erode

variable {α β : ℝ}

/-- The denominator of the silence update is positive under `0 ≤ ε < 1`, `α < 1`, `β ≤ 1`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma erode_denom_pos (hα1 : α < 1) (hβ1 : β ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    0 < ε * (1 - β) + (1 - ε) * (1 - α) := by
  have h1 : 0 ≤ ε * (1 - β) := mul_nonneg hε0 (by linarith)
  have h2 : 0 < (1 - ε) * (1 - α) := mul_pos (by linarith) (by linarith)
  linarith

/-- The silence update is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma erode_nonneg (hα1 : α < 1) (hβ1 : β ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    0 ≤ erode α β ε :=
  div_nonneg (mul_nonneg hε0 (by linarith)) (erode_denom_pos hα1 hβ1 hε0 hε1).le

/-- The silence update stays below one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma erode_lt_one (hα1 : α < 1) (hβ1 : β ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    erode α β ε < 1 := by
  unfold erode
  rw [div_lt_one (erode_denom_pos hα1 hβ1 hε0 hε1)]
  have : 0 < (1 - ε) * (1 - α) := mul_pos (by linarith) (by linarith)
  linarith

/-- `1 − erode = (1 − ε)(1 − α) / D`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma one_sub_erode (hα1 : α < 1) (hβ1 : β ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    1 - erode α β ε = (1 - ε) * (1 - α) / (ε * (1 - β) + (1 - ε) * (1 - α)) := by
  have hD := (erode_denom_pos hα1 hβ1 hε0 hε1).ne'
  unfold erode
  field_simp
  ring

/-- The iterates stay in `[0, 1)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma erode_iter_mem (hα1 : α < 1) (hβ1 : β ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) :
    0 ≤ (erode α β)^[n] ε ∧ (erode α β)^[n] ε < 1 := by
  induction n with
  | zero => exact ⟨hε0, hε1⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨erode_nonneg hα1 hβ1 ih.1 ih.2, erode_lt_one hα1 hβ1 ih.1 ih.2⟩

/-- The iterates lie in `[0, 1]` (the parent's interval hypothesis for `twoState`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma erode_iter_mem_Icc (hα1 : α < 1) (hβ1 : β ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) :
    (erode α β)^[n] ε ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(erode_iter_mem hα1 hβ1 hε0 hε1 n).1, (erode_iter_mem hα1 hβ1 hε0 hε1 n).2.le⟩

/-- **T4(i), the odds identity in product form.** After `n` silent periods,
`e_n·(1 − ε)·(1 − α)^n = ε·(1 − β)^n·(1 − e_n)` — the geometric erosion of the odds with no
division anywhere.
Source: [[corr-wf13-inventory]] 015 (item 9) / soares.md item 9 (the displayed odds recursion); filler.md R4.3(a)
Kind: P
Fidelity: exact (product form of the displayed identity)
Hyps: (a) only -/
theorem erode_iter_product (hα1 : α < 1) (hβ1 : β ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (n : ℕ) :
    (erode α β)^[n] ε * (1 - ε) * (1 - α) ^ n = ε * (1 - β) ^ n * (1 - (erode α β)^[n] ε) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero]; ring
  | succ n ih =>
    obtain ⟨he0, he1⟩ := erode_iter_mem hα1 hβ1 hε0 hε1 n
    set e := (erode α β)^[n] ε with he
    have hD : e * (1 - β) + (1 - e) * (1 - α) ≠ 0 := (erode_denom_pos hα1 hβ1 he0 he1).ne'
    have key : erode α β e * (e * (1 - β) + (1 - e) * (1 - α)) = e * (1 - β) := by
      unfold erode; rw [div_mul_cancel₀ _ hD]
    have key2 : (1 - erode α β e) * (e * (1 - β) + (1 - e) * (1 - α)) = (1 - e) * (1 - α) := by
      rw [sub_mul, key]; ring
    rw [Function.iterate_succ_apply', ← he]
    apply mul_right_cancel₀ hD
    calc erode α β e * (1 - ε) * (1 - α) ^ (n + 1) * (e * (1 - β) + (1 - e) * (1 - α))
        = (erode α β e * (e * (1 - β) + (1 - e) * (1 - α))) * (1 - ε) * (1 - α) ^ (n + 1) := by
          ring
      _ = e * (1 - β) * (1 - ε) * (1 - α) ^ (n + 1) := by rw [key]
      _ = ε * (1 - β) ^ (n + 1) * ((1 - e) * (1 - α)) := by
          linear_combination (1 - β) * (1 - α) * ih
      _ = ε * (1 - β) ^ (n + 1) * ((1 - erode α β e) * (e * (1 - β) + (1 - e) * (1 - α))) := by
          rw [key2]
      _ = ε * (1 - β) ^ (n + 1) * (1 - erode α β e) * (e * (1 - β) + (1 - e) * (1 - α)) := by
          ring

/-- **T4(i), the odds identity.** `odds (e_n) = odds ε · ((1 − β)/(1 − α))^n` on the open interval.
Source: [[corr-wf13-inventory]] 015 (item 9) / soares.md item 9 (displayed)
Kind: L (from `erode_iter_product`)
Fidelity: exact
Hyps: (a) only -/
theorem erode_iter_odds (hα1 : α < 1) (hβ1 : β ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) :
    odds ((erode α β)^[n] ε) = odds ε * ((1 - β) / (1 - α)) ^ n := by
  have hprod := erode_iter_product hα1 hβ1 hε0 hε1 n
  have he1 := (erode_iter_mem hα1 hβ1 hε0 hε1 n).2
  have h1 : (1 - (erode α β)^[n] ε) ≠ 0 := by linarith
  have h2 : (1 - ε) ≠ 0 := by linarith
  have h3 : (1 - α) ≠ 0 := by linarith
  unfold odds
  rw [div_pow, div_mul_div_comm, div_eq_div_iff h1 (mul_ne_zero h2 (pow_ne_zero n h3))]
  linear_combination hprod

/-- The masses `A := (1 − ε)(1 − α)^n`, `B := ε(1 − β)^n` determine `e_n = B/(A + B)`,
`1 − e_n = A/(A + B)`, in product form: `e_n (A + B) = B`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma erode_iter_mul_eq (hα1 : α < 1) (hβ1 : β ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) :
    (erode α β)^[n] ε * ((1 - ε) * (1 - α) ^ n + ε * (1 - β) ^ n) = ε * (1 - β) ^ n := by
  have := erode_iter_product hα1 hβ1 hε0 hε1 n
  linear_combination this

/-- **T4(iii), the crossing criterion.** The compliance condition on the eroded two-state
instance fails at period `n` — `Δ₋(twoState (e_n) α β c h) < 0` — iff
`ε·β·h·(1 − β)^n < (1 − ε)·α·c·(1 − α)^n`. The "least `n`" with this property is the crossing
index (rule 4 of the mandate: stated as a predicate, computed on the instance in `Witnesses`).
Source: [[corr-wf14-inventory]] 008 / filler.md R4.3(a) ("compliance fails at the second silent period"); soares.md item 9
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem erode_deltaMinus_neg_iff (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hα1 : α < 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (c h : ℝ) (n : ℕ) :
    (twoState ((erode α β)^[n] ε) α β c h (erode_iter_mem_Icc hα1 hβ.2 hε0 hε1 n) hα hβ).deltaMinus
        () .cont .stop < 0 ↔
      ε * β * h * (1 - β) ^ n < (1 - ε) * α * c * (1 - α) ^ n := by
  rw [twoState_deltaMinus]
  set e := (erode α β)^[n] ε with he
  set A := (1 - ε) * (1 - α) ^ n with hA
  set B := ε * (1 - β) ^ n with hB
  have hApos : 0 < A := mul_pos (by linarith) (pow_pos (by linarith) n)
  have hB0 : 0 ≤ B := mul_nonneg hε0 (pow_nonneg (by linarith [hβ.2]) n)
  have hAB : 0 < A + B := by linarith
  have hmul : e * (A + B) = B := erode_iter_mul_eq hα1 hβ.2 hε0 hε1 n
  have hmul' : (1 - e) * (A + B) = A := by linear_combination -hmul
  have hcross : (e * β * h - (1 - e) * α * c) * (A + B) = B * β * h - A * α * c := by
    linear_combination (β * h) * hmul - (α * c) * hmul'
  constructor
  · intro hlt
    have : (e * β * h - (1 - e) * α * c) * (A + B) < 0 := mul_neg_of_neg_of_pos hlt hAB
    rw [hcross] at this
    linarith
  · intro hlt
    have : B * β * h - A * α * c < 0 := by linarith
    rw [← hcross] at this
    exact neg_of_mul_neg_left this hAB.le

/-- The crossing criterion is monotone: once compliance fails under silence it stays failed,
because `(1 − β) < (1 − α)` shrinks the left side faster than the right.
Source: soares.md item 9 ("fails for all large `n`"); filler.md R4.3(a)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem crossing_succ (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hαβ : α < β)
    {ε c h : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 ≤ c) (hh : 0 ≤ h) (n : ℕ)
    (hn : ε * β * h * (1 - β) ^ n < (1 - ε) * α * c * (1 - α) ^ n) :
    ε * β * h * (1 - β) ^ (n + 1) < (1 - ε) * α * c * (1 - α) ^ (n + 1) := by
  have h1 : 0 ≤ ε * β * h * (1 - β) ^ n :=
    mul_nonneg (mul_nonneg (mul_nonneg hε0 hβ.1) hh) (pow_nonneg (by linarith [hβ.2]) n)
  have h2 : 0 ≤ (1 - ε) * α * c * (1 - α) ^ n :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hα.1) hc) (pow_nonneg (by linarith [hα.2]) n)
  have h3 : 0 ≤ 1 - β := by linarith [hβ.2]
  have h4 : 1 - β < 1 - α := by linarith
  rw [pow_succ, pow_succ, ← mul_assoc, ← mul_assoc]
  calc ε * β * h * (1 - β) ^ n * (1 - β) ≤ ε * β * h * (1 - β) ^ n * (1 - α) :=
        mul_le_mul_of_nonneg_left h4.le h1
    _ < (1 - ε) * α * c * (1 - α) ^ n * (1 - α) := by
        rcases eq_or_lt_of_le h2 with h2' | h2'
        · exfalso; linarith
        · exact mul_lt_mul_of_pos_right hn (by linarith)

/-- **T4(ii), erosion.** With an informative sensor `α < β ≤ 1`, `0 < α`, `α < 1`, stakes
`c, h > 0` and a stop-world weight `0 ≤ ε < 1` that is a fixed fact updated by conditionally
independent silent periods, the compliance condition `Δ₋ ≥ 0` on `twoState (e_n) α β c h` fails
for all large `n`: every quiet period multiplies the odds of the stop-world by
`(1 − β)/(1 − α) < 1`.
Source: [[corr-wf14-inventory]] 008 / filler.md R4.3(a); [[corr-wf13-inventory]] 015 (item 9) / soares.md item 9, T1(b); [[corr-wf13-2-inventory]] 077(b)
Kind: P
Fidelity: variant: `0 < α` added, and needed — Soares's T1(b) ("for every `P₀(ω⊥) < 1`", sensor `β > α`) omits it, and at `α = 0` D1 holds at every silent period (`d1_forever_of_alpha_zero`; audit r1, F-13)
Hyps: (a) only (the hypotheses are the sensor bounds, informativeness, `0 < α` and positive stakes) -/
theorem erosion_fails_eventually (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hαβ : α < β) (hα0 : 0 < α) {ε c h : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hc : 0 < c) (hh : 0 < h) :
    ∃ N : ℕ, ∀ n ≥ N,
      ¬ (0 ≤ (twoState ((erode α β)^[n] ε) α β c h
        (erode_iter_mem_Icc (by linarith [hβ.2]) hβ.2 hε0 hε1 n) hα hβ).deltaMinus () .cont .stop) := by
  have hα1 : α < 1 := by linarith [hβ.2]
  -- the crossing criterion holds from some `N` on
  suffices hcross : ∃ N : ℕ, ε * β * h * (1 - β) ^ N < (1 - ε) * α * c * (1 - α) ^ N by
    obtain ⟨N, hN⟩ := hcross
    refine ⟨N, fun n hn => ?_⟩
    rw [not_le, erode_deltaMinus_neg_iff hα hβ hα1 hε0 hε1 c h n]
    induction n, hn using Nat.le_induction with
    | base => exact hN
    | succ k _ ih => exact crossing_succ hα hβ hαβ hε0 hε1.le hc.le hh.le k ih
  set r := (1 - β) / (1 - α) with hr
  have h1α : 0 < 1 - α := by linarith
  have hr0 : 0 ≤ r := div_nonneg (by linarith [hβ.2]) h1α.le
  have hr1 : r < 1 := by rw [hr, div_lt_one h1α]; linarith
  have hpos : 0 < (1 - ε) * α * c := mul_pos (mul_pos (by linarith) hα0) hc
  by_cases hε : ε = 0
  · refine ⟨0, ?_⟩
    simp only [hε, zero_mul, pow_zero, mul_one, sub_zero, one_mul]
    exact mul_pos hα0 hc
  have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hε)
  have hβh : 0 < ε * β * h := mul_pos (mul_pos hεpos (by linarith)) hh
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hpos hβh) hr1
  refine ⟨N, ?_⟩
  have hrN : ε * β * h * r ^ N < (1 - ε) * α * c := by
    rw [lt_div_iff₀ hβh] at hN; linarith
  have hkey : (1 - β) ^ N = r ^ N * (1 - α) ^ N := by
    rw [hr, div_pow, div_mul_cancel₀ _ (pow_ne_zero N h1α.ne')]
  rw [hkey]
  have hpowpos : 0 < (1 - α) ^ N := pow_pos h1α N
  calc ε * β * h * (r ^ N * (1 - α) ^ N) = (ε * β * h * r ^ N) * (1 - α) ^ N := by ring
    _ < (1 - ε) * α * c * (1 - α) ^ N := mul_lt_mul_of_pos_right hrN hpowpos

end Erode

/-- **T4, the `α = 0` boundary (F-13).** With no false presses (`α = 0`), desideratum 1 holds on
the eroded instance at *every* silent period, for every `0 ≤ ε < 1`, `β ∈ [0, 1]`, `h ≥ 0`: the
odds still erode (`erode_at_alpha_zero`), but the compliance condition `(1 − e_n)·0·c ≤ e_n β h`
is never violated. So T1(b) as worded ("fails after finitely many silent periods for every
`P₀(ω⊥) < 1`") is false at `α = 0`; `erosion_fails_eventually`'s `0 < α` is load-bearing.
Source: soares.md T1(b) (the missing hypothesis); audit r1 (adversarial) N2
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem d1_forever_of_alpha_zero (β c h : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hh : 0 ≤ h) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (n : ℕ) :
    (twoState ((erode 0 β)^[n] ε) 0 β c h (erode_iter_mem_Icc (by norm_num) hβ.2 hε0 hε1 n)
      mem_Icc_zero hβ).D1At () := by
  rw [twoState_d1At_iff]
  have he := (erode_iter_mem (by norm_num : (0 : ℝ) < 1) hβ.2 hε0 hε1 n).1
  simp only [mul_zero, zero_mul]
  exact mul_nonneg (mul_nonneg he hβ.1) hh

/-- The odds do erode at `α = 0` (the sensor is informative, `β > 0 = α`): one silent period
takes the weight `1/10` with `β = 9/10` to `1/91`.
Source: soares.md item 9; audit r1 (adversarial) N2. Kind: N+. Fidelity: exact -/
theorem erode_at_alpha_zero : erode 0 (9/10) (1/10 : ℝ) = 1/91 := by
  unfold erode; norm_num

/-! ## The per-decision hazard: no erosion -/

/-- The two-point prior on `Bool` with `mass true = ε`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def boolPoint (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Distr Bool where
  mass b := if b then ε else 1 - ε
  nonneg b := by cases b <;> simp <;> linarith [hε.1, hε.2]
  sum_eq_one := by rw [Fintype.sum_bool]; simp

/-- **The per-decision hazard model.** `Ω = Bool × Bool`: today's reliability `r` (rate `ε`)
and tomorrow's `r'`, drawn afresh at rate `ε'` independently of `r`; the press reads today's
`r` only (`β` if `r`, `α` otherwise); `Sh = {stop}`, `V` the two-state value on today's `r`.
Source: [[corr-wf14-inventory]] 008 / filler.md R4.3(b) ("per-plan wrongness `W_t` with a hazard rate"); [[corr-wf13-inventory]] 015 (item 10, escape (i))
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def hazard (ε ε' α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hε' : ε' ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    ThreeStep (Bool × Bool) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => kernelProd (boolPoint ε hε) (fun _ => boolPoint ε' hε')
  press := fun _ p => if p.1 then β else α
  press_nonneg := fun _ p => by cases p.1 <;> simp [hα.1, hβ.1]
  press_le_one := fun _ p => by cases p.1 <;> simp [hα.2, hβ.2]
  V := fun _ _ b p => if p.1 then twoValue c h b .wrong else twoValue c h b .right

section Hazard

variable (ε ε' α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hε' : ε' ∈ Set.Icc (0 : ℝ) 1)
  (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The indicator of "tomorrow's reliability bit is set". Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def tomorrowWrong : Bool × Bool → ℝ := fun p => if p.2 then 1 else 0

/-- **T4, per-decision hazard, silence.** `E_P[1_{r'} 1_{¬Pr}] = ε' · (1 − P(Pr))`: in product
form, the silence-weighted mass of "tomorrow wrong" is `ε'` times the silence mass, so
`P(r' = 1 | ¬Pr) = ε'` — silence today does not touch tomorrow's hazard.
Source: [[corr-wf14-inventory]] 008 / filler.md R4.3(b); amendment-1a.md R9(ii)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem hazard_silent_obsExpect :
    (hazard ε ε' α β c h hε hε' hα hβ).obsExpect () .silent tomorrowWrong =
      ε' * (1 - (hazard ε ε' α β c h hε hε' hα hβ).pressMass ()) := by
  simp [obsExpect, pressMass, obsWeight_silent, hazard, kernelProd_mass, boolPoint,
    tomorrowWrong, Fintype.sum_prod_type]
  ring

/-- **T4, per-decision hazard, press.** `E_P[1_{r'} 1_{Pr}] = ε' · P(Pr)`: a press today does not
touch tomorrow's hazard either.
Source: filler.md R4.3(b)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem hazard_press_obsExpect :
    (hazard ε ε' α β c h hε hε' hα hβ).obsExpect () .press tomorrowWrong =
      ε' * (hazard ε ε' α β c h hε hε' hα hβ).pressMass () := by
  simp [obsExpect, pressMass, obsWeight_press, hazard, kernelProd_mass, boolPoint,
    tomorrowWrong, Fintype.sum_prod_type]
  ring

/-- **T4, per-decision hazard, the conditional.** Under `P(Pr) < 1`, `P(r' = 1 | ¬Pr) = ε'`
(the derived conditional form).
Source: filler.md R4.3(b) ("`ε_t` converges to the realized error frequency", the non-eroding reading)
Kind: L
Fidelity: exact
Hyps: (a) `pressMass < 1` is where the conditional is defined -/
theorem hazard_silent_posterior (hpm : (hazard ε ε' α β c h hε hε' hα hβ).pressMass () < 1) :
    (hazard ε ε' α β c h hε hε' hα hβ).condExpSilent () tomorrowWrong = ε' := by
  rw [condExpSilent, hazard_silent_obsExpect, mul_div_assoc, div_self (by linarith), mul_one]

end Hazard

end Cleanroom.Corrigibility.CorrThreeStepFacts
