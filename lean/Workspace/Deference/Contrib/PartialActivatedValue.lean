/-
# Partial evaluations, completions, and the three regrets

Round `projects/deference/rounds/2026-09-07-reason-mediated-authorship/`.

`ActivatedValue.lean` takes a total payoff `V : Q → W → ℚ`.  Semantically the future
principal's evaluation exists only on certified worlds: it is a **partial** object
`Vp : (w : W) → c w = true → Q → ℚ`.  This module shows that nothing in the activated
algebra depends on how `Vp` is completed off the certified set, and makes the three regrets
exact.

* `Completion`, `activated_completion_congr` — any two bounded completions agreeing with
  `Vp` on certified worlds give the **same** activated securities, pointwise.
* `regretU`, `regretAuth`, `regretU_eq_mass_mul_regretAuth` — activated menu regret is the
  activation mass times the **conditional authoritative regret**, which is defined from
  `Vp` alone (it never reads a completion).
* `regretV_sub_regretU_abs_le` — **the completion theorem**: for every completion with
  payoffs in an interval of width `D`, `|regretVbar − regretU| ≤ D · voidMass`.  Changing
  the arbitrary void-world completion moves fixed-menu regret by at most `D·η` in *either*
  direction; a world-dependent followed strategy can use the void branch to beat every
  fixed candidate, so completion regret can lie *below* activated regret.
  `availability_transfer_completion` is the one-sided upper corollary;
  `regret_constant_completion` shows a completion that does not separate candidates on
  void worlds leaves regret unchanged; `SharpLower.attained` attains `regretU − D·η` and
  `ActivatedValue.Sharp.transfer_sharp` attains `regretU + D·η`, so both constants are
  sharp.
* `regretAuth_le_div` — **the authoritative-regret theorem**: with a normalized credence,
  `regretU ≤ ε`, `0 ≤ ε`, and void mass `≤ η < 1`, the activation mass is at least `1 − η`
  and `regretAuth ≤ ε / (1 − η)`.  `regretAuth_asymptotic` is the sequence form:
  activated regret asymptotically nonpositive and void mass vanishing give conditional
  authoritative regret asymptotically nonpositive.
* `regretU_perturb` — two payoffs within `δ` on certified worlds have activated regrets
  within `2·δ·mass`: the quantitative-authorship interaction, stated as algebra.

**What this does not establish.**  Which completion, if any, is "right": none is, and that
is the point; the authoritative quantity is `regretAuth`, defined without one.  Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.ActivatedValue
import Mathlib.Order.Basic
import Mathlib.Tactic.FinCases

namespace Workspace.Deference.Contrib.ActivatedValue

open Finset

variable {W Q : Type*} [Fintype W]

/-! ## 1. Partial evaluations and completions -/

/-- A completion `Vbar` of the partial evaluation `Vp`: total, and equal to `Vp` wherever the
contract is certified. -/
def Completion (c : W → Bool) (Vp : (w : W) → c w = true → Q → ℚ) (Vbar : Q → W → ℚ) : Prop :=
  ∀ w (h : c w = true) a, Vbar a w = Vp w h a

omit [Fintype W] in
/-- **Completion invariance.**  Two completions of one partial evaluation give the same
activated securities, pointwise. -/
theorem activated_completion_congr (c : W → Bool) (Vp : (w : W) → c w = true → Q → ℚ)
    {Vbar Vbar' : Q → W → ℚ} (h : Completion c Vp Vbar) (h' : Completion c Vp Vbar') :
    activated c Vbar = activated c Vbar' := by
  funext a w
  unfold activated ind
  by_cases hc : c w = true
  · simp only [hc, if_true, one_mul]
    rw [h w hc a, h' w hc a]
  · simp [hc]

/-- The canonical completion by a constant `k` off the certified set. -/
noncomputable def completeBy (c : W → Bool) (Vp : (w : W) → c w = true → Q → ℚ) (k : ℚ)
    (a : Q) (w : W) : ℚ :=
  if h : c w = true then Vp w h a else k

omit [Fintype W] in
theorem completeBy_completion (c : W → Bool) (Vp : (w : W) → c w = true → Q → ℚ) (k : ℚ) :
    Completion c Vp (completeBy c Vp k) := by
  intro w h a
  simp [completeBy, h]

/-! ## 2. The three regrets -/

variable [Fintype Q] [Nonempty Q]

/-- **Activated menu regret** of a followed strategy: the best fixed candidate's activated
expectation, less the strategy's.  The maximum is outside the expectation. -/
noncomputable def regretU (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ) (α : W → Q → ℚ) : ℚ :=
  (univ.sup' univ_nonempty fun a => expect π (activated c V a))
    - expect π (followed α (activated c V))

/-- **Ordinary (completion) regret** against a total payoff. -/
noncomputable def regretV (π : W → ℚ) (V : Q → W → ℚ) (α : W → Q → ℚ) : ℚ :=
  (univ.sup' univ_nonempty fun a => expect π (V a)) - expect π (followed α V)

/-- The conditional expectation of a *partial* payoff on the certified set. -/
def condExpectPartial (π : W → ℚ) (c : W → Bool) (X : (w : W) → c w = true → ℚ) : ℚ :=
  expect π (fun w => if h : c w = true then X w h else 0) / mass π c

/-- **Conditional authoritative regret**: defined from the partial evaluation alone. -/
noncomputable def regretAuth (π : W → ℚ) (c : W → Bool) (Vp : (w : W) → c w = true → Q → ℚ)
    (α : W → Q → ℚ) : ℚ :=
  (univ.sup' univ_nonempty fun a => condExpectPartial π c fun w h => Vp w h a)
    - condExpectPartial π c fun w h => ∑ b, α w b * Vp w h b

omit [Fintype Q] [Nonempty Q] in
/-- The activated followed strategy is the activation of the followed strategy. -/
theorem followed_activated (c : W → Bool) (V : Q → W → ℚ) (α : W → Q → ℚ) [Fintype Q]
    (w : W) : followed α (activated c V) w = ind c w * followed α V w := by
  unfold followed activated
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

omit [Fintype Q] [Nonempty Q] in
/-- An activated expectation is the mass times the partial conditional expectation, for
any completion. -/
theorem expect_activated_eq_mass_mul (π : W → ℚ) (c : W → Bool)
    (Vp : (w : W) → c w = true → Q → ℚ) {Vbar : Q → W → ℚ} (hVbar : Completion c Vp Vbar) (a : Q)
    (hm : 0 < mass π c) :
    expect π (activated c Vbar a) = mass π c * condExpectPartial π c fun w h => Vp w h a := by
  unfold condExpectPartial
  rw [mul_div_cancel₀ _ hm.ne']
  unfold expect activated ind
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hc : c w = true
  · simp [hc, hVbar w hc a]
  · simp [hc]

omit [Fintype Q] [Nonempty Q] in
theorem expect_followed_activated_eq_mass_mul (π : W → ℚ) (c : W → Bool)
    (Vp : (w : W) → c w = true → Q → ℚ) {Vbar : Q → W → ℚ} (hVbar : Completion c Vp Vbar)
    (α : W → Q → ℚ) [Fintype Q] (hm : 0 < mass π c) :
    expect π (followed α (activated c Vbar))
      = mass π c * condExpectPartial π c fun w h => ∑ b, α w b * Vp w h b := by
  unfold condExpectPartial
  rw [mul_div_cancel₀ _ hm.ne']
  unfold expect
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [followed_activated]
  unfold ind followed
  by_cases hc : c w = true
  · simp only [hc, if_true, one_mul, dif_pos]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hVbar w hc b]
  · simp [hc]

/-- A positive scalar commutes with a finite supremum. -/
theorem sup'_mul_left {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (m : ℚ) (hm : 0 < m)
    (f : ι → ℚ) : s.sup' hs (fun i => m * f i) = m * s.sup' hs f := by
  apply le_antisymm
  · refine Finset.sup'_le hs _ fun i hi => ?_
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) hm.le
  · obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_sup' hs f
    rw [hfi]
    exact Finset.le_sup' (fun i => m * f i) hi

/-- **Activated regret is the mass times the conditional authoritative regret.**  The
right-hand side never reads a completion. -/
theorem regretU_eq_mass_mul_regretAuth (π : W → ℚ) (c : W → Bool)
    (Vp : (w : W) → c w = true → Q → ℚ) {Vbar : Q → W → ℚ} (hVbar : Completion c Vp Vbar)
    (α : W → Q → ℚ) (hm : 0 < mass π c) :
    regretU π c Vbar α = mass π c * regretAuth π c Vp α := by
  unfold regretU regretAuth
  rw [mul_sub, ← sup'_mul_left, expect_followed_activated_eq_mass_mul π c Vp hVbar α hm]
  · congr 1
    refine Finset.sup'_congr _ rfl fun a _ => ?_
    exact expect_activated_eq_mass_mul π c Vp hVbar a hm
  · exact hm

/-! ## 3. The completion theorem -/

/-- Regret in the fixed-`sup'` form is bounded by the pointwise form. -/
theorem regretV_le_of_pointwise (π : W → ℚ) (V : Q → W → ℚ) (α : W → Q → ℚ) (r : ℚ)
    (h : ∀ a, expect π (V a) - expect π (followed α V) ≤ r) : regretV π V α ≤ r := by
  unfold regretV
  rw [sub_le_iff_le_add]
  refine Finset.sup'_le _ _ fun a _ => ?_
  linarith [h a]

theorem regretU_ge_pointwise (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ) (α : W → Q → ℚ)
    (a : Q) : expect π (activated c V a) - expect π (followed α (activated c V)) ≤
      regretU π c V α := by
  unfold regretU
  have := Finset.le_sup' (fun a => expect π (activated c V a)) (Finset.mem_univ a)
  linarith

/-- The void mass `𝔼[1 − c]`. -/
def voidMass (π : W → ℚ) (c : W → Bool) : ℚ := expect π fun w => 1 - ind c w

omit [Fintype Q] [Nonempty Q] in
/-- The followed strategy's unactivated excess lies between `L` and `L + D` times the void
mass. -/
theorem followed_excess_bounds [Fintype Q] (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ)
    (α : W → Q → ℚ) (L D : ℚ)
    (hπ : ∀ w, 0 ≤ π w) (hα : ∀ w a, 0 ≤ α w a) (hα1 : ∀ w, ∑ a, α w a = 1)
    (hlo : ∀ a w, L ≤ V a w) (hhi : ∀ a w, V a w ≤ L + D) :
    L * voidMass π c ≤ expect π (followed α V) - expect π (followed α (activated c V)) ∧
    expect π (followed α V) - expect π (followed α (activated c V)) ≤ (L + D) * voidMass π c := by
  have hexp : expect π (followed α V) - expect π (followed α (activated c V))
      = ∑ w, π w * ((1 - ind c w) * followed α V w) := by
    simp only [expect, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [followed_activated]; ring
  have hbounds : ∀ w, L ≤ followed α V w ∧ followed α V w ≤ L + D := by
    intro w
    unfold followed
    constructor
    · calc L = ∑ b, α w b * L := by rw [← Finset.sum_mul, hα1 w, one_mul]
        _ ≤ ∑ b, α w b * V b w :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hlo b w) (hα w b)
    · calc ∑ b, α w b * V b w ≤ ∑ b, α w b * (L + D) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hhi b w) (hα w b)
        _ = L + D := by rw [← Finset.sum_mul, hα1 w, one_mul]
  rw [hexp]
  unfold voidMass expect
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have h1c : 0 ≤ 1 - ind c w := by linarith [ind_le_one c w]
    have := mul_le_mul_of_nonneg_left (hbounds w).1 h1c
    nlinarith [hπ w]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have h1c : 0 ≤ 1 - ind c w := by linarith [ind_le_one c w]
    have := mul_le_mul_of_nonneg_left (hbounds w).2 h1c
    nlinarith [hπ w]

/-- A finite supremum shifted by termwise bounded increments moves by at most those bounds. -/
theorem sup'_add_bounds {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f e : ι → ℚ) (lo hi : ℚ)
    (hlo : ∀ i ∈ s, lo ≤ e i) (hhi : ∀ i ∈ s, e i ≤ hi) :
    s.sup' hs f + lo ≤ s.sup' hs (fun i => f i + e i) ∧
    s.sup' hs (fun i => f i + e i) ≤ s.sup' hs f + hi := by
  constructor
  · obtain ⟨i, hi, hfi⟩ := Finset.exists_mem_eq_sup' hs f
    rw [hfi]
    have := Finset.le_sup' (fun i => f i + e i) hi
    linarith [hlo i hi]
  · refine Finset.sup'_le hs _ fun i hi => ?_
    have := Finset.le_sup' f hi
    linarith [hhi i hi]

/-- **The completion theorem.**  For payoffs in `[L, L + D]`, the completion regret and the
activated regret differ by at most `D` times the void mass, in either direction. -/
theorem regretV_sub_regretU_abs_le (π : W → ℚ) (c : W → Bool) (V : Q → W → ℚ)
    (α : W → Q → ℚ) (L D : ℚ)
    (hπ : ∀ w, 0 ≤ π w) (hα : ∀ w a, 0 ≤ α w a) (hα1 : ∀ w, ∑ a, α w a = 1)
    (hlo : ∀ a w, L ≤ V a w) (hhi : ∀ a w, V a w ≤ L + D) :
    |regretV π V α - regretU π c V α| ≤ D * voidMass π c := by
  have hcand : ∀ a, L * voidMass π c ≤ expect π (V a) - expect π (activated c V a) ∧
      expect π (V a) - expect π (activated c V a) ≤ (L + D) * voidMass π c :=
    fun a => excess_bounds π c V a L D hπ (hlo a) (hhi a)
  have hsup := sup'_add_bounds Finset.univ Finset.univ_nonempty
    (fun a => expect π (activated c V a)) (fun a => expect π (V a) - expect π (activated c V a))
    (L * voidMass π c) ((L + D) * voidMass π c) (fun a _ => (hcand a).1) (fun a _ => (hcand a).2)
  have heq : (Finset.univ.sup' Finset.univ_nonempty fun a =>
      expect π (activated c V a) + (expect π (V a) - expect π (activated c V a)))
      = Finset.univ.sup' Finset.univ_nonempty fun a => expect π (V a) := by
    refine Finset.sup'_congr _ rfl fun a _ => ?_; ring
  rw [heq] at hsup
  have hfoll := followed_excess_bounds π c V α L D hπ hα hα1 hlo hhi
  unfold regretV regretU
  rw [abs_le]
  constructor <;> nlinarith [hsup.1, hsup.2, hfoll.1, hfoll.2]

/-- **Completion-robust availability transfer** (one-sided corollary).  Activated regret
`≤ ε`, void mass `≤ η`, and for every completion with values in `[L, L + D]`, completion
regret `≤ ε + D·η`. -/
theorem availability_transfer_completion (π : W → ℚ) (c : W → Bool)
    (Vp : (w : W) → c w = true → Q → ℚ) (α : W → Q → ℚ) (L D ε η : ℚ) (hD : 0 ≤ D)
    (hπ : ∀ w, 0 ≤ π w) (hα : ∀ w a, 0 ≤ α w a) (hα1 : ∀ w, ∑ a, α w a = 1)
    (hη : expect π (fun w => 1 - ind c w) ≤ η)
    (Vbar : Q → W → ℚ) (_hVbar : Completion c Vp Vbar)
    (hlo : ∀ a w, L ≤ Vbar a w) (hhi : ∀ a w, Vbar a w ≤ L + D)
    (hreg : regretU π c Vbar α ≤ ε) :
    regretV π Vbar α ≤ ε + D * η := by
  have h := regretV_sub_regretU_abs_le π c Vbar α L D hπ hα hα1 hlo hhi
  have hη' : voidMass π c ≤ η := hη
  have := (abs_le.mp h).2
  nlinarith

/-- A completion constant across candidates on void worlds leaves regret unchanged: the
void branch then separates no candidates and no strategy. -/
theorem regret_constant_completion (π : W → ℚ) (c : W → Bool)
    (Vp : (w : W) → c w = true → Q → ℚ) (α : W → Q → ℚ) (hα1 : ∀ w, ∑ a, α w a = 1)
    (k : ℚ) : regretV π (completeBy c Vp k) α = regretU π c (completeBy c Vp k) α := by
  unfold regretV regretU
  have hpt : ∀ a, expect π (completeBy c Vp k a) =
      expect π (activated c (completeBy c Vp k) a) + expect π (fun w => (1 - ind c w) * k) := by
    intro a
    unfold expect
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold activated ind completeBy
    by_cases hc : c w = true
    · simp [hc]
    · simp [hc]
  have hfoll : expect π (followed α (completeBy c Vp k)) =
      expect π (followed α (activated c (completeBy c Vp k)))
        + expect π (fun w => (1 - ind c w) * k) := by
    unfold expect
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [followed_activated]
    unfold followed ind completeBy
    by_cases hc : c w = true
    · simp [hc]
    · simp only [hc, if_false, zero_mul, sub_zero, one_mul]
      simp only [Bool.false_eq_true, dite_false]
      rw [← Finset.sum_mul, hα1 w, one_mul]
      ring
  have hsup : (univ.sup' univ_nonempty fun a => expect π (completeBy c Vp k a))
      = (univ.sup' univ_nonempty fun a => expect π (activated c (completeBy c Vp k) a))
        + expect π (fun w => (1 - ind c w) * k) := by
    rw [Finset.sup'_congr univ_nonempty rfl fun a _ => hpt a]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun a _ => ?_
      have := Finset.le_sup' (fun a => expect π (activated c (completeBy c Vp k) a))
        (Finset.mem_univ a)
      linarith
    · obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' univ_nonempty
        (fun a => expect π (activated c (completeBy c Vp k) a))
      rw [ha]
      exact Finset.le_sup' (fun a => expect π (activated c (completeBy c Vp k) a)
        + expect π (fun w => (1 - ind c w) * k)) (Finset.mem_univ a)
  rw [hsup, hfoll]
  ring

/-! ## 3b. Lower sharpness: the void branch can beat every fixed candidate

Two worlds of mass `½`.  On the certified world candidate `0` is worth `1` and candidate `1`
worth `0`; the completion on the void world reverses them.  The strategy follows `0` on the
certified world and `1` on the void one.  Activated regret is `0`; completion regret is
`−½ = regretU − D·voidMass` with `D = 1`, `voidMass = ½`. -/

namespace SharpLower

def π : Fin 2 → ℚ := ![1/2, 1/2]
def c : Fin 2 → Bool := ![true, false]
def V : Fin 2 → Fin 2 → ℚ := ![![1, 0], ![0, 1]]
def α : Fin 2 → Fin 2 → ℚ := ![![1, 0], ![0, 1]]

theorem sup'_pair (f : Fin 2 → ℚ) (h : f 1 ≤ f 0) :
    Finset.univ.sup' Finset.univ_nonempty f = f 0 := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun i _ => ?_
    fin_cases i <;> simp [h]
  · exact Finset.le_sup' f (Finset.mem_univ 0)

theorem attained :
    regretU π c V α = 0 ∧ voidMass π c = 1/2 ∧ regretV π V α = 0 - 1 * (1/2) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold regretU
    rw [sup'_pair]
    · simp [expect, followed, activated, ind, π, c, V, α, Fin.sum_univ_two]
    · simp [expect, activated, ind, π, c, V, Fin.sum_univ_two]
  · simp [voidMass, expect, ind, π, c, Fin.sum_univ_two]
  · unfold regretV
    rw [sup'_pair]
    · simp [expect, followed, π, V, α, Fin.sum_univ_two]
    · simp [expect, π, V, Fin.sum_univ_two]

end SharpLower

/-! ## 3c. The authoritative-regret theorem -/

/-- The activation mass is the total credence less the void mass. -/
theorem mass_eq (π : W → ℚ) (c : W → Bool) :
    mass π c = (∑ w, π w) - voidMass π c := by
  unfold mass voidMass expect
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

/-- **Authoritative regret.**  With a normalized credence, activated regret `≤ ε`, `0 ≤ ε`,
and void mass `≤ η < 1`: the activation mass is at least `1 − η`, and the conditional
authoritative regret is at most `ε / (1 − η)`. -/
theorem regretAuth_le_div (π : W → ℚ) (c : W → Bool)
    (Vp : (w : W) → c w = true → Q → ℚ) {Vbar : Q → W → ℚ} (hVbar : Completion c Vp Vbar)
    (α : W → Q → ℚ) (ε η : ℚ)
    (hsum : ∑ w, π w = 1) (hη : voidMass π c ≤ η) (hη1 : η < 1) (hε : 0 ≤ ε)
    (hreg : regretU π c Vbar α ≤ ε) :
    1 - η ≤ mass π c ∧ regretAuth π c Vp α ≤ ε / (1 - η) := by
  have hmass : 1 - η ≤ mass π c := by rw [mass_eq, hsum]; linarith
  have hm : 0 < mass π c := by linarith
  refine ⟨hmass, ?_⟩
  have hid := regretU_eq_mass_mul_regretAuth π c Vp hVbar α hm
  rw [hid] at hreg
  have h1η : 0 < 1 - η := by linarith
  rw [le_div_iff₀ h1η]
  by_cases hA : 0 ≤ regretAuth π c Vp α
  · calc regretAuth π c Vp α * (1 - η) ≤ regretAuth π c Vp α * mass π c :=
          mul_le_mul_of_nonneg_left hmass hA
      _ = mass π c * regretAuth π c Vp α := by ring
      _ ≤ ε := hreg
  · push Not at hA
    nlinarith

open LogicalInduction in
/-- **Asymptotic form.**  If `RU n = p n · RA n`, `1 − η n ≤ p n`, `η → 0`, and activated
regret is asymptotically nonpositive, then conditional authoritative regret is
asymptotically nonpositive. -/
theorem regretAuth_asymptotic (RA RU p η : ℕ → ℝ)
    (hid : ∀ n, RU n = p n * RA n) (hp : ∀ n, 1 - η n ≤ p n)
    (hη : ConvergesTo η 0) (hRU : RU ≲ₙ fun _ => 0) :
    RA ≲ₙ fun _ => 0 := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hη (1/2) (by norm_num)
  filter_upwards [hRU (δ/2) hδ2, Filter.eventually_atTop.2 ⟨N, hN⟩] with n h1 h2
  have hηn : |η n| < 1/2 := by simpa [Real.dist_eq] using h2
  have hpn : 1/2 ≤ p n := by linarith [hp n, (abs_lt.1 hηn).2]
  show RA n ≤ 0 + δ
  have h1' : p n * RA n ≤ δ / 2 := by rw [← hid]; simpa using h1
  by_cases hA : 0 ≤ RA n
  · nlinarith
  · linarith

/-! ## 4. Perturbation: the quantitative-authorship interaction -/

omit [Fintype Q] [Nonempty Q] in
theorem expect_activated_sub_le (π : W → ℚ) (c : W → Bool) (V V' : Q → W → ℚ) (δ : ℚ)
    (hπ : ∀ w, 0 ≤ π w) (hδ : ∀ a w, c w = true → |V a w - V' a w| ≤ δ) (a : Q) :
    expect π (activated c V a) - expect π (activated c V' a) ≤ δ * mass π c := by
  unfold mass expect
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold activated ind
  by_cases hc : c w = true
  · simp only [hc, if_true, one_mul]
    have := (abs_le.mp (hδ a w hc)).2
    nlinarith [hπ w]
  · simp [hc]

/-- **Regret perturbation.**  Payoffs within `δ` on certified worlds have activated
regrets within `2·δ·mass`. -/
theorem regretU_perturb (π : W → ℚ) (c : W → Bool) (V V' : Q → W → ℚ) (α : W → Q → ℚ)
    (δ : ℚ) (hπ : ∀ w, 0 ≤ π w) (hα : ∀ w a, 0 ≤ α w a) (hα1 : ∀ w, ∑ a, α w a = 1)
    (hδ : ∀ a w, c w = true → |V a w - V' a w| ≤ δ) :
    regretU π c V α ≤ regretU π c V' α + 2 * δ * mass π c := by
  have hsup : (univ.sup' univ_nonempty fun a => expect π (activated c V a))
      ≤ (univ.sup' univ_nonempty fun a => expect π (activated c V' a)) + δ * mass π c := by
    refine Finset.sup'_le _ _ fun a _ => ?_
    have h1 := expect_activated_sub_le π c V V' δ hπ hδ a
    have h2 := Finset.le_sup' (fun a => expect π (activated c V' a)) (Finset.mem_univ a)
    linarith
  have hfoll : expect π (followed α (activated c V' ))
      - expect π (followed α (activated c V)) ≤ δ * mass π c := by
    unfold mass expect
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [followed_activated, followed_activated]
    unfold ind
    by_cases hc : c w = true
    · simp only [hc, if_true, one_mul]
      have hdiff : followed α V' w - followed α V w ≤ δ := by
        unfold followed
        rw [← Finset.sum_sub_distrib]
        calc ∑ b, (α w b * V' b w - α w b * V b w)
            = ∑ b, α w b * (V' b w - V b w) := by
              refine Finset.sum_congr rfl fun b _ => ?_; ring
          _ ≤ ∑ b, α w b * δ := Finset.sum_le_sum fun b _ =>
              mul_le_mul_of_nonneg_left (by
                have := (abs_le.mp (hδ b w hc)).1; linarith) (hα w b)
          _ = δ := by rw [← Finset.sum_mul, hα1 w, one_mul]
      nlinarith [hπ w]
    · simp [hc]
  unfold regretU
  linarith

end Workspace.Deference.Contrib.ActivatedValue

#print axioms Workspace.Deference.Contrib.ActivatedValue.activated_completion_congr
#print axioms Workspace.Deference.Contrib.ActivatedValue.completeBy_completion
#print axioms Workspace.Deference.Contrib.ActivatedValue.followed_activated
#print axioms Workspace.Deference.Contrib.ActivatedValue.expect_activated_eq_mass_mul
#print axioms Workspace.Deference.Contrib.ActivatedValue.expect_followed_activated_eq_mass_mul
#print axioms Workspace.Deference.Contrib.ActivatedValue.sup'_mul_left
#print axioms Workspace.Deference.Contrib.ActivatedValue.regretU_eq_mass_mul_regretAuth
#print axioms Workspace.Deference.Contrib.ActivatedValue.followed_excess_bounds
#print axioms Workspace.Deference.Contrib.ActivatedValue.sup'_add_bounds
#print axioms Workspace.Deference.Contrib.ActivatedValue.regretV_sub_regretU_abs_le
#print axioms Workspace.Deference.Contrib.ActivatedValue.availability_transfer_completion
#print axioms Workspace.Deference.Contrib.ActivatedValue.SharpLower.attained
#print axioms Workspace.Deference.Contrib.ActivatedValue.mass_eq
#print axioms Workspace.Deference.Contrib.ActivatedValue.regretAuth_le_div
#print axioms Workspace.Deference.Contrib.ActivatedValue.regretAuth_asymptotic
#print axioms Workspace.Deference.Contrib.ActivatedValue.regret_constant_completion
#print axioms Workspace.Deference.Contrib.ActivatedValue.regretU_perturb
