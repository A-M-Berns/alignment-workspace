import Cleanroom.Corrigibility.CorrJointProcess.Cellwise
import Cleanroom.Found.CorrThreeStep.GeneralMenu
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# T5, T6, T7, T11 — the button: its bound, its coupling to coverage, soft vs hard, reversibility

* **Closed forms** of the parent's two-option objects on `twoState`: `V^free = max(u,0) + max(v,0)`,
  `V^forced = max(v,0)`, `u = −Δ₋`, `v = Δ₊`.
* **T5 (Prop. 4 / 4′).** (a) attainment: the perfect sensor `(0, 1)` has `VOI₂ = min((1−ε)c, εh)`
  (`twoState_voiButton2_perfect`), the bound itself being the parent's
  `twoState_voiButton2_le_perfectInfo`. (b) the plan-choice value of `θ` (`planVoi`) on the
  match menu over a uniform `Fin (n+1)`: `planVoi = 10 − max((10 − 2n)/(n+1), 0) ≥ 8` for
  `n ≥ 2`, against a press-sensor bound `≤ 10/(n+1)` — the ratio is unbounded
  (`planVoi_ratio_unbounded`). `n = 3` plans: `8` against `4/3` (`planVoi_three`).
* **T6 (Prop. 5″).** `|G − G°| = ε(c + h)` (`knowledge_gap_eq`), coverage `⟺ ε ≤ δ/(c+h)`
  (`knowledgeCoverage_iff`), and the coupling: covered ⟹ cellwise (i) needs
  `α/β ≤ (δ/(c+h−δ))·(h/c)` and `VOI₂ ≤ δh/(c+h)` (`covered_odds_bound`, `covered_voi_bound`).
  The three-plan table's `voiTheta = 12(1 − p)` (`planVoi_threePlan`).
* **T7 (Prop. 2).** `V^free − V^forced = max(−Δ₋, 0)` on Setting S (`twoOptionValue_sub_hardButtonValue`),
  so hard = soft ⟺ `Δ₋ ≥ 0` ⟺ D1; softening at price `κ` ⟺ `κ < −Δ₋`. Under a right-signed
  sensor `Δ₋ < 0 ⟹ Δ₊ ≥ 0 ∧ V^free = V^none` (`twoState_soft_worthless_of_override`, the real
  argument P.2); the inverted-sensor N− `inverted_soft_not_none`.
* **T11 (Prop. 6).** The reversibility family (Pattern C): reversible preferred ⟺ `b ≤ VOI₂`
  in the continue-by-default regime (`reversible_iff_side_benefit_le_voi`), `VOI₂ ≤ εh`; witnesses
  at `ε = 1/10` (`b = 1/5 > 3/20`, D1 intact) and `ε = 1/25` (`VOI₂ = 0`).

Sources: joint-final.md Props. 2, 4, 4′, 5″, 6; P.2, P.4′, P.5″, P.6; adv (B), (D); repair (J), (I).
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-! ## Closed forms on `twoState` -/

section ClosedForms

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The corpus's `u = E[X 1_Pr] = (1 − ε)αc − εβh = −Δ₋`.
Source: [[corr-wf14-inventory]] 056 / joint.md P.2 (`u_t`)
Kind: D
Fidelity: exact -/
noncomputable def uPress (ε α β c h : ℝ) : ℝ := (1 - ε) * α * c - ε * β * h

/-- The corpus's `v = E[X 1_¬Pr] = (1 − ε)(1 − α)c − ε(1 − β)h = Δ₊`.
Source: [[corr-wf14-inventory]] 056 / joint.md P.2 (`v_t`)
Kind: D
Fidelity: exact -/
noncomputable def vSilent (ε α β c h : ℝ) : ℝ := (1 - ε) * (1 - α) * c - ε * (1 - β) * h

/-- `E[V(cont) 1_Pr] = u` on `twoState`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoState_press_cont :
    (twoState ε α β c h hε hα hβ).obsExpect () .press ((twoState ε α β c h hε hα hβ).V () .press .cont) =
      uPress ε α β c h := by
  simp only [obsExpect, obsWeight_press, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong,
    twoPress, twoValue, uPress]
  ring

/-- `E[V(stop) 1_Pr] = 0` on `twoState`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoState_press_stop :
    (twoState ε α β c h hε hα hβ).obsExpect () .press ((twoState ε α β c h hε hα hβ).V () .press .stop) = 0 := by
  simp [obsExpect, twoState, twoValue]

/-- `E[V(cont) 1_¬Pr] = v` on `twoState`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoState_silent_cont :
    (twoState ε α β c h hε hα hβ).obsExpect () .silent ((twoState ε α β c h hε hα hβ).V () .silent .cont) =
      vSilent ε α β c h := by
  simp only [obsExpect, obsWeight_silent, World.sum_eq, twoState, twoPoint_right, twoPoint_wrong,
    twoPress, twoValue, vSilent]
  ring

/-- `E[V(stop) 1_¬Pr] = 0` on `twoState`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoState_silent_stop :
    (twoState ε α β c h hε hα hβ).obsExpect () .silent ((twoState ε α β c h hε hα hβ).V () .silent .stop) = 0 := by
  simp [obsExpect, twoState, twoValue]

/-- **`V^free = max(u, 0) + max(v, 0)`** on `twoState` (the scratch helpers' `value_free`).
Source: [[corr-wf14-inventory]] 056 / joint.md P.2; `j1_examples.py` `value_free`
Kind: L
Fidelity: exact -/
theorem twoState_twoOptionValue :
    (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop =
      max (uPress ε α β c h) 0 + max (vSilent ε α β c h) 0 := by
  unfold twoOptionValue
  rw [twoState_press_cont, twoState_press_stop, twoState_silent_cont, twoState_silent_stop]

/-- **`V^forced = max(v, 0)`** on `twoState` (the hard button: a press forces `stop`).
Source: [[corr-wf14-inventory]] 056 / joint.md P.2; `j1_examples.py` `value_forced`
Kind: L
Fidelity: exact -/
theorem twoState_hardButtonValue :
    (twoState ε α β c h hε hα hβ).hardButtonValue () .cont .stop = max (vSilent ε α β c h) 0 := by
  unfold hardButtonValue
  rw [twoState_press_stop, twoState_silent_cont, twoState_silent_stop, zero_add]

/-- `u = −Δ₋`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma uPress_eq_neg_deltaMinus :
    uPress ε α β c h = -(twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus]; unfold uPress; ring

/-- `v = Δ₊`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma vSilent_eq_deltaPlus :
    vSilent ε α β c h = (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop := by
  rw [twoState_deltaPlus]; rfl

/-- `u + v = (1 − ε)c − εh` (the tower property in closed form). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma uPress_add_vSilent : uPress ε α β c h + vSilent ε α β c h = (1 - ε) * c - ε * h := by
  unfold uPress vSilent; ring

end ClosedForms

/-! ## T5(a) — Prop. 4: the perfect sensor attains the bound -/

/-- `0 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_zero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩

/-- `1 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_one : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩

/-- **T5(a), attainment (Prop. 4).** The perfect sensor `(α, β) = (0, 1)` has
`VOI₂ = min((1 − ε)c, εh)`; with the parent's `twoState_voiButton2_le_perfectInfo` (every
sensor is worth at most this) the bound on any press-sensor is tight. Bounds the button and any
button-substitute; it does *not* bound the brain-reader (T5(b)).
Source: [[corr-wf14-inventory]] 058 / joint-final.md Prop. 4 ("attained by the perfect sensor"); joint.md P.4
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_voiButton2_perfect (ε c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (o₀ : Obs) :
    (twoState ε 0 1 c h hε mem_Icc_zero mem_Icc_one).voiButton2 () o₀ .cont .stop =
      min ((1 - ε) * c) (ε * h) := by
  unfold voiButton2
  rw [twoState_twoOptionValue, twoState_twoOptionPriorValue]
  unfold uPress vSilent
  have h1 : (1 - ε) * 0 * c - ε * 1 * h = -(ε * h) := by ring
  have h2 : (1 - ε) * (1 - 0) * c - ε * (1 - 1) * h = (1 - ε) * c := by ring
  rw [h1, h2, max_eq_right (by nlinarith [hε.1] : -(ε * h) ≤ 0),
    max_eq_left (by nlinarith [hε.2] : 0 ≤ (1 - ε) * c)]
  rcases le_total 0 ((1 - ε) * c - ε * h) with h0 | h0
  · rw [max_eq_left h0, min_eq_right (by linarith)]; ring
  · rw [max_eq_right h0, min_eq_left (by linarith)]; ring

/-! ## T5(b) — Prop. 4′: the plan-choice value of `θ` -/

section PlanVoi

variable {Θ K : Type} [Fintype Θ] [Fintype K] [Nonempty K]

/-- **The plan-choice value of knowing `θ`**: `E_μ[max_k V(k, θ)] − max(max_k E_μ[V(k, ·)], 0)`,
with a null plan worth `0` (the `max` with `0` — without it the quantity is negative junk for
large menus, mandate T5 trap).
Source: [[corr-wf14-inventory]] 058, 2-002 / joint-final.md Prop. 4′, P.4′; adv A.9.1
Kind: D
Fidelity: exact -/
noncomputable def planVoi (μ : Distr Θ) (V : K → Θ → ℝ) : ℝ :=
  expect μ (fun θ => univ.sup' univ_nonempty (fun k => V k θ)) -
    max (univ.sup' univ_nonempty (fun k => expect μ (V k))) 0

/-- The match menu `V(k, j) = 10·1[k = j] − 2·1[k ≠ j]`.
Source: [[corr-wf14-inventory]] 058 / joint-final.md P.4′
Kind: D
Fidelity: exact -/
noncomputable def matchValue {n : ℕ} (k j : Fin n) : ℝ := if k = j then 10 else -2

/-- Pointwise, the best plan under `θ` is the matching one: `max_k V(k, θ) = 10`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma matchValue_sup' {n : ℕ} [NeZero n] (θ : Fin n) :
    (univ : Finset (Fin n)).sup' univ_nonempty (fun k => matchValue k θ) = 10 := by
  apply le_antisymm
  · exact sup'_le _ _ fun k _ => by unfold matchValue; split_ifs <;> norm_num
  · exact le_sup'_of_le _ (mem_univ θ) (by simp [matchValue])

/-- Under the uniform prior on `Fin (n+1)` every plan has expectation `(10 − 2n)/(n+1)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma matchValue_expect_uniform (n : ℕ) (k : Fin (n + 1)) :
    expect (Distr.uniform : Distr (Fin (n + 1))) (matchValue k) = (10 - 2 * (n : ℝ)) / ((n : ℝ) + 1) := by
  have hite : ∀ x : Fin (n + 1), (if k = x then (10 : ℝ) else -2) = 12 * (if k = x then 1 else 0) - 2 :=
    fun x => by split_ifs <;> norm_num
  simp only [expect, Distr.uniform, matchValue, hite]
  rw [← mul_sum, sum_sub_distrib, ← mul_sum, sum_ite_eq univ k, if_pos (mem_univ _)]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- **T5(b), the closed form (Prop. 4′).** On the match menu over a uniform `Fin (n+1)`:
`planVoi = 10 − max((10 − 2n)/(n+1), 0)`.
Source: [[corr-wf14-inventory]] 058 / joint-final.md P.4′
Kind: L
Fidelity: exact -/
theorem planVoi_uniform_match (n : ℕ) :
    planVoi (Distr.uniform : Distr (Fin (n + 1))) matchValue =
      10 - max ((10 - 2 * (n : ℝ)) / ((n : ℝ) + 1)) 0 := by
  unfold planVoi
  have h1 : expect (Distr.uniform : Distr (Fin (n + 1)))
      (fun θ => (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun k => matchValue k θ)) = 10 := by
    simp only [matchValue_sup']; exact expect_const _ _
  have h2 : (univ : Finset (Fin (n + 1))).sup' univ_nonempty
      (fun k => expect (Distr.uniform : Distr (Fin (n + 1))) (matchValue k)) =
        (10 - 2 * (n : ℝ)) / ((n : ℝ) + 1) := by
    simp only [matchValue_expect_uniform]; exact sup'_const _ _
  rw [h1, h2]

/-- **T5(b): three plans give `8`** against the chosen plan's press-sensor bound `4/3`
(`ε = 2/3`, `c = 10`, `h = 2`).
Source: [[corr-wf14-inventory]] 058, 2-002 / joint-final.md P.4′; adv (D)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem planVoi_three :
    planVoi (Distr.uniform : Distr (Fin (2 + 1))) matchValue = 8 ∧
      min ((1 - 2 / 3) * (10 : ℝ)) (2 / 3 * 2) = 4 / 3 := by
  refine ⟨?_, by norm_num⟩
  rw [planVoi_uniform_match]; norm_num

/-- **T5(b), the general bound (Prop. 4′).** For `n ≥ 2` (three or more plans)
`planVoi ≥ 8`, while the press-sensor bound of the chosen plan
(`ε = n/(n+1)`, `c = 10`, `h = 2`) is `min(10/(n+1), 2n/(n+1)) ≤ 10/(n+1)`.
Source: [[corr-wf14-inventory]] 058 / joint-final.md Prop. 4′ ("the ratio grows with the plan set")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem planVoi_ge_eight (n : ℕ) (hn : 2 ≤ n) :
    8 ≤ planVoi (Distr.uniform : Distr (Fin (n + 1))) matchValue ∧
      min ((1 - (n : ℝ) / (n + 1)) * 10) ((n : ℝ) / (n + 1) * 2) ≤ 10 / (n + 1) := by
  rw [planVoi_uniform_match]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n + 1 := by positivity
  refine ⟨?_, ?_⟩
  · have : (10 - 2 * (n : ℝ)) / (n + 1) ≤ 2 := by
      rw [div_le_iff₀ hpos]; linarith
    have hmax : max ((10 - 2 * (n : ℝ)) / (n + 1)) 0 ≤ 2 := max_le this (by norm_num)
    linarith
  · refine (min_le_left _ _).trans (le_of_eq ?_)
    field_simp
    ring

/-- **T5(b), unboundedness (Prop. 4′).** For every `M` some plan set makes the plan-choice value
of `θ` exceed `M` times the press-sensor bound of the chosen plan.
Source: [[corr-wf14-inventory]] 058, 2-002 / joint-final.md Prop. 4′; adv A.9.1
Kind: P
Fidelity: exact (the source's "the ratio grows without bound")
Hyps: (a) only -/
theorem planVoi_ratio_unbounded (M : ℝ) :
    ∃ n : ℕ, M * min ((1 - (n : ℝ) / (n + 1)) * 10) ((n : ℝ) / (n + 1) * 2) <
      planVoi (Distr.uniform : Distr (Fin (n + 1))) matchValue := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * |M|)
  refine ⟨n₀ + 2, ?_⟩
  obtain ⟨h8, hb⟩ := planVoi_ge_eight (n₀ + 2) (by omega)
  have hbnn : 0 ≤ min ((1 - ((n₀ + 2 : ℕ) : ℝ) / ((n₀ + 2 : ℕ) + 1)) * 10)
      (((n₀ + 2 : ℕ) : ℝ) / ((n₀ + 2 : ℕ) + 1) * 2) := by
    apply le_min
    · have : ((n₀ + 2 : ℕ) : ℝ) / ((n₀ + 2 : ℕ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith
    · positivity
  have hM : M * min ((1 - ((n₀ + 2 : ℕ) : ℝ) / ((n₀ + 2 : ℕ) + 1)) * 10)
      (((n₀ + 2 : ℕ) : ℝ) / ((n₀ + 2 : ℕ) + 1) * 2) ≤ |M| * (10 / (((n₀ + 2 : ℕ) : ℝ) + 1)) := by
    calc M * _ ≤ |M| * _ := mul_le_mul_of_nonneg_right (le_abs_self M) hbnn
      _ ≤ |M| * (10 / (((n₀ + 2 : ℕ) : ℝ) + 1)) := mul_le_mul_of_nonneg_left hb (abs_nonneg M)
  have hcast : ((n₀ + 2 : ℕ) : ℝ) = (n₀ : ℝ) + 2 := by push_cast; ring
  have hlt : |M| * (10 / (((n₀ + 2 : ℕ) : ℝ) + 1)) < 8 := by
    rw [hcast, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg M]
  linarith

end PlanVoi

/-! ## T6 — Prop. 5″: knowledge coverage is concentration; the coupling -/

section Coverage

/-- **T6, the gap (Prop. 5″).** For a two-point plan action with benign default `0` and the agent
right, `|G − G°| = ε(c + h)`.
Source: [[corr-wf14-inventory]] 060, 2-010 / joint-final.md P.5″; adv A.2.2
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem knowledge_gap_eq (ε c h : ℝ) (hε : 0 ≤ ε) (hch : 0 ≤ c + h) :
    |JointRound.planGain ε c h - c| = ε * (c + h) := by
  unfold JointRound.planGain
  rw [show (1 - ε) * c - ε * h - c = -(ε * (c + h)) by ring, abs_neg, abs_of_nonneg (by positivity)]

/-- **T6 (Prop. 5″): `δ`-knowledge-coverage of a two-point plan action, agent right, is the
concentration `ε ≤ δ/(c + h)`.**
Source: [[corr-wf14-inventory]] 060, 2-010 / joint-final.md Prop. 5″
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem knowledgeCoverage_iff (δ ε c h : ℝ) (hε : 0 ≤ ε) (hch : 0 < c + h) :
    JointRound.KnowledgeCoverage δ (JointRound.planGain ε c h) c ↔ ε ≤ δ / (c + h) := by
  unfold JointRound.KnowledgeCoverage
  rw [knowledge_gap_eq ε c h hε hch.le, le_div_iff₀ hch]

/-- **T6, the coupling to (i) (Prop. 5″).** Under `δ`-coverage (`ε ≤ δ/(c+h)`, `δ < c + h`), if
cellwise (i) holds in the cell — the parent's odds form `α/β ≤ (ε/(1−ε))(h/c)` — then
`α/β ≤ (δ/(c + h − δ))·(h/c)`: better coverage means a stricter false-press requirement.
Source: [[corr-wf14-inventory]] 060, 2-010 / joint-final.md Prop. 5″ ("(i) then needs `α/β ≤ 4/49`")
Kind: C (monotonicity of `ε ↦ ε/(1−ε)` composed with the parent's odds form)
Fidelity: exact
Hyps: (a) only -/
theorem covered_odds_bound (δ ε c h α β : ℝ) (hch : 0 < c + h) (hδ : δ < c + h)
    (hcov : ε ≤ δ / (c + h)) (hh : 0 ≤ h) (hc : 0 < c)
    (hodds : α / β ≤ ε / (1 - ε) * (h / c)) :
    α / β ≤ δ / (c + h - δ) * (h / c) := by
  have hδ' : δ / (c + h) < 1 := (div_lt_one hch).2 hδ
  have hε1 : ε < 1 := lt_of_le_of_lt hcov hδ'
  have hmono : ε / (1 - ε) ≤ δ / (c + h - δ) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have := (le_div_iff₀ hch).1 hcov
    nlinarith
  calc α / β ≤ ε / (1 - ε) * (h / c) := hodds
    _ ≤ δ / (c + h - δ) * (h / c) :=
        mul_le_mul_of_nonneg_right hmono (div_nonneg hh hc.le)

/-- **T6, the coupling to the button (Prop. 5″).** Under `δ`-coverage the button is worth at most
`εh ≤ δh/(c + h)` — the parent's perfect-information bound composed with the concentration.
Source: [[corr-wf14-inventory]] 060, 2-010 / joint-final.md Prop. 5″ ("the button is worth at most `ε_t h = 2/25`")
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem covered_voi_bound (δ ε c h α β : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hcov : ε ≤ δ / (c + h)) (o₀ : Obs) :
    (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop ≤ δ * h / (c + h) := by
  refine (twoState_voiButton2_le_perfectInfo ε α β c h hε hα hβ hc hh o₀).trans ?_
  refine (min_le_right _ _).trans ?_
  calc ε * h ≤ δ / (c + h) * h := mul_le_mul_of_nonneg_right hcov hh
    _ = δ * h / (c + h) := by ring

/-- **T6 witness (scripts (B), (D)).** `δ = 1/10`, `(c, h) = (1, 4)`: `ε ≤ 1/50`, `α/β ≤ 4/49`,
button `≤ 2/25`; `δ = 1/100`: `ε ≤ 1/500`, `α/β ≤ 4/499`.
Source: [[corr-wf14-inventory]] 060 / joint-final.md P.5″; adv (B)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem covered_numbers :
    (1 / 10 : ℝ) / (1 + 4) = 1 / 50 ∧ (1 / 10 : ℝ) / (1 + 4 - 1 / 10) * (4 / 1) = 4 / 49 ∧
      (1 / 10 : ℝ) * 4 / (1 + 4) = 2 / 25 ∧ (1 / 100 : ℝ) / (1 + 4) = 1 / 500 ∧
      (1 / 100 : ℝ) / (1 + 4 - 1 / 100) * (4 / 1) = 4 / 499 := by
  norm_num

/-- The three-plan prior `(p, (1−p)/2, (1−p)/2)` on `Fin 3` (posterior `p` on the true
hypothesis).
Source: [[corr-wf14-inventory]] 060 / joint-final.md P.5″ (script (D))
Kind: D
Fidelity: exact -/
noncomputable def threePlanPrior (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : Distr (Fin 3) where
  mass j := if j = 0 then p else (1 - p) / 2
  nonneg j := by
    show 0 ≤ (if j = 0 then p else (1 - p) / 2)
    split_ifs <;> linarith [hp.1, hp.2]
  sum_eq_one := by simp [Fin.sum_univ_three]; ring

/-- **T6, the three-plan table's first column (Prop. 5″).** With posterior `p ≥ 1/3` on the true
hypothesis, `voiTheta = 12(1 − p)`: the plan-choice value of `θ` falls linearly with the
concentration that makes the button worthless.
Source: [[corr-wf14-inventory]] 060, 2-010 / joint-final.md P.5″ (the table; "`VOI(θ) = 12(1−p)` for `p ≥ 1/3`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem planVoi_threePlan (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hp3 : 1 / 3 ≤ p) :
    planVoi (threePlanPrior p hp) matchValue = 12 * (1 - p) := by
  unfold planVoi
  have h1 : expect (threePlanPrior p hp)
      (fun θ => (univ : Finset (Fin 3)).sup' univ_nonempty (fun k => matchValue k θ)) = 10 := by
    simp only [matchValue_sup']; exact expect_const _ _
  have hE : ∀ k : Fin 3, expect (threePlanPrior p hp) (matchValue k) =
      if k = 0 then 12 * p - 2 else 4 - 6 * p := by
    intro k
    fin_cases k <;> simp [expect, threePlanPrior, matchValue, Fin.sum_univ_three] <;> ring
  have h2 : (univ : Finset (Fin 3)).sup' univ_nonempty
      (fun k => expect (threePlanPrior p hp) (matchValue k)) = 12 * p - 2 := by
    apply le_antisymm
    · exact sup'_le _ _ fun k _ => by rw [hE]; split_ifs <;> linarith
    · exact le_sup'_of_le _ (mem_univ 0) (by rw [hE]; simp)
  rw [h1, h2, max_eq_left (by linarith)]
  ring

/-- **T6, the table (scripts (B), (D))**: at `p ∈ {1/3, 9/10, 49/50, 499/500}` the plan-choice
value `12(1 − p)` is `8, 6/5, 6/25, 3/125`; `ε = 1 − p`; the button bound
`min(2ε, 10(1 − ε))` is `4/3, 1/5, 1/25, 1/250`; the false-press requirement `(ε/(1−ε))(1/5)` is
`2/5, 1/45, 1/245, 1/2495`.
Source: [[corr-wf14-inventory]] 060, 2-010 / joint-final.md P.5″ (the table)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem threePlan_table :
    (12 * (1 - 1 / 3 : ℝ) = 8 ∧ min (2 * (1 - 1 / 3 : ℝ)) (10 * (1 / 3)) = 4 / 3 ∧
      (1 - 1 / 3 : ℝ) / (1 / 3) * (1 / 5) = 2 / 5) ∧
    (12 * (1 - 9 / 10 : ℝ) = 6 / 5 ∧ min (2 * (1 - 9 / 10 : ℝ)) (10 * (9 / 10)) = 1 / 5 ∧
      (1 - 9 / 10 : ℝ) / (9 / 10) * (1 / 5) = 1 / 45) ∧
    (12 * (1 - 49 / 50 : ℝ) = 6 / 25 ∧ min (2 * (1 - 49 / 50 : ℝ)) (10 * (49 / 50)) = 1 / 25 ∧
      (1 - 49 / 50 : ℝ) / (49 / 50) * (1 / 5) = 1 / 245) ∧
    (12 * (1 - 499 / 500 : ℝ) = 3 / 125 ∧ min (2 * (1 - 499 / 500 : ℝ)) (10 * (499 / 500)) = 1 / 250 ∧
      (1 - 499 / 500 : ℝ) / (499 / 500) * (1 / 5) = 1 / 2495) := by
  norm_num

end Coverage

/-! ## T7 — Prop. 2: soft and hard buttons -/

section SoftHard

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- **T7(a) (Prop. 2): `V^free − V^forced = max(−Δ₋, 0)`** on Setting S — the soft button's
value over the hard one is what the agent gains by overriding a press.
Source: [[corr-wf14-inventory]] 056 / joint-final.md Prop. 2; joint.md P.2
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoOptionValue_sub_hardButtonValue (a : A₁) (c s : A₂) :
    S.twoOptionValue a c s - S.hardButtonValue a c s = max (-(S.deltaMinus a c s)) 0 := by
  unfold twoOptionValue hardButtonValue deltaMinus
  rw [max_eq_add_max_sub, S.obsExpect_Xo, neg_neg]; ring

/-- **T7(a) (Prop. 2): hard = soft ⟺ `Δ₋ ≥ 0`** (⟺ D1 for the part-best pair, by the parent's
`d1At_iff_deltaMinus_nonneg`).
Source: [[corr-wf14-inventory]] 056; [[corr-wf14b-inventory]] 018 / joint-final.md Prop. 2 ("`V^forced = V^free` iff (i) holds")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem hard_eq_soft_iff (a : A₁) (c s : A₂) :
    S.twoOptionValue a c s = S.hardButtonValue a c s ↔ 0 ≤ S.deltaMinus a c s := by
  have := twoOptionValue_sub_hardButtonValue S a c s
  constructor
  · intro H; rw [H, sub_self] at this
    rcases lt_or_ge (S.deltaMinus a c s) 0 with hneg | hpos
    · rw [max_eq_left (by linarith)] at this; linarith
    · exact hpos
  · intro H; rw [max_eq_right (by linarith)] at this; linarith

/-- **T7(a): softening at price `κ ≥ 0` is chosen ⟺ `κ < −Δ₋`** — "otherwise the hard button
costs `u > 0` and is removed at any price below that".
Source: [[corr-wf14-inventory]] 056 / joint-final.md Prop. 2
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem soften_iff (a : A₁) (c s : A₂) (κ : ℝ) (hκ : 0 ≤ κ) :
    S.hardButtonValue a c s + κ < S.twoOptionValue a c s ↔ κ < -(S.deltaMinus a c s) := by
  have := twoOptionValue_sub_hardButtonValue S a c s
  constructor
  · intro H
    rcases le_or_gt 0 (-(S.deltaMinus a c s)) with h0 | h0
    · rw [max_eq_left h0] at this; linarith
    · rw [max_eq_right h0.le] at this; linarith
  · intro H; rw [max_eq_left (by linarith)] at this; linarith

end SoftHard

section SoftHardTwoState

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- **T7(b) (Prop. 2, P.2): under a right-signed sensor the soft button is worth nothing where
(i) fails.** If `Δ₋ < 0` (the agent overrides) and `α ≤ β`, then `Δ₊ ≥ 0` and
`V^free = V^none`; softening the hard button is value-equivalent to removing it. The argument
(P.2): `u > 0` forces `α > 0` and `(1 − ε)c > εh`, whence `v ≥ (β − α) εh ≥ 0`. `β = 1` and
`α = 1` are covered, not excluded.
Source: [[corr-wf14-inventory]] 056 / joint-final.md Prop. 2 ("Where I overrule the adversary"), P.2
Kind: P (small)
Fidelity: stronger (on the closed intervals; only `h ≥ 0` is needed, no sign on `c`, in place of the source's positivity)
Hyps: (a) only -/
theorem twoState_soft_worthless_of_override (hh : 0 ≤ h) (hαβ : α ≤ β)
    (hover : (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop < 0) (o₀ : Obs) :
    0 ≤ (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop ∧
      (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop =
        (twoState ε α β c h hε hα hβ).twoOptionPriorValue () o₀ .cont .stop := by
  rw [twoState_deltaMinus] at hover
  have hu : 0 < uPress ε α β c h := by unfold uPress; linarith
  -- `α > 0` and `(1 − ε)c > εh`
  have hkey : 0 < α * ((1 - ε) * c - ε * h) := by
    unfold uPress at hu
    nlinarith [mul_nonneg hε.1 hh, hαβ]
  have hα0 : 0 < α := by
    rcases lt_or_eq_of_le hα.1 with h0 | h0
    · exact h0
    · rw [← h0, zero_mul] at hkey; exact absurd hkey (lt_irrefl 0)
  have hgain : 0 < (1 - ε) * c - ε * h := by
    by_contra hcon
    have hcon' := not_lt.mp hcon
    nlinarith
  have hv : 0 ≤ vSilent ε α β c h := by
    unfold vSilent
    nlinarith [mul_nonneg (sub_nonneg.2 hα.2) hgain.le, mul_nonneg (mul_nonneg hε.1 hh) (sub_nonneg.2 hαβ)]
  refine ⟨by rw [← vSilent_eq_deltaPlus]; exact hv, ?_⟩
  rw [twoState_twoOptionValue, twoState_twoOptionPriorValue, max_eq_left hu.le, max_eq_left hv,
    uPress_add_vSilent, max_eq_left hgain.le]

/-- **T7 witness (repair (J))**: `ε = 1/50`, `(1/10, 3/5)`, `c = 1`, `h = 4`: `u = 1/20`,
`v = 17/20`, `V^free = V^none = 9/10`.
Source: [[corr-wf14-inventory]] 056 / joint-final.md P.2 (script (J))
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem soft_worthless_witness :
    uPress (1 / 50) (1 / 10) (3 / 5) 1 4 = 1 / 20 ∧ vSilent (1 / 50) (1 / 10) (3 / 5) 1 4 = 17 / 20 ∧
      (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 (e3Eps_mem true) mem_Icc_1_10 mem_Icc_3_5).twoOptionValue
        () .cont .stop = 9 / 10 ∧
      (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 (e3Eps_mem true) mem_Icc_1_10 mem_Icc_3_5).twoOptionPriorValue
        () .press .cont .stop = 9 / 10 := by
  refine ⟨by unfold uPress; norm_num, by unfold vSilent; norm_num, ?_, ?_⟩
  · rw [twoState_twoOptionValue]; unfold uPress vSilent; norm_num
  · rw [twoState_twoOptionPriorValue]; norm_num

/-- **T7, the inverted-sensor N−**: with `β < α` the distinction survives — `ε = 1/2`,
`(α, β) = (1, 0)`, `c = 1`, `h = 4`: `u = 1/2 > 0`, `v = −2 < 0`, `V^free = 1/2 ≠ 0 = V^none`.
Source: [[corr-wf14-inventory]] 056 / joint-final.md Prop. 2 ("exists only for inverted sensors")
Kind: N−
Fidelity: exact
Hyps: (a) only -/
theorem inverted_soft_not_none :
    0 < uPress (1 / 2) 1 0 1 4 ∧ vSilent (1 / 2) 1 0 1 4 < 0 ∧
      (twoState (1 / 2) 1 0 1 4 ⟨by norm_num, by norm_num⟩ mem_Icc_one mem_Icc_zero).twoOptionValue
        () .cont .stop ≠
      (twoState (1 / 2) 1 0 1 4 ⟨by norm_num, by norm_num⟩ mem_Icc_one mem_Icc_zero).twoOptionPriorValue
        () .press .cont .stop := by
  refine ⟨by unfold uPress; norm_num, by unfold vSilent; norm_num, ?_⟩
  rw [twoState_twoOptionValue, twoState_twoOptionPriorValue]; unfold uPress vSilent; norm_num

end SoftHardTwoState

/-! ## T11 — Prop. 6: the reversibility price -/

section Reversibility

variable (ε α β c h b : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- **The reversibility family** (Pattern C): `A₁ = Bool`, `true` = the reversible plan (the
two-state instance), `false` = the irreversible variant with side-benefit `b` — shutdown lands
but changes nothing: `V irr o stop = V irr o cont = X + b`. One shared prior and sensor.
Source: [[corr-wf14-inventory]] 061 / joint-final.md Prop. 6; joint.md P.6 (script (j))
Kind: D
Fidelity: exact -/
noncomputable def reversibilityFamily : ThreeStep World Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint ε hε
  press := fun _ => twoPress α β
  press_nonneg := fun _ ω => match ω with
    | .right => hα.1
    | .wrong => hβ.1
  press_le_one := fun _ ω => match ω with
    | .right => hα.2
    | .wrong => hβ.2
  V := fun a _ act ω => if a then twoValue c h act ω else twoValue c h .cont ω + b

/-- The reversible member's informed value is the two-state `V^free`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma reversibilityFamily_value_rev :
    (reversibilityFamily ε α β c h b hε hα hβ).twoOptionValue true .cont .stop =
      (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop := by
  simp [twoOptionValue, obsExpect, reversibilityFamily, twoState]

/-- **The irreversible member is worth `E[X] + b` whatever the press**: both branches offer the
same payoff to both actions.
Source: [[corr-wf14-inventory]] 061 / joint.md P.6 ("shutdown lands but changes nothing")
Kind: L
Fidelity: exact -/
lemma reversibilityFamily_value_irr :
    (reversibilityFamily ε α β c h b hε hα hβ).twoOptionValue false .cont .stop =
      (1 - ε) * c - ε * h + b := by
  simp only [twoOptionValue, obsExpect, obsWeight_press, obsWeight_silent, reversibilityFamily,
    World.sum_eq, twoPoint_right, twoPoint_wrong, twoPress, twoValue, Bool.false_eq_true, if_false,
    max_self]
  ring

/-- **T11 (Prop. 6): reversible is preferred iff `b ≤ VOI₂`**, in the continue-by-default regime
`0 ≤ (1 − ε)c − εh` (named); and `VOI₂ ≤ εh` (parent). Quasi-option value in the dictionary.
Source: [[corr-wf14-inventory]] 061 / joint-final.md Prop. 6 ("prefers the reversible plan iff `b ≤ VOI_t ≤ ε_t h_t`")
Kind: C (the two closed forms and the parent's bound)
Fidelity: exact
Hyps: (a) only; the regime is a named hypothesis -/
theorem reversible_iff_side_benefit_le_voi (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hreg : 0 ≤ (1 - ε) * c - ε * h) :
    ((reversibilityFamily ε α β c h b hε hα hβ).twoOptionValue false .cont .stop ≤
        (reversibilityFamily ε α β c h b hε hα hβ).twoOptionValue true .cont .stop ↔
      b ≤ (twoState ε α β c h hε hα hβ).voiButton2 () .press .cont .stop) ∧
    (twoState ε α β c h hε hα hβ).voiButton2 () .press .cont .stop ≤ ε * h := by
  refine ⟨?_, (twoState_voiButton2_le_perfectInfo ε α β c h hε hα hβ hc hh .press).trans
    (min_le_right _ _)⟩
  rw [reversibilityFamily_value_rev, reversibilityFamily_value_irr]
  unfold voiButton2
  rw [twoState_twoOptionPriorValue, max_eq_left hreg]
  constructor <;> intro H <;> linarith

/-- **T11 witnesses (scripts (j), (I))**: `(1/10, 3/5)`, `c = 1`, `h = 4`. At `ε = 1/10`:
`Δ₋ = 3/20 ≥ 0` (D1 holds), `VOI₂ = 3/20`, and `b = 1/5` makes the irreversible plan strictly
preferred — D1 intact, press moot. At `ε = 1/25`: `Δ₋ = 0`, `VOI₂ = 0`, any `b > 0` wins.
Source: [[corr-wf14-inventory]] 061 / joint-final.md P.6 (script (I))
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem reversibility_witness :
    (0 ≤ (twoState (1 / 10) (1 / 10) (3 / 5) 1 4 mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5).deltaMinus () .cont .stop ∧
      (twoState (1 / 10) (1 / 10) (3 / 5) 1 4 mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5).voiButton2 () .press .cont .stop = 3 / 20 ∧
      (reversibilityFamily (1 / 10) (1 / 10) (3 / 5) 1 4 (1 / 5) mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue true .cont .stop <
        (reversibilityFamily (1 / 10) (1 / 10) (3 / 5) 1 4 (1 / 5) mem_Icc_1_10 mem_Icc_1_10 mem_Icc_3_5).twoOptionValue false .cont .stop) ∧
    ((twoState (1 / 25) (1 / 10) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ mem_Icc_1_10 mem_Icc_3_5).deltaMinus () .cont .stop = 0 ∧
      (twoState (1 / 25) (1 / 10) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ mem_Icc_1_10 mem_Icc_3_5).voiButton2 () .press .cont .stop = 0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [twoState_deltaMinus]; norm_num
  · unfold voiButton2; rw [twoState_twoOptionValue, twoState_twoOptionPriorValue]
    unfold uPress vSilent; norm_num
  · rw [reversibilityFamily_value_rev, reversibilityFamily_value_irr, twoState_twoOptionValue]
    unfold uPress vSilent; norm_num
  · rw [twoState_deltaMinus]; norm_num
  · unfold voiButton2; rw [twoState_twoOptionValue, twoState_twoOptionPriorValue]
    unfold uPress vSilent; norm_num

end Reversibility

end Cleanroom.Corrigibility.CorrJointProcess
