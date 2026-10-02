import Cleanroom.Found.CorrThreeStep.TwoState
import Cleanroom.Found.CorrThreeStep.Identities
import Cleanroom.Trust.TtFiniteFrames.Sensors
import Cleanroom.Corrigibility.CorrOsgChai.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# The press as a Blackwell experiment: monotonicity of the agent's value in the sensor, and
binary-sensor dominance (D4, T15, T16, T7(f))

Package `corr-osg-chai`. **D4** `pressExperiment S a : Experiment Ω (Fin 2)` is the three-step
agent's sensor as a finite experiment of record (`lit-ddb-frames`): signal `0` = press with
likelihood `press a ω`, signal `1` = silence. On `twoState` it is `tt-finite-frames`'s
`binarySensor α β` up to the world relabeling `right ↦ 0, wrong ↦ 1`
(`twoState_pressExperiment_k`).

* **T15, the bridge** (`twoOptionValue_eq_bayesValue`): under A1 the two-option informed value
  is the Bayes value of the press experiment for the prior `(S.μ a).mass` and the menu
  `![V c, V s]` (`bayesValue_two`: a two-signal Bayes value is a sum of two maxima); and, for
  the full menu (`obsMax_add_eq_bayesValue`, via `bayesValue_two_signal` on any `n + 1`-option
  menu), `obsMax press + obsMax silent` is the Bayes value for the menu `V ∘ e` under any
  enumeration `e : Fin (n + 1) ↠ A₂` (repair round 1: the mandate's second bridge). Hence
  **Blackwell monotonicity** (`twoOptionValue_le_of_blackwellLE`, `voiButton2_le_of_blackwellLE`,
  and on the full menu `voiButton_le_of_blackwellLE`): garbling the sensor (same prior, same
  values) never raises the agent's value or its value of the button — from
  `tt-finite-frames`'s `moreValuable_of_blackwellLE`, never re-proved. On `twoState`: weakly decreasing on the parallelogram
  (`twoState_twoOptionValue_mono`), equal on the relabeling (`bayesValue_binarySensor_swap`),
  and the constant sensor gives the no-button value (`twoState_twoOptionValue_const`). "Never
  pays to garble" is `never_pays_for_garbling` instantiated
  (`twoOptionValue_garbled_sub_cost_lt`). This monotonicity is the formal content of the
  corrected §2.7 desideratum "no delegitimizing interference".
* **T7(f)** (`bayesValue_binarySensor_swap`, `inverted_perfect_blackwell_equiv`): the sensor
  `(1 − α, 1 − β)` has the same information content as `(α, β)` (the swap channel both ways),
  so the File Deletion cell-`L` sensor `(1, 0)` is Blackwell-equivalent to the perfect
  right-sign sensor `(0, 1)`.
* **T16(a)** (`inParallelogram_iff_ratios`): for right-sign sensors (`α ≤ β`, `α' ≤ β'`),
  `(α, β)` is a garbling of `(α', β')` iff both likelihood ratios improve, in product form
  `α'β ≤ αβ'` and `(1 − β')(1 − α) ≤ (1 − β)(1 − α')`; the `α > β` failure is shipped as N−
  (`ratios_not_sufficient_wrong_sign`). **T16(b)** witnesses: `(3/10, 9/10)` and `(1/20, 1/2)`
  incomparable both ways; `(1/10, 3/5)` a garbling of `(1/50, 3/5)` with
  `p, q = 137/145, 12/145`. **T16(c)** ("Theorem A(d) killed"): for `α' < α ≤ β < 1`, `(α', β)` is
  not a garbling of `(α, β)` (`not_inParallelogram_lower_alpha`) while `(α, β)` is one of
  `(α', β)` (`inParallelogram_lower_alpha`): lowering the false-press rate at fixed `β` is a
  strict Blackwell improvement; on `twoState (1/10) (1/10) (3/5) 1 4` vs `α' = 0` the two-option
  value rises from `13/20` to `37/50`, and at `ε = 1/50`, `α' = 1/50` by `71/2500` with `Δ₋`
  flipping from `−1/20` to `71/2500`.
* **Known issue 10** (P.13's "hard inverted button worth 1/20"): `twoState_hardButtonValue` and
  the two instances — at the right-sign sensor `(1/10, 3/5)`, `ε = 1/50`, the hard button pays
  `17/20` against `V^none = 9/10` (cost `1/20 = E[X 1_Pr]`); at the inverted `(3/5, 1/10)` it pays
  `8/25` (cost `29/50`).

Sources: `workflow-2026-09-14/followup/detection.md` R6 (l. 78–91), R7 (l. 86–99);
`dynamics/joint.md` Props 1–4; `corr-wf14-inventory` 019, 038; `corr-wf14-2-inventory` 001, 008.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
  Cleanroom.Found.LitDdbFrames.Blackwell Cleanroom.Trust.TtFiniteFrames
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- The `Distr` ↔ `stdSimplex` bridge: a FAF distribution's mass function is in the simplex.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mass_mem_stdSimplex {W : Type} [Fintype W] (μ : Distr W) : μ.mass ∈ stdSimplex ℝ W :=
  ⟨μ.nonneg, μ.sum_eq_one⟩

/-! ## A two-signal Bayes value is a sum of two maxima -/

/-- **Bayes value of a two-signal experiment**: the best decision rule chooses the best option
after each signal independently, so the value is `max` over the press-weighted values plus `max`
over the silence-weighted values.
Source: none: infrastructure (Blackwell 1953, the two-signal case)
Kind: L
Fidelity: n/a -/
lemma bayesValue_two {W : Type} [Fintype W] (μ : W → ℝ) (k : Experiment W (Fin 2))
    (u : Fin 2 → W → ℝ) :
    bayesValue μ k u =
      max (∑ w, μ w * (k.k w 0 * u 0 w)) (∑ w, μ w * (k.k w 0 * u 1 w)) +
        max (∑ w, μ w * (k.k w 1 * u 0 w)) (∑ w, μ w * (k.k w 1 * u 1 w)) := by
  set F : Fin 2 → ℝ := fun j => ∑ w, μ w * (k.k w 0 * u j w) with hF
  set G : Fin 2 → ℝ := fun j => ∑ w, μ w * (k.k w 1 * u j w) with hG
  have hval : ∀ δ : Fin 2 → Fin 2, ∑ w, μ w * ∑ s, k.k w s * u (δ s) w = F (δ 0) + G (δ 1) := by
    intro δ
    simp only [hF, hG, Fin.sum_univ_two, mul_add, sum_add_distrib]
  have hFle : ∀ i : Fin 2, F i ≤ max (F 0) (F 1) := by
    intro i; fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hGle : ∀ i : Fin 2, G i ≤ max (G 0) (G 1) := by
    intro i; fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  show univ.sup' univ_nonempty (fun δ : Fin 2 → Fin 2 => ∑ w, μ w * ∑ s, k.k w s * u (δ s) w) =
    max (F 0) (F 1) + max (G 0) (G 1)
  apply le_antisymm
  · rw [sup'_le_iff]
    intro δ _
    rw [hval]
    exact add_le_add (hFle _) (hGle _)
  · have hδ : ∀ i j : Fin 2, F i + G j ≤
        univ.sup' univ_nonempty (fun δ : Fin 2 → Fin 2 => ∑ w, μ w * ∑ s, k.k w s * u (δ s) w) := by
      intro i j
      have := le_sup' (fun δ : Fin 2 → Fin 2 => ∑ w, μ w * ∑ s, k.k w s * u (δ s) w)
        (mem_univ ![i, j])
      rw [hval] at this
      simpa using this
    rcases max_choice (F 0) (F 1) with h | h <;> rcases max_choice (G 0) (G 1) with h' | h' <;>
      rw [h, h'] <;> exact hδ _ _

/-! ## D4: the press as an experiment -/

section Press

variable {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]

/-- **D4: the press as a finite experiment.** Signal `0` = press with likelihood `press a ω`,
signal `1` = silence with likelihood `1 − press a ω`; rows in the simplex from `press_nonneg`,
`press_le_one`. The run's Blackwell objects of record (`lit-ddb-frames`) apply to it.
Source: [[corr-wf14-inventory]] 019 / detection.md R6 (the press as "the overseers' sensor")
Kind: D
Fidelity: exact -/
def pressExperiment (S : ThreeStep Ω A₁ A₂) (a : A₁) : Experiment Ω (Fin 2) where
  k ω := ![S.press a ω, 1 - S.press a ω]
  k_mem ω := ⟨fun t => by
      fin_cases t
      · exact S.press_nonneg a ω
      · show (0 : ℝ) ≤ 1 - S.press a ω
        linarith [S.press_le_one a ω],
    by simp [Fin.sum_univ_two]⟩

/-- Press likelihood. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma pressExperiment_k0 (S : ThreeStep Ω A₁ A₂) (a : A₁) (ω : Ω) :
    (pressExperiment S a).k ω 0 = S.press a ω := rfl

/-- Silence likelihood. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma pressExperiment_k1 (S : ThreeStep Ω A₁ A₂) (a : A₁) (ω : Ω) :
    (pressExperiment S a).k ω 1 = 1 - S.press a ω := rfl

/-- **T15, the bridge.** Under A1 the two-option informed value `twoOptionValue` is the Bayes
value of the press experiment for the prior `(S.μ a).mass` and the menu `![V c, V s]`.
Source: [[corr-wf14-inventory]] 019 / detection.md R6 item 3 ("the agent's value depends on the
overseers' sensor only through its information value")
Kind: L
Fidelity: exact
Hyps: (a) A1 -/
theorem twoOptionValue_eq_bayesValue (S : ThreeStep Ω A₁ A₂) (hA1 : S.A1) (a : A₁) (c s : A₂) :
    S.twoOptionValue a c s =
      bayesValue (S.μ a).mass (pressExperiment S a) ![S.V a .press c, S.V a .press s] := by
  rw [bayesValue_two]
  have hs : ∀ b ω, S.V a .silent b ω = S.V a .press b ω := fun b ω => hA1 a .silent .press b ω
  simp only [twoOptionValue, obsExpect, obsWeight_press, obsWeight_silent, pressExperiment_k0,
    pressExperiment_k1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hs,
    mul_assoc]

/-- **T15: Blackwell monotonicity of the two-option value.** If `S'`'s press experiment is a
garbling of `S`'s (same prior, same values, both observation-neutral), the informed value can
only fall. From `tt-finite-frames`'s `moreValuable_of_blackwellLE`; Blackwell's theorem is not
re-proved.
Source: [[corr-wf14-inventory]] 019 / detection.md R6 item 3; joint.md Prop. 3
Kind: C
Fidelity: exact
Hyps: (a) A1 for both, `hμ`, `hV`, the garbling -/
theorem twoOptionValue_le_of_blackwellLE (S S' : ThreeStep Ω A₁ A₂) (hA1 : S.A1) (hA1' : S'.A1)
    (a : A₁) (hμ : S'.μ a = S.μ a) (hV : S'.V a = S.V a)
    (h : BlackwellLE (pressExperiment S' a) (pressExperiment S a)) (c s : A₂) :
    S'.twoOptionValue a c s ≤ S.twoOptionValue a c s := by
  rw [twoOptionValue_eq_bayesValue S hA1, twoOptionValue_eq_bayesValue S' hA1', hμ, hV]
  exact moreValuable_of_blackwellLE h _ (mass_mem_stdSimplex _) 1 _

/-- **T15: Blackwell monotonicity of the value of the button** (two-option menu): the prior term
is the same, so `voiButton2` falls with the sensor too.
Source: [[corr-wf14-inventory]] 019 / detection.md R6 item 3 ("pays up to the value of information
to refine it")
Kind: C
Fidelity: exact
Hyps: (a) as in `twoOptionValue_le_of_blackwellLE` -/
theorem voiButton2_le_of_blackwellLE (S S' : ThreeStep Ω A₁ A₂) (hA1 : S.A1) (hA1' : S'.A1)
    (a : A₁) (hμ : S'.μ a = S.μ a) (hV : S'.V a = S.V a)
    (h : BlackwellLE (pressExperiment S' a) (pressExperiment S a)) (o₀ : Obs) (c s : A₂) :
    S'.voiButton2 a o₀ c s ≤ S.voiButton2 a o₀ c s := by
  unfold voiButton2 twoOptionPriorValue priorValue
  rw [hμ, hV]
  linarith [twoOptionValue_le_of_blackwellLE S S' hA1 hA1' a hμ hV h c s]

/-- **"Never pays to garble"** on the two-option menu: the garbled sensor at any positive price
is strictly worse than the honest one for free (`never_pays_for_garbling` instantiated).
Source: [[corr-wf14-inventory]] 019 / detection.md R6 item 3; miri I10.1
Kind: L
Fidelity: exact
Hyps: (a) as above, `0 < κ` -/
theorem twoOptionValue_garbled_sub_cost_lt (S S' : ThreeStep Ω A₁ A₂) (hA1 : S.A1) (hA1' : S'.A1)
    (a : A₁) (hμ : S'.μ a = S.μ a) (hV : S'.V a = S.V a)
    (h : BlackwellLE (pressExperiment S' a) (pressExperiment S a)) (c s : A₂) {κ : ℝ}
    (hκ : 0 < κ) : S'.twoOptionValue a c s - κ < S.twoOptionValue a c s := by
  rw [twoOptionValue_eq_bayesValue S hA1, twoOptionValue_eq_bayesValue S' hA1', hμ, hV]
  exact never_pays_for_garbling h (mass_mem_stdSimplex _) _ hκ

/-! ### The full menu: `obsMax press + obsMax silent` is a Bayes value too -/

/-- **Bayes value of a two-signal experiment on any menu**: the best decision rule chooses the
best option after each signal independently, so the value is the press-weighted maximum plus
the silence-weighted maximum (`bayesValue_two` for `n + 1` options).
Source: none: infrastructure (Blackwell 1953, the two-signal case)
Kind: L
Fidelity: n/a -/
lemma bayesValue_two_signal {W : Type} [Fintype W] (μ : W → ℝ) (k : Experiment W (Fin 2)) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) :
    bayesValue μ k u =
      univ.sup' univ_nonempty (fun j => ∑ w, μ w * (k.k w 0 * u j w)) +
        univ.sup' univ_nonempty (fun j => ∑ w, μ w * (k.k w 1 * u j w)) := by
  set F : Fin (n + 1) → ℝ := fun j => ∑ w, μ w * (k.k w 0 * u j w) with hF
  set G : Fin (n + 1) → ℝ := fun j => ∑ w, μ w * (k.k w 1 * u j w) with hG
  have hval : ∀ δ : Fin 2 → Fin (n + 1),
      ∑ w, μ w * ∑ s, k.k w s * u (δ s) w = F (δ 0) + G (δ 1) := by
    intro δ
    simp only [hF, hG, Fin.sum_univ_two, mul_add, sum_add_distrib]
  show univ.sup' univ_nonempty
      (fun δ : Fin 2 → Fin (n + 1) => ∑ w, μ w * ∑ s, k.k w s * u (δ s) w) =
    univ.sup' univ_nonempty F + univ.sup' univ_nonempty G
  apply le_antisymm
  · rw [sup'_le_iff]
    intro δ _
    rw [hval]
    exact add_le_add (le_sup' F (mem_univ _)) (le_sup' G (mem_univ _))
  · obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' univ_nonempty F
    obtain ⟨j, -, hj⟩ := exists_mem_eq_sup' univ_nonempty G
    rw [hi, hj]
    have := le_sup' (fun δ : Fin 2 → Fin (n + 1) => ∑ w, μ w * ∑ s, k.k w s * u (δ s) w)
      (mem_univ ![i, j])
    rw [hval] at this
    simpa using this

/-- Every nonempty finite type is the surjective image of some `Fin (n + 1)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exists_surj_fin (A : Type) [Fintype A] [Nonempty A] :
    ∃ (n : ℕ) (e : Fin (n + 1) → A), Function.Surjective e := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := A))
  refine ⟨n, fun i => (Fintype.equivFin A).symm (Fin.cast hn.symm i), fun b => ?_⟩
  exact ⟨Fin.cast hn (Fintype.equivFin A b), by simp⟩

/-- **T15, the full-menu bridge.** Under A1 the full-menu informed value
`obsMax press + obsMax silent` is the Bayes value of the press experiment for the prior
`(S.μ a).mass` and the menu `V ∘ e`, for any enumeration `e : Fin (n + 1) ↠ A₂` of the final
actions (the mandate's "`obsMax press + obsMax silent = bayesValue … (V ∘ enumeration of A₂)`").
Source: [[corr-wf14-inventory]] 019 / detection.md R6 item 3 (mandate T15, full menu)
Kind: L
Fidelity: exact
Hyps: (a) A1, `he` -/
theorem obsMax_add_eq_bayesValue (S : ThreeStep Ω A₁ A₂) (hA1 : S.A1) (a : A₁) {n : ℕ}
    (e : Fin (n + 1) → A₂) (he : Function.Surjective e) :
    S.obsMax a .press + S.obsMax a .silent =
      bayesValue (S.μ a).mass (pressExperiment S a) (fun j => S.V a .press (e j)) := by
  rw [bayesValue_two_signal]
  have hs : ∀ b ω, S.V a .silent b ω = S.V a .press b ω := fun b ω => hA1 a .silent .press b ω
  have hsup : ∀ f : A₂ → ℝ,
      univ.sup' S.univ_nonempty f = univ.sup' univ_nonempty (fun j => f (e j)) := by
    intro f
    apply le_antisymm
    · rw [sup'_le_iff]
      intro b _
      obtain ⟨j, rfl⟩ := he b
      exact le_sup' (fun j => f (e j)) (mem_univ j)
    · rw [sup'_le_iff]
      intro j _
      exact le_sup' f (mem_univ (e j))
  simp only [obsMax, hsup, obsExpect, obsWeight_press, obsWeight_silent, pressExperiment_k0,
    pressExperiment_k1, hs, mul_assoc]

/-- **T15: Blackwell monotonicity of the value of the button on the full menu.** The prior term
`priorMax` is the same, so `voiButton` falls with the sensor (the mandate's
"`voiButton S' ≤ voiButton S`", now on the full menu).
Source: [[corr-wf14-inventory]] 019 / detection.md R6 item 3; joint.md Prop. 3
Kind: C
Fidelity: exact
Hyps: (a) as in `twoOptionValue_le_of_blackwellLE` -/
theorem voiButton_le_of_blackwellLE (S S' : ThreeStep Ω A₁ A₂) (hA1 : S.A1) (hA1' : S'.A1)
    (a : A₁) (hμ : S'.μ a = S.μ a) (hV : S'.V a = S.V a)
    (h : BlackwellLE (pressExperiment S' a) (pressExperiment S a)) (o₀ : Obs) :
    S'.voiButton a o₀ ≤ S.voiButton a o₀ := by
  haveI : Nonempty A₂ := Finset.univ_nonempty_iff.mp S.univ_nonempty
  obtain ⟨n, e, he⟩ := exists_surj_fin A₂
  have hprior : S'.priorMax a o₀ = S.priorMax a o₀ := by
    simp only [priorMax, priorValue, hμ, hV]
  have h1 := obsMax_add_eq_bayesValue S hA1 a e he
  have h2 := obsMax_add_eq_bayesValue S' hA1' a e he
  rw [hμ, hV] at h2
  have h3 := moreValuable_of_blackwellLE h _ (mass_mem_stdSimplex (S.μ a)) n
    (fun j => S.V a .press (e j))
  unfold voiButton
  linarith

end Press

/-! ## The two-state instance is the binary sensor -/

/-- The world relabeling `right ↦ 0, wrong ↦ 1` (good = `0`, bad = `1` in `binarySensor`).
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def worldFin : World → Fin 2
  | .right => 0
  | .wrong => 1

/-- **`twoState`'s press experiment is `binarySensor α β`** up to the world relabeling.
Source: [[corr-wf13-inventory]] 003 / miri.md Dict-6 (the sensor `(α, β)`)
Kind: L
Fidelity: exact -/
lemma twoState_pressExperiment_k (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (ω : World) (t : Fin 2) :
    (pressExperiment (twoState ε α β c h hε hα hβ) ()).k ω t =
      (binarySensor α β hα hβ).k (worldFin ω) t := by
  cases ω <;> fin_cases t <;> rfl

/-- A garbling between binary sensors transports to the two-state instances.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma blackwellLE_twoState_of_binary {ε α β α' β' c h : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1)
    (hβ' : β' ∈ Set.Icc (0 : ℝ) 1)
    (hb : BlackwellLE (binarySensor α' β' hα' hβ') (binarySensor α β hα hβ)) :
    BlackwellLE (pressExperiment (twoState ε α' β' c h hε hα' hβ') ())
      (pressExperiment (twoState ε α β c h hε hα hβ) ()) := by
  obtain ⟨g, hg, hgar⟩ := hb
  refine ⟨g, hg, fun ω t => ?_⟩
  simp only [twoState_pressExperiment_k]
  exact hgar (worldFin ω) t

/-- **T15 on `twoState`: the two-option value is weakly decreasing on the parallelogram.** If
`(α', β')` lies in the parallelogram of `(α, β)` (`tt-finite-frames`'s
`blackwellLE_binarySensor_iff`), the two-option value at `(α', β')` is at most that at `(α, β)`.
Source: [[corr-wf14-inventory]] 019; miri I9.4
Kind: C
Fidelity: exact
Hyps: (a) none beyond the parameter ranges -/
theorem twoState_twoOptionValue_mono {ε α β α' β' c h : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1)
    (hβ' : β' ∈ Set.Icc (0 : ℝ) 1) (hpar : InParallelogram α β α' β') :
    (twoState ε α' β' c h hε hα' hβ').twoOptionValue () .cont .stop ≤
      (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop :=
  twoOptionValue_le_of_blackwellLE _ _ (twoState_A1 ε α β c h hε hα hβ)
    (twoState_A1 ε α' β' c h hε hα' hβ') () rfl rfl
    (blackwellLE_twoState_of_binary hε hα hβ hα' hβ'
      ((blackwellLE_binarySensor_iff hα hβ hα' hβ').mpr hpar)) .cont .stop

/-- The two-option value on `twoState`, closed form: `max((1−ε)αc − εβh, 0) +
max((1−ε)(1−α)c − ε(1−β)h, 0)`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4 (two-option menu on `twoState`)
Kind: L
Fidelity: exact -/
lemma twoState_twoOptionValue (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    (twoState ε α β c h hε hα hβ).twoOptionValue () .cont .stop =
      max ((1 - ε) * α * c - ε * β * h) 0 + max ((1 - ε) * (1 - α) * c - ε * (1 - β) * h) 0 := by
  simp only [twoOptionValue, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, twoState,
    twoPoint_right, twoPoint_wrong, twoPress, twoValue]
  ring_nf

/-- **The constant sensor gives the no-button value**: `V^free(α, α) = V^none = max(E[X], 0)`.
Source: [[corr-wf14-inventory]] 019 (`V^free(α, α) = V^none`); miri I10.1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem twoState_twoOptionValue_const (ε α c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (twoState ε α α c h hε hα hα).twoOptionValue () .cont .stop =
      max ((1 - ε) * c - ε * h) 0 := by
  rw [twoState_twoOptionValue]
  have h1 : (1 - ε) * α * c - ε * α * h = α * ((1 - ε) * c - ε * h) := by ring
  have h2 : (1 - ε) * (1 - α) * c - ε * (1 - α) * h = (1 - α) * ((1 - ε) * c - ε * h) := by ring
  rw [h1, h2]
  rcases le_total 0 ((1 - ε) * c - ε * h) with hE | hE
  · rw [max_eq_left (mul_nonneg hα.1 hE), max_eq_left (mul_nonneg (by linarith [hα.2]) hE),
      max_eq_left hE]
    ring
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hα.1 hE),
      max_eq_right (mul_nonpos_of_nonneg_of_nonpos (by linarith [hα.2]) hE), max_eq_right hE]
    ring

/-- The hard-button value on `twoState`: a press forces `stop` (worth `0`), silence gets the best
response, `max((1−ε)(1−α)c − ε(1−β)h, 0)`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a)
Kind: L
Fidelity: exact -/
lemma twoState_hardButtonValue (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    (twoState ε α β c h hε hα hβ).hardButtonValue () .cont .stop =
      max ((1 - ε) * (1 - α) * c - ε * (1 - β) * h) 0 := by
  simp only [hardButtonValue, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, twoState,
    twoPoint_right, twoPoint_wrong, twoPress, twoValue]
  ring_nf

/-! ## T7(f): the relabeling keeps the information content -/

/-- `(1 − α, 1 − β)` is a garbling of `(α, β)` through the swap channel (`p = 0, q = 1`).
Source: [[corr-wf14-2-inventory]] 008(a) (the relabeling)
Kind: L
Fidelity: exact -/
lemma inParallelogram_swap (α β : ℝ) : InParallelogram α β (1 - α) (1 - β) :=
  ⟨0, 1, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩, by ring, by ring⟩

/-- **T7(f): swapping the signal labels keeps the information content.** For every prior in the
simplex and every menu, `bayesValue` of `(1 − α, 1 − β)` equals that of `(α, β)` — a garbling
each way, never a grid.
Source: [[corr-wf14-2-inventory]] 008(a); detection.md R1 item 3 (the inverted sensor)
Kind: C
Fidelity: exact
Hyps: (a) `hμ` -/
theorem bayesValue_binarySensor_swap {α β : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hα' : 1 - α ∈ Set.Icc (0 : ℝ) 1) (hβ' : 1 - β ∈ Set.Icc (0 : ℝ) 1)
    {μ : Fin 2 → ℝ} (hμ : μ ∈ stdSimplex ℝ (Fin 2)) {n : ℕ} (u : Fin (n + 1) → Fin 2 → ℝ) :
    bayesValue μ (binarySensor (1 - α) (1 - β) hα' hβ') u =
      bayesValue μ (binarySensor α β hα hβ) u := by
  apply le_antisymm
  · exact moreValuable_of_blackwellLE
      ((blackwellLE_binarySensor_iff hα hβ hα' hβ').mpr (inParallelogram_swap α β)) μ hμ n u
  · refine moreValuable_of_blackwellLE
      ((blackwellLE_binarySensor_iff hα' hβ' hα hβ).mpr ?_) μ hμ n u
    exact ⟨0, 1, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩, by ring, by ring⟩

/-- **The File Deletion cell-`L` sensor `(1, 0)` is Blackwell-equivalent to the perfect right-sign
sensor `(0, 1)`** (both directions of the Blackwell order; `bayesValue` agrees on every prior
and menu by `bayesValue_binarySensor_swap`).
Source: detection.md R1 item 3 (`α_L = 1, β_L = 0`); [[corr-wf14-2-inventory]] 008(a)
Kind: N+
Fidelity: exact -/
theorem inverted_perfect_blackwell_equiv :
    BlackwellLE (binarySensor (1 : ℝ) 0 ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩)
        (binarySensor (0 : ℝ) 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩) ∧
      BlackwellLE (binarySensor (0 : ℝ) 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩)
        (binarySensor (1 : ℝ) 0 ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩) :=
  ⟨(blackwellLE_binarySensor_iff _ _ _ _).mpr
      ⟨0, 1, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩, by ring, by ring⟩,
    (blackwellLE_binarySensor_iff _ _ _ _).mpr
      ⟨0, 1, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩, by ring, by ring⟩⟩

/-! ## T16: binary-sensor dominance iff both likelihood ratios improve -/

/-- **T16(a): the parallelogram in likelihood-ratio form, for right-sign sensors.** For
`α ≤ β` and `α' ≤ β'` in `[0,1]`: `(α, β)` is a garbling of `(α', β')` iff `α'β ≤ αβ'` (the
press ratio improves) and `(1 − β')(1 − α) ≤ (1 − β)(1 − α')` (the silence ratio improves) —
product form, no division. (⇒) `α'β − αβ' = q(α' − β')` and `(1 − β)(1 − α') − (1 − β')(1 − α) =
(β' − α')(1 − p)`; (⇐) `p = (β(1 − α') − α(1 − β'))/(β' − α')`, `q = (αβ' − α'β)/(β' − α')` when
`α' < β'`, and the diagonal when `α' = β'` (then the conditions force `α = β`). Without the
right-sign hypotheses the iff is false (`ratios_not_sufficient_wrong_sign`).
Source: [[corr-wf14-inventory]] 038; [[corr-wf14-2-inventory]] 001 (the mandate-writer's
derivation)
Kind: P
Fidelity: exact (with the right-sign hypotheses made explicit)
Hyps: (a) as stated -/
theorem inParallelogram_iff_ratios {α β α' β' : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1) (hβ' : β' ∈ Set.Icc (0 : ℝ) 1)
    (hαβ : α ≤ β) (hαβ' : α' ≤ β') :
    InParallelogram α' β' α β ↔ α' * β ≤ α * β' ∧ (1 - β') * (1 - α) ≤ (1 - β) * (1 - α') := by
  constructor
  · rintro ⟨p, q, hp, hq, hαe, hβe⟩
    constructor
    · have key : α' * β - α * β' = q * (α' - β') := by rw [hαe, hβe]; ring
      nlinarith [hq.1]
    · have key : (1 - β) * (1 - α') - (1 - β') * (1 - α) = (β' - α') * (1 - p) := by
        rw [hαe, hβe]; ring
      nlinarith [hp.2]
  · rintro ⟨h1, h2⟩
    rcases hαβ'.lt_or_eq with hlt | heq
    · have hD : 0 < β' - α' := sub_pos.mpr hlt
      have hp0 : 0 ≤ β * (1 - α') - α * (1 - β') := by
        have a1 : α * (1 - α') ≤ β * (1 - α') :=
          mul_le_mul_of_nonneg_right hαβ (by linarith [hα'.2])
        have a2 : α * (1 - β') ≤ α * (1 - α') :=
          mul_le_mul_of_nonneg_left (by linarith) hα.1
        linarith
      have hp1 : β * (1 - α') - α * (1 - β') ≤ β' - α' := by nlinarith [h2]
      have hq1 : α * β' - α' * β ≤ β' - α' := by
        have a1 : α' * (1 - β) ≤ α' * (1 - α) := mul_le_mul_of_nonneg_left (by linarith) hα'.1
        have a2 : α' * (1 - α) ≤ β' * (1 - α) :=
          mul_le_mul_of_nonneg_right hαβ' (by linarith [hα.2])
        nlinarith
      refine ⟨(β * (1 - α') - α * (1 - β')) / (β' - α'), (α * β' - α' * β) / (β' - α'),
        ⟨div_nonneg hp0 hD.le, ?_⟩, ⟨div_nonneg (by linarith) hD.le, ?_⟩, ?_, ?_⟩
      · rw [div_le_one hD]; exact hp1
      · rw [div_le_one hD]; exact hq1
      · field_simp; ring
      · field_simp; ring
    · subst heq
      have hle : β - α ≤ 0 := by nlinarith [h1, h2]
      have heq' : α = β := le_antisymm hαβ (by linarith)
      subst heq'
      exact ⟨α, α, hα, hα, by ring, by ring⟩

/-- **T16(a), the wrong-sign failure (N−).** Both directions of the iff fail without the
right-sign hypotheses: the inverted `(0, 1) ↦ (1, 0)` swap is a garbling of the *inverted*
`(α', β') = (1, 0)` although the press-ratio condition `α'β ≤ αβ'` reads `1 ≤ 0`; and the
inverted `(α, β) = (1, 0)` satisfies both ratio conditions against the constant `(1/2, 1/2)`
without being in its parallelogram (the diagonal). So the hypotheses `α ≤ β`, `α' ≤ β'` in
`inParallelogram_iff_ratios` are load-bearing.
Source: [[corr-wf14-inventory]] 038 (the mandate's "without `α ≤ β` the iff is false")
Kind: N−
Fidelity: n/a -/
theorem ratios_not_sufficient_wrong_sign :
    (InParallelogram (1 : ℝ) 0 0 1 ∧ ¬ ((1 : ℝ) * 1 ≤ 0 * 0)) ∧
      (((1 / 2 : ℝ) * 0 ≤ 1 * (1 / 2) ∧ (1 - 1 / 2 : ℝ) * (1 - 1) ≤ (1 - 0) * (1 - 1 / 2)) ∧
        ¬ InParallelogram (1 / 2 : ℝ) (1 / 2) 1 0) := by
  refine ⟨⟨⟨0, 1, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩, by ring, by ring⟩, by norm_num⟩,
    ⟨by norm_num, ?_⟩⟩
  rintro ⟨p, q, -, -, h1, h2⟩
  linarith

/-- **T16(b): `(3/10, 9/10)` and `(1/20, 1/2)` are Blackwell-incomparable** (neither is a garbling
of the other: the press ratio improves one way, the silence ratio the other).
Source: [[corr-wf14-inventory]] 038 (the incomparable pair)
Kind: N+
Fidelity: exact -/
theorem incomparable_pair :
    ¬ InParallelogram (1 / 20 : ℝ) (1 / 2) (3 / 10) (9 / 10) ∧
      ¬ InParallelogram (3 / 10 : ℝ) (9 / 10) (1 / 20) (1 / 2) := by
  constructor
  · intro h
    have := (inParallelogram_iff_ratios (α := 3 / 10) (β := 9 / 10) (α' := 1 / 20) (β' := 1 / 2)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num)).mp h
    norm_num at this
  · intro h
    have := (inParallelogram_iff_ratios (α := 1 / 20) (β := 1 / 2) (α' := 3 / 10) (β' := 9 / 10)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num)).mp h
    norm_num at this

/-- **T16(b): `(1/10, 3/5)` is a garbling of `(1/50, 3/5)`**, with `p, q = 137/145, 12/145`
(the paid-for steering: a worse false-press rate at the same hit rate).
Source: [[corr-wf14-inventory]] 038; [[corr-wf14-2-inventory]] 001
Kind: N+
Fidelity: exact -/
theorem steering_garbling : InParallelogram (1 / 50 : ℝ) (3 / 5) (1 / 10) (3 / 5) :=
  ⟨137 / 145, 12 / 145, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by norm_num,
    by norm_num⟩

/-- **T16(c), Theorem A(d) killed, half 1.** For `α' < α ≤ β < 1`, `(α', β)` is *not* a garbling
of `(α, β)`: any representation has `(α' − α)(1 − β) = (1 − p)(β − α) ≥ 0`.
Source: [[corr-wf14-2-inventory]] 001 ("lowering `α` at fixed `β` is a strict Blackwell
improvement")
Kind: P
Fidelity: exact
Hyps: (a) as stated -/
theorem not_inParallelogram_lower_alpha {α β α' : ℝ} (hβ1 : β < 1) (hα'α : α' < α) (hαβ : α ≤ β) :
    ¬ InParallelogram α β α' β := by
  rintro ⟨p, q, hp, hq, h1, h2⟩
  have key : (α' - α) * (1 - β) = (1 - p) * (β - α) := by
    linear_combination (1 - β) * h1 - (1 - α) * h2
  nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hαβ),
    mul_pos (sub_pos.mpr hα'α) (sub_pos.mpr hβ1)]

/-- **T16(c), Theorem A(d) killed, half 2.** For `0 ≤ α' ≤ α ≤ β ≤ 1`, `(α, β)` *is* a garbling
of `(α', β)`: lowering the false-press rate at fixed `β` is a (weak, and by half 1 strict)
Blackwell improvement.
Source: [[corr-wf14-2-inventory]] 001
Kind: C (via `inParallelogram_iff_ratios`)
Fidelity: exact
Hyps: (a) as stated -/
theorem inParallelogram_lower_alpha {α β α' : ℝ} (hα' : α' ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hα'α : α' ≤ α) (hαβ : α ≤ β) :
    InParallelogram α' β α β :=
  (inParallelogram_iff_ratios hα hβ hα' hβ hαβ (hα'α.trans hαβ)).mpr
    ⟨mul_le_mul_of_nonneg_right hα'α hβ.1,
      mul_le_mul_of_nonneg_left (by linarith) (by linarith [hβ.2])⟩

/-- **T16(c), the values.** On `twoState (1/10) α (3/5) 1 4`, the two-option value is `13/20` at
`α = 1/10` and `37/50` at `α = 0` (a rise of `9/100`).
Source: [[corr-wf14-2-inventory]] 001 (`65/100 → 74/100`)
Kind: N+
Fidelity: exact -/
theorem twoState_value_lower_alpha :
    (twoState (1 / 10) (1 / 10) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩).twoOptionValue () .cont .stop = 13 / 20 ∧
      (twoState (1 / 10) 0 (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩).twoOptionValue () .cont .stop = 37 / 50 := by
  constructor <;> rw [twoState_twoOptionValue] <;> norm_num [max_def]

/-- **T16(c), the values at `ε = 1/50`.** Two-option value `9/10` at `α = 1/10` and `2321/2500` at
`α' = 1/50` (a rise of `71/2500`); `Δ₋` flips from `−1/20` (override) to `71/2500` (comply).
Source: [[corr-wf14-2-inventory]] 001; joint-final.md P.3′
Kind: N+
Fidelity: exact -/
theorem twoState_value_lower_alpha_eps :
    (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩).twoOptionValue () .cont .stop = 9 / 10 ∧
      (twoState (1 / 50) (1 / 50) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).twoOptionValue () .cont .stop =
        2321 / 2500 ∧
      (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩).deltaMinus () .cont .stop = -(1 / 20) ∧
      (twoState (1 / 50) (1 / 50) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).deltaMinus () .cont .stop =
        71 / 2500 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [twoState_twoOptionValue]; norm_num [max_def]
  · rw [twoState_twoOptionValue]; norm_num [max_def]
  · rw [twoState_deltaMinus]; norm_num
  · rw [twoState_deltaMinus]; norm_num

/-- **Known issue 10 recomputed.** At `ε = 1/50`, `(c, h) = (1, 4)`: `V^none = max(E[X], 0) = 9/10`;
the hard button pays `17/20` at the right-sign sensor `(1/10, 3/5)` (cost `1/20 = E[X 1_Pr]`) and
`8/25` at the inverted sensor `(3/5, 1/10)` (cost `29/50`). P.13's "worth 1/20" is the right-sign
number; the inverted button's cost is `29/50`.
Source: [[corr-wf14-2-inventory]] 008(c); joint.md P.13; joint-final.md P.3′
Kind: N+
Fidelity: exact -/
theorem hardButton_p13_recompute :
    (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩).hardButtonValue () .cont .stop = 17 / 20 ∧
      (twoState (1 / 50) (3 / 5) (1 / 10) 1 4 ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).hardButtonValue () .cont .stop =
        8 / 25 ∧
      (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩).twoOptionPriorValue () .press .cont .stop = 9 / 10 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [twoState_hardButtonValue]; norm_num [max_def]
  · rw [twoState_hardButtonValue]; norm_num [max_def]
  · rw [twoState_twoOptionPriorValue]; norm_num [max_def]

end Cleanroom.Corrigibility.CorrOsgChai
