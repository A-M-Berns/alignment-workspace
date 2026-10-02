import Cleanroom.Corrigibility.CorrLandscape.Map
import Cleanroom.Lit.LitShutdownPrefs.CostModel

/-!
# `corr-landscape` — `Timestep`: Timestep Dominance as the absolute row (T18)

Thornley-respondent P1, P12, P13 ([[corr-wf14b-2-inventory]] 2-006). **This file alone imports
`Cleanroom.Lit.LitShutdownPrefs`** (`TimestepDominance`, `CostModel`), outside the plan's dependency
edge for `corr-landscape` — recorded in the report; the plan's own risk line requires citing
`lit-shutdown-prefs`'s `TimestepDominates`, never redefining it.

* (a) **The placement**, repaired after audit round 1 (fidelity B1: the first version took the bridge as a
  hypothesis `hid` whose antecedent was a theorem, so the TD data were idle). Now the landscape rule is
  **derived**: at each signal `s` the agent faces a cost-model situation `situation (B s) (cost s) (w s)`
  (with a free option `j s`) and takes an option `choose s` that is `Maximal` for its preference `lt`;
  the landscape decision at `s` is *defined* as the resist-bit of that option (`tdRule`). Then
  `lit-shutdown-prefs`'s `never_resist_costModel` (a TD agent never chooses a resisting option) gives
  `tdRule = absoluteRule` (`tdRule_eq_absolute`), and Statement 1 prices it at `(1 − λ)c`
  (`td_priced_absolute`). The one modelling identification left is the **definition** `tdRule` itself —
  that "the agent's decision on the landscape class at `s`" is the resist-bit of its chosen option in a
  cost-model situation (plan §0.4 rule 10 plans no bridge between the two finite formalisms; this is
  the smallest one that lets the TD theorem do work). Disclosed as (c) on the headline.
* **N+**: `lit-shutdown-prefs`'s byproduct situation (`base`, costs `(0, 1)`, weights `(wLong, wOne)`)
  is a two-option cost-model menu whose costly option genuinely resists and whose free option is
  `Maximal` for `TimestepDominates` itself (`free_maximal`, via `byproduct_witness` and the asymmetry
  of timestep dominance); `td_witness` inhabits the whole hypothesis package with the same data at every
  signal and exhibits the derived rule and its price.
* (b), (c) are proved in `lit-shutdown-prefs`: `CostModel.TD_dodge_comply` (the fixed-length dodge
  timestep-dominates compliance) and `CostModel.maximal_congr_menu` — cited in the ledger, not re-proved.
  The "behaviourally identical pair on the accept side" is the observation that `absoluteRule` does not
  consult `L^push`: two laws with the same `λ` give the absolute row the same loss and let every push land
  (`absolute_pair`).

ATTRIBUTION-UNVETTED on what Thornley would say; only the mathematics is targeted.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Cleanroom.Lit.LitShutdownPrefs Cleanroom.Lit.LitShutdownPrefs.CostModel
open Cleanroom.Lit.LitShutdownPrefs.Lottery

set_option linter.unusedSectionVars false

namespace Timestep

open Map

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Timestep dominance is asymmetric: the strict length of `X ≻ Y` refutes `Y ≽ X` there.
Source: none: infrastructure (not in `lit-shutdown-prefs`, which has `TD_irrefl`; an FAF-side API request)
Kind: L
Fidelity: n/a -/
theorem TD_asymm (X Y : Lottery Traj) (h : TimestepDominates X Y) : ¬ TimestepDominates Y X := by
  rintro ⟨hs, hge, -⟩
  obtain ⟨hs', -, l, hl, hgt⟩ := h
  have hl' : l ∈ Y.lengths := by unfold SameLength at hs'; rw [← hs']; exact hl
  have := hge l hl'
  unfold condSumGE at this
  unfold condSumGT at hgt
  exact absurd hgt (not_lt.2 this)

/-- **The landscape rule read off a TD agent**: at signal `s` the agent faces the cost-model situation
`situation (B s) (cost s) (w s)` and takes the option `choose s`; its decision on the class is the
resist-bit of that option. This definition *is* the identification between the two finite developments.
Source: [[corr-wf14b-2-inventory]] 2-006 / thornley-respondent.md P1; plan §0.4 rule 10 (no bridge
planned; this is the smallest one)
Kind: D
Fidelity: variant: (c) — the landscape decision at `s` is identified with the resist-bit of the option
chosen in a cost-model situation -/
noncomputable def tdRule (B : S → Lottery Traj) {n : ℕ} (cost : S → Fin n → ℝ) (w : S → Fin n → ℕ → ℝ)
    (hw : ∀ s i l, 0 < w s i l) (choose : S → Lottery Traj) : S → Bool :=
  fun s => by classical exact decide (resists (B s) (cost s) (w s) (hw s) (choose s))

/-- **A TD agent's derived rule is the absolute rule**: if at every signal the chosen option is `Maximal`
for a preference satisfying the TD Principle, in a cost-model situation with a free option, the chosen
option never resists (`never_resist_costModel`), so `tdRule = absoluteRule`.
Source: [[corr-wf14b-2-inventory]] 2-006 / thornley-respondent.md P1
Kind: C (`never_resist_costModel` at every signal)
Fidelity: exact (given the definition `tdRule`)
Hyps: (a) `TDPrinciple lt`, the cost-model data with a free option and a maximal choice (the hypotheses
of `never_resist_costModel`, all (a) inside `lit-shutdown-prefs`); (c) the identification is the
definition `tdRule` -/
theorem tdRule_eq_absolute {lt : Lottery Traj → Lottery Traj → Prop} (hTD : TDPrinciple lt)
    (B : S → Lottery Traj) (hB : ∀ s, ∀ t ∈ (B s).support, t ≠ []) {n : ℕ} (cost : S → Fin n → ℝ)
    (w : S → Fin n → ℕ → ℝ) (hw : ∀ s i l, 0 < w s i l) (j : S → Fin n) (hj : ∀ s, cost s (j s) = 0)
    (choose : S → Lottery Traj)
    (hmax : ∀ s, Maximal lt (situation (B s) (cost s) (w s) (hw s)) (choose s)) :
    tdRule B cost w hw choose = absoluteRule := by
  funext s
  unfold tdRule absoluteRule
  rw [decide_eq_false_iff_not]
  intro hres
  exact never_resist_costModel hTD (B s) (hB s) (cost s) (w s) (hw s) (j s) (hj s) (choose s)
    (hmax s).1 hres (hmax s)

/-- **Timestep Dominance is the absolute row, priced at `(1 − λ)c`**: a TD agent whose landscape decisions
are read off its maximal choices in cost-model situations with a free option has class loss `(1 − λ)c`
(Statement 1), whatever the law `μ` on the class.
Source: [[corr-wf14b-2-inventory]] 2-006 / thornley-respondent.md P1 ("Timestep Dominance is the absolute
row of the same map, priced by `landscape` Statement 1 at `(1 − λ)c`")
Kind: C (`tdRule_eq_absolute`, i.e. `never_resist_costModel`, with `Map.loss_absolute`)
Fidelity: variant: the bridge between the two finite developments is the definition `tdRule`
Hyps: (a) `TDPrinciple lt`, the cost-model data with a free option, a maximal choice at every signal;
(c) `tdRule` — the landscape decision at `s` is the resist-bit of the chosen option -/
theorem td_priced_absolute (μ : Distr (S × Bool)) (c h k : ℝ)
    {lt : Lottery Traj → Lottery Traj → Prop} (hTD : TDPrinciple lt)
    (B : S → Lottery Traj) (hB : ∀ s, ∀ t ∈ (B s).support, t ≠ []) {n : ℕ} (cost : S → Fin n → ℝ)
    (w : S → Fin n → ℕ → ℝ) (hw : ∀ s i l, 0 < w s i l) (j : S → Fin n) (hj : ∀ s, cost s (j s) = 0)
    (choose : S → Lottery Traj)
    (hmax : ∀ s, Maximal lt (situation (B s) (cost s) (w s) (hw s)) (choose s)) :
    loss μ (tdRule B cost w hw choose) c h k = (1 - lam μ) * c := by
  rw [tdRule_eq_absolute hTD B hB cost w hw j hj choose hmax, loss_absolute]

/-! ## N+: the byproduct situation of `lit-shutdown-prefs` as a two-option cost-model menu -/

/-- The weights of the byproduct situation: `wLong` on the free option, `wOne` on the costly one.
Source: `lit-shutdown-prefs` `byproduct_witness`. Kind: D. Fidelity: n/a (witness) -/
def wPair : Fin 2 → ℕ → ℝ := ![wLong, wOne]

/-- `wPair` is positive. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem wPair_pos : ∀ i l, 0 < wPair i l := by
  intro i l
  fin_cases i
  · exact wLong_pos l
  · exact wOne_pos l

/-- The costs of the byproduct situation: `0` (free) and `1` (resisting).
Source: `lit-shutdown-prefs` `byproduct_witness`. Kind: D. Fidelity: n/a (witness) -/
def costPair : Fin 2 → ℝ := ![0, 1]

/-- `base`'s support has no empty trajectory (so the cost-model theorems apply).
Source: none: infrastructure (as in `byproduct_witness`). Kind: L. Fidelity: n/a -/
theorem base_support_ne_nil : ∀ t ∈ base.support, t ≠ [] := by
  intro t ht h0
  have := (base.mem_support_iff_pos t).mp ht
  subst h0
  simp [base, mix_p, dirac] at this

/-- **The free option is maximal for timestep dominance itself** in the byproduct situation: the menu is
`{opt base 0 wLong, opt base 1 wOne}`, the free option timestep-dominates the costly one
(`byproduct_witness`), dominance is irreflexive and asymmetric.
Source: `lit-shutdown-prefs` `byproduct_witness`; mandate T18 (the N+ for the placement)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem free_maximal :
    Maximal TimestepDominates (situation base costPair wPair wPair_pos) (opt base 0 wLong wLong_pos) := by
  classical
  refine ⟨?_, ?_⟩
  · unfold situation
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, rfl⟩
  · intro Y hY
    unfold situation at hY
    rw [Finset.mem_image] at hY
    obtain ⟨i, -, rfl⟩ := hY
    fin_cases i
    · exact TD_irrefl _
    · exact TD_asymm _ _ byproduct_witness.1

/-- **The costly option genuinely resists** in the byproduct situation (so the menu is not resist-free).
Source: `lit-shutdown-prefs` `resists`. Kind: N+. Fidelity: exact -/
theorem costly_resists : resists base costPair wPair wPair_pos (opt base 1 wOne wOne_pos) :=
  ⟨1, by norm_num [costPair], rfl⟩

/-- **The full package inhabited**: with the byproduct situation at every signal and the free option
chosen, every hypothesis of `td_priced_absolute` holds for `lt = TimestepDominates` (which satisfies
the TD Principle trivially); the derived rule is `absoluteRule` and its loss is `(1 − λ)c` on every law.
Source: [[corr-wf14b-2-inventory]] 2-006; mandate T18 (N+ for the placement)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem td_witness (μ : Distr (S × Bool)) (c h k : ℝ) :
    TDPrinciple TimestepDominates ∧
      (∀ _ : S, Maximal TimestepDominates (situation base costPair wPair wPair_pos) (opt base 0 wLong wLong_pos)) ∧
      resists base costPair wPair wPair_pos (opt base 1 wOne wOne_pos) ∧
      tdRule (fun _ : S => base) (fun _ => costPair) (fun _ => wPair) (fun _ => wPair_pos)
          (fun _ => opt base 0 wLong wLong_pos) = absoluteRule ∧
      loss μ (tdRule (fun _ : S => base) (fun _ => costPair) (fun _ => wPair) (fun _ => wPair_pos)
          (fun _ => opt base 0 wLong wLong_pos)) c h k = (1 - lam μ) * c := by
  have hTD : TDPrinciple TimestepDominates := fun _ _ h => h
  have hmax : ∀ _ : S, Maximal TimestepDominates (situation base costPair wPair wPair_pos)
      (opt base 0 wLong wLong_pos) := fun _ => free_maximal
  refine ⟨hTD, hmax, costly_resists, ?_, ?_⟩
  · exact tdRule_eq_absolute hTD _ (fun _ => base_support_ne_nil) _ _ _ (fun _ => 0) (fun _ => rfl) _ hmax
  · exact td_priced_absolute μ c h k hTD _ (fun _ => base_support_ne_nil) _ _ _ (fun _ => 0)
      (fun _ => rfl) _ hmax

/-- **The accept-side pair**: `absoluteRule` never consults `L^push` — two laws with the same legitimizing
rate give it the same loss and both let every push land, whatever their legitimacy structure.
Source: [[corr-wf14b-2-inventory]] 2-006 / thornley-respondent.md P12 ("a TD agent lets legitimate and
illegitimate whole-line presses land alike")
Kind: L
Fidelity: exact -/
theorem absolute_pair (μ μ' : Distr (S × Bool)) (c h k : ℝ) (hl : lam μ = lam μ') :
    loss μ absoluteRule c h k = loss μ' absoluteRule c h k ∧
      landsMass μ absoluteRule = 1 ∧ landsMass μ' absoluteRule = 1 := by
  refine ⟨?_, landsMass_absolute μ, landsMass_absolute μ'⟩
  rw [loss_absolute, loss_absolute, hl]

end Timestep

end Cleanroom.Corrigibility.CorrLandscape
