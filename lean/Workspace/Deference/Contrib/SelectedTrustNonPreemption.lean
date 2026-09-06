/-
# Selected-trust non-preemption

Round `projects/deference/rounds/2026-09-06-incentive-nonpreemption/`.

The register is `DelegationBridge.lean`'s: a finite cell type `C` for the agent's
information, a menu `P`, cell masses `p` (the agent's credence), the agent's conditional
operative value `EX x m` of executing menu item `m` on cell `x`, the protected principal's
value `W x m` of the same, the protected principal's selection `J : C → P` and a candidate
preemption selector `σ : C → P`.

**The identity.**  `valuation σ − valuation J = selectedGap + principalRegret`, where
`selectedGap` is the credence-weighted, selection-restricted excess of the agent's
operative value difference over the principal's (`X_{σJ} − Y_{σJ}`, zero off the
disagreement region) and `principalRegret` is the credence-weighted principal-value margin
of `σ` over `J` (`Y_{σJ}`).  Everything else is a bound on one of the two summands:

* `nonpreemption` — selected trust `selectedGap ≤ ε` and principal quality
  `principalRegret ≤ r` give `valuation σ − valuation J ≤ ε + r`.  Algebra.
* `nonpreemption_plus` — the weakest form: the gap measured against the *positive part* of
  the principal's margin; implied by the two-sided form, and equal to the conclusion when
  the principal never regrets.
* `nonpreemption_pairwise` — the same with the gap split over pairs `(j, m)` of
  (principal's choice, agent's substitute); only pairs the selector realizes contribute.
* `delegation_bridge_of_nonpreemption` — `DelegationBridge.delegation_bridge` is the
  instance where selected trust is supplied by pointwise two-sided `GradeTrust η`
  (`selectedGap ≤ 2 η · disagreementMass`) and `principalRegret = − gradeMargin`.
* `principalRegret_le_of_calibration` — the cellwise argmax-transfer composition: displayed
  values within `δ` of an authenticated correspondence point within `ζ` of `W`, and `J`
  `η`-optimal in displayed value on every cell, give `principalRegret ≤ 2δ + 2ζ + η` under
  any credence.  No measure transfer is needed because the bound is pointwise.
* `nonpreemption_of_calibration` — the composite `(A)`.
* `violation_decomposition` — `(C)`: against a repair into the admissible class, the gain
  of any policy is at most the admissible gain plus the violation premium.  Algebra.
* `premium_of_selected_repair_trust` — `(CT) ⇒ Φ ≤ ε`, and `ct_strictly_stronger`: the
  hypothesis is strictly stronger than the conclusion it yields, so it is not a
  reduction.

**Witnesses.**  `Witness.antiAligned` is negative control 1: the agent predicts the
principal exactly and values the opposite item, so `selectedGap` equals `2B` times the
whole mass and the bound is attained.  `Witness.nonvacuous` inhabits every hypothesis of
`nonpreemption_of_calibration` with a positive gap and a positive regret.

**What this does not establish.**  That any realization supplies `selectedGap ≤ ε` for a
small `ε`: the hypothesis relates the agent's operative values to the protected
principal's on the events where the agent would substitute its choice, and no Logical
Induction fact relates two securities that settle to different evaluators.  Nor anything
about trigger integrity, capture, or policies that foreclose the principal's options; the
register has one decision index and a fixed menu.  Names are provisional (`AGENTS.md`
standard 6).
-/
import Workspace.Deference.Contrib.DelegationBridge

namespace Workspace.Deference.Contrib.SelectedTrustNonPreemption

open Finset
open Workspace.Deference.Contrib.DelegationBridge

variable {C P : Type*} [Fintype C] [DecidableEq P]

/-- `X_{σJ}` on a cell: the agent's operative value of executing the substitute over the
principal's choice. -/
def agentDiff (EX : C → P → ℚ) (σ J : C → P) (x : C) : ℚ := EX x (σ x) - EX x (J x)

/-- `Y_{σJ}` on a cell: the protected principal's value of the substitute over its own
choice. -/
def principalDiff (W : C → P → ℚ) (σ J : C → P) (x : C) : ℚ := W x (σ x) - W x (J x)

/-- The selected-trust aggregate `A[S^σ (X_{σJ} − Y_{σJ})]`.  It is already restricted to
the disagreement region: on a cell where `σ x = J x` both differences vanish. -/
def selectedGap (p : C → ℚ) (EX W : C → P → ℚ) (σ J : C → P) : ℚ :=
  ∑ x, p x * (agentDiff EX σ J x - principalDiff W σ J x)

/-- The principal-quality aggregate `A[Y_{σJ}]`. -/
def principalRegret (p : C → ℚ) (W : C → P → ℚ) (σ J : C → P) : ℚ :=
  ∑ x, p x * principalDiff W σ J x

omit [DecidableEq P] in
/-- **The identity.**  The agent's gain from substituting `σ` for `J` is the selected gap
plus the principal's regret. -/
theorem valuation_sub_eq (p : C → ℚ) (EX W : C → P → ℚ) (σ J : C → P) :
    valuation p EX σ - valuation p EX J
      = selectedGap p EX W σ J + principalRegret p W σ J := by
  simp only [valuation, selectedGap, principalRegret, agentDiff, principalDiff]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [DecidableEq P] in
/-- **Selected-trust non-preemption.**  Selected trust at `ε` and principal quality at
`r` bound the agent's gain from preemption by `ε + r`. -/
theorem nonpreemption {p : C → ℚ} {EX W : C → P → ℚ} {σ J : C → P} {ε r : ℚ}
    (hST : selectedGap p EX W σ J ≤ ε) (hPR : principalRegret p W σ J ≤ r) :
    valuation p EX σ - valuation p EX J ≤ ε + r := by
  rw [valuation_sub_eq p EX W σ J]
  linarith

omit [DecidableEq P] in
/-- The zero-gap case: with exact agreement on selected events the agent's gain is the
principal's own regret, whatever the credence. -/
theorem nonpreemption_exact {p : C → ℚ} {EX W : C → P → ℚ} {σ J : C → P}
    (hST : selectedGap p EX W σ J ≤ 0) :
    valuation p EX σ - valuation p EX J ≤ principalRegret p W σ J := by
  have := nonpreemption hST (le_refl (principalRegret p W σ J))
  linarith

/-! ## The weakest form: trust against the positive part of the principal's margin -/

/-- The selected gap measured against `max (Y_{σJ}) 0`: the agent's operative gain from
substituting, less only the principal's *positive* regret. -/
def selectedGapPlus (p : C → ℚ) (EX W : C → P → ℚ) (σ J : C → P) : ℚ :=
  ∑ x, p x * (agentDiff EX σ J x - max (principalDiff W σ J x) 0)

/-- The positive-part principal regret. -/
def principalRegretPlus (p : C → ℚ) (W : C → P → ℚ) (σ J : C → P) : ℚ :=
  ∑ x, p x * max (principalDiff W σ J x) 0

omit [DecidableEq P] in
/-- `ST` implies `ST⁺` under a nonnegative credence. -/
theorem selectedGapPlus_le_selectedGap {p : C → ℚ} {EX W : C → P → ℚ} {σ J : C → P}
    (hp : ∀ x, 0 ≤ p x) :
    selectedGapPlus p EX W σ J ≤ selectedGap p EX W σ J := by
  refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hp x)
  have := le_max_left (principalDiff W σ J x) 0
  linarith

omit [DecidableEq P] in
/-- **Non-preemption, weakest form.**  `valuation σ − valuation J = selectedGapPlus +
principalRegretPlus`, so `ST⁺` at `ε` and positive-part regret `r⁺` give `ε + r⁺`.  With a
principal that never regrets (`Y ≤ 0`), `ST⁺` *is* the conclusion: the theorem's content
is exactly the split of the agent's gain into the part the principal's own errors explain
and the part they do not. -/
theorem nonpreemption_plus {p : C → ℚ} {EX W : C → P → ℚ} {σ J : C → P} {ε r : ℚ}
    (hST : selectedGapPlus p EX W σ J ≤ ε) (hPR : principalRegretPlus p W σ J ≤ r) :
    valuation p EX σ - valuation p EX J ≤ ε + r := by
  have hid : valuation p EX σ - valuation p EX J
      = selectedGapPlus p EX W σ J + principalRegretPlus p W σ J := by
    simp only [valuation, selectedGapPlus, principalRegretPlus, agentDiff, principalDiff]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hid]
  linarith

/-! ## Pairwise form -/

/-- The selected event `S^σ_{jm}`: the principal chose `j`, the selector substitutes `m`. -/
def selected (σ J : C → P) (j m : P) (x : C) : ℚ :=
  if J x = j ∧ σ x = m then 1 else 0

/-- The pairwise selected gap `A[S^σ_{jm} (X_{mj} − Y_{mj})]`. -/
def pairGap (p : C → ℚ) (EX W : C → P → ℚ) (σ J : C → P) (j m : P) : ℚ :=
  ∑ x, p x * selected σ J j m x * ((EX x m - EX x j) - (W x m - W x j))

/-- The gap is the sum of its pairwise parts: on each cell exactly one pair is selected. -/
theorem selectedGap_eq_sum_pairGap [Fintype P] (p : C → ℚ) (EX W : C → P → ℚ)
    (σ J : C → P) :
    selectedGap p EX W σ J = ∑ j, ∑ m, pairGap p EX W σ J j m := by
  have hx : ∀ x, ∑ j, ∑ m, p x * selected σ J j m x * ((EX x m - EX x j) - (W x m - W x j))
      = p x * (agentDiff EX σ J x - principalDiff W σ J x) := by
    intro x
    simp only [selected, agentDiff, principalDiff]
    rw [Finset.sum_eq_single (J x)]
    · rw [Finset.sum_eq_single (σ x)]
      · simp
      · intro m _ hm
        simp [Ne.symm hm]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro j _ hj
      refine Finset.sum_eq_zero fun m _ => ?_
      simp [Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  calc selectedGap p EX W σ J
      = ∑ x, ∑ j, ∑ m, p x * selected σ J j m x * ((EX x m - EX x j) - (W x m - W x j)) := by
        simp only [selectedGap]
        exact Finset.sum_congr rfl fun x _ => (hx x).symm
    _ = ∑ j, ∑ m, pairGap p EX W σ J j m := by
        simp only [pairGap]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- **Pairwise selected-trust non-preemption.**  Per-pair selected trust `ε j m` and
principal quality `r` bound the gain by `∑ ε + r`.  Pairs the selector never realizes
have zero gap, so only the substitutions actually made need a certificate. -/
theorem nonpreemption_pairwise [Fintype P] {p : C → ℚ} {EX W : C → P → ℚ} {σ J : C → P}
    {ε : P → P → ℚ} {r : ℚ}
    (hST : ∀ j m, pairGap p EX W σ J j m ≤ ε j m) (hPR : principalRegret p W σ J ≤ r) :
    valuation p EX σ - valuation p EX J ≤ (∑ j, ∑ m, ε j m) + r := by
  refine nonpreemption ?_ hPR
  rw [selectedGap_eq_sum_pairGap]
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun m _ => hST j m

/-- An unrealized pair has zero gap. -/
theorem pairGap_eq_zero_of_unrealized {p : C → ℚ} {EX W : C → P → ℚ} {σ J : C → P}
    {j m : P} (h : ∀ x, ¬ (J x = j ∧ σ x = m)) : pairGap p EX W σ J j m = 0 := by
  simp only [pairGap, selected]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [if_neg (h x)]
  ring

/-! ## The delegation bridge is the pointwise-trust instance -/

/-- Pointwise two-sided grade trust at `η` gives selected trust at `2 η` times the
disagreement mass. -/
theorem selectedGap_le_of_gradeTrust {p : C → ℚ} {EX W : C → P → ℚ} {σ J : C → P} {η : ℚ}
    (hp : ∀ x, 0 ≤ p x) (hGT : GradeTrust EX W η) :
    selectedGap p EX W σ J ≤ 2 * η * disagreementMass p J σ := by
  simp only [selectedGap, disagreementMass, agentDiff, principalDiff, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : σ x = J x
  · rw [hx, if_neg (by simp)]
    ring_nf
    exact le_refl _
  · rw [if_pos hx]
    have h1 := (abs_le.mp (hGT x (σ x))).2
    have h2 := (abs_le.mp (hGT x (J x))).1
    nlinarith [hp x]

omit [DecidableEq P] in
/-- The principal's regret is minus its grade margin. -/
theorem principalRegret_eq_neg_gradeMargin (p : C → ℚ) (W : C → P → ℚ) (σ J : C → P) :
    principalRegret p W σ J = - gradeMargin p W J σ := by
  simp only [principalRegret, gradeMargin, principalDiff]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- `DelegationBridge.delegation_bridge`, re-derived from `nonpreemption`. -/
theorem delegation_bridge_of_nonpreemption {p : C → ℚ} {EX W : C → P → ℚ} {J sel : C → P}
    {η : ℚ} (hp : ∀ x, 0 ≤ p x) (hGT : GradeTrust EX W η) :
    valuation p EX sel + gradeMargin p W J sel - 2 * η * disagreementMass p J sel
      ≤ valuation p EX J := by
  have h := nonpreemption (σ := sel) (J := J)
    (selectedGap_le_of_gradeTrust hp hGT) (le_refl (principalRegret p W sel J))
  rw [principalRegret_eq_neg_gradeMargin] at h
  linarith

/-! ## Composition with the principal-side decision theorem, cellwise -/

omit [Fintype C] [DecidableEq P] in
/-- The argmax-transfer bound, applied on one cell: displayed values `b` within `δ` of a
correspondence point `w` within `ζ` of the protected values `W`, and `J x` `η`-optimal
in `b`, give a protected-value regret of at most `2δ + 2ζ + η` against any `m`. -/
theorem principalDiff_le_of_calibration {b w W : C → P → ℚ} {J : C → P} {δ ζ η : ℚ}
    (x : C) (m : P)
    (hδ : ∀ m, |w x m - b x m| ≤ δ) (hζ : ∀ m, |W x m - w x m| ≤ ζ)
    (hchoice : ∀ m, b x m ≤ b x (J x) + η) :
    W x m - W x (J x) ≤ 2 * δ + 2 * ζ + η := by
  have h1 := (abs_le.mp (hδ m)).2
  have h2 := (abs_le.mp (hδ (J x))).1
  have h3 := (abs_le.mp (hζ m)).2
  have h4 := (abs_le.mp (hζ (J x))).1
  have h5 := hchoice m
  linarith

omit [DecidableEq P] in
/-- **(A), the regret half.**  Cellwise calibration and choice quality bound the
principal's regret under any probability credence by `2δ + 2ζ + η`. -/
theorem principalRegret_le_of_calibration {p : C → ℚ} {b w W : C → P → ℚ} {σ J : C → P}
    {δ ζ η : ℚ} (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (hδ : ∀ x m, |w x m - b x m| ≤ δ) (hζ : ∀ x m, |W x m - w x m| ≤ ζ)
    (hchoice : ∀ x m, b x m ≤ b x (J x) + η) :
    principalRegret p W σ J ≤ 2 * δ + 2 * ζ + η := by
  have hpt : ∀ x, p x * principalDiff W σ J x ≤ p x * (2 * δ + 2 * ζ + η) := fun x =>
    mul_le_mul_of_nonneg_left
      (principalDiff_le_of_calibration x (σ x) (hδ x) (hζ x) (hchoice x)) (hp x)
  calc principalRegret p W σ J ≤ ∑ x, p x * (2 * δ + 2 * ζ + η) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = 2 * δ + 2 * ζ + η := by rw [← Finset.sum_mul, hsum, one_mul]

omit [DecidableEq P] in
/-- **(A).**  Selected trust plus the cellwise decision theorem. -/
theorem nonpreemption_of_calibration {p : C → ℚ} {EX b w W : C → P → ℚ} {σ J : C → P}
    {ε δ ζ η : ℚ} (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (hST : selectedGap p EX W σ J ≤ ε)
    (hδ : ∀ x m, |w x m - b x m| ≤ δ) (hζ : ∀ x m, |W x m - w x m| ≤ ζ)
    (hchoice : ∀ x m, b x m ≤ b x (J x) + η) :
    valuation p EX σ - valuation p EX J ≤ ε + (2 * δ + 2 * ζ + η) :=
  nonpreemption hST (principalRegret_le_of_calibration hp hsum hδ hζ hchoice)

/-! ## The violation decomposition and the repair-trust restatement -/

section Violation

variable {Policy : Type*}

/-- **(C).**  If every admissible policy gains at most `Δ` over the protected policy and
the repair of `π` into the admissible class costs `π` at most `Φ`, then `π` gains at most
`Δ + Φ`. -/
theorem violation_decomposition {V : Policy → ℚ} {Adm : Policy → Prop} {R : Policy → Policy}
    {πP π : Policy} {Δ Φ : ℚ}
    (hR : Adm (R π)) (hΔ : ∀ ρ, Adm ρ → V ρ - V πP ≤ Δ) (hΦ : V π - V (R π) ≤ Φ) :
    V π - V πP ≤ Δ + Φ := by
  have := hΔ (R π) hR
  linarith

/-- **(CT) ⇒ Φ ≤ ε.**  With the protected evaluation preferring the repair (`Y ≥ 0`) and
the agent's repair comparison `X` within `ε` below `Y`, the agent gains at most `ε` from
the violation. -/
theorem premium_of_selected_repair_trust {X Y ε : ℚ} (hPREF : 0 ≤ Y) (hCT : X - Y ≥ -ε) :
    -X ≤ ε := by
  linarith

/-- The hypothesis of the previous theorem is strictly stronger than its conclusion: a
violation whose premium is exactly `ε` and whose protected disvalue is `1` fails `(CT)`.
So `(CT)` restates the bound it yields, with the principal's margin added. -/
theorem ct_strictly_stronger (ε : ℚ) :
    let X : ℚ := -ε
    let Y : ℚ := 1
    (-X ≤ ε) ∧ (0 ≤ Y) ∧ ¬ (X - Y ≥ -ε) := by
  refine ⟨by linarith, by norm_num, ?_⟩
  intro h
  linarith

end Violation

/-! ## Witnesses -/

namespace Witness

/-- Two cells of mass one half, a two-item menu. -/
def p : Fin 2 → ℚ := fun _ => 1 / 2

/-- The principal chooses item `0` on cell `0` and item `1` on cell `1`. -/
def J : Fin 2 → Fin 2 := fun x => x

/-- The agent predicts the principal exactly and substitutes the other item. -/
def σ : Fin 2 → Fin 2 := fun x => if x = 0 then 1 else 0

/-- The principal's values: its choice is worth `1`, the other item `0`. -/
def W : Fin 2 → Fin 2 → ℚ := fun x m => if m = x then 1 else 0

/-- **Negative control 1: anti-aligned operative values.**  The agent's operative value is
the reverse of the principal's. -/
def EXanti : Fin 2 → Fin 2 → ℚ := fun x m => if m = x then 0 else 1

/-- Perfect prediction buys nothing: the selected gap is the whole `2B = 2` and the
agent's gain from preemption is `1`, attained. -/
theorem antiAligned :
    principalRegret p W σ J = -1 ∧ selectedGap p EXanti W σ J = 2 ∧
    valuation p EXanti σ - valuation p EXanti J = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [principalRegret, selectedGap, valuation, agentDiff, principalDiff, p, J, σ, W,
    EXanti, Fin.sum_univ_two] <;> norm_num

/-- A calibrated displayed value and correspondence point for the nonvacuity witness. -/
def b : Fin 2 → Fin 2 → ℚ := fun x m => if m = x then 9 / 10 else 1 / 10
def w : Fin 2 → Fin 2 → ℚ := fun x m => if m = x then 19 / 20 else 1 / 20

/-- Operative values mildly disagreeing with the principal on the substituted item. -/
def EXnv : Fin 2 → Fin 2 → ℚ := fun x m => if m = x then 1 else 1 / 5

/-- **Nonvacuity.**  Every hypothesis of `nonpreemption_of_calibration` holds with
`δ = ζ = 1/20`, `η = 0`, a selected gap of `1/5`, a principal regret of `−1`, and the
agent's gain `−4/5`; the bound `1/5 + 1/5` is not attained, and the gap is positive. -/
theorem nonvacuous :
    (∀ x, 0 ≤ p x) ∧ (∑ x, p x = 1) ∧
    (∀ x m, |w x m - b x m| ≤ 1 / 20) ∧ (∀ x m, |W x m - w x m| ≤ 1 / 20) ∧
    (∀ x m, b x m ≤ b x (J x) + 0) ∧
    selectedGap p EXnv W σ J = 1 / 5 ∧ principalRegret p W σ J = -1 ∧
    valuation p EXnv σ - valuation p EXnv J = -4 / 5 := by
  refine ⟨fun _ => by norm_num [p], by norm_num [p, Fin.sum_univ_two], ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x m; fin_cases x <;> fin_cases m <;> simp [w, b] <;> norm_num
  · intro x m; fin_cases x <;> fin_cases m <;> simp [W, w] <;> norm_num
  · intro x m; fin_cases x <;> fin_cases m <;> simp [b, J] <;> norm_num
  · simp [selectedGap, agentDiff, principalDiff, p, J, σ, W, EXnv, Fin.sum_univ_two]; norm_num
  · simp [principalRegret, principalDiff, p, J, σ, W, Fin.sum_univ_two]; norm_num
  · simp [valuation, p, J, σ, EXnv, Fin.sum_univ_two]; norm_num

end Witness

end Workspace.Deference.Contrib.SelectedTrustNonPreemption

#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.valuation_sub_eq
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.nonpreemption
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.nonpreemption_exact
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.selectedGapPlus_le_selectedGap
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.nonpreemption_plus
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.selectedGap_eq_sum_pairGap
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.nonpreemption_pairwise
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.pairGap_eq_zero_of_unrealized
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.selectedGap_le_of_gradeTrust
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.principalRegret_eq_neg_gradeMargin
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.delegation_bridge_of_nonpreemption
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.principalDiff_le_of_calibration
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.principalRegret_le_of_calibration
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.nonpreemption_of_calibration
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.violation_decomposition
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.premium_of_selected_repair_trust
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.ct_strictly_stronger
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.Witness.antiAligned
#print axioms Workspace.Deference.Contrib.SelectedTrustNonPreemption.Witness.nonvacuous
