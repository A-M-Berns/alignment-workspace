import Cleanroom.Decision.DpFirstpersonSc.PredictorLabel
import Cleanroom.Decision.DpFirstpersonSc.WitnessesNewcomb
import Cleanroom.Found.DpCoreTree.Seed

/-!
# Witnesses for T14: the predictor-labelled instantiation on TN-V2

On `tnV2 (3/4) 4 1` (both hypothetical queries, `d_F` then `d_E`, then the real branch):

* **Classification** (`tnV2_F_predictorAt`, `tnV2_E_predictorAt`, `tnReal_not_predictorAt`): the
  two hypothetical nodes are predictor nodes (not live — both fills occur below them — and every
  `O_d`-leaf below passes the real `d`-node), the two real nodes are live. No routing node: TN-V2
  is routing-free at both points (GR-D2′(iii)).
* **GR-2's numbers**: under the mixed procedure `C = (2/5, 3/7)` the independent-redraw value is
  `V_{B}(C) = V_{B_C}(C) = 9427/4900` (`tnV2_value_mixed`, `tnV2_replacePred_value_self`); the
  shared-seed value of `B_C` is the same `9427/4900` (`tnV2_replacePred_value'_mixed`: `B_C` is
  almost fair, so Definition 6′ agrees with Definition 6 on it) while the shared-seed value of `B`
  itself is `269/140 ≠ 9427/4900` (`tnV2_value'_mixed`, `tnV2_seed_failure`): the exact-label
  predictor is the shared-seed simulation only on non-nested fibers; on the nested `d_F`/`d_E`
  fibers with a stochastic `C` they differ (GR-2's "fails for mixed `C` on fibers with a
  positive-probability nested pair").
* **GR-4's instance** (`tnV2_gr4_cell`): `θ = (2/5, 3/7)`, `θ' = (1, 3/7)` (differ at `d_F`
  only), payoffs in `[0, 5]`, `TV = 3/5`, `usePred_θ(d_F) = 1`: `|V_{B_θ} − V_{B_θ'}| =
  1269/2450 ≤ 3 = 5 · (3/5) · 1`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- A mixed action on `Box`: `large` with probability `t`. Source: none: infrastructure. Kind: D -/
def boxDistr (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : FinDistr ℚ Box where
  w := fun b => if b = .large then t else 1 - t
  nonneg := by intro b; split_ifs <;> linarith
  sum_one := by rw [box_sum_univ]; simp

/-- Weights. Source: none: infrastructure. Kind: L -/
@[simp] theorem boxDistr_large (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (boxDistr t h0 h1).w .large = t := by simp [boxDistr]

/-- Weights. Source: none: infrastructure. Kind: L -/
@[simp] theorem boxDistr_both (t : ℚ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (boxDistr t h0 h1).w .both = 1 - t := by simp [boxDistr]

/-- **GR-2's mixed procedure `C = (2/5, 3/7)`**: `large` w.p. `2/5` at `d_F`, `3/7` at `d_E`.
Source: `grounding.md` GR-2 ("mixed `C = (2/5, 3/7)`")
Kind: D -/
def tnMixed : Proc TnPt (fun _ => Box) ℚ
  | .F => boxDistr (2/5) (by norm_num) (by norm_num)
  | .E => boxDistr (3/7) (by norm_num) (by norm_num)

/-- The label `θ' = (1, 3/7)`: differs from `tnMixed` at `d_F` only.
Source: `grounding.md` GR-4 (`θ, θ'` differ only at `d`); mandate T14(b)
Kind: D -/
def tnMixed' : Proc TnPt (fun _ => Box) ℚ
  | .F => boxDistr 1 (by norm_num) le_rfl
  | .E => boxDistr (3/7) (by norm_num) (by norm_num)

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem tnMixed_F : tnMixed .F = boxDistr (2/5) (by norm_num) (by norm_num) := rfl
/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem tnMixed_E : tnMixed .E = boxDistr (3/7) (by norm_num) (by norm_num) := rfl
/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem tnMixed'_F : tnMixed' .F = boxDistr 1 (by norm_num) le_rfl := rfl
/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem tnMixed'_E : tnMixed' .E = boxDistr (3/7) (by norm_num) (by norm_num) := rfl

/-- The payoff at a leaf of V2. Source: none: infrastructure. Kind: L -/
theorem tnV2_payoff' (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (x y : Box) (i : Fin 2)
    (act : Box) : payoff (tnV2 p h0 h1 L S) ⟨x, y, i, act, ()⟩ = tnPay L S (decide (i = 0), act) := by
  unfold tnV2 tnReal; simp

/-! ## Classification of TN-V2's four nodes -/

section classify

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-- **The real nodes are live** (both edges lead to leaves whose fill is the branch's): neither
`tnReal L S i` node is a predictor node.
Source: `grounding.md` GR-D2′(iii) (TN-V2 routing-free at both points)
Kind: L -/
theorem tnReal_not_predictorAt (i : Fin 2) :
    ¬ PredictorAt (acts := fun _ => Box) tnObs (if i = 0 then TnPt.F else TnPt.E)
      (fun act => Tree.leaf (decide (i = 0), act) (tnPay L S (decide (i = 0), act))) := by
  apply not_predictorAt_of_liveAt
  intro act ℓ
  rw [world_leaf]
  fin_cases i <;> simp [tnObs]

/-- **The hypothetical `d_E` node is a predictor node**: not live (the full branch lies below
it), and every empty-branch leaf below it passes the real `d_E`-node.
Source: `grounding.md` GR-D2 (predictor = "Omega's simulation of the agent at `d`")
Kind: L -/
theorem tnV2_E_predictorAt (x : Box) :
    PredictorAt tnObs TnPt.E (fun y =>
      Tree.chance 2 (FinDistr.coin (if x = .large ∧ y = .large then p else 1 - p)
        (by split_ifs <;> linarith) (by split_ifs <;> linarith)) (tnReal L S)) := by
  refine ⟨fun h => ?_, fun y ℓ hw => ?_⟩
  · have := h .large ⟨0, .large, ()⟩
    rw [world_chance] at this
    unfold tnReal at this
    rw [world_decision, world_leaf] at this
    simp [tnObs] at this
  · obtain ⟨i, act, ⟨⟩⟩ := ℓ
    rw [world_chance] at hw
    unfold tnReal at hw
    rw [world_decision, world_leaf] at hw
    rw [count_chance]
    unfold tnReal
    rw [count_decision, count_leaf]
    simp only [tnObs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    fin_cases i <;> simp_all

/-- **The hypothetical `d_F` node is a predictor node**: not live (the empty branch lies below
it), and every full-branch leaf below it passes the real `d_F`-node.
Source: `grounding.md` GR-D2
Kind: L -/
theorem tnV2_F_predictorAt :
    PredictorAt tnObs TnPt.F (fun x => Tree.decision TnPt.E fun y =>
      Tree.chance 2 (FinDistr.coin (if x = .large ∧ y = .large then p else 1 - p)
        (by split_ifs <;> linarith) (by split_ifs <;> linarith)) (tnReal L S)) := by
  refine ⟨fun h => ?_, fun x ℓ hw => ?_⟩
  · have := h .large ⟨.large, 1, .large, ()⟩
    rw [world_decision, world_chance] at this
    unfold tnReal at this
    rw [world_decision, world_leaf] at this
    simp [tnObs] at this
  · obtain ⟨y, i, act, ⟨⟩⟩ := ℓ
    rw [world_decision, world_chance] at hw
    unfold tnReal at hw
    rw [world_decision, world_leaf] at hw
    rw [count_decision, count_chance]
    unfold tnReal
    rw [count_decision, count_leaf]
    simp only [tnObs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    fin_cases i <;> simp_all

/-- `valueRepl` on a real branch: the live node keeps `C`. Source: none: infrastructure. Kind: L -/
theorem tnReal_valueRepl (θ C : Proc TnPt (fun _ => Box) ℚ) (i : Fin 2) :
    valueRepl tnObs θ C (tnReal L S i) =
      ∑ act, (C (if i = 0 then TnPt.F else TnPt.E)).w act * tnPay L S (decide (i = 0), act) := by
  unfold tnReal
  simp only [valueRepl, tnReal_not_predictorAt L S i, if_false]

/-- `usePred` on a real branch is `0` (no predictor node). Source: none: infrastructure. Kind: L -/
theorem tnReal_usePred (θ C : Proc TnPt (fun _ => Box) ℚ) (d : TnPt) (i : Fin 2) :
    usePred tnObs θ C d (tnReal L S i) = 0 := by
  unfold tnReal
  simp only [usePred, tnReal_not_predictorAt L S i, if_false, mul_zero, Finset.sum_const_zero]

/-- `countNonPred` on a real branch. Source: none: infrastructure. Kind: L -/
theorem tnReal_countNonPred (d : TnPt) (i : Fin 2) (act : Box) :
    countNonPred tnObs d (tnReal L S i) ⟨act, ()⟩ =
      if (if i = 0 then TnPt.F else TnPt.E) = d then 1 else 0 := by
  unfold tnReal
  simp only [countNonPred, tnReal_not_predictorAt L S i, if_false, Nat.add_zero]

/-- **`V_{B_θ}(C)` on TN-V2 as an explicit sum**: the two hypothetical nodes draw from `θ`, the
real nodes from `C`.
Source: `grounding.md` GR-2/GR-4 (the TN-V2 instance)
Kind: L -/
theorem tnV2_valueRepl (θ C : Proc TnPt (fun _ => Box) ℚ) :
    valueRepl tnObs θ C (tnV2 p h0 h1 L S) =
      ∑ x, (θ .F).w x * ∑ y, (θ .E).w y * ∑ i : Fin 2,
        (![if x = .large ∧ y = .large then p else 1 - p,
            1 - (if x = .large ∧ y = .large then p else 1 - p)] i) *
          ∑ act, (C (if i = 0 then TnPt.F else TnPt.E)).w act * tnPay L S (decide (i = 0), act) := by
  unfold tnV2
  simp only [valueRepl, tnV2_F_predictorAt p h0 h1 L S, tnV2_E_predictorAt p h0 h1 L S, if_true,
    tnReal_valueRepl]
  rfl

/-- **`usePred` at `d_F` on TN-V2 is `1`**: the hypothetical `d_F` node is passed on every run.
Source: `grounding.md` GR-4 (`𝔼[#pred_d]`)
Kind: L -/
theorem tnV2_usePred_F (θ C : Proc TnPt (fun _ => Box) ℚ) :
    usePred tnObs θ C .F (tnV2 p h0 h1 L S) = 1 := by
  unfold tnV2
  simp only [usePred, tnV2_F_predictorAt p h0 h1 L S, tnV2_E_predictorAt p h0 h1 L S, if_true,
    tnReal_usePred, mul_zero, Finset.sum_const_zero, add_zero]
  simp

/-- **`B_θ` on TN-V2 is almost fair**: after the replacement each path carries one real node.
Source: `grounding.md` GR-2 ("holds … on non-nested fibers")
Kind: L -/
theorem tnV2_replacePred_almostFair (θ : Proc TnPt (fun _ => Box) ℚ) :
    AlmostFair (replacePred tnObs θ (tnV2 p h0 h1 L S)) := by
  intro d ℓ'
  rw [count_replacePred]
  generalize fromRepl tnObs θ (tnV2 p h0 h1 L S) ℓ' = ℓ
  obtain ⟨x, y, i, act, ⟨⟩⟩ := ℓ
  unfold tnV2
  simp only [countNonPred, tnV2_F_predictorAt p h0 h1 L S, tnV2_E_predictorAt p h0 h1 L S,
    if_true, zero_add, tnReal_countNonPred]
  split_ifs <;> omega

end classify

/-! ## GR-2's numbers at `p = 3/4`, `L = 4`, `S = 1`, `C = (2/5, 3/7)` -/

/-- **`V_B(C) = 9427/4900`** (independent redraws).
Source: `grounding.md` GR-2 ("`9427/4900` on V2")
Kind: N+ -/
theorem tnV2_value_mixed :
    value tnMixed (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) = 9427 / 4900 := by
  rw [← value_replacePred_self tnObs, value_replacePred_eq_valueRepl, tnV2_valueRepl]
  simp [box_sum_univ, Fin.sum_univ_two, tnPay]
  norm_num

/-- **GR-2 on TN-V2: `V_{B_C}(C) = V_B(C) = 9427/4900`** (the instance of
`value_replacePred_self`).
Source: `grounding.md` GR-2
Kind: N+ -/
theorem tnV2_replacePred_value_self :
    value tnMixed (replacePred tnObs tnMixed (tnV2 (3/4) (by norm_num) (by norm_num) 4 1)) =
      9427 / 4900 := by
  rw [value_replacePred_self, tnV2_value_mixed]

/-- **The shared-seed value of `B_C` is the independent-redraw value** (`B_C` is almost fair).
Source: `grounding.md` GR-2 ("the exact label predictor is the shared-seed simulation exactly on
non-nested fibers")
Kind: N+ -/
theorem tnV2_replacePred_value'_mixed :
    value' tnMixed (replacePred tnObs tnMixed (tnV2 (3/4) (by norm_num) (by norm_num) 4 1)) =
      9427 / 4900 := by
  rw [← (tnV2_replacePred_almostFair (3/4) (by norm_num) (by norm_num) 4 1 tnMixed).value_eq_value'
    tnMixed, tnV2_replacePred_value_self]

/-- **The shared-seed value of TN-V2 itself under `C = (2/5, 3/7)` is `269/140`**: the
hypothetical draws seed the real nodes.
Source: `grounding.md` GR-2 ("V2: `269/140 ≠ 9427/4900`")
Kind: N+ -/
theorem tnV2_value'_mixed :
    value' tnMixed (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) = 269 / 140 := by
  unfold value'
  rw [tnV2_sum]
  simp only [tnV2_payoff', box_sum_univ, Fin.sum_univ_two]
  unfold leafLaw' tnV2 tnReal
  simp [leafLawSeed, Function.update_apply, tnPay, FinDistr.coin]
  norm_num

/-- **GR-2's shared-seed failure on the nested fiber** (rule 3's refutation row for the
shared-seed reading): `V'_{B_C}(C) = 9427/4900 ≠ 269/140 = V'_B(C)` — the exact-label chance
node is *not* the shared-seed simulation on TN-V2's nested `d_F`/`d_E` fibers for the mixed
`C = (2/5, 3/7)`.
Source: `grounding.md` GR-2 ("Under shared seed the identity fails for mixed `C` on fibers with a
positive-probability nested pair (V2: `269/140 ≠ 9427/4900`)")
Kind: N+
Fidelity: exact -/
theorem tnV2_seed_failure :
    value' tnMixed (replacePred tnObs tnMixed (tnV2 (3/4) (by norm_num) (by norm_num) 4 1)) ≠
      value' tnMixed (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) := by
  rw [tnV2_replacePred_value'_mixed, tnV2_value'_mixed]; norm_num

/-! ## GR-4's instance -/

/-- `V_{B_{θ'}}(C) = 2393/980` for `θ' = (1, 3/7)`, `C = (2/5, 3/7)`.
Source: `grounding.md` GR-4 (instance); mandate T14(b)
Kind: N+ -/
theorem tnV2_value_replacePred_mixed' :
    value tnMixed (replacePred tnObs tnMixed' (tnV2 (3/4) (by norm_num) (by norm_num) 4 1)) =
      2393 / 980 := by
  rw [value_replacePred_eq_valueRepl, tnV2_valueRepl]
  simp [box_sum_univ, Fin.sum_univ_two, tnPay]
  norm_num

/-- `TV((2/5, 3/5), (1, 0)) = 3/5`. Source: none: infrastructure. Kind: L -/
theorem tnMixed_tv_F : tv (tnMixed .F) (tnMixed' .F) = 3 / 5 := by
  unfold tv
  rw [box_sum_univ]
  simp
  norm_num

/-- TN-V2's payoffs at `L = 4`, `S = 1` lie in `[0, 5]`. Source: none: infrastructure. Kind: L -/
theorem tnV2_payoff_bounds (ℓ : (tnV2 (3/4) (by norm_num) (by norm_num) 4 1).Leaves) :
    0 ≤ payoff (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) ℓ ∧
      payoff (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) ℓ ≤ 5 := by
  obtain ⟨x, y, i, act, ⟨⟩⟩ := ℓ
  rw [tnV2_payoff']
  fin_cases i <;> cases act <;> simp [tnPay] <;> norm_num

/-- **GR-4 on TN-V2 (N+)**: with `θ = (2/5, 3/7)`, `θ' = (1, 3/7)` and `C = θ`, the verdict gap is
`|9427/4900 − 2393/980| = 1269/2450`, the bound `R · TV · usePred = 5 · (3/5) · 1 = 3`, and the
general theorem `value_replacePred_sub_le` applies with its full hypothesis package (labels agree
at `d_E`; payoffs in `[0, 5]`). The bound is loose by a factor of about six here (the coupling
bound counts every divergence as a full-range loss).
Source: `grounding.md` GR-4; mandate T14(b)
Kind: N+
Fidelity: exact -/
theorem tnV2_gr4_cell :
    |value tnMixed (replacePred tnObs tnMixed (tnV2 (3/4) (by norm_num) (by norm_num) 4 1)) -
      value tnMixed (replacePred tnObs tnMixed' (tnV2 (3/4) (by norm_num) (by norm_num) 4 1))| =
        1269 / 2450 ∧
    (5 - 0) * tv (tnMixed .F) (tnMixed' .F) *
      usePred tnObs tnMixed tnMixed .F (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) = 3 ∧
    |value tnMixed (replacePred tnObs tnMixed (tnV2 (3/4) (by norm_num) (by norm_num) 4 1)) -
      value tnMixed (replacePred tnObs tnMixed' (tnV2 (3/4) (by norm_num) (by norm_num) 4 1))| ≤
      (5 - 0) * tv (tnMixed .F) (tnMixed' .F) *
        usePred tnObs tnMixed tnMixed .F (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tnV2_replacePred_value_self, tnV2_value_replacePred_mixed']; norm_num
  · rw [tnMixed_tv_F, tnV2_usePred_F]; norm_num
  · exact value_replacePred_sub_le tnObs tnMixed tnMixed' tnMixed .F
      (fun d hd => by cases d <;> simp_all) 0 5 _
      (fun ℓ => (tnV2_payoff_bounds ℓ).1) (fun ℓ => (tnV2_payoff_bounds ℓ).2)

end Cleanroom.Decision.DpFirstpersonSc
