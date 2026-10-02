import Cleanroom.Decision.DpReferentsCdt.Defs
import Cleanroom.Decision.DpCalibration.Examples

/-!
# FA-18's Transparent-Newcomb row: V2 at `d_E`

Mandate T1(c): on `dp-core-tree`'s `tnV2 p L S` (query `d_F` then `d_E` hypothetically, the chance
node sends the run to the full branch with probability `p` iff both answers are `large`, the real
branch queries `d_F` or `d_E` and records the act), at the point `d_E` under the one-boxer
`procLarge = (large, large)`: R1-prior `(pL, (1−p)L + pS)`, R1-state `(0, S)`, R2-SIA
`(pL, (1−p)(L + S))`, R2-real `(0, S)` — at `(p, L, S) = (3/4, 4, 1)` the table's
`(3, 7/4)`, `(0, 1)`, `(3, 5/4)`, `(0, 1)` (`tnV2_row_34`). The real fiber at `d_E` is the four real
`E`-nodes of the empty branches (`tnV2_realFiber_E`); the two hypothetical `E`-nodes are not
node-action-veridical. `d_E` is a point whose payoff-relevant simulation sits *above* the real node:
R1-state and R2-real agree (`(0, S)`: the real draw in the empty box pays `S` iff two-boxing), while
R1-prior and R2-SIA carry the hypothetical node's effect on the fill — the weighting axis of FA-21′,
and Q13′'s member `tnV2` at `d_E` (EV = R1-state without the exactly-one clause).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

section tn

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-- Sums over the sixteen leaves of V2. Source: none: infrastructure. Kind: L -/
theorem tnV2_sum (f : (tnV2 p h0 h1 L S).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ x, ∑ y, ∑ i, ∑ act, f ⟨x, y, i, act, ()⟩ := by
  unfold tnV2 at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (∑ ℓ : (tnReal L S i).Leaves, f ⟨x, y, i, ℓ⟩) = _
  unfold tnReal
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The real `E`-node on the empty branch below the hypothetical answers `(x, y)`.
Source: [[decision-problems-v2]] §7.2 (the real query `d_E` on the empty branch); mandate T1(c)
Kind: D -/
def tnRealE (x y : Box) : (tnV2 p h0 h1 L S).DecNode := some ⟨x, some ⟨y, ⟨1, none⟩⟩⟩

/-- The real `E`-nodes carry `d_E`. Source: none: infrastructure. Kind: L -/
theorem tnRealE_pt (x y : Box) : pt (tnV2 p h0 h1 L S) (tnRealE p h0 h1 L S x y) = .E := by
  simp [tnRealE, tnV2, tnReal, pt]

/-- The real `E`-nodes are node-action-veridical. Source: `faithful.md` F3′. Kind: L -/
theorem tnRealE_nav (x y : Box) :
    NodeActionVeridical tnActEv (tnV2 p h0 h1 L S) (tnRealE p h0 h1 L S x y) := by
  intro ℓ a ha
  rcases ℓ with ⟨x', y', i, ℓ'⟩
  by_cases hx : x' = x
  · subst hx
    by_cases hy : y' = y
    · subst hy
      by_cases hi : i = 1
      · subst hi
        simp [tnRealE, tnV2, edgeOf_decision_some, edgeOf_chance] at ha
        rcases ℓ' with ⟨act, _⟩
        simp [tnReal, edgeOf_decision_none] at ha
        subst ha
        simp [tnActEv, tnV2, tnReal, world]
      · simp [tnRealE, tnV2, edgeOf_decision_some, edgeOf_chance, hi] at ha
    · simp [tnRealE, tnV2, edgeOf_decision_some, hy] at ha
  · simp [tnRealE, tnV2, edgeOf_decision_some, hx] at ha

/-- The hypothetical `E`-node below answer `x` is not node-action-veridical (its leaves record the
real draw, not the answer). Source: `faithful.md` F3′ ("hypothetical" nodes). Kind: L -/
theorem tnHypE_not_nav (x : Box) :
    ¬ NodeActionVeridical tnActEv (tnV2 p h0 h1 L S) (some ⟨x, none⟩) := by
  intro h
  have := h ⟨x, .large, 1, .both, ()⟩ .large (by
    simp [tnV2, edgeOf_decision_some, edgeOf_decision_none])
  simp [tnActEv, tnV2, tnReal, world] at this

/-- **The real fiber of V2 at `d_E` is the set of four real `E`-nodes.**
Source: `faithful.md` Definition F2 (the node-action-veridical instances); mandate T1(c)
Kind: L -/
theorem tnV2_realFiber_E :
    realFiber tnActEv (tnV2 p h0 h1 L S) .E =
      (Finset.univ : Finset (Box × Box)).image fun xy => tnRealE p h0 h1 L S xy.1 xy.2 := by
  ext q
  rw [mem_realFiber, Finset.mem_image]
  constructor
  · rintro ⟨hpt, hnav⟩
    rcases q with _ | ⟨x, _ | ⟨y, i, _ | ⟨act, e⟩⟩⟩
    · simp [tnV2, pt] at hpt
    · exact absurd hnav (tnHypE_not_nav p h0 h1 L S x)
    · fin_cases i
      · simp [tnV2, tnReal, pt] at hpt
      · exact ⟨(x, y), Finset.mem_univ _, rfl⟩
    · exact e.elim
  · rintro ⟨⟨x, y⟩, -, rfl⟩
    exact ⟨tnRealE_pt p h0 h1 L S x y, tnRealE_nav p h0 h1 L S x y⟩

/-- `tnRealE` is injective. Source: none: infrastructure. Kind: L -/
theorem tnRealE_injective :
    Function.Injective fun xy : Box × Box => tnRealE p h0 h1 L S xy.1 xy.2 := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [tnRealE] at h
  have h1 := Option.some.inj h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h1
  have h3 := Option.some.inj (eq_of_heq h2)
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp h3
  rfl

variable (C : Proc TnPt (fun _ => Box) ℚ)

/-- `R_q` at a real `E`-node: `C(F)(x) · C(E)(y) · (1 − p_{xy})`. Source: none: infrastructure. Kind: L -/
theorem tnV2_reach_realE (x y : Box) :
    reach C (tnV2 p h0 h1 L S) (tnRealE p h0 h1 L S x y) =
      (C .F).w x * ((C .E).w y * (1 - if x = .large ∧ y = .large then p else 1 - p)) := by
  simp [tnRealE, tnV2, tnReal, reach, FinDistr.coin]

/-- `forcedBelow` at a real `E`-node: `R_q · tnPay(0, a)`. Source: none: infrastructure. Kind: L -/
theorem tnV2_forcedBelow_realE (x y : Box) (a : Box) :
    forcedBelow (tnV2 p h0 h1 L S) (NodePolicy.ofProc C _) (tnRealE p h0 h1 L S x y) a =
      (C .F).w x * ((C .E).w y * ((1 - if x = .large ∧ y = .large then p else 1 - p) *
        tnPay L S (false, a))) := by
  unfold tnRealE tnV2
  rw [forcedBelow_decision_some, NodePolicy.ofProc_none, NodePolicy.ofProc_restrictDecision,
    forcedBelow_decision_some, NodePolicy.ofProc_none, NodePolicy.ofProc_restrictDecision,
    forcedBelow_chance, NodePolicy.ofProc_restrictChance]
  unfold tnReal
  rw [forcedBelow_decision_none, NodePolicy.ofProc_restrictDecision]
  unfold valueNode
  rw [Tree.sum_leaves_leaf]
  simp [leafLawNode, FinDistr.coin]

/-- **`∑_{q ∈ realFiber(E)} R_q`** on V2: the empty-branch mass. Source: none: infrastructure. Kind: L -/
theorem tnV2_realReach_E :
    realReach tnActEv C (tnV2 p h0 h1 L S) .E =
      ∑ x, ∑ y, (C .F).w x * ((C .E).w y * (1 - if x = .large ∧ y = .large then p else 1 - p)) := by
  unfold realReach
  rw [tnV2_realFiber_E, Finset.sum_image (fun x _ y _ h => tnRealE_injective p h0 h1 L S h),
    Fintype.sum_prod_type]
  simp only [tnV2_reach_realE]

/-- **`∑_{q ∈ realFiber(E)} R_q G_q(a)`** on V2: the empty-branch mass times `tnPay(0, a)`.
Source: none: infrastructure. Kind: L -/
theorem tnV2_realForced_E (a : Box) :
    realForced tnActEv C (tnV2 p h0 h1 L S) .E a =
      (∑ x, ∑ y, (C .F).w x * ((C .E).w y * (1 - if x = .large ∧ y = .large then p else 1 - p))) *
        tnPay L S (false, a) := by
  unfold realForced
  rw [tnV2_realFiber_E, Finset.sum_image (fun x _ y _ h => tnRealE_injective p h0 h1 L S h),
    Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [dif_pos (tnRealE_pt p h0 h1 L S x y), tnV2_forcedBelow_realE]
  ring

/-- **R2-real at `d_E` on V2 is `tnPay(0, ·) = (0, S)`** at every label with positive empty-branch
mass: the real draw in the empty box pays `S` iff two-boxing, the hypothetical node's effect on the
fill is not the agent's.
Source: `faithful.md` FA-18 (TN-V2 `d_E` row, R2-real `(0, 1)`); mandate T1(c)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ∑_{realFiber(E)} R_q` -/
theorem tnV2_refR2Real_E (a : Box)
    (hpos : 0 < ∑ x, ∑ y, (C .F).w x * ((C .E).w y *
      (1 - if x = .large ∧ y = .large then p else 1 - p))) :
    refR2Real tnActEv C (tnV2 p h0 h1 L S) .E a = tnPay L S (false, a) := by
  unfold refR2Real
  rw [tnV2_realForced_E, tnV2_realReach_E, mul_div_cancel_left₀ _ hpos.ne']

/-- **R1-prior at `d_E` under the one-boxer**: `V(C[E↦large]) = pL`, `V(C[E↦both]) = (1−p)L + pS` —
deviating `d_E` changes the hypothetical answer and hence the fill.
Source: `faithful.md` FA-18 (TN-V2 `d_E` row, R1-prior `(3, 7/4)`); mandate T1(c)
Kind: P
Fidelity: exact -/
theorem tnV2_refR1Prior_E_large (a : Box) :
    refR1Prior procLarge (tnV2 p h0 h1 L S) .E a =
      if a = .large then p * L else (1 - p) * L + p * S := by
  unfold refR1Prior value
  rw [tnV2_sum]
  cases a <;> simp [tnV2, tnReal, leafLaw, payoff, tnPay, procLarge, Proc.ofFun, Proc.deviatePure,
    Proc.deviate, Function.update, Box.sum_univ, Fin.sum_univ_two, FinDistr.coin]

/-- `ν_{C[E↦a]}(O_E)` under the one-boxer: `1 − p` for `large`, `p` for `both`.
Source: none: infrastructure. Kind: L -/
theorem tnV2_nu_E_large (a : Box) :
    nu (procLarge.deviatePure .E a) (tnV2 p h0 h1 L S) (tnObs .E) =
      if a = .large then 1 - p else p := by
  rw [nu_eq_sum, tnV2_sum]
  cases a <;> simp [tnV2, tnReal, leafLaw, world, tnObs, procLarge, Proc.ofFun, Proc.deviatePure,
    Proc.deviate, Function.update, Box.sum_univ, Fin.sum_univ_two, FinDistr.coin]

/-- `paySum_{C[E↦a]}(O_E)` under the one-boxer: `0` for `large`, `pS` for `both`.
Source: none: infrastructure. Kind: L -/
theorem tnV2_paySum_E_large (a : Box) :
    paySum (procLarge.deviatePure .E a) (tnV2 p h0 h1 L S) (tnObs .E) =
      if a = .large then 0 else p * S := by
  rw [paySum_eq_sum_ite, tnV2_sum]
  cases a <;> simp [tnV2, tnReal, leafLaw, world, payoff, tnPay, tnObs, procLarge, Proc.ofFun,
    Proc.deviatePure, Proc.deviate, Function.update, Box.sum_univ, Fin.sum_univ_two,
    FinDistr.coin]

/-- **R1-state at `d_E` under the one-boxer is `(0, S)`** for `0 < p < 1`: conditioning the deviation
on the empty box leaves only the real draw's `S`.
Source: `faithful.md` FA-18 (TN-V2 `d_E` row, R1-state `(0, 1)`); mandate T1(c)
Kind: P
Fidelity: exact
Hyps: (a) `0 < p < 1` -/
theorem tnV2_refR1State_E_large (hp0 : 0 < p) (hp1 : p < 1) (a : Box) :
    refR1State tnObs procLarge (tnV2 p h0 h1 L S) .E a = if a = .both then S else 0 := by
  unfold refR1State condExp
  rw [tnV2_nu_E_large, tnV2_paySum_E_large]
  have h1 : 1 - p ≠ 0 := by linarith
  cases a <;> simp <;> field_simp

/-- **R2-SIA at `d_E` under the one-boxer**: `(pL, (1−p)(L + S))` — Theorem 1's sum counts the
hypothetical `E`-node's forcing (which moves the fill) with the real node's.
Source: `faithful.md` FA-18 (TN-V2 `d_E` row, R2-SIA `(3, 5/4)`); [[decision-problems-v2]] §8
Theorem 1; mandate T1(c)
Kind: P
Fidelity: exact -/
theorem tnV2_refR2Sia_E_large (a : Box) :
    refR2Sia procLarge (tnV2 p h0 h1 L S) .E a =
      if a = .large then p * L else (1 - p) * (L + S) := by
  unfold refR2Sia tnV2
  simp only [siaSum_decision, siaSum_chance, siaSum_leaf, value_leaf, value_chance, value_decision,
    tnReal, Fin.sum_univ_two]
  cases a <;> simp [tnPay, procLarge, Proc.ofFun, Box.sum_univ, FinDistr.coin] <;> ring

/-- **FA-18's TN-V2 `d_E` row** at `(p, L, S) = (3/4, 4, 1)` under the one-boxer: R1-prior `(3, 7/4)`,
R1-state `(0, 1)`, R2-SIA `(3, 5/4)`, R2-real `(0, 1)` — the `O_d`-conditioned referents agree and
the prior-level ones differ, a payoff-relevant simulation sitting above the real node.
Source: `faithful.md` FA-18 (TN-V2 `d_E` row); `sl-workflow` dp-sl-073 (Q13′: `tnV2` at `d_E` is a
member of the EV = R1-state class); mandate T1(c)
Kind: N+ -/
theorem tnV2_row_34 :
    let B := tnV2 (3/4) (by norm_num) (by norm_num) 4 1
    (refR1Prior procLarge B .E .large = 3 ∧ refR1Prior procLarge B .E .both = 7/4) ∧
    (refR1State tnObs procLarge B .E .large = 0 ∧ refR1State tnObs procLarge B .E .both = 1) ∧
    (refR2Sia procLarge B .E .large = 3 ∧ refR2Sia procLarge B .E .both = 5/4) ∧
    (refR2Real tnActEv procLarge B .E .large = 0 ∧ refR2Real tnActEv procLarge B .E .both = 1) := by
  intro B
  have hpos : 0 < ∑ x, ∑ y, (procLarge .F).w x * ((procLarge .E).w y *
      (1 - if x = .large ∧ y = .large then (3/4 : ℚ) else 1 - 3/4)) := by
    norm_num [procLarge, Proc.ofFun, Box.sum_univ]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [tnV2_refR1Prior_E_large]; simp <;> norm_num
  · rw [tnV2_refR1Prior_E_large]; simp <;> norm_num
  · rw [tnV2_refR1State_E_large (3/4) (by norm_num) (by norm_num) 4 1
      (by norm_num : (0 : ℚ) < 3/4) (by norm_num : (3/4 : ℚ) < 1)]
    simp
  · rw [tnV2_refR1State_E_large (3/4) (by norm_num) (by norm_num) 4 1
      (by norm_num : (0 : ℚ) < 3/4) (by norm_num : (3/4 : ℚ) < 1)]
    simp
  · rw [tnV2_refR2Sia_E_large]; simp <;> norm_num
  · rw [tnV2_refR2Sia_E_large]; simp <;> norm_num
  · rw [tnV2_refR2Real_E _ _ _ _ _ _ _ hpos]; simp [tnPay]
  · rw [tnV2_refR2Real_E _ _ _ _ _ _ _ hpos]; simp [tnPay]

end tn

end Cleanroom.Decision.DpReferentsCdt
