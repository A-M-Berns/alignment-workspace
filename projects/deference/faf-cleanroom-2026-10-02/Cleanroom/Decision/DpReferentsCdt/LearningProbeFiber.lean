import Cleanroom.Decision.DpReferentsCdt.LearningProbe

/-!
# The label-probe tree's real fiber and its R2-real

`LearningProbe.lean` gave single-instance forcing at one real node. Here the **real fiber** of the
probe tree for the realized-act events is characterised: of its fourteen `d`-nodes, the six real
`E = 0` nodes (one on each simulation path) are node-action-veridical and the others — the two
simulation nodes and the six real `E = 1` nodes, whose realized act is the coin's — are not
(`probe_realFiber`). Summing: `∑_{realFiber} R_q = 1 − ε` (`probe_realReach`),
`∑_{realFiber} R_q G_q(a) = (1−ε)(10 q_ε − [a = one])` (`probe_realForced`), hence
**`refR2Real a = 10 q_ε − [a = one]`** at every label for `ε < 1` (`probe_refR2Real`): the referent
form of the note's "forcing `−1` always" — the fill held at its `C`-statistics, the dollar the only
act-dependent term — on the label-probe rendering (findings F5).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

/-- The realized-act event family of the probe tree. Source: mandate §3.5. Kind: D -/
def probeActEv : (d : Unit) → Act2 → Finset ProbeW := fun _ a => probeAct a

section fiber

variable (ε : ℚ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)

/-- The real agent's `E = 0` node on the exploration simulation path `E' = 1, D' = x, K' = k'`.
Source: mandate T9; handoff item 2
Kind: D -/
def probeRealNode1 (x : Act2) (k' : Fin 2) : (probeTree ε hε0 hε1).DecNode :=
  ⟨1, some ⟨x, k', ⟨0, none⟩⟩⟩

/-- The real `E = 0` nodes on the deliberate simulation paths are node-action-veridical.
Source: `faithful.md` F3′ (node-action-veridicality); mandate T9
Kind: L -/
theorem probe_realNode0_nav (x : Act2) :
    NodeActionVeridical probeActEv (probeTree ε hε0 hε1) (probeRealNode0 ε hε0 hε1 x) := by
  intro ℓ a ha
  rcases ℓ with ⟨i, ℓ⟩
  fin_cases i
  · rcases ℓ with ⟨x', j, ℓ⟩
    by_cases hx : x' = x
    · subst hx
      fin_cases j
      · rcases ℓ with ⟨D, _⟩
        simp [probeRealNode0, probeTree, probeReal, edgeOf_chance, edgeOf_decision_some,
          edgeOf_decision_none] at ha
        subst ha
        simp [probeActEv, probeAct, probeA, probeTree, probeReal, probeLeaf, world]
      · simp [probeRealNode0, probeTree, probeReal, edgeOf_chance, edgeOf_decision_some] at ha
    · simp [probeRealNode0, probeTree, edgeOf_chance, edgeOf_decision_some, hx] at ha
  · simp [probeRealNode0, probeTree, edgeOf_chance] at ha

/-- The real `E = 0` nodes on the exploration simulation paths are node-action-veridical.
Source: `faithful.md` F3′; mandate T9
Kind: L -/
theorem probe_realNode1_nav (x : Act2) (k' : Fin 2) :
    NodeActionVeridical probeActEv (probeTree ε hε0 hε1) (probeRealNode1 ε hε0 hε1 x k') := by
  intro ℓ a ha
  rcases ℓ with ⟨i, ℓ⟩
  fin_cases i
  · simp [probeRealNode1, probeTree, edgeOf_chance] at ha
  · rcases ℓ with ⟨x', k, j, ℓ⟩
    by_cases hx : x' = x
    · subst hx
      by_cases hk : k = k'
      · subst hk
        fin_cases j
        · rcases ℓ with ⟨D, _⟩
          simp [probeRealNode1, probeTree, probeReal, edgeOf_chance, edgeOf_decision_some,
            edgeOf_decision_none] at ha
          subst ha
          simp [probeActEv, probeAct, probeA, probeTree, probeReal, probeLeaf, world]
        · simp [probeRealNode1, probeTree, probeReal, edgeOf_chance, edgeOf_decision_some] at ha
      · simp [probeRealNode1, probeTree, edgeOf_chance, edgeOf_decision_some, hk] at ha
    · simp [probeRealNode1, probeTree, edgeOf_chance, edgeOf_decision_some, hx] at ha

/-- The simulation's `E' = 0` node is not node-action-veridical (below its `one`-edge the real agent
may two-box). Source: `faithful.md` F3′; mandate T9. Kind: L -/
theorem probe_sim0_not_nav :
    ¬ NodeActionVeridical probeActEv (probeTree ε hε0 hε1) ⟨0, none⟩ := by
  intro h
  have := h ⟨0, .a, ⟨0, .b, ()⟩⟩ .a (by simp [probeTree, edgeOf_chance, edgeOf_decision_none])
  simp [probeActEv, probeAct, probeA, probeTree, probeReal, probeLeaf, world] at this

/-- The simulation's `E' = 1` node is not node-action-veridical. Source: `faithful.md` F3′. Kind: L -/
theorem probe_sim1_not_nav :
    ¬ NodeActionVeridical probeActEv (probeTree ε hε0 hε1) ⟨1, none⟩ := by
  intro h
  have := h ⟨1, .a, 0, ⟨0, .b, ()⟩⟩ .a (by simp [probeTree, edgeOf_chance, edgeOf_decision_none])
  simp [probeActEv, probeAct, probeA, probeTree, probeReal, probeLeaf, world] at this

/-- The real `E = 1` node on a deliberate simulation path is not node-action-veridical (its realized
act is the coin's). Source: `faithful.md` F3′; dp-core-097. Kind: L -/
theorem probe_real01_not_nav (x : Act2) :
    ¬ NodeActionVeridical probeActEv (probeTree ε hε0 hε1) ⟨0, some ⟨x, ⟨1, none⟩⟩⟩ := by
  intro h
  have := h ⟨0, x, ⟨1, .a, 1, ()⟩⟩ .a (by
    simp [probeTree, probeReal, edgeOf_chance, edgeOf_decision_some, edgeOf_decision_none])
  simp [probeActEv, probeAct, probeA, probeTree, probeReal, probeLeaf, world, coinAct] at this

/-- The real `E = 1` node on an exploration simulation path is not node-action-veridical.
Source: `faithful.md` F3′; dp-core-097. Kind: L -/
theorem probe_real11_not_nav (x : Act2) (k' : Fin 2) :
    ¬ NodeActionVeridical probeActEv (probeTree ε hε0 hε1) ⟨1, some ⟨x, k', ⟨1, none⟩⟩⟩ := by
  intro h
  have := h ⟨1, x, k', ⟨1, .a, 1, ()⟩⟩ .a (by
    simp [probeTree, probeReal, edgeOf_chance, edgeOf_decision_some, edgeOf_decision_none])
  simp [probeActEv, probeAct, probeA, probeTree, probeReal, probeLeaf, world, coinAct] at this

/-- **The real fiber of the probe tree is the set of six real `E = 0` nodes.**
Source: `faithful.md` Definition F2 (R2-real "averaged over the node-action-veridical instances");
mandate T9
Kind: L -/
theorem probe_realFiber :
    realFiber probeActEv (probeTree ε hε0 hε1) () =
      ((Finset.univ : Finset Act2).image fun x => probeRealNode0 ε hε0 hε1 x) ∪
        ((Finset.univ : Finset (Act2 × Fin 2)).image fun y => probeRealNode1 ε hε0 hε1 y.1 y.2) := by
  ext q
  rw [mem_realFiber, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨-, hnav⟩
    rcases q with ⟨i, q⟩
    fin_cases i
    · rcases q with _ | ⟨x, j, q⟩
      · exact absurd hnav (probe_sim0_not_nav ε hε0 hε1)
      · fin_cases j
        · rcases q with _ | ⟨D, e⟩
          · exact Or.inl ⟨x, Finset.mem_univ _, rfl⟩
          · exact e.elim
        · rcases q with _ | ⟨D, k, e⟩
          · exact absurd hnav (probe_real01_not_nav ε hε0 hε1 x)
          · exact e.elim
    · rcases q with _ | ⟨x, k', j, q⟩
      · exact absurd hnav (probe_sim1_not_nav ε hε0 hε1)
      · fin_cases j
        · rcases q with _ | ⟨D, e⟩
          · exact Or.inr ⟨(x, k'), Finset.mem_univ _, rfl⟩
          · exact e.elim
        · rcases q with _ | ⟨D, k, e⟩
          · exact absurd hnav (probe_real11_not_nav ε hε0 hε1 x k')
          · exact e.elim
  · rintro (⟨x, -, rfl⟩ | ⟨⟨x, k'⟩, -, rfl⟩)
    · exact ⟨rfl, probe_realNode0_nav ε hε0 hε1 x⟩
    · exact ⟨rfl, probe_realNode1_nav ε hε0 hε1 x k'⟩

/-- `probeRealNode0` is injective. Source: none: infrastructure. Kind: L -/
theorem probeRealNode0_injective : Function.Injective (probeRealNode0 ε hε0 hε1) := by
  intro x y h
  unfold probeRealNode0 at h
  have h1 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have h2 := Option.some.inj h1
  exact (Sigma.mk.inj_iff.mp h2).1

/-- `probeRealNode1` is injective. Source: none: infrastructure. Kind: L -/
theorem probeRealNode1_injective :
    Function.Injective fun y : Act2 × Fin 2 => probeRealNode1 ε hε0 hε1 y.1 y.2 := by
  rintro ⟨x, k⟩ ⟨y, k'⟩ h
  simp only [probeRealNode1] at h
  have h1 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have h2 := Option.some.inj h1
  obtain ⟨rfl, h3⟩ := Sigma.mk.inj_iff.mp h2
  have h4 := eq_of_heq h3
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp h4
  rfl

/-- The two families of real nodes are disjoint. Source: none: infrastructure. Kind: L -/
theorem probe_realNodes_disjoint :
    Disjoint ((Finset.univ : Finset Act2).image fun x => probeRealNode0 ε hε0 hε1 x)
      ((Finset.univ : Finset (Act2 × Fin 2)).image fun y => probeRealNode1 ε hε0 hε1 y.1 y.2) := by
  rw [Finset.disjoint_left]
  rintro q hq hq'
  rw [Finset.mem_image] at hq hq'
  obtain ⟨x, -, rfl⟩ := hq
  obtain ⟨⟨y, k'⟩, -, h⟩ := hq'
  have := (Sigma.mk.inj_iff.mp h).1
  exact absurd this (by decide)

variable (C : Proc Unit (fun _ => Act2) ℚ)

/-- `R_q` at a deliberate-path real node: `(1−ε) · C(d)(x) · (1−ε)`. Source: none: infrastructure.
Kind: L -/
theorem probe_reach_real0 (x : Act2) :
    reach C (probeTree ε hε0 hε1) (probeRealNode0 ε hε0 hε1 x) = (1 - ε) * ((C ()).w x * (1 - ε)) := by
  simp [probeRealNode0, probeTree, probeReal, reach, FinDistr.coin]

/-- `R_q` at an exploration-path real node: `ε · C(d)(x) · (1/2) · (1−ε)`. Source: none: infrastructure.
Kind: L -/
theorem probe_reach_real1 (x : Act2) (k' : Fin 2) :
    reach C (probeTree ε hε0 hε1) (probeRealNode1 ε hε0 hε1 x k') =
      ε * ((C ()).w x * (1 / 2 * (1 - ε))) := by
  fin_cases k' <;> simp [probeRealNode1, probeTree, probeReal, reach, FinDistr.coin, FinDistr.fair] <;>
    norm_num

/-- **`∑_{q ∈ realFiber} R_q(C) = 1 − ε`**: the real `E = 0` nodes carry exactly the non-exploration
mass. Source: none: infrastructure. Kind: L -/
theorem probe_realReach : realReach probeActEv C (probeTree ε hε0 hε1) () = 1 - ε := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  unfold realReach
  rw [probe_realFiber, Finset.sum_union (probe_realNodes_disjoint ε hε0 hε1),
    Finset.sum_image (fun x _ y _ h => probeRealNode0_injective ε hε0 hε1 h),
    Finset.sum_image (fun x _ y _ h => probeRealNode1_injective ε hε0 hε1 h),
    Fintype.sum_prod_type]
  simp only [probe_reach_real0, probe_reach_real1]
  simp [Act2.sum_univ, Fin.sum_univ_two, hb]
  ring

/-- `forcedBelow` at a deliberate-path real node: `(1−ε) · C(d)(x) · (1−ε) · (10·[x = one] − [a = one])`.
Source: none: infrastructure. Kind: L -/
theorem probe_forcedBelow_real0 (x a : Act2) :
    forcedBelow (probeTree ε hε0 hε1) (NodePolicy.ofProc C _) (probeRealNode0 ε hε0 hε1 x) a =
      (1 - ε) * ((C ()).w x * ((1 - ε) *
        ((if x = .a then 10 else 0) - (if a = .a then 1 else 0)))) := by
  unfold probeRealNode0 probeTree
  rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance]
  simp only [Matrix.cons_val_zero]
  rw [forcedBelow_decision_some, NodePolicy.ofProc_none, NodePolicy.ofProc_restrictDecision]
  unfold probeReal
  rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance]
  simp only [Matrix.cons_val_zero]
  rw [forcedBelow_decision_none, NodePolicy.ofProc_restrictDecision]
  unfold valueNode probeLeaf
  rw [Tree.sum_leaves_leaf]
  simp [leafLawNode, probePay, probeA, FinDistr.coin]

/-- `forcedBelow` at an exploration-path real node:
`ε · C(d)(x) · (1/2) · (1−ε) · (10·[K' = one] − [a = one])`. Source: none: infrastructure. Kind: L -/
theorem probe_forcedBelow_real1 (x : Act2) (k' : Fin 2) (a : Act2) :
    forcedBelow (probeTree ε hε0 hε1) (NodePolicy.ofProc C _) (probeRealNode1 ε hε0 hε1 x k') a =
      ε * ((C ()).w x * (1 / 2 * ((1 - ε) *
        ((if coinAct k' = .a then 10 else 0) - (if a = .a then 1 else 0))))) := by
  unfold probeRealNode1 probeTree
  rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance]
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  rw [forcedBelow_decision_some, NodePolicy.ofProc_none, NodePolicy.ofProc_restrictDecision,
    forcedBelow_chance, NodePolicy.ofProc_restrictChance]
  unfold probeReal
  rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance]
  simp only [Matrix.cons_val_zero]
  rw [forcedBelow_decision_none, NodePolicy.ofProc_restrictDecision]
  unfold valueNode probeLeaf
  rw [Tree.sum_leaves_leaf]
  simp [leafLawNode, probePay, probeA, FinDistr.coin, FinDistr.fair]
  all_goals (fin_cases k' <;> cases x <;> cases a <;> simp [coinAct] <;> norm_num)

/-- **`∑_{q ∈ realFiber} R_q G_q(a) = (1−ε)(10 q_ε − [a = one])`**: forcing at the real nodes holds the
fill at its `C`-statistics `q_ε`.
Source: `faithful.md` FA-19′ (the forcing referent "holds the prediction at its `C`-statistics");
mandate T9
Kind: P
Fidelity: exact -/
theorem probe_realForced (a : Act2) :
    realForced probeActEv C (probeTree ε hε0 hε1) () a =
      (1 - ε) * (10 * ((1 - ε) * (C ()).w .a + ε / 2) - if a = .a then 1 else 0) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  rw [realForced_unit, probe_realFiber, Finset.sum_union (probe_realNodes_disjoint ε hε0 hε1),
    Finset.sum_image (fun x _ y _ h => probeRealNode0_injective ε hε0 hε1 h),
    Finset.sum_image (fun x _ y _ h => probeRealNode1_injective ε hε0 hε1 h),
    Fintype.sum_prod_type]
  simp only [probe_forcedBelow_real0, probe_forcedBelow_real1]
  cases a <;> simp [Act2.sum_univ, Fin.sum_univ_two, coinAct, hb] <;> ring

/-- **R2-real on the label-probe tree: `refR2Real a = 10 q_ε − [a = one]`** at every label (for
`ε < 1`): the fill term `10 q_ε` is act-independent, the gap is exactly `−1` — the referent form of
the note's "forcing `−1` always" on this rendering (contrast `learn_gNode0` on the `(r_D, r_K)`
rendering, findings F5). Two-boxing at every label, as classical CDT by construal (FA-19′,
ATTRIBUTION-UNVETTED).
Source: `newcomb-correction.md` ("forcing at the live node, `−1` always"); `faithful.md` FA-19′;
mandate T9
Kind: P
Fidelity: exact for the tree
Hyps: (a) `ε < 1` -/
theorem probe_refR2Real (hε : ε < 1) (a : Act2) :
    refR2Real probeActEv C (probeTree ε hε0 hε1) () a =
      10 * ((1 - ε) * (C ()).w .a + ε / 2) - if a = .a then 1 else 0 := by
  have h1 : (1 - ε) ≠ 0 := by linarith
  unfold refR2Real
  rw [probe_realForced, probe_realReach, mul_div_cancel_left₀ _ h1]

/-- **R2-SIA on the label-probe tree has gap `9(1−ε)`**: Theorem 1's reach-weighted forcing over
*all* `d`-nodes adds the simulation's `+10` (it reads the label) to the real nodes' `−1` and recovers
the deviation `V(δ_one) − V(δ_two) = 9(1−ε)` — the SIA weighting, not the forcing type, is what
makes the label-probe one-box (FA-19′'s diagnosis of Remark 3.11).
Source: [[decision-problems-v2]] §8 Theorem 1; `faithful.md` FA-19′, FA-21′ (the weighting axis);
mandate T9, T11
Kind: P
Fidelity: exact -/
theorem probe_refR2Sia_gap :
    refR2Sia C (probeTree ε hε0 hε1) () .a - refR2Sia C (probeTree ε hε0 hε1) () .b =
      9 * (1 - ε) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := Act2.w_b_eq _
  unfold refR2Sia probeTree
  simp only [probeReal, siaSum_chance, siaSum_decision_self, siaSum_leaf, mul_zero,
    Finset.sum_const_zero, zero_add, value_leaf, value_chance, value_decision, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  simp [probeLeaf, probePay, probeA, coinAct, FinDistr.coin, FinDistr.fair, Act2.sum_univ, hb]
  ring

end fiber

end Cleanroom.Decision.DpReferentsCdt
