import Cleanroom.Bli.UdtBliSist.Iterated

/-!
# Audit round 2 (adversarial) probe: the `K`-node family at `K = 2` — the other node's tables are
inert at `Ask_0` on positive cells, and the residual is positive

`Iter.classInert_node` is stated for every `K`; this checks it is not vacuous at `K = 2`: with
`ε = 1/5` (`2Kε = 4/5 < 1`, residual `1/5 > 0`) node `1`'s tables `Ask_1`, `Rec_1` have positive
cells at `Ask_0` under both actions, so the inertness `condEU Ask_1 Ask_0 give = condEU Ask_1 Ask_0
refuse` holds with content; and the node-`0` verdict is `ε·(V − c)`. Not imported by the library.
-/

namespace Cleanroom.Bli.UdtBliSist.Iter

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

/-- `ε = 1/5` is admissible at `K = 2`. -/
lemma hε : (0 : ℚ) ≤ 1 / 5 := by norm_num

lemma hK : 2 * (2 : ℕ) * (1 / 5 : ℚ) ≤ 1 := by norm_num

/-- The instance's data at `K = 2`. -/
abbrev D₂ (c V : ℚ) (r₀ : Bool → ℚ) : IndepData (iterIndex 2) 1 (iterTables 2) Bool :=
  iterData 2 (wIter 2 (1 / 5)) (wIter_nonneg 2 hε hK) (wIter_sum 2 (1 / 5)) c V r₀

/-- The instance's prior at `K = 2`. -/
abbrev P₂ (c V : ℚ) (r₀ : Bool → ℚ) : FiniteBLIPrior (iterIndex 2) 1 (iterTables 2) Bool :=
  iterPrior 2 (wIter 2 (1 / 5)) (wIter_nonneg 2 hε hK) (wIter_sum 2 (1 / 5)) c V r₀

/-- The residual has mass `1/5 > 0`. -/
theorem residual_pos : 0 < wIter 2 (1 / 5 : ℚ) none := by norm_num [wIter]

/-- Node `1`'s tables have positive cells at `Ask_0` under both actions. -/
theorem node1_cells_pos (c V : ℚ) (r₀ : Bool → ℚ) (a : Bool) :
    0 < (P₂ c V r₀).jointMass (askT 2 1) (askT 2 0) a ∧
      0 < (P₂ c V r₀).jointMass (recT 2 1) (askT 2 0) a := by
  constructor
  · change 0 < (D₂ c V r₀).toPrior.jointMass (askT 2 1) (askT 2 0) a
    rw [jointMass_toPrior_of_injective (D₂ c V r₀) (st_injective 2) (some (true, 1)) (askT 2 1) rfl,
      massOf_point]
    change 0 < wIter 2 (1 / 5) (some (true, 1)) * (1 / 2)
    norm_num [wIter]
  · change 0 < (D₂ c V r₀).toPrior.jointMass (recT 2 1) (askT 2 0) a
    rw [jointMass_toPrior_of_injective (D₂ c V r₀) (st_injective 2) (some (false, 1)) (recT 2 1) rfl,
      massOf_point]
    change 0 < wIter 2 (1 / 5) (some (false, 1)) * (1 / 2)
    norm_num [wIter]

/-- `Ask_1 ∉ {Ask_0, Rec_0}`. -/
lemma askT1_not_mem : askT 2 1 ∉ nodeClass 2 0 := by
  simp only [nodeClass, Finset.mem_insert, Finset.mem_singleton, askT, recT, (st_injective 2).eq_iff]
  decide

/-- **Inertness with content at `K = 2`**: `condEU Ask_1 Ask_0 give = condEU Ask_1 Ask_0 refuse`
on positive cells (from `classInert_node`). -/
theorem node1_inert_at_node0 (c V : ℚ) (r₀ : Bool → ℚ) :
    (P₂ c V r₀).condEU (askT 2 1) (askT 2 0) true = (P₂ c V r₀).condEU (askT 2 1) (askT 2 0) false :=
  classInert_node 2 _ _ _ c V r₀ 0 (askT 2 1) askT1_not_mem true false
    (node1_cells_pos c V r₀ true).1 (node1_cells_pos c V r₀ false).1

/-- The node-`0` verdict at `K = 2`, `ε = 1/5`: `EU Ask_0 give − EU Ask_0 refuse = (V − c)/5`. -/
theorem verdict_node0 (c V : ℚ) (r₀ : Bool → ℚ) :
    (P₂ c V r₀).EU (askT 2 0) true - (P₂ c V r₀).EU (askT 2 0) false = (V - c) / 5 := by
  rw [verdict]
  simp only [wIter]
  ring

end Cleanroom.Bli.UdtBliSist.Iter
