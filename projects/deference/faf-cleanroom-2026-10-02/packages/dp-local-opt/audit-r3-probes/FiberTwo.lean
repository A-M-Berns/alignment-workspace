import Cleanroom.Decision.DpLocalOpt.GatedInduction

/-!
# Audit round 3 (adversarial) probe: `stronglyFair_strictLocalMax_isOptimal` on a two-node fiber

Not imported by the library. The package's inhabitant of the theorem's hypothesis package
(`stronglyFair_strictLocalMax_inhabited`) lives on `twoPoint 2 4 1`, where `pt` is injective:
every fiber is a singleton, `StronglyFair` holds by `LabIso.refl`, and the theorem reduces to
`twoPoint_strictLocalMax_isOptimal`. Nothing in the package inhabits the package on a tree with a
fiber of size `≥ 2` — the regime where strong fairness says something (`LabIso` between *distinct*
nodes), where `siaSum_eq_fiberMass_mul_of_iso` sums over two nodes, and where the induction's
minimality step (`exists_node_lt_of_mem_queried_child`) is exercised against a real gate.

This probe builds `gatedTwo`: `p1: out → 1; in → fair coin over two copies of
decision p2 [x → 4, y → 1/2]`. It has `V(p, q) = p + (1 − p)(4q + (1 − q)/2)` — the value
function of `fairDepth2 = twoPoint 1 4 (1/2)` — but a two-node `p2`-fiber. Checked:

1. `gatedTwo_stronglyFair` — strongly fair (the two `p2`-subtrees are equal, hence `LabIso`), with
   `pt` **not** injective (`gatedTwo_pt_not_injective`), so `StronglyFair.of_injective_pt` does not
   apply and the fiber genuinely has two nodes (`p2node_ne`, `p2node_mem`).
2. `gatedTwo_inX_isStrictLocalMax` — `(in, x)` is a strict local maximum (`ε = 1/3`).
3. `gatedTwo_inX_isOptimal` — optimality **from the general theorem**, and
   `gatedTwo_inX_isOptimal'` — the same fact checked directly from the closed form, so the
   theorem's conclusion is confirmed independently on this instance (`V ≤ 4 = V(in, x)`,
   `V(out, y) = 1`).
-/

namespace Cleanroom.Decision.DpLocalOpt.AuditR3

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

/-- The `p2`-gadget `decision p2 [x → 4, y → 1/2]`. -/
def p2gadget : Tree TwoW Pt2 (fun _ => Act2) ℚ :=
  .decision .p2 fun
    | .a => .leaf .inX 4
    | .b => .leaf .inY (1/2)

/-- `p1: out → 1; in → fair coin over two copies of `p2gadget``. -/
def gatedTwo : Tree TwoW Pt2 (fun _ => Act2) ℚ :=
  .decision .p1 fun
    | .a => .leaf .out 1
    | .b => .chance 2 FinDistr.fair fun _ => p2gadget

/-- The closed form: `fairDepth2`'s value function. -/
theorem gatedTwo_value (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    value (proc2 p q hp0 hp1 hq0 hq1) gatedTwo = p + (1 - p) * (4 * q + (1 - q) / 2) := by
  simp only [gatedTwo, p2gadget, value_decision, value_chance, value_leaf, Act2.sum_univ,
    Fin.sum_univ_two, proc2_p1, proc2_p2, FinDistr.act2_a, FinDistr.act2_b, FinDistr.fair,
    FinDistr.coin, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Same value function as `fairDepth2 = twoPoint 1 4 (1/2)`. -/
theorem gatedTwo_value_eq_fairDepth2 (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    value (proc2 p q hp0 hp1 hq0 hq1) gatedTwo = value (proc2 p q hp0 hp1 hq0 hq1) fairDepth2 := by
  rw [gatedTwo_value, fairDepth2, twoPoint_value]; ring

/-- The `i`-th `p2`-node (`i : Fin 2`), under `in` and the coin's branch `i`. -/
def p2node (i : Fin 2) : gatedTwo.DecNode := some ⟨.b, ⟨i, none⟩⟩

theorem p2node_mem (i : Fin 2) : p2node i ∈ fiber gatedTwo .p2 :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

/-- The coin index of a `p2`-node (`0` elsewhere). -/
def nodeIdx : gatedTwo.DecNode → Fin 2
  | some ⟨.b, ⟨i, _⟩⟩ => i
  | _ => 0

/-- The two `p2`-nodes are distinct: the fiber has (at least) two nodes. -/
theorem p2node_ne : p2node 0 ≠ p2node 1 :=
  fun h => absurd (congrArg nodeIdx h) (by decide)

/-- `pt` is not injective on `gatedTwo`: `StronglyFair.of_injective_pt` does not apply. -/
theorem gatedTwo_pt_not_injective : ¬ Function.Injective (pt gatedTwo) :=
  fun h => p2node_ne (h (rfl : pt gatedTwo (p2node 0) = pt gatedTwo (p2node 1)))

/-- Every node of `gatedTwo` is the root (point `p1`, subtree the whole tree) or a `p2`-node
(subtree `p2gadget`). -/
theorem gatedTwo_subtree (q : gatedTwo.DecNode) :
    (pt gatedTwo q = .p1 ∧ subtreeAt gatedTwo q = gatedTwo) ∨
    (pt gatedTwo q = .p2 ∧ subtreeAt gatedTwo q = p2gadget) := by
  rcases q with _ | ⟨x, q⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · cases x
    · exact q.elim
    · obtain ⟨i, q⟩ := q
      rcases q with _ | ⟨y, q⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · cases y <;> exact q.elim

/-- **`gatedTwo` is strongly fair** (`dp-fairness-reloc`'s definition of record): both
`p2`-subtrees are `p2gadget`. -/
theorem gatedTwo_stronglyFair : StronglyFair gatedTwo := by
  intro d q hq q' hq'
  rw [mem_fiber] at hq hq'
  rcases gatedTwo_subtree q with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases gatedTwo_subtree q' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · rw [h2, h2']; exact LabIso.refl _
  · exact absurd (h1.symm.trans (hq.trans (hq'.symm.trans h1'))) (by decide)
  · exact absurd (h1.symm.trans (hq.trans (hq'.symm.trans h1'))) (by decide)
  · rw [h2, h2']; exact LabIso.refl _

/-- **`(in, x)` is a strict local maximum on `gatedTwo`** (`ε = 1/3`): for `q ≥ 2/3`,
`V(p, q) − 4 = −p(7q − 1)/2 − 7(1 − q)/2 < 0` unless `p = 0` and `q = 1`. -/
theorem gatedTwo_inX_isStrictLocalMax : IsStrictLocalMax inX gatedTwo := by
  refine ⟨1/3, by norm_num, ?_⟩
  intro C' hne hnear
  obtain ⟨p, q, hp0, hp1, hq0, hq1, rfl⟩ :
      ∃ p q hp0 hp1 hq0 hq1, C' = proc2 p q hp0 hp1 hq0 hq1 :=
    ⟨_, _, _, _, _, _, Proc.pt2_eq_proc2 C'⟩
  have hp := hnear .p1 .a
  have hq := hnear .p2 .a
  simp only [proc2_p1, proc2_p2, FinDistr.act2_a, inX, sub_zero] at hp hq
  rw [abs_le] at hp hq
  have hne' : p ≠ 0 ∨ q ≠ 1 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d, _, hd⟩ := hne
    exact hd rfl
  rw [gatedTwo_value, gatedTwo_value]
  have h7q : 0 ≤ 7 * q - 1 := by linarith
  rcases hne' with hp' | hq'
  · have hpos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp')
    nlinarith [mul_pos hpos (show (0:ℚ) < 7 * q - 1 by linarith), mul_nonneg hp0 h7q]
  · have hlt : q < 1 := lt_of_le_of_ne hq1 hq'
    nlinarith [mul_nonneg hp0 h7q]

/-- **The general theorem applied on a two-node fiber**: `(in, x)` is optimal on `gatedTwo`. -/
theorem gatedTwo_inX_isOptimal : IsOptimal inX gatedTwo :=
  stronglyFair_strictLocalMax_isOptimal gatedTwo gatedTwo_stronglyFair inX
    gatedTwo_inX_isStrictLocalMax

/-- The same fact from the closed form (independent check of the theorem's conclusion here):
`4 − V(r, s) = (7/2)(1 − r)(1 − s) + 3r ≥ 0`. -/
theorem gatedTwo_inX_isOptimal' : IsOptimal inX gatedTwo := by
  show IsOptimal (proc2 0 1 _ _ _ _) gatedTwo
  rw [isOptimal_proc2_iff]
  intro r s r0 r1 s0 s1
  rw [gatedTwo_value, gatedTwo_value]
  nlinarith [mul_nonneg (sub_nonneg.mpr r1) (sub_nonneg.mpr s1)]

/-- `V` is not constant on `gatedTwo`: `V(in, x) = 4`, `V(out, y) = 1`. -/
theorem gatedTwo_values : value inX gatedTwo = 4 ∧ value outY gatedTwo = 1 :=
  ⟨by rw [show inX = proc2 0 1 le_rfl zero_le_one zero_le_one le_rfl from rfl, gatedTwo_value];
      norm_num,
   by rw [show outY = proc2 1 0 zero_le_one le_rfl le_rfl zero_le_one from rfl, gatedTwo_value];
      norm_num⟩

/-- The full package, in one statement: strongly fair, `pt` not injective, `(in, x)` a strict
local maximum, optimal, `V` non-constant. -/
theorem gatedTwo_package :
    StronglyFair gatedTwo ∧ ¬ Function.Injective (pt gatedTwo) ∧
    IsStrictLocalMax inX gatedTwo ∧ IsOptimal inX gatedTwo ∧
    value inX gatedTwo = 4 ∧ value outY gatedTwo = 1 :=
  ⟨gatedTwo_stronglyFair, gatedTwo_pt_not_injective, gatedTwo_inX_isStrictLocalMax,
    gatedTwo_inX_isOptimal, gatedTwo_values.1, gatedTwo_values.2⟩

end Cleanroom.Decision.DpLocalOpt.AuditR3
