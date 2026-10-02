import Cleanroom.Decision.DpCartesianFrames.Witnesses
import Cleanroom.Found.DpCoreTree.Agreement

/-!
# ZO-15: recording ⟹ column-determined at `Loc d`

Package `dp-cartesian-frames`, file 14 (repair round 1; mandate T11(d)). Lazy seeding.

* `runLeaf_eq_or_below_both`: the run-comparison lemma with **both** leaves below the same
  `d`-node (the first `d`-node the common prefix meets).
* `subtreeVeridical_of_pruned_recordsForAll`: on a pruned tree recording at `d` for every
  procedure, every `d`-node with an `O_d`-leaf below it is subtree-veridical — ZO-15's
  argument: that leaf has positive mass under the uniform procedure, so Definition 7's clause
  (2) applies to the node.
* **ZO-15** `columnDetermined_loc_of_pruned_recordsForAll`: hence `S_{O_d}` is column-determined
  at `Loc d B` — the first `d`-node a column reaches decides membership independently of the
  `d`-answer.
* The mandate's parenthetical "(and at `Fr B`)" is **false**: `lookRecTree` (look-decide with the
  action recorded in the world) is pruned and records at `d` for every procedure, yet `S_{O_d}`
  is not column-determined in `Fr` — membership depends on the *other* point's answer
  (`lookRecTree_records_not_columnDetermined_fr`). ZO-15's sentence is about the `d`-answer only.
* The converse of ZO-15 is false (the source's CX2): `inertTree` has `S_{O_d}` column-determined
  at `Loc d` and records at `d` for no action events (`inertTree_columnDetermined_not_records`).
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

section general

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- **The run-comparison lemma, both leaves.** If `π₀` and `π₁` agree off `d`, then under any
profile either their runs coincide or both leaves lie below one and the same `d`-node (the
first one the common walk meets).
Source: cf-correspondence CF-10 proof (line 43); zoo ZO-15 (line 120: "the first `d`-node a
column reaches")
Kind: P
Fidelity: exact
Hyps: none -/
theorem runLeaf_eq_or_below_both (d : ι) (π₀ π₁ : (e : ι) → acts e)
    (h : ∀ e, e ≠ d → π₀ e = π₁ e) :
    (B : Tree Ω ι acts K) → ∀ ε : ChanceProfile B,
      runLeaf π₀ B ε = runLeaf π₁ B ε ∨
        ∃ q : B.DecNode, pt B q = d ∧ runLeaf π₀ B ε ∈ leavesBelow B q ∧
          runLeaf π₁ B ε ∈ leavesBelow B q
  | .leaf _ _, _ => Or.inl rfl
  | .chance n β child, ε => by
      rcases runLeaf_eq_or_below_both d π₀ π₁ h (child ε.1) (ε.2 ε.1) with heq | ⟨q, hq, h₀, h₁⟩
      · exact Or.inl (congrArg (Sigma.mk ε.1) heq)
      · refine Or.inr ⟨⟨ε.1, q⟩, hq, ?_, ?_⟩
        · rw [mem_leavesBelow] at h₀ ⊢
          show (edgeOf (Tree.chance n β child) ⟨ε.1, q⟩
            ⟨ε.1, runLeaf π₀ (child ε.1) (ε.2 ε.1)⟩).isSome
          rw [edgeOf_chance, dif_pos rfl]
          exact h₀
        · rw [mem_leavesBelow] at h₁ ⊢
          show (edgeOf (Tree.chance n β child) ⟨ε.1, q⟩
            ⟨ε.1, runLeaf π₁ (child ε.1) (ε.2 ε.1)⟩).isSome
          rw [edgeOf_chance, dif_pos rfl]
          exact h₁
  | .decision d' child, ε => by
      by_cases hd : d' = d
      · subst hd
        refine Or.inr ⟨none, rfl, ?_, ?_⟩
        · rw [mem_leavesBelow]; rfl
        · rw [mem_leavesBelow]; rfl
      · have hπ : π₀ d' = π₁ d' := h d' hd
        rcases runLeaf_eq_or_below_both d π₀ π₁ h (child (π₀ d')) (ε (π₀ d'))
          with heq | ⟨q, hq, h₀, h₁⟩
        · left
          simp only [runLeaf_decision]
          rw [← hπ]
          exact congrArg (Sigma.mk (π₀ d')) heq
        · refine Or.inr ⟨some ⟨π₀ d', q⟩, hq, ?_, ?_⟩
          · rw [mem_leavesBelow] at h₀ ⊢
            show (edgeOf (Tree.decision d' child) (some ⟨π₀ d', q⟩)
              ⟨π₀ d', runLeaf π₀ (child (π₀ d')) (ε (π₀ d'))⟩).isSome
            rw [edgeOf_decision_some, dif_pos rfl]
            exact h₀
          · rw [mem_leavesBelow] at h₁ ⊢
            have e1 : runLeaf π₁ (Tree.decision d' child) ε =
                ⟨π₀ d', runLeaf π₁ (child (π₀ d')) (ε (π₀ d'))⟩ := by
              simp only [runLeaf_decision]
              rw [← hπ]
            rw [e1]
            show (edgeOf (Tree.decision d' child) (some ⟨π₀ d', q⟩)
              ⟨π₀ d', runLeaf π₁ (child (π₀ d')) (ε (π₀ d'))⟩).isSome
            rw [edgeOf_decision_some, dif_pos rfl]
            exact h₁

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-- **ZO-15's key step**: on a pruned tree that records at `d` for every procedure, a `d`-node
with an `O_d`-leaf below it is subtree-veridical — that leaf has positive mass under the
uniform procedure, so Definition 7's clause (2) names the node.
Source: zoo ZO-15 (line 120: "every `d`-node with an `O_d`-leaf below it is the unique
`d`-node of an `O_d`-run under a full-support procedure, hence subtree-veridical")
Kind: P
Fidelity: exact
Hyps: none (`Pruned`, `RecordsForAll` are `dp-fairness-reloc`'s / `dp-core-tree`'s definitions
of record) -/
theorem subtreeVeridical_of_pruned_recordsForAll [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    {d : ι} (hP : Pruned B) (hrec : RecordsForAll obs actEv B d) (q : B.DecNode)
    (hq : pt B q = d) (ℓ : B.Leaves) (hℓ : ℓ ∈ leavesBelow B q) (hw : world B ℓ ∈ obs d) :
    SubtreeVeridical obs B q := by
  have hpos : 0 < leafLaw (Proc.uniform : Proc ι acts K) B ℓ :=
    (leafLaw_pos_iff_of_fullSupport Proc.uniform_fullSupport B ℓ).mpr (hP ℓ)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ((mem_leavesBelow B q ℓ).mp hℓ)
  exact ((hrec Proc.uniform ℓ hpos hw).2 q hq a ha).1

/-- **ZO-15** (lazy, at `Loc d`): on a pruned tree recording at `d` for every procedure,
`S_{O_d}` is column-determined at `Loc d B` — the two runs of a column under two `d`-answers
either coincide or both pass the first `d`-node of their common walk, which is subtree-veridical
as soon as one of them lands in `O_d`.
Source: zoo ZO-15 (line 119–120: "FRec ⟹ column-determined at every point (zero-probability
chance edges pruned)"); mandate T11(d)
Kind: P
Fidelity: exact (at `Loc d`, varying the `d`-answer — ZO-15's sentence; the mandate's "and at
`Fr B`" is refuted below. The proof uses recording for `Proc.uniform` only, so any one
full-support procedure would do: `RecordsForAll` is ZO-15's hypothesis as stated, more than the
proof needs)
Hyps: none -/
theorem columnDetermined_loc_of_pruned_recordsForAll [∀ d, Nonempty (acts d)]
    {B : Tree Ω ι acts K} {d : ι} (hP : Pruned B) (hrec : RecordsForAll obs actEv B d) :
    ColumnDetermined (Loc d B) (SO obs d) := by
  rintro ⟨p, ε⟩ a₀ a₁
  rcases runLeaf_eq_or_below_both d (extend d a₀ p) (extend d a₁ p)
      (fun e he => by rw [extend_ne d a₀ p he, extend_ne d a₁ p he]) B ε with heq | ⟨q, hq, h₀, h₁⟩
  · show readout B (runLeaf _ B ε) ∈ SO obs d ↔ readout B (runLeaf _ B ε) ∈ SO obs d
    rw [heq]
  · constructor
    · intro hin
      have hV := subtreeVeridical_of_pruned_recordsForAll obs actEv hP hrec q hq _ h₀ hin
      have := hV _ h₁
      rw [hq] at this
      exact this
    · intro hin
      have hV := subtreeVeridical_of_pruned_recordsForAll obs actEv hP hrec q hq _ h₁ hin
      have := hV _ h₀
      rw [hq] at this
      exact this

end general

/-! ### The global-frame variant is false -/

/-- Look-decide with the `d`-action recorded in the world: root point `true` (look = `a`,
leave = `b`); look → a node of point `false` whose leaves record `(opened, action)`; leave →
`(closed, b)`.
Source: cf-correspondence CF-13 (line 59), with the action recorded so that Definition 7's
action-veridicality clause can hold
Kind: D -/
def lookRecTree : Tree (Bool × Act2) Bool (fun _ => Act2) ℚ :=
  .decision true fun
    | .a => .decision false fun x => .leaf (true, x) (if x = .a then 1 else 0)
    | .b => .leaf (false, .b) 0

/-- `O_{d'} = ⊤`, `O_d = {opened}`.
Source: cf-correspondence CF-13 (line 59)
Kind: D -/
def lookRecObs : Bool → Finset (Bool × Act2) :=
  fun p => if p then Finset.univ else Finset.univ.filter fun w => w.1 = true

/-- Action events `{act = ·}` (read off the world's second coordinate).
Source: none: infrastructure
Kind: D -/
def lookRecActEv (_ : Bool) (x : Act2) : Finset (Bool × Act2) := Finset.univ.filter fun w => w.2 = x

/-- `lookRecTree` is pruned (chance-free: every path has chance weight `1`).
Source: none: infrastructure
Kind: L -/
theorem lookRecTree_pruned : Pruned lookRecTree := by
  rintro ⟨x, ℓ⟩
  cases x
  · obtain ⟨y, ⟨⟩⟩ := ℓ
    show (0 : ℚ) < 1
    norm_num
  · obtain ⟨⟩ := ℓ
    show (0 : ℚ) < 1
    norm_num

/-- `lookRecTree` records at `d = false` for every procedure.
Source: `dp-core-tree`'s `RecordsForAll` (definition of record)
Kind: L -/
theorem lookRecTree_recordsForAll : RecordsForAll lookRecObs lookRecActEv lookRecTree false := by
  intro C ℓ hpos hw
  clear hpos
  revert hw
  revert ℓ
  unfold SubtreeVeridical
  decide

/-- **The mandate's "(and at `Fr B`)" is false**: `lookRecTree` is pruned and records at `d` for
every procedure, yet `S_{O_d}` is not column-determined in the global frame — the look row lands
in `O_d`, the leave row outside, on the one column. ZO-15 concerns the `d`-answer only
(`columnDetermined_loc_of_pruned_recordsForAll`).
Source: mandate T11(d) ("`ColumnDetermined (Loc d B) (S_O d)` (and at `Fr B`)"); zoo ZO-15
(line 120)
Kind: N+
Fidelity: exact -/
theorem lookRecTree_records_not_columnDetermined_fr :
    Pruned lookRecTree ∧ RecordsForAll lookRecObs lookRecActEv lookRecTree false ∧
    ¬ ColumnDetermined (Fr lookRecTree) (SO lookRecObs false) := by
  refine ⟨lookRecTree_pruned, lookRecTree_recordsForAll, fun h => ?_⟩
  have := h (chanceProfileNonempty lookRecTree).some (fun _ => Act2.a) (fun _ => Act2.b)
  have h1 : (Fr lookRecTree).outcome (fun _ => Act2.a) (chanceProfileNonempty lookRecTree).some ∈
      SO lookRecObs false := by
    show (true, Act2.a) ∈ lookRecObs false
    decide
  have h2 := this.mp h1
  exact absurd (show (false, Act2.b) ∈ lookRecObs false from h2) (by decide)

/-! ### The converse of ZO-15 is false -/

/-- **The converse of ZO-15 fails** (the source's CX2, here on the inert simulation):
`S_{O_d}` is column-determined at `Loc d inertTree` (even powerless outside it), yet the tree
records at `d` for *no* choice of action events — the two tails leaves share the world `true`,
so no action event can separate the actions drawn there.
Source: zoo ZO-15 (line 120: "Converse false (CX2: column-determined, not FRec)")
Kind: N+
Fidelity: variant: the source's CX2 is replaced by `inertTree` (N− acceptable per the mandate;
this witness is non-degenerate: both cells of `S_{O_d}` are realized at `Loc d`) -/
theorem inertTree_columnDetermined_not_records :
    ColumnDetermined (Loc () inertTree) (SO trueObs ()) ∧
    ∀ actEv : (d : Unit) → Act2 → Finset Bool, ¬ RecordsForAll trueObs actEv inertTree () := by
  refine ⟨inert_powerless_not_veridical.1.columnDetermined, fun actEv hrec => ?_⟩
  have hpos : ∀ ℓ : inertTree.Leaves, 0 < leafLaw (Proc.uniform : Proc Unit (fun _ => Act2) ℚ)
      inertTree ℓ := fun ℓ =>
    (leafLaw_pos_iff_of_fullSupport Proc.uniform_fullSupport inertTree ℓ).mpr (by
      rcases ℓ with ⟨i, ⟨x, ⟨⟩⟩⟩
      fin_cases i <;> show (0 : ℚ) < FinDistr.fair.w _ * 1 <;>
        norm_num [FinDistr.fair, FinDistr.coin])
  have ha := hrec Proc.uniform ⟨0, ⟨Act2.a, ()⟩⟩ (hpos _)
    (by show (true : Bool) ∈ trueObs (); decide)
  have hb := hrec Proc.uniform ⟨0, ⟨Act2.b, ()⟩⟩ (hpos _)
    (by show (true : Bool) ∈ trueObs (); decide)
  have hqa := ha.2 ⟨0, none⟩ rfl Act2.a (by decide)
  have hqb := hb.2 ⟨0, none⟩ rfl Act2.b (by decide)
  have h1 : (true : Bool) ∈ actEv () Act2.b := hqb.2.1
  have h2 := hqa.2.2 Act2.b h1
  exact absurd h2 (by decide)

end Cleanroom.Decision.DpCartesianFrames
