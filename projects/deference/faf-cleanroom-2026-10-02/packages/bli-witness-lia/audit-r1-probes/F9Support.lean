import Cleanroom.Bli.BliWitnessLia

/-!
# Audit round 1 (adversarial) — probe: the two premises of findings F9, machine-checked

F9 ([[bli-witness-lia-findings]]) argues — by analysis, not in Lean — that under `H_unif` the
one-level precommitment test is inert on `segmentSist`: every positive-mass policy has
`NoStrictPrecommit`. The argument rests on two structural facts about the prior that this probe
checks in Lean (the `exAnteValue` invariance that completes the argument is not checked here):

* **(ii) The Ask class on the day-`(n+1)` grid is not a singleton.** There is a grid table with
  the coin at `1` other than `sliceT n` (here: `sliceT n` with its `⊤`-coordinate flipped), so a
  one-point update of a class-constant policy at an Ask table leaves the image of `unifMk` and has
  `unifLaw`-mass `0`.
* **(iii) The utility only ever reads the policy at an Ask-class table.** `skelRef ω` is in the
  Ask class for every base world `ω` (the state itself when it is Ask; the observed table
  `askTable` otherwise).

Both are what F9 says they are. The full statement F9 proposes
(`∀ π, 0 < policyMass π → NoStrictPrecommit (segmentSist …) π`) is not proved here.
-/

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Skel
open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
open Cleanroom.Bli.BliWitnessLia

namespace AuditR1F9

noncomputable section

/-- (iii) `skelRef` is always an Ask-class table on `segmentSist`. -/
theorem skelRef_askC {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H)
    (h2 : 2 ≤ n) (ω : SkelBase (𝒮 := smallIndex) (d := (Bli.segmentMesh K).d) n 0) :
    askC n 0 (coinAt n (Nat.le_of_succ_le h2))
      (skelRef n 0 (coinAt n (Nat.le_of_succ_le h2)) (askTable K hK hn) ω) := by
  unfold skelRef
  split_ifs with h1 h3
  · exact h1
  · exact askC_askTable hK hn h2
  · exact askC_askTable hK hn h2

/-- `⊤` as a day-`(n+1)` small sentence. -/
def topAt (n : ℕ) : ↥(smallIndex.S (n + 0 + 1)) :=
  ⟨⊤, show (⊤ : Sentence) ∈ smallIndex.S (n + 0 + 1) from top_mem_smallSet (Nat.le_add_left 1 (n + 0))⟩

/-- (ii) A second Ask-class table: `sliceT n` with its `⊤`-coordinate flipped to a different grid
value. -/
def askTable' (n : ℕ) : Table smallIndex (n + 0 + 1) :=
  Function.update (sliceT n) (topAt n) (if sliceT n (topAt n) = 0 then 1 else 0)

theorem askTable'_mem_grid {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) :
    askTable' n ∈ grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1) := by
  rw [mem_grid_iff]
  intro φ
  unfold askTable'
  by_cases hφ : φ = topAt n
  · subst hφ
    rw [Function.update_self]
    split_ifs
    · exact one_mem_gridVals ((Bli.segmentMesh K).d_pos _)
    · exact zero_mem_gridVals _
  · rw [Function.update_of_ne hφ]
    exact mem_grid_iff.mp
      (sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 1 0 1 True) φ

theorem askTable'_ne_sliceT (n : ℕ) : askTable' n ≠ sliceT n := by
  intro h
  have := congrFun h (topAt n)
  unfold askTable' at this
  rw [Function.update_self] at this
  split_ifs at this with h0
  · rw [h0] at this; norm_num at this
  · exact h0 this.symm

/-- The coin is not `⊤` (an atom versus a compound). -/
theorem coin_ne_top {n : ℕ} (h1 : 1 ≤ n) : coinAt n h1 ≠ topAt n := by
  intro h
  have h' : freshCoord = (⊤ : Sentence) := congrArg Subtype.val h
  rw [show freshCoord = Formula.atom (freshAtomCode freshFamily (Nat.pair 0 0)) from rfl] at h'
  cases h'

theorem askC_askTable' {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H)
    (h2 : 2 ≤ n) :
    askC n 0 (coinAt n (Nat.le_of_succ_le h2))
      (⟨askTable' n, askTable'_mem_grid hK hn⟩ :
        ↥(grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1))) := by
  show askTable' n (coinAt n (Nat.le_of_succ_le h2)) = 1
  unfold askTable'
  rw [Function.update_of_ne (coin_ne_top (Nat.le_of_succ_le h2))]
  exact (sliceTable_fresh n 1 0 1 True _).trans (by simp)

/-- (ii), bundled: two distinct Ask-class grid tables on day `n+1`. -/
theorem two_ask_tables {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H)
    (h2 : 2 ≤ n) :
    ∃ T₁ T₂ : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1)),
      T₁ ≠ T₂ ∧ askC n 0 (coinAt n (Nat.le_of_succ_le h2)) T₁ ∧
        askC n 0 (coinAt n (Nat.le_of_succ_le h2)) T₂ :=
  ⟨askTable K hK hn, ⟨askTable' n, askTable'_mem_grid hK hn⟩,
    fun h => askTable'_ne_sliceT n (congrArg Subtype.val h).symm,
    askC_askTable hK hn h2, askC_askTable' hK hn h2⟩

end

end AuditR1F9
