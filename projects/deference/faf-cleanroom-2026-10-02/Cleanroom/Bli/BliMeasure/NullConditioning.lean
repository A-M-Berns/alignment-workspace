import Cleanroom.Bli.BliMeasure.Dogmatism
import Cleanroom.Bli.BliMeasure.Coherence

/-!
# `bli-measure` · NullConditioning: the null-conditioning N− for `b3_TB` (target 4)

The mandate's target 4 asks for an N− in which "the realized state leaves the face (`TB` then
holds with both sides `0`, the null-conditioning case of `bli-trajectory` F-3)". Rounds 0–1
described it and did not build it (`support_lost_of_coarse` shows support loss by rounding
only); audit r2 (adversarial, N2) built it as a probe, and this module carries that probe into
the package. It is the **adversarial degeneracy check of the flagship**: `b3_TB` has no
hypothesis, so this base inhabits it, and there it says `0 = 0` — which is why the N+ witness on
the real construction (`paper_TB_witness`, `Witness.lean`: both factors strictly inside `(0, 1)`,
every day `n ≥ 2`) carries the headline's non-degeneracy, not the theorem.

The base: over the empty process, with `B m := sup atomBound (smallSet m)`, the day-`n` measure
is the point mass at the all-`false` world up to day `kDay := tokenSize (atom 0)` (so that the
day-`kDay` bound is positive and the two worlds differ) and at the all-`true` world after. On
the denominator mesh the realized day-`(kDay+1)` state is the point table at all-`true`, which is
not in the face of the rounded day-`kDay` table (the point mass at all-`false`): the face is a
support condition on the grid of record (`mem_faceGen_cgrid_iff`), and all-`true` is off the
support.

* `emptyDP`, `supBounds`, `dogBase` — the base; every `CoherentBase` field discharged.
* `dog_null_conditioning` — `𝐏_kDay(⌜𝑸_{kDay+1} = actual (kDay+1)⌝) = 0` on the denominator mesh.
* `dog_TB_degenerate` — both sides of `TB` at day `kDay` are `0`, for every `ψ` (the N− row).

Over the recursion of record this cannot happen on the denominator mesh (`paper_realized_charged`):
the base there has full support on the stage's consistent worlds (`recBase_fullSupport`), which is
exactly the hypothesis `realized_charged` needs and `dogBase` lacks.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

/-- The empty deductive process.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def emptyDP : DeductiveProcess := ⟨fun _ => ∅, fun _ => Finset.Subset.refl _⟩

/-- Atom bounds: the largest atom bound of a day-`m` small sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def supBounds : AtomBounds where
  B m := (smallSet m).sup atomBound
  B_mono m := Finset.sup_mono (smallSet_mono (Nat.le_succ m))
  B_cover _ _ hφ := Finset.le_sup hφ
  B_unbounded a := ⟨tokenSize (Formula.atom a),
    lt_of_lt_of_le (Nat.lt_succ_self a)
      (show atomBound (Formula.atom a) ≤ _ from
        Finset.le_sup (mem_smallSet.mpr (smallOn_tokenSize (Formula.atom a))))⟩

/-- The all-`false` finite world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def allFalseFW (B : ℕ) : FiniteWorld B := fun _ => false

/-- The all-`true` finite world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def allTrueFW (B : ℕ) : FiniteWorld B := fun _ => true

/-- The day on which the point mass switches (chosen so that the day-`kDay` bound is `> 0`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev kDay : ℕ := tokenSize (Formula.atom 0)

/-- The charged world of day `n`: all-`false` up to day `kDay`, all-`true` after.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def dogPoint (n : ℕ) : FiniteWorld (supBounds.B n) :=
  if n ≤ kDay then allFalseFW _ else allTrueFW _

/-- The dogmatic measures: the point mass at `dogPoint n`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def dogW (n : ℕ) : FiniteWorld (supBounds.B n) → ℚ :=
  fun u => if u = dogPoint n then 1 else 0

/-- **The dogmatic base over the empty process**, whose day-`(kDay+1)` measure leaves the
day-`kDay` support. A `CoherentBase` with every field discharged (the empty stage makes `w_supp`
and `B_stage` vacuous; `Q` is the marginal by definition).
Source: [[bli-measure-mandate]] target 4 (N−); audit r2 adversarial N2
Kind: D
Fidelity: exact (a concrete abstract base; (c) standing alone as every `CoherentBase` not over the recursion) -/
noncomputable def dogBase : CoherentBase emptyDP where
  𝔅 := supBounds
  Q n φ := wMarginal (dogW n) φ
  w := dogW
  w_nonneg n u := by unfold dogW; split_ifs <;> norm_num
  w_sum n := by
    unfold dogW
    rw [Finset.sum_eq_single (dogPoint n)]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  w_supp _ _ _ φ hφ := absurd hφ (Finset.notMem_empty φ)
  Q_eq _ _ _ := rfl
  B_stage _ φ hφ := absurd hφ (Finset.notMem_empty φ)

/-- The day-`kDay` bound is positive (`atom 0` is small on day `kDay`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kDay_bound_pos : 0 < dogBase.𝔅.B kDay := by
  show 0 < (smallSet kDay).sup atomBound
  exact lt_of_lt_of_le (Nat.lt_succ_self 0)
    (show atomBound (Formula.atom 0) ≤ _ from
      Finset.le_sup (mem_smallSet.mpr (smallOn_tokenSize (Formula.atom 0))))

/-- On the day-`kDay` bound, all-`true` differs from all-`false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma allTrueFW_ne_allFalseFW : allTrueFW (dogBase.𝔅.B kDay) ≠ allFalseFW (dogBase.𝔅.B kDay) := by
  intro h
  have := congrFun h ⟨0, kDay_bound_pos⟩
  exact Bool.false_ne_true this.symm

/-- **Null conditioning: `𝐏_kDay(⌜𝑸_{kDay+1} = actual (kDay+1)⌝) = 0`.** The realized next state
(the point mass at all-`true`) is not in the face of the rounded day-`kDay` table (the point mass
at all-`false`): on the grid of record the face is a support condition (`mem_faceGen_cgrid_iff`),
and all-`true` is off the day-`kDay` support.
Source: [[bli-measure-mandate]] target 4 (N−: "the realized state leaves the face"); audit r2 adversarial N2
Kind: N-
Fidelity: exact (on the denominator mesh of `dogBase`)
Hyps: (a) none -/
theorem dog_null_conditioning :
    b3History dogBase (denomMesh dogBase) kDay
      (stateAtom (kDay + 1) (b3Actual dogBase (denomMesh dogBase) (kDay + 1))) = 0 := by
  have hnot : ¬ (0 < superbelief (b3History dogBase (denomMesh dogBase)) kDay
      (b3Actual dogBase (denomMesh dogBase) (kDay + 1))) := by
    rw [b3_FS dogBase (denomMesh dogBase) kDay (b3Actual_mem dogBase (denomMesh dogBase) (kDay + 1)),
      wdecode_b3Actual, mem_faceGen_cgrid_iff dogBase (denomMesh dogBase)
        (roundedTable_mem_cgrid dogBase (denomMesh dogBase) kDay)]
    rintro ⟨-, hsupp⟩
    have h0 : vecOf (roundedTable dogBase (denomMesh dogBase) kDay) (allTrueFW (dogBase.𝔅.B kDay)) = 0 := by
      rw [vecOf_roundedTable, measureRound_denomMesh]
      show dogW kDay (allTrueFW _) = 0
      unfold dogW dogPoint
      rw [if_pos le_rfl]
      split_ifs with h
      · exact absurd h allTrueFW_ne_allFalseFW
      · rfl
    have h := hsupp (allTrueFW (dogBase.𝔅.B kDay)) h0
    rw [cgrid_apply_wcAt (𝔅 := dogBase.𝔅) (𝓜 := denomMesh dogBase)
      (roundedTable_mem_cgrid dogBase (denomMesh dogBase) (kDay + 1)) (Nat.le_succ kDay),
      vecOf_roundedTable, measureRound_denomMesh] at h
    have hmem : allTrueFW (dogBase.𝔅.B (kDay + 1)) ∈ univ.filter
        (fun u' : FiniteWorld (dogBase.𝔅.B (kDay + 1)) =>
          restrFW (dogBase.𝔅.B_le (Nat.le_succ kDay)) u' = allTrueFW (dogBase.𝔅.B kDay)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hle := Finset.single_le_sum (f := dogBase.w (kDay + 1))
      (fun u _ => dogBase.w_nonneg (kDay + 1) u) hmem
    have hone : dogBase.w (kDay + 1) (allTrueFW (dogBase.𝔅.B (kDay + 1))) = 1 := by
      show dogW (kDay + 1) (allTrueFW _) = 1
      unfold dogW dogPoint
      rw [if_neg (Nat.not_succ_le_self kDay), if_pos rfl]
    have hcontra := hle.trans_eq h
    rw [hone] at hcontra
    norm_num at hcontra
  exact le_antisymm (not_lt.mp hnot) (b3History_range _ _ _ _).1

/-- **The N− for `b3_TB`: at day `kDay` on `dogBase` both sides of `TB` are `0`, for every `ψ`.**
`b3_TB` has no hypothesis and this base inhabits it; the identity reads `0 = 0` there, so the
non-degeneracy of the flagship lives in `paper_TB_witness`, not in the theorem.
Source: [[bli-measure-mandate]] target 4 (N−: "`TB` then holds with both sides `0`"); `bli-trajectory` F-3; audit r2 adversarial N2
Kind: N-
Fidelity: exact
Hyps: (a) none -/
theorem dog_TB_degenerate (ψ : Sentence) :
    b3History dogBase (denomMesh dogBase) (kDay + 1) ψ *
        b3History dogBase (denomMesh dogBase) kDay
          (stateAtom (kDay + 1) (b3Actual dogBase (denomMesh dogBase) (kDay + 1))) = 0 ∧
    b3History dogBase (denomMesh dogBase) kDay
        (ψ ⋏ stateAtom (kDay + 1) (b3Actual dogBase (denomMesh dogBase) (kDay + 1))) = 0 := by
  refine ⟨by rw [dog_null_conditioning, mul_zero], ?_⟩
  apply le_antisymm _ (b3History_range _ _ _ _).1
  calc b3History dogBase (denomMesh dogBase) kDay
        (ψ ⋏ stateAtom (kDay + 1) (b3Actual dogBase (denomMesh dogBase) (kDay + 1)))
      ≤ b3History dogBase (denomMesh dogBase) kDay
          (stateAtom (kDay + 1) (b3Actual dogBase (denomMesh dogBase) (kDay + 1))) :=
        b3History_mono dogBase (denomMesh dogBase) kDay
          (fun v h => ((PCWorld.holds_and v _ _).mp h).2)
    _ = 0 := dog_null_conditioning

end Cleanroom.Bli.BliMeasure
