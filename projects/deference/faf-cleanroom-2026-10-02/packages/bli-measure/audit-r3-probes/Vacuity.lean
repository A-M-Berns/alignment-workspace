import Cleanroom.Bli.BliMeasure.Ui

/-!
# Audit r3 (adversarial) probe — two vacuity checks

* `uiAt_empty`: the one inhabitant of `b3_UIAt`'s hypothesis package that needs no process
  (`C := ∅`) makes its conclusion vacuous; the meaningful inhabitant (a nonempty `C` whose
  implications lie in the stage) is the N+ the ledger records as not done.
* `val_non_candidate`: `b3StateSystem.val m q φ` is the junk `0` for a non-candidate code `q`
  (the `wdecode` default), as `Measure.lean` discloses; no headline sums over non-candidates.

Not imported by the library.
-/

namespace Cleanroom.Bli.BliMeasure.AuditR3

open LogicalInduction LO.Propositional Finset Cleanroom.Bli.BliFinite Cleanroom.Bli.BliFound
  Cleanroom.Bli.BliRvcUi Cleanroom.Bli.BliMeasure

/-- `UIAt` on no instances holds for every valuation and family. -/
theorem uiAt_empty (V : Sentence → ℝ) (F : UIFamily) : UIAt V F ∅ :=
  fun c hc => absurd hc (Finset.notMem_empty c)

/-- `val` on a non-candidate code is `0`. -/
theorem val_non_candidate {DP : DeductiveProcess} (base : CoherentBase DP) (𝓜 : Mesh) (m q : ℕ)
    (hq : q ∉ wstates base.𝔅 𝓜 m) (φ : Sentence) : (b3StateSystem base 𝓜).val m q φ = 0 := by
  rw [b3StateSystem_val]
  have hdec : wdecode base.𝔅 𝓜 m q = fun _ => 0 := by
    unfold wdecode
    rw [dif_neg]
    rintro ⟨Q, hQ, hcode⟩
    exact hq ((mem_wstates_iff base.𝔅 𝓜).mpr ⟨Q, hQ, hcode⟩)
  rw [hdec]
  unfold vecOf wMarginal
  simp

end Cleanroom.Bli.BliMeasure.AuditR3
