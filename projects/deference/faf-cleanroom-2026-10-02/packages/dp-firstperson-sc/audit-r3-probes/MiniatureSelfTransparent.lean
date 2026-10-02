import Cleanroom.Decision.DpFirstpersonSc.SlItems

/-!
Audit r3 (adversarial) probe for T17(a): the C-headline `cedt_selfTransparent_of_recordsFor`
takes `RecordsFor` (Definition 7) at every queried point. The package's only T17(a) tree is the
miniature, and `dp-calibration` proves `miniature_not_recordsFor : ¬ RecordsFor miniObs miniActEv
C miniature ()` for every `C` (self-succession: `#_d = 2` on every path). So the hypothesis
package of that headline is **refuted on the package's instance tree** and inhabited nowhere in
the package — the row's witness `miniature_cedt_iff` is a witness for `CEDT`, not for the
recording lemma. The mandate's rule of record is "CEDT *at self-transparent points*"; on the
miniature self-transparency holds anyway, by the `#_d = 2` symmetry (both draws are `C()`), and is
literally `dp-calibration`'s `miniState_pr_live`. This probe states it, derives
`CEDTSelfTransparent ↔ q = 2/3` from `miniature_cedt_iff`, and records the refutation of the
recording package on the miniature. Not imported by the library.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt

/-- The miniature's point is self-transparent for every label `q` — Appendix B item 2 by the
`#_d = 2` symmetry, not by Definition 7. -/
theorem probe_miniature_selfTransparent (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    SelfTransparent (fun _ => miniState q h0 h1) miniActEv (procQ q h0 h1) () :=
  fun act => miniState_pr_live q h0 h1 act

/-- **`CEDT(R2-real) = {2/3}` at self-transparent points** — the mandate's rule of record on the
miniature, with the self-transparency clause discharged. -/
theorem probe_miniature_cedtSelfTransparent_iff (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    CEDTSelfTransparent (fun _ => miniState q h0 h1) miniObs (miniForceCf q h0 h1) miniActEv
      (procQ q h0 h1) miniature ↔ q = 2 / 3 := by
  constructor
  · rintro ⟨h, -⟩
    exact (miniature_cedt_iff q h0 h1).mp h
  · intro hq
    refine ⟨(miniature_cedt_iff q h0 h1).mpr hq, fun d _ => ?_⟩
    cases d
    exact probe_miniature_selfTransparent q h0 h1

/-- The hypothesis package of `cedt_selfTransparent_of_recordsFor` is false on the miniature
for every label: the miniature does not record (`dp-calibration`'s `miniature_not_recordsFor`). -/
theorem probe_recordsFor_package_refuted_on_miniature (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ¬ (∀ d ∈ queried miniature,
        RecordsFor miniObs miniActEv (procQ q h0 h1) miniature d ∧
          0 < nu (procQ q h0 h1) miniature (miniObs d)) :=
  fun h => miniature_not_recordsFor (procQ q h0 h1) (h () miniature_queried).1

end Cleanroom.Decision.DpFirstpersonSc
