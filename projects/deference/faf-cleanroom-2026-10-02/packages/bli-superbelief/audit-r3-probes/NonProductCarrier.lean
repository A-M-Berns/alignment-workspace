import Cleanroom.Bli.BliSuperbelief.Witnesses

/-!
# Audit r3 (adversarial) probe — the E1 carrier is not the product grid

The ledger's E1 witness cell says the carrier `coherentGrid extIndex extMesh.d 1 ∅ 2` is
"non-product". The package establishes it indirectly (`faceGen ≠ faceProd` on it, `bli-finite`'s
`faceGen_coherentGrid_not_prod`; `(1,1,0)` incoherent, `ext11_charged_not_coherent`). Here it is
literal: `(1,1,0)` is a table of the 27-point product grid and is **not** on the carrier, so the
carrier is a proper subset of the product grid (and, with `(1,0,0)`, `(0,1,0)` on it, not a product
of coordinate sets). Not imported by the library.
-/

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFinite Cleanroom.Bli.BliSuperbelief

namespace AuditR3

theorem ext11_mem_grid_not_mem_coherentGrid :
    ext11 ∈ grid extIndex extMesh.d 1 ∧ ext11 ∉ coherentGrid extIndex extMesh.d 1 ∅ 2 ∧
    coherentGrid extIndex extMesh.d 1 ∅ 2 ≠ grid extIndex extMesh.d 1 := by
  have h1 : ext11 ∈ grid extIndex extMesh.d 1 := by
    rw [mem_grid_iff]
    intro φ
    unfold ext11
    split_ifs
    · exact zero_mem_gridVals _
    · exact one_mem_gridVals (extMesh.d_pos 1)
  have h2 : ext11 ∉ coherentGrid extIndex extMesh.d 1 ∅ 2 := fun h =>
    ext11_charged_not_coherent.2 2 (coherentOn_of_mem_coherentGrid (extMesh.d_pos 1) h)
  exact ⟨h1, h2, fun h => h2 (h ▸ h1)⟩

end AuditR3
