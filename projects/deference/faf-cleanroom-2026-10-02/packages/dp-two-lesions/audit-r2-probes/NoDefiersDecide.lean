import Cleanroom.Decision.DpTwoLesions.Coupled

/-!
Audit r2 (adversarial) probe. `noDefiers` is graded Kind P in the ledger, but it is a statement
about the finite world type `DlWc` through the definition of `potAct` alone — no tree, no law:
after splitting the state and the forcing bit, `decide` settles each case. It is true for the
reason the IV note gives (forcing is to a fixed act), but that reason is encoded in `potAct`
(the link to the tree is `potAct_eq`, Kind L), so the declaration is plumbing (L), not a proved
claim about the coupled tree. (A single `decide` over all 144 worlds hits the elaborator's
recursion limit; the per-case form below is the same check.) Not imported by the library.
-/

namespace Cleanroom.Decision.DpTwoLesions

example (w : DlWc) : ¬ IsDefier w := by
  rcases w with ⟨s, f, c, m', m, k⟩
  cases f <;> cases s <;> decide +revert

-- the same by unfolding `potAct`, with no decision procedure
example (w : DlWc) : ¬ IsDefier w := by
  rcases w with ⟨s, f, c, m', m, k⟩
  cases f <;> cases s <;> simp [IsDefier, potAct]

end Cleanroom.Decision.DpTwoLesions
