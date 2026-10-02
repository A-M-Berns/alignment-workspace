import Cleanroom.Decision.DpCartesianFrames.DiagWitnesses
import Cleanroom.Decision.DpCartesianFrames.RelocWitnesses

/-!
# Audit r4 (fidelity) probe: the shape of `zmTree`, and a non-trivial instance of T7(c)

Two checks on repair round 3's T7(c) material. Not imported by the library.

1. **`zmTree` is a reduction of the source's 2-fold linear mugging, not "the source's tree".**
   The toolkit's `k_fold_mugging(2, "linear")` (`phase2-notes/toolkit/examples.py`) has a real
   `d`-query on tails and transfer coins under *both* inconsistent sim paths (pay, refuse) and
   (refuse, pay): three chance nodes, so `Fr(B)` is `2 × 8` (zoo line 72). The package's
   `zmTree β` has a leaf on tails and one transfer coin under `d:a, d:b` only: two chance nodes,
   so `Fr (zmTree β)` has **4** columns. `zmTree_card_columns` pins this. The witness still
   exhibits ZO-5(b)'s mechanism (a coin under an inconsistently answered nested path is lost),
   so `notInjective_diagStruct_zm` is N+; but the Fidelity cells saying "exact (the source's
   tree)" are wrong — it is a variant.

2. **T7(c)'s headline has a non-trivial instance.** `frLit_iso_fr_of_not_nestedFiber`'s
   hypothesis is trivially satisfiable (`U = ∅`); the ledger names no instance with `U ≠ ∅`.
   The catalogue's mugging with `U = {d}` is one: its `d`-fiber has two nodes on different
   branches, none nested (`mug1_not_nestedFiber`), the coin is copied into both `σ`-branches,
   and the literal identified frame of the relocation output is isomorphic in `Chu(W)` to
   `Fr (mug1 x y)` (`frLit_iso_fr_mug1`, every `x`, `y`) — the `2 × 2 = 2 × 2` matrix equality
   that CFF-15's relocated mugging is about.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

/-- `Fr (zmTree fair)` has four columns (root coin × one transfer coin), not the source's
eight: the package's tree is the source's with the (refuse, pay) transfer coin and the real
tails query removed. -/
theorem zmTree_card_columns : Fintype.card (ChanceProfile (zmTree FinDistr.fair)) = 4 := by
  decide

/-- The mugging's `d`-fiber is not nested: both `d`-nodes are immediate children of the root
coin, so each is minimal. -/
theorem mug1_not_nestedFiber (x y : ℚ) : ∀ d ∈ U1, ¬ NestedFiber (mug1 x y) d := by
  rintro ⟨⟩ - ⟨⟨i, q⟩, -, hmin⟩
  rcases q with _ | ⟨a, q⟩
  · exact hmin (by show () ∉ ([] : List Unit); simp)
  · exact q.elim

/-- A non-trivial instance of T7(c)'s core half: for the catalogue's mugging with `U = {d}`
(a two-node fiber, the coin copied into both `σ`-branches), the literal identified frame of
the relocation output is isomorphic in `Chu(W)` to `Fr (mug1 x y)`, for every `x`, `y`. -/
theorem frLit_iso_fr_mug1 (x y : ℚ) : Nonempty (FrLit U1 (mug1 x y) ≅ Fr (mug1 x y)) :=
  frLit_iso_fr_of_not_nestedFiber U1 (mug1 x y) (mug1_not_nestedFiber x y)

end Cleanroom.Decision.DpCartesianFrames
