import Cleanroom.Decision.DpLocalOpt.Coalition
import Cleanroom.Decision.DpLocalOpt.TwoPointWitness

/-!
# `dp-local-opt`: Definition 23 spectrum witnesses (T10, repair round 1)

The refinement order of Proposition 13 is strict already on two points: `(H,H)` on `twoStag` is
conflict-free for the singleton family (it is mixed-coherent) and not for the grand coalition
(it is not optimal). A39's three-point claim — an intermediate family `{{d₁,d₂},{d₃}}` strictly
between — is shipped on `threeCoal` in `ThreeCoalWitness.lean` (`threeCoal_spectrum_strict`,
same repair round; this header and the docstring below were stale until repair round 2, audit
r2 fidelity non-blocking 3 / adversarial N4).
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

/-- **The Definition 23 spectrum is strict on two points**: `(H,H)` on `twoStag` is conflict-free
for the singleton family and not for the grand coalition `{queried B}` (from
`twoStag_HH_coherent_thm1_not_optimal`, `conflictFree_singletons_iff` and
`conflictFree_trivial_iff'`). Endpoints of `conflictFree_antitone`'s order separated; A39's
three-point intermediate family is `threeCoal_spectrum_strict` (`ThreeCoalWitness.lean`).
Source: A39; `repair/harmony.md` HA-9′ (the strictness claim); audit r1 adversarial N2 (probe D,
adopted)
Kind: N+
Fidelity: weaker: two-point endpoints only (HA-9′'s three-point table is
`threeCoal_spectrum_strict`)
Hyps: (a) all -/
theorem twoStag_spectrum_strict :
    ConflictFree profHH twoStag
        ((fun d => ({d} : Finset Pt2)) '' (↑(queried twoStag) : Set Pt2)) ∧
    ¬ ConflictFree profHH twoStag {queried twoStag} := by
  obtain ⟨hcoh, -, -, hnopt, -, -⟩ := twoStag_HH_coherent_thm1_not_optimal
  refine ⟨(conflictFree_singletons_iff _ _).mpr hcoh, ?_⟩
  rw [conflictFree_trivial_iff']
  exact hnopt

end Cleanroom.Decision.DpLocalOpt
