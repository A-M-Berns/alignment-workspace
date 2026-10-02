import Cleanroom.Decision.DpReferentsCdt.Defs
import Cleanroom.Decision.DpLocalOpt.Trees

/-!
# C2-3″ under the shared seed: the Death-in-Damascus row

Mandate T7's third row. `dp-local-opt`'s `deathDamascus p L c` keys Death's city to a draw: with
probability `p` Death is at the drawn city (one `d`-node), with probability `1 − p` Death's city is
an *independent sample* from `C(d)` (a second `d`-node). Under Definition 6′ (`leafLaw'`, the shared
seed) the second `d`-node re-reads the seed drawn at the first, so "Death's independent sample" is
the agent's own draw and Death is always at the agent's city: **`V′(q) = −c(1−q)` at every `p`**
(`deathDamascus_value'`), maximised by always staying (`q = 1`, value `0`), while Definition 6's
`V(q)` at `p = 0` is P03's quadratic (`dp-local-opt`'s `deathDamascus_value`). The seed deviation
conditioned on `O_d = ⊤` is `refR1State' = (0, −c)` (`deathDamascus_refR1State'`): the row's
`(0, −1)` at `c = 1`. (The mandate names `p = 1`; at `p = 1` the tree has one `d`-node on every
positive path and the two semantics agree; the content is at `p < 1`, where the seed collapses the
independent sample — the row is stated for every `p`.)

Worlds are `Unit` on this tree, so no act coordinate is recorded and the forcing referents (which
read `actEv`) have no meaningful instance here; the row is about `value'`/`refR1State'` only.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

section dd

variable (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L c : ℚ)

/-- Sums over the six leaves of Death in Damascus. Source: none: infrastructure. Kind: L -/
theorem dd_sum (f : (deathDamascus p hp0 hp1 L c).Leaves → ℚ) :
    ∑ ℓ, f ℓ = (f ⟨0, .a, ()⟩ + f ⟨0, .b, ()⟩) +
      ((f ⟨1, .a, .a, ()⟩ + f ⟨1, .a, .b, ()⟩) + (f ⟨1, .b, .a, ()⟩ + f ⟨1, .b, .b, ()⟩)) := by
  unfold deathDamascus at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  have h0 : (∑ ℓ : (Tree.decision () fun | .a => Tree.leaf () 0 | .b => Tree.leaf () (-c) :
      Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨0, ℓ⟩) = f ⟨0, .a, ()⟩ + f ⟨0, .b, ()⟩ := by
    rw [sum_leaves_decision (M := ℚ), Act2.sum_univ]
    show (∑ ℓ : (Tree.leaf () 0 : Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨0, .a, ℓ⟩) +
      (∑ ℓ : (Tree.leaf () (-c) : Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨0, .b, ℓ⟩) = _
    rw [Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  have h1 : (∑ ℓ : (Tree.decision () fun
      | .a => Tree.decision () fun | .a => Tree.leaf () 0 | .b => Tree.leaf () (L - c)
      | .b => Tree.decision () fun | .a => Tree.leaf () L | .b => Tree.leaf () (-c) :
      Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨1, ℓ⟩) =
      (f ⟨1, .a, .a, ()⟩ + f ⟨1, .a, .b, ()⟩) + (f ⟨1, .b, .a, ()⟩ + f ⟨1, .b, .b, ()⟩) := by
    rw [sum_leaves_decision (M := ℚ), Act2.sum_univ]
    show (∑ ℓ : (Tree.decision () fun | .a => Tree.leaf () 0 | .b => Tree.leaf () (L - c) :
        Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨1, .a, ℓ⟩) +
      (∑ ℓ : (Tree.decision () fun | .a => Tree.leaf () L | .b => Tree.leaf () (-c) :
        Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨1, .b, ℓ⟩) = _
    rw [sum_leaves_decision (M := ℚ), sum_leaves_decision (M := ℚ), Act2.sum_univ, Act2.sum_univ]
    show ((∑ ℓ : (Tree.leaf () 0 : Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨1, .a, .a, ℓ⟩) +
        (∑ ℓ : (Tree.leaf () (L - c) : Tree Unit Unit (fun _ => Act2) ℚ).Leaves,
          f ⟨1, .a, .b, ℓ⟩)) +
      ((∑ ℓ : (Tree.leaf () L : Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨1, .b, .a, ℓ⟩) +
        (∑ ℓ : (Tree.leaf () (-c) : Tree Unit Unit (fun _ => Act2) ℚ).Leaves,
          f ⟨1, .b, .b, ℓ⟩)) = _
    rw [Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  show (∑ ℓ : (Tree.decision () fun | .a => Tree.leaf () 0 | .b => Tree.leaf () (-c) :
      Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.decision () fun
      | .a => Tree.decision () fun | .a => Tree.leaf () 0 | .b => Tree.leaf () (L - c)
      | .b => Tree.decision () fun | .a => Tree.leaf () L | .b => Tree.leaf () (-c) :
      Tree Unit Unit (fun _ => Act2) ℚ).Leaves, f ⟨1, ℓ⟩) = _
  rw [h0, h1]

variable (C : Proc Unit (fun _ => Act2) ℚ)

/-- **Death in Damascus under the shared seed: `V′(q) = −c(1 − q)` at every `p`**, `q := C(d)(stay)` —
Death is always at the agent's city, so only fleeing costs; always staying is optimal with value
`0`. Definition 6's value at `p = 0` is P03's quadratic (`dp-local-opt`'s `deathDamascus_value`:
`q(1−q)(L−c) + (1−q)(qL − (1−q)c)`, which rewards mixing).
Source: `C2.md` C2-3″ (the Death-in-Damascus row); `repair/P03.md` P03-7; mandate T7
Kind: P
Fidelity: exact -/
theorem deathDamascus_value' :
    value' C (deathDamascus p hp0 hp1 L c) = -(c * (1 - (C ()).w .a)) := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := by
    have := (C ()).sum_one
    rw [Act2.sum_univ] at this
    linarith
  unfold value'
  rw [dd_sum]
  simp [leafLaw', leafLawSeed, deathDamascus, payoff, FinDistr.coin, hb]
  ring

/-- **The seed deviation conditioned on `O_d = ⊤` is `(0, −c)`**: `refR1State'(stay) = 0`,
`refR1State'(flee) = −c` — the row's `(0, −1)` at `c = 1`, at every `p`.
Source: `C2.md` C2-3″ ("deathDamascus … `(0, −1)`"); mandate T7
Kind: N+ -/
theorem deathDamascus_refR1State' (x : Act2) :
    refR1State' C (deathDamascus p hp0 hp1 L c) (fun _ => Finset.univ) () x =
      if x = .a then 0 else -c := by
  unfold refR1State' condExp' paySum' nu'
  have huniv : worldEv (deathDamascus p hp0 hp1 L c) (Finset.univ : Finset Unit) = Finset.univ := by
    ext ℓ; simp [worldEv]
  rw [huniv, sum_leafLaw', div_one]
  change value' (C.deviatePure () x) (deathDamascus p hp0 hp1 L c) = _
  rw [deathDamascus_value']
  cases x <;> simp [Proc.deviatePure, Proc.deviate_same]

end dd

end Cleanroom.Decision.DpReferentsCdt
