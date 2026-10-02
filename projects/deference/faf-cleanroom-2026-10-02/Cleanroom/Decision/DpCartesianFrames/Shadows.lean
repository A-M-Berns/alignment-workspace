import Cleanroom.Decision.DpCartesianFrames.Witnesses
import Cleanroom.Found.DpCoreTree.Shadow

/-!
# CF-23: the extensional shadow and the biextensional collapse are transverse

Package `dp-cartesian-frames`, file 17 (repair round 1; mandate T5(c)). Lazy seeding.

Two separations, over `dp-core-tree`'s `shadow` (the joint law of `(λ, r)` under `μ_{B,C}`):

* **(i) Equal frames, different shadows**: the β-pair has one frame literally
  (`fr_pairTree_eq`, `rfl`) and different shadows under the pure `a` procedure — the shadow
  keeps the probabilities the frame forgets (`shadow_pairTree_ne`).
* **(ii) Equal shadows, inequivalent frames**: the scrambled-consultation pair — `scrX` (a fair
  coin routing to two `d`-nodes with the answer-to-leaf maps swapped) and `scrZ` (a fair coin
  with an inert `d`-query per branch) — has `shadow C scrX = shadow C scrZ` for **every**
  procedure `C` (`shadow_scrX_eq_scrZ`), while `Fr scrX` has two distinct rows and `Fr scrZ`
  one, so the frames are not biextensionally equivalent (`not_biextEquiv_fr_scrX_scrZ`; the
  invariant is "all rows agree", `PowerlessOutside _ ∅`, as in `Cff8.lean`).

Neither quotient refines the other: the frame remembers counterfactual-profile act-relevance
that every distribution washes out; the shadow remembers the measure the frame forgets.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ### (i) The β-pair: equal frames, different shadows -/

/-- Sums over the leaves of `pairSub β`: over the action, then the inner coin.
Source: none: infrastructure
Kind: L -/
theorem sum_leaves_pairSub (β : FinDistr ℚ (Fin 2)) (f : (pairSub β).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ act, ∑ j, f ⟨act, ⟨j, ()⟩⟩ := by
  show ∑ ℓ : (Tree.decision (acts := fun _ : Unit => Act2) () fun act =>
    Tree.chance 2 β fun j => Tree.leaf (coinOf j) (if act = .a then 1 else 0)).Leaves, f ℓ = _
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- Sums over the leaves of `pairTree β`: the fair-coin member, then the `β` member.
Source: none: infrastructure
Kind: L -/
theorem sum_leaves_pairTree (β : FinDistr ℚ (Fin 2)) (f : (pairTree β).Leaves → ℚ) :
    ∑ ℓ, f ℓ = (∑ ℓ : (pairSub FinDistr.fair).Leaves, f ⟨0, ℓ⟩) +
      ∑ ℓ : (pairSub β).Leaves, f ⟨1, ℓ⟩ := by
  show ∑ ℓ : (Tree.chance 2 FinDistr.fair fun i => pairSub (![FinDistr.fair, β] i)).Leaves,
    f ℓ = _
  rw [sum_leaves_chance, Fin.sum_univ_two]
  rfl

/-- The shadow of `pairTree β` under the pure `a` procedure at the world `(true, 1)`:
`½ · ½ + ½ · β(0)` (tails of the root coin → the fair inner coin; heads → the inner coin `β`).
Source: cf-correspondence CF-23 (line 120: "the shadow keeps probabilities")
Kind: L -/
theorem shadow_pairTree_pure_a (β : FinDistr ℚ (Fin 2)) :
    shadow (Proc.ofFun fun _ => Act2.a) (pairTree β) (true, 1) = 1 / 4 + β.w 0 / 2 := by
  unfold shadow
  rw [sum_leaves_pairTree, sum_leaves_pairSub, sum_leaves_pairSub]
  simp only [Act2.sum_univ, Fin.sum_univ_two, pairTree, pairSub, world_chance, world_decision,
    world_leaf, payoff_chance, payoff_decision, payoff_leaf, leafLaw_chance, leafLaw_decision,
    leafLaw_leaf, Matrix.cons_val_zero, Matrix.cons_val_one, coinOf, Proc.ofFun_w, FinDistr.fair,
    FinDistr.coin, reduceCtorEq, if_true, if_false]
  norm_num
  ring

/-- **CF-23 (i): equal frames, different shadows.** `Fr (pairTree fair) = Fr (pairTree coinThird)`
literally, yet their shadows under the pure `a` procedure differ (`½` vs `5/12` at `(true, 1)`):
the extensional shadow is not a function of the frame.
Source: cf-correspondence CF-23 (line 120: "(i) the β-pair of CF-14(a): identical frames,
different shadows (the shadow keeps probabilities)"); mandate T5(c)
Kind: N+
Fidelity: exact -/
theorem shadow_pairTree_ne :
    Fr (pairTree FinDistr.fair) = Fr (pairTree coinThird) ∧
    shadow (Proc.ofFun fun _ => Act2.a) (pairTree FinDistr.fair) ≠
      shadow (Proc.ofFun fun _ => Act2.a) (pairTree coinThird) := by
  refine ⟨fr_pairTree_eq _ _, fun h => ?_⟩
  have h1 := congrFun h (true, 1)
  rw [shadow_pairTree_pure_a, shadow_pairTree_pure_a] at h1
  norm_num [FinDistr.fair, FinDistr.coin, coinThird] at h1

/-! ### (ii) The scrambled-consultation pair: equal shadows, inequivalent frames -/

/-- The left `d`-node of `X`: `a ↦ w₁ = true`, `b ↦ w₂ = false`.
Source: cf-correspondence CF-23 (line 120)
Kind: D -/
def scrL : Tree Bool Unit (fun _ => Act2) ℚ :=
  .decision () fun act => .leaf (if act = .a then true else false) 0

/-- The right `d`-node of `X`: `a ↦ w₂`, `b ↦ w₁`.
Source: cf-correspondence CF-23 (line 120)
Kind: D -/
def scrR : Tree Bool Unit (fun _ => Act2) ℚ :=
  .decision () fun act => .leaf (if act = .a then false else true) 0

/-- Tree `X`: a fair coin routing to two `d`-nodes with the answer-to-leaf maps swapped.
Source: cf-correspondence CF-23 (line 120: "tree `X` = fair coin routing to two `d`-nodes with
answer-to-leaf maps swapped")
Kind: D -/
def scrX : Tree Bool Unit (fun _ => Act2) ℚ := .chance 2 FinDistr.fair ![scrL, scrR]

/-- The inert `d`-node landing in `w`.
Source: cf-correspondence CF-23 (line 120)
Kind: D -/
def scrI (w : Bool) : Tree Bool Unit (fun _ => Act2) ℚ := .decision () fun _ => .leaf w 0

/-- Tree `Z`: a fair coin with a spurious `d`-query per branch (`L`: both answers `↦ w₁`;
`R`: both `↦ w₂`).
Source: cf-correspondence CF-23 (line 120: "tree `Z` = fair coin with a spurious `d`-query per
branch")
Kind: D -/
def scrZ : Tree Bool Unit (fun _ => Act2) ℚ := .chance 2 FinDistr.fair ![scrI true, scrI false]

/-- Sums over the leaves of `X`.
Source: none: infrastructure
Kind: L -/
theorem sum_leaves_scrX (f : scrX.Leaves → ℚ) :
    ∑ ℓ, f ℓ = (∑ act, f ⟨0, ⟨act, ()⟩⟩) + ∑ act, f ⟨1, ⟨act, ()⟩⟩ := by
  show ∑ ℓ : (Tree.chance 2 FinDistr.fair ![scrL, scrR]).Leaves, f ℓ = _
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : (Tree.decision (acts := fun _ : Unit => Act2) () fun act =>
      Tree.leaf (if act = .a then true else false) (0 : ℚ)).Leaves, f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.decision (acts := fun _ : Unit => Act2) () fun act =>
      Tree.leaf (if act = .a then false else true) (0 : ℚ)).Leaves, f ⟨1, ℓ⟩) = _
  rw [sum_leaves_decision, sum_leaves_decision]
  simp only [Tree.sum_leaves_leaf]

/-- Sums over the leaves of `Z`.
Source: none: infrastructure
Kind: L -/
theorem sum_leaves_scrZ (f : scrZ.Leaves → ℚ) :
    ∑ ℓ, f ℓ = (∑ act, f ⟨0, ⟨act, ()⟩⟩) + ∑ act, f ⟨1, ⟨act, ()⟩⟩ := by
  show ∑ ℓ : (Tree.chance 2 FinDistr.fair ![scrI true, scrI false]).Leaves, f ℓ = _
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : (Tree.decision (acts := fun _ : Unit => Act2) () fun _ =>
      Tree.leaf true (0 : ℚ)).Leaves, f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.decision (acts := fun _ : Unit => Act2) () fun _ =>
      Tree.leaf false (0 : ℚ)).Leaves, f ⟨1, ℓ⟩) = _
  rw [sum_leaves_decision, sum_leaves_decision]
  simp only [Tree.sum_leaves_leaf]

/-- **CF-23 (ii), the shadows coincide**: for every procedure `C`, `shadow C scrX = shadow C scrZ`
(each world `w₁`, `w₂` has mass `½ C(a) + ½ C(b)` in both; mixed procedures included).
Source: cf-correspondence CF-23 (line 120: "Every procedure, mixed included, has leaf-law
`½ w₁ + ½ w₂` in both: `X̂ = Ẑ` as functionals")
Kind: P
Fidelity: exact
Hyps: none -/
theorem shadow_scrX_eq_scrZ (C : Proc Unit (fun _ => Act2) ℚ) : shadow C scrX = shadow C scrZ := by
  funext x
  unfold shadow
  rw [sum_leaves_scrX, sum_leaves_scrZ]
  simp only [Act2.sum_univ, scrX, scrZ, scrL, scrR, scrI, world_chance, world_decision,
    world_leaf, payoff_chance, payoff_decision, payoff_leaf, leafLaw_chance, leafLaw_decision,
    leafLaw_leaf, Matrix.cons_val_zero, Matrix.cons_val_one, reduceCtorEq, if_true, if_false]
  obtain ⟨ω, r⟩ := x
  simp only [FinDistr.fair, FinDistr.coin, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases eq_or_ne r 0 with rfl | hr
  · cases ω <;> ring_nf
  · cases ω <;> simp [Ne.symm hr]

/-- Every row of `Fr scrZ` is the same function of the column (both queries are inert).
Source: cf-correspondence CF-23 (line 120: "`Fr(Z)` collapses to one row")
Kind: L -/
theorem scrZ_rows_agree : PowerlessOutside (Fr scrZ) ∅ := by
  rintro ⟨i, f⟩ π π' _
  fin_cases i <;> rfl

/-- The two rows of `Fr scrX` differ (on the tails column `a` lands in `w₁`, `b` in `w₂`).
Source: cf-correspondence CF-23 (line 120: "`Fr(X)` has two distinct rows `(w₁,w₂), (w₂,w₁)`")
Kind: L -/
theorem scrX_rows_differ : ¬ PowerlessOutside (Fr scrX) ∅ := by
  intro h
  have h0 := h (0, fun _ => Classical.arbitrary _) (fun _ => Act2.a) (fun _ => Act2.b)
    (Set.notMem_empty _)
  have h1 : ((true : Bool), (0 : ℚ)) = (false, 0) := h0
  exact Bool.noConfusion (congrArg Prod.fst h1)

/-- **CF-23 (ii): equal shadows, inequivalent frames.** `shadow C scrX = shadow C scrZ` for every
`C`, yet `¬ (Fr scrX ≃ᵇ Fr scrZ)` — "all rows agree" is a biextensional invariant separating
them. So v2's shadow is not the tree-side face of biextensional collapse; the two are transverse
quotients.
Source: cf-correspondence CF-23 (line 120: "(ii) The scrambled-consultation pair … `≄`"); mandate
T5(c)
Kind: N+
Fidelity: exact (non-equivalence through the row-agreement invariant rather than `collapse`
cardinalities — same content, no counting needed) -/
theorem not_biextEquiv_fr_scrX_scrZ :
    (∀ C : Proc Unit (fun _ => Act2) ℚ, shadow C scrX = shadow C scrZ) ∧ ¬ (Fr scrX ≃ᵇ Fr scrZ) :=
  ⟨shadow_scrX_eq_scrZ, fun h => scrX_rows_differ
    ((powerlessOutside_iff_of_biextEquiv h ∅).mpr scrZ_rows_agree)⟩

end Cleanroom.Decision.DpCartesianFrames
