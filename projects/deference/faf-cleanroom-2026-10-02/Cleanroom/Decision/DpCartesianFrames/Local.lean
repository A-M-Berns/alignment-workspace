import Cleanroom.Decision.DpCartesianFrames.Profiles

/-!
# The run lemmas and the Local Theorem

Package `dp-cartesian-frames`, file 3.

* **`runLeaf_eq_or_below`** (the run-comparison lemma, the real content of T3, reused by T6 and
  T7): two policies agreeing off `d` reach the same leaf under any profile, unless the run of
  the first passes a `d`-node — in which case its leaf lies below that node.
* **`runLeaf_congr`**: a run depends only on the answers at the points it consults (`#_d > 0`
  on its leaf) — the "agreement along the path" lemma T6's no-straddle policy needs.
* **The Local Theorem** (CF-10, headline 2), for a point `d` with claimed observation
  `S := S_{O_d}`: (i) every `d`-node subtree-veridical (dp-core-tree's possibilistic
  `SubtreeVeridical`) ⟹ (ii) `Loc d B`'s agent is powerless outside `S`
  (`powerlessOutside_loc_of_subtreeVeridical`) ⟹ (iii) `{S, Sᶜ}` is observable in `Loc d B`
  (`observable2_loc_of_subtreeVeridical`, through CF-9). No coverage hypothesis appears, and `d`
  need not be queried. Both converses are refuted by trees in `Witnesses.lean`.
* **CF-15's contrapositive** (T11(a)): a powerlessness failure at `Loc d B` exhibits a
  `d`-node that is not subtree-veridical.

Lazy seeding throughout (`Fr`/`Loc` of `Profiles.lean`).
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### The run lemmas -/

/-- **The run-comparison lemma.** If `π₀` and `π₁` agree at every point other than `d`, then
under any profile `ε` either their runs on `B` coincide, or the run of `π₀` passes a `d`-node
`q` (so its leaf lies below `q`). Structural induction: the two walks take identical edges until
a `d`-node is met.
Source: cf-correspondence CF-10 proof (line 43: "the runs … walk identical edges unless/until a
`d`-node is reached")
Kind: P
Fidelity: exact
Hyps: none -/
theorem runLeaf_eq_or_below [DecidableEq ι] [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] (d : ι) (π₀ π₁ : (e : ι) → acts e)
    (h : ∀ e, e ≠ d → π₀ e = π₁ e) :
    (B : Tree Ω ι acts K) → ∀ ε : ChanceProfile B,
      runLeaf π₀ B ε = runLeaf π₁ B ε ∨
        ∃ q : B.DecNode, pt B q = d ∧ runLeaf π₀ B ε ∈ leavesBelow B q
  | .leaf _ _, _ => Or.inl rfl
  | .chance n β child, ε => by
      rcases runLeaf_eq_or_below d π₀ π₁ h (child ε.1) (ε.2 ε.1) with heq | ⟨q, hq, hmem⟩
      · exact Or.inl (congrArg (Sigma.mk ε.1) heq)
      · refine Or.inr ⟨⟨ε.1, q⟩, hq, ?_⟩
        rw [mem_leavesBelow] at hmem ⊢
        show (edgeOf (Tree.chance n β child) ⟨ε.1, q⟩
          ⟨ε.1, runLeaf π₀ (child ε.1) (ε.2 ε.1)⟩).isSome
        rw [edgeOf_chance, dif_pos rfl]
        exact hmem
  | .decision d' child, ε => by
      by_cases hd : d' = d
      · subst hd
        refine Or.inr ⟨none, rfl, ?_⟩
        rw [mem_leavesBelow]
        rfl
      · have hπ : π₀ d' = π₁ d' := h d' hd
        rcases runLeaf_eq_or_below d π₀ π₁ h (child (π₀ d')) (ε (π₀ d')) with heq | ⟨q, hq, hmem⟩
        · left
          simp only [runLeaf_decision]
          rw [← hπ]
          exact congrArg (Sigma.mk (π₀ d')) heq
        · refine Or.inr ⟨some ⟨π₀ d', q⟩, hq, ?_⟩
          rw [mem_leavesBelow] at hmem ⊢
          show (edgeOf (Tree.decision d' child) (some ⟨π₀ d', q⟩)
            ⟨π₀ d', runLeaf π₀ (child (π₀ d')) (ε (π₀ d'))⟩).isSome
          rw [edgeOf_decision_some, dif_pos rfl]
          exact hmem

/-- **A run depends only on the answers at the points it consults**: if `π'` agrees with `π` at
every point `d` with `#_d > 0` on the leaf of `π`'s run, the runs coincide.
Source: cf-frontier CFF-12 proof (line 80: "the run of `π_f` from `x` consults only
`S`-points, at which `π_f = f(S)`, so it coincides with the run of `f(S)`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem runLeaf_congr [DecidableEq ι] (π π' : (e : ι) → acts e) :
    (B : Tree Ω ι acts K) → ∀ ε : ChanceProfile B,
      (∀ d, 0 < count d B (runLeaf π B ε) → π d = π' d) → runLeaf π B ε = runLeaf π' B ε
  | .leaf _ _, _, _ => rfl
  | .chance _ _ child, ε, h =>
      congrArg (Sigma.mk ε.1)
        (runLeaf_congr π π' (child ε.1) (ε.2 ε.1) fun d hd => h d hd)
  | .decision d child, ε, h => by
      have hd : π d = π' d := h d (by
        show 0 < (if d = d then 1 else 0) + count d (child (π d)) (runLeaf π (child (π d)) (ε (π d)))
        rw [if_pos rfl]
        omega)
      simp only [runLeaf_decision]
      rw [← hd]
      refine congrArg (Sigma.mk (π d)) (runLeaf_congr π π' (child (π d)) (ε (π d)) fun e he => ?_)
      refine h e ?_
      show 0 < (if d = e then 1 else 0) + count e (child (π d)) (runLeaf π (child (π d)) (ε (π d)))
      exact Nat.lt_of_lt_of_le he (Nat.le_add_left _ _)

/-! ### The Local Theorem -/

section local_theorem

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (obs : ι → Finset Ω) (B : Tree Ω ι acts K) (d : ι)

/-- **Local Theorem, (i) ⟹ (ii)** (headline 2): if every `d`-node of `B` is subtree-veridical
for `O_d` (possibilistic no-simulation: every leaf below every `d`-node has its world in
`O_d`), then `Loc d B`'s agent is powerless outside `S_{O_d}`. For a frozen column `(p, ε)`,
the runs of `p[d ↦ a₀]` and `p[d ↦ a₁]` either coincide or the first passes a `d`-node, in
which case its leaf-world lies in `O_d` — so the powerlessness antecedent never fires. No
coverage hypothesis; `d` need not be queried (then the agent is inert and the claim trivial).
Lazy seeding.
Source: cf-correspondence CF-10 (lines 43–45); mandate T3
Kind: P
Fidelity: exact
Hyps: none (`SubtreeVeridical` is dp-core-tree's definition of record) -/
theorem powerlessOutside_loc_of_subtreeVeridical
    (hV : ∀ q ∈ fiber B d, SubtreeVeridical obs B q) :
    PowerlessOutside (Loc d B) (SO obs d) := by
  rintro ⟨p, ε⟩ a₀ a₁ hout
  rcases runLeaf_eq_or_below d (extend d a₀ p) (extend d a₁ p)
      (fun e he => by rw [extend_ne d a₀ p he, extend_ne d a₁ p he]) B ε with heq | ⟨q, hq, hmem⟩
  · exact congrArg (readout B) heq
  · exfalso
    apply hout
    have hw := hV q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩) _ hmem
    rw [hq] at hw
    exact hw

/-- **Local Theorem, (i) ⟹ (iii)** (headline 2): subtree-veridicality at every `d`-node makes
the claimed observation `{S_{O_d}, ¬S_{O_d}}` a true Observation at `Loc d B`. Composition of
(i) ⟹ (ii) with CF-9. Lazy seeding; no coverage hypothesis.
Source: cf-correspondence CF-10 (line 43); mandate T3
Kind: C
Fidelity: exact
Hyps: none -/
theorem observable2_loc_of_subtreeVeridical
    (hV : ∀ q ∈ fiber B d, SubtreeVeridical obs B q) :
    Observable2 (Loc d B) (SO obs d) :=
  (powerlessOutside_loc_of_subtreeVeridical obs B d hV).observable2

/-- **CF-15's diagnosis, contrapositive of (i) ⟹ (ii)**: a powerlessness failure at `Loc d B`
outside `S_{O_d}` exhibits a `d`-node that is not subtree-veridical — the failure is at a
simulation node.
Source: cf-correspondence CF-15 (line 75: "powerlessness outside `S` fails at the `H`-column,
i.e. exactly at the simulation node ((V_d) fails there), per CF-10's contrapositive")
Kind: C
Fidelity: exact
Hyps: none -/
theorem exists_not_subtreeVeridical_of_not_powerless
    (h : ¬ PowerlessOutside (Loc d B) (SO obs d)) :
    ∃ q ∈ fiber B d, ¬ SubtreeVeridical obs B q := by
  by_contra hc
  exact h (powerlessOutside_loc_of_subtreeVeridical obs B d fun q hq => by
    by_contra hn
    exact hc ⟨q, hq, hn⟩)

end local_theorem

end Cleanroom.Decision.DpCartesianFrames
