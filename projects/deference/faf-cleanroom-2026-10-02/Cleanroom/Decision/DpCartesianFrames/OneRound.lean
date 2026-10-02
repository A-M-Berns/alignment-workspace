import Cleanroom.Decision.DpCartesianFrames.Local
import Cleanroom.Found.DpCoreTree.RecordingThms

/-!
# The one-round Global Theorem (CF-12)

Package `dp-cartesian-frames`, file 10 (T4(a),(b)). Lazy seeding.

* `DecisionFree`, `OneRound` (no decision node strictly below another), by recursion; a run of
  a one-round tree consults at most one point (`OneRound.eq_of_count_pos`).
* `obsSystem obs : Ω × K → Option ι`, the observation system (the point whose observation the
  world satisfies; `none` for the rest), well defined on realized worlds under pairwise
  disjointness of the realized observation events — which coverage + one-round implies
  (`disjoint_of_cover`).
* **CF-12** (`observable_fr_obsSystem_of_oneRound`): one-round, every `d`-node
  subtree-veridical, realized observation events pairwise disjoint ⟹ the observation system
  is observable in `Fr B` (policy `π_f(d) := f(some d)(d)`).
* The general fact `Observable.columnDeterminedV` (CF-8 for any number of cells) and the
  `&`-decomposition `Fr B ≃ᵇ &_c Assume_{E_c}(Fr B)` (T4(b)) through T10(b).
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### One-round trees -/

/-- A tree with no decision node at all.
Source: cf-correspondence CF-12 (line 47: "one-round"); mandate T4(a)
Kind: D -/
def DecisionFree : Tree Ω ι acts K → Prop
  | .leaf _ _ => True
  | .chance _ _ child => ∀ i, DecisionFree (child i)
  | .decision _ _ => False

/-- **One-round**: no decision node lies strictly below another (every child of a decision node
is decision-free).
Source: cf-correspondence CF-12 (line 47); mandate T4(a) ("not `dp-core-tree`'s `IsTopmost`,
which is per point")
Kind: D
Fidelity: exact -/
def OneRound : Tree Ω ι acts K → Prop
  | .leaf _ _ => True
  | .chance _ _ child => ∀ i, OneRound (child i)
  | .decision _ child => ∀ a, DecisionFree (child a)

/-- No point is consulted on any path of a decision-free tree.
Source: none: infrastructure
Kind: L -/
theorem DecisionFree.count_eq_zero [DecidableEq ι] :
    (B : Tree Ω ι acts K) → DecisionFree B → ∀ (e : ι) (ℓ : B.Leaves), count e B ℓ = 0
  | .leaf _ _, _, _, _ => rfl
  | .chance _ _ child, h, e, ⟨i, ℓ⟩ => DecisionFree.count_eq_zero (child i) (h i) e ℓ
  | .decision _ _, h, _, _ => h.elim

/-- A run of a one-round tree consults at most one point.
Source: cf-correspondence CF-12 (line 47)
Kind: P
Fidelity: exact
Hyps: none -/
theorem OneRound.eq_of_count_pos [DecidableEq ι] :
    (B : Tree Ω ι acts K) → OneRound B → ∀ (ℓ : B.Leaves) (e e' : ι),
      0 < count e B ℓ → 0 < count e' B ℓ → e = e'
  | .leaf _ _, _, _, _, _, he, _ => absurd he (lt_irrefl 0)
  | .chance _ _ child, h, ⟨i, ℓ⟩, e, e', he, he' =>
      OneRound.eq_of_count_pos (child i) (h i) ℓ e e' he he'
  | .decision d child, h, ⟨a, ℓ⟩, e, e', he, he' => by
      have h0 := DecisionFree.count_eq_zero (child a) (h a)
      have key : ∀ x, 0 < count x (.decision d child) ⟨a, ℓ⟩ → d = x := by
        intro x hx
        by_contra hne
        have : count x (.decision d child) ⟨a, ℓ⟩ = 0 := by
          show (if d = x then 1 else 0) + count x (child a) ℓ = 0
          rw [if_neg hne, h0]
        omega
      exact (key e he).symm.trans (key e' he')

/-! ### The observation system -/

/-- **The observation system**: the point whose observation the world satisfies (`none` if
none does; a choice if several do — unique on realized worlds under disjointness).
Source: cf-correspondence CF-12 (line 47: "`V_obs := {S_{O_d}}_{d ∈ D_B} ∪ {S₀}`, `S₀` the
remaining image-worlds")
Kind: D
Fidelity: exact (as a map `W → Option ι`, CF-2's partition convention) -/
noncomputable def obsSystem (obs : ι → Finset Ω) : Ω × K → Option ι :=
  fun w => open Classical in
    if h : ∃ d, w.1 ∈ obs d then some (Classical.choose h) else none

/-- Under pairwise disjointness of the realized observation events, the observation system of a
realized world satisfying `O_d` is `some d`.
Source: cf-correspondence CF-12 (line 47)
Kind: L -/
theorem obsSystem_readout_eq_some (obs : ι → Finset Ω) (B : Tree Ω ι acts K)
    (hdisj : ∀ d d', d ≠ d' → ∀ ℓ : B.Leaves, ¬ (world B ℓ ∈ obs d ∧ world B ℓ ∈ obs d'))
    (ℓ : B.Leaves) (d : ι) (hd : world B ℓ ∈ obs d) : obsSystem obs (readout B ℓ) = some d := by
  unfold obsSystem
  rw [dif_pos ⟨d, hd⟩]
  congr 1
  by_contra hne
  exact hdisj _ _ hne ℓ ⟨Classical.choose_spec (⟨d, hd⟩ : ∃ d, (readout B ℓ).1 ∈ obs d), hd⟩

/-- **Coverage + one-round ⟹ disjointness**: a leaf satisfying `O_d` and `O_{d'}` would need a
`d`-node and a `d'`-node on one path.
Source: cf-correspondence CF-12 (line 47: "(which (C_d) + one-round implies …)")
Kind: P
Fidelity: exact (possibilistic coverage: every leaf satisfying `O_d` passes a `d`-node)
Hyps: none -/
theorem disjoint_of_cover [DecidableEq ι] (obs : ι → Finset Ω) (B : Tree Ω ι acts K)
    (h1 : OneRound B) (hcov : ∀ d (ℓ : B.Leaves), world B ℓ ∈ obs d → 0 < count d B ℓ) :
    ∀ d d', d ≠ d' → ∀ ℓ : B.Leaves, ¬ (world B ℓ ∈ obs d ∧ world B ℓ ∈ obs d') :=
  fun d d' hne ℓ ⟨hd, hd'⟩ =>
    hne (OneRound.eq_of_count_pos B h1 ℓ d d' (hcov d ℓ hd) (hcov d' ℓ hd'))

/-! ### CF-12 -/

/-- **CF-12, the one-round Global Theorem**: on a one-round tree with every `d`-node
subtree-veridical and pairwise disjoint realized observation events, the observation system is
observable in the lazy frame `Fr B`. The policy `π_f(d) := f(some d)(d)` works: a run consults
at most one point `d`; if one, its leaf-world lies in `O_d` (veridicality), the observation
system reads `some d` (disjointness), and the run coincides with `f(some d)`'s
(`runLeaf_congr`); if none, every policy runs to the same leaf. Coverage is not needed.
Source: cf-correspondence CF-12 (line 47); mandate T4(a)
Kind: P
Fidelity: exact (disjointness taken as the hypothesis, as the source states it; coverage +
one-round gives it by `disjoint_of_cover`)
Hyps: none -/
theorem observable_fr_obsSystem_of_oneRound [DecidableEq ι] [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] (obs : ι → Finset Ω) (B : Tree Ω ι acts K) (h1 : OneRound B)
    (hV : ∀ d, ∀ q ∈ fiber B d, SubtreeVeridical obs B q)
    (hdisj : ∀ d d', d ≠ d' → ∀ ℓ : B.Leaves, ¬ (world B ℓ ∈ obs d ∧ world B ℓ ∈ obs d')) :
    Observable (Fr B) (obsSystem obs) := by
  intro f
  refine ⟨fun d => f (some d) d, fun ε => ?_⟩
  simp only [Fr_outcome]
  by_cases hc : ∃ e, 0 < count e B (runLeaf (fun d => f (some d) d) B ε)
  · obtain ⟨e, he⟩ := hc
    obtain ⟨q, hq, hedge⟩ := exists_dNode_of_count_pos e B _ he
    have hw : world B (runLeaf (fun d => f (some d) d) B ε) ∈ obs e := by
      have := hV e q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩) _
        ((mem_leavesBelow _ _ _).mpr hedge)
      rwa [hq] at this
    rw [obsSystem_readout_eq_some obs B hdisj _ e hw]
    congr 1
    exact (runLeaf_congr (fun d => f (some d) d) (f (some e)) B ε fun e' he' => by
      obtain rfl := OneRound.eq_of_count_pos B h1 _ e' e he' he
      rfl).symm
  · congr 1
    exact (runLeaf_congr (fun d => f (some d) d) _ B ε fun e' he' => absurd ⟨e', he'⟩ hc).symm

/-- **CF-8 for any number of cells**: an observable partition has column-determined cells (the
two-cell argument, with `f` sending the first cell to `a₁` and everything else to `a₀`).
Source: cf-correspondence CF-8 (line 37), cellwise
Kind: P
Fidelity: exact
Hyps: none -/
theorem Observable.columnDeterminedV {W : Type} {V : Type} {C : CartesianFrames.Frame W}
    {v : W → V} (h : Observable C v) : ColumnDeterminedV C v := by
  classical
  intro e a₀ a₁
  by_contra hne
  obtain ⟨a, ha⟩ := h fun c => if c = v (C.outcome a₀ e) then a₁ else a₀
  have hae := ha e
  by_cases hm : v (C.outcome a e) = v (C.outcome a₀ e)
  · rw [if_pos hm] at hae
    exact hne (by rw [← hm, ← hae])
  · rw [if_neg hm] at hae
    exact hm (by rw [← hae])

/-- **CF-12's `&`-decomposition** (T4(b)): under CF-12's hypotheses the lazy frame is
biextensionally equivalent to the sum over cells of the observation system of the assumed
frames — through the assuming definition (T10(b)).
Source: cf-correspondence CF-12 (line 47: "`Fr(B) ≃ &_d Assume_{S_{O_d}}(Fr(B)) & Assume_{S₀}(Fr(B))`")
Kind: C
Fidelity: exact (indexed by `Option ι`, the `none` cell being `S₀`)
Hyps: none -/
theorem fr_biextEquiv_sumI_assume_obsSystem [DecidableEq ι] [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] [∀ d, Nonempty (acts d)] (obs : ι → Finset Ω)
    (B : Tree Ω ι acts K) (h1 : OneRound B) (hV : ∀ d, ∀ q ∈ fiber B d, SubtreeVeridical obs B q)
    (hdisj : ∀ d d', d ≠ d' → ∀ ℓ : B.Leaves, ¬ (world B ℓ ∈ obs d ∧ world B ℓ ∈ obs d')) :
    Fr B ≃ᵇ sumI fun c => (Fr B).assume (colCell (Fr B) (obsSystem obs) c) :=
  (observable_fr_obsSystem_of_oneRound obs B h1 hV hdisj).biextEquiv_sumI_assume
    (observable_fr_obsSystem_of_oneRound obs B h1 hV hdisj).columnDeterminedV
    ⟨fun d => Classical.arbitrary (acts d)⟩

end Cleanroom.Decision.DpCartesianFrames
