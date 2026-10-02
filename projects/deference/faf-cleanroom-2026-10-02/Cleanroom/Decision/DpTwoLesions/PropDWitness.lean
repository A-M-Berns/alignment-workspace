import Cleanroom.Decision.DpTwoLesions.PropD

/-!
# T10 — the overwrite tree as Proposition D's witness; channel 3

`overwrite P` is **not act-recorded** at any interior label (a forced run's act is not its
draw), yet both draw-recording clauses hold for every procedure (every run meets `d` once;
`O_d = ⊤`), so Proposition D(1) holds on it (`propD1_overwrite`): the identity needs no
action-veridicality. Channel 3 (dp-core-086) is `dp-core-tree`'s `screening_draw`
instantiated: on `overwrite P` the draw is independent of the state for every procedure
(`channel3_overwrite`), whereas the realized act is not (`act_not_indep_state_at_doc`, T1's
cells).
Serves [[dp-two-lesions-mandate]] T10 (witness, (d)).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace DlParams

variable (P : DlParams K)

/-- Every decision node of `overwrite P` is a root `d`-node `⟨i, none⟩`.
Source: none: infrastructure
Kind: L -/
theorem overwrite_nodes_cases (q : P.overwrite.DecNode) :
    ∃ i : Fin 3, q = (⟨i, none⟩ : P.overwrite.DecNode) := by
  unfold overwrite kBlock at q
  rcases q with ⟨i, (_ | ⟨m', j, k, e⟩)⟩
  · exact ⟨i, rfl⟩
  · exact e.elim

/-- Every leaf of `overwrite P` is some `⟨i, m', j, k, ()⟩`. Source: none: infrastructure.
Kind: L -/
theorem overwrite_leaves (ℓ : P.overwrite.Leaves) :
    ∃ (i : Fin 3) (m' : Bool) (j k : Fin 2), ℓ = ⟨i, m', j, k, ()⟩ := by
  unfold overwrite kBlock at ℓ
  rcases ℓ with ⟨i, m', j, k, ⟨⟩⟩
  exact ⟨i, m', j, k, rfl⟩

/-- The edge taken at the `d`-node `⟨i, none⟩` by the leaf `⟨i', m', j, k, ()⟩`.
Source: none: infrastructure
Kind: L -/
theorem overwrite_edgeOf (i i' : Fin 3) (m' : Bool) (j k : Fin 2) :
    edgeOf P.overwrite (⟨i, none⟩ : P.overwrite.DecNode) ⟨i', m', j, k, ()⟩ =
      if i' = i then some m' else none := by
  unfold overwrite kBlock
  by_cases h : i' = i
  · subst h; simp [edgeOf_chance, edgeOf_decision_none]
  · simp [edgeOf_chance, h]

/-- **`overwrite P` is not act-recorded** at any interior label: the forced run
`(L, drew abstain, fired)` has positive mass and its act is smoke.
Source: [[iv-design-draw-as-instrument]] §4 Definition 7′ ("The overwrite tree is draw-recorded,
not act-recorded (action-veridicality fails)"); `dp-core-tree`'s `overwrite_not_recordsFor`
Kind: N+ -/
theorem overwrite_not_recordsFor (p : K) (h0 : 0 < p) (h1 : p < 1) :
    ¬ RecordsFor dlObs dlActEv (procBoolK p h0.le h1.le) P.overwrite () := by
  intro hrec
  have hbase : 0 < P.ρ * (1 - p) * P.δL :=
    mul_pos (mul_pos P.ρ_pos (sub_pos.mpr h1)) P.δL_pos
  have hpos : ∃ k : Fin 2,
      0 < leafLaw (procBoolK p h0.le h1.le) P.overwrite ⟨0, false, 0, k, ()⟩ := by
    rcases (P.gam_nonneg 0).lt_or_eq with hγ | hγ
    · refine ⟨0, ?_⟩
      rw [overwrite_leafLaw]
      simp only [stateW_zero, procBoolK_w, Bool.false_eq_true, if_false, force_zero, gam_zero]
      simp only [if_true]
      rw [gam_zero] at hγ
      exact mul_pos hbase hγ
    · refine ⟨1, ?_⟩
      rw [overwrite_leafLaw]
      simp only [stateW_zero, procBoolK_w, Bool.false_eq_true, if_false, force_zero, gam_zero]
      simp only [if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
      rw [gam_zero] at hγ
      rw [← hγ]
      simpa using hbase
  obtain ⟨k, hk⟩ := hpos
  obtain ⟨-, h⟩ := hrec ⟨0, false, 0, k, ()⟩ hk (Finset.mem_univ _)
  have he : edgeOf P.overwrite (⟨0, none⟩ : P.overwrite.DecNode) ⟨0, false, 0, k, ()⟩ =
      some false := by rw [P.overwrite_edgeOf]; simp
  obtain ⟨-, hav, -⟩ := h ⟨0, none⟩ rfl false he
  rw [P.overwrite_world] at hav
  simp [dlActEv] at hav

/-- **Both draw-recording clauses hold on `overwrite P` for every procedure**: every run meets
`d` exactly once, and with `O_d = ⊤` every node is subtree-veridical.
Source: [[iv-design-draw-as-instrument]] §4 Definition 7′ ("The overwrite tree is draw-recorded")
Kind: P
Fidelity: exact
Hyps: none -/
theorem overwrite_drawRecorded (C : Proc Unit (fun _ => Bool) K) :
    (∀ ℓ, 0 < leafLaw C P.overwrite ℓ → world P.overwrite ℓ ∈ dlObs () →
      count () P.overwrite ℓ ≤ 1) ∧
    (∀ ℓ, 0 < leafLaw C P.overwrite ℓ → world P.overwrite ℓ ∈ dlObs () →
      ∀ q, pt P.overwrite q = () → (edgeOf P.overwrite q ℓ).isSome →
        SubtreeVeridical dlObs P.overwrite q) := by
  constructor
  · intro ℓ _ _; rw [P.overwrite_count]
  · intro ℓ _ _ q _ _ ℓ' _; exact Finset.mem_univ _

/-- **Proposition D(1) on the overwrite tree, at every label**: the identity holds although
the tree is not act-recorded (the N+ witness of `propD1`; the ITT-on-cancer `0` it yields is
`dissolve_draw` on the lifted tree).
Source: [[iv-design-draw-as-instrument]] §4 Proposition D ("which is what lets it hold on the
overwrite tree"); mandate T10 witness
Kind: N+
Fidelity: exact -/
theorem propD1_overwrite (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) (a : Bool) (X : Finset DlW) :
    mass (procBoolK p h0 h1) P.overwrite
        (worldEv P.overwrite X ∩ drew () a P.overwrite ∩ worldEv P.overwrite (dlObs ())) *
        (∑ q ∈ activeFiber dlObs (procBoolK p h0 h1) P.overwrite (), reach (procBoolK p h0 h1)
          P.overwrite q) =
      (∑ q ∈ activeFiber dlObs (procBoolK p h0 h1) P.overwrite (),
        if pt P.overwrite q = () then
          forcedBelowEv (procBoolK p h0 h1) P.overwrite q a X else 0) *
        mass (procBoolK p h0 h1) P.overwrite (drew () a P.overwrite ∩ worldEv P.overwrite (dlObs ())) := by
  have h := propD1 dlObs (procBoolK p h0 h1) P.overwrite () (P.overwrite_drawRecorded _).1
    (P.overwrite_drawRecorded _).2 a X
  simpa only [eq_rec_constant, dite_eq_ite] using h

/-- The state is decided at every `d`-node of `overwrite P`. Source: v2 Lemma 3 ("pre-query
events"). Kind: L -/
theorem overwrite_decided_state (q : P.overwrite.DecNode) (s : DlState) :
    DecidedAt P.overwrite q (evState s) := by
  obtain ⟨i, rfl⟩ := P.overwrite_nodes_cases q
  by_cases h : stateOf i = s
  · left
    intro ℓ hℓ
    obtain ⟨i', m', j, k, rfl⟩ := P.overwrite_leaves ℓ
    rw [mem_leavesBelow, P.overwrite_edgeOf] at hℓ
    by_cases hi : i' = i
    · subst hi; rw [P.overwrite_world, mem_evState]; exact h
    · simp [hi] at hℓ
  · right
    intro ℓ hℓ
    obtain ⟨i', m', j, k, rfl⟩ := P.overwrite_leaves ℓ
    rw [mem_leavesBelow, P.overwrite_edgeOf] at hℓ
    by_cases hi : i' = i
    · subst hi; rw [P.overwrite_world, mem_evState]; exact h
    · simp [hi] at hℓ

/-- **Channel 3 (dp-core-086) on the overwrite tree** — `screening_draw` instantiated: for every
procedure and state, the draw is independent of the state on the consulting runs (all of them):
`μ(state ∧ drew a)·μ(occ) = μ(state ∧ occ)·μ(drew a)`.
Source: [[smoking-lesion-exploration-and-boundaries]] §4 (channel 3: "a draw correlated with an
upstream variable is not a Definition-4 procedure"); dp-core-086 ("channel 3 as a theorem");
`dp-core-tree`'s `screening_draw`
Kind: C
Fidelity: exact (run level, `O_d = ⊤`)
Hyps: none -/
theorem channel3_overwrite (C : Proc Unit (fun _ => Bool) K) (s : DlState) (a : Bool) :
    mass C P.overwrite (worldEv P.overwrite (evState s) ∩ drew () a P.overwrite) *
        mass C P.overwrite (occ () P.overwrite) =
      mass C P.overwrite (worldEv P.overwrite (evState s) ∩ occ () P.overwrite) *
        mass C P.overwrite (drew () a P.overwrite) :=
  screening_draw (fun ℓ _ => by rw [P.overwrite_count])
    (fun ℓ _ q _ _ => P.overwrite_decided_state q s) a

/-- **The realized act is not independent of the state** (contrast to channel 3): at the doc's
parameters with `δ = 1/100` and `p = ½`, `ν(L ∧ smoke) = 101/1000 ≠ 1/5 · 251/500 = ν(L)·ν(smoke)`.
Source: [[two-lesions-doc-2026-09-18]] §3 (the correlation between act and lesion);
`dp-core-tree`'s `overwrite_m_not_indep_lesion`
Kind: N+ -/
theorem act_not_indep_state_at_doc :
    (docP (1/100 : ℚ) (by norm_num) (by norm_num)).nuP (1/2) (evState .L ∩ evAct true) ≠
      (docP (1/100 : ℚ) (by norm_num) (by norm_num)).nuP (1/2) (evState .L) *
        (docP (1/100 : ℚ) (by norm_num) (by norm_num)).nuP (1/2) evSmoke := by
  rw [nuP_cell _ _ (by norm_num) (by norm_num), (nuP_state _ _ (by norm_num) (by norm_num)).1,
    nuP_smoke _ _ (by norm_num) (by norm_num)]
  simp only [cellMass, kappa, docP]
  norm_num

end DlParams

end Cleanroom.Decision.DpTwoLesions
