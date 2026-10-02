import Cleanroom.Bli.BliRvcUi.Rvc.Antitone
import Cleanroom.Bli.BliRvcUi.Rvc.Grid
import Cleanroom.Bli.BliFound.Constraints

/-!
# `bli-rvc-ui` · Rvc/Process: real-value coherence relative to a deductive process (T2.4, T1.2 bridge)

**T2.4 (M8 verbatim).** If the base `Q` is propositionally coherent on the small sentences relative
to its process (`bli-found`'s `D_PC Q DP`), the threshold atoms of `X` on `R` are day-`n` small,
and every world consistent with `DP.D n` holds the monotonicity and range facts, then `Q n` is
`RVC_B` on `R`. So D-RVC(B) *is* D-PC on the threshold atoms plus the process's facts.

**Honesty clause (mandate T2.4).** At a finite stage the monotonicity facts of a quote LUV are
**not** in general entailed by `(paperDP T).D n` — they hold in completed-theory worlds only
(`quoteLuv_valuesAt`, `Rvc/Paper.lean`). So the third hypothesis is a disclosed **(c)** at finite
days and becomes **(a)** only in the limit (T2.3, `Rvc/LimitB.lean`). It is not derived from
`quoteLuv_valuesAt` and called (a).

**T1.2's bridge to D-PC.** Over any `Constraints.CoherentOn D A V` whose consistent worlds all
value `Z = X + Y` and whose atom set covers the grid thresholds, `RVC_E_eps V k X Y Z (3/k)`; at
`k := n + 1` and `D := DP.D n` this is the day-`n` form for `LUV.expect`.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset Cleanroom.Bli.BliFound

/-! ## The antitone characterization of a mixture of fact-holding worlds -/

/-- **A mixture of worlds holding the monotonicity and range facts has an antitone threshold
profile.**
Source: mandate T2.4 route
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem thresholdAntitone_of_mixture {ι : Type*} [Fintype ι] {V : Sentence → ℝ} {W : ι → PCWorld}
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {X : LUV} {R : Finset ℚ}
    (hfacts : ∀ i, (W i).ConsistentWith (monoFacts X R ∪ rangeFacts X R))
    (hV : ∀ r ∈ R, V (X.gt r) = ∑ i, w i * (W i).payout (X.gt r)) :
    ThresholdAntitone V X R := by
  refine ⟨fun r hr => ?_, fun r hr r' hr' hlt => ?_, fun r hr hlt => ?_, fun r hr hle => ?_⟩
  · rw [hV r hr]
    constructor
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (payout_mem_Icc _ _).1
    · calc ∑ i, w i * (W i).payout (X.gt r) ≤ ∑ i, w i :=
            Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hw0 i) (payout_mem_Icc _ _).2
        _ = 1 := hw1
  · rw [hV r hr, hV r' hr']
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw0 i)
    have himp : (W i).Holds (X.gt r) → (W i).Holds (X.gt r') :=
      hfacts i _ (Finset.mem_union_left _ (monoFact_mem hr hr' hlt))
    by_cases h : (W i).Holds (X.gt r)
    · rw [payout_of_holds h, payout_of_holds (himp h)]
    · rw [payout_of_not_holds h]
      exact (payout_mem_Icc _ _).1
  · rw [hV r hr]
    calc ∑ i, w i * (W i).payout (X.gt r) = ∑ i, w i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [payout_of_holds (hfacts i _ (Finset.mem_union_right _ (rangeFact_neg_mem hr hlt))),
            mul_one]
      _ = 1 := hw1
  · rw [hV r hr]
    apply Finset.sum_eq_zero
    intro i _
    have hn : ¬ (W i).Holds (X.gt r) :=
      (PCWorld.holds_neg _ _).mp (hfacts i _ (Finset.mem_union_right _ (rangeFact_one_mem hr hle)))
    rw [payout_of_not_holds hn, mul_zero]

/-- The atom codes of a small sentence lie in the day's atom set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomCodes_subset_of_mem_smallSet {n : ℕ} {φ : Sentence} (h : φ ∈ smallSet n) :
    sentenceAtomCodes φ ⊆ (smallSet n).biUnion sentenceAtomCodes :=
  Finset.subset_biUnion_of_mem sentenceAtomCodes h

/-- **T2.4 — D-RVC(B) from D-PC** (M8 verbatim): a base coherent on the small sentences relative to
its process is `RVC_B` on every threshold set whose atoms are day-small, provided every world
consistent with the day's stage holds the monotonicity and range facts.
Source: [[bli-program]] M8; [[bli-program-desiderata]] D-RVC(B), D-PC; mandate T2.4
Kind: C
Fidelity: exact
Hyps: (c) `hfacts` — at a finite stage the monotonicity/range facts of a quote LUV are not in
general entailed by `(paperDP T).D n` (they hold in completed-theory worlds only); this is a
disclosed modelling hypothesis at finite days, and (a) only in the limit (T2.3). -/
theorem rvcB_of_D_PC {Q : History} {DP : DeductiveProcess} (hPC : D_PC Q DP) (n : ℕ) {X : LUV}
    {R : Finset ℚ} (hsmall : thresholdAtoms X R ⊆ smallSet n)
    (hfacts : ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      v.ConsistentWith (monoFacts X R ∪ rangeFacts X R)) :
    RVC_B (Q n) X R := by
  obtain ⟨k, W, w, hW, hw0, hw1, hQ⟩ := hPC n
  refine rvcB_iff_antitone.mpr (thresholdAntitone_of_mixture hw0 hw1 (fun i => hfacts _ (hW i))
    fun r hr => ?_)
  exact hQ _ (atomCodes_subset_of_mem_smallSet (hsmall (mem_thresholdAtoms.mpr ⟨r, hr, rfl⟩)))

/-! ## T1.2 relative to a stage: the bridge to D-PC -/

/-- **ε-additivity over a stage-coherent valuation**: if `V` is coherent on the atoms `A` relative
to `D` (`bli-found`'s `Constraints.CoherentOn`), every world consistent with `D` values `Z = X + Y`,
and the grid thresholds of `X`, `Y`, `Z` have their atoms in `A`, then `RVC_E_eps V k X Y Z (3/k)`.
Source: mandate T1.2 (the bridge to `D_PC`); [[bli-program-desiderata]] D-RVC(E_ε)
Kind: C
Fidelity: exact (the ε is the mesh)
Hyps: (a) -/
theorem rvcE_eps_of_coherentOn {D : Finset Sentence} {A : Finset ℕ} {V : Sentence → ℝ}
    (h : CoherentOn D A V) {k : ℕ} (hk : 0 < k) {X Y Z : LUV}
    (hsum : ∀ v : PCWorld, v.ConsistentWith D → SumValued v X Y Z)
    (hX : ∀ i ∈ Finset.range k, sentenceAtomCodes (X.gt ((i : ℚ) / (k : ℚ))) ⊆ A)
    (hY : ∀ i ∈ Finset.range k, sentenceAtomCodes (Y.gt ((i : ℚ) / (k : ℚ))) ⊆ A)
    (hZ : ∀ i ∈ Finset.range k, sentenceAtomCodes (Z.gt ((i : ℚ) / (k : ℚ))) ⊆ A) :
    RVC_E_eps V k X Y Z (3 / k) := by
  obtain ⟨m, W, w, hW, hw0, hw1, hV⟩ := h
  exact rvcE_eps_of_worldMixture hk hw0 hw1 (fun i => hsum _ (hW i))
    (fun i hi => hV _ (hX i hi)) (fun i hi => hV _ (hY i hi)) (fun i hi => hV _ (hZ i hi))

/-- **T1.2 at day `n` over a D-PC base**: `|𝔼ₙ(X) + 𝔼ₙ(Y) − 𝔼ₙ(Z)| ≤ 3/(n+1)` for FAF's day-`n`
expectation `LUV.expect`, when the day's stage forces `Z = X + Y` and the grid thresholds are
day-small.
Source: mandate T1.2; [[bli-program-desiderata]] I9 ("the ε-form is the satisfiable one")
Kind: C
Fidelity: exact
Hyps: (c) `hsum` — that the day-`n` stage forces the sum relation in every consistent world is a
modelling hypothesis at finite days (for quote LUVs it holds in completed-theory worlds) -/
theorem expect_eps_of_D_PC {Q : History} {DP : DeductiveProcess} (hPC : D_PC Q DP) (n : ℕ)
    {X Y Z : LUV} (hsum : ∀ v : PCWorld, v.ConsistentWith (DP.D n) → SumValued v X Y Z)
    (hX : ∀ i ∈ Finset.range (n + 1), X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) ∈ smallSet n)
    (hY : ∀ i ∈ Finset.range (n + 1), Y.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) ∈ smallSet n)
    (hZ : ∀ i ∈ Finset.range (n + 1), Z.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) ∈ smallSet n) :
    |X.expect Q n + Y.expect Q n - Z.expect Q n| ≤ 3 / ((n + 1 : ℕ) : ℝ) :=
  rvcE_eps_of_coherentOn (hPC n) (Nat.succ_pos n) hsum
    (fun i hi => atomCodes_subset_of_mem_smallSet (hX i hi))
    (fun i hi => atomCodes_subset_of_mem_smallSet (hY i hi))
    (fun i hi => atomCodes_subset_of_mem_smallSet (hZ i hi))

end Cleanroom.Bli.BliRvcUi
