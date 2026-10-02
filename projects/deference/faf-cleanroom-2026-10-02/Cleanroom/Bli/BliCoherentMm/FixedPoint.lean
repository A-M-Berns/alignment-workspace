import Cleanroom.Bli.BliCoherentMm.Worlds
import Cleanroom.Bli.BliCoherentMm.AttemptA.FixedPoint
import Cleanroom.Bli.BliCoherentMm.AttemptB.FixedPoint

/-!
# `bli-coherent-mm` · FixedPoint (reconciled): T1, the coherent fixed point (Soto's Theorem 2)

**Of record: attempt A's headline** `coherent_fixed_point` — for a day-`n` strategy, any prior
history, a stage `D` and an atom bound `B` with a `D`-consistent finite world, a real world
measure on `FiniteWorld B` supported on the `D`-consistent worlds makes the strategy's value
`≤ 0` **in every `D`-consistent world over `B` atoms** when day `n` is priced at its marginals.
It is of record because it is the stronger statement: it needs **no atom bound** (findings F13;
attempt B's headline carries `hB` on `mentionedSet T ∪ D`), and any prior `History` (attempt
B's is at `beliefHistory past`). The mandate's exact shape — `beliefHistory past`, `hB` on
`mentionedSet T ∪ D`, both the finite-world and the `PCWorld` conclusions — is the corollary
`coherent_fixed_point_mandate`, and attempt B's clip-and-normalise route proves that same
corollary independently (`coherent_fixed_point_viaB`): the two attempts agree on T1.

**The abstract lemma of record is attempt B's** `coherent_fixed_point_abstract` (continuity
*on the simplex* suffices), the more general statement; attempt A's Nash-map lemma (continuity
of each coordinate on the whole space) is kept as the independent route
(`coherent_fixed_point_abstract_viaNash`). Both are Brouwer on FAF's `stdSimplex_hasFPP`,
neither uses Kakutani. The zero-expected-value identity is **proved** for the instance in both
attempts (`sum_mul_value_worldHistory`, `sum_mul_value_update_viaB`), from `∑ p = 1` alone.

Sources: [[bli-coherent-mm-mandate]] T1; Soto PDF 05 Thm 2 (bli-soto-a-044); [[bli-program]]
§3.8, §4 row M1.
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## The abstract lemma -/

/-- **T1, abstract lemma (of record; Soto's Theorem 2, finite form).** For a nonempty finite `ι`
and `G : (ι → ℝ) → ι → ℝ` continuous on the simplex with `∑ u, p u * G p u = 0` there, some
`p* ∈ stdSimplex ℝ ι` has `G p* u ≤ 0` for every `u`. Attempt B's clip-and-normalise map and
FAF's Brouwer (`stdSimplex_hasFPP`).
Source: [[bli-coherent-mm-mandate]] T1 (abstract lemma); Soto PDF 05 Thm 2
Kind: P
Fidelity: exact (the identity is a hypothesis of the abstract lemma only; derived at the instance)
Hyps: (a) `hG`, `hid` — the lemma's own; the headline discharges both -/
theorem coherent_fixed_point_abstract {ι : Type} [Fintype ι] [Nonempty ι]
    (G : (ι → ℝ) → ι → ℝ) (hG : ContinuousOn G (stdSimplex ℝ ι))
    (hid : ∀ p ∈ stdSimplex ℝ ι, ∑ u, p u * G p u = 0) :
    ∃ p ∈ stdSimplex ℝ ι, ∀ u, G p u ≤ 0 :=
  AttemptB.coherent_fixed_point_abstract G hG hid

/-- **T1, abstract lemma by Nash's map** (attempt A's independent route; continuity of each
coordinate on the whole space, a special case of the record's hypothesis).
Source: [[bli-coherent-mm-mandate]] T1 (abstract lemma), §Attempt angles (A)
Kind: P
Fidelity: exact
Hyps: (a) `hG`, `hid` -/
theorem coherent_fixed_point_abstract_viaNash {ι : Type} [Fintype ι] [Nonempty ι]
    (G : (ι → ℝ) → ι → ℝ) (hG : ∀ u, Continuous fun p => G p u)
    (hid : ∀ p ∈ stdSimplex ℝ ι, ∑ u, p u * G p u = 0) :
    ∃ p ∈ stdSimplex ℝ ι, ∀ u, G p u ≤ 0 :=
  AttemptA.coherent_fixed_point_abstract G hG hid

/-! ## The instance: world tables and histories -/

/-- **The day-`n` price table of a real weight vector** `∑ u, p u * payout_u φ`.
Source: [[bli-coherent-mm-mandate]] T1 (`V_p`)
Kind: D
Fidelity: exact -/
noncomputable abbrev worldTable {B : ℕ} (p : FiniteWorld B → ℝ) (φ : Sentence) : ℝ :=
  AttemptA.worldTable p φ

/-- **The history with day `n` priced by `p`**: `V_p := Function.update prior n (worldTable p)`.
Source: [[bli-coherent-mm-mandate]] T1 (`V_p`)
Kind: D
Fidelity: exact -/
noncomputable abbrev worldHistory (prior : History) (n : ℕ) {B : ℕ} (p : FiniteWorld B → ℝ) :
    History :=
  AttemptA.worldHistory prior n p

/-- The record's `V_p` over `beliefHistory past` is the mandate's displayed history (attempt
B's `fixedHistory`).
Source: [[bli-coherent-mm-mandate]] T1 (`V_p`)
Kind: L
Fidelity: n/a -/
theorem worldHistory_eq_update (past : List RationalBeliefState) (n : ℕ) {B : ℕ}
    (p : FiniteWorld B → ℝ) :
    worldHistory (beliefHistory past) n p =
      Function.update (beliefHistory past) n (fun φ => ∑ u, p u * (worldOf u).payout φ) := by
  unfold worldHistory AttemptA.worldHistory AttemptA.worldTable
  congr 1
  funext φ
  apply Finset.sum_congr rfl
  intro u _
  rw [← AttemptA.payoutReal_eq_payout]
  rfl

/-- **The zero-expected-value identity, proved** (attempt A): for a weight vector of total
mass one, the `p`-expectation over worlds of a strategy's value on `V_p` is zero, because
`∑ u, p u * payout_u φ = V_p n φ` for every traded `φ`. Only `∑ p = 1` is used (findings F15).
Source: [[bli-coherent-mm-mandate]] T1 ("the identity … is proved, not assumed")
Kind: P
Fidelity: exact -/
theorem sum_mul_value_worldHistory {n : ℕ} (T : Strategy n) (prior : History) {B : ℕ}
    (p : FiniteWorld B → ℝ) (hp : ∑ u, p u = 1) :
    ∑ u, p u * T.value (worldHistory prior n p) (AttemptA.payoutReal u) = 0 :=
  AttemptA.sum_mul_value_worldHistory T prior p hp

/-- **The identity, attempt B's independent proof**, in the mandate's displayed form.
Source: [[bli-coherent-mm-mandate]] T1; §Deliverables (cross-check)
Kind: P
Fidelity: exact -/
theorem sum_mul_value_update_viaB {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    {B : ℕ} (p : FiniteWorld B → ℝ) (hp : ∑ u, p u = 1) :
    ∑ u, p u * T.value (Function.update (beliefHistory past) n
      (fun φ => ∑ u, p u * (worldOf u).payout φ)) (worldOf u).payout = 0 :=
  AttemptB.sum_worldValue_eq_zero T past p hp

/-! ## T1, the headline over FAF's objects -/

/-- **T1 (of record, headline, M1). The coherent fixed point.** For a day-`n` strategy `T`, a
prior history, a stage `D` and an atom bound `B` with a `D`-consistent finite world, there is a
real world measure `p` on `FiniteWorld B` — nonnegative, total mass one, supported on the
`D`-consistent worlds — such that with day `n` priced by `p`'s marginals, `T`'s value is `≤ 0`
**in every `D`-consistent world over `B` atoms**. No atom bound is needed in this form. Not
FAF's `fixed_point_lemma` (a per-sentence valuation with no measure); not a bound over all
Boolean tables on the support (false for coherent prices, `Contrast.lean`).
Source: [[bli-coherent-mm-mandate]] T1; Soto PDF 05 Thm 2; [[bli-program]] §3.8, §4 row M1
Kind: P
Fidelity: exact (stronger than the mandate's shape: any prior `History`, no `hB`)
Hyps: (a) `hW` — the simplex is nonempty (from `paperDP_hworld` at the witness); the identity
and the continuity are derived -/
theorem coherent_fixed_point {n : ℕ} (T : Strategy n) (prior : History) (D : Finset Sentence)
    (B : ℕ) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) :
    ∃ p : FiniteWorld B → ℝ, (∀ u, 0 ≤ p u) ∧ ∑ u, p u = 1 ∧
      (∀ u, p u ≠ 0 → (worldOf u).ConsistentWith D) ∧
      ∀ u ∈ WD D B, T.value (worldHistory prior n p) (AttemptA.payoutReal u) ≤ 0 :=
  AttemptA.coherent_fixed_point T prior D B hW

/-- **T1, `PCWorld` form (of record).** With every traded and every stage sentence within the
atom bound (`T.support ∪ D` suffices), the fixed point's value is `≤ 0` in every `PCWorld`
consistent with `D`.
Source: [[bli-coherent-mm-mandate]] T1 (`PCWorld` form)
Kind: C
Fidelity: exact (`hB` on `T.support ∪ D`, weaker than the mandate's `mentionedSet T ∪ D`)
Hyps: (a) `hB`, `hW` -/
theorem coherent_fixed_point_pcWorld {n : ℕ} (T : Strategy n) (prior : History)
    (D : Finset Sentence) (B : ℕ) (hB : ∀ φ ∈ T.support ∪ D, atomBound φ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) :
    ∃ p : FiniteWorld B → ℝ, (∀ u, 0 ≤ p u) ∧ ∑ u, p u = 1 ∧
      (∀ u, p u ≠ 0 → (worldOf u).ConsistentWith D) ∧
      ∀ v : PCWorld, v.ConsistentWith D → T.value (worldHistory prior n p) v.payout ≤ 0 :=
  AttemptA.coherent_fixed_point_pcWorld T prior D B hB hW

/-- **T1 in the mandate's exact shape** (both attempts' common ground): over `beliefHistory
past`, with `hB` on `mentionedSet T ∪ D`, a real world measure `p` on the `D`-consistent worlds
such that, with `V_p := Function.update (beliefHistory past) n (fun φ => ∑ u, p u * payout_u φ)`,
`T.value V_p payout_u ≤ 0` for every `u ∈ WD D B` and `T.value V_p v.payout ≤ 0` for every
`PCWorld` `v` consistent with `D`. Derived from the record's `coherent_fixed_point`.
Source: [[bli-coherent-mm-mandate]] T1 (the displayed statement)
Kind: C
Fidelity: exact
Hyps: (a) `hB` (computed in witnesses and by `B n` in the recursion), `hW` -/
theorem coherent_fixed_point_mandate {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) :
    ∃ p : FiniteWorld B → ℝ, (∀ u, 0 ≤ p u) ∧ ∑ u, p u = 1 ∧
      (∀ u, p u ≠ 0 → (worldOf u).ConsistentWith D) ∧
      (∀ u ∈ WD D B, T.value (Function.update (beliefHistory past) n
        (fun φ => ∑ u, p u * (worldOf u).payout φ)) (worldOf u).payout ≤ 0) ∧
      ∀ v : PCWorld, v.ConsistentWith D → T.value (Function.update (beliefHistory past) n
        (fun φ => ∑ u, p u * (worldOf u).payout φ)) v.payout ≤ 0 := by
  obtain ⟨p, h0, h1, hD, hval⟩ := coherent_fixed_point_pcWorld T (beliefHistory past) D B
    (fun φ hφ => hB φ (by
      rcases Finset.mem_union.mp hφ with h | h
      · exact Finset.mem_union_left _ (support_subset_mentionedSet T h)
      · exact Finset.mem_union_right _ h)) hW
  refine ⟨p, h0, h1, hD, fun u hu => ?_, fun v hv => ?_⟩
  · have h := hval (worldOf u) (mem_WD.mp hu)
    rwa [worldHistory_eq_update] at h
  · have h := hval v hv
    rwa [worldHistory_eq_update] at h

/-- **T1 in the mandate's shape, attempt B's independent proof** (clip-and-normalise map; the
same statement as `coherent_fixed_point_mandate`, reached by the other route — the two attempts
agree on T1).
Source: [[bli-coherent-mm-mandate]] T1, §Attempt angles (B); §Deliverables (cross-check)
Kind: P
Fidelity: exact
Hyps: (a) `hB`, `hW` -/
theorem coherent_fixed_point_viaB {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) :
    ∃ p : FiniteWorld B → ℝ, (∀ u, 0 ≤ p u) ∧ ∑ u, p u = 1 ∧
      (∀ u, p u ≠ 0 → (worldOf u).ConsistentWith D) ∧
      (∀ u ∈ WD D B, T.value (Function.update (beliefHistory past) n
        (fun φ => ∑ u, p u * (worldOf u).payout φ)) (worldOf u).payout ≤ 0) ∧
      ∀ v : PCWorld, v.ConsistentWith D → T.value (Function.update (beliefHistory past) n
        (fun φ => ∑ u, p u * (worldOf u).payout φ)) v.payout ≤ 0 := by
  obtain ⟨p, hmeas, hfin, hpc⟩ := AttemptB.coherent_fixed_point T past D B hB hW
  obtain ⟨h0, h1, hD⟩ := hmeas
  refine ⟨p, h0, h1, hD, fun u hu => hfin u ?_, hpc⟩
  rw [WD_eq_attemptB] at hu
  exact hu

end Cleanroom.Bli.BliCoherentMm
