import Cleanroom.Bli.BliExactBase.Defs

/-!
# `bli-exact-base` — K7b: the D-ND mixing lemma

A **complete family** of stage-consistent worlds for a finite atom set `A` relative to a finite
stage `D` (`CompleteFor`: every pattern on `A` realized by some `D`-consistent world is realized
by a member) mixed with strictly positive weights gives a price assignment that is (i) a stage
mixture — `CoherentOn D A` — and (ii) **non-dogmatic on the algebra over `A`**: every sentence
with atoms in `A` is decided true by `D`, decided false by `D`, or priced strictly inside `(0,1)`
(`mixRat_trichotomy`, Kind `P`). "Decided" is semantic — all `D`-consistent worlds agree — so a
sentence decided by the completed theory but not yet by the stage counts as undecided and gets an
interior price, which is what `D_ND` (relative to the stage) asks.

Existence (`exists_completeFor`, Kind `P`): the finitely many assignments to the first `B` atoms
(`FiniteWorld B`, with `B` above `A` and above every atom of `D`) that are `D`-consistent, through
`bli-finite`'s `worldOf` and `holds_worldOf_restrict`; nonempty when `D` has a consistent world.
`exists_mixture` packages the uniform mixture over such a family: rational values in `[0,1]`,
coherence, the trichotomy. A free atom (mentioned by no sentence of `D`) is undecided at `D`
(`free_atom_undecided`), which is what makes the segment tables' interior prices exhibitable.

Nothing here is enumerated: `smallSet n` has more than `2^(2^n)` members and the families are
existential over `Fin k`; the tables of `Tables.lean` are data exhibited by a choice.
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliLinkageB
open LogicalInduction.BoolPCWorld (atomBound FiniteWorld)

/-! ## Rational payouts -/

/-- The rational payout is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutRat_nonneg' (v : PCWorld) (φ : Sentence) : 0 ≤ v.payoutRat φ := by
  unfold PCWorld.payoutRat; split_ifs <;> norm_num

/-- The rational payout is at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutRat_le_one' (v : PCWorld) (φ : Sentence) : v.payoutRat φ ≤ 1 := by
  unfold PCWorld.payoutRat; split_ifs <;> norm_num

/-- A held sentence pays `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutRat_of_holds' {v : PCWorld} {φ : Sentence} (h : v.Holds φ) : v.payoutRat φ = 1 := by
  unfold PCWorld.payoutRat; rw [if_pos h]

/-- A sentence not held pays `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutRat_of_not_holds' {v : PCWorld} {φ : Sentence} (h : ¬ v.Holds φ) :
    v.payoutRat φ = 0 := by
  unfold PCWorld.payoutRat; rw [if_neg h]

/-! ## Complete families and their mixtures -/

/-- **A complete family for `A` relative to `D`**: every assignment to the atoms `A` that some
`D`-consistent world realizes is realized by some member of the family.
Source: mandate § 2 ("complete for `A` relative to `D`")
Kind: D
Fidelity: exact -/
def CompleteFor (D : Finset Sentence) (A : Finset ℕ) {k : ℕ} (W : Fin k → PCWorld) : Prop :=
  ∀ v : PCWorld, v.ConsistentWith D → ∃ i, ∀ a ∈ A, (W i a ↔ v a)

/-- **The rational mixture** of a finite world family with rational weights.
Source: mandate § 2 (`p φ := ∑ i, w i * (W i).payout φ`)
Kind: D
Fidelity: exact -/
noncomputable def mixRat {k : ℕ} (W : Fin k → PCWorld) (w : Fin k → ℚ) (φ : Sentence) : ℚ :=
  ∑ i, w i * (W i).payoutRat φ

/-- The real cast of the rational mixture is the real mixture.
Source: none: infrastructure (FAF `PCWorld.payout_eq_ratCast`)
Kind: L
Fidelity: n/a -/
lemma mixRat_cast {k : ℕ} (W : Fin k → PCWorld) (w : Fin k → ℚ) (φ : Sentence) :
    ((mixRat W w φ : ℚ) : ℝ) = ∑ i, (w i : ℝ) * (W i).payout φ := by
  simp [mixRat, PCWorld.payout_eq_ratCast]

/-- A mixture with nonnegative weights summing to one takes values in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mixRat_mem_Icc {k : ℕ} {W : Fin k → PCWorld} {w : Fin k → ℚ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (φ : Sentence) : 0 ≤ mixRat W w φ ∧ mixRat W w φ ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (payoutRat_nonneg' _ _)
  · calc mixRat W w φ ≤ ∑ i, w i * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (payoutRat_le_one' _ _) (hw0 i)
      _ = 1 := by simp [hw1]

/-- **The mixture is a stage mixture** on every algebra: `CoherentOn D A` for every `A`.
Source: mandate § 2 (the mixing lemma, coherence clause)
Kind: L
Fidelity: exact -/
theorem mixRat_coherentOn {D : Finset Sentence} (A : Finset ℕ) {k : ℕ} {W : Fin k → PCWorld}
    {w : Fin k → ℚ} (hW : ∀ i, (W i).ConsistentWith D) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) : CoherentOn D A (fun φ => (mixRat W w φ : ℝ)) :=
  ⟨k, W, fun i => (w i : ℝ), hW, fun i => show (0 : ℝ) ≤ (w i : ℝ) from Rat.cast_nonneg.2 (hw0 i),
    show ∑ i, (w i : ℝ) = 1 by rw [← Rat.cast_sum, hw1, Rat.cast_one],
    fun φ _ => mixRat_cast W w φ⟩

/-- **The D-ND mixing lemma.** A complete family for `A` relative to `D`, mixed with strictly
positive weights summing to one, prices every sentence with atoms in `A` either at a decided
value — all `D`-consistent worlds hold it, or none does — or strictly inside `(0, 1)`: if some
consistent world holds `φ` and some does not, the family realizes both patterns on `A`
(`holds_congr_atomCodes`), so a positive weight sits on each side.
Source: [[bli-program]] §2.6 (`D_ND`); mandate § 2 ("the mixing lemma (P, general)")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem mixRat_trichotomy {D : Finset Sentence} {A : Finset ℕ} {k : ℕ} {W : Fin k → PCWorld}
    {w : Fin k → ℚ} (hw0 : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hc : CompleteFor D A W)
    {φ : Sentence} (hφ : sentenceAtomCodes φ ⊆ A) :
    (∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) ∨
    (∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) ∨
    (0 < mixRat W w φ ∧ mixRat W w φ < 1) := by
  by_cases h1 : ∀ v : PCWorld, v.ConsistentWith D → v.Holds φ
  · exact Or.inl h1
  by_cases h2 : ∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  push Not at h1 h2
  obtain ⟨v, hv, hvφ⟩ := h1
  obtain ⟨v', hv', hv'φ⟩ := h2
  obtain ⟨i, hi⟩ := hc v hv
  obtain ⟨j, hj⟩ := hc v' hv'
  have hiφ : ¬ (W i).Holds φ := fun h =>
    hvφ ((PCWorld.holds_congr_atomCodes φ fun a ha => hi a (hφ ha)).1 h)
  have hjφ : (W j).Holds φ :=
    (PCWorld.holds_congr_atomCodes φ fun a ha => hj a (hφ ha)).2 hv'φ
  constructor
  · have hle : w j * (W j).payoutRat φ ≤ mixRat W w φ :=
      Finset.single_le_sum (f := fun i => w i * (W i).payoutRat φ)
        (fun i _ => mul_nonneg (hw0 i).le (payoutRat_nonneg' _ _)) (Finset.mem_univ j)
    rw [payoutRat_of_holds' hjφ, mul_one] at hle
    exact lt_of_lt_of_le (hw0 j) hle
  · have hsum : 1 - mixRat W w φ = ∑ i', w i' * (1 - (W i').payoutRat φ) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hw1, mixRat]
    have hle : w i * (1 - (W i).payoutRat φ) ≤ ∑ i', w i' * (1 - (W i').payoutRat φ) :=
      Finset.single_le_sum (f := fun i' => w i' * (1 - (W i').payoutRat φ))
        (fun i' _ => mul_nonneg (hw0 i').le (sub_nonneg.2 (payoutRat_le_one' _ _)))
        (Finset.mem_univ i)
    rw [payoutRat_of_not_holds' hiφ, sub_zero, mul_one] at hle
    linarith [hw0 i]

/-! ## Existence of a complete family -/

/-- **A complete family exists** whenever the stage has a consistent world: the `D`-consistent
assignments to the first `B` atoms, `B` above every atom of `A` and of `D`, read as worlds through
`bli-finite`'s `worldOf`; the restriction of any `D`-consistent world to `B` atoms is one of them
and agrees with it on `A` (`holds_worldOf_restrict`).
Source: mandate § 2 ("existence of a complete family (P)"); bli-finite `worldOf`, `holds_worldOf_restrict`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem exists_completeFor (D : Finset Sentence) (A : Finset ℕ)
    (hne : ∃ v : PCWorld, v.ConsistentWith D) :
    ∃ (k : ℕ) (W : Fin k → PCWorld), 0 < k ∧ (∀ i, (W i).ConsistentWith D) ∧
      CompleteFor D A W := by
  classical
  set B : ℕ := max (A.sup id + 1) (D.sup atomBound) with hB
  have hA : ∀ a ∈ A, a < B := fun a ha =>
    lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)) (le_max_left _ _)
  have hD : ∀ φ ∈ D, atomBound φ ≤ B := fun φ hφ =>
    (Finset.le_sup (f := atomBound) hφ).trans (le_max_right _ _)
  have hres : ∀ v : PCWorld, v.ConsistentWith D →
      (worldOf (BoolPCWorld.FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B)).ConsistentWith D ∧
      ∀ a ∈ A, (worldOf (BoolPCWorld.FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B) a ↔ v a) := by
    intro v hv
    refine ⟨fun φ hφ => (holds_worldOf_restrict v (hD φ hφ)).2 (hv φ hφ), fun a ha => ?_⟩
    have h := holds_worldOf_restrict v (B := B) (φ := Formula.atom a)
      (by simp only [atomBound]; exact hA a ha)
    exact h
  let S : Finset (FiniteWorld B) := Finset.univ.filter fun u => (worldOf u).ConsistentWith D
  obtain ⟨v₀, hv₀⟩ := hne
  have hmem : ∀ v : PCWorld, v.ConsistentWith D →
      BoolPCWorld.FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B ∈ S := fun v hv =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (hres v hv).1⟩
  haveI : Nonempty S := ⟨⟨_, hmem v₀ hv₀⟩⟩
  refine ⟨Fintype.card S, fun i => worldOf ((Fintype.equivFin S).symm i).1,
    Fintype.card_pos, ?_, ?_⟩
  · intro i
    exact (Finset.mem_filter.1 ((Fintype.equivFin S).symm i).2).2
  · intro v hv
    refine ⟨Fintype.equivFin S ⟨_, hmem v hv⟩, ?_⟩
    intro a ha
    simp only [Equiv.symm_apply_apply]
    exact (hres v hv).2 a ha

/-- **The uniform mixture over a complete family**: a rational price assignment in `[0, 1]`
that is a stage mixture on every algebra and non-dogmatic on the algebra over `A`.
Source: mandate § 2 (the mixing lemma applied with uniform weights)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_mixture (D : Finset Sentence) (A : Finset ℕ)
    (hne : ∃ v : PCWorld, v.ConsistentWith D) :
    ∃ p : Sentence → ℚ, (∀ φ, 0 ≤ p φ ∧ p φ ≤ 1) ∧
      (∀ A', CoherentOn D A' (fun φ => (p φ : ℝ))) ∧
      ∀ φ, sentenceAtomCodes φ ⊆ A →
        (∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) ∨
        (∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) ∨
        (0 < p φ ∧ p φ < 1) := by
  obtain ⟨k, W, hk, hW, hc⟩ := exists_completeFor D A hne
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  let w : Fin k → ℚ := fun _ => 1 / k
  have hw0 : ∀ i, 0 < w i := fun _ => by positivity
  have hw1 : ∑ i, w i = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  exact ⟨mixRat W w, fun φ => mixRat_mem_Icc (fun i => (hw0 i).le) hw1 φ,
    fun A' => mixRat_coherentOn A' hW (fun i => (hw0 i).le) hw1,
    fun φ hφ => mixRat_trichotomy hw0 hw1 hc hφ⟩

/-! ## Free atoms are undecided -/

/-- **An atom mentioned by no sentence of a consistent stage is undecided at that stage**: some
`D`-consistent world holds it and some does not (override one consistent world at the atom; the
stage's sentences do not see the change, `holds_congr_atomCodes`).
Source: mandate § 2 (the `freshCoord` N+: "a day-`1` undecided sentence priced strictly inside");
bli-found `Unlinked.stateAtom_free` (the completed-theory analogue)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem free_atom_undecided {D : Finset Sentence} {a : ℕ}
    (hfree : ∀ φ ∈ D, a ∉ sentenceAtomCodes φ) (hne : ∃ v : PCWorld, v.ConsistentWith D) :
    (∃ v : PCWorld, v.ConsistentWith D ∧ v.Holds (Formula.atom a)) ∧
    (∃ v : PCWorld, v.ConsistentWith D ∧ ¬ v.Holds (Formula.atom a)) := by
  obtain ⟨v, hv⟩ := hne
  have hcons : ∀ u : PCWorld, (∀ b, b ≠ a → (u b ↔ v b)) → u.ConsistentWith D :=
    fun u hu φ hφ =>
      (PCWorld.holds_congr_atomCodes φ fun b hb => hu b fun h => hfree φ hφ (h ▸ hb)).2 (hv φ hφ)
  refine ⟨⟨fun b => if b = a then True else v b, hcons _ fun b hb => by simp [hb], ?_⟩,
    ⟨fun b => if b = a then False else v b, hcons _ fun b hb => by simp [hb], ?_⟩⟩
  · show (if a = a then True else v a)
    simp
  · show ¬ (if a = a then False else v a)
    simp

end Cleanroom.Bli.BliExactBase
