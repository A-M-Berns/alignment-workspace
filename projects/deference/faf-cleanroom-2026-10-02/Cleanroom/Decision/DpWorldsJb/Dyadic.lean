import Cleanroom.Decision.DpWorldsJb.Annihilation
import Cleanroom.Decision.DpWorldsJb.Worlds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The dyadic algebra: N+ witness for annihilation (T6)

`Dy` is the Boolean subalgebra of `Set [0,1)` of **dyadic sets**: sets whose membership depends
only on the first `n` binary digits of the point, for some `n` (equivalently finite unions of
level-`n` dyadic intervals `[k/2ⁿ, (k+1)/2ⁿ)`). Its measure `dyProb` is Lebesgue measure of the
underlying set of reals, so finite additivity is automatic; `dyProb` is strictly positive (a
nonempty dyadic set contains a dyadic interval) with exact halving (keep the left halves), and
`no_world_of_halving` applies: **`(Dy, Jω Dy)` has no worlds** (`dyadic_no_world`), although
`Dy` is nontrivial and has `J = ∅` worlds (T5(a)) and is atomless.

This is a *variant* witness: the appendix's instance is the Lebesgue measure algebra (Borel
mod null), which Mathlib does not have; the abstract theorem needs no σ-additivity, so the
countable atomless subalgebra suffices.
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open MeasureTheory Set Classical

/-- The half-open unit interval `[0,1)` as a type.
Source: [[decision-problems-v2]] Appendix A "Annihilation"
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev Unit01 : Type := Set.Ico (0 : ℝ) 1

/-- The level-`n` index of a point of `[0,1)`: `⌊x · 2ⁿ⌋₊`, the first `n` binary digits.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def dyIdx (n : ℕ) (x : Unit01) : ℕ := ⌊x.1 * 2 ^ n⌋₊

theorem dyIdx_lt (n : ℕ) (x : Unit01) : dyIdx n x < 2 ^ n := by
  unfold dyIdx
  rw [Nat.floor_lt (mul_nonneg x.2.1 (by positivity))]
  push_cast
  exact mul_lt_of_lt_one_left (by positivity) x.2.2

theorem dyIdx_succ_div (n : ℕ) (x : Unit01) : dyIdx (n + 1) x / 2 = dyIdx n x := by
  unfold dyIdx
  have h : x.1 * 2 ^ (n + 1) / ((2 : ℕ) : ℝ) = x.1 * 2 ^ n := by
    push_cast
    rw [pow_succ]
    ring
  rw [← h, Nat.floor_div_natCast]

/-- The level-`n` dyadic set with index set `T`: the points whose level-`n` index lies in `T`.
Source: [[decision-problems-v2]] Appendix A "Annihilation" (the dyadic algebra as a stand-in)
Kind: D
Fidelity: exact
Hyps: n/a -/
def dySet (n : ℕ) (T : Finset ℕ) : Set Unit01 := {x | dyIdx n x ∈ T}

theorem mem_dySet {n : ℕ} {T : Finset ℕ} {x : Unit01} : x ∈ dySet n T ↔ dyIdx n x ∈ T := Iff.rfl

/-- The index set of a level-`n` set read at level `n + 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def refineT (n : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.range (2 ^ (n + 1))).filter (fun j => j / 2 ∈ T)

theorem dySet_refine (n : ℕ) (T : Finset ℕ) : dySet n T = dySet (n + 1) (refineT n T) := by
  ext x
  simp only [mem_dySet, refineT, Finset.mem_filter, Finset.mem_range]
  rw [dyIdx_succ_div]
  exact ⟨fun h => ⟨dyIdx_lt _ _, h⟩, fun h => h.2⟩

theorem refineT_subset (n : ℕ) (T : Finset ℕ) : refineT n T ⊆ Finset.range (2 ^ (n + 1)) :=
  Finset.filter_subset _ _

/-- `s` is dyadic at level `n`, with a normalized index set `T ⊆ range (2ⁿ)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def IsDyadicLevel (n : ℕ) (s : Set Unit01) : Prop :=
  ∃ T : Finset ℕ, T ⊆ Finset.range (2 ^ n) ∧ s = dySet n T

theorem IsDyadicLevel.succ {n : ℕ} {s : Set Unit01} (h : IsDyadicLevel n s) :
    IsDyadicLevel (n + 1) s := by
  obtain ⟨T, -, rfl⟩ := h
  exact ⟨refineT n T, refineT_subset n T, dySet_refine n T⟩

theorem IsDyadicLevel.mono {n m : ℕ} {s : Set Unit01} (h : IsDyadicLevel n s) (hnm : n ≤ m) :
    IsDyadicLevel m s := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact ih.succ

/-- `s` is dyadic: dyadic at some level.
Source: [[decision-problems-v2]] Appendix A "Annihilation"
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsDyadic (s : Set Unit01) : Prop := ∃ n, IsDyadicLevel n s

theorem IsDyadic.common {s t : Set Unit01} (hs : IsDyadic s) (ht : IsDyadic t) :
    ∃ n, IsDyadicLevel n s ∧ IsDyadicLevel n t := by
  obtain ⟨n, hn⟩ := hs
  obtain ⟨m, hm⟩ := ht
  exact ⟨max n m, hn.mono (le_max_left _ _), hm.mono (le_max_right _ _)⟩

theorem dySet_union (n : ℕ) (T₁ T₂ : Finset ℕ) :
    dySet n T₁ ∪ dySet n T₂ = dySet n (T₁ ∪ T₂) := by
  ext x
  simp [mem_dySet]

theorem dySet_inter (n : ℕ) (T₁ T₂ : Finset ℕ) :
    dySet n T₁ ∩ dySet n T₂ = dySet n (T₁ ∩ T₂) := by
  ext x
  simp [mem_dySet]

theorem dySet_compl (n : ℕ) (T : Finset ℕ) :
    (dySet n T)ᶜ = dySet n (Finset.range (2 ^ n) \ T) := by
  ext x
  simp [mem_dySet, dyIdx_lt]

theorem dySet_empty (n : ℕ) : dySet n ∅ = ∅ := by
  ext x
  simp [mem_dySet]

/-- **The dyadic algebra** `Dy`, a Boolean subalgebra of `Set [0,1)`.
Source: [[decision-problems-v2]] Appendix A "Annihilation" | dp-core-2-058
Kind: D
Fidelity: variant: the countable dyadic algebra in place of the Lebesgue measure algebra
Hyps: n/a -/
def Dy : BooleanSubalgebra (Set Unit01) where
  carrier := {s | IsDyadic s}
  supClosed' := by
    intro s hs t ht
    obtain ⟨n, ⟨T₁, hT₁, rfl⟩, ⟨T₂, hT₂, rfl⟩⟩ := IsDyadic.common hs ht
    exact ⟨n, T₁ ∪ T₂, Finset.union_subset hT₁ hT₂, dySet_union n T₁ T₂⟩
  infClosed' := by
    intro s hs t ht
    obtain ⟨n, ⟨T₁, hT₁, rfl⟩, ⟨T₂, hT₂, rfl⟩⟩ := IsDyadic.common hs ht
    exact ⟨n, T₁ ∩ T₂, (Finset.inter_subset_left).trans hT₁, dySet_inter n T₁ T₂⟩
  compl_mem' := by
    intro s hs
    obtain ⟨n, T, _, rfl⟩ := hs
    exact ⟨n, Finset.range (2 ^ n) \ T, Finset.sdiff_subset, dySet_compl n T⟩
  bot_mem' := ⟨0, ∅, Finset.empty_subset _, (dySet_empty 0).symm⟩

theorem mem_Dy (s : Set Unit01) : s ∈ Dy ↔ IsDyadic s := Iff.rfl

/-! ### Lebesgue measure of dyadic sets -/

/-- The level-`n` dyadic interval `[k/2ⁿ, (k+1)/2ⁿ)`.
Source: [[decision-problems-v2]] Appendix A "Annihilation"
Kind: D
Fidelity: exact
Hyps: n/a -/
def dyInt (n k : ℕ) : Set ℝ := Ico ((k : ℝ) / 2 ^ n) ((k + 1 : ℝ) / 2 ^ n)

theorem mem_dyInt_iff {n k : ℕ} {y : ℝ} (hy : 0 ≤ y) : y ∈ dyInt n k ↔ ⌊y * 2 ^ n⌋₊ = k := by
  unfold dyInt
  rw [Set.mem_Ico, Nat.floor_eq_iff (mul_nonneg hy (by positivity))]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(div_le_iff₀ (by positivity)).1 h1, (lt_div_iff₀ (by positivity)).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(div_le_iff₀ (by positivity)).2 h1, (lt_div_iff₀ (by positivity)).2 h2⟩

/-- A level-`n` dyadic set, as a set of reals, is the union of its dyadic intervals.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem image_val_dySet (n : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range (2 ^ n)) :
    Subtype.val '' dySet n T = ⋃ k ∈ T, dyInt n k := by
  ext y
  simp only [Set.mem_image, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨dyIdx n x, hx, (mem_dyInt_iff x.2.1).2 rfl⟩
  · rintro ⟨k, hk, hy⟩
    have hk' : k < 2 ^ n := Finset.mem_range.1 (hT hk)
    have hy0 : 0 ≤ y := le_trans (by positivity) hy.1
    have hy1 : y < 1 := by
      refine lt_of_lt_of_le hy.2 ?_
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.succ_le_of_lt hk'
    refine ⟨⟨y, hy0, hy1⟩, ?_, rfl⟩
    show ⌊y * 2 ^ n⌋₊ ∈ T
    rw [(mem_dyInt_iff hy0).1 hy]
    exact hk

theorem volume_dyInt (n k : ℕ) : volume (dyInt n k) = ENNReal.ofReal (1 / 2 ^ n) := by
  unfold dyInt
  rw [Real.volume_Ico]
  congr 1
  ring

theorem dyInt_pairwiseDisjoint (n : ℕ) : (Set.univ : Set ℕ).PairwiseDisjoint (dyInt n) := by
  intro k _ k' _ hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro y hy hy'
  have hy0 : 0 ≤ y := le_trans (by positivity) hy.1
  rw [mem_dyInt_iff hy0] at hy hy'
  exact hkk' (hy.symm.trans hy')

theorem measurableSet_dyInt (n k : ℕ) : MeasurableSet (dyInt n k) := measurableSet_Ico

theorem volume_dySet (n : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range (2 ^ n)) :
    volume (Subtype.val '' dySet n T) = T.card * ENNReal.ofReal (1 / 2 ^ n) := by
  rw [image_val_dySet n T hT,
    measure_biUnion_finset ((dyInt_pairwiseDisjoint n).subset (Set.subset_univ _))
      (fun k _ => measurableSet_dyInt n k)]
  simp [volume_dyInt]

/-- Lebesgue measure of the underlying set of reals of a dyadic set.
Source: [[decision-problems-v2]] Appendix A "Annihilation" (measures `2⁻ⁿ`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def dyMeasure (s : Dy) : ℝ := (volume (Subtype.val '' (s : Set Unit01))).toReal

theorem dyMeasure_eq (n : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range (2 ^ n)) (s : Dy)
    (hs : (s : Set Unit01) = dySet n T) : dyMeasure s = T.card / 2 ^ n := by
  unfold dyMeasure
  rw [hs, volume_dySet n T hT, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)]
  ring

theorem dy_measurable (s : Dy) : MeasurableSet (Subtype.val '' (s : Set Unit01)) := by
  obtain ⟨n, T, hT, hs⟩ := s.2
  rw [hs, image_val_dySet n T hT]
  exact Finset.measurableSet_biUnion _ (fun k _ => measurableSet_dyInt n k)

theorem dy_volume_ne_top (s : Dy) : volume (Subtype.val '' (s : Set Unit01)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (b := volume (Ico (0 : ℝ) 1))
  · rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  · apply measure_mono
    rintro _ ⟨x, _, rfl⟩
    exact x.2

/-- **The dyadic probability**: Lebesgue measure on `Dy`, a finitely additive probability
(`Prob ∅`).
Source: [[decision-problems-v2]] Appendix A "Annihilation" | dp-core-2-058
Kind: P
Fidelity: variant: on the dyadic algebra
Hyps: (a) -/
def dyProb : Prob (∅ : Designation Dy) where
  P := dyMeasure
  nonneg _ := ENNReal.toReal_nonneg
  top := by
    show (volume (Subtype.val '' ((⊤ : Dy) : Set Unit01))).toReal = 1
    rw [BooleanSubalgebra.val_top, Set.top_eq_univ, Set.image_univ, Subtype.range_coe, Real.volume_Ico]
    simp
  add s t h := by
    show (volume (Subtype.val '' ((s ⊔ t : Dy) : Set Unit01))).toReal = _
    rw [BooleanSubalgebra.val_sup]
    show (volume (Subtype.val '' ((s : Set Unit01) ∪ t))).toReal = _
    have hdisj : Disjoint (Subtype.val '' (s : Set Unit01)) (Subtype.val '' (t : Set Unit01)) := by
      rw [Set.disjoint_image_iff Subtype.val_injective]
      have h2 := congrArg (fun z : Dy => (z : Set Unit01)) (disjoint_iff.1 h)
      simp only [BooleanSubalgebra.val_inf, BooleanSubalgebra.val_bot] at h2
      exact disjoint_iff.2 h2
    rw [Set.image_union, measure_union hdisj (dy_measurable t),
      ENNReal.toReal_add (dy_volume_ne_top s) (dy_volume_ne_top t)]
    rfl
  cont _ hD := hD.elim

theorem dyProb_apply (s : Dy) : dyProb.P s = dyMeasure s := rfl

/-- `dyProb` is strictly positive: a nonempty dyadic set has a nonempty index set.
Source: [[decision-problems-v2]] Appendix A "Annihilation"
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem dyProb_strictlyPositive : StrictlyPositive dyProb := by
  intro s hs
  obtain ⟨n, T, hT, hsT⟩ := s.2
  rw [dyProb_apply, dyMeasure_eq n T hT s hsT]
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hs
    apply Subtype.ext
    rw [hsT, dySet_empty]
    rfl
  have := Finset.card_pos.2 hTne
  exact div_pos (by exact_mod_cast this) (by positivity)

/-- `dyProb` has exact halving: keep the left half of every interval.
Source: [[decision-problems-v2]] Appendix A "Annihilation" ("a decreasing chain of halves")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem dyProb_exactHalving : ExactHalving dyProb := by
  intro s _
  obtain ⟨n, T, hT, hsT⟩ := s.2
  let T' : Finset ℕ := T.image (2 * ·)
  have hT' : T' ⊆ Finset.range (2 ^ (n + 1)) := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    rw [Finset.mem_range, pow_succ]
    have := Finset.mem_range.1 (hT hk)
    omega
  refine ⟨⟨dySet (n + 1) T', n + 1, T', hT', rfl⟩, ?_, ?_⟩
  · show dySet (n + 1) T' ⊆ (s : Set Unit01)
    rw [hsT]
    intro x hx
    rw [mem_dySet] at hx ⊢
    rw [Finset.mem_image] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    rw [← dyIdx_succ_div, ← hkx, Nat.mul_div_cancel_left k (by norm_num)]
    exact hk
  · show dyMeasure ⟨dySet (n + 1) T', _⟩ = dyMeasure s / 2
    rw [dyMeasure_eq (n + 1) T' hT' _ rfl, dyMeasure_eq n T hT s hsT,
      Finset.card_image_of_injective _ (mul_right_injective₀ two_ne_zero), pow_succ]
    ring

/-- **T6, N+.** The dyadic algebra with every countable existing meet designated has no
worlds — by `no_world_of_halving`, with the hypotheses discharged by `dyProb`.
Source: [[decision-problems-v2]] Appendix A "Annihilation" (line 327) | dp-core-2-058
Kind: N+
Fidelity: variant: the dyadic algebra in place of the Lebesgue measure algebra (a countable
atomless subalgebra; the abstract theorem needs no σ-additivity)
Hyps: (a) -/
theorem dyadic_no_world : IsEmpty (World (Jω Dy)) :=
  no_world_of_halving dyProb dyProb_strictlyPositive dyProb_exactHalving

instance Dy.nontrivial : Nontrivial Dy :=
  ⟨⟨⊤, ⊥, fun h => by
    have h2 := congrArg (fun z : Dy => (z : Set Unit01)) h
    simp only [BooleanSubalgebra.val_top, BooleanSubalgebra.val_bot] at h2
    exact (Set.univ_eq_empty_iff.1 h2).false ⟨0, le_refl 0, zero_lt_one⟩⟩⟩

/-- The same algebra has worlds for `J = ∅` (so annihilation is the designation's doing, not the
algebra's).
Source: [[decision-problems-v2]] Appendix A "Annihilation"
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem dyadic_nonempty_world_empty : Nonempty (World (∅ : Designation Dy)) := nonempty_world

/-- The dyadic algebra is atomless.
Source: [[decision-problems-v2]] Appendix A "Annihilation" ("atomlessness")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem dyadic_atomless : ∀ X : Dy, X ≠ ⊥ → ∃ Y, Y ≤ X ∧ Y ≠ ⊥ ∧ Y ≠ X :=
  atomless_of_halving dyProb dyProb_strictlyPositive dyProb_exactHalving

end

end Cleanroom.Decision.DpWorldsJb
