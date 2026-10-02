import Cleanroom.Bli.BliFinite.Coherence
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# `bli-finite` · WorldRound: rounding a world distribution; the coherent grid (T4)

The surviving reading of Appendix B's "`D_n` rounds … maintaining propositional consistency"
(bli-paper-033; bli-slides-008's "round the world-distribution, not the marginals"):
coordinatewise rounding breaks coherence (`roundTo_not_coherent`), so round the **world
weights** to multiples of `1/d` instead, and take the marginal. The rounding used is a
*remainder distribution*: floor every `w_i · d`, then hand the `d − ∑⌊w_i d⌋` missing units to
coordinates with positive remainder — **which ones is chosen classically**, so this is not
literally the "largest remainder" method (the bounds below need only "positive remainder"),
and the definition is named `remainderRound`, not `largestRemainder`, for that reason. It is
noncomputable (an existence statement made a function by choice); a canonical computable
selection is the stretch target T10(b), not attempted.

Error bound: every world weight moves by less than `1/d`, so a marginal (payouts in `{0,1}`)
moves by less than `2^B / d` — **not** `1/(2d)`, which is `roundTo`'s bound.
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction Finset BoolPCWorld Classical

/-! ## Rounding a probability vector to the grid `(1/d)·ℕ` -/

/-- **Existence of a grid rounding of a probability vector**: for `0 < d` and a nonnegative `w`
summing to `1`, there is `w'` with values in `(1/d)·ℕ`, nonnegative, summing to `1`, vanishing
where `w` vanishes, and within `1/d` (strictly) of `w` in every coordinate.
Source: bli-slides-008 ("round the finite measure on `2^N` worlds to a rational grid with
`ℓ¹` error `≤ ε`"); mandate T4
Kind: P
Fidelity: exact (strict `< 1/d` per coordinate; the choice of coordinates receiving the extra
units is classical, not "largest remainder")
Hyps: (a) `0 < d`; (a) `w` a probability vector -/
theorem exists_gridRound {ι : Type} [Fintype ι] {d : ℕ} (hd : 0 < d) (w : ι → ℚ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ∃ w' : ι → ℚ, (∀ i, ∃ k : ℕ, w' i = (k : ℚ) / d) ∧ (∀ i, 0 ≤ w' i) ∧ ∑ i, w' i = 1 ∧
      (∀ i, w i = 0 → w' i = 0) ∧ ∀ i, |w' i - w i| < 1 / d := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  -- floors and remainders
  set f : ι → ℕ := fun i => ⌊w i * d⌋₊ with hf
  set r : ι → ℚ := fun i => w i * d - f i with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => by
    simp only [hr, hf]; linarith [Nat.floor_le (mul_nonneg (hw0 i) hdq.le)]
  have hr1 : ∀ i, r i < 1 := fun i => by
    simp only [hr, hf]; linarith [Nat.lt_floor_add_one (w i * d)]
  have hsum_wd : ∑ i, w i * d = d := by rw [← Finset.sum_mul, hw1, one_mul]
  have hsum_f_le : ∑ i, f i ≤ d := by
    have : ((∑ i, f i : ℕ) : ℚ) ≤ d := by
      push_cast
      calc ∑ i, (f i : ℚ) ≤ ∑ i, w i * d :=
            Finset.sum_le_sum fun i _ => by
              simp only [hf]; exact Nat.floor_le (mul_nonneg (hw0 i) hdq.le)
        _ = d := hsum_wd
    exact_mod_cast this
  set R : ℕ := d - ∑ i, f i with hR
  have hRq : (R : ℚ) = ∑ i, r i := by
    simp only [hR, hr]
    rw [Nat.cast_sub hsum_f_le, Finset.sum_sub_distrib, hsum_wd]
    push_cast
    ring
  -- coordinates with positive remainder
  set P : Finset ι := univ.filter (fun i => 0 < r i) with hP
  have hRP : R ≤ P.card := by
    have h1 : (R : ℚ) = ∑ i ∈ P, r i := by
      rw [hRq, ← Finset.sum_filter_add_sum_filter_not univ (fun i => 0 < r i)]
      have : ∑ i ∈ univ.filter (fun i => ¬ 0 < r i), r i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_filter] at hi; exact le_antisymm (not_lt.mp hi.2) (hr0 i)
      rw [this, add_zero]
    have h2 : ∑ i ∈ P, r i ≤ ∑ i ∈ P, (1 : ℚ) := Finset.sum_le_sum fun i _ => (hr1 i).le
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    have : (R : ℚ) ≤ P.card := h1 ▸ h2
    exact_mod_cast this
  obtain ⟨C, hCP, hC⟩ := Finset.exists_subset_card_eq hRP
  -- the rounded vector
  refine ⟨fun i => ((f i + if i ∈ C then 1 else 0 : ℕ) : ℚ) / d, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact ⟨_, rfl⟩
  · intro i; positivity
  · simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, Finset.sum_add_distrib, Finset.sum_boole]
    have hcard : (univ.filter (fun i => i ∈ C)).card = R := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]; exact hC
    rw [hcard]
    simp only [Nat.cast_id]
    rw [hR, Nat.add_sub_cancel' hsum_f_le]
    exact mul_inv_cancel₀ hdq.ne'
  · intro i hi
    have hfi : f i = 0 := by
      simp only [hf]; rw [hi, zero_mul]; exact Nat.floor_zero
    have hri : r i = 0 := by simp only [hr, hfi, hi]; simp
    have hiC : i ∉ C := fun h => by
      have := hCP h
      rw [hP, Finset.mem_filter] at this
      rw [hri] at this
      exact lt_irrefl _ this.2
    simp [hfi, hiC]
  · intro i
    have key : ((f i + if i ∈ C then 1 else 0 : ℕ) : ℚ) / d - w i =
        ((if i ∈ C then 1 else 0) - r i) / d := by
      simp only [hr]
      push_cast
      field_simp
      split_ifs <;> ring
    rw [key, abs_div, abs_of_pos hdq, div_lt_div_iff_of_pos_right hdq]
    rw [abs_lt]
    by_cases hiC : i ∈ C
    · have hiP := hCP hiC
      rw [hP, Finset.mem_filter] at hiP
      simp only [hiC, if_true]
      constructor <;> linarith [hiP.2, hr1 i]
    · simp only [hiC, if_false, zero_sub]
      constructor <;> linarith [hr0 i, hr1 i]

/-- **Remainder rounding** of a probability vector to `(1/d)·ℕ`: a chosen witness of
`exists_gridRound`. Noncomputable (classical choice of the coordinates receiving the extra
units); see the module docstring for why it is not called "largest remainder".
Source: mandate T4 (`largestRemainder`, renamed)
Kind: D
Fidelity: variant: some remainder-distribution rounding, not necessarily largest-remainder
(disclosed) -/
noncomputable def remainderRound {ι : Type} [Fintype ι] {d : ℕ} (hd : 0 < d) (w : ι → ℚ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) : ι → ℚ :=
  Classical.choose (exists_gridRound hd w hw0 hw1)

section RemainderRound

variable {ι : Type} [Fintype ι] {d : ℕ} (hd : 0 < d) (w : ι → ℚ) (hw0 : ∀ i, 0 ≤ w i)
  (hw1 : ∑ i, w i = 1)

/-- The defining specification of `remainderRound`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma remainderRound_spec :
    (∀ i, ∃ k : ℕ, remainderRound hd w hw0 hw1 i = (k : ℚ) / d) ∧
    (∀ i, 0 ≤ remainderRound hd w hw0 hw1 i) ∧ ∑ i, remainderRound hd w hw0 hw1 i = 1 ∧
    (∀ i, w i = 0 → remainderRound hd w hw0 hw1 i = 0) ∧
    ∀ i, |remainderRound hd w hw0 hw1 i - w i| < 1 / d :=
  Classical.choose_spec (exists_gridRound hd w hw0 hw1)

/-- Rounded weights are multiples of `1/d`.
Source: mandate T4 (`largestRemainder_mem`)
Kind: L
Fidelity: exact -/
lemma remainderRound_mem (i : ι) : ∃ k : ℕ, remainderRound hd w hw0 hw1 i = (k : ℚ) / d :=
  (remainderRound_spec hd w hw0 hw1).1 i

/-- Rounded weights are nonnegative.
Source: mandate T4
Kind: L
Fidelity: exact -/
lemma remainderRound_nonneg (i : ι) : 0 ≤ remainderRound hd w hw0 hw1 i :=
  (remainderRound_spec hd w hw0 hw1).2.1 i

/-- Rounded weights sum to one.
Source: mandate T4
Kind: L
Fidelity: exact -/
lemma remainderRound_sum_one : ∑ i, remainderRound hd w hw0 hw1 i = 1 :=
  (remainderRound_spec hd w hw0 hw1).2.2.1

/-- A zero weight stays zero (so `D`-consistency of the support is preserved).
Source: mandate T4 (`support_subset`)
Kind: L
Fidelity: exact -/
lemma remainderRound_support_subset (i : ι) (h : w i = 0) : remainderRound hd w hw0 hw1 i = 0 :=
  (remainderRound_spec hd w hw0 hw1).2.2.2.1 i h

/-- Every weight moves by less than `1/d`.
Source: mandate T4 (`abs_sub_le`, strengthened to strict)
Kind: L
Fidelity: stronger: strict inequality -/
lemma remainderRound_abs_sub_lt (i : ι) : |remainderRound hd w hw0 hw1 i - w i| < 1 / d :=
  (remainderRound_spec hd w hw0 hw1).2.2.2.2 i

/-- The `ℓ¹` change is at most `card ι / d`.
Source: mandate T4 (`l1_le`)
Kind: L
Fidelity: exact -/
lemma remainderRound_l1_le : ∑ i, |remainderRound hd w hw0 hw1 i - w i| ≤ (Fintype.card ι : ℚ) / d := by
  calc ∑ i, |remainderRound hd w hw0 hw1 i - w i| ≤ ∑ _i : ι, (1 : ℚ) / d :=
        Finset.sum_le_sum fun i _ => (remainderRound_abs_sub_lt hd w hw0 hw1 i).le
    _ = (Fintype.card ι : ℚ) / d := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]

end RemainderRound

/-! ## The coherent grid and world rounding -/

variable {𝒮 : SmallIndex} {m : ℕ}

/-- Integer world weights (in units of `1/d`) summing to `d`, supported on `D`-consistent worlds.
Source: [[bli-program]] §2.2 (`coherentGrid`: "world weights in `(1/d)·ℤ`")
Kind: D
Fidelity: exact -/
noncomputable def worldWeights (D : Finset Sentence) (B d : ℕ) : Finset (FiniteWorld B → Fin (d + 1)) :=
  (Fintype.piFinset fun _ => (univ : Finset (Fin (d + 1)))).filter
    fun c => ∑ u, (c u).val = d ∧ ∀ u, (c u).val ≠ 0 → (worldOf u).ConsistentWith D

/-- The marginal table of integer world weights (in units of `1/d`).
Source: [[bli-program]] §2.2
Kind: D
Fidelity: exact -/
def marginalOf (𝒮 : SmallIndex) (m : ℕ) {B : ℕ} (d : ℕ) (c : FiniteWorld B → Fin (d + 1)) :
    Table 𝒮 m :=
  fun φ => ∑ u, ((c u).val : ℚ) / d * u.payoutRat φ.1

/-- **The coherent grid**: the day-`m` tables that are marginals of `D`-consistent world weights
in `(1/d m)·ℕ` (the variant of Appendix B's `𝒟_n` that *does* maintain propositional
consistency).
Source: bli-paper-033 (the surviving reading of `𝒟_n`); [[bli-program]] §2.2
Kind: D
Fidelity: exact -/
noncomputable def coherentGrid (𝒮 : SmallIndex) (d : ℕ → ℕ) (m : ℕ) (D : Finset Sentence) (B : ℕ) :
    Finset (Table 𝒮 m) :=
  (worldWeights D B (d m)).image (marginalOf 𝒮 m (d m))

/-- Every coherent-grid table is coherent.
Source: [[bli-program]] §2.2
Kind: L
Fidelity: exact -/
lemma coherentOn_of_mem_coherentGrid {d : ℕ → ℕ} (hd : 0 < d m) {D : Finset Sentence} {B : ℕ}
    {Q : Table 𝒮 m} (hQ : Q ∈ coherentGrid 𝒮 d m D B) : CoherentOn Q D B := by
  unfold coherentGrid at hQ
  rw [Finset.mem_image] at hQ
  obtain ⟨c, hc, rfl⟩ := hQ
  unfold worldWeights at hc
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hsum, hsupp⟩ := hc
  have hdq : (0 : ℚ) < d m := by exact_mod_cast hd
  refine ⟨fun u => ((c u).val : ℚ) / d m, fun u => by positivity, ?_, ?_, fun φ => rfl⟩
  · simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, hsum]
    exact mul_inv_cancel₀ hdq.ne'
  · intro u hu
    apply hsupp u
    intro h0
    apply hu
    show (((c u).val : ℕ) : ℚ) / (d m : ℚ) = 0
    rw [h0]; simp

/-- **World rounding** of a coherent table: round a chosen world distribution by
`remainderRound` and take the marginal. Noncomputable (the world distribution is
`Classical.choose`, the rounding is classical too); disclosed.
Source: bli-paper-033 (the surviving reading of `D_n`); bli-slides-008; [[bli-program]] §2.2
Kind: D
Fidelity: variant: noncomputable choice of the world distribution and of the rounding
(disclosed) -/
noncomputable def worldRound {d : ℕ} (hd : 0 < d) {D : Finset Sentence} {B : ℕ} {t : Table 𝒮 m}
    (ht : CoherentOn t D B) : Table 𝒮 m :=
  fun φ => ∑ u, remainderRound hd (Classical.choose ht) (Classical.choose_spec ht).1
    (Classical.choose_spec ht).2.1 u * u.payoutRat φ.1

section WorldRound

variable {d : ℕ} (hd : 0 < d) {D : Finset Sentence} {B : ℕ} {t : Table 𝒮 m} (ht : CoherentOn t D B)

/-- **World rounding preserves coherence** (the property coordinatewise rounding lacks).
Source: bli-paper-033; bli-slides-008
Kind: P
Fidelity: exact
Hyps: (a) `0 < d`; (a) `CoherentOn t D B` -/
theorem worldRound_coherent : CoherentOn (worldRound hd ht) D B := by
  set w := Classical.choose ht with hw
  have hspec := Classical.choose_spec ht
  refine ⟨remainderRound hd w hspec.1 hspec.2.1, remainderRound_nonneg hd w _ _,
    remainderRound_sum_one hd w _ _, ?_, fun φ => rfl⟩
  intro u hu
  apply hspec.2.2.1 u
  intro h0
  exact hu (remainderRound_support_subset hd w _ _ u h0)

/-- **World rounding lands on the coherent grid.**
Source: bli-paper-033 (`𝒟_n`); [[bli-program]] §2.2
Kind: P
Fidelity: exact
Hyps: (a) `0 < d`; (a) `CoherentOn t D B` -/
theorem worldRound_mem_coherentGrid {dd : ℕ → ℕ} (hdd : dd m = d) :
    worldRound hd ht ∈ coherentGrid 𝒮 dd m D B := by
  subst hdd
  set w := Classical.choose ht with hw
  have hspec := Classical.choose_spec ht
  set w' := remainderRound hd w hspec.1 hspec.2.1 with hw'
  have hmem := remainderRound_mem hd w hspec.1 hspec.2.1
  have hdq : (0 : ℚ) < dd m := by exact_mod_cast hd
  -- the integer weights
  set k : FiniteWorld B → ℕ := fun u => Classical.choose (hmem u) with hk
  have hkw : ∀ u, w' u = (k u : ℚ) / dd m := fun u => Classical.choose_spec (hmem u)
  have hksum : ∑ u, k u = dd m := by
    have h := remainderRound_sum_one hd w hspec.1 hspec.2.1
    rw [Finset.sum_congr rfl (fun u _ => hkw u)] at h
    simp only [div_eq_mul_inv] at h
    rw [← Finset.sum_mul, mul_inv_eq_one₀ hdq.ne'] at h
    exact_mod_cast h
  have hkle : ∀ u, k u < dd m + 1 := fun u =>
    Nat.lt_succ_of_le (hksum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u))
  unfold coherentGrid
  rw [Finset.mem_image]
  refine ⟨fun u => ⟨k u, hkle u⟩, ?_, ?_⟩
  · unfold worldWeights
    rw [Finset.mem_filter]
    refine ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, hksum, ?_⟩
    intro u hu
    apply hspec.2.2.1 u
    intro h0
    have hz : w' u = 0 := remainderRound_support_subset hd w hspec.1 hspec.2.1 u h0
    rw [hkw u] at hz
    apply hu
    show k u = 0
    have : (k u : ℚ) = 0 := by
      rcases (div_eq_zero_iff.mp hz) with h | h
      · exact h
      · exact absurd h hdq.ne'
    exact_mod_cast this
  · funext φ
    unfold marginalOf worldRound
    exact Finset.sum_congr rfl fun u _ => by rw [← hkw u]

/-- **Error of world rounding**: every marginal moves by less than `2^B / d` (the `ℓ¹` change of
`2^B` world weights each moving by less than `1/d`, against `{0,1}` payouts). Not `1/(2d)`:
that is coordinatewise rounding's bound.
Source: bli-slides-008 ("then the marginals move by `≤ ε`"); mandate T4
Kind: P
Fidelity: stronger: strict
Hyps: (a) `0 < d`; (a) `CoherentOn t D B` -/
theorem worldRound_err (φ : ↥(𝒮.S m)) : |worldRound hd ht φ - t φ| < (2 : ℚ) ^ B / d := by
  set w := Classical.choose ht with hw
  have hspec := Classical.choose_spec ht
  set w' := remainderRound hd w hspec.1 hspec.2.1 with hw'
  have ht' : t φ = ∑ u, w u * u.payoutRat φ.1 := hspec.2.2.2 φ
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  calc |worldRound hd ht φ - t φ|
      = |∑ u, (w' u - w u) * u.payoutRat φ.1| := by
        unfold worldRound
        rw [ht', ← Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl fun u _ => by ring
    _ ≤ ∑ u, |(w' u - w u) * u.payoutRat φ.1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, |w' u - w u| := Finset.sum_le_sum fun u _ => by
        rw [abs_mul, abs_of_nonneg (payoutRat_nonneg u _)]
        exact mul_le_of_le_one_right (abs_nonneg _) (payoutRat_le_one u _)
    _ < ∑ _u : FiniteWorld B, (1 : ℚ) / d :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          fun u _ => remainderRound_abs_sub_lt hd w hspec.1 hspec.2.1 u
    _ = (2 : ℚ) ^ B / d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, mul_one_div]
        push_cast
        rfl

end WorldRound

end Cleanroom.Bli.BliFinite
