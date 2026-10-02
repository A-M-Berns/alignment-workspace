import LogicalInduction.Framework.Expectations
import LogicalInduction.Framework.Criterion
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `bli-rvc-ui` · Rvc/Defs: real-value coherence, the objects of record

**Design decisions 2–4 of the mandate.** A real variable is FAF's `LUV` — its entire market-facing
content is the threshold family `X.gt r = ⌜X > r⌝` — and a threshold set is a `Finset ℚ`.

* `thresholdAtoms X R`, `monoFacts X R` (`X.gt r 🡒 X.gt r'` for `r' < r`), `rangeFacts X R`
  (`X.gt r` for `r < 0`, `∼X.gt r` for `1 ≤ r`): the finite stage relative to which coherence on
  the thresholds is the coherence of a real variable.
* `RVC_B` — slide p. 7's (B), "individual beliefs `ℙ(x > .2)`, … are consistent with some overall
  distribution on `x`", as a **finite mixture of point values** (on finitely many thresholds a
  probability measure on `[0,1]` is matched by a finite mixture, so this is not a weakening; the
  measure form is not shipped).
* `ThresholdAntitone` — the cheap characterization of `RVC_B` (`Rvc/Antitone.lean`): the threshold
  beliefs lie in `[0,1]`, are antitone in the threshold, are `1` below `0` and `0` at or above `1`.
* `SumValued`, `RVC_E_exact`, `RVC_E_eps` — slide p. 7's (E) on FAF's grid expectation
  `LUV.expectApprox`, with the sum `Z = X + Y` tied through worlds in FAF's determined-value form.

**The boundary threshold `1` (findings F-12).** FAF's `PCWorld.ValuesAt v X x` decides `X.gt r` for
`r < x` and `x < r` only; at `r = x` it says nothing. So a world valuing `X` at exactly `1` need not
hold `∼X.gt 1`, and `rangeFacts` at `r = 1` is **not** forced by `ValuesAt` (the mandate's decision 2
says it is: that is the one place it is wrong). `holds_rangeFacts_of_valuesAt` therefore carries
`1 ∉ R`; the finite two-axiom equivalence (`Rvc/Finite.lean`) needs no such clause because
`RVC_B` itself forces `V (X.gt 1) = 0` (point values lie in `[0,1]`).
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset

/-! ## Threshold atoms and the facts a valued variable satisfies -/

/-- The threshold sentences `⌜X > r⌝`, `r ∈ R`.
Source: mandate design decision 2; bli-slides-014 (B)
Kind: D
Fidelity: exact -/
def thresholdAtoms (X : LUV) (R : Finset ℚ) : Finset Sentence := R.image X.gt

/-- The monotonicity facts `⌜X > r⌝ 🡒 ⌜X > r'⌝` for `r' < r`, both in `R`.
Source: mandate design decision 2; bli-soto-a-051 (the "digit" constraints)
Kind: D
Fidelity: exact -/
def monoFacts (X : LUV) (R : Finset ℚ) : Finset Sentence :=
  ((R ×ˢ R).filter (fun p : ℚ × ℚ => p.2 < p.1)).image (fun p => X.gt p.1 🡒 X.gt p.2)

/-- The range facts of a `[0,1]`-variable: `⌜X > r⌝` for `r < 0` and `∼⌜X > r⌝` for `1 ≤ r`.
Source: mandate design decision 2
Kind: D
Fidelity: exact (the `1 ≤ r` clause is not forced by `ValuesAt` at `r = 1`, see the module header) -/
def rangeFacts (X : LUV) (R : Finset ℚ) : Finset Sentence :=
  (R.filter (fun r => r < 0)).image X.gt ∪ (R.filter (fun r => 1 ≤ r)).image (fun r => ∼X.gt r)

/-- `mem_thresholdAtoms`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mem_thresholdAtoms {X : LUV} {R : Finset ℚ} {φ : Sentence} :
    φ ∈ thresholdAtoms X R ↔ ∃ r ∈ R, X.gt r = φ := by
  simp [thresholdAtoms]

/-- `mem_monoFacts`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_monoFacts {X : LUV} {R : Finset ℚ} {φ : Sentence} :
    φ ∈ monoFacts X R ↔ ∃ r ∈ R, ∃ r' ∈ R, r' < r ∧ X.gt r 🡒 X.gt r' = φ := by
  simp only [monoFacts, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨r, r', ⟨⟨hr, hr'⟩, hlt⟩, rfl⟩
    exact ⟨r, hr, r', hr', hlt, rfl⟩
  · rintro ⟨r, hr, r', hr', hlt, rfl⟩
    exact ⟨r, r', ⟨⟨hr, hr'⟩, hlt⟩, rfl⟩

/-- `monoFact_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma monoFact_mem {X : LUV} {R : Finset ℚ} {r r' : ℚ} (hr : r ∈ R) (hr' : r' ∈ R)
    (hlt : r' < r) : X.gt r 🡒 X.gt r' ∈ monoFacts X R :=
  mem_monoFacts.mpr ⟨r, hr, r', hr', hlt, rfl⟩

/-- `mem_rangeFacts`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_rangeFacts {X : LUV} {R : Finset ℚ} {φ : Sentence} :
    φ ∈ rangeFacts X R ↔
      (∃ r ∈ R, r < 0 ∧ X.gt r = φ) ∨ (∃ r ∈ R, 1 ≤ r ∧ ∼X.gt r = φ) := by
  simp only [rangeFacts, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (⟨r, ⟨hr, hlt⟩, rfl⟩ | ⟨r, ⟨hr, hle⟩, rfl⟩)
    · exact Or.inl ⟨r, hr, hlt, rfl⟩
    · exact Or.inr ⟨r, hr, hle, rfl⟩
  · rintro (⟨r, hr, hlt, rfl⟩ | ⟨r, hr, hle, rfl⟩)
    · exact Or.inl ⟨r, ⟨hr, hlt⟩, rfl⟩
    · exact Or.inr ⟨r, ⟨hr, hle⟩, rfl⟩

/-- `rangeFact_neg_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rangeFact_neg_mem {X : LUV} {R : Finset ℚ} {r : ℚ} (hr : r ∈ R) (hlt : r < 0) :
    X.gt r ∈ rangeFacts X R :=
  mem_rangeFacts.mpr (Or.inl ⟨r, hr, hlt, rfl⟩)

/-- `rangeFact_one_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rangeFact_one_mem {X : LUV} {R : Finset ℚ} {r : ℚ} (hr : r ∈ R) (hle : 1 ≤ r) :
    ∼X.gt r ∈ rangeFacts X R :=
  mem_rangeFacts.mpr (Or.inr ⟨r, hr, hle, rfl⟩)

/-- A world valuing `X` holds `X.gt r` for every threshold strictly below the value (FAF's
`ValuesAt`, first clause) and fails it strictly above (second clause).
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma holds_gt_of_valuesAt {v : PCWorld} {X : LUV} {x : ℝ} (h : v.ValuesAt X x) {r : ℚ}
    (hr : (r : ℝ) < x) : v.Holds (X.gt r) := (h.2.2 r).1 hr

/-- `not_holds_gt_of_valuesAt`.
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma not_holds_gt_of_valuesAt {v : PCWorld} {X : LUV} {x : ℝ} (h : v.ValuesAt X x) {r : ℚ}
    (hr : x < (r : ℝ)) : ¬ v.Holds (X.gt r) := (h.2.2 r).2 hr

/-- A world holding `X.gt r` values `X` at or above `r` (contrapositive of the second clause).
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma le_of_holds_gt_of_valuesAt {v : PCWorld} {X : LUV} {x : ℝ} (h : v.ValuesAt X x) {r : ℚ}
    (hr : v.Holds (X.gt r)) : (r : ℝ) ≤ x :=
  le_of_not_gt fun hlt => not_holds_gt_of_valuesAt h hlt hr

/-- **Every world valuing `X` holds all monotonicity facts** (the cut is downward closed).
Source: mandate design decision 2 ("every world that values `X` holds all of them")
Kind: L
Fidelity: exact -/
theorem holds_monoFacts_of_valuesAt {v : PCWorld} {X : LUV} {x : ℝ} (h : v.ValuesAt X x)
    (R : Finset ℚ) : v.ConsistentWith (monoFacts X R) := by
  intro φ hφ
  obtain ⟨r, -, r', -, hlt, rfl⟩ := mem_monoFacts.mp hφ
  intro hr
  have hle : (r : ℝ) ≤ x := le_of_holds_gt_of_valuesAt h hr
  have hlt' : (r' : ℝ) < x := lt_of_lt_of_le (by exact_mod_cast hlt) hle
  exact holds_gt_of_valuesAt h hlt'

/-- **Every world valuing `X` holds the range facts, provided `1 ∉ R`.** At `r = 1` FAF's cut
semantics leaves `X.gt 1` undetermined for a world valuing `X` at `1` (module header; findings
F-12), which is why the clause is needed.
Source: mandate design decision 2 (corrected at the boundary)
Kind: L
Fidelity: weaker: the mandate claims it without `1 ∉ R`; that claim is false at `r = 1` -/
theorem holds_rangeFacts_of_valuesAt {v : PCWorld} {X : LUV} {x : ℝ} (h : v.ValuesAt X x)
    {R : Finset ℚ} (h1 : (1 : ℚ) ∉ R) : v.ConsistentWith (rangeFacts X R) := by
  intro φ hφ
  rcases mem_rangeFacts.mp hφ with ⟨r, -, hlt, rfl⟩ | ⟨r, hr, hle, rfl⟩
  · exact holds_gt_of_valuesAt h (lt_of_lt_of_le (by exact_mod_cast hlt) h.1)
  · rw [PCWorld.holds_neg]
    have hne : r ≠ 1 := fun heq => h1 (heq ▸ hr)
    have hgt : (1 : ℚ) < r := lt_of_le_of_ne hle (Ne.symm hne)
    exact not_holds_gt_of_valuesAt h (lt_of_le_of_lt h.2.1 (by exact_mod_cast hgt))

/-! ## Real-value coherence (B): a finite mixture of point values -/

/-- **`RVC_B`** (slide p. 7, (B)): on the thresholds `R`, `V` is the threshold-belief profile of a
finite mixture of point values in `[0,1]`: `V ⌜X > r⌝ = ∑ᵢ wᵢ·[r < xᵢ]`. On finitely many
thresholds a probability measure on `[0,1]` is matched by a finite mixture, so this is not a
weakening of "consistent with some overall distribution on `x`"; the measure form is an optional
corollary not shipped here. **Boundary convention**: the indicator is strict, `[r < x]`, so a
point value `x` prices `⌜X > x⌝` at `0`; FAF's `ValuesAt` is agnostic at `r = x`. This is why
`rvcB_limit` needs `1 ∉ R` (F-12) while `rvcB_iff_twoAxiom` needs no such clause (`RVC_B` itself
forces `V ⌜X > 1⌝ = 0`, consistent with the `1 ≤ r` range fact).
Source: bli-slides-014 (B); bli-paper-048; [[bli-program-desiderata]] D-RVC(B)
Kind: D
Fidelity: exact (finite-mixture form) -/
def RVC_B (V : Sentence → ℝ) (X : LUV) (R : Finset ℚ) : Prop :=
  ∃ (k : ℕ) (x : Fin k → ℝ) (w : Fin k → ℝ),
    (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    ∀ r ∈ R, V (X.gt r) = ∑ i, w i * (if (r : ℝ) < x i then 1 else 0)

/-- **The antitone characterization** of threshold beliefs: values in `[0,1]`, antitone in the
threshold, `1` below `0`, `0` at or above `1`. Stated over any ordered field so that the same
statement serves the rational two-axiom side and the real mixture side.
Source: mandate T2.1 route ("the cheap characterization first")
Kind: D
Fidelity: n/a -/
def ThresholdAntitone {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (V : Sentence → K) (X : LUV) (R : Finset ℚ) : Prop :=
  (∀ r ∈ R, 0 ≤ V (X.gt r) ∧ V (X.gt r) ≤ 1) ∧
  (∀ r ∈ R, ∀ r' ∈ R, r' < r → V (X.gt r) ≤ V (X.gt r')) ∧
  (∀ r ∈ R, r < 0 → V (X.gt r) = 1) ∧
  (∀ r ∈ R, 1 ≤ r → V (X.gt r) = 0)

/-- The antitone characterization is invariant under the cast `ℚ → ℝ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma thresholdAntitone_cast_iff {V : Sentence → ℚ} {X : LUV} {R : Finset ℚ} :
    ThresholdAntitone (fun φ => (V φ : ℝ)) X R ↔ ThresholdAntitone V X R := by
  simp only [ThresholdAntitone]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨fun r hr => ⟨by exact_mod_cast (h0 r hr).1, by exact_mod_cast (h0 r hr).2⟩,
      fun r hr r' hr' hlt => by exact_mod_cast h1 r hr r' hr' hlt,
      fun r hr hlt => by exact_mod_cast h2 r hr hlt,
      fun r hr hle => by exact_mod_cast h3 r hr hle⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨fun r hr => ⟨by exact_mod_cast (h0 r hr).1, by exact_mod_cast (h0 r hr).2⟩,
      fun r hr r' hr' hlt => by exact_mod_cast h1 r hr r' hr' hlt,
      fun r hr hlt => by exact_mod_cast h2 r hr hlt,
      fun r hr hle => by exact_mod_cast h3 r hr hle⟩

/-! ## Real-value coherence (E): additivity of the grid expectation -/

/-- A world **values `Z` as the sum of `X` and `Y`**: it values `X` at `x`, `Y` at `y` and `Z` at
`x + y` (the paper's `Θ ⊢ Z = X + Y` in FAF's determined-value form; for a `[0,1]`-LUV `Z` this
presupposes `x + y ≤ 1`).
Source: mandate design decision 4; `main.tex:349` ("the expectation of `A + B`")
Kind: D
Fidelity: exact (determined-value form) -/
def SumValued (v : PCWorld) (X Y Z : LUV) : Prop :=
  ∃ x y : ℝ, v.ValuesAt X x ∧ v.ValuesAt Y y ∧ v.ValuesAt Z (x + y)

/-- **Exact additivity of FAF's grid expectation at precision `k`**: `𝔼ᵏ_V(X) + 𝔼ᵏ_V(Y) = 𝔼ᵏ_V(Z)`.
The refuted object of `rvcE_exact_fails` (it fails at a single world valuing `Z = X + Y`).
Source: `main.tex:349`; bli-slides-014 (E); [[bli-program-desiderata]] I9
Kind: D
Fidelity: exact -/
def RVC_E_exact (V : Valuation) (k : ℕ) (X Y Z : LUV) : Prop :=
  X.expectApprox V k + Y.expectApprox V k = Z.expectApprox V k

/-- **ε-additivity of FAF's grid expectation at precision `k`**.
Source: bli-slides-014 (E); [[bli-program-desiderata]] D-RVC(E_ε), I9
Kind: D
Fidelity: exact -/
def RVC_E_eps (V : Valuation) (k : ℕ) (X Y Z : LUV) (ε : ℝ) : Prop :=
  |X.expectApprox V k + Y.expectApprox V k - Z.expectApprox V k| ≤ ε

/-- `payout_mem_Icc`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_mem_Icc (v : PCWorld) (φ : Sentence) : 0 ≤ v.payout φ ∧ v.payout φ ≤ 1 := by
  unfold PCWorld.payout
  split_ifs <;> norm_num

/-- `payout_of_holds`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_of_holds {v : PCWorld} {φ : Sentence} (h : v.Holds φ) : v.payout φ = 1 := by
  unfold PCWorld.payout
  rw [if_pos h]

/-- `payout_of_not_holds`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_of_not_holds {v : PCWorld} {φ : Sentence} (h : ¬ v.Holds φ) : v.payout φ = 0 := by
  unfold PCWorld.payout
  rw [if_neg h]

/-- A world's payout on a threshold sentence, given a value, is the indicator `[r < x]` for
every threshold `r ≠ x`. (At `r = x` nothing is determined.)
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma payout_gt_of_valuesAt {v : PCWorld} {X : LUV} {x : ℝ} (h : v.ValuesAt X x) {r : ℚ}
    (hne : (r : ℝ) ≠ x) : v.payout (X.gt r) = if (r : ℝ) < x then 1 else 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [if_pos hlt, PCWorld.payout, if_pos (holds_gt_of_valuesAt h hlt)]
  · rw [if_neg (not_lt.mpr hgt.le), PCWorld.payout, if_neg (not_holds_gt_of_valuesAt h hgt)]

end Cleanroom.Bli.BliRvcUi
