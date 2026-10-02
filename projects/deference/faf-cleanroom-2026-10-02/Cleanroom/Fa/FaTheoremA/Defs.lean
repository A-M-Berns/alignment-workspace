import Cleanroom.Found.LiQuoteLane.Defs
import Cleanroom.Found.LiQuoteLane.Feature
import Cleanroom.Found.LiAsympCalc.Ramp
import LogicalInduction.Construction.Quotation.DeferralFibre
import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Framework.Affine

/-!
# `fa-theorem-a` · Defs: the quote feature, its ramps, and their generability (T1, T2)

The definitions module of the package `Cleanroom.Fa.FaTheoremA` ([[fa-theorem-a-mandate]]).
Everything is stated over FAF's objects (`LUV`, `History`, `EF`, `DeferralFunction`,
`PGenerableWeighting`, `ctsIndFeature`) and `li-quote-lane`'s `CrossQuotePackage`.

* `quoteFeature Y n` is `A`'s day-`n` expectation of the quote LUV `Y n` as an expressible
  feature of `A`'s *own* day-`n` prices (FAF's `priceFeature` of FAF's `expectAffine`); it denotes
  `𝔼^A_n(Y_n)` (`quoteFeature_denote`, T1).
* `quoteRampAbove Y t δ n` is the gate `u_n := Ind_δ(a_n > t)` of
  [[faithful-acceleration-result]] §3 (FAF's `ctsIndFeature` at constant width and threshold);
  `quoteRampBelow` is the dual gate `Ind_δ(a_n < t)` of vq-wiki-2-013.
* **T2 (headline):** for any e.c. quote family (`LUV.MachineThresholdCodeSeq Y`, the
  `quote_codes` field of a `CrossQuotePackage`), the quote feature and both ramps are
  `PGenerableWeighting` — FAF's `def:ece` class exactly, assembled from FAF's own combinators
  (`PolySequence.priceFeature_polySeg`, `priceFeature_rank`, `priceFeature_closed`,
  `ctsIndFeature_generated`). This is the certificate the corpus never wrote ("a market is never
  stale to itself", [[delay-program]] §2): the gate is generable from `A`'s market alone.

Scope: one-way — every object here is a feature of `A`'s own prices; `H` enters only through the
LUV `Y n` of `A`'s language, which the quote package (`CrossQuotePackage`) ties to `H`'s
realized expectation. Nothing here reads `H`'s prices.
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. Definitions of record -/

/-- **The quote feature** `𝔼^A_n(Y_n)` as an expressible feature of `A`'s own day-`n` prices: the
price feature of the day-`n` threshold bundle (`LUV.expectAffine`, precision `n + 1`) of the
quote LUV `Y n`. Denotes `(Y n).expect A n` (`quoteFeature_denote`). Mirrors `li-quote-lane`'s
`ledgerFeature` with the LUV family `Y` free. Scope: one-way.
Source: [[faithful-acceleration-result]] §3 ("the quote is a rational combination of `A`'s own day-`n` prices, so it is an expressible feature of rank `n`"; vq-wiki-030)
Kind: D
Fidelity: exact (FAF's `AffineCombination.priceFeature` of FAF's `LUV.expectAffine`)
Hyps: n/a -/
def quoteFeature (Y : ℕ → LUV) (n : ℕ) : EF := ((Y n).expectAffine (n + 1)).priceFeature n

/-- **The upper gate** `u_n := Ind_δ(a_n > t)`: FAF's ramp `ctsIndFeature` at constant width `δ`
of the quote feature against the constant threshold `t`. Denotes `ctsInd δ (𝔼^A_n(Y_n)) t`
(`quoteRampAbove_denote`, for `0 < δ`): positive iff `t < a_n`, equal to `1` iff `a_n ≥ t + δ`.
Scope: one-way.
Source: [[faithful-acceleration-result]] §3 (`u_n := Ind_δ(a_n > t)`; vq-wiki-030); [[delay-program]] §2 lines 60–66
Kind: D
Fidelity: exact (FAF's `ctsInd δ x y = clip01 ((x − y)/δ)`)
Hyps: n/a -/
def quoteRampAbove (Y : ℕ → LUV) (t δ : ℚ) (n : ℕ) : EF :=
  ctsIndFeature (fun _ => δ) (quoteFeature Y) (fun _ => EF.const t) n

/-- **The dual (lower) gate** `u⁻_n := Ind_δ(a_n < t)`: the ramp of the constant threshold `t`
against the quote feature. Denotes `ctsInd δ t (𝔼^A_n(Y_n))` (`quoteRampBelow_denote`): positive
iff `a_n < t`, equal to `1` iff `a_n ≤ t − δ`. Scope: one-way.
Source: [[route-recurring-ccee]] §4 ("Dual gate: with `u⁻_n := Ind_δ(a_n < t)` …"; vq-wiki-2-013)
Kind: D
Fidelity: exact
Hyps: n/a -/
def quoteRampBelow (Y : ℕ → LUV) (t δ : ℚ) (n : ℕ) : EF :=
  ctsIndFeature (fun _ => δ) (fun _ => EF.const t) (quoteFeature Y) n

/-- `a_n := 𝔼^A_n(Y_n)`, the advisor's day-`n` quote, as a real sequence.
Source: [[faithful-acceleration-result]] §1 (the object `a_n`); [[delay-program]] §2
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable abbrev quoteSeq (Y : ℕ → LUV) (A : History) : ℕ → ℝ := fun n => (Y n).expect A n

/-- `Y_n := 𝔼^H_{f(n)}(X_n)`, the human's realized day-`f n` expectation of `X_n` — the `truth`
of every unbiasedness statement of this package. For a fixed `X` pass `fun _ => X`.
Source: [[faithful-acceleration-result]] §1 (the object `Y_n`); [[delay-program]] §2
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable abbrev realized (H : History) (f : DeferralFunction) (X : ℕ → LUV) : ℕ → ℝ :=
  fun n => (X n).expect H (f.f n)

/-- **The gated upper ramp** `E_n · Ind_δ(a_n > t)`: the upper gate restricted to a day-set
feature `E` (Lemma P's `E ⊆ ℕ⁺`, rendered as a `{0,1}`-valued generable feature).
Source: [[route-negative-introspective]] §7 (Lemma P; vq-wiki-058)
Kind: D
Fidelity: exact
Hyps: n/a -/
def gatedAbove (Y : ℕ → LUV) (E : ℕ → EF) (t δ : ℚ) (n : ℕ) : EF :=
  EF.mul (E n) (quoteRampAbove Y t δ n)

/-- **The gated lower ramp** `E_n · Ind_δ(a_n < t)`.
Source: [[route-negative-introspective]] §7 (Lemma P; vq-wiki-058)
Kind: D
Fidelity: exact
Hyps: n/a -/
def gatedBelow (Y : ℕ → LUV) (E : ℕ → EF) (t δ : ℚ) (n : ℕ) : EF :=
  EF.mul (E n) (quoteRampBelow Y t δ n)

/-! ## B. T1: the features denote what they name -/

/-- **T1.** The quote feature denotes the quote: `(quoteFeature Y n).denote A = 𝔼^A_n(Y_n)`.
Source: [[faithful-acceleration-result]] §3 (vq-wiki-030); FAF `priceFeature_denote`, `expectAffine_price`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteFeature_denote (Y : ℕ → LUV) (A : History) (n : ℕ) :
    (quoteFeature Y n).denote A = (Y n).expect A n := by
  unfold quoteFeature
  rw [AffineCombination.priceFeature_denote, LUV.expectAffine_price]

/-- **T1.** The upper gate denotes the ramp `ctsInd δ a_n t` (positive width).
Source: [[faithful-acceleration-result]] §3 (vq-wiki-030); FAF `ctsIndFeature_denote`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteRampAbove_denote (Y : ℕ → LUV) {t δ : ℚ} (hδ : 0 < δ) (A : History) (n : ℕ) :
    (quoteRampAbove Y t δ n).denote A = ctsInd δ ((Y n).expect A n) (t : ℝ) := by
  unfold quoteRampAbove
  rw [ctsIndFeature_denote _ _ _ (fun _ => hδ), quoteFeature_denote]
  simp

/-- **T1.** The lower gate denotes the ramp `ctsInd δ t a_n` (positive width).
Source: [[route-recurring-ccee]] §4 (vq-wiki-2-013); FAF `ctsIndFeature_denote`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteRampBelow_denote (Y : ℕ → LUV) {t δ : ℚ} (hδ : 0 < δ) (A : History) (n : ℕ) :
    (quoteRampBelow Y t δ n).denote A = ctsInd δ (t : ℝ) ((Y n).expect A n) := by
  unfold quoteRampBelow
  rw [ctsIndFeature_denote _ _ _ (fun _ => hδ), quoteFeature_denote]
  simp

/-- The upper gate is positive exactly when the quote is above the threshold (no false positives).
Source: [[route-recurring-ccee]] §4 ("the ramp has no false positives, so `u_i > 0 ⇒ a_i > t`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteRampAbove_pos_iff (Y : ℕ → LUV) {t δ : ℚ} (hδ : 0 < δ) (A : History) (n : ℕ) :
    0 < (quoteRampAbove Y t δ n).denote A ↔ (t : ℝ) < (Y n).expect A n := by
  rw [quoteRampAbove_denote Y hδ, ctsInd_pos_iff hδ]

/-- The upper gate is `1` exactly when the quote is at least `t + δ`.
Source: [[faithful-acceleration-result]] §4.2 ("infinitely many days carry weight `1`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteRampAbove_eq_one_iff (Y : ℕ → LUV) {t δ : ℚ} (hδ : 0 < δ) (A : History) (n : ℕ) :
    (quoteRampAbove Y t δ n).denote A = 1 ↔ (δ : ℝ) ≤ (Y n).expect A n - t := by
  rw [quoteRampAbove_denote Y hδ, ctsInd_eq_one_iff hδ]

/-- The lower gate is positive exactly when the quote is below the threshold.
Source: [[route-recurring-ccee]] §4 (vq-wiki-2-013)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteRampBelow_pos_iff (Y : ℕ → LUV) {t δ : ℚ} (hδ : 0 < δ) (A : History) (n : ℕ) :
    0 < (quoteRampBelow Y t δ n).denote A ↔ (Y n).expect A n < (t : ℝ) := by
  rw [quoteRampBelow_denote Y hδ, ctsInd_pos_iff hδ]

/-- The lower gate is `1` exactly when the quote is at most `t − δ`.
Source: [[route-recurring-ccee]] §4 (vq-wiki-2-013)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteRampBelow_eq_one_iff (Y : ℕ → LUV) {t δ : ℚ} (hδ : 0 < δ) (A : History) (n : ℕ) :
    (quoteRampBelow Y t δ n).denote A = 1 ↔ (δ : ℝ) ≤ (t : ℝ) - (Y n).expect A n := by
  rw [quoteRampBelow_denote Y hδ, ctsInd_eq_one_iff hδ]

/-- The upper gate takes values in `[0,1]`.
Source: none: infrastructure (FAF `ctsInd_mem_Icc`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem quoteRampAbove_mem_Icc (Y : ℕ → LUV) {t δ : ℚ} (hδ : 0 < δ) (A : History) (n : ℕ) :
    0 ≤ (quoteRampAbove Y t δ n).denote A ∧ (quoteRampAbove Y t δ n).denote A ≤ 1 := by
  rw [quoteRampAbove_denote Y hδ]
  exact ctsInd_mem_Icc δ _ _

/-- The lower gate takes values in `[0,1]`.
Source: none: infrastructure (FAF `ctsInd_mem_Icc`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem quoteRampBelow_mem_Icc (Y : ℕ → LUV) {t δ : ℚ} (hδ : 0 < δ) (A : History) (n : ℕ) :
    0 ≤ (quoteRampBelow Y t δ n).denote A ∧ (quoteRampBelow Y t δ n).denote A ≤ 1 := by
  rw [quoteRampBelow_denote Y hδ]
  exact ctsInd_mem_Icc δ _ _

/-- The gated upper ramp denotes the product `E_n · ctsInd δ a_n t`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gatedAbove_denote (Y : ℕ → LUV) (E : ℕ → EF) {t δ : ℚ} (hδ : 0 < δ) (A : History)
    (n : ℕ) :
    (gatedAbove Y E t δ n).denote A = (E n).denote A * ctsInd δ ((Y n).expect A n) (t : ℝ) := by
  unfold gatedAbove
  rw [EF.denote_mul, Pi.mul_apply, quoteRampAbove_denote Y hδ]

/-- The gated lower ramp denotes the product `E_n · ctsInd δ t a_n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gatedBelow_denote (Y : ℕ → LUV) (E : ℕ → EF) {t δ : ℚ} (hδ : 0 < δ) (A : History)
    (n : ℕ) :
    (gatedBelow Y E t δ n).denote A = (E n).denote A * ctsInd δ (t : ℝ) ((Y n).expect A n) := by
  unfold gatedBelow
  rw [EF.denote_mul, Pi.mul_apply, quoteRampBelow_denote Y hδ]

/-! ## C. T2: the ramp of the quote is a legal feature progression (headline) -/

/-- **T2 (headline). The quote feature is a legal feature progression** — FAF's
`PGenerableWeighting` exactly: machine-metered serialization (`PolySequence.priceFeature_polySeg`
on the day-indexed expectation mesh, whose `PolySequence` certificate is FAF's
`expectAffineSeq_polySequence` at the e.c. certificate `hY`), rank `≤ n` (every price inside is a
day-`n` price of `A` — this is why a ramp of `A`'s *future* quote would not be legal), closed
denotation. The e.c. hypothesis `hY` is the `quote_codes` field of a `CrossQuotePackage`.
Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. The quote LUV `Y n` lives in `A`'s language; `H` enters only through the quote package.
Source: [[delay-program]] §6 T2 ("`Ind_δ` of the quote is an expressible feature by LI Def. 4.3.2's own closing remark, generable from `A`'s market alone"); root-fa-024; vq-wiki-030; [[faithful-acceleration-result]] §3
Kind: C
Fidelity: exact
Hyps: (a) none (`hY` is the e.c. certificate of the quote family, FAF's own `def:ec` metering) -/
theorem quoteFeature_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) :
    PGenerableWeighting (quoteFeature Y) := by
  have hpoly := LUV.expectAffineSeq_polySequence Y hY
  refine { polySeg := ?_, rank_le := ?_, closed := ?_ }
  · refine (hpoly.priceFeature_polySeg.comp (UnaryRuler.id.pair UnaryRuler.id)).of_eq
      fun n => ?_
    simp only [Nat.unpair_pair]
    rfl
  · intro n
    refine AffineCombination.priceFeature_rank _ (Nat.zero_le n) (by simp [LUV.expectAffine]) ?_
    intro p hp
    simp only [LUV.expectAffine, List.mem_map, List.mem_range] at hp
    obtain ⟨i, -, rfl⟩ := hp
    simp
  · intro n ρ V
    exact hpoly.priceFeature_closed n n ρ V

/-- **T2 (headline). The upper gate `Ind_δ(a_n > t)` is a legal feature progression** (FAF's
`PGenerableWeighting`), by FAF's ramp compiler `ctsIndFeature_generated` on the quote feature
against a constant threshold, with the constant width written by `MachineRatCodes.const`. This
is the certificate behind "`u` is `ℙ^A`-generable with no visibility of `H` whatsoever"
([[delay-program]] §2) — a (a)-grade fact assembled from FAF's combinators, not an assumption.
Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices.
Source: root-fa-024 ("the `PGenerableWeighting` certificate for a ramp of an expectation feature is the work"); vq-wiki-030; [[delay-program]] §6 T2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem quoteRampAbove_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (t δ : ℚ) : PGenerableWeighting (quoteRampAbove Y t δ) :=
  ctsIndFeature_generated _ _ _ (MachineRatCodes.const (1 / δ)) (quoteFeature_pgenerable Y hY)
    (pgenerableWeighting_const t)

/-- **T2 (headline), dual.** The lower gate `Ind_δ(a_n < t)` is a legal feature progression.
Scope: one-way.
Source: [[route-recurring-ccee]] §4 (vq-wiki-2-013, the dual gate); root-fa-024
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem quoteRampBelow_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (t δ : ℚ) : PGenerableWeighting (quoteRampBelow Y t δ) :=
  ctsIndFeature_generated _ _ _ (MachineRatCodes.const (1 / δ)) (pgenerableWeighting_const t)
    (quoteFeature_pgenerable Y hY)

/-- The gated upper ramp is a legal feature progression when the day-set feature is (FAF's
`PGenerableWeighting.mul`).
Source: [[route-negative-introspective]] §7 (Lemma P needs `E` e.c.; vq-wiki-058)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem gatedAbove_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) {E : ℕ → EF}
    (hE : PGenerableWeighting E) (t δ : ℚ) : PGenerableWeighting (gatedAbove Y E t δ) :=
  PGenerableWeighting.mul hE (quoteRampAbove_pgenerable Y hY t δ)

/-- The gated lower ramp is a legal feature progression when the day-set feature is.
Source: [[route-negative-introspective]] §7 (vq-wiki-058)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem gatedBelow_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) {E : ℕ → EF}
    (hE : PGenerableWeighting E) (t δ : ℚ) : PGenerableWeighting (gatedBelow Y E t δ) :=
  PGenerableWeighting.mul hE (quoteRampBelow_pgenerable Y hY t δ)

end Cleanroom.Fa.FaTheoremA
