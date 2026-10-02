import Cleanroom.Deference.DefFrozenSibling.Defs
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.TimelyLearning
import LogicalInduction.Construction.Quotation.DeferralFibre

/-!
# `def-frozen-sibling` · Gated: provability induction along an e.c. sub-fragment

The engine behind every on-`G` theorem of the package ([[def-frozen-sibling-mandate]] T3 route):
FAF's vanishing-error affine provability induction
(`PolySequence.affine_provind_theory_tendsto_zero`, `Properties/AffineCoherence.lean`) applied to
an affine family **gated by a unary ruler** `t` — the family is the real combination on
`G' = {n | t n = 0}` and a harmless constant combination (`𝟙(⊤)` against `⊤`) off it. The gating
is done at the level of the LUV and sentence families (`gatedLuv`, `gatedSentence`), where FAF's
`MachineSentenceCodes.ifZero` certifies the dispatch; the `PolySequence` of the gap combination is
then FAF's `expectAffineSeq_polySequence` plus `sentenceAffine_polySequence`, joined by
`PolySequence.add` (`Construction/Quotation/DeferralFibre.lean`, in the import closure of
`Construction.LUV.Endpoints`). No `MachineThresholdCodeSeq.ifZero` is needed and none is asked of
FAF: the LUV-level gate is one `MachineSentenceCodes.ifZero` on the threshold-sentence stream.

Two engines:

* `gated_pin` — **two-sided, a LUV family against a sentence family**: if on `G'` every
  completed-theory world values `X n` at `y n` (`hdet`, from settlement) and `y n` is eventually
  within every `ε` of the world's payout of `φ n` (`hgap`, from the fragment's tolerance or from an
  earlier pin), then `𝔼^P_n(X_n)` and `P_n(φ_n)` agree along `G'` (`AgreeAlong`). This is T3's
  A-side at `X = C_n`, `φ = P^{(n)}`, `y = Y`, and T3's H-side at `y = a` in `Hplus`'s process.
* `gated_three_ge` — **one-sided, three sentences**: if on `G'` every completed-theory world gives
  `payout φ₁ + c·payout φ₂ − payout φ₃ ≥ 0`, the prices satisfy it asymptotically along `G'`. This
  is T4's two-option Value at `φ₁ = P ∧ q`, `φ₂ = ∼q`, `φ₃ = P`.

Nothing here is about the construction: `P`, `DP`, `t`, the families are free. Scope: one-way
(a single reader `P`).
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology AffineCombination

/-! ## A. Gated families -/

/-- The LUV family `X` gated by the ruler `t`: `X n` on `G' = {n | t n = 0}`, FAF's `𝟙(⊤)` off it.
Source: none: infrastructure (mandate T3, "gating by the ruler")
Kind: D
Fidelity: n/a -/
def gatedLuv (t : ℕ → ℕ) (X : ℕ → LUV) (n : ℕ) : LUV :=
  if t n = 0 then X n else LUV.indicatorOf (⊤ : Sentence)

/-- The sentence family `φ` gated by `t`: `φ n` on `G'`, `⊤` off it (the pattern of
`li-projection`'s `decided_fragment_agree_daySet`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def gatedSentence (t : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) : Sentence :=
  if t n = 0 then φ n else ⊤

/-- `gatedLuv_of_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma gatedLuv_of_zero {t : ℕ → ℕ} {X : ℕ → LUV} {n : ℕ} (h : t n = 0) :
    gatedLuv t X n = X n := by simp [gatedLuv, h]

/-- `gatedSentence_of_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma gatedSentence_of_zero {t : ℕ → ℕ} {φ : ℕ → Sentence} {n : ℕ} (h : t n = 0) :
    gatedSentence t φ n = φ n := by simp [gatedSentence, h]

/-- The gated LUV family is e.c. when `X` is and `t` is a unary ruler: one
`MachineSentenceCodes.ifZero` on the threshold-sentence stream, the test being `t` read off the
day coordinate of the paired index.
Source: none: infrastructure (FAF `MachineSentenceCodes.ifZero`, `indicatorOf_machineThresholdCodeSeq`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gatedLuv_codes {t : ℕ → ℕ} (ht : UnaryRuler t) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) : LUV.MachineThresholdCodeSeq (gatedLuv t X) := by
  have hT : LUV.MachineThresholdCodeSeq (fun _ : ℕ => LUV.indicatorOf (⊤ : Sentence)) :=
    LUV.indicatorOf_machineThresholdCodeSeq (MachineSentenceCodes.const ⊤)
  unfold LUV.MachineThresholdCodeSeq at hX hT ⊢
  refine (MachineSentenceCodes.ifZero hX hT (ht.comp UnaryRuler.unpairFst)).of_eq (fun m => ?_)
  simp only [gatedLuv]
  split_ifs <;> rfl

/-- The gated sentence family is e.c.
Source: none: infrastructure (FAF `MachineSentenceCodes.ifZero`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gatedSentence_codes {t : ℕ → ℕ} (ht : UnaryRuler t) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) : MachineSentenceCodes (gatedSentence t φ) :=
  (MachineSentenceCodes.ifZero hφ (MachineSentenceCodes.const ⊤) ht).of_eq (fun _ => rfl)

/-! ## B. World-side facts -/

/-- Every world pays `1` on `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem payout_top (w : PCWorld) : w.payout (⊤ : Sentence) = 1 := by
  unfold PCWorld.payout
  rw [if_pos (PCWorld.holds_top w)]

/-- **The mesh error at one world**: a world valuing `X` at `y` has its precision-`k` threshold
mesh within `1/k` of `y` (`def-tracking-pin`'s `determinedVia_expectApprox_near` at a single world;
FAF's `PCWorld.expectApprox_near_ofGrid`).
Source: none: infrastructure (FAF `lem:conluvapprox`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem valuesAt_expectApprox_near {X : LUV} {y : ℝ} {v : PCWorld} (hval : v.ValuesAt X y)
    {k : ℕ} (hk : 0 < k) : |X.expectApprox v.payout k - y| ≤ 1 / k := by
  have hgrid : ∀ i : ℕ, i < k →
      (((i : ℝ) / k < y → v.Holds (X.gt ((i : ℚ) / (k : ℚ)))) ∧
        (y < (i : ℝ) / k → ¬ v.Holds (X.gt ((i : ℚ) / (k : ℚ))))) := by
    intro i _
    have hc : (((i : ℚ) / (k : ℚ) : ℚ) : ℝ) = (i : ℝ) / (k : ℝ) := by
      push_cast
      ring
    have := hval.2.2 ((i : ℚ) / (k : ℚ))
    rw [hc] at this
    exact this
  exact PCWorld.expectApprox_near_ofGrid hval.1 hval.2.1 hk hgrid

/-! ## C. The gap combination `mesh(X_n) − φ_n`, gated -/

/-- The gap combination of a LUV family against a sentence family, gated by `t`: the day-`n` mesh
of `gatedLuv t X n` minus one share of `gatedSentence t φ n`. On `G'` it is `mesh(X_n) − φ_n`;
off `G'` it is `mesh(𝟙⊤) − ⊤`, valued within `1/(n+1)` of `0` in every world.
Source: none: infrastructure (mandate T3's `Z n := if t n = 0 then C_n − 𝟙(contract n) else 0`, at the sentence rather than the indicator LUV)
Kind: D
Fidelity: n/a -/
def gapComb (t : ℕ → ℕ) (X : ℕ → LUV) (φ : ℕ → Sentence) (n : ℕ) : AffineCombination :=
  ((gatedLuv t X n).expectAffine (n + 1)).add (sentenceAffine (gatedSentence t φ) n).neg

/-- The gap combination is a `PolySequence` (FAF's `expectAffineSeq_polySequence` for the mesh,
`sentenceAffine_polySequence` for the share, `PolySequence.add`/`.neg` for the join).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def gapComb_polySequence {t : ℕ → ℕ} (ht : UnaryRuler t) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) :
    PolySequence (gapComb t X φ) :=
  (LUV.expectAffineSeq_polySequence (gatedLuv t X) (gatedLuv_codes ht hX)).add
    (sentenceAffine_polySequence (gatedSentence t φ) (gatedSentence_codes ht hφ)).neg

/-- `gapComb_price`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gapComb_price (t : ℕ → ℕ) (X : ℕ → LUV) (φ : ℕ → Sentence) (P : History) (n : ℕ) :
    (gapComb t X φ n).price P n = (gatedLuv t X n).expect P n - P n (gatedSentence t φ n) := by
  rw [gapComb, add_price, neg_price, LUV.expectAffine_price, sentenceAffine_price]
  ring

/-- `gapComb_value`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gapComb_value (t : ℕ → ℕ) (X : ℕ → LUV) (φ : ℕ → Sentence) (P : History) (w : PCWorld)
    (n : ℕ) :
    (gapComb t X φ n).value P w.payout =
      (gatedLuv t X n).expectApprox w.payout (n + 1) - w.payout (gatedSentence t φ n) := by
  rw [gapComb, add_value, neg_value, LUV.expectAffine_value, sentenceAffine_value_payout]
  ring

/-- `gapComb_magnitude_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gapComb_magnitude_le (t : ℕ → ℕ) (X : ℕ → LUV) (φ : ℕ → Sentence) (P : History)
    (n : ℕ) : (gapComb t X φ n).magnitude P ≤ 2 := by
  rw [gapComb, add_magnitude, neg_magnitude, sentenceAffine_magnitude]
  linarith [(gatedLuv t X n).expectAffine_magnitude_le_one P (n + 1)]

/-- `gapComb_boundedPrices`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gapComb_boundedPrices (t : ℕ → ℕ) (X : ℕ → LUV) (φ : ℕ → Sentence) (P : History)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] : BoundedAffinePrices (gapComb t X φ) P := by
  have hP : ∀ m ψ, 0 ≤ P m ψ ∧ P m ψ ≤ 1 := fun m ψ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) m ψ
  refine ⟨2, by norm_num, fun n m => ?_⟩
  rw [gapComb, add_price, neg_price, sentenceAffine_price, price, LUV.expectAffine_value]
  have h0 := (gatedLuv t X n).expectApprox_nonneg (P m) (n + 1) (fun s => (hP m s).1)
  have h1 := (gatedLuv t X n).expectApprox_le_one (P m) (n + 1) (fun s => (hP m s).2)
  obtain ⟨h2, h3⟩ := hP m (gatedSentence t φ n)
  rw [abs_le]
  constructor <;> linarith

/-! ## D. Engine 1: two-sided pinning of a LUV family to a sentence family along `G'` -/

/-- **Gated pinning (the engine of T3, both sides).** For a reader `P` over `DP` (every stage
satisfiable), a unary ruler `t`, an e.c. LUV family `X` and an e.c. sentence family `φ`: if on
`G' = {n | t n = 0}` every completed-theory world values `X n` at `y n` (settlement), and
eventually on `G'` the value `y n` is within every `ε` of every completed-theory world's payout of
`φ n`, then the reader's day-`n` expectation of `X n` and its day-`n` price of `φ n` agree along
`G'`. Route: the gated gap combination is a `PolySequence` with bounded prices and magnitude; its
completed-theory value is within `1/(n+1) + ε` of `0` on `G'` (the mesh error at `y n`, then
`hgap`) and within `1/(n+1)` of `0` off `G'` (`𝟙⊤` against `⊤`); FAF's vanishing-error affine
provability induction gives price `→ 0`; on `G'` the price is `𝔼^P_n(X_n) − P_n(φ_n)`. **No
generability of `y` is asked**: the target enters only through world values. Reader `P`; one-way.
Source: mandate T3 (the route); FAF `PolySequence.affine_provind_theory_tendsto_zero` (`thm:affprovind`, vanishing-error form)
Kind: C
Fidelity: n/a (infrastructure; the instances carry the fidelity)
Hyps: (a) none -/
theorem gated_pin (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {t : ℕ → ℕ} (ht : UnaryRuler t) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) (y : ℕ → ℝ)
    (hdet : ∀ n, t n = 0 → ∀ w : PCWorld, w.ConsistentWithTheory DP → w.ValuesAt (X n) (y n))
    (hgap : ∀ ε > 0, ∀ᶠ n in atTop, t n = 0 → ∀ w : PCWorld, w.ConsistentWithTheory DP →
      |y n - w.payout (φ n)| ≤ ε) :
    AgreeAlong t (fun n => (X n).expect P n) (fun n => P n (φ n)) := by
  have hpoly := gapComb_polySequence ht hX hφ
  have hmag : ∃ C : ℝ, ∀ n, (gapComb t X φ n).magnitude P ≤ C :=
    ⟨2, fun n => gapComb_magnitude_le t X φ P n⟩
  have hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ w : PCWorld,
      w.ConsistentWithTheory DP → |(gapComb t X φ n).value P w.payout| ≤ ε := by
    intro ε hε
    have hlim1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlim1.eventually (eventually_le_nhds (half_pos hε)),
      hgap (ε / 2) (half_pos hε)] with n hn1 hn2 w hw
    rw [gapComb_value]
    have hk : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) = 1 / ((n : ℝ) + 1) := by push_cast; rfl
    by_cases h0 : t n = 0
    · simp only [gatedLuv, gatedSentence, if_pos h0]
      have hnear := valuesAt_expectApprox_near (hdet n h0 w hw) (Nat.succ_pos n)
      rw [hk] at hnear
      calc |(X n).expectApprox w.payout (n + 1) - w.payout (φ n)|
          = |((X n).expectApprox w.payout (n + 1) - y n) + (y n - w.payout (φ n))| := by
            congr 1
            ring
        _ ≤ |(X n).expectApprox w.payout (n + 1) - y n| + |y n - w.payout (φ n)| :=
            abs_add_le _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add (hnear.trans hn1) (hn2 h0 w hw)
        _ = ε := by ring
    · simp only [gatedLuv, gatedSentence, if_neg h0]
      rw [payout_top]
      have hnear := valuesAt_expectApprox_near
        (indicatorOf_valuesAt_one' hw (PCWorld.holds_top w)) (Nat.succ_pos n)
      rw [hk] at hnear
      exact hnear.trans (hn1.trans (by linarith))
  have hlim0 := hpoly.affine_provind_theory_tendsto_zero P DP (gapComb_boundedPrices t X φ P DP)
    hmag hworld hval
  intro δ hδ
  filter_upwards [asympEq_iff_eventuallyWithin.1 hlim0 δ hδ] with n hn h0
  rw [sub_zero, gapComb_price] at hn
  simp only [gatedLuv, gatedSentence, if_pos h0] at hn
  exact hn

/-- `|c·x| ≤ |c|` for `x ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem abs_mul_le_abs_of_mem_Icc (c : ℝ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : |c * x| ≤ |c| := by
  rw [abs_mul, abs_of_nonneg h0]
  calc |c| * x ≤ |c| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |c| := mul_one _

/-! ## E. Engine 2: a one-sided three-sentence inequality along `G'` -/

/-- The gated three-sentence combination `φ₁ + c₂·φ₂ − c₃·φ₃` (one share of each gated sentence,
the second scaled by `c₂`, the third by `−c₃`). Off `G'` its value is `1 + c₂ − c₃`.
Source: none: infrastructure (mandate T4's `Ŝ_n − O^i_n` gated to `G'`)
Kind: D
Fidelity: n/a -/
def triComb (t : ℕ → ℕ) (φ₁ φ₂ φ₃ : ℕ → Sentence) (c₂ c₃ : ℚ) (n : ℕ) : AffineCombination :=
  ((sentenceAffine (gatedSentence t φ₁) n).add
    ((sentenceAffine (gatedSentence t φ₂) n).scale (.const c₂))).add
    ((sentenceAffine (gatedSentence t φ₃) n).scale (.const (-c₃)))

/-- `triComb_polySequence`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
noncomputable def triComb_polySequence {t : ℕ → ℕ} (ht : UnaryRuler t) {φ₁ φ₂ φ₃ : ℕ → Sentence}
    (h₁ : MachineSentenceCodes φ₁) (h₂ : MachineSentenceCodes φ₂) (h₃ : MachineSentenceCodes φ₃)
    (c₂ c₃ : ℚ) : PolySequence (triComb t φ₁ φ₂ φ₃ c₂ c₃) :=
  ((sentenceAffine_polySequence _ (gatedSentence_codes ht h₁)).add
    ((sentenceAffine_polySequence _ (gatedSentence_codes ht h₂)).scaleRat c₂)).add
    ((sentenceAffine_polySequence _ (gatedSentence_codes ht h₃)).scaleRat (-c₃))

/-- `triComb_price`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem triComb_price (t : ℕ → ℕ) (φ₁ φ₂ φ₃ : ℕ → Sentence) (c₂ c₃ : ℚ) (P : History)
    (n m : ℕ) :
    (triComb t φ₁ φ₂ φ₃ c₂ c₃ n).price P m =
      P m (gatedSentence t φ₁ n) + (c₂ : ℝ) * P m (gatedSentence t φ₂ n) -
        (c₃ : ℝ) * P m (gatedSentence t φ₃ n) := by
  rw [triComb, add_price, add_price, scale_price, scale_price, sentenceAffine_price,
    sentenceAffine_price, sentenceAffine_price, EF.denote_const, EF.denote_const]
  push_cast
  ring

/-- `triComb_value`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem triComb_value (t : ℕ → ℕ) (φ₁ φ₂ φ₃ : ℕ → Sentence) (c₂ c₃ : ℚ) (P : History)
    (w : PCWorld) (n : ℕ) :
    (triComb t φ₁ φ₂ φ₃ c₂ c₃ n).value P w.payout =
      w.payout (gatedSentence t φ₁ n) + (c₂ : ℝ) * w.payout (gatedSentence t φ₂ n) -
        (c₃ : ℝ) * w.payout (gatedSentence t φ₃ n) := by
  rw [triComb, add_value, add_value, scale_value, scale_value, sentenceAffine_value_payout,
    sentenceAffine_value_payout, sentenceAffine_value_payout, EF.denote_const, EF.denote_const]
  push_cast
  ring

/-- `triComb_magnitude_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem triComb_magnitude_le (t : ℕ → ℕ) (φ₁ φ₂ φ₃ : ℕ → Sentence) (c₂ c₃ : ℚ) (P : History)
    (n : ℕ) : (triComb t φ₁ φ₂ φ₃ c₂ c₃ n).magnitude P ≤ 1 + |(c₂ : ℝ)| + |(c₃ : ℝ)| := by
  rw [triComb, add_magnitude, add_magnitude, scale_magnitude, scale_magnitude,
    sentenceAffine_magnitude, sentenceAffine_magnitude, sentenceAffine_magnitude, EF.denote_const,
    EF.denote_const]
  push_cast
  simp only [mul_one, abs_neg]
  linarith

/-- `triComb_boundedPrices`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem triComb_boundedPrices (t : ℕ → ℕ) (φ₁ φ₂ φ₃ : ℕ → Sentence) (c₂ c₃ : ℚ) (P : History)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] :
    BoundedAffinePrices (triComb t φ₁ φ₂ φ₃ c₂ c₃) P := by
  have hP : ∀ m ψ, 0 ≤ P m ψ ∧ P m ψ ≤ 1 := fun m ψ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) m ψ
  refine ⟨1 + |(c₂ : ℝ)| + |(c₃ : ℝ)|, by positivity, fun n m => ?_⟩
  rw [triComb_price]
  obtain ⟨a0, a1⟩ := hP m (gatedSentence t φ₁ n)
  obtain ⟨b0, b1⟩ := hP m (gatedSentence t φ₂ n)
  obtain ⟨d0, d1⟩ := hP m (gatedSentence t φ₃ n)
  have hb := abs_mul_le_abs_of_mem_Icc (c₂ : ℝ) b0 b1
  have hd := abs_mul_le_abs_of_mem_Icc (c₃ : ℝ) d0 d1
  obtain ⟨hb1, hb2⟩ := abs_le.1 hb
  obtain ⟨hd1, hd2⟩ := abs_le.1 hd
  rw [abs_le]
  constructor <;> linarith

/-- **Gated one-sided provability induction, three sentences.** For a reader `P` over `DP`, a unary
ruler `t`, three e.c. sentence families and rationals `c₂ ≥ 0`, `c₃ ≤ 1 + c₂` (so that the
off-`G'` filler value `1 + c₂ − c₃` is non-negative): if eventually on `G'` every
completed-theory world has `payout φ₁ + c₂·payout φ₂ − c₃·payout φ₃ ≥ 0`, then along `G'` the
prices satisfy `P_n(φ₁ n) + c₂·P_n(φ₂ n) − c₃·P_n(φ₃ n) ≥ −δ` eventually, for every `δ > 0`.
FAF's `affine_provind_theory_ge_const` at `c = 0` on the gated combination. Reader `P`; one-way.
Source: mandate T4a (the route); FAF `PolySequence.affine_provind_theory_ge_const`
Kind: C
Fidelity: n/a (infrastructure)
Hyps: (a) none -/
theorem gated_three_ge (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {t : ℕ → ℕ} (ht : UnaryRuler t) {φ₁ φ₂ φ₃ : ℕ → Sentence}
    (h₁ : MachineSentenceCodes φ₁) (h₂ : MachineSentenceCodes φ₂) (h₃ : MachineSentenceCodes φ₃)
    (c₂ c₃ : ℚ) (hc₂ : 0 ≤ c₂) (hc₃ : c₃ ≤ 1 + c₂)
    (hval : ∀ᶠ n in atTop, t n = 0 → ∀ w : PCWorld, w.ConsistentWithTheory DP →
      0 ≤ w.payout (φ₁ n) + (c₂ : ℝ) * w.payout (φ₂ n) - (c₃ : ℝ) * w.payout (φ₃ n)) :
    ∀ δ > 0, ∀ᶠ n in atTop, t n = 0 →
      -δ ≤ P n (φ₁ n) + (c₂ : ℝ) * P n (φ₂ n) - (c₃ : ℝ) * P n (φ₃ n) := by
  have hpoly := triComb_polySequence ht h₁ h₂ h₃ c₂ c₃
  have hmag : ∃ C : ℝ, ∀ n, (triComb t φ₁ φ₂ φ₃ c₂ c₃ n).magnitude P ≤ C :=
    ⟨1 + |(c₂ : ℝ)| + |(c₃ : ℝ)|, fun n => triComb_magnitude_le t φ₁ φ₂ φ₃ c₂ c₃ P n⟩
  have hval' : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWithTheory DP → (0 : ℝ) - ε ≤ (triComb t φ₁ φ₂ φ₃ c₂ c₃ n).value P v.payout := by
    intro ε hε
    filter_upwards [hval] with n hn w hw
    rw [triComb_value]
    by_cases h0 : t n = 0
    · simp only [gatedSentence, if_pos h0]
      linarith [hn h0 w hw]
    · simp only [gatedSentence, if_neg h0, payout_top]
      have h2 : (0 : ℝ) ≤ c₂ := by exact_mod_cast hc₂
      have h3 : (c₃ : ℝ) ≤ 1 + c₂ := by exact_mod_cast hc₃
      linarith
  have hge := hpoly.affine_provind_theory_ge_const P DP
    (triComb_boundedPrices t φ₁ φ₂ φ₃ c₂ c₃ P DP) hmag hworld 0 hval'
  intro δ hδ
  filter_upwards [hge δ hδ] with n hn h0
  rw [triComb_price] at hn
  simp only [gatedSentence, if_pos h0] at hn
  linarith

end Cleanroom.Deference.DefFrozenSibling
