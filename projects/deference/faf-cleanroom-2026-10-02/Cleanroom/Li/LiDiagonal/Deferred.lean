import Cleanroom.Li.LiDiagonal.Defs
import Cleanroom.Found.LiAsympCalc.Luv
import Cleanroom.Found.LiAsympCalc.Ramp
import Cleanroom.Deference.DefSelfTrust.Comb
import LogicalInduction.Construction.Quotation.Packages
import LogicalInduction.Construction.Quotation.DeferralFibre
import LogicalInduction.Properties.TimelyLearning
import LogicalInduction.Properties.AffinePreemptiveLearning

/-!
# `li-diagonal` · Deferred: the deferred liar (T5)

The deferred liar `χ_n ↔ (ℙ_{f(n)}(χ_n) < p)` of [[weak-endorsement-deference-model]] §2.1 is the
reindexing `defDiag ψ f n := ψ (f n)` of FAF's same-day Kleene diagonal `ψ` of `(market, T, p)`
(`kleeneDiag`): `ψ (f n)` holds in every completed world iff its own day-`f n` price is below `p`
(T5a, `defDiag_reflected`). It is *not* a new fixed point (finding, presentation).

Over it: **both prices pin** — the future price `P_{f(n)}(χ_n) → p` is a subsequence of `thm:lp`
(T5b), and the present price `P_n(χ_n) → p` follows from `thm:ceu` (no expected net update:
`P_n(χ_n) ≈ₙ 𝔼_n(⌜P_{f(n)}(χ_n)⌝)`) plus expectation provability induction for a LUV family
determined at a convergent value (T5c, `defDiag_present_price_of_quote`). The **uncontrolled
step** of trust-lab-2-024, `𝔼_n(w) > 0` for `w := 𝟙[ℙ_{f(n)}(χ_n) ≥ ½]`, is settled: that
indicator is the sentence `∼χ_n`, whose price `→ 1 − p` (T5d, `defDiag_neg_price_of_quote`; at
`p = ½`, `→ ½`). **Hard two-sided endorsement fails**: `P_n(χ_n ⋏ ∼χ_n) → 0` by provability
induction while `½ · P_n(∼χ_n) → ¼` (T5e, `hard_endorsement_fails_deferredDiagonal`). **Soft
one-sided self-trust** is FAF's `thm:st` at `φ := χ`, and the file proves the limit facts that
grade its instances (T5f).

The `thm:ceu` and `thm:st` quote packages (`FuturePriceQuote`, `SelfTrustQuote`) are hypotheses
here and are discharged over FAF's paper market in `Paper.lean` (`lic_no_expected_net_update_closed`,
`lic_self_trust_closed`). The e.c. certificate `MachineSentenceCodes (defDiag ψ f)` is derived for
`succDeferral` (`defDiag_codes_succ`) and for any `UnaryRuler` deferral; for `2^n` it is a
hypothesis (K9; the write-out of `ψ (2^n)` is a numeral-size question this package does not
settle).

Infrastructure proved here and reusable: `expect_asympEq_of_determinedVia_tendsto` (expectation
provability induction at a *convergent* determined value, via `def-self-trust`'s tail trick) and
`neg_coherence` (`P_n(φ_n) + P_n(∼φ_n) → 1`, the negation-coherence lemma FAF lacks; API request K9).

Scope: single-market throughout.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefSelfTrust
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Filter Topology

/-! ## A. Expectation provability induction at a convergent determined value -/

/-- The compact syntax of the one-share combination `α · Y n + β`.
Source: none: infrastructure (FAF `LUVCombinationSyntax`; `Engine.lean`'s `ofLUVSyntax`)
Kind: D
Fidelity: n/a -/
noncomputable def affineImageSyntax (α β : ℚ) (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) :
    LUVCombinationSyntax (fun n => LUVCombination.affineImage α β (Y n)) where
  termCount _ := 1
  coefficient _ := EF.const α
  luv z := Y z.unpair.1
  termCount_poly := UnaryRuler.const 1
  const_poly := MachineSpliceStream.serialize_const β
  coefficient_poly := MachineSpliceStream.serialize_const α
  threshold_poly := by
    have h := MachineSentenceCodes.comp hY
      ((UnaryRuler.unpairFst.comp UnaryRuler.unpairFst).pair UnaryRuler.unpairSnd)
    refine MachineSentenceCodes.of_eq h fun m => ?_
    simp only [Nat.unpair_pair]
  terms_eq n := by simp [LUVCombination.affineImage]
  const_rank n := by simp [LUVCombination.affineImage]
  coefficient_rank n j _ := by simp
  const_closed n ρ V := by simp [LUVCombination.affineImage, EF.denoteWith, EF.denote]
  coefficient_closed z ρ V := by simp [EF.denoteWith, EF.denote]

/-- **Expectation provability induction at a convergent determined value**: an e.c. LUV family
`Y`, each `Y n` determined in `DP`'s completed theory at `y n`, with `y n → c`, has market
expectation `𝔼_n(Y_n) → c`. FAF's `lic_expect_combination_provind_*` endpoints demand a world
bound at *every* day; `def-self-trust`'s tail trick (`expect_asympEq_zero_of_eventually_abs_le`)
transports the eventual bound `|y n − c| ≤ ε`. Applied to `Y n − c`.
Source: none: infrastructure (LI paper `thm:expprovind`; `def-self-trust` tail trick)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem expect_asympEq_of_determinedVia_tendsto (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (y : ℕ → ℝ)
    (hdet : ∀ n, LUV.DeterminedVia (Y n) DP (y n)) (c : ℚ)
    (hy : Tendsto y atTop (𝓝 (c : ℝ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Y n).expect P n) ≈ₙ fun _ => (c : ℝ) := by
  have hzero := expect_asympEq_zero_of_eventually_abs_le (P := P) (DP := DP)
    (affineImageSyntax 1 (-c) Y hY) (B := |((-c : ℚ) : ℝ)| + |((1 : ℚ) : ℝ)|)
    (fun n => (l1Norm_affineImage 1 (-c) (Y n) P).le)
    (worldValued_affineImage 1 (-c) (fun n v hv => ⟨y n, hdet n v hv⟩))
    (fun ε hε => by
      have hev : ∀ᶠ n in atTop, |y n - c| ≤ ε := by
        filter_upwards [(Metric.tendsto_nhds.1 hy) ε hε] with n hn
        rw [Real.dist_eq] at hn
        exact hn.le
      filter_upwards [hev] with n hn v hv ν hν
      rw [affineImage_value]
      have hval : ν (Y n) = y n :=
        ((valuesAt_affineImage_iff 1 (-c) v (Y n) ν).1 hν).eq (hdet n v hv)
      rw [hval]
      push_cast
      rw [one_mul, ← sub_eq_add_neg]
      exact hn)
    hworld
  have heq : (fun n => (LUVCombination.affineImage 1 (-c) (Y n)).expect P n) =
      fun n => (Y n).expect P n - c := by
    funext n
    rw [affineImage_expect]
    push_cast
    ring
  rw [heq] at hzero
  unfold AsympEq at hzero ⊢
  simpa using hzero

/-! ## B. Negation coherence -/

/-- The two-share portfolio `φ_n + ∼φ_n`.
Source: none: infrastructure (FAF `sentenceAffine`, `AffineCombination.add`)
Kind: D
Fidelity: n/a -/
def negPairAffine (φ : ℕ → Sentence) (n : ℕ) : AffineCombination :=
  (AffineCombination.sentenceAffine φ n).add
    (AffineCombination.sentenceAffine (fun k => ∼ φ k) n)

/-- **Negation coherence**: for an e.c. sentence family, `P_n(φ_n) + P_n(∼φ_n) → 1`. Affine
provability induction (`affine_provind_theory_eq`) on the portfolio `φ_n + ∼φ_n`, whose value in
every world is `1`. FAF API request (K9): FAF has `lic_limitingBelief_add_neg` for the limit
only.
Source: LI paper `thm:affprovind`; [[li-diagonal-mandate]] K9
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem neg_coherence (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (φ n) + P n (∼ φ n)) ≈ₙ fun _ => 1 := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hpoly : AffineCombination.PolySequence (negPairAffine φ) :=
    (AffineCombination.sentenceAffine_polySequence φ hφ).add
      (AffineCombination.sentenceAffine_polySequence _ hφ.neg)
  have hbounded : BoundedAffinePrices (negPairAffine φ) P := ⟨2, by norm_num, fun n m => by
    unfold negPairAffine
    simp only [AffineCombination.add_price, AffineCombination.sentenceAffine_price]
    rw [abs_le]
    constructor <;> linarith [(hP m (φ n)).1, (hP m (φ n)).2, (hP m (∼ φ n)).1, (hP m (∼ φ n)).2]⟩
  have hmag : ∃ C : ℝ, ∀ n, (negPairAffine φ n).magnitude P ≤ C := ⟨2, fun n => by
    unfold negPairAffine
    simp only [AffineCombination.add_magnitude, AffineCombination.sentenceAffine_magnitude]
    norm_num⟩
  have heq := hpoly.affine_provind_theory_eq P DP hbounded hmag hworld 1 (fun n v hv => by
    unfold negPairAffine
    rw [AffineCombination.add_value]
    simp only [AffineCombination.sentenceAffine, AffineCombination.value, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const, PCWorld.payout]
    by_cases h : v.Holds (φ n)
    · rw [if_pos h, if_neg (fun h' => (PCWorld.holds_neg v (φ n)).mp h' h)]
      norm_num
    · rw [if_neg h, if_pos ((PCWorld.holds_neg v (φ n)).mpr h)]
      norm_num)
  have hprice : (fun n => (negPairAffine φ n).price P n) = fun n => P n (φ n) + P n (∼ φ n) := by
    funext n
    unfold negPairAffine
    simp only [AffineCombination.add_price, AffineCombination.sentenceAffine_price]
  rwa [hprice] at heq

/-- The ramp `ctsInd δ x t` is bounded by `|x − t| / δ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ctsInd_le_abs_div {δ : ℚ} (hδ : 0 < δ) (x t : ℝ) :
    ctsInd δ x t ≤ |x - t| / δ := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  refine (min_le_right _ _).trans (max_le (by positivity) ?_)
  exact div_le_div_of_nonneg_right (le_abs_self _) hδR.le

/-- **The negation's price from the sentence's**: for an e.c. family with `P_n(φ_n) → p`,
`P_n(∼φ_n) → 1 − p`. `neg_coherence` minus the hypothesis.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem neg_price_of_pos (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (p : ℚ)
    (hpos : (fun n => P n (φ n)) ≈ₙ fun _ => (p : ℝ)) :
    (fun n => P n (∼ φ n)) ≈ₙ fun _ => 1 - (p : ℝ) := by
  have h := (neg_coherence P DP φ hφ hworld).sub hpos
  have heq : (fun n => (P n (φ n) + P n (∼ φ n)) - P n (φ n)) = fun n => P n (∼ φ n) :=
    funext fun n => by ring
  rwa [heq] at h

/-! ## C. FAF's Kleene diagonal and the deferred liar over it -/

/-- **FAF's Kleene diagonal sentence family** of `(market, T, p)`: the public Boolean quote of
`parameterizedDiagonalQuoteCodeOfMarket`, true in every completed world iff its own day-`n`
price is below `p`. A name for the expression, nothing more (`kleeneDiag_eq`).
Source: FAF `parameterizedDiagonalQuoteCodeOfMarket` (`Construction/Quotation/Packages.lean`)
Kind: D
Fidelity: exact (FAF's object)
Hyps: n/a -/
noncomputable def kleeneDiag (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] {P : History}
    (market : MarketComputation P) (p : ℚ) : ℕ → Sentence :=
  (parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence

/-- `kleeneDiag_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kleeneDiag_eq (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] {P : History}
    (market : MarketComputation P) (p : ℚ) :
    kleeneDiag T market p =
      (parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence := rfl

/-- The e.c. certificate of FAF's Kleene diagonal, from the quote code's whole-value emitter.
Source: none: infrastructure (FAF `BooleanQuoteCode.sentence_poly`)
Kind: L
Fidelity: n/a -/
theorem kleeneDiag_codes (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] {P : History}
    (market : MarketComputation P) (p : ℚ) : MachineSentenceCodes (kleeneDiag T market p) :=
  MachineSentenceCodes.ofPolySentenceCodes
    (parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence_poly

/-- **The deferred liar is e.c. along any ruler-computable deferral** (K9): the reindexing of an
e.c. family by a `UnaryRuler` deferral is e.c. (FAF's `MachineSentenceCodes.comp`).
Source: [[li-diagonal-mandate]] K9
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem defDiag_codes_of_ruler {ψ : ℕ → Sentence} (hψ : MachineSentenceCodes ψ)
    (f : DeferralFunction) (hf : UnaryRuler f.f) : MachineSentenceCodes (defDiag ψ f) :=
  MachineSentenceCodes.comp hψ hf

/-- **The deferred liar at `succDeferral` is e.c.** (K9, the `(a)` case).
Source: [[li-diagonal-mandate]] K9
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem defDiag_codes_succ {ψ : ℕ → Sentence} (hψ : MachineSentenceCodes ψ) :
    MachineSentenceCodes (defDiag ψ succDeferral) :=
  defDiag_codes_of_ruler hψ succDeferral UnaryRuler.id.succ

/-- The harmonic-width `ParadoxResistanceQuote` of FAF's Kleene diagonal, over any quotation
presentation and market: FAF's `paradoxResistanceQuoteOfDiagonal` at `width n := 1/(n+1)` (the
certificate is FAF's own, from `cxQuote`'s proof). Its `sentence` field is `kleeneDiag T market p`
definitionally.
Source: FAF `paradoxResistanceQuoteOfDiagonal`, `cxQuote` (`Construction/Freeze/Counterexample.lean`)
Kind: D
Fidelity: n/a -/
noncomputable def harmonicDiagonalQuote {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗜𝚺₁ ⪯ T] (Q : QuotationTheoryPresentation DP T) {P : History}
    (market : MarketComputation P) (p : ℚ) : ParadoxResistanceQuote P DP p :=
  paradoxResistanceQuoteOfDiagonal Q market p (fun n : ℕ => 1 / ((n : ℚ) + 1))
    (DigitRatCodes.toMachine (DigitRatCodes.ofPolyRatCodes
      (PolyRatCodes.inv_of_pos harmonicWeight_polyRatCodes (fun n => by positivity))))
    (fun n => by positivity)
    (by
      have h : ∀ n : ℕ, ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) = 1 / ((n : ℝ) + 1) := by
        intro n; push_cast; ring
      simpa only [h] using tendsto_one_div_add_atTop_nhds_zero_nat)

/-- `harmonicDiagonalQuote_sentence`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma harmonicDiagonalQuote_sentence {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗜𝚺₁ ⪯ T] (Q : QuotationTheoryPresentation DP T) {P : History}
    (market : MarketComputation P) (p : ℚ) :
    (harmonicDiagonalQuote Q market p).sentence = kleeneDiag T market p := rfl

section Deferred

variable {DP : DeductiveProcess} {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]
  (Q : QuotationTheoryPresentation DP T) (P : History) [IsLogicalInductor P DP]
  (market : MarketComputation P) (p : ℚ) (f : DeferralFunction)

include Q

/-- **T5a. The deferred liar reflects its own future price**: in every completed world,
`defDiag ψ f n` holds iff `P (f n) (defDiag ψ f n) < p`. The deferred liar of
[[weak-endorsement-deference-model]] §2.1 **is** FAF's same-day diagonal reindexed by `f`; no
new fixed point is built (finding, presentation).
Scope: single-market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
Source: [[weak-endorsement-deference-model]] §2.1 (trust-lab-023); [[li-diagonal-mandate]] T5a
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem defDiag_reflected :
    ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      (v.Holds (defDiag (kleeneDiag T market p) f n) ↔
        P (f n) (defDiag (kleeneDiag T market p) f n) < (p : ℝ)) := by
  intro n v hv
  exact ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.reflected
    Q (f n) v hv).trans (parameterizedDiagonalQuoteCodeOfMarket_public_price_iff market T p (f n))

/-- **T5b. The deferred liar's future price pins**: `P_{f(n)}(χ_n) → p`, a subsequence of
`thm:lp` along the deferral.
Scope: single-market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
Source: [[weak-endorsement-deference-model]] §2.1; [[li-diagonal-mandate]] T5b
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem defDiag_future_price (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P (f n) (defDiag (kleeneDiag T market p) f n)) ≈ₙ fun _ => (p : ℝ) := by
  have h := lic_paradox_resistance P DP p hp0 hp1 (harmonicDiagonalQuote Q market p) hworld
  unfold AsympEq at h ⊢
  exact h.comp f.tendsto_atTop

/-- `P_{f(n)}(χ_n) → p` as a `Tendsto`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem defDiag_future_price_tendsto (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P (f n) (defDiag (kleeneDiag T market p) f n)) atTop (𝓝 (p : ℝ)) := by
  have h := defDiag_future_price Q P market p f hp0 hp1 hworld
  unfold AsympEq at h
  have := h.add (tendsto_const_nhds (x := (p : ℝ)))
  simpa using this

/-- **T5c (headline, load-bearing). The deferred liar's present price pins**: `P_n(χ_n) → p`.
Composition: `thm:ceu` (`lic_no_expected_net_update`: `P_n(χ_n) ≈ₙ 𝔼_n(Y_n)` where `Y n` is the
quoted future price, determined at `P_{f(n)}(χ_n)`), T5b (`P_{f(n)}(χ_n) → p`), and expectation
provability induction at a convergent determined value (`expect_asympEq_of_determinedVia_tendsto`).
The `thm:ceu` package `hq` is FAF's `FuturePriceQuote`, discharged over the paper market by
`lic_no_expected_net_update_closed` (`Paper.lean`, `paper_defDiag_present_price`).
Scope: single-market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
Source: [[weak-endorsement-deference-model]] §2.2 (trust-lab-023/024); [[root-fa-inventory]] 040 (K2); [[li-diagonal-mandate]] T5c
Kind: C
Fidelity: exact
Hyps: (a) `hq` (FAF's `thm:ceu` package; discharged over `paperDP T` in `Paper.lean`) -/
theorem defDiag_present_price_of_ceu (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (Y : ℕ → LUV)
    (hY : LUV.MachineThresholdCodeSeq Y)
    (hrefl : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Y n) (P (f n) (defDiag (kleeneDiag T market p) f n)))
    (hceu : (fun n => P n (defDiag (kleeneDiag T market p) f n)) ≈ₙ
      fun n => (Y n).expect P n) :
    (fun n => P n (defDiag (kleeneDiag T market p) f n)) ≈ₙ fun _ => (p : ℝ) := by
  have hdet : ∀ n, LUV.DeterminedVia (Y n) DP (P (f n) (defDiag (kleeneDiag T market p) f n)) :=
    fun n v hv => hrefl n v hv
  exact hceu.trans (expect_asympEq_of_determinedVia_tendsto P DP Y hY _ hdet p
    (defDiag_future_price_tendsto Q P market p f hp0 hp1 hworld) hworld)

/-- T5c over FAF's bundled `thm:ceu` package `FuturePriceQuote` (the component form
`defDiag_present_price_of_ceu` is what `Paper.lean` discharges from the closed form).
Scope: single-market; threshold `p`, deferral `f`.
Source: [[li-diagonal-mandate]] T5c
Kind: C
Fidelity: exact
Hyps: (a) `hq` (FAF's `thm:ceu` package) -/
theorem defDiag_present_price_of_quote (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (Y : ℕ → LUV)
    (hq : FuturePriceQuote P DP f (defDiag (kleeneDiag T market p) f) Y) :
    (fun n => P n (defDiag (kleeneDiag T market p) f n)) ≈ₙ fun _ => (p : ℝ) :=
  defDiag_present_price_of_ceu Q P market p f hp0 hp1 hworld Y hq.quote_codes hq.reflected
    (lic_no_expected_net_update P DP f _ Y hworld hq)

/-- **T5d (K4, trust-lab-2-024 settled). The negated deferred liar's price pins at `1 − p`**:
`P_n(∼χ_n) → 1 − p`. The hard indicator `𝟙[ℙ_{f(n)}(χ_n) ≥ ½]` of the model is the *sentence*
`∼χ_n` (by T5a), never a weighting (no `EF` is discontinuous, `not_exists_ef_hardIndicator`);
at `p = ½` its price `→ ½`, so the model's contested `q > 0` holds with `q = ½` and the
red-team's "plausibly `→ 0`" is refuted. From `neg_coherence` and T5c.
Scope: single-market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
Source: [[trust-lab-inventory]] 023; [[trust-lab-2-inventory]] 024; [[li-diagonal-mandate]] T5d, K4
Kind: C
Fidelity: exact
Hyps: (a) `hq` as in T5c -/
theorem defDiag_neg_price_of_quote (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (Y : ℕ → LUV)
    (hq : FuturePriceQuote P DP f (defDiag (kleeneDiag T market p) f) Y) :
    (fun n => P n (∼ defDiag (kleeneDiag T market p) f n)) ≈ₙ fun _ => 1 - (p : ℝ) :=
  neg_price_of_pos P DP _ hq.sentence_codes hworld p
    (defDiag_present_price_of_quote Q P market p f hp0 hp1 hworld Y hq)

end Deferred

/-! ## D. Hard endorsement fails (T5e) -/

/-- **Hard two-sided endorsement fails on any family whose price pins at `½`**: for e.c. `χ`
with `P_n(χ_n) → ½`, the "hard endorsement" identity `P_n(χ_n ⋏ ∼χ_n) ≈ₙ ½ · P_n(∼χ_n)` is
false — the left side `→ 0` (`lic_provind_false` on the refutable family `χ_n ⋏ ∼χ_n`), the right
side `→ ¼` (`neg_coherence`).
Scope: single-market; any e.c. family pinned at `½`.
Source: [[trust-lab-inventory]] 023 ("HARD endorsement at `t=½` on `χ_n` is contradictory"); [[li-diagonal-mandate]] T5e
Kind: P
Fidelity: exact — the value-vs-demand reading (the red-team's own restatement)
Hyps: (a) `hhalf` is T5c on the deferred liar -/
theorem hard_endorsement_fails_of_half (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (χ : ℕ → Sentence) (hχ : MachineSentenceCodes χ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hhalf : (fun n => P n (χ n)) ≈ₙ fun _ => ((1 / 2 : ℚ) : ℝ)) :
    ¬ ((fun n => P n (χ n ⋏ ∼ χ n)) ≈ₙ fun n => (1 / 2 : ℝ) * P n (∼ χ n)) := by
  intro h
  have hfalse : (fun n => P n (χ n ⋏ ∼ χ n)) ≈ₙ fun _ => 0 :=
    lic_provind_false P DP (fun n => χ n ⋏ ∼ χ n) (hχ.and hχ.neg) (fun n v _ => by
      rw [PCWorld.holds_neg, PCWorld.holds_and, PCWorld.holds_neg]
      tauto) hworld
  have hneg : Tendsto (fun n => P n (∼ χ n)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h1 := (neg_coherence P DP χ hχ hworld).sub hhalf
    have heq : (fun n => (P n (χ n) + P n (∼ χ n)) - P n (χ n)) = fun n => P n (∼ χ n) :=
      funext fun n => by ring
    rw [heq] at h1
    unfold AsympEq at h1
    have h2 := h1.add (tendsto_const_nhds (x := (1 : ℝ) - ((1 / 2 : ℚ) : ℝ)))
    have hc : (1 : ℝ) - ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by push_cast; norm_num
    rw [zero_add, hc] at h2
    refine h2.congr fun n => ?_
    ring
  have hB0 : Tendsto (fun n => (1 / 2 : ℝ) * P n (∼ χ n)) atTop (𝓝 0) := by
    have := h.symm.trans hfalse
    unfold AsympEq at this
    simpa using this
  have hB : Tendsto (fun n => (1 / 2 : ℝ) * P n (∼ χ n)) atTop (𝓝 ((1 / 2 : ℝ) * (1 / 2))) :=
    hneg.const_mul (1 / 2)
  have := tendsto_nhds_unique hB0 hB
  norm_num at this

/-- **T5e (headline; the note's no-go confirmed). Hard endorsement fails on the deferred liar at
`p = ½`**: for every logical inductor and every `thm:ceu` package on `χ := defDiag ψ f` (any
deferral `f`) at `p = ½`,
`¬ (P_n(χ_n ⋏ ∼χ_n) ≈ₙ ½ · P_n(∼χ_n))`. Source sentence: "HARD endorsement at `t=½` on `χ_n` is
contradictory" (trust-lab-023); reading: the value-vs-demand form (the red-team's own
restatement); surviving neighbour: soft one-sided self-trust (T5f, `soft_self_trust_deferredDiagonal`).
Scope: single-market; threshold `½`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
Source: [[trust-lab-inventory]] 023; [[weak-endorsement-deference-model]] §2.2; [[li-diagonal-mandate]] T5e
Kind: P
Fidelity: exact (value-vs-demand reading)
Hyps: (a) `hq` as in T5c -/
theorem hard_endorsement_fails_deferredDiagonal {DP : DeductiveProcess} {T : ArithmeticTheory}
    [𝗜𝚺₁ ⪯ T] (Q : QuotationTheoryPresentation DP T) (P : History) [IsLogicalInductor P DP]
    (market : MarketComputation P) (f : DeferralFunction)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (Y : ℕ → LUV)
    (hq : FuturePriceQuote P DP f (defDiag (kleeneDiag T market (1 / 2)) f) Y) :
    ¬ ((fun n => P n (defDiag (kleeneDiag T market (1 / 2)) f n ⋏
          ∼ defDiag (kleeneDiag T market (1 / 2)) f n)) ≈ₙ
        fun n => (1 / 2 : ℝ) * P n (∼ defDiag (kleeneDiag T market (1 / 2)) f n)) :=
  hard_endorsement_fails_of_half P DP _ hq.sentence_codes hworld
    (defDiag_present_price_of_quote Q P market (1 / 2) f (by norm_num) (by norm_num) hworld Y hq)

/-! ## E. Soft one-sided self-trust survives (T5f) -/

section SelfTrust

variable {DP : DeductiveProcess} {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]
  (Q : QuotationTheoryPresentation DP T) (P : History) [IsLogicalInductor P DP]
  (market : MarketComputation P) (p : ℚ) (f : DeferralFunction)

include Q

omit Q in
/-- **T5f. Soft one-sided self-trust on the deferred liar** is FAF's `thm:st` (`lic_self_trust`)
at `φ := χ`, constant threshold `p'` and constant width `δ`:
`𝔼_n(𝟙χ_n · Ind_δ(P_{f(n)}(χ_n) > p')) ≳ₙ p' · 𝔼_n(Ind_δ(P_{f(n)}(χ_n) > p'))`. The package
`hq` is FAF's `SelfTrustQuote`, discharged over the paper market by `lic_self_trust_closed`
(`Paper.lean`). Grading of the instances: at `p' + δ < p` the confidence factor `→ 1`
(`confidence_expect_tendsto_one`, N+ side); at `p' = p` both sides `→ 0`
(`confidence_expect_tendsto_zero`, `product_expect_tendsto_zero`, N−).
Scope: single-market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
Source: [[trust-lab-inventory]] 024; [[li-diagonal-mandate]] T5f
Kind: L
Fidelity: exact (FAF's `thm:st` instance)
Hyps: (a) `hq` (FAF's `thm:st` package; discharged over `paperDP T` in `Paper.lean`) -/
theorem soft_self_trust_deferredDiagonal (δ p' : ℚ) (A B : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hq : SelfTrustQuote P DP f (defDiag (kleeneDiag T market p) f) (fun _ => δ) (fun _ => p') A B) :
    (fun n => (A n).expect P n) ≳ₙ fun n => (p' : ℝ) * (B n).expect P n :=
  lic_self_trust P DP f _ _ _ A B hworld hq

/-- **The confidence factor saturates below the pin**: when `p' + δ < p`, the quoted indicator
`Ind_δ(P_{f(n)}(χ_n) > p')` is eventually `1` (the future price `→ p`), so its expectation `→ 1`.
The N+ side of T5f's grading at `p = ½`, `p' = ¼`, `δ < ¼`.
Scope: single-market; threshold `p`, deferral `f`.
Source: [[trust-lab-inventory]] 024; [[li-diagonal-mandate]] T5f
Kind: C
Fidelity: exact
Hyps: (a) `hq` as in T5f -/
theorem confidence_expect_tendsto_one (hp0 : 0 < p) (hp1 : p < 1) (δ p' : ℚ) (hδ : 0 < δ)
    (hlt : p' + δ < p) (B : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hB : LUV.MachineThresholdCodeSeq B)
    (hBrefl : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (B n) (ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ))) :
    (fun n => (B n).expect P n) ≈ₙ fun _ => 1 := by
  have hfut := defDiag_future_price_tendsto Q P market p f hp0 hp1 hworld
  have hev : ∀ᶠ n in atTop,
      ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ) = 1 := by
    have hgap : (p' : ℝ) + δ < p := by exact_mod_cast hlt
    filter_upwards [hfut.eventually (Ioi_mem_nhds hgap)] with n hn
    have hn' : (p' : ℝ) + δ < P (f n) (defDiag (kleeneDiag T market p) f n) := hn
    exact ctsInd_eq_one_of_le_sub δ _ _ hδ (by linarith)
  have hy : Tendsto (fun n => ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ))
      atTop (𝓝 ((1 : ℚ) : ℝ)) := by
    rw [Rat.cast_one]
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  have := expect_asympEq_of_determinedVia_tendsto P DP B hB _
    (fun n v hv => hBrefl n v hv) 1 hy hworld
  simpa using this

/-- **The confidence factor vanishes at the pin**: at `p' = p` the quoted indicator
`Ind_δ(P_{f(n)}(χ_n) > p)` is `≤ |P_{f(n)}(χ_n) − p| / δ → 0`, so its expectation `→ 0`. The N−
side of T5f's grading.
Scope: single-market; threshold `p`, deferral `f`.
Source: [[trust-lab-inventory]] 024; [[li-diagonal-mandate]] T5f
Kind: C
Fidelity: exact
Hyps: (a) `hq` as in T5f -/
theorem confidence_expect_tendsto_zero (hp0 : 0 < p) (hp1 : p < 1) (δ : ℚ) (hδ : 0 < δ)
    (B : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hB : LUV.MachineThresholdCodeSeq B)
    (hBrefl : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (B n) (ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p : ℝ))) :
    (fun n => (B n).expect P n) ≈ₙ fun _ => 0 := by
  have hfut := defDiag_future_price_tendsto Q P market p f hp0 hp1 hworld
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hy : Tendsto (fun n => ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p : ℝ))
      atTop (𝓝 ((0 : ℚ) : ℝ)) := by
    rw [Rat.cast_zero]
    have hdiff : Tendsto (fun n => |P (f n) (defDiag (kleeneDiag T market p) f n) - p| / δ)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => P (f n) (defDiag (kleeneDiag T market p) f n) - p)
          atTop (𝓝 0) := by
        have := hfut.sub (tendsto_const_nhds (x := (p : ℝ)))
        simpa using this
      have h2 := (h1.abs).div_const (δ : ℝ)
      simpa using h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff
      (fun n => ctsInd_nonneg _ _ _) (fun n => ctsInd_le_abs_div hδ _ _)
  have := expect_asympEq_of_determinedVia_tendsto P DP B hB _
    (fun n v hv => hBrefl n v hv) 0 hy hworld
  simpa using this

/-- **The product vanishes at the pin**: at `p' = p` the quoted product `𝟙χ_n · Ind_δ(…)` is
determined (the completed theory decides `χ_n`, T5a) at `𝟙[P_{f(n)}(χ_n) < p] · Ind_δ(…) → 0`,
so its expectation `→ 0`. With `confidence_expect_tendsto_zero`, the `p' = p` instance of T5f holds
degenerately: `0 ≳ p · 0`. N−.
Scope: single-market; threshold `p`, deferral `f`.
Source: [[trust-lab-inventory]] 024; [[li-diagonal-mandate]] T5f
Kind: C
Fidelity: exact
Hyps: (a) `hq` as in T5f -/
theorem product_expect_tendsto_zero (hp0 : 0 < p) (hp1 : p < 1) (δ : ℚ) (hδ : 0 < δ)
    (A : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : LUV.MachineThresholdCodeSeq A)
    (hArefl : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (A n) (v.payout (defDiag (kleeneDiag T market p) f n) *
        ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p : ℝ))) :
    (fun n => (A n).expect P n) ≈ₙ fun _ => 0 := by
  have hfut := defDiag_future_price_tendsto Q P market p f hp0 hp1 hworld
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  set τ : ℕ → ℝ := fun n => diagTruth P (kleeneDiag T market p) p (f n) with hτ
  have hdet : ∀ n, LUV.DeterminedVia (A n) DP
      (τ n * ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p : ℝ)) := by
    intro n v hv
    have h := hArefl n v hv
    have hpay : v.payout (defDiag (kleeneDiag T market p) f n) = τ n := by
      have hr := defDiag_reflected Q P market p f n v hv
      simp only [hτ]
      unfold PCWorld.payout diagTruth
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (hr.1 h1) h2
      · exact absurd (hr.2 h2) h1
      · rfl
    rwa [hpay] at h
  have hτ01 : ∀ n, 0 ≤ τ n ∧ τ n ≤ 1 := fun n => by
    simp only [hτ, diagTruth]; split_ifs <;> norm_num
  have hy : Tendsto (fun n => τ n * ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p : ℝ))
      atTop (𝓝 ((0 : ℚ) : ℝ)) := by
    rw [Rat.cast_zero]
    have hdiff : Tendsto (fun n => |P (f n) (defDiag (kleeneDiag T market p) f n) - p| / δ)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => P (f n) (defDiag (kleeneDiag T market p) f n) - p)
          atTop (𝓝 0) := by
        have := hfut.sub (tendsto_const_nhds (x := (p : ℝ)))
        simpa using this
      have h2 := (h1.abs).div_const (δ : ℝ)
      simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff
      (fun n => mul_nonneg (hτ01 n).1 (ctsInd_nonneg _ _ _)) (fun n => ?_)
    calc τ n * ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p : ℝ)
        ≤ 1 * ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p : ℝ) :=
          mul_le_mul_of_nonneg_right (hτ01 n).2 (ctsInd_nonneg _ _ _)
      _ = ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p : ℝ) := one_mul _
      _ ≤ _ := ctsInd_le_abs_div hδ _ _
  have := expect_asympEq_of_determinedVia_tendsto P DP A hA _ hdet 0 hy hworld
  simpa using this

end SelfTrust

end Cleanroom.Li.LiDiagonal
