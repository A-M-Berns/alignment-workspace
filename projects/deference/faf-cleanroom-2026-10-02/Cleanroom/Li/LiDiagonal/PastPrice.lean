import Cleanroom.Li.LiDiagonal.GatedForcing
import Cleanroom.Li.LiDiagonal.Deferred
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# `li-diagonal` · PastPrice: Lemma F's N+ witness — a gate on the market's own past price (T6a)

The mandate's instance of Lemma F (T6a), built after audit round 1 found the same-day diagonal
instance degenerate (its gate dies by T1; `gated_forcing_diagonal`, N−). Here the sentence family
is the **Boolean quote of the market's own earlier-day price of its Kleene diagonal**:

* `X_n := ⌜r_n < P_{g n}(ψ_{g n})⌝` (`pastPriceQuote`), FAF's `BooleanQuoteCode.ofComputable` at the
  computable predicate `pastPriceTruth` (the market program's exact rational quote at day `g n`
  of the diagonal `ψ := kleeneDiag T market p`, compared with a computable threshold `r_n`); its
  completed-theory truth is the predicate itself (`BooleanQuoteCode.reflected`);
* `λ_n := Ind_δ(P_{g n}(ψ_{g n}) > r_n + δ)` (`pastPriceRamp`), a legal ramp of rank `g n ≤ n`
  (`pastPriceRamp_pgenerable`) that fires only where `X_n` is true (`pastPriceRamp_fire`); mirror
  `μ_n := Ind_δ(r_n − δ > P_{g n}(ψ_{g n}))` (`pastPriceRampNeg`), firing only where `X_n` is false.

Lemma F applies (`gated_forcing_pastPrice`, `gated_forcing_pastPrice_neg`). Because the diagonal's
price is pinned at `p` (T1), the gate's eventual behaviour is read off the threshold
(`pastPriceRamp_eventually`): below `p` it is eventually fully **on** and `X_n` eventually true;
above `p` it is eventually off and `X_n` eventually false. Two instances at `g n := n − 1`:

* `gated_forcing_pastPrice_const` (constant `r + 2δ < p`): the gate is eventually `1`, `X_n` is
  eventually true, and Lemma F forces `P_n(X_n) → 1` — the market learning a settled fact about
  its own past price, which is what [[route-negative-introspective]] §5.1 is for;
* `gated_forcing_pastPrice_alternating` (`r_n := r₀` on even days, `r₁` on odd days, with
  `r₀ + 2δ < p < r₁ − 2δ`): the gate is eventually `1` exactly on the even days and `0` on the odd
  days, `X_n` is eventually true exactly on the even days, and Lemma F plus its mirror force
  `P_{2k}(X_{2k}) → 1` and `P_{2k+1}(X_{2k+1}) → 0`. Here the gate genuinely *selects* the true
  days of a family that is true on half its days — Lemma F's content exercised (N+).

Also here, as the same legality spine at a ruler-computable earlier day: **T7c(ii)**, the soft
ramp on yesterday's price is a legal feature progression (`priceRampBelow_yesterday_pgenerable`).

Two caveats for the grading (audit r2, fidelity N1 / adversarial N1). (i) `_alternating` is the
N+ witness of record; `_const`'s gate is *eventually constant* `1`, the eventually-on special
case. (ii) On both instances the gate's firing set is eventually a day-computable set (all days;
the even days), so the *limit* conclusions (v) are also reachable by `thm:provind` on a
prefix- or parity-patched e.c. family with no gate at all (audit r2 probe `PastPriceViaProvind.lean`);
what the instances add is that the selecting gate is a price-reading legal feature, not a
day-computable indicator. An instance of Lemma F whose gate reads a price that does *not*
converge — the content beyond provability induction — is unbuilt, and cannot live on the pinned
diagonal (F-12). Day `0`: `g n := n − 1` reads day `0` at `n = 0` (`Nat` subtraction); every
statement below is eventual or true per day, so nothing depends on it.

Scope: single-market (the market reads its own earlier price through FAF's quotation presentation).
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Filter Topology

/-! ## Ramps of an earlier day's price, and their legality -/

/-- The ramp of the day-`g n` price of `X_{g n}` above the threshold `r_n + δ`:
`Ind_δ(P_{g n}(X_{g n}) > r_n + δ)` as a feature of rank `g n`.
Source: [[li-diagonal-mandate]] T6a instance (the "`ctsIndFeature`-style ramp of the day-`g n` price")
Kind: D
Fidelity: exact
Hyps: n/a -/
def pastPriceRamp (X : ℕ → Sentence) (g : ℕ → ℕ) (r : ℕ → ℚ) (δ : ℚ) (n : ℕ) : EF :=
  rampFeature δ (EF.price (X (g n)) (g n)) (EF.const (r n + δ))

/-- The mirror ramp, below the threshold `r_n − δ`: `Ind_δ(r_n − δ > P_{g n}(X_{g n}))`.
Source: [[li-diagonal-mandate]] T6a instance (mirror)
Kind: D
Fidelity: exact
Hyps: n/a -/
def pastPriceRampNeg (X : ℕ → Sentence) (g : ℕ → ℕ) (r : ℕ → ℚ) (δ : ℚ) (n : ℕ) : EF :=
  rampFeature δ (EF.const (r n - δ)) (EF.price (X (g n)) (g n))

/-- `pastPriceRamp_denote`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pastPriceRamp_denote (X : ℕ → Sentence) (g : ℕ → ℕ) (r : ℕ → ℚ) {δ : ℚ} (hδ : 0 < δ)
    (n : ℕ) (P : History) :
    (pastPriceRamp X g r δ n).denote P = ctsInd δ (P (g n) (X (g n))) ((r n : ℝ) + δ) := by
  unfold pastPriceRamp
  rw [rampFeature_denote hδ]
  simp [EF.denote_const, EF.denote]

/-- `pastPriceRampNeg_denote`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pastPriceRampNeg_denote (X : ℕ → Sentence) (g : ℕ → ℕ) (r : ℕ → ℚ) {δ : ℚ} (hδ : 0 < δ)
    (n : ℕ) (P : History) :
    (pastPriceRampNeg X g r δ n).denote P = ctsInd δ ((r n : ℝ) - δ) (P (g n) (X (g n))) := by
  unfold pastPriceRampNeg
  rw [rampFeature_denote hδ]
  simp [EF.denote_const, EF.denote]

/-- **The past-price ramp is a legal feature progression** for e.c. `X`, a ruler-computable
day map `g` with `g n ≤ n`, and a digit-computable threshold stream.
Source: none: infrastructure (the `priceRampBelow_pgenerable` spine at the day map `g`)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem pastPriceRamp_pgenerable (X : ℕ → Sentence) (hX : MachineSentenceCodes X)
    {g : ℕ → ℕ} (hg : UnaryRuler g) (hgle : ∀ n, g n ≤ n) (r : ℕ → ℚ) (δ : ℚ)
    (hr : MachineDigits (fun n => Encodable.encode (r n + δ))) :
    PGenerableWeighting (pastPriceRamp X g r δ) := by
  have hprice := MachineSpliceStream.serialize_price hX hg (MachineDigits.ofUnaryRuler hg)
  have hramp := MachineSpliceStream.serialize_clip01
    (MachineSpliceStream.serialize_mul
      (MachineSpliceStream.serialize_add hprice
        (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1))
          (MachineSpliceStream.serialize_const_write hr)))
      (MachineSpliceStream.serialize_const (1 / δ)))
  refine { polySeg := hramp, rank_le := ?_, closed := ?_ }
  · intro n
    simp only [pastPriceRamp, rampFeature, clip01, efMin, EF.rank]
    simpa using hgle n
  · intro n ρ V
    simp [pastPriceRamp, rampFeature, clip01, efMin, EF.denoteWith, EF.denote]

/-- **The mirror past-price ramp is a legal feature progression.**
Source: none: infrastructure
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem pastPriceRampNeg_pgenerable (X : ℕ → Sentence) (hX : MachineSentenceCodes X)
    {g : ℕ → ℕ} (hg : UnaryRuler g) (hgle : ∀ n, g n ≤ n) (r : ℕ → ℚ) (δ : ℚ)
    (hr : MachineDigits (fun n => Encodable.encode (r n - δ))) :
    PGenerableWeighting (pastPriceRampNeg X g r δ) := by
  have hprice := MachineSpliceStream.serialize_price hX hg (MachineDigits.ofUnaryRuler hg)
  have hramp := MachineSpliceStream.serialize_clip01
    (MachineSpliceStream.serialize_mul
      (MachineSpliceStream.serialize_add (MachineSpliceStream.serialize_const_write hr)
        (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1)) hprice))
      (MachineSpliceStream.serialize_const (1 / δ)))
  refine { polySeg := hramp, rank_le := ?_, closed := ?_ }
  · intro n
    simp only [pastPriceRampNeg, rampFeature, clip01, efMin, EF.rank]
    simpa using hgle n
  · intro n ρ V
    simp [pastPriceRampNeg, rampFeature, clip01, efMin, EF.denoteWith, EF.denote]

/-- **T7c(ii). The soft ramp on an earlier day's price is legal**: for e.c. `X`, a ruler-computable
`g` with `g n ≤ n` and a constant threshold `t`, `n ↦ Ind_δ(t > P_{g n}(X_{g n}))` is a
`PGenerableWeighting` (the `priceRampBelow_pgenerable` spine with `df := g`).
Source: [[trust-lab-inventory]] 056, 057 (K6: the soft gate on yesterday's price); [[li-diagonal-mandate]] T7c(ii)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem priceRampBelow_at_pgenerable (X : ℕ → Sentence) (hX : MachineSentenceCodes X)
    {g : ℕ → ℕ} (hg : UnaryRuler g) (hgle : ∀ n, g n ≤ n) (t δ : ℚ) :
    PGenerableWeighting (fun n => rampFeature δ (EF.const t) (EF.price (X (g n)) (g n))) := by
  have hprice := MachineSpliceStream.serialize_price hX hg (MachineDigits.ofUnaryRuler hg)
  have hramp := MachineSpliceStream.serialize_clip01
    (MachineSpliceStream.serialize_mul
      (MachineSpliceStream.serialize_add (MachineSpliceStream.serialize_const t)
        (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1)) hprice))
      (MachineSpliceStream.serialize_const (1 / δ)))
  refine { polySeg := hramp, rank_le := ?_, closed := ?_ }
  · intro n
    simp only [rampFeature, clip01, efMin, EF.rank]
    simpa using hgle n
  · intro n ρ V
    simp [rampFeature, clip01, efMin, EF.denoteWith, EF.denote]

/-- `n − 1` is a unary ruler (`UnaryRuler.sub` of the identity and the constant `1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem predRuler : UnaryRuler (fun n : ℕ => n - 1) :=
  UnaryRuler.id.sub (UnaryRuler.const 1)

/-- **T7c(ii) at yesterday**: the soft ramp on yesterday's price, `Ind_δ(t > P_{n−1}(X_{n−1}))`,
is a legal feature progression (K6's positive half: the soft gate survives where the hard one,
`hardGate_yesterday_not_ef`, does not).
Source: [[trust-lab-inventory]] 056, 057; [[li-diagonal-mandate]] T7c(ii)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem priceRampBelow_yesterday_pgenerable (X : ℕ → Sentence) (hX : MachineSentenceCodes X)
    (t δ : ℚ) :
    PGenerableWeighting (fun n => rampFeature δ (EF.const t) (EF.price (X (n - 1)) (n - 1))) :=
  priceRampBelow_at_pgenerable X hX predRuler (fun n => Nat.sub_le n 1) t δ

/-! ## The Boolean quote of the market's own earlier-day price of the diagonal -/

section PastPrice

variable {DP : DeductiveProcess} (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T]
  {P : History} (market : MarketComputation P) (p : ℚ)

/-- The predicate "`r_n` is below the market program's exact day-`g n` quote of the diagonal
`ψ_{g n}`" — the truth value of the past-price quote `X_n`.
Source: [[li-diagonal-mandate]] T6a instance ("`P (g n) (ψ (g n)) > ¼`", at a threshold stream `r`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def pastPriceTruth (g : ℕ → ℕ) (r : ℕ → ℚ) (n : ℕ) : Prop :=
  r n < market.quote (g n) (Encodable.encode (kleeneDiag T market p (g n)))

/-- The same predicate as a `0/1` real stream (the `TheoryTruth` of the quote family).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pastPriceTruthR (g : ℕ → ℕ) (r : ℕ → ℚ) (n : ℕ) : ℝ :=
  by classical exact if pastPriceTruth T market p g r n then 1 else 0

/-- The encoded diagonal sentence is a primitive recursive function of the day (FAF's
`encode_quoteAtom` shell around the fixed selector; the `diagonalPriceDecisionPart_partrec` idiom).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem kleeneDiag_encode_primrec :
    Primrec fun m : ℕ => Encodable.encode (kleeneDiag T market p m) := by
  have hpayload : Primrec fun m : ℕ =>
      quotationClaimCode universalQuotePos universalQuoteNeg
        (Nat.pair (parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.code m) :=
    Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const (Encodable.encode universalQuotePos))
        (Primrec₂.natPair.comp (Primrec.const (Encodable.encode universalQuoteNeg))
          (Primrec₂.natPair.comp (Primrec.const _) Primrec.id)))
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1) hpayload)).of_eq
    fun _ => rfl

/-- **The past-price predicate is computable** for computable `g` and `r`: the market program's
exact quote along computable streams (FAF `MarketComputation.quote_comp_computable`) compared by
`ratLE_prim`.
Source: none: infrastructure (FAF `decodedQuotationRat_lt_computablePred`'s idiom)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem pastPriceTruth_computablePred {g : ℕ → ℕ} (hg : Computable g) {r : ℕ → ℚ}
    (hr : Computable r) : ComputablePred (pastPriceTruth T market p g r) := by
  rw [ComputablePred.computable_iff]
  refine ⟨fun n => !(decide
    (market.quote (g n) (Encodable.encode (kleeneDiag T market p (g n))) ≤ r n)), ?_, ?_⟩
  · have hψ : Computable fun n => Encodable.encode (kleeneDiag T market p (g n)) :=
      (kleeneDiag_encode_primrec T market p).to_comp.comp hg
    have hq : Computable fun n =>
        market.quote (g n) (Encodable.encode (kleeneDiag T market p (g n))) :=
      market.quote_comp_computable hg hψ
    have hleB : Primrec fun q : ℚ × ℚ => decide (q.1 ≤ q.2) := ratLE_prim.decide
    have hle : Computable fun n : ℕ =>
        decide (market.quote (g n) (Encodable.encode (kleeneDiag T market p (g n))) ≤ r n) :=
      (hleB.to_comp.comp (hq.pair hr) : _)
    exact (Primrec.dom_bool Bool.not).to_comp.comp hle
  · funext n
    simp only [pastPriceTruth, Bool.not_eq_true', decide_eq_false_iff_not, not_le]

/-- **The past-price quote**: FAF's Boolean quote code of `pastPriceTruth` — the sentence
`X_n := ⌜r_n < P_{g n}(ψ_{g n})⌝`, a public literal of the quotation presentation. FAF's
`ofComputable` picks a decider code by `Classical.choice` from the computability proof, so `X` is
*a* Boolean quote of the predicate, fixed by the proof terms it is applied to, not a syntactically
canonical sentence; every property used (`sentence_poly`, `reflected`) holds for any such choice
(audit r2 adversarial N6).
Source: [[li-diagonal-mandate]] T6a instance (`BooleanQuoteCode.ofComputable` over the quotation presentation)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def pastPriceQuote {g : ℕ → ℕ} (hg : Computable g) {r : ℕ → ℚ}
    (hr : Computable r) : BooleanQuoteCode T (pastPriceTruth T market p g r) :=
  BooleanQuoteCode.ofComputable (pastPriceTruth_computablePred T market p hg hr)

/-- The past-price quote family is e.c. (FAF's whole-value emitter `sentence_poly`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pastPriceQuote_codes {g : ℕ → ℕ} (hg : Computable g) {r : ℕ → ℚ} (hr : Computable r) :
    MachineSentenceCodes (pastPriceQuote T market p hg hr).sentence :=
  MachineSentenceCodes.ofPolySentenceCodes (pastPriceQuote T market p hg hr).sentence_poly

/-- Every completed-theory world of the quotation presentation pays the past-price quote at its
predicate's truth value (`BooleanQuoteCode.reflected`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem pastPriceQuote_theoryTruth (Q : QuotationTheoryPresentation DP T) {g : ℕ → ℕ}
    (hg : Computable g) {r : ℕ → ℚ} (hr : Computable r) :
    AffineCombination.TheoryTruth (pastPriceQuote T market p hg hr).sentence DP
      (pastPriceTruthR T market p g r) := by
  intro n v hv
  unfold PCWorld.payout pastPriceTruthR
  by_cases h : pastPriceTruth T market p g r n
  · rw [if_pos (((pastPriceQuote T market p hg hr).reflected Q n v hv).2 h), if_pos h]
  · rw [if_neg (fun hh => h (((pastPriceQuote T market p hg hr).reflected Q n v hv).1 hh)),
      if_neg h]

/-- **The past-price ramp fires only where the past-price quote is true**: a nonzero
`Ind_δ(P_{g n}(ψ_{g n}) > r_n + δ)` means `r_n + δ < P_{g n}(ψ_{g n})`, hence `r_n` is below the
exact quote (`quote_exact`).
Source: [[li-diagonal-mandate]] T6a instance (`hfire`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem pastPriceRamp_fire (g : ℕ → ℕ) (r : ℕ → ℚ) {δ : ℚ} (hδ : 0 < δ) (n : ℕ)
    (h : (pastPriceRamp (kleeneDiag T market p) g r δ n).denote P ≠ 0) :
    pastPriceTruth T market p g r n := by
  rw [pastPriceRamp_denote _ _ _ hδ] at h
  have hpos := lt_of_le_of_ne (ctsInd_nonneg _ _ _) (Ne.symm h)
  have hlt := (ctsInd_pos_iff hδ _ _).1 hpos
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold pastPriceTruth
  rw [market.quote_exact] at hlt
  exact_mod_cast (show (r n : ℝ) < (market.quote (g n)
    (Encodable.encode (kleeneDiag T market p (g n))) : ℝ) by linarith)

/-- **The mirror ramp fires only where the past-price quote is false.**
Source: [[li-diagonal-mandate]] T6a instance (mirror `hfire`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem pastPriceRampNeg_fire (g : ℕ → ℕ) (r : ℕ → ℚ) {δ : ℚ} (hδ : 0 < δ) (n : ℕ)
    (h : (pastPriceRampNeg (kleeneDiag T market p) g r δ n).denote P ≠ 0) :
    ¬ pastPriceTruth T market p g r n := by
  rw [pastPriceRampNeg_denote _ _ _ hδ] at h
  have hpos := lt_of_le_of_ne (ctsInd_nonneg _ _ _) (Ne.symm h)
  have hlt := (ctsInd_pos_iff hδ _ _).1 hpos
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold pastPriceTruth
  rw [market.quote_exact] at hlt
  intro hcontra
  have : (r n : ℝ) < (market.quote (g n)
      (Encodable.encode (kleeneDiag T market p (g n))) : ℝ) := by exact_mod_cast hcontra
  linarith

/-- **T6a, Lemma F on the past-price quote** (the mandate's instance, general form): with
`X_n := ⌜r_n < P_{g n}(ψ_{g n})⌝` and the legal gate `λ_n := Ind_δ(P_{g n}(ψ_{g n}) > r_n + δ)`,
`λ_n · (1 − P_n(X_n)) ≈ₙ 0`, on every logical inductor over a quotation presentation.
Scope: single-market; threshold `p`; FAF's Kleene diagonal read at the earlier day `g n`.
Source: [[li-diagonal-mandate]] T6a instance; [[route-negative-introspective]] §5.1
Kind: C
Fidelity: exact (instance of `gated_forcing`)
Hyps: (a) none (`hg`, `hgc`, `hrc`, `hrdig` are the day map's and threshold stream's own certificates) -/
theorem gated_forcing_pastPrice [IsLogicalInductor P DP] (Q : QuotationTheoryPresentation DP T)
    {g : ℕ → ℕ} (hg : UnaryRuler g) (hgc : Computable g) (hgle : ∀ n, g n ≤ n)
    {r : ℕ → ℚ} (hrc : Computable r) {δ : ℚ} (hδ : 0 < δ)
    (hrdig : MachineDigits (fun n => Encodable.encode (r n + δ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (pastPriceRamp (kleeneDiag T market p) g r δ n).denote P *
      (1 - P n ((pastPriceQuote T market p hgc hrc).sentence n))) ≈ₙ fun _ => 0 :=
  gated_forcing P DP _ (pastPriceQuote_codes T market p hgc hrc) _
    (pastPriceQuote_theoryTruth T market p Q hgc hrc) _
    (pastPriceRamp_pgenerable _ (kleeneDiag_codes T market p) hg hgle r δ hrdig) 1
    (fun n => by
      rw [pastPriceRamp_denote _ _ _ hδ, abs_of_nonneg (ctsInd_nonneg _ _ _)]
      exact ctsInd_le_one _ _ _)
    (fun n hne => by
      unfold pastPriceTruthR
      rw [if_pos (pastPriceRamp_fire T market p g r hδ n hne)])
    hworld

/-- **Lemma F's mirror on the past-price quote**: `μ_n · P_n(X_n) ≈ₙ 0` for the mirror gate.
Scope: single-market; threshold `p`; FAF's Kleene diagonal read at the earlier day `g n`.
Source: [[li-diagonal-mandate]] T6a instance (mirror)
Kind: C
Fidelity: exact (instance of `gated_forcing_neg`)
Hyps: (a) none -/
theorem gated_forcing_pastPrice_neg [IsLogicalInductor P DP]
    (Q : QuotationTheoryPresentation DP T)
    {g : ℕ → ℕ} (hg : UnaryRuler g) (hgc : Computable g) (hgle : ∀ n, g n ≤ n)
    {r : ℕ → ℚ} (hrc : Computable r) {δ : ℚ} (hδ : 0 < δ)
    (hrdig : MachineDigits (fun n => Encodable.encode (r n - δ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (pastPriceRampNeg (kleeneDiag T market p) g r δ n).denote P *
      P n ((pastPriceQuote T market p hgc hrc).sentence n)) ≈ₙ fun _ => 0 :=
  gated_forcing_neg P DP _ (pastPriceQuote_codes T market p hgc hrc) _
    (pastPriceQuote_theoryTruth T market p Q hgc hrc) _
    (pastPriceRampNeg_pgenerable _ (kleeneDiag_codes T market p) hg hgle r δ hrdig) 1
    (fun n => by
      rw [pastPriceRampNeg_denote _ _ _ hδ, abs_of_nonneg (ctsInd_nonneg _ _ _)]
      exact ctsInd_le_one _ _ _)
    (fun n hne => by
      unfold pastPriceTruthR
      rw [if_neg (pastPriceRampNeg_fire T market p g r hδ n hne)])
    hworld

/-- **The gates' eventual behaviour is read off the threshold** (T1 at the earlier day): for every
`ε > 0`, eventually on every day `n` — if `r_n + 2δ + ε ≤ p` then `λ_n = 1`, `μ_n = 0` and `X_n`
is true; if `p + ε + 2δ ≤ r_n` then `λ_n = 0`, `μ_n = 1` and `X_n` is false. Because
`P_m(ψ_m) → p` and `g n → ∞`.
Scope: single-market; threshold `p`.
Source: [[li-diagonal-mandate]] T6a instance ("the day-`g n` price is eventually near `p`"); `thm:lp`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem pastPriceRamp_eventually [IsLogicalInductor P DP] (Q : QuotationTheoryPresentation DP T)
    (hp0 : 0 < p) (hp1 : p < 1) (g : ℕ → ℕ) (hgt : Tendsto g atTop atTop) (r : ℕ → ℚ)
    {δ : ℚ} (hδ : 0 < δ) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ((r n : ℝ) + 2 * δ + ε ≤ p →
        (pastPriceRamp (kleeneDiag T market p) g r δ n).denote P = 1 ∧
        (pastPriceRampNeg (kleeneDiag T market p) g r δ n).denote P = 0 ∧
        pastPriceTruth T market p g r n) ∧
      ((p : ℝ) + ε + 2 * δ ≤ r n →
        (pastPriceRamp (kleeneDiag T market p) g r δ n).denote P = 0 ∧
        (pastPriceRampNeg (kleeneDiag T market p) g r δ n).denote P = 1 ∧
        ¬ pastPriceTruth T market p g r n) := by
  have hlp := lic_paradox_resistance P DP p hp0 hp1 (harmonicDiagonalQuote Q market p) hworld
  rw [harmonicDiagonalQuote_sentence] at hlp
  have ht : Tendsto (fun m => P m (kleeneDiag T market p m)) atTop (𝓝 (p : ℝ)) := by
    unfold AsympEq at hlp
    simpa using hlp.add_const (p : ℝ)
  have htg := ht.comp hgt
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  filter_upwards [htg.eventually (Ioo_mem_nhds (sub_lt_self (p : ℝ) hε)
    (lt_add_of_pos_right (p : ℝ) hε))] with n hn
  obtain ⟨hlo, hhi⟩ := hn
  simp only [Function.comp] at hlo hhi
  set x : ℝ := P (g n) (kleeneDiag T market p (g n)) with hx
  have hxq : x = (market.quote (g n) (Encodable.encode (kleeneDiag T market p (g n))) : ℝ) :=
    market.quote_exact _ _
  rw [pastPriceRamp_denote _ _ _ hδ, pastPriceRampNeg_denote _ _ _ hδ, ← hx]
  constructor
  · intro hA
    refine ⟨(ctsInd_eq_one_iff hδ _ _).2 (by linarith), (ctsInd_eq_zero_iff hδ _ _).2 (by linarith),
      ?_⟩
    unfold pastPriceTruth
    exact_mod_cast (show (r n : ℝ) < (market.quote (g n)
      (Encodable.encode (kleeneDiag T market p (g n))) : ℝ) by rw [← hxq]; linarith)
  · intro hB
    refine ⟨(ctsInd_eq_zero_iff hδ _ _).2 (by linarith), (ctsInd_eq_one_iff hδ _ _).2 (by linarith),
      ?_⟩
    unfold pastPriceTruth
    intro hcontra
    have : (r n : ℝ) < (market.quote (g n)
        (Encodable.encode (kleeneDiag T market p (g n))) : ℝ) := by exact_mod_cast hcontra
    rw [← hxq] at this
    linarith

/-! ## The instances at `g n := n − 1` -/

/-- `n − 1` is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem predComputable : Computable (fun n : ℕ => n - 1) :=
  (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).to_comp

/-- `n − 1 → ∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem predTendsto : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun n hn => by omega⟩

/-- `2k → ∞` and `2k + 1 → ∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twoMulTendsto : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b, fun k hk => by omega⟩

/-- **T6a, N+ witness (constant threshold).** On any logical inductor over a quotation
presentation, with `X_n := ⌜r < P_{n−1}(ψ_{n−1})⌝` (the quote of yesterday's price of FAF's Kleene
diagonal exceeding `r`) and the legal gate `λ_n := Ind_δ(P_{n−1}(ψ_{n−1}) > r + δ)`, for
`r + 2δ < p`: (i) the gate fires only where `X_n` is true; (ii) the gate is eventually `1`;
(iii) `X_n` is eventually true in every completed world; (iv) Lemma F:
`λ_n · (1 − P_n(X_n)) ≈ₙ 0`; hence (v) `P_n(X_n) → 1` — the market learns the settled fact
about its own past price. The gate is not eventually `0` (unlike `gated_forcing_diagonal`), so
the forcing is exercised; but it is eventually *constant* `1`, so this is the eventually-on
special case and `gated_forcing_pastPrice_alternating` is the N+ witness of record. The limit (v)
is also provind-reachable on the tail of the e.c. family (audit r2 probe `PastPriceViaProvind`);
what the instance adds is that the gate is a price-reading legal feature.
Scope: single-market; threshold `p`; FAF's Kleene diagonal read at yesterday.
Source: [[li-diagonal-mandate]] T6a instance; [[route-negative-introspective]] §5.1
Kind: N+ (eventually-on special case; `_alternating` is the witness of record)
Fidelity: exact (the mandate's instance at the threshold `r` in place of `¼`, `g n := n − 1`)
Hyps: (a) none -/
theorem gated_forcing_pastPrice_const [IsLogicalInductor P DP]
    (Q : QuotationTheoryPresentation DP T) (hp0 : 0 < p) (hp1 : p < 1)
    (r δ : ℚ) (hδ : 0 < δ) (hr : r + 2 * δ < p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (∀ n, (pastPriceRamp (kleeneDiag T market p) (fun n => n - 1) (fun _ => r) δ n).denote P ≠ 0 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        v.Holds ((pastPriceQuote T market p predComputable (Computable.const r)).sentence n)) ∧
    (∀ᶠ n in atTop,
      (pastPriceRamp (kleeneDiag T market p) (fun n => n - 1) (fun _ => r) δ n).denote P = 1) ∧
    (∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      v.Holds ((pastPriceQuote T market p predComputable (Computable.const r)).sentence n)) ∧
    ((fun n => (pastPriceRamp (kleeneDiag T market p) (fun n => n - 1) (fun _ => r) δ n).denote P *
      (1 - P n ((pastPriceQuote T market p predComputable (Computable.const r)).sentence n))) ≈ₙ
      fun _ => 0) ∧
    Tendsto (fun n => P n ((pastPriceQuote T market p predComputable (Computable.const r)).sentence n))
      atTop (𝓝 1) := by
  have hrdig : MachineDigits (fun _ : ℕ => Encodable.encode (r + δ)) := MachineDigits.const _
  have hF := gated_forcing_pastPrice T market p Q predRuler predComputable (fun n => Nat.sub_le n 1)
    (Computable.const r) hδ hrdig hworld
  have hε : (0 : ℝ) < ((p : ℝ) - r - 2 * δ) / 2 := by
    have : (r : ℝ) + 2 * δ < p := by exact_mod_cast hr
    linarith
  have hev := pastPriceRamp_eventually T market p Q hp0 hp1 (fun n => n - 1) predTendsto
    (fun _ => r) hδ hworld _ hε
  have hev1 : ∀ᶠ n in atTop,
      (pastPriceRamp (kleeneDiag T market p) (fun n => n - 1) (fun _ => r) δ n).denote P = 1 ∧
      pastPriceTruth T market p (fun n => n - 1) (fun _ => r) n := by
    filter_upwards [hev] with n hn
    obtain ⟨h1, _, h3⟩ := hn.1 (by linarith)
    exact ⟨h1, h3⟩
  refine ⟨fun n hne v hv =>
    ((pastPriceQuote T market p predComputable (Computable.const r)).reflected Q n v hv).2
      (pastPriceRamp_fire T market p _ _ hδ n hne), ?_, ?_, hF, ?_⟩
  · filter_upwards [hev1] with n hn using hn.1
  · filter_upwards [hev1] with n hn
    exact fun v hv => ((pastPriceQuote T market p predComputable
      (Computable.const r)).reflected Q n v hv).2 hn.2
  · unfold AsympEq at hF
    have h1 : Tendsto (fun n => 1 - P n ((pastPriceQuote T market p predComputable
        (Computable.const r)).sentence n)) atTop (𝓝 0) := by
      refine (hF.congr' ?_)
      filter_upwards [hev1] with n hn
      rw [hn.1]; ring
    have := h1.const_sub 1
    simpa using this

/-- The alternating threshold `r_n := r₀` on even days, `r₁` on odd days, is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem alternatingThreshold_computable (r₀ r₁ : ℚ) :
    Computable (fun n : ℕ => if Even n then r₀ else r₁) := by
  have hmod : Primrec (fun n : ℕ => n % 2) := Primrec.nat_mod.comp Primrec.id (Primrec.const 2)
  have hpred : PrimrecPred (fun n : ℕ => n % 2 = 0) := Primrec.eq.comp hmod (Primrec.const 0)
  exact ((Primrec.ite hpred (Primrec.const r₀) (Primrec.const r₁)).to_comp).of_eq fun n => by
    simp [Nat.even_iff]

/-- The alternating threshold shifted by a constant has digit-computable codes
(`UnaryRuler.ifZero` on `n mod 2`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem alternatingThreshold_digits (r₀ r₁ c : ℚ) :
    MachineDigits (fun n : ℕ => Encodable.encode ((if Even n then r₀ else r₁) + c)) := by
  have h0 : UnaryRuler (fun n : ℕ => n % 2) := (MachineDigits.ofUnaryRuler UnaryRuler.id).mod_two
  refine (MachineDigits.ofUnaryRuler (UnaryRuler.ifZero h0
    (UnaryRuler.const (Encodable.encode (r₀ + c)))
    (UnaryRuler.const (Encodable.encode (r₁ + c))))).of_eq fun n => ?_
  by_cases h : Even n
  · rw [if_pos h, if_pos (Nat.even_iff.1 h)]
  · rw [if_neg h, if_neg (fun hh => h (Nat.even_iff.2 hh))]

/-- **T6a, N+ witness (alternating threshold): the gate selects the true days.** With
`X_n := ⌜r_n < P_{n−1}(ψ_{n−1})⌝` for `r_n := r₀` on even and `r₁` on odd days,
`r₀ + 2δ < p < r₁ − 2δ`, the gate `λ_n := Ind_δ(P_{n−1}(ψ_{n−1}) > r_n + δ)` and its mirror
`μ_n := Ind_δ(r_n − δ > P_{n−1}(ψ_{n−1}))`: (i) `λ` fires only where `X_n` is true, `μ` only
where it is false; (ii) eventually, on even days `λ_n = 1`, `μ_n = 0` and `X_n` is true, on odd
days `λ_n = 0`, `μ_n = 1` and `X_n` is false — a family true on half its days, with the legal
gate picking out exactly those days; (iii) Lemma F and its mirror; hence (iv)
`P_{2k}(X_{2k}) → 1` and `P_{2k+1}(X_{2k+1}) → 0`. This is Lemma F's content exercised: the
price is pushed to `1` where the gate fires and to `0` where the mirror fires, on FAF's real
objects (the market's own quotation of its own past price). The firing set is eventually the
even days, a day-computable set, so the limits (iv) are also provind-reachable through the parity
subfamilies (audit r2 probe `PastPriceViaProvind`); what the instance adds is that the selecting
gate is a price-reading legal feature, not a day-computable indicator.
Scope: single-market; threshold `p`; FAF's Kleene diagonal read at yesterday.
Source: [[li-diagonal-mandate]] T6a instance; [[route-negative-introspective]] §5.1
Kind: N+
Fidelity: exact (the mandate's instance with an alternating threshold stream)
Hyps: (a) none -/
theorem gated_forcing_pastPrice_alternating [IsLogicalInductor P DP]
    (Q : QuotationTheoryPresentation DP T) (hp0 : 0 < p) (hp1 : p < 1)
    (r₀ r₁ δ : ℚ) (hδ : 0 < δ) (hr₀ : r₀ + 2 * δ < p) (hr₁ : p + 2 * δ < r₁)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    let r : ℕ → ℚ := fun n => if Even n then r₀ else r₁
    let ψ := kleeneDiag T market p
    let X := (pastPriceQuote T market p predComputable (alternatingThreshold_computable r₀ r₁)).sentence
    (∀ n, (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P ≠ 0 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (X n)) ∧
    (∀ n, (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P ≠ 0 →
      ∀ v : PCWorld, v.ConsistentWithTheory DP → ¬ v.Holds (X n)) ∧
    (∀ᶠ n in atTop, Even n →
      (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P = 1 ∧
      (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P = 0 ∧
      ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (X n)) ∧
    (∀ᶠ n in atTop, ¬ Even n →
      (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P = 0 ∧
      (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P = 1 ∧
      ∀ v : PCWorld, v.ConsistentWithTheory DP → ¬ v.Holds (X n)) ∧
    ((fun n => (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P * (1 - P n (X n))) ≈ₙ
      fun _ => 0) ∧
    ((fun n => (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P * P n (X n)) ≈ₙ
      fun _ => 0) ∧
    Tendsto (fun k => P (2 * k) (X (2 * k))) atTop (𝓝 1) ∧
    Tendsto (fun k => P (2 * k + 1) (X (2 * k + 1))) atTop (𝓝 0) := by
  intro r ψ X
  have hrc := alternatingThreshold_computable r₀ r₁
  have hF := gated_forcing_pastPrice T market p Q predRuler predComputable
    (fun n => Nat.sub_le n 1) hrc hδ (alternatingThreshold_digits r₀ r₁ δ) hworld
  have hFneg := gated_forcing_pastPrice_neg T market p Q predRuler predComputable
    (fun n => Nat.sub_le n 1) hrc hδ
    ((alternatingThreshold_digits r₀ r₁ (-δ)).of_eq fun n => by simp [sub_eq_add_neg]) hworld
  have hε : (0 : ℝ) < min (((p : ℝ) - r₀ - 2 * δ) / 2) (((r₁ : ℝ) - p - 2 * δ) / 2) := by
    have h0 : (r₀ : ℝ) + 2 * δ < p := by exact_mod_cast hr₀
    have h1 : (p : ℝ) + 2 * δ < r₁ := by exact_mod_cast hr₁
    exact lt_min (by linarith) (by linarith)
  have hev := pastPriceRamp_eventually T market p Q hp0 hp1 (fun n => n - 1) predTendsto r hδ
    hworld _ hε
  have hrefl := fun n v hv =>
    (pastPriceQuote T market p predComputable hrc).reflected Q n v hv
  have hevE : ∀ᶠ n in atTop, Even n →
      (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P = 1 ∧
      (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P = 0 ∧
      pastPriceTruth T market p (fun n => n - 1) r n := by
    filter_upwards [hev] with n hn he
    refine hn.1 ?_
    have hr : r n = r₀ := by simp [r, he]
    rw [hr]
    have := min_le_left (((p : ℝ) - r₀ - 2 * δ) / 2) (((r₁ : ℝ) - p - 2 * δ) / 2)
    linarith
  have hevO : ∀ᶠ n in atTop, ¬ Even n →
      (pastPriceRamp ψ (fun n => n - 1) r δ n).denote P = 0 ∧
      (pastPriceRampNeg ψ (fun n => n - 1) r δ n).denote P = 1 ∧
      ¬ pastPriceTruth T market p (fun n => n - 1) r n := by
    filter_upwards [hev] with n hn ho
    refine hn.2 ?_
    have hr : r n = r₁ := by simp [r, ho]
    rw [hr]
    have := min_le_right (((p : ℝ) - r₀ - 2 * δ) / 2) (((r₁ : ℝ) - p - 2 * δ) / 2)
    linarith
  refine ⟨fun n hne v hv => (hrefl n v hv).2 (pastPriceRamp_fire T market p _ _ hδ n hne),
    fun n hne v hv ht => pastPriceRampNeg_fire T market p _ _ hδ n hne ((hrefl n v hv).1 ht),
    ?_, ?_, hF, hFneg, ?_, ?_⟩
  · filter_upwards [hevE] with n hn he
    obtain ⟨h1, h2, h3⟩ := hn he
    exact ⟨h1, h2, fun v hv => (hrefl n v hv).2 h3⟩
  · filter_upwards [hevO] with n hn ho
    obtain ⟨h1, h2, h3⟩ := hn ho
    exact ⟨h1, h2, fun v hv ht => h3 ((hrefl n v hv).1 ht)⟩
  · unfold AsympEq at hF
    have hFe := hF.comp twoMulTendsto
    have h1 : Tendsto (fun k => 1 - P (2 * k) (X (2 * k))) atTop (𝓝 0) := by
      refine hFe.congr' ?_
      filter_upwards [twoMulTendsto.eventually hevE] with k hk
      simp only [Function.comp]
      rw [(hk (even_two_mul k)).1]; ring
    have := h1.const_sub 1
    simpa using this
  · unfold AsympEq at hFneg
    have hodd : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b, fun k hk => by omega⟩
    have hFo := hFneg.comp hodd
    refine hFo.congr' ?_
    filter_upwards [hodd.eventually hevO] with k hk
    simp only [Function.comp]
    rw [(hk (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k))).2.1]; ring

end PastPrice

end Cleanroom.Li.LiDiagonal
