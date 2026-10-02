import Cleanroom.Li.LiDiagonal.Pinned
import Cleanroom.Found.LiAsympCalc.Ramp
import LogicalInduction.Properties.AffinePreemptiveLearning
import LogicalInduction.Properties.TimelyLearning
import LogicalInduction.Framework.Machine.SpliceMachine
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# `li-diagonal` · GatedForcing: Lemma F, gated forcing (T6a)

**Lemma F** (vq-wiki-059/060): for an e.c. sentence family `X` with completed-theory truth
`truth` and a legal gate `λ` that fires only on days where `X_n` is true, `λ_n · (1 − P_n(X_n)) → 0`;
mirror: a gate `μ` firing only where `X_n` is false has `μ_n · P_n(X_n) → 0`. Proof: the affine
portfolio `λ_n · (X_n − 1)` (feature coefficients are allowed in `AffineCombination`) has
completed-theory value `0` on every day — `0` when the gate is off, `λ(1 − 1)` when it is on —
so FAF's affine provability induction (`affine_provind_theory_eq`) prices it at `≈ₙ 0`.

**Two forms, two fidelities (audit r1, B1).** The source's Lemma F ([[route-negative-introspective]]
§5.1) has hypothesis "`D^n_H` decides `X_n`" and conclusion `∑_n λ_n(1 − P_n(X_n)) < ∞`, with
"`→ 0`" as its stated corollary. `gated_forcing` is the *variant* with a weaker hypothesis
(completed-theory truth only — the lab's stage-decidedness is not needed for `→ 0`) and the weaker
conclusion (`≈ₙ 0`). `gated_forcing_summable` is the source's own form: under stage-decidedness
(`hdec : λ_n ≠ 0 → X_n ∈ D_n`) the gated gap is **summable**, by the buy trader
`λ_n · X_n` (e.c. through `MachineSpliceStream.ec`), whose net worth in every plausible world is
the nonnegative partial sum — bounded below, so unbounded above would exploit. Mirror:
`gated_forcing_neg`, `gated_forcing_neg_summable`.

**Instance on the diagonal** (`gated_forcing_diagonal`, **N−**): `X := χ` (FAF's diagonal), `λ_n :=
ctsInd δ (p − δ) (P_n(χ_n))` (the ramp of the same-day price; legal, rank `n`; fires only when
`P_n(χ_n) < p − δ < p`, i.e. `χ_n` true). The package is inhabited, but by T1
(`ramp_silence_below`) the gate is eventually *exactly* `0`, so the conclusion holds on the tail by
`0 · x = 0` and Lemma F's forcing is never exercised (audit r1 probes `GateSilent.lean`,
`GateSilentAdv.lean`). That silence is itself the "general principle" of
[[route-negative-introspective]] §3.1: on FAF's diagonal every legal gate keyed to the price's own
threshold with a positive e.c. margin is eventually exactly `0`, and the margin-`0` gate tends to
`0` (`ramp_margin_zero_tendsto_zero`; its *exact* silence is E2, open — audit r2 adversarial N2).
Either way no diagonal-keyed instance can exercise the forcing in the limit. The **N+** witness is
the mandate's earlier-day instance, `PastPrice.lean` (`gated_forcing_pastPrice_*`): the gate reads
the day-`(n−1)` price of the diagonal, is eventually fully on (constant threshold) or selects the
true half of a half-true family (alternating threshold), and Lemma F forces the market's price of
the quote of its own past price accordingly.

Scope: single-market.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## The gated portfolios -/

/-- The portfolio `λ_n · (X_n − 1)`: coefficient `λ_n` on `X_n`, constant `−λ_n`.
Source: [[vq-wiki-inventory]] 059 (Lemma F's trader); [[li-diagonal-mandate]] T6a
Kind: D
Fidelity: exact
Hyps: n/a -/
def gatedAffine (X : ℕ → Sentence) (lam : ℕ → EF) (n : ℕ) : AffineCombination :=
  ⟨EF.mul (EF.const (-1)) (lam n), [(lam n, X n)]⟩

/-- The portfolio `μ_n · X_n`.
Source: [[vq-wiki-inventory]] 059; [[li-diagonal-mandate]] T6a (mirror)
Kind: D
Fidelity: exact
Hyps: n/a -/
def gatedAffinePos (X : ℕ → Sentence) (mu : ℕ → EF) (n : ℕ) : AffineCombination :=
  ⟨EF.const 0, [(mu n, X n)]⟩

/-- `gatedAffine_value`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedAffine_value (X : ℕ → Sentence) (lam : ℕ → EF) (n : ℕ) (P : History)
    (w : Valuation) :
    (gatedAffine X lam n).value P w = -(lam n).denote P + (lam n).denote P * w (X n) := by
  simp [gatedAffine, AffineCombination.value, EF.denote_mul, EF.denote_const]

/-- `gatedAffine_price`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedAffine_price (X : ℕ → Sentence) (lam : ℕ → EF) (n : ℕ) (P : History) (m : ℕ) :
    (gatedAffine X lam n).price P m = -(lam n).denote P + (lam n).denote P * P m (X n) := by
  simp [AffineCombination.price, gatedAffine_value]

/-- `gatedAffine_magnitude`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedAffine_magnitude (X : ℕ → Sentence) (lam : ℕ → EF) (n : ℕ) (P : History) :
    (gatedAffine X lam n).magnitude P = |(lam n).denote P| := by
  simp [gatedAffine, AffineCombination.magnitude]

/-- `gatedAffinePos_value`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedAffinePos_value (X : ℕ → Sentence) (mu : ℕ → EF) (n : ℕ) (P : History)
    (w : Valuation) :
    (gatedAffinePos X mu n).value P w = (mu n).denote P * w (X n) := by
  simp [gatedAffinePos, AffineCombination.value, EF.denote_const]

/-- `gatedAffinePos_price`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedAffinePos_price (X : ℕ → Sentence) (mu : ℕ → EF) (n : ℕ) (P : History) (m : ℕ) :
    (gatedAffinePos X mu n).price P m = (mu n).denote P * P m (X n) := by
  simp [AffineCombination.price, gatedAffinePos_value]

/-- `gatedAffinePos_magnitude`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedAffinePos_magnitude (X : ℕ → Sentence) (mu : ℕ → EF) (n : ℕ) (P : History) :
    (gatedAffinePos X mu n).magnitude P = |(mu n).denote P| := by
  simp [gatedAffinePos, AffineCombination.magnitude]

/-- The gated portfolio is a polynomial affine sequence for e.c. `X` and a legal gate `λ`.
Source: none: infrastructure (FAF `sentenceAffine_polySequence`, `sentenceMinusFeature_polySequence` pattern)
Kind: D
Fidelity: n/a -/
noncomputable def gatedAffine_polySequence (X : ℕ → Sentence) (hX : MachineSentenceCodes X)
    (lam : ℕ → EF) (hlam : PGenerableWeighting lam) :
    AffineCombination.PolySequence (gatedAffine X lam) where
  termCount _ := 1
  coefficient z := lam z.unpair.1
  sentence z := X z.unpair.1
  termCount_poly := UnaryRuler.const 1
  const_poly := MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1))
    hlam.polySeg
  coefficient_poly := hlam.polySeg.comp UnaryRuler.unpairFst
  sentence_poly := hX.comp UnaryRuler.unpairFst
  terms_eq n := by simp [gatedAffine]
  const_rank n := by
    simp only [gatedAffine, EF.rank]
    exact Nat.max_le.mpr ⟨by simp [EF.rank], hlam.rank_le n⟩
  coefficient_rank n j _ := by simpa using hlam.rank_le n
  const_closed n ρ V := by simp [gatedAffine, EF.denoteWith, hlam.closed n ρ V]
  coefficient_closed z ρ V := hlam.closed _ ρ V

/-- The positive gated portfolio is a polynomial affine sequence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def gatedAffinePos_polySequence (X : ℕ → Sentence) (hX : MachineSentenceCodes X)
    (mu : ℕ → EF) (hmu : PGenerableWeighting mu) :
    AffineCombination.PolySequence (gatedAffinePos X mu) where
  termCount _ := 1
  coefficient z := mu z.unpair.1
  sentence z := X z.unpair.1
  termCount_poly := UnaryRuler.const 1
  const_poly := MachineSpliceStream.serialize_const 0
  coefficient_poly := hmu.polySeg.comp UnaryRuler.unpairFst
  sentence_poly := hX.comp UnaryRuler.unpairFst
  terms_eq n := by simp [gatedAffinePos]
  const_rank n := by simp [gatedAffinePos]
  coefficient_rank n j _ := by simpa using hmu.rank_le n
  const_closed n ρ V := by simp [gatedAffinePos, EF.denoteWith, EF.denote]
  coefficient_closed z ρ V := hmu.closed _ ρ V

/-! ## Lemma F -/

/-- **T6a (headline). Lemma F, gated forcing — the `→ 0` form**: for an e.c. family `X` with
completed-theory truth `truth`, a legal gate `λ` (`PGenerableWeighting`, bounded by `C`) that fires
only where `truth n = 1` has `λ_n · (1 − P_n(X_n)) ≈ₙ 0`. Affine provability induction on
`λ_n · (X_n − 1)`, whose completed-theory value is `0` every day. Weaker hypothesis than the
source's (no "`D_H` decides `X_n` by day `n`", only completed-theory truth) **and** weaker
conclusion (the source concludes `∑ < ∞`, with `→ 0` as its corollary): the two are
incomparable. The source's own form is `gated_forcing_summable`.
Scope: single-market; any e.c. family `X`.
Source: [[vq-wiki-inventory]] 059, 060 (Lemma F); [[route-negative-introspective]] §5.1; [[li-diagonal-mandate]] T6a
Kind: C
Fidelity: variant — weaker hypothesis (completed-theory truth in place of stage-decidedness), weaker conclusion (`λ_n(1 − P_n(X_n)) ≈ₙ 0` in place of `∑ < ∞`)
Hyps: (a) none (`hC` is a bound on the gate; `1` for every ramp) -/
theorem gated_forcing (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : ℕ → Sentence) (hX : MachineSentenceCodes X) (truth : ℕ → ℝ)
    (htruth : AffineCombination.TheoryTruth X DP truth)
    (lam : ℕ → EF) (hlam : PGenerableWeighting lam) (C : ℝ) (hC : ∀ n, |(lam n).denote P| ≤ C)
    (hfire : ∀ n, (lam n).denote P ≠ 0 → truth n = 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (lam n).denote P * (1 - P n (X n))) ≈ₙ fun _ => 0 := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hpoly := gatedAffine_polySequence X hX lam hlam
  have hbounded : BoundedAffinePrices (gatedAffine X lam) P := ⟨max C 0, le_max_right _ _,
    fun n m => by
      rw [gatedAffine_price, show -(lam n).denote P + (lam n).denote P * P m (X n) =
        (lam n).denote P * (P m (X n) - 1) by ring, abs_mul]
      have h1 : |P m (X n) - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [(hP m (X n)).1, (hP m (X n)).2]
      exact (mul_le_of_le_one_right (abs_nonneg _) h1).trans ((hC n).trans (le_max_left _ _))⟩
  have hmag : ∃ C' : ℝ, ∀ n, (gatedAffine X lam n).magnitude P ≤ C' :=
    ⟨C, fun n => by rw [gatedAffine_magnitude]; exact hC n⟩
  have heq := hpoly.affine_provind_theory_eq P DP hbounded hmag hworld 0 (fun n v hv => by
    rw [gatedAffine_value]
    by_cases hl : (lam n).denote P = 0
    · simp [hl]
    · rw [htruth n v hv, hfire n hl]; ring)
  have hprice : (fun n => (gatedAffine X lam n).price P n) =
      fun n => -((lam n).denote P * (1 - P n (X n))) := by
    funext n; rw [gatedAffine_price]; ring
  rw [hprice] at heq
  have := heq.const_mul (-1)
  simp only [neg_mul, one_mul, neg_neg, mul_zero] at this
  exact this

/-- **Lemma F, mirror, `→ 0` form**: a legal gate `μ` firing only where `truth n = 0` has
`μ_n · P_n(X_n) ≈ₙ 0`. The source's summable form is `gated_forcing_neg_summable`.
Scope: single-market; any e.c. family `X`.
Source: [[vq-wiki-inventory]] 059, 060; [[li-diagonal-mandate]] T6a (mirror)
Kind: C
Fidelity: variant — as `gated_forcing`
Hyps: (a) none -/
theorem gated_forcing_neg (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : ℕ → Sentence) (hX : MachineSentenceCodes X) (truth : ℕ → ℝ)
    (htruth : AffineCombination.TheoryTruth X DP truth)
    (mu : ℕ → EF) (hmu : PGenerableWeighting mu) (C : ℝ) (hC : ∀ n, |(mu n).denote P| ≤ C)
    (hfire : ∀ n, (mu n).denote P ≠ 0 → truth n = 0)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (mu n).denote P * P n (X n)) ≈ₙ fun _ => 0 := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hpoly := gatedAffinePos_polySequence X hX mu hmu
  have hbounded : BoundedAffinePrices (gatedAffinePos X mu) P := ⟨max C 0, le_max_right _ _,
    fun n m => by
      rw [gatedAffinePos_price, abs_mul]
      have h1 : |P m (X n)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [(hP m (X n)).1, (hP m (X n)).2]
      exact (mul_le_of_le_one_right (abs_nonneg _) h1).trans ((hC n).trans (le_max_left _ _))⟩
  have hmag : ∃ C' : ℝ, ∀ n, (gatedAffinePos X mu n).magnitude P ≤ C' :=
    ⟨C, fun n => by rw [gatedAffinePos_magnitude]; exact hC n⟩
  have heq := hpoly.affine_provind_theory_eq P DP hbounded hmag hworld 0 (fun n v hv => by
    rw [gatedAffinePos_value]
    by_cases hl : (mu n).denote P = 0
    · simp [hl]
    · rw [htruth n v hv, hfire n hl]; ring)
  have hprice : (fun n => (gatedAffinePos X mu n).price P n) =
      fun n => (mu n).denote P * P n (X n) := by
    funext n; rw [gatedAffinePos_price]
  rwa [hprice] at heq

/-! ## The instance on the diagonal -/

/-- The ramp of the same-day price of `X n` below a threshold: `Ind_δ(t > P_n(X_n))` as a feature.
Source: none: infrastructure (`li-asymp-calc` `rampFeature`, FAF `calibrationLower`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def priceRampBelow (X : ℕ → Sentence) (t δ : ℚ) (n : ℕ) : EF :=
  rampFeature δ (EF.const t) (EF.price (X n) n)

/-- `priceRampBelow` denotes `ctsInd δ t (P_n(X_n))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem priceRampBelow_denote (X : ℕ → Sentence) {t δ : ℚ} (hδ : 0 < δ) (n : ℕ) (P : History) :
    (priceRampBelow X t δ n).denote P = ctsInd δ (t : ℝ) (P n (X n)) := by
  unfold priceRampBelow
  rw [rampFeature_denote hδ]
  simp [EF.denote_const, EF.denote]

/-- `priceRampBelow` is a legal feature progression (the `dsFeature_pgenerable` spine).
Source: none: infrastructure (`li-asymp-calc` `dsFeature_pgenerable`)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem priceRampBelow_pgenerable (X : ℕ → Sentence) (hX : MachineSentenceCodes X) (t δ : ℚ) :
    PGenerableWeighting (priceRampBelow X t δ) := by
  have hprice := MachineSpliceStream.serialize_price hX UnaryRuler.id
    (MachineDigits.ofUnaryRuler UnaryRuler.id)
  have hramp := MachineSpliceStream.serialize_clip01
    (MachineSpliceStream.serialize_mul
      (MachineSpliceStream.serialize_add (MachineSpliceStream.serialize_const t)
        (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1)) hprice))
      (MachineSpliceStream.serialize_const (1 / δ)))
  refine { polySeg := hramp, rank_le := ?_, closed := ?_ }
  · intro n
    simp [priceRampBelow, rampFeature]
  · intro n ρ V
    simp [priceRampBelow, rampFeature, clip01, efMin, EF.denoteWith, EF.denote]

/-- **Lemma F on FAF's diagonal** (**N−**, audit r1 B2): with `X := χ` and the gate
`λ_n := Ind_δ(p − δ > P_n(χ_n))` (legal, fires only when `P_n(χ_n) < p − δ < p`, i.e. when `χ_n`
is true), `λ_n · (1 − P_n(χ_n)) → 0`. The full hypothesis package of `gated_forcing` is inhabited
on the real diagonal, but the gate is eventually *exactly* `0` (T1, `ramp_silence_below` at the
constant margin `δ`), so the conclusion holds on the tail by `0 · x = 0` without Lemma F: the
forcing content (price pushed to `1` where the gate fires) is never exercised. Degenerate, and
necessarily so in the limit for any gate keyed to the diagonal's own threshold — the "general
principle" of §3.1 (with a positive e.c. margin the gate is eventually exactly `0`; at margin `0`
it tends to `0`, `ramp_margin_zero_tendsto_zero`, and its exact silence is E2). The N+ witness is
`gated_forcing_pastPrice_const` / `_alternating` (`PastPrice.lean`).
Scope: single-market; threshold `p`; FAF's same-day diagonal.
Source: [[route-negative-introspective]] §3.1; [[vq-wiki-inventory]] 059; [[li-diagonal-mandate]] T6a instance
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem gated_forcing_diagonal (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (p : ℚ) (q : ParadoxResistanceQuote P DP p) (δ : ℚ) (hδ : 0 < δ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => ctsInd δ ((p : ℝ) - δ) (P n (q.sentence n)) * (1 - P n (q.sentence n))) ≈ₙ
      fun _ => 0 := by
  have htruth : AffineCombination.TheoryTruth q.sentence DP (diagTruth P q.sentence p) := by
    intro n v hv
    unfold PCWorld.payout diagTruth
    by_cases hlt : P n (q.sentence n) < (p : ℝ)
    · rw [if_pos ((q.diagonal_reflected n v hv).2 hlt), if_pos hlt]
    · rw [if_neg (fun h => hlt ((q.diagonal_reflected n v hv).1 h)), if_neg hlt]
  have h := gated_forcing P DP q.sentence q.sentence_codes _ htruth
    (priceRampBelow q.sentence (p - δ) δ) (priceRampBelow_pgenerable _ q.sentence_codes _ _) 1
    (fun n => by
      rw [priceRampBelow_denote _ hδ, abs_of_nonneg (ctsInd_nonneg _ _ _)]
      exact ctsInd_le_one _ _ _)
    (fun n hne => by
      rw [priceRampBelow_denote _ hδ] at hne
      have hpos : 0 < ctsInd δ ((p - δ : ℚ) : ℝ) (P n (q.sentence n)) :=
        lt_of_le_of_ne (ctsInd_nonneg _ _ _) (Ne.symm hne)
      have hlt := (ctsInd_pos_iff hδ _ _).1 hpos
      have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
      unfold diagTruth
      rw [if_pos (by push_cast at hlt; linarith)])
    hworld
  have heq : (fun n => (priceRampBelow q.sentence (p - δ) δ n).denote P *
      (1 - P n (q.sentence n))) =
      fun n => ctsInd δ ((p : ℝ) - δ) (P n (q.sentence n)) * (1 - P n (q.sentence n)) := by
    funext n; rw [priceRampBelow_denote _ hδ]; push_cast; rfl
  rwa [heq] at h

/-! ## Lemma F, the source's summable form (audit r1, B1) -/

/-- The trader that buys `λ_n` shares of `X_n` on day `n` (Lemma F's trader, vq-wiki-059; the
rank certificate of the gate is the strategy's `rank_le`).
Source: [[route-negative-introspective]] §5.1 (Lemma F's proof); [[vq-wiki-inventory]] 059
Kind: D
Fidelity: exact
Hyps: n/a -/
def gatedTrader (X : ℕ → Sentence) (lam : ℕ → EF) (hrank : ∀ n, (lam n).rank ≤ n) : Trader :=
  ⟨fun n => ⟨[(lam n, X n)], fun p hp => by
    simp only [List.mem_singleton] at hp
    subst hp
    exact hrank n⟩⟩

/-- The trader that sells `μ_n` shares of `X_n` on day `n` (coefficient `−μ_n`).
Source: [[route-negative-introspective]] §5.1 (Lemma F's mirror trader)
Kind: D
Fidelity: exact
Hyps: n/a -/
def gatedTraderNeg (X : ℕ → Sentence) (mu : ℕ → EF) (hrank : ∀ n, (mu n).rank ≤ n) : Trader :=
  ⟨fun n => ⟨[(EF.mul (EF.const (-1)) (mu n), X n)], fun p hp => by
    simp only [List.mem_singleton] at hp
    subst hp
    simpa using hrank n⟩⟩

/-- The gated buy trader is efficiently computable for e.c. `X` and a legal gate: the gate's own
splice stream, the trade frame `[6, ⌜X_n⌝]` at the identity ruler, `MachineSpliceStream.ec`.
Source: none: infrastructure (FAF `EfficientlyComputable.ofSingleTradeBlocksBig`'s assembly, with a price-reading coefficient)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gatedTrader_ec (X : ℕ → Sentence) (hX : MachineSentenceCodes X) (lam : ℕ → EF)
    (hlam : PGenerableWeighting lam) : EfficientlyComputable (gatedTrader X lam hlam.rank_le) := by
  have hslot : MachineSpliceStream (fun n => [6, Encodable.encode (X n)]) :=
    (MachineSpliceStream.tradeSlot hX (f := fun n => n) UnaryRuler.id).of_eq (fun _ => rfl)
  refine MachineSpliceStream.ec _ ((hlam.polySeg.append hslot).of_eq (fun n => ?_))
  simp [gatedTrader, serializeTrades]

/-- The gated sell trader is efficiently computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gatedTraderNeg_ec (X : ℕ → Sentence) (hX : MachineSentenceCodes X) (mu : ℕ → EF)
    (hmu : PGenerableWeighting mu) :
    EfficientlyComputable (gatedTraderNeg X mu hmu.rank_le) := by
  have hslot : MachineSpliceStream (fun n => [6, Encodable.encode (X n)]) :=
    (MachineSpliceStream.tradeSlot hX (f := fun n => n) UnaryRuler.id).of_eq (fun _ => rfl)
  have hcoef := MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1))
    hmu.polySeg
  refine MachineSpliceStream.ec _ ((hcoef.append hslot).of_eq (fun n => ?_))
  simp [gatedTraderNeg, serializeTrades]

/-- `gatedTrader_netWorth`: `∑_{i ≤ n} λ_i · (payout(X_i) − P_i(X_i))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedTrader_netWorth (X : ℕ → Sentence) (lam : ℕ → EF) (hrank : ∀ n, (lam n).rank ≤ n)
    (P : History) (v : PCWorld) (n : ℕ) :
    (gatedTrader X lam hrank).netWorth P v n =
      ∑ i ∈ Finset.range (n + 1), (lam i).denote P * (v.payout (X i) - P i (X i)) := by
  unfold Trader.netWorth
  simp [gatedTrader, Strategy.value]

/-- `gatedTraderNeg_netWorth`: `∑_{i ≤ n} μ_i · (P_i(X_i) − payout(X_i))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedTraderNeg_netWorth (X : ℕ → Sentence) (mu : ℕ → EF) (hrank : ∀ n, (mu n).rank ≤ n)
    (P : History) (v : PCWorld) (n : ℕ) :
    (gatedTraderNeg X mu hrank).netWorth P v n =
      ∑ i ∈ Finset.range (n + 1), (mu i).denote P * (P i (X i) - v.payout (X i)) := by
  unfold Trader.netWorth
  simp only [gatedTraderNeg, Strategy.value, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, EF.denote_mul, EF.denote_const, Pi.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A trader whose net worth in every plausible world is a nonnegative partial sum with
unbounded partial sums exploits the market (bounded below by `0`, unbounded above).
Source: none: infrastructure (FAF `exploits_of_bddBelow_of_unbounded`; the engine behind vq-wiki-059's "sum converges")
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem exploits_of_partialSums_unbounded (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (w : ℕ → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hval : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      Tr.netWorth P v n = ∑ i ∈ Finset.range (n + 1), w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tr.Exploits P DP := by
  refine exploits_of_bddBelow_of_unbounded Tr P DP 0 ?_ ?_
  · rintro x ⟨n, v, hv, rfl⟩
    rw [hval n v hv, neg_zero]
    exact Finset.sum_nonneg fun i _ => hw0 i
  · intro B
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atTop.1 hdiv (B + 1))
    obtain ⟨v, hv⟩ := hworld N
    refine ⟨_, ⟨N, v, hv, rfl⟩, ?_⟩
    rw [hval N v hv, Finset.sum_range_succ]
    linarith [hN N le_rfl, hw0 N]

/-- **T6a, Lemma F in the source's summable form**: for an e.c. family `X` and a legal
nonnegative gate `λ` that fires only on days where `X_n` is **already in the process by day `n`**
(stage-decidedness: `λ_n ≠ 0 → X_n ∈ D_n`), `∑_n λ_n · (1 − P_n(X_n)) < ∞`. The buy trader
`λ_n · X_n` has net worth `∑_{i ≤ n} λ_i(1 − P_i(X_i))` in every world consistent with `D_n`
(fired shares pay `1`), nonnegative; unbounded partial sums would exploit the market
(`IsLogicalInductor.noExploit`), so the series is summable. Compare `gated_forcing`
(weaker hypothesis, weaker conclusion).
Scope: single-market; any e.c. family `X`.
Source: [[route-negative-introspective]] §5.1 (Lemma F, as stated and proved there); [[vq-wiki-inventory]] 059
Kind: C
Fidelity: exact (the source's hypothesis and conclusion; `hnonneg` is implicit in the source's ramp gates)
Hyps: (a) none -/
theorem gated_forcing_summable (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : ℕ → Sentence) (hX : MachineSentenceCodes X)
    (lam : ℕ → EF) (hlam : PGenerableWeighting lam) (hnonneg : ∀ n, 0 ≤ (lam n).denote P)
    (hdec : ∀ n, (lam n).denote P ≠ 0 → X n ∈ DP.D n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Summable (fun n => (lam n).denote P * (1 - P n (X n))) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  set w : ℕ → ℝ := fun n => (lam n).denote P * (1 - P n (X n)) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n =>
    mul_nonneg (hnonneg n) (by linarith [(hP n (X n)).2])
  have hmono : Monotone DP.D := monotone_nat_of_le_succ DP.mono
  have hval : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      (gatedTrader X lam hlam.rank_le).netWorth P v n = ∑ i ∈ Finset.range (n + 1), w i := by
    intro n v hv
    rw [gatedTrader_netWorth]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hl : (lam i).denote P = 0
    · simp [hw, hl]
    · have hmem : X i ∈ DP.D n := hmono (by omega : i ≤ n) (hdec i hl)
      have hpay : v.payout (X i) = 1 := by
        unfold PCWorld.payout; rw [if_pos (hv _ hmem)]
      simp [hw, hpay]
  by_contra hns
  have hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop := by
    by_contra h
    exact hns ((summable_iff_not_tendsto_nat_atTop_of_nonneg hw0).2 h)
  exact IsLogicalInductor.noExploit _ (gatedTrader_ec X hX lam hlam)
    (exploits_of_partialSums_unbounded _ P DP w hw0 hval hdiv hworld)

/-- **Lemma F, mirror, summable form**: a legal nonnegative gate `μ` firing only where `∼X_n` is
already in the process by day `n` has `∑_n μ_n · P_n(X_n) < ∞` (the sell trader).
Scope: single-market; any e.c. family `X`.
Source: [[route-negative-introspective]] §5.1 (Lemma F's mirror); [[vq-wiki-inventory]] 059
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem gated_forcing_neg_summable (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : ℕ → Sentence) (hX : MachineSentenceCodes X)
    (mu : ℕ → EF) (hmu : PGenerableWeighting mu) (hnonneg : ∀ n, 0 ≤ (mu n).denote P)
    (hdec : ∀ n, (mu n).denote P ≠ 0 → ∼ X n ∈ DP.D n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Summable (fun n => (mu n).denote P * P n (X n)) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  set w : ℕ → ℝ := fun n => (mu n).denote P * P n (X n) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => mul_nonneg (hnonneg n) (hP n (X n)).1
  have hmono : Monotone DP.D := monotone_nat_of_le_succ DP.mono
  have hval : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      (gatedTraderNeg X mu hmu.rank_le).netWorth P v n = ∑ i ∈ Finset.range (n + 1), w i := by
    intro n v hv
    rw [gatedTraderNeg_netWorth]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hl : (mu i).denote P = 0
    · simp [hw, hl]
    · have hmem : ∼ X i ∈ DP.D n := hmono (by omega : i ≤ n) (hdec i hl)
      have hholds : v.Holds (∼ X i) := hv _ hmem
      rw [PCWorld.holds_neg] at hholds
      have hpay : v.payout (X i) = 0 := by
        unfold PCWorld.payout; rw [if_neg hholds]
      simp [hw, hpay]
  by_contra hns
  have hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop := by
    by_contra h
    exact hns ((summable_iff_not_tendsto_nat_atTop_of_nonneg hw0).2 h)
  exact IsLogicalInductor.noExploit _ (gatedTraderNeg_ec X hX mu hmu)
    (exploits_of_partialSums_unbounded _ P DP w hw0 hval hdiv hworld)

/-- The day-`k` cutoff indicator `𝟙[k ≤ n]` as a legal feature progression (FAF's
`UnaryRuler.ite_lt_const` written out as a constant leaf).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem cutoffIndicator_pgenerable (k : ℕ) :
    PGenerableWeighting (fun n => EF.const (if n < k then 0 else 1)) := by
  have hdig : MachineDigits (fun n : ℕ => Encodable.encode (if n < k then (0 : ℚ) else 1)) := by
    refine (MachineDigits.ofUnaryRuler
      (UnaryRuler.ite_lt_const k (Encodable.encode (0 : ℚ)) (Encodable.encode (1 : ℚ)))).of_eq
      fun n => ?_
    split_ifs <;> rfl
  refine { polySeg := MachineSpliceStream.serialize_const_write hdig, rank_le := ?_, closed := ?_ }
  · intro n; simp
  · intro n ρ V; simp [EF.denoteWith, EF.denote]

/-- **Summable provability induction** (Lemma F's summable form at a constant family, gate
`𝟙[k ≤ n]`): a sentence lying in stage `k` of the process has `∑_n (1 − P_n(φ)) < ∞`, not merely
`P_n(φ) → 1` (`lic_provind_true`). Non-vacuity witness of `gated_forcing_summable`, graded
**N−** (constant family, eventually-constant gate) — but a genuine strengthening of `thm:provind`
on that family.
Scope: single-market.
Source: [[route-negative-introspective]] §5.1 (Lemma F's summable form, specialized); LI `thm:provind`
Kind: N−
Fidelity: stronger (summable in place of `→ 1`)
Hyps: (a) none -/
theorem price_summable_of_mem (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : Sentence) (k : ℕ) (hk : φ ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Summable (fun n => 1 - P n φ) := by
  have hmono : Monotone DP.D := monotone_nat_of_le_succ DP.mono
  have h := gated_forcing_summable P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun n => EF.const (if n < k then 0 else 1)) (cutoffIndicator_pgenerable k)
    (fun n => by rw [EF.denote_const]; split_ifs <;> norm_num)
    (fun n hn => by
      rw [EF.denote_const] at hn
      have hkn : k ≤ n := by
        by_contra hlt
        push Not at hlt
        rw [if_pos hlt] at hn
        exact hn (by norm_num)
      exact hmono hkn hk)
    hworld
  rw [← summable_nat_add_iff k] at h ⊢
  refine h.congr fun n => ?_
  rw [EF.denote_const, if_neg (by omega : ¬ n + k < k)]
  simp

/-- **Summable refutation**: a sentence whose negation lies in stage `k` has `∑_n P_n(φ) < ∞`.
Scope: single-market.
Source: [[route-negative-introspective]] §5.1 (Lemma F's mirror, specialized); LI `thm:provind`
Kind: N−
Fidelity: stronger (summable in place of `→ 0`)
Hyps: (a) none -/
theorem price_summable_of_neg_mem (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : Sentence) (k : ℕ) (hk : ∼ φ ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Summable (fun n => P n φ) := by
  have hmono : Monotone DP.D := monotone_nat_of_le_succ DP.mono
  have h := gated_forcing_neg_summable P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun n => EF.const (if n < k then 0 else 1)) (cutoffIndicator_pgenerable k)
    (fun n => by rw [EF.denote_const]; split_ifs <;> norm_num)
    (fun n hn => by
      rw [EF.denote_const] at hn
      have hkn : k ≤ n := by
        by_contra hlt
        push Not at hlt
        rw [if_pos hlt] at hn
        exact hn (by norm_num)
      exact hmono hkn hk)
    hworld
  rw [← summable_nat_add_iff k] at h ⊢
  refine h.congr fun n => ?_
  rw [EF.denote_const, if_neg (by omega : ¬ n + k < k)]
  simp

end Cleanroom.Li.LiDiagonal
