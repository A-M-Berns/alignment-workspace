import Cleanroom.Li.LiDiagonal.Defs
import Cleanroom.Found.LiAsympCalc.Ramp
import LogicalInduction.Construction.Quotation.Packages

/-!
# `li-diagonal` · Pinned: pinning beats every e.c. rate (T1)

The sharpened `thm:lp`. FAF's `ParadoxResistanceQuote` package carries two affine certificates
whose gaps are `ctsInd (width n) p (P n χ_n) · (1 − P n χ_n)` and
`ctsInd (width n) (P n χ_n) p · P n χ_n`; `CompletedAffineQuoteEq.gap_asympEq_zero` says each
gap `≈ₙ 0`. FAF's ramp `ctsInd δ x y = min 1 (max 0 ((x − y)/δ))` is fully on once `x − y ≥ δ`,
so a price `≤ p − width n` makes the lower gap `≥ 1 − p`, and a price `≥ p + width n` makes the
upper gap `≥ p`: neither can happen eventually. Hence **eventually `|P n χ_n − p| < width n`** —
and since FAF's Kleene diagonal sentence family depends on `(market, T, p)` only, with `width`
entering the package's certificates alone, one sentence family is pinned within *every* e.c.
rate at once (`paradox_pinned_every_rate`). That is vq-wiki-2-014's "pinning beats every
efficiently computable rate" with constant `1`, strict, uniform in the rate (the note's constant
`2` is its own ramp's width convention; K3).

Corollaries: `thm:lp` re-derived (`paradox_resistance_of_pinned`); **ramp silence** — every
e.c. ramp around `p` on the diagonal's price is eventually `0`
(`ramp_silence_above`/`_below`, `ramp_silence_every_rate`), the precise form of "Introspection
has nothing to bite on" (`lic_introspection`'s affirmative clause needs a margin
`a n + δ n < P n (φ n)`, which never holds eventually at `a n = p`:
`introspection_margin_fails`).

Scope: single-market throughout; FAF's same-day `χ^p_n`. The `N+` witnesses over
`liaHistory (paperDP T)` are in `Paper.lean`.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Filter Topology

/-! ## T1 over an abstract package -/

/-- **T1 (headline). The diagonal's price is pinned within the package's width**: for a logical
inductor and a `ParadoxResistanceQuote` at `p ∈ (0,1)`, eventually `|P n χ_n − p| < width n`.
Strictly stronger than FAF's `lic_paradox_resistance` (`thm:lp`, which concludes only
`P n χ_n ≈ₙ p`): the rate is the package's own width, with constant `1`. Proof: the two affine
certificates' gaps vanish (`gap_asympEq_zero`); a price `≤ p − width n` turns the lower ramp fully
on (`ctsInd_eq_one_of_le_sub`) and makes the lower gap `1 − P n χ_n ≥ 1 − p`, which is not
eventually `≤ (1−p)/2`; dually above with the upper gap `≥ p`. `hp0`/`hp1` are needed: at
`p ∈ {0,1}` one of the gap bounds degenerates to `0`.
Scope: single-market; threshold `p`; FAF's same-day diagonal `χ^p_n` (any `ParadoxResistanceQuote`).
Source: [[vq-wiki-2-inventory]] 014 (pinning beats every e.c. rate); [[lean-deference-inventory]] 048 (Forcing Theorem A, single-market core); LI paper `thm:lp`
Kind: P
Fidelity: stronger — constant `1`, strict, and at the package's own width (the note's `2` is its ramp convention, K3)
Hyps: (a) none beyond FAF's package (`IsLogicalInductor`, `ParadoxResistanceQuote`, `hworld`) -/
theorem paradox_pinned_within_width (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ParadoxResistanceQuote P DP p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ n in atTop, |P n (q.sentence n) - (p : ℝ)| < (q.width n : ℝ) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hlower := asympEq_iff_eventuallyWithin.1 (q.lower_affine.gap_asympEq_zero hworld)
    ((1 - p) / 2) (by linarith)
  have hupper := asympEq_iff_eventuallyWithin.1 (q.upper_affine.gap_asympEq_zero hworld)
    (p / 2) (by linarith)
  filter_upwards [hlower, hupper] with n hlo hhi
  simp only [_root_.sub_zero] at hlo hhi
  have hw : (0 : ℝ) < q.width n := by exact_mod_cast q.width_pos n
  rw [abs_lt]
  constructor
  · by_contra hnot
    push_neg at hnot
    have hgate : ctsInd (q.width n) (p : ℝ) (P n (q.sentence n)) = 1 :=
      ctsInd_eq_one_of_le_sub _ _ _ (q.width_pos n) (by linarith)
    rw [hgate, one_mul, abs_of_nonneg (by linarith [(hP n (q.sentence n)).2])] at hlo
    linarith
  · by_contra hnot
    push_neg at hnot
    have hgate : ctsInd (q.width n) (P n (q.sentence n)) (p : ℝ) = 1 :=
      ctsInd_eq_one_of_le_sub _ _ _ (q.width_pos n) (by linarith)
    rw [hgate, one_mul, abs_of_nonneg (hP n (q.sentence n)).1] at hhi
    linarith

/-- **`thm:lp` re-derived from pinning**: `P n χ_n ≈ₙ p`, as the squeeze of
`paradox_pinned_within_width` against `width → 0`. Recorded to show the sharpened statement
really contains FAF's; no new content.
Scope: single-market; threshold `p`; FAF's same-day diagonal.
Source: LI paper `thm:lp`; FAF `lic_paradox_resistance`
Kind: L
Fidelity: exact (FAF's conclusion)
Hyps: (a) none -/
theorem paradox_resistance_of_pinned (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ParadoxResistanceQuote P DP p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (q.sentence n)) ≈ₙ fun _ => (p : ℝ) := by
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  filter_upwards [paradox_pinned_within_width P DP p hp0 hp1 q hworld,
    q.width_tendsto_zero (Iio_mem_nhds hε)] with n h1 h2
  exact h1.le.trans (le_of_lt h2)

/-! ## T1 over FAF's Kleene diagonal: one family, every rate -/

/-- **T1 (headline). Pinning beats every e.c. rate.** For FAF's genuine Kleene diagonal
`ψ := (parameterizedDiagonalQuoteCodeOfMarket market T p).sentence` — a sentence family that
depends on `(market, T, p)` only — and *every* e.c. width `width → 0` (certificate
`MachineRatCodes (1 / width)`), eventually `|P n (ψ n) − p| < width n`. The width is not a
hypothesis on the sentence: `paradoxResistanceQuoteOfDiagonal` builds a package whose sentence
field is `ψ` and whose width is the given one, and `paradox_pinned_within_width` applies. This
answers the plan's "is `2η_k` tight": no e.c. rate is beaten by less than constant `1`.
Scope: single-market; threshold `p`; FAF's same-day Kleene diagonal.
Source: [[vq-wiki-2-inventory]] 014; [[li-diagonal-mandate]] T1, E1
Kind: C
Fidelity: stronger — constant `1`, strict, uniform in the rate (one family for all rates)
Hyps: (a) none (`hwidth` is the e.c. certificate of the *rate*, the quantity the claim is about) -/
theorem paradox_pinned_every_rate {DP : DeductiveProcess} {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]
    (Q : QuotationTheoryPresentation DP T) (P : History) [IsLogicalInductor P DP]
    (market : MarketComputation P) (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (width : ℕ → ℚ) (hwidth : MachineRatCodes (fun n => 1 / width n))
    (hwidthPos : ∀ n, 0 < width n)
    (hwidthZero : Tendsto (fun n => (width n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      |P n ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n)
        - (p : ℝ)| < (width n : ℝ) :=
  paradox_pinned_within_width P DP p hp0 hp1
    (paradoxResistanceQuoteOfDiagonal Q market p width hwidth hwidthPos hwidthZero) hworld

/-! ## Ramp silence -/

/-- **Ramp silence, above**: on a pinned diagonal, every ramp `ctsInd (δ n) (P n χ_n) (p + η n)`
whose threshold margin `η n` eventually dominates the pinning width is eventually `0`.
Scope: single-market; threshold `p`; any `ParadoxResistanceQuote`.
Source: [[route-negative-introspective]] §3.1 ("Introspection has nothing to bite on"); [[li-diagonal-mandate]] T1 corollary
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ramp_silence_above (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ParadoxResistanceQuote P DP p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (η : ℕ → ℚ) (hη : ∀ᶠ n in atTop, q.width n ≤ η n) (δ : ℕ → ℚ) (hδ : ∀ n, 0 < δ n) :
    ∀ᶠ n in atTop, ctsInd (δ n) (P n (q.sentence n)) ((p : ℝ) + η n) = 0 := by
  filter_upwards [paradox_pinned_within_width P DP p hp0 hp1 q hworld, hη] with n h1 h2
  have h2R : (q.width n : ℝ) ≤ η n := by exact_mod_cast h2
  rw [ctsInd_eq_zero_iff (hδ n)]
  have := (abs_lt.1 h1).2
  linarith

/-- **Ramp silence, below**: the mirror `ctsInd (δ n) (p − η n) (P n χ_n)` is eventually `0`.
Scope: single-market; threshold `p`; any `ParadoxResistanceQuote`.
Source: [[route-negative-introspective]] §3.1; [[li-diagonal-mandate]] T1 corollary
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ramp_silence_below (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ParadoxResistanceQuote P DP p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (η : ℕ → ℚ) (hη : ∀ᶠ n in atTop, q.width n ≤ η n) (δ : ℕ → ℚ) (hδ : ∀ n, 0 < δ n) :
    ∀ᶠ n in atTop, ctsInd (δ n) ((p : ℝ) - η n) (P n (q.sentence n)) = 0 := by
  filter_upwards [paradox_pinned_within_width P DP p hp0 hp1 q hworld, hη] with n h1 h2
  have h2R : (q.width n : ℝ) ≤ η n := by exact_mod_cast h2
  rw [ctsInd_eq_zero_iff (hδ n)]
  have := (abs_lt.1 h1).1
  linarith

/-- **Ramp silence on the Kleene diagonal, every e.c. rate**: for every e.c. `δ → 0`, both ramps
`ctsInd (δ n) (P n (ψ n)) (p + δ n)` and `ctsInd (δ n) (p − δ n) (P n (ψ n))` are eventually `0`
on FAF's diagonal of `(market, T, p)`. The precise form of "Introspection has nothing to bite on"
([[route-negative-introspective]] §3.1): the general principle that a legal gate keyed to the
diagonal's own price above/below its threshold is eventually silent.
Scope: single-market; threshold `p`; FAF's same-day Kleene diagonal.
Source: [[route-negative-introspective]] §3.1 (vq-wiki-059/060's "general principle"); [[li-diagonal-mandate]] T1 corollary, T6a's last sentence
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ramp_silence_every_rate {DP : DeductiveProcess} {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]
    (Q : QuotationTheoryPresentation DP T) (P : History) [IsLogicalInductor P DP]
    (market : MarketComputation P) (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (δ : ℕ → ℚ) (hδ : MachineRatCodes (fun n => 1 / δ n)) (hδPos : ∀ n, 0 < δ n)
    (hδZero : Tendsto (fun n => (δ n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ctsInd (δ n)
        (P n ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n))
        ((p : ℝ) + δ n) = 0 ∧
      ctsInd (δ n) ((p : ℝ) - δ n)
        (P n ((parameterizedDiagonalQuoteCodeOfMarket market T p).toBooleanQuoteCode.sentence n))
        = 0 := by
  have hpin := paradox_pinned_every_rate Q P market p hp0 hp1 hworld δ hδ hδPos hδZero
  filter_upwards [hpin] with n h1
  obtain ⟨hlo, hhi⟩ := abs_lt.1 h1
  constructor
  · rw [ctsInd_eq_zero_iff (hδPos n)]; linarith
  · rw [ctsInd_eq_zero_iff (hδPos n)]; linarith

/-- **Introspection's margin fails on the diagonal**: `lic_introspection`'s affirmative clause
asks for `a n + δ n < P n (φ n)`; at `a n := p` on a pinned diagonal this never holds eventually,
for any `δ` dominating the width — and dually for the clause `P n (φ n) < b n − δ n` at
`b n := p`. So the introspection package, applied to the interval `(p, p)` around the diagonal's
own threshold, certifies nothing about the diagonal's price: its hypotheses are eventually false.
Scope: single-market; threshold `p`; any `ParadoxResistanceQuote`.
Source: [[route-negative-introspective]] §3.1; [[li-diagonal-mandate]] T1 corollary
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem introspection_margin_fails (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ParadoxResistanceQuote P DP p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (δ : ℕ → ℚ) (hδ : ∀ᶠ n in atTop, q.width n ≤ δ n) :
    ∀ᶠ n in atTop, ¬ ((p : ℝ) + δ n < P n (q.sentence n)) ∧
      ¬ (P n (q.sentence n) < (p : ℝ) - δ n) := by
  filter_upwards [paradox_pinned_within_width P DP p hp0 hp1 q hworld, hδ] with n h1 h2
  have h2R : (q.width n : ℝ) ≤ δ n := by exact_mod_cast h2
  obtain ⟨hlo, hhi⟩ := abs_lt.1 h1
  exact ⟨fun h => by linarith, fun h => by linarith⟩

/-! ## Ramps at margin `0` (repair round 2) -/

/-- **The margin-`0` ramps are silent only in the limit** (repair round 2; audit r2 adversarial
N2, probe `MarginZeroRamp.lean`). `ramp_silence_above/below` need a margin `η` dominating the
pinning width; the ramps keyed *exactly* at `p` — `Ind_δ(p > P_n(χ_n))` and `Ind_δ(P_n(χ_n) > p)`,
equally legal, firing exactly where `χ_n` is true (resp. false) — are not covered. What T1 gives
for them is the bound `width n / δ`, hence `→ 0`; their *exact* eventual silence is the two halves
of E2 (`paper_kleene_exact_pinning`), open. So "every legal ramp around `p` is eventually exactly
`0`" (F-12's first wording) holds with a positive e.c. margin; at margin `0` the honest statement
is this one.
Scope: single-market; threshold `p`; any `ParadoxResistanceQuote`.
Source: [[route-negative-introspective]] §3.1; [[li-diagonal-mandate]] T1 corollary, E2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ramp_margin_zero_le_width (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ParadoxResistanceQuote P DP p) (δ : ℚ) (hδ : 0 < δ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ n in atTop, ctsInd δ (p : ℝ) (P n (q.sentence n)) ≤ (q.width n : ℝ) / δ ∧
      ctsInd δ (P n (q.sentence n)) (p : ℝ) ≤ (q.width n : ℝ) / δ := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  filter_upwards [paradox_pinned_within_width P DP p hp0 hp1 q hworld] with n hn
  obtain ⟨hlo, hhi⟩ := abs_lt.1 hn
  have hw : (0 : ℝ) < q.width n := by exact_mod_cast q.width_pos n
  constructor
  · unfold ctsInd
    refine (min_le_right _ _).trans (max_le (div_nonneg hw.le hδR.le) ?_)
    exact div_le_div_of_nonneg_right (by linarith) hδR.le
  · unfold ctsInd
    refine (min_le_right _ _).trans (max_le (div_nonneg hw.le hδR.le) ?_)
    exact div_le_div_of_nonneg_right (by linarith) hδR.le

/-- **The margin-`0` ramps tend to `0`** on a pinned diagonal (the limit form of
`ramp_margin_zero_le_width`): degenerate for Lemma F in the limit, but not provably exactly `0`.
Scope: single-market; threshold `p`; any `ParadoxResistanceQuote`.
Source: [[route-negative-introspective]] §3.1; [[li-diagonal-mandate]] T1 corollary
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ramp_margin_zero_tendsto_zero (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ParadoxResistanceQuote P DP p) (δ : ℚ) (hδ : 0 < δ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => ctsInd δ (p : ℝ) (P n (q.sentence n))) atTop (𝓝 0) ∧
    Tendsto (fun n => ctsInd δ (P n (q.sentence n)) (p : ℝ)) atTop (𝓝 0) := by
  have hbound := ramp_margin_zero_le_width P DP p hp0 hp1 q δ hδ hworld
  have hwz : Tendsto (fun n => (q.width n : ℝ) / δ) atTop (𝓝 0) := by
    simpa using q.width_tendsto_zero.div_const (δ : ℝ)
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwz
      (Eventually.of_forall fun n => ctsInd_nonneg _ _ _) (hbound.mono fun n h => h.1)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwz
      (Eventually.of_forall fun n => ctsInd_nonneg _ _ _) (hbound.mono fun n h => h.2)

/-- **Exact silence of the margin-`0` ramp is E2's upper half**: the ramp `Ind_δ(p > P_n(χ_n))`
is `0` on day `n` iff `p ≤ P_n(χ_n)`, so "eventually exactly `0`" for it is "eventually
`P_n(χ_n) ≥ p`" — one half of `paper_kleene_exact_pinning` (open).
Scope: single-market; threshold `p`.
Source: [[li-diagonal-mandate]] E2; audit r2 adversarial N2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ramp_margin_zero_eq_zero_iff (P : History) (χ : ℕ → Sentence) (p δ : ℚ) (hδ : 0 < δ)
    (n : ℕ) : ctsInd δ (p : ℝ) (P n (χ n)) = 0 ↔ (p : ℝ) ≤ P n (χ n) :=
  ctsInd_eq_zero_iff hδ _ _

end Cleanroom.Li.LiDiagonal
