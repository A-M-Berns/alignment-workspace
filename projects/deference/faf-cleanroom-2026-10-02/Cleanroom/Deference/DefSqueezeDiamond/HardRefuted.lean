import Cleanroom.Found.DefLattice.Witness
import Cleanroom.Deference.DefLatticeArrows.Packages
import LogicalInduction.Construction.Quotation.MarketQuoteCodes
import LogicalInduction.Construction.Paper.Market

/-!
# `def-squeeze-diamond` · HardRefuted: hard Total Trust toward the future self is false (target 7)

**The sources, quoted** (repair round 1: the round-1 record cited "v6 §1.6 l. 251" for a
sentence that is root-deference-013 (ii)'s *gloss*, not v6's text). The primary source is the LI
paper, `main.tex` ll. 2117–2127 (§4.12, via [[reflection-in-li]]): "Let each $\phi_n$ be the
self-referential sentence $\ulcorner \mathbb P_{f(n)}(\phi_n) < 0.5 \urcorner$ which says
that the future $\mathbb P_{f(n)}$ will assign probability less than 0.5 to $\phi_n$. Then,
conditional on $\mathbb P_{f(n)}(\phi_n) \ge 0.5$, $\mathbb P_n$ should believe that the
probability of $\phi_n$ is 0. And indeed, this is what a logical inductor will do:
$\mathbb P_n(\ulcorner \phi_n \wedge (\mathbb P_{f(n)}(\phi_n) \ge 0.5) \urcorner)
\eqsim_n 0$, by Theorem perkno, because each of those conjunctions is disprovable. This is why
Thm st uses continuous indicator functions: With discrete conjunctions, the result would be
undesirable (not to mention false)." The corpus's own words are v6 §1.6 l. 234, "a hard
$\mathbb 1[E^*(X) > t]$ is discontinuous (illegal as a weight) and liar-prone", and the end of
l. 249, "$\mathbb 1[E^*(X) > t]$ is the liar-prone event the inductor refuses to evaluate
sharply (the refusal that *protects* it from paradox)"; neither says the hard tower *fails* on
the diagonal — that wording is root-013 (ii)'s gloss of the LI paper. Over FAF, with
`def-lattice`'s predicates:

* **The deferred-day liar** `DeferredLiar P DP f p`: an e.c. sentence family with
  `v.Holds (φ n) ↔ P (f n) (φ n) < p` in every completed-theory world — FAF's
  `ParadoxResistanceQuote.diagonal_reflected` with the day moved to `f n` and the affine
  certificates dropped. **Inhabited at grade (a)** (`deferredLiarOfDiagonal`): FAF's
  `parameterizedDiagonalQuoteCodeOfMarket` takes any `MarketComputation`, and the deferred
  history `n ↦ P (f n)` has one (`deferredMarket`: the quote table `(n, s) ↦ quote (f n) s`,
  computable because `DeferralFunction.computable`), so FAF's same-day diagonal over the
  deferred market *is* the deferred-day liar. No new fixed point is built.
* **Sharp weights as quoted decided LUVs** (design decision 5): `sharpAboveValue`,
  `sharpBelowValue` are the computable `{0,1}`-sequences `1[½ ≤ quote (g n) (φ n)]`,
  `1[quote (g n) (φ n) ≤ ½]`; `RationalQuoteCode.ofComputable` quotes them, the indicator
  products are `indicatorProductLUV`, and for the self-expert on the literal-indicator source
  these are `WeightQuote`s at `hardAbove ½` / `hardBelow ½` with `slack ≡ 0`
  (`hardAboveQuote`, `hardBelowQuote`). `def-lattice`'s `no_generable_hard_indicator` is about
  trade *weights* (`EF` features) and is untouched: nothing here is a feature.
* **The refutation** (`hardTotalTrust_refuted`, `hardTotalTrust_refuted_paper`): on the liar
  family the above-face product `XW` is valued `0` in every world (where the weight is `1` the
  sentence is false) and the below-face product `XW'` is valued `1 − W` (checked at the
  boundary `P = ½`: `W = W' = 1`, sentence false, `XW' = 0 = 1 − W`); `thm:expprovind` on
  `[XW]` and `[XW', W]` gives `E_n(XW) ≈ₙ 0`, `E_n(XW') ≈ₙ 1 − E_n(W)`; the above face forces
  `E_n(W) → 0`, the below face with `E_n(W') ≤ 1` forces `E_n(W) ≳ₙ ½`. Contradiction, with no
  assumption on which side of `½` the deferred price sits — paradox resistance is not used.
* **The same-day instance** (`sameDay_hard_faces_refuted`, N+): FAF's own
  `paperDiagonalQuoteCode T ½` with the day map `id`; not a `def-lattice` notion (an `Expert`
  needs `f n > n`), stated as a bare theorem about `P` — the kernel-checked sanity instance of
  the argument with no deferred object at all.
* **The surviving neighbour**: `def-self-trust`'s `selfTotalTrust` (soft, both faces, every
  threshold). The refuted object is the **conjunction** of the two hard faces at `½`:
  `HardTotalTrustAbove ½` alone is **not refuted by this family** (on it the above face reduces
  to `E_n(W) ≲ₙ 0`, which holds whenever the deferred price is eventually below `½`); see the
  register below and the report.

Register (plan §0.4 rule 3). What is refuted is `def-lattice`'s two-faced `HardTotalTrust` at
`½` with `hardAbove ½ = 1[½ ≤ ·]` and `hardBelow ½ = 1[· ≤ ½]` — the LI paper's `≥ 0.5`
convention (`sharpAboveValue_cast`, `sharpBelowValue_cast`). Three register notes. (i) **Which
object**: relative to that predicate the refutation is exact; relative to the LI paper's claim it
is *weaker* — the paper's "(not to mention false)" is about the one-sided discrete `st` (the
above face alone, at the event `P_{f(n)}(φ_n) ≥ 0.5`), and on this family the above face alone
is not refuted (it reduces to `E_n(W) ≲ₙ 0`, which holds whenever the deferred price is
eventually below `½`); whether the one-sided hard face is false for the paper's inductor is
**open** here (it would need the novice's mass on `1[½ ≤ P_{f n}(φ_n)]` not to vanish, which
nothing here controls). (ii) **Boundary convention**: the world identity `XW' ≡ 1 − W`
(`hXW'val`) uses the non-strict above weight at `p = ½` (there `W = W' = 1`, `φ` false,
`XW' = 0 = 1 − W`); with v6's and root-013's *strict* `1[E*(X) > t]` one gets
`XW' = 1 − W − 1[p = ½]`, and on days with `P_{f n}(φ_n) = ½` exactly both faces hold trivially
(above: `0 ≳ 0`; below: `0 − ½ ≲ 0`), so under the strict convention this family does not
obviously refute (not attempted). (iii) **Attribution**: the reading "both hard faces of
`HardTotalTrust` at `½`, sharp weights as quoted decided LUVs, self-expert, deferral `f`" is
*a* reading of root-013 (ii) / v6 §1.6 — which name the weight `1[E*(X) > t]` but not the day
(the LI paper names the day `f(n)`) — ATTRIBUTION-UNVETTED; the conditional-*tower* reading is a
different predicate which this family does not obviously refute (findings K7).
Construction-facing; single market (self).
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## The deferred-day liar -/

/-- **The deferred-day liar family**: e.c. sentences `φ n` true in a completed-theory world
exactly when the day-`f n` price of `φ n` is below `p` — FAF's
`ParadoxResistanceQuote.diagonal_reflected` with the day moved from `n` to `f n`, without the
affine certificates (they are same-day paradox resistance, not needed for the refutation).
Source: mandate target 7a; FAF `ParadoxResistanceQuote` (`Properties/Introspection.lean`);
[[reflection-in-li]] §The LI paper's own reflection discussion (LI §4.12's
`φ_n := ⌜P_{f(n)}(φ_n) < 0.5⌝`)
Kind: D
Fidelity: exact (the paper's family, as a reflection clause) -/
structure DeferredLiar (P : History) (DP : DeductiveProcess) (f : DeferralFunction) (p : ℚ) where
  /-- the family -/
  sentence : ℕ → Sentence
  /-- it is e.c. -/
  codes : MachineSentenceCodes sentence
  /-- the liar clause at the deferred day -/
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    (v.Holds (sentence n) ↔ P (f n) (sentence n) < (p : ℝ))

/-! ## Sharp weights as quoted decided LUVs -/

section Sharp

variable {P : History} (market : MarketComputation P)

/-- The sharp above-weight of the day-`g n` price of `φ n` at `½`, as a `{0,1}`-rational:
`1[½ ≤ quote (g n) (φ n)]`.
Source: mandate target 7b (the sharp weights, design decision 5)
Kind: D
Fidelity: exact -/
def sharpAboveValue (g : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) : ℚ :=
  if (1 / 2 : ℚ) ≤ market.quote (g n) (Encodable.encode (φ n)) then 1 else 0

/-- The sharp below-weight `1[quote (g n) (φ n) ≤ ½]`.
Source: mandate target 7b
Kind: D
Fidelity: exact -/
def sharpBelowValue (g : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) : ℚ :=
  if market.quote (g n) (Encodable.encode (φ n)) ≤ (1 / 2 : ℚ) then 1 else 0

/-- The sharp weights lie in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sharpAboveValue_mem (g : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) :
    0 ≤ sharpAboveValue market g φ n ∧ sharpAboveValue market g φ n ≤ 1 := by
  unfold sharpAboveValue; split_ifs <;> norm_num

/-- The sharp below-weights lie in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sharpBelowValue_mem (g : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) :
    0 ≤ sharpBelowValue market g φ n ∧ sharpBelowValue market g φ n ≤ 1 := by
  unfold sharpBelowValue; split_ifs <;> norm_num

/-- The sharp above-weight is a computable sequence (the market's quote along a computable day
map and an e.c. sentence family, compared with `½`).
Source: none: infrastructure (FAF `MarketComputation.quote_comp_computable`,
`MachineSentenceCodes.primrec`, `ratLE_prim`)
Kind: L
Fidelity: n/a -/
theorem sharpAboveValue_computable {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) : Computable (sharpAboveValue market g φ) := by
  have hq : Computable fun n => market.quote (g n) (Encodable.encode (φ n)) :=
    market.quote_comp_computable hg hφ.primrec.to_comp
  have hleB : Primrec fun p : ℚ × ℚ => decide (p.1 ≤ p.2) := ratLE_prim.decide
  have hdec : Computable fun n =>
      decide ((1 / 2 : ℚ) ≤ market.quote (g n) (Encodable.encode (φ n))) :=
    (hleB.to_comp.comp ((Computable.const (1 / 2 : ℚ)).pair hq) : _)
  exact (Computable.cond hdec (Computable.const (1 : ℚ)) (Computable.const (0 : ℚ))).of_eq
    (fun n => by simp [sharpAboveValue, Bool.cond_decide])

/-- The sharp below-weight is a computable sequence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sharpBelowValue_computable {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) : Computable (sharpBelowValue market g φ) := by
  have hq : Computable fun n => market.quote (g n) (Encodable.encode (φ n)) :=
    market.quote_comp_computable hg hφ.primrec.to_comp
  have hleB : Primrec fun p : ℚ × ℚ => decide (p.1 ≤ p.2) := ratLE_prim.decide
  have hdec : Computable fun n =>
      decide (market.quote (g n) (Encodable.encode (φ n)) ≤ (1 / 2 : ℚ)) :=
    (hleB.to_comp.comp (hq.pair (Computable.const (1 / 2 : ℚ))) : _)
  exact (Computable.cond hdec (Computable.const (1 : ℚ)) (Computable.const (0 : ℚ))).of_eq
    (fun n => by simp [sharpBelowValue, Bool.cond_decide])

/-- As a real, the sharp above-weight is `def-lattice`'s `hardAbove ½` of the day-`g n` price.
Source: none: infrastructure (FAF `MarketComputation.quote_exact`)
Kind: L
Fidelity: n/a -/
theorem sharpAboveValue_cast (g : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) :
    ((sharpAboveValue market g φ n : ℚ) : ℝ) = hardAbove (1 / 2) (P (g n) (φ n)) := by
  unfold sharpAboveValue hardAbove
  rw [market.quote_exact (g n) (φ n)]
  by_cases h : (1 / 2 : ℚ) ≤ market.quote (g n) (Encodable.encode (φ n))
  · rw [if_pos h, if_pos (by exact_mod_cast h)]; simp
  · rw [if_neg h, if_neg (fun hc => h (by exact_mod_cast hc))]; simp

/-- As a real, the sharp below-weight is `hardBelow ½` of the day-`g n` price.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sharpBelowValue_cast (g : ℕ → ℕ) (φ : ℕ → Sentence) (n : ℕ) :
    ((sharpBelowValue market g φ n : ℚ) : ℝ) = hardBelow (1 / 2) (P (g n) (φ n)) := by
  unfold sharpBelowValue hardBelow
  rw [market.quote_exact (g n) (φ n)]
  by_cases h : market.quote (g n) (Encodable.encode (φ n)) ≤ (1 / 2 : ℚ)
  · rw [if_pos h, if_pos (by exact_mod_cast h)]; simp
  · rw [if_neg h, if_neg (fun hc => h (by exact_mod_cast hc))]; simp

end Sharp

/-! ## The quote codes over the paper's theory -/

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- FAF's quote code of the sharp above-weight along the day map `g` (design decision 5:
`RationalQuoteCode.ofComputable` on a computable `{0,1}`-sequence).
Source: mandate target 7b; FAF `RationalQuoteCode.ofComputable`
Kind: D
Fidelity: exact -/
def sharpAboveCode {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) :
    RationalQuoteCode T (sharpAboveValue (paperMarketComputation T) g φ) :=
  RationalQuoteCode.ofComputable T (sharpAboveValue_computable _ hg hφ)
    (sharpAboveValue_mem _ g φ)

/-- FAF's quote code of the sharp below-weight along `g`.
Source: mandate target 7b
Kind: D
Fidelity: exact -/
def sharpBelowCode {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) :
    RationalQuoteCode T (sharpBelowValue (paperMarketComputation T) g φ) :=
  RationalQuoteCode.ofComputable T (sharpBelowValue_computable _ hg hφ)
    (sharpBelowValue_mem _ g φ)

/-- The sharp above-weight LUV `W n = ⌜1[½ ≤ P_{g n}(φ_n)]⌝`.
Source: mandate target 7b
Kind: D
Fidelity: exact -/
def sharpW {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ)
    (n : ℕ) : LUV := (sharpAboveCode T hg hφ).luv n

/-- The above-face product LUV `XW n = ⌜1(φ_n) · 1[½ ≤ P_{g n}(φ_n)]⌝` (`indicatorProductLUV`).
Source: mandate target 7b
Kind: D
Fidelity: exact (`slack ≡ 0`) -/
def sharpXW {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ)
    (n : ℕ) : LUV := indicatorProductLUV (sharpAboveCode T hg hφ) φ n

/-- The sharp below-weight LUV `W' n = ⌜1[P_{g n}(φ_n) ≤ ½]⌝`.
Source: mandate target 7b
Kind: D
Fidelity: exact -/
def sharpW' {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ)
    (n : ℕ) : LUV := (sharpBelowCode T hg hφ).luv n

/-- The below-face product LUV `XW' n = ⌜1(φ_n) · 1[P_{g n}(φ_n) ≤ ½]⌝`.
Source: mandate target 7b
Kind: D
Fidelity: exact (`slack ≡ 0`) -/
def sharpXW' {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ)
    (n : ℕ) : LUV := indicatorProductLUV (sharpBelowCode T hg hφ) φ n

omit [Entailment.Consistent T] in
/-- `W n` is valued at `hardAbove ½ (P_{g n}(φ_n))` in every completed-theory world.
Source: FAF `RationalQuoteCode.reflected`
Kind: L
Fidelity: n/a -/
theorem sharpW_reflected {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (sharpW T hg hφ n) (hardAbove (1 / 2) (liaHistory (paperDP T) (g n) (φ n))) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) (sharpAboveCode T hg hφ) n v hv
  rwa [sharpAboveValue_cast] at h

omit [Entailment.Consistent T] in
/-- `XW n` is valued at `payout(φ_n) · hardAbove ½ (P_{g n}(φ_n))`.
Source: FAF `indicatorProductLUV_valuesAt`
Kind: L
Fidelity: n/a -/
theorem sharpXW_reflected {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (sharpXW T hg hφ n)
      (v.payout (φ n) * hardAbove (1 / 2) (liaHistory (paperDP T) (g n) (φ n))) := by
  have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T) (sharpAboveCode T hg hφ)
    φ n v hv
  rwa [sharpAboveValue_cast] at h

omit [Entailment.Consistent T] in
/-- `W' n` is valued at `hardBelow ½ (P_{g n}(φ_n))`.
Source: FAF `RationalQuoteCode.reflected`
Kind: L
Fidelity: n/a -/
theorem sharpW'_reflected {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (sharpW' T hg hφ n) (hardBelow (1 / 2) (liaHistory (paperDP T) (g n) (φ n))) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) (sharpBelowCode T hg hφ) n v hv
  rwa [sharpBelowValue_cast] at h

omit [Entailment.Consistent T] in
/-- `XW' n` is valued at `payout(φ_n) · hardBelow ½ (P_{g n}(φ_n))`.
Source: FAF `indicatorProductLUV_valuesAt`
Kind: L
Fidelity: n/a -/
theorem sharpXW'_reflected {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (sharpXW' T hg hφ n)
      (v.payout (φ n) * hardBelow (1 / 2) (liaHistory (paperDP T) (g n) (φ n))) := by
  have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T) (sharpBelowCode T hg hφ)
    φ n v hv
  rwa [sharpBelowValue_cast] at h

omit [Entailment.Consistent T] in
/-- The four sharp LUV families are e.c.
Source: FAF `RationalQuoteCode.poly`, `indicatorProductLUV_machineThresholdCodeSeq`
Kind: L
Fidelity: n/a -/
theorem sharp_codes {g : ℕ → ℕ} (hg : Computable g) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) :
    LUV.MachineThresholdCodeSeq (sharpW T hg hφ) ∧ LUV.MachineThresholdCodeSeq (sharpXW T hg hφ) ∧
      LUV.MachineThresholdCodeSeq (sharpW' T hg hφ) ∧
        LUV.MachineThresholdCodeSeq (sharpXW' T hg hφ) :=
  ⟨(sharpAboveCode T hg hφ).poly, indicatorProductLUV_machineThresholdCodeSeq _ hφ,
    (sharpBelowCode T hg hφ).poly, indicatorProductLUV_machineThresholdCodeSeq _ hφ⟩

/-! ## The `WeightQuote`s at the hard weights, for the self-expert -/

/-- **The hard above-face `WeightQuote` for the self-expert** on the literal-indicator source of
`φ`, with `slack ≡ 0` (the pattern of `def-lattice`'s `WeightQuote.of_selfTrustQuote`): the
weight LUV is valued at `hardAbove ½ (E*(X_n))` because
`(literalIndicator (φ n)).expect P (f n) = P (f n) (φ n)` exactly.
Source: mandate target 7b; `def-lattice` `WeightQuote.of_selfTrustQuote`
Kind: D
Fidelity: exact (`slack ≡ 0`; the sharp weight is a quoted decided LUV, not a trade weight) -/
def hardAboveQuote (f : DeferralFunction) {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) :
    WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (φ n)) (hardAbove (1 / 2)) (sharpW T f.computable hφ)
      (sharpXW T f.computable hφ) where
  weight_codes := (sharp_codes T f.computable hφ).1
  product_codes := (sharp_codes T f.computable hφ).2.1
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  source_valued := fun n v hv => ⟨_, literalIndicator_valuesAt (φ n) (paperDP T) hv⟩
  weight_reflected := fun n v hv => by
    simpa [Expert.estimate, literalIndicator_expect] using sharpW_reflected T f.computable hφ n v hv
  product_reflected := fun n v hv x hx => by
    have hx' : x = v.payout (φ n) := hx.eq (literalIndicator_valuesAt (φ n) (paperDP T) hv)
    refine ⟨v.payout (φ n) * hardAbove (1 / 2) (liaHistory (paperDP T) (f n) (φ n)),
      sharpXW_reflected T f.computable hφ n v hv, ?_⟩
    simp [hx', Expert.estimate, literalIndicator_expect]

/-- **The hard below-face `WeightQuote` for the self-expert**, likewise.
Source: mandate target 7b
Kind: D
Fidelity: exact (`slack ≡ 0`) -/
def hardBelowQuote (f : DeferralFunction) {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) :
    WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (φ n)) (hardBelow (1 / 2)) (sharpW' T f.computable hφ)
      (sharpXW' T f.computable hφ) where
  weight_codes := (sharp_codes T f.computable hφ).2.2.1
  product_codes := (sharp_codes T f.computable hφ).2.2.2
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  source_valued := fun n v hv => ⟨_, literalIndicator_valuesAt (φ n) (paperDP T) hv⟩
  weight_reflected := fun n v hv => by
    simpa [Expert.estimate, literalIndicator_expect] using sharpW'_reflected T f.computable hφ n v hv
  product_reflected := fun n v hv x hx => by
    have hx' : x = v.payout (φ n) := hx.eq (literalIndicator_valuesAt (φ n) (paperDP T) hv)
    refine ⟨v.payout (φ n) * hardBelow (1 / 2) (liaHistory (paperDP T) (f n) (φ n)),
      sharpXW'_reflected T f.computable hφ n v hv, ?_⟩
    simp [hx', Expert.estimate, literalIndicator_expect]

/-! ## The refutation, abstractly -/

section Core

variable {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]

/-- **The two hard faces at `½` are jointly refuted on any liar family** (the argument, over an
arbitrary inductor): `φ` with `Holds (φ n) ↔ p n < ½` in every world, sharp weight LUVs `W`,
`W'` valued at `hardAbove ½ (p n)`, `hardBelow ½ (p n)` and products `XW`, `XW'` valued at the
payout times the weight. World facts: `XW ≡ 0`; `XW' ≡ 1 − W`. `thm:expprovind` on `[XW]` and
`[XW', W]`; the above face gives `E_n(W) ≲ₙ 0`, the below face with `E_n(W') ≤ 1` gives
`E_n(W) ≳ₙ ½`; at `ε = 1/16` the four eventual facts meet in a contradiction. No assumption on
which side of `½` the price sits.
Source: mandate target 7b (the proof shape); [[reflection-in-li]] §The LI paper's own reflection
discussion (LI §4.12: "each conjunction `φ_n ∧ (P_{f(n)}(φ_n) ≥ 0.5)` is disprovable")
Kind: P
Fidelity: exact
Hyps: (a) the world facts (data from the quote codes); `hworld` -/
theorem hard_faces_refuted_core (φ : ℕ → Sentence) (p : ℕ → ℝ)
    (hliar : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      (v.Holds (φ n) ↔ p n < ((1 / 2 : ℚ) : ℝ)))
    {W XW W' XW' : ℕ → LUV} (hXW : LUV.MachineThresholdCodeSeq XW)
    (hW : LUV.MachineThresholdCodeSeq W) (hXW' : LUV.MachineThresholdCodeSeq XW')
    (hWv : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (W n) (hardAbove (1 / 2) (p n)))
    (hXWv : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (XW n) (v.payout (φ n) * hardAbove (1 / 2) (p n)))
    (hXW'v : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (XW' n) (v.payout (φ n) * hardBelow (1 / 2) (p n)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (habove : (fun n => (XW n).expect P n - ((1 / 2 : ℚ) : ℝ) * (W n).expect P n) ≳ₙ
      (fun _ => (0 : ℝ)))
    (hbelow : (fun n => (XW' n).expect P n - ((1 / 2 : ℚ) : ℝ) * (W' n).expect P n) ≲ₙ
      (fun _ => (0 : ℝ))) : False := by
  have h12 : ((1 / 2 : ℚ) : ℝ) = 2⁻¹ := by norm_num
  have hliar' : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      (v.Holds (φ n) ↔ p n < (2⁻¹ : ℝ)) := by
    intro n v hv; rw [← h12]; exact hliar n v hv
  -- the above-face product is valued `0` in every world
  have hXW0val : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.payout (φ n) * hardAbove (1 / 2) (p n) = 0 := by
    intro n v hv
    unfold PCWorld.payout hardAbove
    rw [h12]
    by_cases hp : (2⁻¹ : ℝ) ≤ p n
    · have hnot : ¬ v.Holds (φ n) := fun hh => absurd ((hliar' n v hv).mp hh) (not_lt.2 hp)
      simp [hnot]
    · simp [hp]
  -- the below-face product is valued `1 − W` in every world
  have hXW'val : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.payout (φ n) * hardBelow (1 / 2) (p n) + hardAbove (1 / 2) (p n) = 1 := by
    intro n v hv
    unfold PCWorld.payout hardAbove hardBelow
    rw [h12]
    by_cases hlt : p n < (2⁻¹ : ℝ)
    · have hh : v.Holds (φ n) := (hliar' n v hv).mpr hlt
      simp [hh, hlt.le, not_le.2 hlt]
    · have hnot : ¬ v.Holds (φ n) := fun hh => hlt ((hliar' n v hv).mp hh)
      simp [hnot, not_lt.1 hlt]
  have hXW0 : (fun n => (XW n).expect P n) ≈ₙ (fun _ => (0 : ℝ)) := by
    have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
      (B := 0) (fun _ => by simp) (ts := [(1, XW)])
      (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact hXW)
      (listComb_worldValued _ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact fun n v hv => ⟨_, hXWv n v hv⟩))
      (0 : ℝ) (slack := fun _ => 0) tendsto_const_nhds
      (fun n v hv ν hν => by
        have h1 := listComb_valuesAt_mem hν (p := (1, XW)) (List.mem_singleton_self _)
        rw [listComb_value]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [h1.eq (hXWv n v hv), hXW0val n v hv]
        simp) hworld
    refine (tendsto_congr (fun n => ?_)).mp h
    simp [listComb_expect]
  have hXW'1 : (fun n => (XW' n).expect P n + (W n).expect P n) ≈ₙ (fun _ => (1 : ℝ)) := by
    have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
      (B := 0) (fun _ => by simp) (ts := [(1, XW'), (1, W)])
      (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hXW'
        · exact hW)
      (listComb_worldValued _ (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact fun n v hv => ⟨_, hXW'v n v hv⟩
        · exact fun n v hv => ⟨_, hWv n v hv⟩))
      (1 : ℝ) (slack := fun _ => 0) tendsto_const_nhds
      (fun n v hv ν hν => by
        have h1 := listComb_valuesAt_mem hν (p := (1, XW')) (by simp)
        have h2 := listComb_valuesAt_mem hν (p := (1, W)) (by simp)
        rw [listComb_value]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [h1.eq (hXW'v n v hv), h2.eq (hWv n v hv)]
        have := hXW'val n v hv
        simp only [Rat.cast_zero, Rat.cast_one, one_mul, zero_add, add_zero]
        rw [this]
        simp) hworld
    refine (tendsto_congr (fun n => ?_)).mp h
    simp [listComb_expect]
  have hW'le : ∀ n, (W' n).expect P n ≤ 1 := fun n =>
    (LUV.expect_mem_Icc P n (W' n) (fun s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s)).2
  have hε : (0 : ℝ) < 1 / 16 := by norm_num
  have hev := (habove (1 / 16) hε).and ((hbelow (1 / 16) hε).and
    ((asympEq_eventually_abs_le hXW0 hε).and (asympEq_eventually_abs_le hXW'1 hε)))
  obtain ⟨n, h1, h2, h3, h4⟩ := hev.exists
  have h5 := hW'le n
  simp only at h1 h2 h3 h4
  rw [abs_le] at h3 h4
  push_cast at h1 h2
  linarith [h1, h2, h3.1, h3.2, h4.1, h4.2, h5]

end Core

/-! ## The refutation for the self-expert over the paper's inductor -/

/-- **7b. Hard Total Trust toward the future self is refuted at threshold `½`** (load-bearing 4):
for the self-expert over the paper's inductor, at any deferral `f`, given a deferred-day liar
family, the conjunction of `def-lattice`'s two hard faces at `½` is false — witnessed on the
source `X n := literalIndicator (L.sentence n)` with the sharp weights as quoted decided LUVs
(`hardAboveQuote`, `hardBelowQuote`, `slack ≡ 0`). The surviving neighbour is
`def-self-trust`'s `selfTotalTrust` (soft, both faces, every threshold).
Source: mandate target 7b; LI `main.tex` ll. 2117–2127 (§4.12, via [[reflection-in-li]]);
v6 §1.6 l. 234 and l. 249 ("liar-prone"); root-deference-013 (ii) (its gloss); `def-lattice`
report §T5 ("a refutation must *exhibit* one")
Kind: P
Fidelity: exact for `def-lattice`'s `HardTotalTrust` at `½` under `hardAbove ½ = 1[½ ≤ ·]`
(the LI paper's `≥ 0.5`); weaker than LI §4.12's one-sided claim (the above face alone is not
refuted by this family); variant w.r.t. v6/root-013's strict `1[E*(X) > t]` (the boundary
`p = ½` is not covered). Register: ATTRIBUTION-UNVETTED as *a* reading of root-013 (ii) — see
the module docstring
Hyps: (a) given the liar family `L` (inhabited: `deferredLiarOfDiagonal`) -/
theorem hardTotalTrust_refuted (f : DeferralFunction)
    (L : DeferredLiar (liaHistory (paperDP T)) (paperDP T) f (1 / 2)) :
    ¬ (HardTotalTrustAbove (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) (1 / 2) ∧
      HardTotalTrustBelow (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) (1 / 2)) := by
  rintro ⟨hA, hB⟩
  have hXcodes : LUV.MachineThresholdCodeSeq (fun n => literalIndicator (L.sentence n)) :=
    literalIndicator_machineThresholdCodeSeq L.codes
  have habove := hA _ _ _ hXcodes (hardAboveQuote T f L.codes)
  have hbelow := hB _ _ _ hXcodes (hardBelowQuote T f L.codes)
  exact hard_faces_refuted_core (P := liaHistory (paperDP T)) (DP := paperDP T) L.sentence
    (fun n => liaHistory (paperDP T) (f n) (L.sentence n)) L.reflected
    (sharp_codes T f.computable L.codes).2.1 (sharp_codes T f.computable L.codes).1
    (sharp_codes T f.computable L.codes).2.2.2
    (sharpW_reflected T f.computable L.codes) (sharpXW_reflected T f.computable L.codes)
    (sharpXW'_reflected T f.computable L.codes) (paperDP_hworld T) habove hbelow

/-! ## 7d — the deferred liar exists: FAF's diagonal over the deferred market -/

/-- The deferred history `n ↦ P (f n)`: the market the expert's day-`f n` prices form when
read as a day-`n` sequence.
Source: mandate target 7d
Kind: D
Fidelity: exact -/
def deferredHistory (P : History) (f : DeferralFunction) : History := fun n => P (f n)

/-- **The deferred market presentation**: a `MarketComputation` of the deferred history from
one of `P` — the quote table `(n, s) ↦ quote (f n) s`, computable because `f` is
(`DeferralFunction.computable`), through FAF's `ComputableMarket.ofComputableTable`.
Source: mandate target 7d ("if FAF's parameterized constructor admits a day map, instantiate")
Kind: D
Fidelity: exact -/
def deferredMarket {P : History} (market : MarketComputation P) (f : DeferralFunction) :
    MarketComputation (deferredHistory P f) :=
  Classical.choice (ComputableMarket.ofComputableTable (P := deferredHistory P f)
    (fun n s => market.quote (f n) s) (fun n φ => market.price_mem_Icc (f n) φ)
    (fun n φ => market.quote_exact (f n) φ)
    (Computable.encode.comp (market.quote_comp_computable
      (f.computable.comp (Primrec.fst.comp Primrec.unpair).to_comp)
      (Primrec.snd.comp Primrec.unpair).to_comp))).nonemptyComputation

/-- **7d. The deferred-day liar is inhabited at grade (a)**: FAF's
`parameterizedDiagonalQuoteCodeOfMarket` over the deferred market presentation. Its sentence
`φ n` holds in a completed-theory world iff `(deferredMarket …).quote n ⌜φ n⌝ < p`, i.e. iff
`P (f n) (φ n) < p` — the same-day diagonal of the deferred market *is* the deferred-day
liar; no new fixed point.
Source: mandate target 7d; FAF `parameterizedDiagonalQuoteCodeOfMarket`,
`parameterizedDiagonalQuoteCodeOfMarket_public_price_iff`, `BooleanQuoteCode.reflected`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
def deferredLiarOfDiagonal (f : DeferralFunction) (p : ℚ) :
    DeferredLiar (liaHistory (paperDP T)) (paperDP T) f p where
  sentence := (parameterizedDiagonalQuoteCodeOfMarket
    (deferredMarket (paperMarketComputation T) f) T p).toBooleanQuoteCode.sentence
  codes := MachineSentenceCodes.ofPolySentenceCodes (parameterizedDiagonalQuoteCodeOfMarket
    (deferredMarket (paperMarketComputation T) f) T p).toBooleanQuoteCode.sentence_poly
  reflected := fun n v hv =>
    ((parameterizedDiagonalQuoteCodeOfMarket (deferredMarket (paperMarketComputation T) f) T
      p).toBooleanQuoteCode.reflected (paperQuotationPresentation T) n v hv).trans
      (parameterizedDiagonalQuoteCodeOfMarket_public_price_iff
        (deferredMarket (paperMarketComputation T) f) T p n)

/-- **Hard Total Trust toward the future self is false, unconditionally** (load-bearing 4, with
7d discharged): for every deferral `f`, the two hard faces at `½` cannot both hold for the
self-expert over the paper's inductor.
Source: mandate target 7 (load-bearing 4); LI §4.12 (`main.tex` ll. 2117–2127); v6 §1.6 ll. 234/249
Kind: P
Fidelity: exact (see `hardTotalTrust_refuted`'s register line)
Hyps: (a) none -/
theorem hardTotalTrust_refuted_paper (f : DeferralFunction) :
    ¬ (HardTotalTrustAbove (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) (1 / 2) ∧
      HardTotalTrustBelow (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) (1 / 2)) :=
  hardTotalTrust_refuted T f (deferredLiarOfDiagonal T f (1 / 2))

/-- **The full hard predicate is refuted** (`def-lattice`'s `HardTotalTrust`, all thresholds).
Source: mandate target 7; `def-lattice` `HardTotalTrust`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem hardTotalTrust_false (f : DeferralFunction) :
    ¬ HardTotalTrust (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  fun h => hardTotalTrust_refuted_paper T f (h (1 / 2))

/-! ## The same-day instance (N+, no deferred object) -/

/-- **The same-day mechanism on FAF's own `paperDiagonalQuoteCode T ½`** (the kernel-checked
sanity instance of the argument): with `χ_n` satisfying `Holds (χ_n) ↔ P n (χ_n) < ½` and the
sharp quotes along the day map `id`, the two faces at day `n` — not a `def-lattice` notion,
since an `Expert` needs `f n > n`; stated as a bare conjunction about `P` — are jointly refuted.
Source: mandate target 7d ("the same-day mechanism with FAF's own `paperDiagonalQuoteCode`")
Kind: N+
Fidelity: exact (same-day; the `def-lattice` predicates do not apply)
Hyps: (a) none -/
theorem sameDay_hard_faces_refuted :
    ¬ ((fun n => (sharpXW T Computable.id (MachineSentenceCodes.ofPolySentenceCodes
          (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence_poly) n).expect
            (liaHistory (paperDP T)) n -
        ((1 / 2 : ℚ) : ℝ) * (sharpW T Computable.id (MachineSentenceCodes.ofPolySentenceCodes
          (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence_poly) n).expect
            (liaHistory (paperDP T)) n) ≳ₙ (fun _ => (0 : ℝ)) ∧
      (fun n => (sharpXW' T Computable.id (MachineSentenceCodes.ofPolySentenceCodes
          (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence_poly) n).expect
            (liaHistory (paperDP T)) n -
        ((1 / 2 : ℚ) : ℝ) * (sharpW' T Computable.id (MachineSentenceCodes.ofPolySentenceCodes
          (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence_poly) n).expect
            (liaHistory (paperDP T)) n) ≲ₙ (fun _ => (0 : ℝ))) := by
  rintro ⟨habove, hbelow⟩
  set hχ := MachineSentenceCodes.ofPolySentenceCodes
    (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence_poly
  have hliar : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      (v.Holds ((paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence n) ↔
        liaHistory (paperDP T) (id n)
          ((paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence n) < ((1 / 2 : ℚ) : ℝ)) :=
    fun n v hv =>
      ((paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.reflected
        (paperQuotationPresentation T) n v hv).trans
        (parameterizedDiagonalQuoteCodeOfMarket_public_price_iff (paperMarketComputation T) T
          (1 / 2) n)
  exact hard_faces_refuted_core (P := liaHistory (paperDP T)) (DP := paperDP T) _
    (fun n => liaHistory (paperDP T) (id n)
      ((paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence n)) hliar
    (sharp_codes T Computable.id hχ).2.1 (sharp_codes T Computable.id hχ).1
    (sharp_codes T Computable.id hχ).2.2.2
    (sharpW_reflected T Computable.id hχ) (sharpXW_reflected T Computable.id hχ)
    (sharpXW'_reflected T Computable.id hχ) (paperDP_hworld T) habove hbelow

/-- Target 7 over `𝗣𝗔` at `succDeferral`: no binder left unwitnessed.
Source: mandate design decision 7
Kind: L
Fidelity: n/a -/
example : ¬ HardTotalTrust (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔)
    (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) :=
  hardTotalTrust_false 𝗣𝗔 succDeferral

end

end Cleanroom.Deference.DefSqueezeDiamond
