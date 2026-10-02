import Cleanroom.Found.DefLattice
import Cleanroom.Deference.DefSelfTrust.Transfer
import Cleanroom.Deference.DefSelfTrust.Weights

/-!
# `def-self-trust` — targets 1a, 1b, 9, 10: the self-instances of FAF's endpoints

The four endpoints of LI §4.12 over the paper's inductor `liaHistory (paperDP T)`, restated as
`def-lattice`'s notions for the self-expert `Expert.self P DP f`:

* **1a** `selfTower_valued`: `thm:cee` at *every* reflecting quote (`Reflects`), for
  world-valued sources — the `Tower` clause restricted to `Valued` sources; the unrestricted
  predicate is not reached (finding F4), and the conditional form the mandate offered
  (`(∀ X, e.c. X → Valued X) → Tower …`) is **not** stated because its antecedent is refutable
  over `paperDP T`: `not_all_valued` (the all-`⊤` family `allTop` is e.c. and valued by no
  world) is the machine-checked record of that, replacing the vacuous theorem the round-1
  audits flagged;
* **1b** `selfCondTower`: `thm:ccee` at every `CondQuote` — `CondTower` for the self-expert,
  outright (the package carries `source_valued`);
* **9** `selfCeu`: `thm:ceu` in the package's vocabulary, and at every reflecting quote;
* **10** `mergeHop1`: Hop 1 of the merge (trust-lab-010), `ccee` at the literal indicator with
  FAF's exact indicator product on the left.

Exactness scope (mandate design decision 4): self-expert `Expert.self P DP f` over
`liaHistory (paperDP T)`; the product quote is reflected within FAF's `1/(n+1)` mesh slack
(`dd:mesh`), exact for literal-indicator sources; weight at the deferred day `w (f n)`; single
market — no second inductor. Binders `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`, all
discharged at `𝗣𝗔` by the `example`s at the end.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-! ## 1a — `thm:cee` at every reflecting quote -/

omit [Entailment.Consistent T] in
/-- FAF's deferred-expectation quote reflects the self-expert's estimate, in every
completed-theory world (the cast identity `expectQuoteAt_cast`).
Source: FAF `RationalQuoteCode.reflected`, `MarketComputation.expectQuoteAt_cast`
Kind: L
Fidelity: n/a -/
lemma deferredExpectationQuote_reflected (f : DeferralFunction) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((paperDeferredExpectationQuoteCode T f X hX).luv n)
      ((X n).expect (liaHistory (paperDP T)) (f n)) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
    (paperDeferredExpectationQuoteCode T f X hX) n v hv
  rwa [← (paperMarketComputation T).expectQuoteAt_cast X n (f.f n)] at h

/-- **The self-case Tower, at every reflecting quote, for world-valued sources** (target 1a):
for e.c. `X` valued in every completed-theory world and every e.c. `Y` with
`Reflects DP (Expert.self P DP f) X Y` (every world values `Y n` at `E_{f n}(X n)`),
`E_n(X_n) ≈ₙ E_n(Y_n)`. Route: FAF's `thm:cee` at its own quote
`paperDeferredExpectationQuoteCode`, then the exact transfer lemma between that quote and `Y`.
Scope: self-expert over `liaHistory (paperDP T)`; exact (no product); single market. The
`Valued` clause is FAF's `source_valued`, which `def-lattice`'s `Tower` does not carry
(finding F4): this theorem is `Tower` on valued sources, not the predicate `Tower`.
Source: root-deference-020 (v6 §3.2 table, row Mart = `cee` 4.12.1); [[deference-notions]] §Mart;
FAF `lic_expected_future_expectations_closed`
Kind: C
Fidelity: weaker: restricted to `Valued` sources (FAF's premise; the predicate `Tower` demands
the equality on unvalued e.c. sources too, which no FAF theorem reaches)
Hyps: (a) -/
theorem selfTower_valued (f : DeferralFunction) (X Y : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (hY : LUV.MachineThresholdCodeSeq Y)
    (hval : Valued (paperDP T) X)
    (hR : Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X Y) :
    (fun n => (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (Y n).expect (liaHistory (paperDP T)) n) := by
  have h1 := lic_expected_future_expectations_closed T f X hX hval
  have h2 : (fun n => (Y n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => ((paperDeferredExpectationQuoteCode T f X hX).luv n).expect
        (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_exact hY (paperDeferredExpectationQuoteCode T f X hX).poly
      (fun n _ => (X n).expect (liaHistory (paperDP T)) (f n))
      (fun n v hv => hR n v hv)
      (fun n v hv => deferredExpectationQuote_reflected T f X hX n v hv)
      (paperDP_hworld T)
  exact h1.trans h2.symm

/-! ### Why the predicate `Tower` is not reached: an e.c. source valued by no world

The mandate's conditional form `(∀ X, e.c. X → Valued (paperDP T) X) → Tower …` was stated in
round 1 (`selfTower_of_valued`) and deleted in repair round 1: its antecedent is refutable, so
the theorem was an instance of `absurd` (round-1 adversarial audit B1, fidelity audit N3). The
refutation is kept instead, as the machine-checked form of finding F4 / `def-lattice` F7. -/

/-- The all-`⊤` threshold family: every threshold sentence `X > r` is `⊤`.
Source: `def-lattice` F7 (an all-`⊤` threshold family); finding F4
Kind: D
Fidelity: exact -/
def allTop : LUV where
  gt _ := (⊤ : Sentence)

/-- The constant all-`⊤` family is machine-metered (e.c.).
Source: FAF `MachineSentenceCodes.const`
Kind: L
Fidelity: n/a -/
theorem allTop_codes : LUV.MachineThresholdCodeSeq (fun _ : ℕ => allTop) :=
  MachineSentenceCodes.const (⊤ : Sentence)

/-- Every world holds `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem holds_verum (v : PCWorld) : v.Holds (⊤ : Sentence) := by
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- No p.c. world values `allTop` at any real: `ValuesAt` demands `¬ v.Holds (X.gt r)` for
every rational `r > x`, and every world holds `⊤`.
Source: `def-lattice` F7; FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
theorem allTop_not_valued (v : PCWorld) (x : ℝ) : ¬ v.ValuesAt allTop x := by
  rintro ⟨-, -, h⟩
  obtain ⟨r, hr⟩ := exists_rat_gt x
  exact (h r).2 hr (holds_verum v)

/-- **Not every e.c. source is world-valued over `paperDP T`**: the antecedent of the mandate's
conditional `Tower` form is false, so that form is vacuous and is not stated. `def-lattice`'s
`Tower` quantifies over such sources, on which FAF's `cee` (which takes `source_valued`) says
nothing — finding F4, now machine-checked. An elementary refutation (the constant all-`⊤`
family, `exists_rat_gt`, `paperDP_nonvacuous`): Kind L, a guard against the vacuous conditional
form rather than real content (round-2 fidelity audit N4; it was labelled P).
Source: `def-lattice` F7; finding F4; FAF `paperDP_nonvacuous`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem not_all_valued :
    ¬ (∀ X : ℕ → LUV, LUV.MachineThresholdCodeSeq X → Valued (paperDP T) X) := by
  intro hall
  obtain ⟨v, hv⟩ := paperDP_nonvacuous (T := T)
  obtain ⟨x, hx⟩ := hall _ allTop_codes 0 v hv
  exact allTop_not_valued v x hx

/-- The day-`m` expectation of `allTop` is the price of `⊤`: every grid threshold sentence is
`⊤`, so the grid average `(m+1)⁻¹ Σ_{i ≤ m} P_m(⊤)` collapses.
Source: FAF `LUV.expectApprox` (`dd:e`); the pattern of `def-lattice` `literalIndicator_expect`
Kind: L
Fidelity: n/a -/
theorem allTop_expect (P : History) (m : ℕ) : LUV.expect P m allTop = P m (⊤ : Sentence) := by
  unfold LUV.expect LUV.expectApprox
  simp only [allTop, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- **The self-expert's `Tower` instance holds on `allTop`** — the unvalued family that refutes
the mandate's conditional form: for every e.c. `Y` reflecting the self-expert's estimate of
`allTop` (`Y n` valued at `E_{f n}(allTop) = P_{f n}(⊤)` in every completed-theory world),
`E_n(allTop) ≈ₙ E_n(Y_n)`; both tend to `1` by `thm:provind` on `⊤`. So the unvalued case of
`def-lattice`'s `Tower` is *not* refuted by the family that breaks `Valued` — a data point for
`def-lattice`'s F4 question (round-1 adversarial audit N5), not the unvalued case in general,
which remains unverified. Route: `E_n(allTop) = P_n(⊤) = E_n(1(⊤))` (`allTop_expect`,
`literalIndicator_expect`), and the transfer lemma between `Y` (valued at `P_{f n}(⊤)`, within
`|P_{f n}(⊤) − 1|` of `1`, a vanishing slack along `f`) and `1(⊤)` (valued at `1`).
Source: finding F4; round-1 adversarial audit N5; FAF `lic_provind_true`
Kind: C
Fidelity: n/a (one unvalued family; the predicate `Tower` is still not reached)
Hyps: (a) -/
theorem selfTower_allTop (f : DeferralFunction) (Y : ℕ → LUV)
    (hY : LUV.MachineThresholdCodeSeq Y)
    (hR : Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun _ => allTop) Y) :
    (fun n => LUV.expect (liaHistory (paperDP T)) n allTop) ≈ₙ
      (fun n => (Y n).expect (liaHistory (paperDP T)) n) := by
  have hTop : (fun m => liaHistory (paperDP T) m (⊤ : Sentence)) ≈ₙ (fun _ => (1 : ℝ)) :=
    lic_provind_true (liaHistory (paperDP T)) (paperDP T) (fun _ => (⊤ : Sentence))
      (MachineSentenceCodes.const _) (fun _ v _ => holds_verum v) (paperDP_hworld T)
  have hTop' : Tendsto (fun m => liaHistory (paperDP T) m (⊤ : Sentence) - 1) atTop (𝓝 0) :=
    hTop
  have hs : Tendsto (fun n => |liaHistory (paperDP T) (f n) (⊤ : Sentence) - 1|) atTop (𝓝 0) := by
    have := (hTop'.comp f.tendsto_atTop).abs
    simpa using this
  have h1 : (fun n => (Y n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (literalIndicator (⊤ : Sentence)).expect (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_within hY
      (literalIndicator_machineThresholdCodeSeq (MachineSentenceCodes.const (⊤ : Sentence)))
      (fun _ _ => (1 : ℝ)) hs tendsto_const_nhds
      (fun n v hv => ⟨_, hR n v hv, by
        show |LUV.expect (liaHistory (paperDP T)) (f n) allTop - 1| ≤ _
        rw [allTop_expect]⟩)
      (fun n v hv => ⟨_, literalIndicator_valuesAt (⊤ : Sentence) (paperDP T) hv, by
        simp [PCWorld.payout, holds_verum v]⟩)
      (paperDP_hworld T)
  have h2 : (fun n => LUV.expect (liaHistory (paperDP T)) n allTop) =
      (fun n => (literalIndicator (⊤ : Sentence)).expect (liaHistory (paperDP T)) n) := by
    funext n
    rw [allTop_expect, literalIndicator_expect]
  rw [h2]
  exact h1.symm

/-! ## 1b — `thm:ccee` at every conditional quote: `CondTower` -/

omit [Entailment.Consistent T] in
/-- FAF's deferred-weight quote is valued at `w (f n)` in every completed-theory world.
Source: FAF `RationalQuoteCode.reflected`
Kind: L
Fidelity: n/a -/
lemma deferredWeightQuote_reflected (f : DeferralFunction) (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((paperDeferredWeightQuoteCode T f w hw hmem).luv n) ((w (f n) : ℚ) : ℝ) :=
  RationalQuoteCode.reflected (paperQuotationPresentation T)
    (paperDeferredWeightQuoteCode T f w hw hmem) n v hv

omit [Entailment.Consistent T] in
/-- FAF's conditional-expectation quote is valued at `E_{f n}(X n) · w (f n)` in every
completed-theory world.
Source: FAF `RationalQuoteCode.reflected`, `expectQuoteAt_cast`
Kind: L
Fidelity: n/a -/
lemma conditionalExpectationQuote_reflected (f : DeferralFunction) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((paperConditionalExpectationQuoteCode T f X hX w hw hmem).luv n)
      ((X n).expect (liaHistory (paperDP T)) (f n) * ((w (f n) : ℚ) : ℝ)) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
    (paperConditionalExpectationQuoteCode T f X hX w hw hmem) n v hv
  rwa [Rat.cast_mul, ← (paperMarketComputation T).expectQuoteAt_cast X n (f.f n)] at h

omit [Entailment.Consistent T] in
/-- FAF's mesh product is valued within `1/(n+1)` of `x · w (f n)` whenever the source is valued
at `x` (`dd:mesh`).
Source: FAF `meshProductLUV_valuesAt`
Kind: L
Fidelity: n/a -/
lemma meshProduct_reflected (f : DeferralFunction) (X : ℕ → LUV) (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) {x : ℝ} (hx : v.ValuesAt (X n) x) :
    ∃ z, v.ValuesAt (meshProductLUV (paperDeferredWeightQuoteCode T f w hw hmem) X n) z ∧
      |z - x * ((w (f n) : ℚ) : ℝ)| ≤ 1 / ((n : ℝ) + 1) :=
  meshProductLUV_valuesAt (paperQuotationPresentation T)
    (paperDeferredWeightQuoteCode T f w hw hmem) X n v hv hx

/-- **The self-case conditional tower** (target 1b, load-bearing 2): `CondTower` holds for the
self-expert over the paper's inductor — for every e.c. source, every `[0,1]` P-generable weight
`w` and every `CondQuote` `(Z, Z')` (left product within its own vanishing slack of
`x · w (f n)`, right product exactly at `E_{f n}(X n) · w (f n)`),
`E_n(Z_n) ≈ₙ E_n(Z'_n)`. Route: FAF's `thm:ccee` at its own mesh product and conditional
quote, then the transfer lemma on each side (left within `slack n + 1/(n+1)`, right exact).
This is trust-lab-2-034 (i) and root-deference-059's first model; target 4 re-exports it under
the legitimacy name.
Scope: self-expert over `liaHistory (paperDP T)`; product within FAF's `1/(n+1)` mesh slack on
FAF's side and within the quote's own slack on `def-lattice`'s side; weight at `w (f n)`;
single market.
Source: root-deference-020 (row ccee 4.12.3); [[deference-notions]] §The conditional tower;
trust-lab-2-034 (i); FAF `lic_no_expected_net_update_conditional_closed`
Kind: C
Fidelity: variant: product within FAF's slack (as `CondQuote` and FAF disclose)
Hyps: (a) -/
theorem selfCondTower (f : DeferralFunction) :
    CondTower (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) := by
  intro X w hmem hgen hX Z Z' q
  have hccee := lic_no_expected_net_update_conditional_closed T f X hX q.source_valued w hmem hgen
  have hleft : (fun n => (Z n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (meshProductLUV (paperDeferredWeightQuoteCode T f w hgen hmem) X n).expect
        (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_within q.left_codes
      (meshProductLUV_machineThresholdCodeSeq _ hX)
      (fun n v => worldValue v (X n) * ((w (f n) : ℚ) : ℝ))
      q.slack_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n v hv => by
        obtain ⟨x, hx⟩ := q.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := q.left_reflected n v hv x hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩)
      (fun n v hv => by
        obtain ⟨x, hx⟩ := q.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := meshProduct_reflected T f X w hgen hmem n v hv hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩)
      (paperDP_hworld T)
  have hright : (fun n => (Z' n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => ((paperConditionalExpectationQuoteCode T f X hX w hgen hmem).luv n).expect
        (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_exact q.right_codes
      (paperConditionalExpectationQuoteCode T f X hX w hgen hmem).poly
      (fun n _ => (X n).expect (liaHistory (paperDP T)) (f n) * ((w (f n) : ℚ) : ℝ))
      (fun n v hv => q.right_reflected n v hv)
      (fun n v hv => conditionalExpectationQuote_reflected T f X hX w hgen hmem n v hv)
      (paperDP_hworld T)
  exact (hleft.trans hccee).trans hright.symm

/-! ## 9 — the `ceu` "surprise" instance -/

/-- **`thm:ceu` in the package's vocabulary** (target 9): `H`'s present credence is its own
forecast of its future credence, `P_n(φ_n) ≈ₙ E_n(⌜P_{f n}(φ_n)⌝)` at FAF's future-price
quote — the `H`-side deficit of the "surprise" channel is zero. The lagging-question
"`E^H_n(X_n) ≈ a_n`" of the source is a per-day *cross-market* claim this package does not
state (finding F9; deferred to `def-squeeze-diamond` over `li-quote-lane`).
Source: vq-wiki-2-016 (ii) ([[route-negative-introspective]] §3.4); FAF
`lic_no_expected_net_update_closed`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem selfCeu (f : DeferralFunction) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    (fun n => liaHistory (paperDP T) n (φ n)) ≈ₙ
      (fun n => ((paperFutureQuoteCode T f φ hφ).luv n).expect (liaHistory (paperDP T)) n) :=
  lic_no_expected_net_update_closed T f φ hφ

/-- `thm:ceu` at **every** e.c. quote of the future price: any e.c. `Y` valued at `P_{f n}(φ_n)`
in every completed-theory world satisfies `P_n(φ_n) ≈ₙ E_n(Y_n)`.
Source: vq-wiki-2-016 (ii); mandate target 9
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem selfCeu_reflecting (f : DeferralFunction) (φ : ℕ → Sentence)
    (hφ : MachineSentenceCodes φ) (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (hR : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (Y n) (liaHistory (paperDP T) (f n) (φ n))) :
    (fun n => liaHistory (paperDP T) n (φ n)) ≈ₙ
      (fun n => (Y n).expect (liaHistory (paperDP T)) n) := by
  refine (selfCeu T f φ hφ).trans (expect_asympEq_of_reflected_exact
    (paperFutureQuoteCode T f φ hφ).poly hY (fun n _ => liaHistory (paperDP T) (f n) (φ n))
    (fun n v hv => ?_) hR (paperDP_hworld T))
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
    (paperFutureQuoteCode T f φ hφ) n v hv
  rwa [← (paperMarketComputation T).quote_exact (f.f n) (φ n)] at h

/-! ## 10 — Hop 1 of the merge -/

/-- **Hop 1** (trust-lab-010): `E_n(⌜1(φ_n)·w_{f(n)}⌝) ≈ₙ E_n(⌜P_{f(n)}(φ_n)·w_{f(n)}⌝)` for a
`[0,1]` P-generable `w`, with FAF's **exact** indicator product on the left (`slack ≡ 0`) and
FAF's conditional quote at the literal indicator on the right (valued at
`E_{f n}(1(φ_n)) · w (f n) = P_{f n}(φ_n) · w (f n)` by `literalIndicator_expect`). The source
writes `w_t`; the weight is at the deferred day `w (f t)` (`def-lattice` F2). `trust-merge`
imports this name.
Source: trust-lab-010 ([[merging-inductors-model]] §(b.2) Hop 1); FAF
`lic_no_expected_net_update_conditional_closed`, `indicatorProductLUV_valuesAt`
Kind: C
Fidelity: exact (indicator source: the left product is exact, the mesh slack is transferred
away)
Hyps: (a) -/
theorem mergeHop1 (f : DeferralFunction) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (w : ℕ → ℚ) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) :
    (fun n => (indicatorProductLUV (paperDeferredWeightQuoteCode T f w hw hmem) φ n).expect
        (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => ((paperConditionalExpectationQuoteCode T f (fun n => literalIndicator (φ n))
        (literalIndicator_machineThresholdCodeSeq hφ) w hw hmem).luv n).expect
        (liaHistory (paperDP T)) n) := by
  have hX := literalIndicator_machineThresholdCodeSeq hφ
  have hval : Valued (paperDP T) (fun n => literalIndicator (φ n)) :=
    fun n v hv => ⟨_, literalIndicator_valuesAt (φ n) (paperDP T) hv⟩
  have hccee := lic_no_expected_net_update_conditional_closed T f _ hX hval w hmem hw
  have hleft : (fun n => (indicatorProductLUV (paperDeferredWeightQuoteCode T f w hw hmem) φ n).expect
        (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (meshProductLUV (paperDeferredWeightQuoteCode T f w hw hmem)
        (fun n => literalIndicator (φ n)) n).expect (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_within
      (indicatorProductLUV_machineThresholdCodeSeq _ hφ)
      (meshProductLUV_machineThresholdCodeSeq _ hX)
      (fun n v => v.payout (φ n) * ((w (f n) : ℚ) : ℝ))
      (s₁ := fun _ => 0) tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n v hv => ⟨_, indicatorProductLUV_valuesAt (paperQuotationPresentation T)
        (paperDeferredWeightQuoteCode T f w hw hmem) φ n v hv, by simp⟩)
      (fun n v hv => meshProduct_reflected T f _ w hw hmem n v hv
        (literalIndicator_valuesAt (φ n) (paperDP T) hv))
      (paperDP_hworld T)
  exact hleft.trans hccee

/-! ## The `𝗣𝗔` instances (no binder left unwitnessed) -/

example (f : DeferralFunction) :
    CondTower (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔)
      (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) f) :=
  selfCondTower 𝗣𝗔 f

example (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    (fun n => liaHistory (paperDP 𝗣𝗔) n (φ n)) ≈ₙ
      (fun n => ((paperFutureQuoteCode 𝗣𝗔 succDeferral φ hφ).luv n).expect
        (liaHistory (paperDP 𝗣𝗔)) n) :=
  selfCeu 𝗣𝗔 succDeferral φ hφ

end

end Cleanroom.Deference.DefSelfTrust
