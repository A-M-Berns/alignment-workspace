import Cleanroom.Deference.DefSelfTrust.SelfInstances
import Cleanroom.Deference.DefSelfTrust.Ramp

/-!
# `def-self-trust` — target 2: `est`, the LUV form of Self-Trust, both faces

**The package's first headline** (load-bearing 1). For the paper's inductor
`P := liaHistory (paperDP T)`, every rational threshold `s` and width `δ > 0`, and every
injective deferral `f`:

`SoftTotalTrustAbove P DP (Expert.self P DP f) s δ` and `SoftTotalTrustBelow …`, i.e. for every
e.c. `[0,1]`-LUV source `X` and every ramp `WeightQuote` `(W, XW)`:

`E^H_n(⌜X_n · Ind_δ(E^H_{f(n)}(X_n) > s)⌝) ≳ₙ s · E^H_n(⌜Ind_δ(E^H_{f(n)}(X_n) > s)⌝)`

and the dual `≲ₙ` at `Ind_δ(E^H_{f(n)}(X_n) < s)`; packaged as `selfTotalTrust :
TotalTrust P DP (Expert.self P DP f)`. The LI paper proves only the propositional `st`
(4.12.4, sentence sources); this is the corpus's `est` (vq-wiki-061, route-recurring-ccee §7.1
T4, route-transitivity §2 Lemma A; trust-lab-2-020 (i)).

**Route A landed** (`ccee` + `expprovind`): (i) the ramp-of-deferred-expectation weight
`rampWeight` of `Weights.lean` is P-generable, with `w (f n) = ratCtsInd δ (E_{f n}(X n)) s`
(injectivity of `f`); (ii) FAF's `thm:ccee` at that weight: `E(Z_F) ≈ₙ E(Z'_F)`; (iii)
`thm:expprovind` (`≥` face) on the two-term bet `Z'_F − s·W_F`, whose world value is
`(E_{f n}(X n) − s) · ctsInd δ (E_{f n}(X n)) s ≥ 0` by no-false-positives (`Ramp.lean`);
(iv) chain; (v) the transfer lemma to any `WeightQuote` at the ramp. Route B (the `st`-proof
mimic with `thm:er`) was not needed.

Exactness scope (mandate design decision 4): self-expert `Expert.self P DP f` over
`liaHistory (paperDP T)`; the product quote is reflected within FAF's `1/(n+1)` mesh slack
(`dd:mesh`) on FAF's side and within the quote's own slack on `def-lattice`'s side, exact for
literal-indicator sources (the `WeightQuote.of_selfTrustQuote` instance); weight at the
deferred day `w (f n)`; single market — no second inductor. Injectivity of `f` is a hypothesis
FAF's `DeferralFunction` does not carry (finding F2), discharged for `succDeferral`.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-! ## The objects of the above face -/

/-- The `est` weight (above face) over the paper market: `rampWeight` at
`paperMarketComputation T`.
Source: vq-wiki-061; mandate design decision 3
Kind: D
Fidelity: exact -/
def estWeight (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) : ℕ → ℚ :=
  rampWeight (paperMarketComputation T) f X δ s

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The `est` weight is P-generable over the paper market.
Source: `Weights.lean` `rampWeight_pgenerable`
Kind: L
Fidelity: n/a -/
theorem estWeight_pgenerable (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) :
    PGenerableRat (liaHistory (paperDP T)) (estWeight T f X δ s) :=
  rampWeight_pgenerable (paperMarketComputation T) f hX hδ s

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The `est` weight lies in `[0,1]`.
Source: `Weights.lean` `rampWeight_mem`
Kind: L
Fidelity: n/a -/
theorem estWeight_mem (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) (m : ℕ) :
    0 ≤ estWeight T f X δ s m ∧ estWeight T f X δ s m ≤ 1 :=
  rampWeight_mem (paperMarketComputation T) f X δ s m

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- At the deferred day the `est` weight is the ramp of the deferred expectation, as a real.
Source: `Weights.lean` `rampWeight_at`; FAF `ratCtsInd_cast`, `expectQuoteAt_cast`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estWeight_at_cast (f : DeferralFunction) (hinj : Function.Injective f.f) (X : ℕ → LUV)
    (δ s : ℚ) (n : ℕ) :
    ((estWeight T f X δ s (f n) : ℚ) : ℝ) =
      ctsInd δ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ) := by
  rw [estWeight, rampWeight_at _ f hinj, ← ratCtsInd_cast,
    ← (paperMarketComputation T).expectQuoteAt_cast]

/-- FAF's deferred-weight quote at the `est` weight: `W_F n = ⌜Ind_δ(E_{f n}(X n) > s)⌝`.
Source: FAF `paperDeferredWeightQuoteCode`
Kind: D
Fidelity: exact -/
def estW (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ}
    (hδ : 0 < δ) (s : ℚ) : ℕ → LUV :=
  (paperDeferredWeightQuoteCode T f (estWeight T f X δ s) (estWeight_pgenerable T f hX hδ s)
    (estWeight_mem T f X δ s)).luv

/-- FAF's mesh product at the `est` weight: `Z_F n = ⌜X_n · Ind_δ(E_{f n}(X n) > s)⌝` within
`1/(n+1)`.
Source: FAF `meshProductLUV`
Kind: D
Fidelity: variant: product within FAF's slack -/
def estXW (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ}
    (hδ : 0 < δ) (s : ℚ) : ℕ → LUV :=
  meshProductLUV (paperDeferredWeightQuoteCode T f (estWeight T f X δ s)
    (estWeight_pgenerable T f hX hδ s) (estWeight_mem T f X δ s)) X

/-- FAF's conditional-expectation quote at the `est` weight:
`Z'_F n = ⌜E_{f n}(X n) · Ind_δ(E_{f n}(X n) > s)⌝` (exact).
Source: FAF `paperConditionalExpectationQuoteCode`
Kind: D
Fidelity: exact -/
def estZ' (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ}
    (hδ : 0 < δ) (s : ℚ) : ℕ → LUV :=
  (paperConditionalExpectationQuoteCode T f X hX (estWeight T f X δ s)
    (estWeight_pgenerable T f hX hδ s) (estWeight_mem T f X δ s)).luv

omit [Entailment.Consistent T] in
/-- `W_F n` is valued at the ramp of the deferred expectation in every completed-theory world.
Source: `SelfInstances.lean` `deferredWeightQuote_reflected`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estW_reflected (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (estW T f hX hδ s n)
      (ctsInd δ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ)) := by
  have h := deferredWeightQuote_reflected T f (estWeight T f X δ s)
    (estWeight_pgenerable T f hX hδ s) (estWeight_mem T f X δ s) n v hv
  rwa [estWeight_at_cast T f hinj] at h

omit [Entailment.Consistent T] in
/-- `Z'_F n` is valued at `E_{f n}(X n) · Ind_δ(E_{f n}(X n) > s)` in every completed-theory
world.
Source: `SelfInstances.lean` `conditionalExpectationQuote_reflected`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estZ'_reflected (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (estZ' T f hX hδ s n)
      ((X n).expect (liaHistory (paperDP T)) (f n) *
        ctsInd δ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ)) := by
  have h := conditionalExpectationQuote_reflected T f X hX (estWeight T f X δ s)
    (estWeight_pgenerable T f hX hδ s) (estWeight_mem T f X δ s) n v hv
  rwa [estWeight_at_cast T f hinj] at h

omit [Entailment.Consistent T] in
/-- `Z_F n` is valued within `1/(n+1)` of `x · Ind_δ(E_{f n}(X n) > s)` when `X n` is valued at
`x`.
Source: `SelfInstances.lean` `meshProduct_reflected`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estXW_reflected (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) {x : ℝ} (hx : v.ValuesAt (X n) x) :
    ∃ z, v.ValuesAt (estXW T f hX hδ s n) z ∧
      |z - x * ctsInd δ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ)| ≤
        1 / ((n : ℝ) + 1) := by
  have h := meshProduct_reflected T f X (estWeight T f X δ s)
    (estWeight_pgenerable T f hX hδ s) (estWeight_mem T f X δ s) n v hv hx
  rwa [estWeight_at_cast T f hinj] at h

/-- **Step (ii): `thm:ccee` at the `est` weight** — `E_n(Z_F) ≈ₙ E_n(Z'_F)`.
Source: vq-wiki-061 (step 2 of the proof); FAF `lic_no_expected_net_update_conditional_closed`
Kind: C
Fidelity: variant: product within FAF's slack
Hyps: (a) -/
theorem est_ccee (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (hval : Valued (paperDP T) X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) :
    (fun n => (estXW T f hX hδ s n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (estZ' T f hX hδ s n).expect (liaHistory (paperDP T)) n) :=
  lic_no_expected_net_update_conditional_closed T f X hX hval (estWeight T f X δ s)
    (estWeight_mem T f X δ s) (estWeight_pgenerable T f hX hδ s)

/-- **Step (iii): the bet `Z'_F − s·W_F` is nonnegative in every completed-theory world**, so
`thm:expprovind` gives `E_n(Z'_F) − s·E_n(W_F) ≳ₙ 0`. The world value is
`(E_{f n}(X n) − s) · Ind_δ(E_{f n}(X n) > s) ≥ 0` — no false positives.
Source: vq-wiki-061 (step 3: "no false positives gives `W(⌜E_{f(n)}(X_n)v_n⌝ − p⌜v_n⌝) ≥ 0`
in every Γ-consistent world; 4.8.10 finishes"); FAF `lic_expect_combination_provind_ge`
Kind: C
Fidelity: exact
Hyps: (a); `hinj` -/
theorem est_bet (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) :
    (fun n => (estZ' T f hX hδ s n).expect (liaHistory (paperDP T)) n -
      (s : ℝ) * (estW T f hX hδ s n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => (0 : ℝ)) := by
  set terms : List (ℚ × (ℕ → LUV)) := [(1, estZ' T f hX hδ s), (-s, estW T f hX hδ s)]
    with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (paperConditionalExpectationQuoteCode T f X hX _ _ _).poly
    · exact (paperDeferredWeightQuoteCode T f _ _ _).poly
  have hwv : LUVCombination.WorldValued (constComb 0 terms) (paperDP T) := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact valuesAt_worldValue (estZ'_reflected T f hinj hX hδ s n v hv)
    · exact valuesAt_worldValue (estW_reflected T f hinj hX hδ s n v hv)
  have hval : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        (0 : ℝ) ≤ (constComb 0 terms n).value (liaHistory (paperDP T)) ν := by
    intro n v hv ν hν
    have e₁ := (hν (EF.const 1, estZ' T f hX hδ s n) (by simp [constComb, hterms])).eq
      (estZ'_reflected T f hinj hX hδ s n v hv)
    have e₂ := (hν (EF.const (-s), estW T f hX hδ s n) (by simp [constComb, hterms])).eq
      (estW_reflected T f hinj hX hδ s n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂]
    push_cast
    nlinarith [sub_mul_ctsInd_nonneg hδ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ)]
  have h := lic_expect_combination_provind_ge
    (constComb_boundedSequence (liaHistory (paperDP T)) 0 terms hcodes) hwv 0 hval
    (paperDP_hworld T)
  have hE : (fun n => (constComb 0 terms n).expect (liaHistory (paperDP T)) n) =
      (fun n => (estZ' T f hX hδ s n).expect (liaHistory (paperDP T)) n -
        (s : ℝ) * (estW T f hX hδ s n).expect (liaHistory (paperDP T)) n) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rwa [hE] at h

/-- **`est` at FAF's own quotes (above face, product form):**
`E_n(Z_F) − s·E_n(W_F) ≳ₙ 0` — steps (ii)–(iv) chained.
Source: vq-wiki-061; trust-lab-2-020 (i)
Kind: C
Fidelity: variant: product within FAF's slack
Hyps: (a); `hinj` -/
theorem est_productForm (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {δ : ℚ} (hδ : 0 < δ)
    (s : ℚ) :
    (fun n => (estXW T f hX hδ s n).expect (liaHistory (paperDP T)) n -
      (s : ℝ) * (estW T f hX hδ s n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => (0 : ℝ)) :=
  asympGE_zero_of_asympEq_pair (s : ℝ) (est_ccee T f hX hval hδ s) (AsympEq.refl _)
    (est_bet T f hinj hX hδ s)

/-- **`est`, above face — soft Total Trust toward the future self at every `(s, δ)`, `δ > 0`**
(load-bearing 1, above): `SoftTotalTrustAbove P DP (Expert.self P DP f) s δ` over the paper's
inductor — for every e.c. source `X` and every ramp `WeightQuote` `(W, XW)`,
`E^H_n(⌜X_n · Ind_δ(E^H_{f(n)}(X_n) > s)⌝) − s · E^H_n(⌜Ind_δ(E^H_{f(n)}(X_n) > s)⌝) ≳ₙ 0`.
Route A: `est_productForm` at FAF's quotes, transferred to the given quotes (weight exact,
product within `slack + 1/(n+1)`).
Scope: self-expert over `liaHistory (paperDP T)`; product within the quote's slack (exact for
literal-indicator sources); weight at `w (f n)`; single market; `f` injective.
Source: vq-wiki-061 (T4 / Lemma A); [[route-recurring-ccee]] §7.1; [[route-transitivity]] §2;
trust-lab-2-020 (i); [[deference-notions]] §Total Trust
Kind: C
Fidelity: variant: product within the quote's vanishing slack (`dd:mesh`); `f` injective
Hyps: (a); `hinj` (see the module docstring) -/
theorem selfSoftTotalTrustAbove (f : DeferralFunction) (hinj : Function.Injective f.f)
    (s : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    SoftTotalTrustAbove (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) s δ := by
  intro X W XW hX q
  have hW : (fun n => (W n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (estW T f hX hδ s n).expect (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_exact q.weight_codes
      (paperDeferredWeightQuoteCode T f _ _ _).poly
      (fun n _ => ctsInd δ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ))
      (fun n v hv => q.weight_reflected n v hv)
      (fun n v hv => estW_reflected T f hinj hX hδ s n v hv) (paperDP_hworld T)
  have hXW : (fun n => (XW n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (estXW T f hX hδ s n).expect (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_within q.product_codes
      (meshProductLUV_machineThresholdCodeSeq _ hX)
      (fun n v => worldValue v (X n) *
        ctsInd δ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ))
      q.slack_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n v hv => by
        obtain ⟨x, hx⟩ := q.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := q.product_reflected n v hv x hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩)
      (fun n v hv => by
        obtain ⟨x, hx⟩ := q.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := estXW_reflected T f hinj hX hδ s n v hv hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩)
      (paperDP_hworld T)
  exact asympGE_zero_of_asympEq_pair (s : ℝ) hXW hW
    (est_productForm T f hinj hX q.source_valued hδ s)

/-! ## The below face -/

/-- The `est` weight, below face: the down-ramp `Ind_δ(E_{f n}(X n) < s)` pulled back along `f`.
Source: vq-wiki-061 (dual face); trust-lab-2-020 ("the dual `≲` with `< t`")
Kind: D
Fidelity: exact -/
def estWeightBelow (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) : ℕ → ℚ :=
  rampWeightBelow (paperMarketComputation T) f X δ s

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The below-face weight is P-generable.
Source: `Weights.lean` `rampWeightBelow_pgenerable`
Kind: L
Fidelity: n/a -/
theorem estWeightBelow_pgenerable (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) :
    PGenerableRat (liaHistory (paperDP T)) (estWeightBelow T f X δ s) :=
  rampWeightBelow_pgenerable (paperMarketComputation T) f hX hδ s

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The below-face weight lies in `[0,1]`.
Source: `Weights.lean` `rampWeightBelow_mem`
Kind: L
Fidelity: n/a -/
theorem estWeightBelow_mem (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) (m : ℕ) :
    0 ≤ estWeightBelow T f X δ s m ∧ estWeightBelow T f X δ s m ≤ 1 :=
  rampWeightBelow_mem (paperMarketComputation T) f X δ s m

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- At the deferred day the below-face weight is the down-ramp of the deferred expectation.
Source: `Weights.lean` `rampWeightBelow_at`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estWeightBelow_at_cast (f : DeferralFunction) (hinj : Function.Injective f.f)
    (X : ℕ → LUV) (δ s : ℚ) (n : ℕ) :
    ((estWeightBelow T f X δ s (f n) : ℚ) : ℝ) =
      ctsInd δ (s : ℝ) ((X n).expect (liaHistory (paperDP T)) (f n)) := by
  rw [estWeightBelow, rampWeightBelow_at _ f hinj, ← ratCtsInd_cast,
    ← (paperMarketComputation T).expectQuoteAt_cast]

/-- FAF's deferred-weight quote at the below-face weight.
Source: FAF `paperDeferredWeightQuoteCode`
Kind: D
Fidelity: exact -/
def estWBelow (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) : ℕ → LUV :=
  (paperDeferredWeightQuoteCode T f (estWeightBelow T f X δ s)
    (estWeightBelow_pgenerable T f hX hδ s) (estWeightBelow_mem T f X δ s)).luv

/-- FAF's mesh product at the below-face weight.
Source: FAF `meshProductLUV`
Kind: D
Fidelity: variant: product within FAF's slack -/
def estXWBelow (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) : ℕ → LUV :=
  meshProductLUV (paperDeferredWeightQuoteCode T f (estWeightBelow T f X δ s)
    (estWeightBelow_pgenerable T f hX hδ s) (estWeightBelow_mem T f X δ s)) X

/-- FAF's conditional-expectation quote at the below-face weight.
Source: FAF `paperConditionalExpectationQuoteCode`
Kind: D
Fidelity: exact -/
def estZ'Below (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) : ℕ → LUV :=
  (paperConditionalExpectationQuoteCode T f X hX (estWeightBelow T f X δ s)
    (estWeightBelow_pgenerable T f hX hδ s) (estWeightBelow_mem T f X δ s)).luv

omit [Entailment.Consistent T] in
/-- Below-face weight quote reflection.
Source: `SelfInstances.lean` `deferredWeightQuote_reflected`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estWBelow_reflected (f : DeferralFunction) (hinj : Function.Injective f.f)
    {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (estWBelow T f hX hδ s n)
      (ctsInd δ (s : ℝ) ((X n).expect (liaHistory (paperDP T)) (f n))) := by
  have h := deferredWeightQuote_reflected T f (estWeightBelow T f X δ s)
    (estWeightBelow_pgenerable T f hX hδ s) (estWeightBelow_mem T f X δ s) n v hv
  rwa [estWeightBelow_at_cast T f hinj] at h

omit [Entailment.Consistent T] in
/-- Below-face conditional quote reflection.
Source: `SelfInstances.lean` `conditionalExpectationQuote_reflected`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estZ'Below_reflected (f : DeferralFunction) (hinj : Function.Injective f.f)
    {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (estZ'Below T f hX hδ s n)
      ((X n).expect (liaHistory (paperDP T)) (f n) *
        ctsInd δ (s : ℝ) ((X n).expect (liaHistory (paperDP T)) (f n))) := by
  have h := conditionalExpectationQuote_reflected T f X hX (estWeightBelow T f X δ s)
    (estWeightBelow_pgenerable T f hX hδ s) (estWeightBelow_mem T f X δ s) n v hv
  rwa [estWeightBelow_at_cast T f hinj] at h

omit [Entailment.Consistent T] in
/-- Below-face mesh product reflection.
Source: `SelfInstances.lean` `meshProduct_reflected`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estXWBelow_reflected (f : DeferralFunction) (hinj : Function.Injective f.f)
    {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) {x : ℝ} (hx : v.ValuesAt (X n) x) :
    ∃ z, v.ValuesAt (estXWBelow T f hX hδ s n) z ∧
      |z - x * ctsInd δ (s : ℝ) ((X n).expect (liaHistory (paperDP T)) (f n))| ≤
        1 / ((n : ℝ) + 1) := by
  have h := meshProduct_reflected T f X (estWeightBelow T f X δ s)
    (estWeightBelow_pgenerable T f hX hδ s) (estWeightBelow_mem T f X δ s) n v hv hx
  rwa [estWeightBelow_at_cast T f hinj] at h

/-- Step (ii), below face: `thm:ccee` at the down-ramp weight.
Source: vq-wiki-061 (dual face); FAF `lic_no_expected_net_update_conditional_closed`
Kind: C
Fidelity: variant: product within FAF's slack
Hyps: (a) -/
theorem est_ccee_below (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {δ : ℚ} (hδ : 0 < δ)
    (s : ℚ) :
    (fun n => (estXWBelow T f hX hδ s n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (estZ'Below T f hX hδ s n).expect (liaHistory (paperDP T)) n) :=
  lic_no_expected_net_update_conditional_closed T f X hX hval (estWeightBelow T f X δ s)
    (estWeightBelow_mem T f X δ s) (estWeightBelow_pgenerable T f hX hδ s)

/-- Step (iii), below face: the bet `Z'_F − s·W_F` is nonpositive in every completed-theory
world (`(E_{f n}(X n) − s) · Ind_δ(E_{f n}(X n) < s) ≤ 0`), so `E_n(Z'_F) − s·E_n(W_F) ≲ₙ 0`.
Source: vq-wiki-061 (dual face); FAF `lic_expect_combination_provind_le`
Kind: C
Fidelity: exact
Hyps: (a); `hinj` -/
theorem est_bet_below (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) :
    (fun n => (estZ'Below T f hX hδ s n).expect (liaHistory (paperDP T)) n -
      (s : ℝ) * (estWBelow T f hX hδ s n).expect (liaHistory (paperDP T)) n) ≲ₙ
      (fun _ => (0 : ℝ)) := by
  set terms : List (ℚ × (ℕ → LUV)) :=
    [(1, estZ'Below T f hX hδ s), (-s, estWBelow T f hX hδ s)] with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (paperConditionalExpectationQuoteCode T f X hX _ _ _).poly
    · exact (paperDeferredWeightQuoteCode T f _ _ _).poly
  have hwv : LUVCombination.WorldValued (constComb 0 terms) (paperDP T) := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact valuesAt_worldValue (estZ'Below_reflected T f hinj hX hδ s n v hv)
    · exact valuesAt_worldValue (estWBelow_reflected T f hinj hX hδ s n v hv)
  have hval : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        (constComb 0 terms n).value (liaHistory (paperDP T)) ν ≤ (0 : ℝ) := by
    intro n v hv ν hν
    have e₁ := (hν (EF.const 1, estZ'Below T f hX hδ s n) (by simp [constComb, hterms])).eq
      (estZ'Below_reflected T f hinj hX hδ s n v hv)
    have e₂ := (hν (EF.const (-s), estWBelow T f hX hδ s n) (by simp [constComb, hterms])).eq
      (estWBelow_reflected T f hinj hX hδ s n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂]
    push_cast
    nlinarith [sub_mul_ctsInd_nonpos hδ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ)]
  have h := lic_expect_combination_provind_le
    (constComb_boundedSequence (liaHistory (paperDP T)) 0 terms hcodes) hwv 0 hval
    (paperDP_hworld T)
  have hE : (fun n => (constComb 0 terms n).expect (liaHistory (paperDP T)) n) =
      (fun n => (estZ'Below T f hX hδ s n).expect (liaHistory (paperDP T)) n -
        (s : ℝ) * (estWBelow T f hX hδ s n).expect (liaHistory (paperDP T)) n) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rwa [hE] at h

/-- `est` at FAF's own quotes, below face: `E_n(Z_F) − s·E_n(W_F) ≲ₙ 0`.
Source: vq-wiki-061 (dual face)
Kind: C
Fidelity: variant: product within FAF's slack
Hyps: (a); `hinj` -/
theorem est_productForm_below (f : DeferralFunction) (hinj : Function.Injective f.f)
    {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {δ : ℚ}
    (hδ : 0 < δ) (s : ℚ) :
    (fun n => (estXWBelow T f hX hδ s n).expect (liaHistory (paperDP T)) n -
      (s : ℝ) * (estWBelow T f hX hδ s n).expect (liaHistory (paperDP T)) n) ≲ₙ
      (fun _ => (0 : ℝ)) :=
  asympLE_zero_of_asympEq_pair (s : ℝ) (est_ccee_below T f hX hval hδ s) (AsympEq.refl _)
    (est_bet_below T f hinj hX hδ s)

/-- **`est`, below face — soft Total Trust toward the future self, lower cut** (load-bearing 1,
below): `SoftTotalTrustBelow P DP (Expert.self P DP f) s δ` over the paper's inductor —
`E^H_n(⌜X_n · Ind_δ(E^H_{f(n)}(X_n) < s)⌝) − s · E^H_n(⌜Ind_δ(E^H_{f(n)}(X_n) < s)⌝) ≲ₙ 0` for
every e.c. source and every down-ramp `WeightQuote`.
Scope: as `selfSoftTotalTrustAbove`.
Source: vq-wiki-061 (dual face); trust-lab-2-020 (i, "the dual `≲` with `< t`");
[[deference-notions]] §Total Trust (the lower cut)
Kind: C
Fidelity: variant: product within the quote's vanishing slack; `f` injective
Hyps: (a); `hinj` -/
theorem selfSoftTotalTrustBelow (f : DeferralFunction) (hinj : Function.Injective f.f)
    (s : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    SoftTotalTrustBelow (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) s δ := by
  intro X W XW hX q
  have hW : (fun n => (W n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (estWBelow T f hX hδ s n).expect (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_exact q.weight_codes
      (paperDeferredWeightQuoteCode T f _ _ _).poly
      (fun n _ => ctsInd δ (s : ℝ) ((X n).expect (liaHistory (paperDP T)) (f n)))
      (fun n v hv => q.weight_reflected n v hv)
      (fun n v hv => estWBelow_reflected T f hinj hX hδ s n v hv) (paperDP_hworld T)
  have hXW : (fun n => (XW n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (estXWBelow T f hX hδ s n).expect (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_within q.product_codes
      (meshProductLUV_machineThresholdCodeSeq _ hX)
      (fun n v => worldValue v (X n) *
        ctsInd δ (s : ℝ) ((X n).expect (liaHistory (paperDP T)) (f n)))
      q.slack_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n v hv => by
        obtain ⟨x, hx⟩ := q.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := q.product_reflected n v hv x hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩)
      (fun n v hv => by
        obtain ⟨x, hx⟩ := q.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := estXWBelow_reflected T f hinj hX hδ s n v hv hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩)
      (paperDP_hworld T)
  exact asympLE_zero_of_asympEq_pair (s : ℝ) hXW hW
    (est_productForm_below T f hinj hX q.source_valued hδ s)

/-! ## The headline -/

/-- **`est`: Total Trust toward the future self is free** (load-bearing 1):
`TotalTrust P DP (Expert.self P DP f)` over the paper's inductor `P = liaHistory (paperDP T)`
for every injective deferral `f` — both soft threshold inequalities at every rational
threshold `s` and every positive width `δ`, for every e.c. `[0,1]`-LUV source and every ramp
quote. The LI paper's `st` (4.12.4) is the sentence-source shadow of this (target 2d).
Scope: self-expert over `liaHistory (paperDP T)`; product quotes within their vanishing slack
(`dd:mesh`; exact for literal-indicator sources); weight at the deferred day `w (f n)`; single
market — no second inductor; `f` injective (`succDeferral` and every strictly increasing
deferral qualify).
Source: vq-wiki-061 ("the LUV form of Self-Trust, free, full limit, all days");
root-deference-020 (row Total Trust = `st` 4.12.4, lifted to LUVs); [[deference-notions]]
§Total Trust; [[centered-bet-squeeze]] §0
Kind: C
Fidelity: variant: product within the quote's vanishing slack; `f` injective
Hyps: (a); `hinj` -/
theorem selfTotalTrust (f : DeferralFunction) (hinj : Function.Injective f.f) :
    TotalTrust (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  fun s _ hδ => ⟨selfSoftTotalTrustAbove T f hinj s hδ, selfSoftTotalTrustBelow T f hinj s hδ⟩

/-- `succDeferral` is injective (the discharge of `hinj` for the deferral of record).
Source: FAF `succDeferral`
Kind: L
Fidelity: n/a -/
theorem succDeferral_injective : Function.Injective succDeferral.f :=
  fun _ _ h => Nat.add_right_cancel h

/-- `est` over `𝗣𝗔` at `succDeferral`: no binder left unwitnessed (an instantiability check
of the section variable's instances, not a non-vacuity witness — that is `Witness.lean`).
Source: mandate design decision 1
Kind: L
Fidelity: n/a -/
example : TotalTrust (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔)
    (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) :=
  selfTotalTrust 𝗣𝗔 succDeferral succDeferral_injective

end

end Cleanroom.Deference.DefSelfTrust
