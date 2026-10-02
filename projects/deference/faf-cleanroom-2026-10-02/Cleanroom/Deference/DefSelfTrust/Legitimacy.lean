import Cleanroom.Deference.DefSelfTrust.Est

/-!
# `def-self-trust` — target 4: the legitimacy gate lives inside `ccee`

[[li-deference]] §0.3 (root-deference-059) proposes a *legitimacy-modified Tower*:
`E_now(X) = E[E_fut(X) | legit]·P(legit) + E[corrected E_fut(X) | illegit]·P(illegit)`, with a
*correction function* mapping illegitimate future beliefs to corrected ones. trust-lab-2-034 (i)
observes that for a gate `w` that is a P-generable weight the gated tower
`E_n(⌜X_n·w_{f(n)}⌝) ≈ₙ E_n(⌜E_{f(n)}(X_n)·w_{f(n)}⌝)` is an instance of `thm:ccee`. This file
makes that exact and pushes it to its consequence:

* **4a** `legitimacyGated_tower_of_generable`: the gated tower for every `[0,1]` P-generable
  gate, at the deferred day `w (f n)` — a named re-export of `thm:ccee` (`selfCondTower` gives
  it at every reflecting quote); and `gatedSelfTrust_productForm`, the gated Self-Trust instance
  at the product weight `Ind_δ(E_{f(n)}(X_n) > s) · w_{f(n)}` (both factors generable, so their
  product is — `pgenerableRat_mul`);
* **4b** `modifiedTower_decomposition`: `E_n(X_n) ≈ₙ E_n(⌜E_{f(n)}(X_n)·w_{f(n)}⌝) +
  E_n(⌜E_{f(n)}(X_n)·(1 − w_{f(n)})⌝)` (`cee`, then one exact `thm:expprovind` bet), and
  `correctionFunction_idle`: any LUV family `G` for which the modified Tower holds with `G` in
  the illegitimate slot satisfies `E_n(G_n) ≈ₙ E_n(⌜E_{f(n)}(X_n)·(1 − w_{f(n)})⌝)` — the
  correction is asymptotically idle *in the novice's own day-`n` expectation* (not: `G_n`
  equals the uncorrected quote in any world, nor: no corrected `G` exists). For a single
  inductor and a generable gate the proposal has no content at expectation level
  (`corr-li-shutdown`'s "legitimacy is vacuous for a single inductor"); its content is the
  non-generable gate (target 4c, `Pseudorandom.lean`).

The theorems are about **generable weights**, not about legitimacy: the names say
`_of_generable`. The note's `w_n := Ind_δ(C_n < τ)` for a corruption LUV `C` is an instance
whenever that ramp is generable (`pgenerableRat_ratCtsInd_right` when `C`'s day-`f n`
expectation is a generable rational); the gate is indexed at the deferred day (`def-lattice` F2).
`corr-li-shutdown` and `legit-li-register` import these names.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-! ## 4a — the gated tower is `ccee` -/

/-- **The legitimacy-gated tower holds for every P-generable gate** (load-bearing 2, the name the
corrigibility consumers cite): for every `w : ℕ → ℚ` in `[0,1]` with `PGenerableRat P w` and
every e.c. world-valued `X`, `E_n(⌜X_n · w_{f(n)}⌝) ≈ₙ E_n(⌜E_{f(n)}(X_n) · w_{f(n)}⌝)` at FAF's
quoted LUVs (mesh product left, conditional quote right). It **is** `thm:ccee` — a named
re-export of FAF's closed endpoint, verbatim (Kind L); the theorem is about generable weights,
and legitimacy enters only as an interpretation of `w`.
Source: root-deference-059 ([[li-deference]] §0.3, the modified Tower); trust-lab-2-034 (i);
FAF `lic_no_expected_net_update_conditional_closed`
Kind: L
Fidelity: variant: product within FAF's slack; weight at `w (f n)` (F2)
Hyps: (a) -/
theorem legitimacyGated_tower_of_generable (f : DeferralFunction) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) (w : ℕ → ℚ)
    (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hw : PGenerableRat (liaHistory (paperDP T)) w) :
    (fun n => (meshProductLUV (paperDeferredWeightQuoteCode T f w hw hmem) X n).expect
        (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => ((paperConditionalExpectationQuoteCode T f X hX w hw hmem).luv n).expect
        (liaHistory (paperDP T)) n) :=
  lic_no_expected_net_update_conditional_closed T f X hX hval w hmem hw

/-- The gated tower at **every** reflecting quote pair (`CondQuote`): the `CondTower` form, a
verbatim re-export of `selfCondTower` under the legitimacy name (Kind L for that reason, as
its sibling `legitimacyGated_tower_of_generable`; the content is `selfCondTower`'s, Kind C).
Source: root-deference-059; trust-lab-2-034 (i)
Kind: L
Fidelity: variant: product within the quote's slack
Hyps: (a) -/
theorem legitimacyGated_condTower (f : DeferralFunction) :
    CondTower (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  selfCondTower T f

/-- The gated `est` weight: the product `Ind_δ(E_{f⁻¹ m}… > s) · w_m` of the ramp weight and a
gate.
Source: trust-lab-2-034 (i) ("likewise a gated Self-Trust instance from `thm:st`")
Kind: D
Fidelity: exact -/
def gatedWeight (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) (w : ℕ → ℚ) (m : ℕ) : ℚ :=
  estWeight T f X δ s m * w m

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The gated weight is P-generable (product of two generable weights).
Source: `Weights.lean` `pgenerableRat_mul`
Kind: L
Fidelity: n/a -/
theorem gatedWeight_pgenerable (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) {w : ℕ → ℚ}
    (hw : PGenerableRat (liaHistory (paperDP T)) w) :
    PGenerableRat (liaHistory (paperDP T)) (gatedWeight T f X δ s w) :=
  pgenerableRat_mul (estWeight_pgenerable T f hX hδ s) hw

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The gated weight lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedWeight_mem (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) {w : ℕ → ℚ}
    (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (m : ℕ) :
    0 ≤ gatedWeight T f X δ s w m ∧ gatedWeight T f X δ s w m ≤ 1 := by
  obtain ⟨h0, h1⟩ := estWeight_mem T f X δ s m
  obtain ⟨g0, g1⟩ := hmem m
  exact ⟨mul_nonneg h0 g0, by unfold gatedWeight; nlinarith⟩

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- At the deferred day the gated weight is `Ind_δ(E_{f n}(X n) > s) · w (f n)`.
Source: `Est.lean` `estWeight_at_cast`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem gatedWeight_at_cast (f : DeferralFunction) (hinj : Function.Injective f.f) (X : ℕ → LUV)
    (δ s : ℚ) (w : ℕ → ℚ) (n : ℕ) :
    ((gatedWeight T f X δ s w (f n) : ℚ) : ℝ) =
      ctsInd δ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ) * ((w (f n) : ℚ) : ℝ) := by
  rw [gatedWeight, Rat.cast_mul, estWeight_at_cast T f hinj]

/-- **The gated Self-Trust instance** (4a, second half): at the product weight
`Ind_δ(E_{f(n)}(X_n) > s) · w_{f(n)}` for a `[0,1]` P-generable gate `w`,
`E_n(⌜X_n · Ind_δ(…) · w_{f(n)}⌝) − s · E_n(⌜Ind_δ(…) · w_{f(n)}⌝) ≳ₙ 0` at FAF's quotes: the
world value of the bet is `(E_{f n}(X n) − s) · Ind_δ(…) · w (f n) ≥ 0` (no false positives
times a nonnegative gate), the rest is `ccee` and `expprovind` as in `est`.
Source: trust-lab-2-034 (i) ("likewise a gated Self-Trust instance"); root-deference-059
Kind: C
Fidelity: variant: product within FAF's slack; `f` injective
Hyps: (a); `hinj` -/
theorem gatedSelfTrust_productForm (f : DeferralFunction) (hinj : Function.Injective f.f)
    {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {δ : ℚ}
    (hδ : 0 < δ) (s : ℚ) {w : ℕ → ℚ} (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) :
    (fun n => (meshProductLUV (paperDeferredWeightQuoteCode T f (gatedWeight T f X δ s w)
        (gatedWeight_pgenerable T f hX hδ s hw) (gatedWeight_mem T f X δ s hmem)) X n).expect
          (liaHistory (paperDP T)) n -
      (s : ℝ) * ((paperDeferredWeightQuoteCode T f (gatedWeight T f X δ s w)
        (gatedWeight_pgenerable T f hX hδ s hw) (gatedWeight_mem T f X δ s hmem)).luv n).expect
          (liaHistory (paperDP T)) n) ≳ₙ (fun _ => (0 : ℝ)) := by
  set g := gatedWeight T f X δ s w with hg
  have hgw := gatedWeight_pgenerable T f hX hδ s hw
  have hgm := gatedWeight_mem T f X δ s hmem
  set WF := (paperDeferredWeightQuoteCode T f g hgw hgm).luv with hWF
  set Z'F := (paperConditionalExpectationQuoteCode T f X hX g hgw hgm).luv with hZ'F
  have hccee := lic_no_expected_net_update_conditional_closed T f X hX hval g hgm hgw
  have hWr : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (WF n) (ctsInd δ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ) *
        ((w (f n) : ℚ) : ℝ)) := fun n v hv => by
    have h := deferredWeightQuote_reflected T f g hgw hgm n v hv
    rwa [gatedWeight_at_cast T f hinj] at h
  have hZr : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (Z'F n) ((X n).expect (liaHistory (paperDP T)) (f n) *
        (ctsInd δ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ) *
          ((w (f n) : ℚ) : ℝ))) := fun n v hv => by
    have h := conditionalExpectationQuote_reflected T f X hX g hgw hgm n v hv
    rwa [gatedWeight_at_cast T f hinj] at h
  -- the bet `Z'_F − s·W_F`
  set terms : List (ℚ × (ℕ → LUV)) := [(1, Z'F), (-s, WF)] with hterms
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
    · exact valuesAt_worldValue (hZr n v hv)
    · exact valuesAt_worldValue (hWr n v hv)
  have hvalb : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        (0 : ℝ) ≤ (constComb 0 terms n).value (liaHistory (paperDP T)) ν := by
    intro n v hv ν hν
    have e₁ := (hν (EF.const 1, Z'F n) (by simp [constComb, hterms])).eq (hZr n v hv)
    have e₂ := (hν (EF.const (-s), WF n) (by simp [constComb, hterms])).eq (hWr n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂]
    push_cast
    have hr := sub_mul_ctsInd_nonneg hδ ((X n).expect (liaHistory (paperDP T)) (f n)) (s : ℝ)
    have hg0 : (0 : ℝ) ≤ ((w (f n) : ℚ) : ℝ) := by exact_mod_cast (hmem (f n)).1
    nlinarith [mul_nonneg hr hg0]
  have hbet := lic_expect_combination_provind_ge
    (constComb_boundedSequence (liaHistory (paperDP T)) 0 terms hcodes) hwv 0 hvalb
    (paperDP_hworld T)
  have hE : (fun n => (constComb 0 terms n).expect (liaHistory (paperDP T)) n) =
      (fun n => (Z'F n).expect (liaHistory (paperDP T)) n -
        (s : ℝ) * (WF n).expect (liaHistory (paperDP T)) n) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rw [hE] at hbet
  exact asympGE_zero_of_asympEq_pair (s : ℝ) hccee (AsympEq.refl _) hbet

/-! ## 4b — the modified-Tower decomposition and the idle correction function -/

/-- `1 − w` stays in `[0,1]` when `w` does.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem one_sub_mem {w : ℕ → ℚ} (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (n : ℕ) :
    0 ≤ 1 - w n ∧ 1 - w n ≤ 1 :=
  ⟨by linarith [(hmem n).2], by linarith [(hmem n).1]⟩

/-- The illegitimate-slot quote: FAF's conditional quote at the complementary gate `1 − w`,
`⌜E_{f(n)}(X_n) · (1 − w_{f(n)})⌝`.
Source: root-deference-059 (the second summand of the modified Tower)
Kind: D
Fidelity: exact -/
def illegitQuote (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    {w : ℕ → ℚ} (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hw : PGenerableRat (liaHistory (paperDP T)) w) :
    ℕ → LUV :=
  (paperConditionalExpectationQuoteCode T f X hX (fun n => 1 - w n) (pgenerableRat_one_sub hw)
    (one_sub_mem hmem)).luv

/-- **The modified-Tower decomposition** (4b): for every `[0,1]` P-generable gate `w` and e.c.
world-valued `X`,
`E_n(X_n) ≈ₙ E_n(⌜E_{f(n)}(X_n)·w_{f(n)}⌝) + E_n(⌜E_{f(n)}(X_n)·(1 − w_{f(n)})⌝)`
— `cee` to the deferred-expectation quote `Q`, then one exact `thm:expprovind` bet
`Q − Z'_w − Z'_{1−w}` (world value `e − e·w − e·(1 − w) = 0`). The note's modified Tower with
the *uncorrected* future expectation in the illegitimate slot is therefore a theorem.
Source: root-deference-059 ([[li-deference]] §0.3: the modified Tower display); mandate
target 4b
Kind: C
Fidelity: exact (both summands are FAF's exact conditional quotes)
Hyps: (a) -/
theorem modifiedTower_decomposition (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {w : ℕ → ℚ}
    (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hw : PGenerableRat (liaHistory (paperDP T)) w) :
    (fun n => (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => ((paperConditionalExpectationQuoteCode T f X hX w hw hmem).luv n).expect
          (liaHistory (paperDP T)) n +
        (illegitQuote T f hX hmem hw n).expect (liaHistory (paperDP T)) n) := by
  set Q := (paperDeferredExpectationQuoteCode T f X hX).luv with hQ
  set Zw := (paperConditionalExpectationQuoteCode T f X hX w hw hmem).luv with hZw
  set Zc := illegitQuote T f hX hmem hw with hZc
  have hcee := lic_expected_future_expectations_closed T f X hX hval
  set terms : List (ℚ × (ℕ → LUV)) := [(1, Q), (-1, Zw), (-1, Zc)] with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact (paperDeferredExpectationQuoteCode T f X hX).poly
    · exact (paperConditionalExpectationQuoteCode T f X hX _ _ _).poly
    · exact (paperConditionalExpectationQuoteCode T f X hX _ _ _).poly
  have hQr := deferredExpectationQuote_reflected T f X hX
  have hZwr := conditionalExpectationQuote_reflected T f X hX w hw hmem
  have hZcr := conditionalExpectationQuote_reflected T f X hX (fun n => 1 - w n)
    (pgenerableRat_one_sub hw) (one_sub_mem hmem)
  have hwv : LUVCombination.WorldValued (constComb 0 terms) (paperDP T) := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact valuesAt_worldValue (hQr n v hv)
    · exact valuesAt_worldValue (hZwr n v hv)
    · exact valuesAt_worldValue (hZcr n v hv)
  have hvalb : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        (constComb 0 terms n).value (liaHistory (paperDP T)) ν = 0 := by
    intro n v hv ν hν
    have e₁ := (hν (EF.const 1, Q n) (by simp [constComb, hterms])).eq (hQr n v hv)
    have e₂ := (hν (EF.const (-1), Zw n) (by simp [constComb, hterms])).eq (hZwr n v hv)
    have e₃ := (hν (EF.const (-1), Zc n) (by simp [constComb, hterms])).eq (hZcr n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂, e₃]
    push_cast
    ring
  have hbet := lic_expect_combination_provind_eq
    (constComb_boundedSequence (liaHistory (paperDP T)) 0 terms hcodes) hwv 0 hvalb
    (paperDP_hworld T)
  have hE : (fun n => (constComb 0 terms n).expect (liaHistory (paperDP T)) n) =
      (fun n => (Q n).expect (liaHistory (paperDP T)) n -
        ((Zw n).expect (liaHistory (paperDP T)) n + (Zc n).expect (liaHistory (paperDP T)) n)) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rw [hE] at hbet
  have hQZ : (fun n => (Q n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (Zw n).expect (liaHistory (paperDP T)) n +
        (Zc n).expect (liaHistory (paperDP T)) n) := by
    unfold AsympEq at hbet ⊢
    simpa using hbet
  exact hcee.trans hQZ

/-- **The correction function is idle** (4b, the consequence): if the modified Tower holds with
*any* LUV family `G` in the illegitimate slot — `E_n(X_n) ≈ₙ E_n(⌜E_{f(n)}(X_n)·w_{f(n)}⌝) +
E_n(G_n)` — then `E_n(G_n) ≈ₙ E_n(⌜E_{f(n)}(X_n)·(1 − w_{f(n)})⌝)`: asymptotically, the
"corrected future expectation conditional on illegitimacy" must equal the *uncorrected* one.
No hypothesis on `G` beyond the display (it need not even be e.c.): the decomposition pins the
illegitimate summand. What is proved is expectation-level: for a single inductor and a
generable gate, the correction is *asymptotically idle in the novice's own day-`n`
expectation* — it does **not** say `G_n` equals the uncorrected quote in any world, nor that a
corrected `G` cannot exist. The proposal has content only when the gate is not generable
(target 4c). The line of the note this addresses is its single-inductor sentence
([[li-deference]] line 65: "LI comes to trust its future self in these senses … To modify
Tower in particular …"); the note's primary proposal (lines 51–63) is cross-process (the AI
predicting the humans) and is outside this package. Kind L: `modifiedTower_decomposition` plus
the cancellation of two `≈ₙ` (the content is the decomposition). Relative to
`modifiedTower_decomposition` this is S-shaped: given the decomposition, the hypothesis `hG` is
*equivalent* to the conclusion (subtract the decomposition from `hG`, and back), so this is not
a second theorem but the decomposition read in the note's vocabulary (round-2 adversarial
audit N2); nothing downstream cites it for content the decomposition lacks.
Source: root-deference-059 (the correction function); trust-lab-2-034 (ii-a, "sound but not
safe" is the finite frame, not this); mandate target 4b
Kind: L (S relative to `modifiedTower_decomposition`, whose content it is)
Fidelity: exact
Hyps: (a); `hG` is the display itself (the modified Tower for `G`) -/
theorem correctionFunction_idle (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {w : ℕ → ℚ}
    (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hw : PGenerableRat (liaHistory (paperDP T)) w)
    (G : ℕ → LUV)
    (hG : (fun n => (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => ((paperConditionalExpectationQuoteCode T f X hX w hw hmem).luv n).expect
          (liaHistory (paperDP T)) n + (G n).expect (liaHistory (paperDP T)) n)) :
    (fun n => (G n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (illegitQuote T f hX hmem hw n).expect (liaHistory (paperDP T)) n) := by
  have hdec := modifiedTower_decomposition T f hX hval hmem hw
  have h := (hG.symm.trans hdec).sub (AsympEq.refl (fun n =>
    ((paperConditionalExpectationQuoteCode T f X hX w hw hmem).luv n).expect
      (liaHistory (paperDP T)) n))
  unfold AsympEq at h ⊢
  refine h.congr (fun n => ?_)
  ring

end

end Cleanroom.Deference.DefSelfTrust
