import Cleanroom.Deference.DefSelfTrust.Legitimacy
import Cleanroom.Found.LiAsympCalc.Ramp
import LogicalInduction.Construction.LIA
import LogicalInduction.Construction.Paper.Market

/-!
# `corr-li-shutdown` — Legitimacy (T2): no legitimacy predicate has forced content for a single
inductor

(a) **The twice-instantiated theorem** (`legitimacy_vacuous_of_generable`, L): over FAF's paper
inductor, for **every** `[0,1]` P-generable weight `w`, the legitimacy-gated tower holds at `w`
**and at `1 − w`** — reflection conditional on "legitimacy" and conditional on "illegitimacy"
are both `thm:ccee`. The quantifier over generable weightings is in the statement; the pair at
`w` and `1 − w` *is* the vacuity witness (corr-wf14-2-033). Two applications of
`def-self-trust`'s `legitimacyGated_tower_of_generable` with `pgenerableRat_one_sub` — Kind L,
not P: the content is `def-self-trust`'s (and FAF's). Also the Total-Trust form
(`legitimacy_vacuous_totalTrust`) from `gatedSelfTrust_productForm`.

(b) **The specific legitimacy weight** `w^L_m := Ind_δ(P_m(L_m) > 1 − ε)` (`legitWeight`): its
`PGenerableRat` certificate is a theorem (`legitWeight_pgenerable`, from the market's own price
feature, `price_pgenerableRat`); the instance of (a) at it (`legitimacy_vacuous_at_legitWeight`);
and reading (b) of corr-wf13-061 — when `L` is decided by the judged day the weight is
asymptotically the indicator of `L` (`legitWeight_eventually_one` for a family of theorems,
`legitWeight_eventually_zero` for a refutable family; FAF's `thm:provind`). Reading (a) (decided
by day `n`: the weight factors out by `loe`) is **stated OPEN** (repair round 3, audit r3 fidelity
N3): `decidedWeight_factors_open` over the current-day weight quote `paperCurrentWeightQuoteCode`
— the wiki's open-problems item 4; the obstacle for the mandate's `loe` route is recorded in
section (b′) and findings F19. Reading (c) (never decided): `lic_nonDogmatism` keeps the limit
price in `(0,1)` — recorded, not stated.

(c) **The exact form is false, desirably** — **proved** in repair round 2 (`Paradox.lean`,
`exact_selfTrust_refuted`; round 0 had stated it OPEN here): on FAF's constructed paradoxical family
`χ_n ↔ (P_n(χ_n) < 1/2)` (at the *diagonal* day, FAF's `lic_paradox_resistance_ofDiagonal_
unconditional`; the sources' family is at `f(n)` — reading ATTRIBUTION-UNVETTED), the
hard-indicator self-trust inequality at `p = 1/2`, with the event "`P_n(χ_n) ≥ 1/2`" read as
`∼χ_n` through the diagonal, fails: `P_n(χ_n ⋏ ∼χ_n) → 0` while `(1/2)·P_n(∼χ_n) → 1/4`. The
three FAF inputs are `thm:provind` on the refutable conjunction, `thm:lp`, and the complement
`P_n(χ_n) + P_n(∼χ_n) ≈ₙ 1` (affine provability induction on the two-share family `χ_n + ∼χ_n`,
`Paradox.lean`); the e.c. certificates of `∼χ_n` and `χ_n ⋏ ∼χ_n` come from the quote code's
own emitter. Surviving neighbour: the ramp-weighted `st` (`lic_self_trust_closed`; this
package's T8).

**Gloss, flagged:** the sources read this as "Abram's correction function of [[li-deference]]
§0.3 is the identity for a single inductor" — an ATTRIBUTION-UNVETTED reading of a person's
intent; the theorem is about generable weights.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefSelfTrust
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

section Vacuity

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **The legitimacy-gated tower at a weight `w`** (a name for `def-self-trust`'s conclusion):
`E_n(⌜X_n · w_{f(n)}⌝) ≈ₙ E_n(⌜E_{f(n)}(X_n) · w_{f(n)}⌝)` at FAF's quoted LUVs over the paper
inductor.
Source: [[corr-wf13-inventory]] 061 (I5, the tower form); `def-self-trust` `legitimacyGated_tower_of_generable`
Kind: D
Fidelity: variant: product within FAF's slack; weight at `w (f n)`
Hyps: n/a -/
abbrev GatedTower (f : DeferralFunction) (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (w : ℕ → ℚ) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) : Prop :=
  (fun n => (meshProductLUV (paperDeferredWeightQuoteCode T f w hw hmem) X n).expect
      (liaHistory (paperDP T)) n) ≈ₙ
    (fun n => ((paperConditionalExpectationQuoteCode T f X hX w hw hmem).luv n).expect
      (liaHistory (paperDP T)) n)

/-- **For a single inductor no P-generable legitimacy predicate has forced content** (T2(a),
load-bearing 2): for **every** `[0,1]` P-generable weight `w`, the gated tower holds at `w`
and at `1 − w` — reflection conditional on `w` ("legitimate") and conditional on `1 − w`
("illegitimate") both hold. The pair is the vacuity witness; the quantifier over generable
weightings is in the statement. Two applications of `def-self-trust`'s theorem (Kind L: the
content is FAF's `thm:ccee`).
Source: [[corr-wf13-inventory]] 061 (I5.2); [[corr-wf14-inventory]] 090, 091; [[corr-wf14-2-inventory]] 2-033; [[corr-wf14b-inventory]] 058 (Statement 10)
Kind: L
Fidelity: variant: product within FAF's slack; weight at `w (f n)` (`def-self-trust` F2)
Hyps: (a) -/
theorem legitimacy_vacuous_of_generable (f : DeferralFunction) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) :
    ∀ (w : ℕ → ℚ) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hw : PGenerableRat (liaHistory (paperDP T)) w),
      GatedTower T f X hX w hmem hw ∧
        GatedTower T f X hX (fun n => 1 - w n) (one_sub_mem hmem) (pgenerableRat_one_sub hw) :=
  fun w hmem hw =>
    ⟨legitimacyGated_tower_of_generable T f X hX hval w hmem hw,
     legitimacyGated_tower_of_generable T f X hX hval _ (one_sub_mem hmem)
       (pgenerableRat_one_sub hw)⟩

/-- **The gated Self-Trust inequality at a weight `w`** (a name for `def-self-trust`'s
`gatedSelfTrust_productForm` conclusion): `E_n(⌜X_n·Ind_δ(E_{f n}(X_n) > s)·w_{f n}⌝) −
s·E_n(⌜Ind_δ(…)·w_{f n}⌝) ≳ₙ 0`.
Source: [[corr-wf13-inventory]] 061 (I5, the Total-Trust form); `def-self-trust` `gatedSelfTrust_productForm`
Kind: D
Fidelity: variant: product within FAF's slack; `f` injective
Hyps: n/a -/
abbrev GatedSelfTrust (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (w : ℕ → ℚ) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) : Prop :=
  (fun n => (meshProductLUV (paperDeferredWeightQuoteCode T f (gatedWeight T f X δ s w)
      (gatedWeight_pgenerable T f hX hδ s hw) (gatedWeight_mem T f X δ s hmem)) X n).expect
        (liaHistory (paperDP T)) n -
    (s : ℝ) * ((paperDeferredWeightQuoteCode T f (gatedWeight T f X δ s w)
      (gatedWeight_pgenerable T f hX hδ s hw) (gatedWeight_mem T f X δ s hmem)).luv n).expect
        (liaHistory (paperDP T)) n) ≳ₙ (fun _ => (0 : ℝ))

/-- **The Total-Trust form of the vacuity** (T2(a), second display of corr-wf13-061): the gated
Self-Trust inequality holds at every `[0,1]` P-generable `w` and at `1 − w`.
Source: [[corr-wf13-inventory]] 061 (I5, Total-Trust form); `def-self-trust` `gatedSelfTrust_productForm`
Kind: L
Fidelity: variant: as `GatedSelfTrust`
Hyps: (a); `hinj` -/
theorem legitimacy_vacuous_totalTrust (f : DeferralFunction) (hinj : Function.Injective f.f)
    {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {δ : ℚ}
    (hδ : 0 < δ) (s : ℚ) :
    ∀ (w : ℕ → ℚ) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hw : PGenerableRat (liaHistory (paperDP T)) w),
      GatedSelfTrust T f hX hδ s w hmem hw ∧
        GatedSelfTrust T f hX hδ s (fun n => 1 - w n) (one_sub_mem hmem) (pgenerableRat_one_sub hw) :=
  fun w hmem hw =>
    ⟨gatedSelfTrust_productForm T f hinj hX hval hδ s hmem hw,
     gatedSelfTrust_productForm T f hinj hX hval hδ s (one_sub_mem hmem) (pgenerableRat_one_sub hw)⟩

/-! ## (b) The specific legitimacy weight -/

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- **The market's own prices of an e.c. family are a P-generable rational sequence**: the
feature progression `n ↦ price (L n) n` denotes `liaQuote (paperDP T) n (L n)` at the paper
inductor (FAF's `liaHistory_eq_quote_cast`), is machine-metered (`serialize_price`), closed, and
of rank `≤ n`.
Source: none: infrastructure (FAF `GeneratedRatFeature`, `MachineSpliceStream.serialize_price`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem price_pgenerableRat (L : ℕ → Sentence) (hL : MachineSentenceCodes L) :
    PGenerableRat (liaHistory (paperDP T)) (fun m => liaQuote (paperDP T) m (L m)) :=
  ⟨fun m => EF.price (L m) m,
    { rank_le := fun n => by simp
      polyTok := MachineSpliceStream.serialize_price hL UnaryRuler.id
        (MachineDigits.ofUnaryRuler UnaryRuler.id)
      closed := fun n ρ V => by simp [EF.denoteWith, EF.denote]
      denote := fun n => liaHistory_eq_quote_cast _ _ _ }⟩

/-- **The legitimacy weight** `w^L_m := Ind_δ(P_m(L_m) > 1 − ε)` for an e.c. sentence family
`L` — a ramp of the market's own day-`m` price of `L_m` (FAF's `ratCtsInd`).
Source: [[corr-wf13-inventory]] 061 (I5: "`w^L_m := Ind_δ(P_m(L) > 1 − ε)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def legitWeight (L : ℕ → Sentence) (δ ε : ℚ) (m : ℕ) : ℚ :=
  ratCtsInd δ (liaQuote (paperDP T) m (L m)) (1 - ε)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- `w^L` is P-generable (`pgenerableRat_ratCtsInd_left` on the price sequence).
Source: [[corr-wf13-inventory]] 061 (I5: "generable from day-`m` prices")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem legitWeight_pgenerable (L : ℕ → Sentence) (hL : MachineSentenceCodes L) {δ : ℚ}
    (hδ : 0 < δ) (ε : ℚ) : PGenerableRat (liaHistory (paperDP T)) (legitWeight T L δ ε) :=
  pgenerableRat_ratCtsInd_left (price_pgenerableRat T L hL) hδ (1 - ε)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- `w^L` lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem legitWeight_mem (L : ℕ → Sentence) (δ ε : ℚ) (m : ℕ) :
    0 ≤ legitWeight T L δ ε m ∧ legitWeight T L δ ε m ≤ 1 :=
  ratCtsInd_mem_Icc _ _ _

/-- **The vacuity at the legitimacy weight** (T2(b), the instance of (a) at `w^L` and `1 − w^L`):
reflection conditional on "my day-`f(n)` self rates `L` legitimate" and conditional on its
complement both hold.
Source: [[corr-wf13-inventory]] 061 (I5.1–I5.2)
Kind: L
Fidelity: variant: as `GatedTower`
Hyps: (a) -/
theorem legitimacy_vacuous_at_legitWeight (f : DeferralFunction) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) (L : ℕ → Sentence)
    (hL : MachineSentenceCodes L) {δ : ℚ} (hδ : 0 < δ) (ε : ℚ) :
    GatedTower T f X hX (legitWeight T L δ ε) (legitWeight_mem T L δ ε)
        (legitWeight_pgenerable T L hL hδ ε) ∧
      GatedTower T f X hX (fun n => 1 - legitWeight T L δ ε n)
        (one_sub_mem (legitWeight_mem T L δ ε))
        (pgenerableRat_one_sub (legitWeight_pgenerable T L hL hδ ε)) :=
  legitimacy_vacuous_of_generable T f X hX hval _ _ _

/-- **Reading (b), decided legitimate**: if every `L_m` is a theorem of the completed paper
theory, the legitimacy weight is eventually exactly `1` (for `δ < ε`): asymptotically the
weight *is* the indicator of `L`. FAF's `thm:provind` on `L`.
Source: [[corr-wf13-inventory]] 061 (I5.1: "by Provability Induction on the decided `L`, `w^L_{f(n)} → 1(L)`")
Kind: L
Fidelity: exact (eventual equality, stronger than the source's convergence)
Hyps: (a) -/
theorem legitWeight_eventually_one (L : ℕ → Sentence) (hL : MachineSentenceCodes L)
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) → v.Holds (L n)) {δ ε : ℚ}
    (hδ : 0 < δ) (hδε : δ < ε) :
    ∀ᶠ m in atTop, legitWeight T L δ ε m = 1 := by
  haveI := paperLIA T
  have h1 := lic_provind_true (liaHistory (paperDP T)) (paperDP T) L hL hthm (paperDP_hworld T)
  have hgap : (0 : ℝ) < ε - δ := by
    have : ((δ : ℚ) : ℝ) < ε := by exact_mod_cast hδε
    linarith
  have hev := (Metric.tendsto_nhds.mp h1) (ε - δ) hgap
  filter_upwards [hev] with m hm
  rw [Real.dist_eq, abs_lt] at hm
  have hcast : ((legitWeight T L δ ε m : ℚ) : ℝ) = 1 := by
    unfold legitWeight
    rw [← ratCtsInd_cast, ctsInd_eq_one_iff hδ, ← liaHistory_eq_quote_cast]
    push_cast
    linarith [hm.1]
  exact_mod_cast hcast

/-- **Reading (b), decided illegitimate**: if every `L_m` is refuted by the completed paper
theory, the legitimacy weight is eventually exactly `0` (for `0 < ε < 1`). FAF's `thm:provind`
(negative polarity).
Source: [[corr-wf13-inventory]] 061 (I5.1)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem legitWeight_eventually_zero (L : ℕ → Sentence) (hL : MachineSentenceCodes L)
    (hdis : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) → v.Holds (∼ L n)) {δ ε : ℚ}
    (hδ : 0 < δ) (hε1 : ε < 1) :
    ∀ᶠ m in atTop, legitWeight T L δ ε m = 0 := by
  haveI := paperLIA T
  have h0 := lic_provind_false (liaHistory (paperDP T)) (paperDP T) L hL hdis (paperDP_hworld T)
  have hgap : (0 : ℝ) < 1 - ε := by
    have : ((ε : ℚ) : ℝ) < 1 := by exact_mod_cast hε1
    linarith
  have hev := (Metric.tendsto_nhds.mp h0) (1 - ε) hgap
  filter_upwards [hev] with m hm
  rw [Real.dist_eq, abs_lt] at hm
  have hcast : ((legitWeight T L δ ε m : ℚ) : ℝ) = 0 := by
    unfold legitWeight
    rw [← ratCtsInd_cast, ctsInd_eq_zero_iff hδ, ← liaHistory_eq_quote_cast]
    push_cast
    linarith [hm.2]
  exact_mod_cast hcast

end Vacuity

section ReadingA

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-! ## (b′) Reading (a): the current-day weight quote, and the factoring stated OPEN

The mandate's reading (a) of corr-wf13-061 ("decided by day `n`: the weight factors out by
`loe`") is the wiki's open-problems item 4 — introspection for market-generable features,
`E_n(⌜X_n · θ_n⌝) ≈ₙ θ_n · E_n(X_n)` for a continuous feature `θ` of the market's own day-`n`
prices. The weight is quoted at the current day (`paperCurrentWeightQuoteCode`: FAF's
`paperDeferredWeightQuoteCode` with the deferral removed — `RationalQuoteCode.ofComputable` on the
program of the P-generable sequence), and the factoring is stated OPEN
(`decidedWeight_factors_open`, listed).

**What resists** (the mandate's "if FAF's `loe` coefficient route resists, state OPEN"): FAF's
`lic_linearity_of_expectation_seq` takes the coefficient as an expressible feature `a n`, but
needs `DeterminedViaTheory` — the day-`n` deductive state must decide the value of the
combination, i.e. the quote literals of `a n`'s value — and no deductive process decides the
literals of its own day-`n` prices at day `n`, since the day-`n` prices are computed *from*
`D_n`. So `loe` reaches a *deferred* weight only through `thm:ccee` (reading (b), proved above),
and the current-day weight needs the paper's introspection family (4.11 `introspection`, 4.12
`self-knowledge`) in LUV-product form, which is exactly item 4. Nearest FAF objects:
`lic_iterated_expectations_closed` (the market's own current expectation, quoted) and
`paperPriceQuoteCode` (the current-day price, quoted). Findings F19. -/

/-- **The current-day weight quote**: a `RationalQuoteCode` for the P-generable `[0,1]` weight
`w` at its own day — `paperDeferredWeightQuoteCode` without the deferral — from the program of the
feature presentation (`PGenerableRat.computable` at the paper market).
Source: wiki open-problems item 4; FAF `deferredWeightQuoteCode` (`thm:ccee`), `RationalQuoteCode.ofComputable` (`thm:epr`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def paperCurrentWeightQuoteCode (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) :
    RationalQuoteCode T w :=
  RationalQuoteCode.ofComputable T (hw.computable (paperMarketComputation T)) hmem

/-- **T2(b), reading (a) — OPEN** (the wiki's open-problems item 4): for every e.c. world-valued
`X` and every P-generable `[0,1]` weight `w`, the day-`n` expectation of the mesh product of `X_n`
with the current-day quote of `w_n` is `w_n` times the day-`n` expectation of `X_n`:
`E_n(⌜X_n · w_n⌝) ≈ₙ w_n · E_n(X_n)` — a weight that is a function of the market's own day-`n`
prices factors out. Listed in `corr-li-shutdown-open.txt`; the obstacle for the `loe` route is in
the section header. At `w := legitWeight` this is the mandate's `decidedWeight_factors`.
Source: [[corr-wf13-inventory]] 061 (reading (a)); mandate T2(b); wiki open-problems item 4
Kind: OPEN
Fidelity: variant: the mesh product at FAF's quote (`meshProductLUV`), as `GatedTower`; the weight at the current day
Hyps: (a) -/
theorem decidedWeight_factors_open (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (hval : Valued (paperDP T) X) (w : ℕ → ℚ) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) :
    (fun n => (meshProductLUV (paperCurrentWeightQuoteCode T w hw hmem) X n).expect
        (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (w n : ℝ) * (X n).expect (liaHistory (paperDP T)) n) := by
  sorry

end ReadingA

/-! ## (c) The exact form on the paradoxical family — PROVED in `Paradox.lean` (repair round 2)

Round 0 stated T2(c) here as the OPEN `exact_selfTrust_refuted_open`. Its two missing inputs
(the e.c. certificate of `n ↦ χ_n ⋏ ∼χ_n` and the negation-price complement) were built in
repair round 2, and the theorem — statement verbatim — is `exact_selfTrust_refuted` in
`Cleanroom.Corrigibility.CorrLiShutdown.Paradox` (kept in its own file: it needs FAF's affine
provability induction and the machine dispatch combinator, not needed by the rest of T2). -/

end Cleanroom.Corrigibility.CorrLiShutdown
