import Cleanroom.Trust.TrustMerge.Defs
import Cleanroom.Found.DefLattice.TwoOptionLUV
import Cleanroom.Deference.DefSelfTrust.Comb
import Cleanroom.Deference.DefSelfTrust.Ramp
import Cleanroom.Deference.DefSelfTrust.Transfer
import Cleanroom.Deference.DefSelfTrust.Weights
import Cleanroom.Found.LiQuoteLane.Codes

/-!
# `trust-merge` · Merge: `H` endorses `B` on hedged two-option menus (T5)

**T5 (trust-lab-009; [[deference-in-logical-induction-v2]] §10.2; the plan's "composition").**
From the §10 premise toward the merge expert — `CondTowerEst H DPH f est` ("LUV-Total-Trust
`H → B`", Route B's relocated hypothesis, grade (c) until T4(b) discharges its averaged form) —
and a generable ramp weight of the estimate, `H` soft-Total-Trusts `B` above threshold at
`(s, δ)` per quoted instance, hence hedged two-option Value against the constant:
`𝔼^H_n(twoOptionComb s XW W n) ≳ₙ s`, mirroring `def-self-trust`'s `selfCase_twoOptionValue`
through `def-lattice`'s `twoOptionComb_value_iff_productForm`.

The derivation (`def-self-trust`'s `est_ccee` → `est_bet` → `est_productForm` with `est` abstract):
1. the premise at the pulled-back ramp weight `w` (`w (f n) = ctsind_δ(est(X_n) > s)`) and the
   package `(XW, Z')` — `XW` the hedged product (within slack), `Z'` the exact quote of
   `est(X_n) · w (f n)` — gives `𝔼^H_n(XW_n) ≈ₙ 𝔼^H_n(Z'_n)`;
2. **the bet** (`betEst`): `Z'_n − s·W_n` is valued `(est(X_n) − s) · ctsind_δ(est(X_n) > s) ≥ 0`
   in every completed-theory world (no false positives, `sub_mul_ctsInd_nonneg`), so
   `thm:expprovind` (`lic_expect_combination_provind_ge`) gives `𝔼^H_n(Z'_n) − s·𝔼^H_n(W_n) ≳ₙ 0`;
3. transport along 1.

**What is derived and what is carried.** The weight's generability is *derived* for the ledger
instance (`ledgerRampWeight_pgenerable`): the ramp of `H`'s own rational day-`n` expectation of
the ledger LUV naming `B_n` (`li-quote-lane` F2/F4: a published number enters `H`'s feature
language as `H`'s estimate of the decided sentences naming it), pulled back along `f`
(`def-self-trust`'s `pullbackWeight`). So the instance is stated at the **reader's estimate**
`readEst H β X n = 𝔼^H_n(β_n)`, not at `B_n` itself; `readEst ≈ₙ est` per day is `readability`
and costs (L) (`hL`). Two hypotheses stay disclosed: `hprem` (c) — the cross-agent premise, which
no FAF theorem supplies for a distinct expert (that is T4 / the two-way pair) — and the quote `Z'`
(c) — a same-day product quote `⌜est(X_n) · w_{f n}⌝` in `H`'s language; FAF's quotation lane
emits deferred-day products (`paperConditionalExpectationQuoteCode`), and the same-day one over
`paperDP T ⊕ ledger` is `RationalQuoteCode.ofComputable` at a computable sequence (findings
F-Z').

**The premise is per source** (repair round 1, audit r1 B1 of both lenses). The round-0 statement
took `hprem : CondTowerEst H DPH f est` — the premise over *every* e.c. source — at the ledger
estimate `est := readEst H (fun _ n => ledgerLuv j n)`, which is the same number `𝔼^H_n(α_{j,n})`
for every source. That universal identifies the prices of the left products of any two sources
sharing the right quote `Z'`; at a source valued `1` everywhere (whose left product at the ramp
weight is the weight quote `W` itself) and one valued `0` everywhere it forces `𝔼^H_n(W_n) → 0`,
so the hedged gate died and the conclusion was `s + o(1) ≳ s`; with a same-day quote at
`(δ, s) = (1, −1)` the premise is outright false. These are now package theorems
(`MergeUniversal.lean`: `universalPremise_gate_dies`, `universalPremise_refuted`). The headline
takes the premise on the quoted family only, `hprem : CondTowerEstOn P DP f est {X}` — the
analogue of `LUVTotalTrustAvgOn {X}` (F-T3): the §10 premise toward `B` *about `X`*. Nothing
else in the derivation changes; the universal form implies it (`CondTowerEst.toOn`).

**Scope.** Direction: `H` reads `B` (the merge's `H`-side; two-way once `B`'s estimate is `A`'s
expectation of `H`'s quote, `partial: over the OPEN pair`); the one-way shadow (`H` reads a
*fixed* `A`, `paperOneWayPair`) gives the same statement with `hprem` a bare (c). Grade: per-day.
Weight class: `H`-generable. `0 < δ` throughout (a theorem whose only instance is `δ = 0` is a
stub). The `k`-option softmax form (`BlendValue`) is `def-squeeze-diamond`'s and not stated here.
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc Cleanroom.Found.LiQuoteLane
open Cleanroom.Deference.DefSelfTrust

noncomputable section

/-! ## The bet: no false positives at an abstract estimate -/

/-- **The bet `Z'_n − s·W_n` is nonnegative in every completed-theory world, so `thm:expprovind`
prices it `≳ₙ 0`** (`def-self-trust`'s `est_bet` with the estimate abstract): with `W_n` valued
at `ctsind_δ(est(X_n) > s)` and `Z'_n` at `est(X_n) · w (f n)` where `w (f n)` is that ramp, the
world value is `(est(X_n) − s) · ctsind_δ(est(X_n) > s) ≥ 0` — no false positives.
Source: vq-wiki-061 (step 3); `def-self-trust` `est_bet`; FAF
`lic_expect_combination_provind_ge`
Kind: C
Fidelity: exact
Hyps: (a) none beyond the reflection data of `W` and `Z'` -/
theorem betEst {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (est : (ℕ → LUV) → ℕ → ℝ) (X : ℕ → LUV) {δ : ℚ} (hδ : 0 < δ) (s : ℚ)
    (f : DeferralFunction) (w : ℕ → ℚ) (hw : ∀ n, (w (f n) : ℝ) = ctsInd δ (est X n) s)
    (W Z' : ℕ → LUV) (hW : LUV.MachineThresholdCodeSeq W) (hZ' : LUV.MachineThresholdCodeSeq Z')
    (hWr : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (W n) (ctsInd δ (est X n) s))
    (hZ'r : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Z' n) (est X n * (w (f n) : ℝ))) :
    (fun n => (Z' n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  set terms : List (ℚ × (ℕ → LUV)) := [(1, Z'), (-s, W)] with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hZ'
    · exact hW
  have hwv : LUVCombination.WorldValued (constComb 0 terms) DP := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact valuesAt_worldValue (hZ'r n v hv)
    · exact valuesAt_worldValue (hWr n v hv)
  have hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        (0 : ℝ) ≤ (constComb 0 terms n).value P ν := by
    intro n v hv ν hν
    have e₁ := (hν (EF.const 1, Z' n) (by simp [constComb, hterms])).eq (hZ'r n v hv)
    have e₂ := (hν (EF.const (-s), W n) (by simp [constComb, hterms])).eq (hWr n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂, hw n]
    push_cast
    nlinarith [sub_mul_ctsInd_nonneg hδ (est X n) (s : ℝ)]
  have h := lic_expect_combination_provind_ge (constComb_boundedSequence P 0 terms hcodes) hwv 0
    hval hworld
  have hE : (fun n => (constComb 0 terms n).expect P n) =
      (fun n => (Z' n).expect P n - (s : ℝ) * (W n).expect P n) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rwa [hE] at h

/-! ## T5 — soft Total Trust and hedged Value from the cross-agent premise -/

/-- **Soft Total Trust above threshold toward an abstract estimate, from the §10 premise on the
quoted family, per quoted instance** (T5's engine). Given `hprem : CondTowerEstOn P DP f est {X}`
(the premise *about `X`*; the universal `CondTowerEst` implies it by `CondTowerEst.toOn`, and at
an `X`-independent `est` the universal is degenerate — module docstring), a ramp `WeightQuoteEst`
`(W, XW)` for `X` at `(s, δ)`, a `P`-generable `[0,1]` weight `w` with `w (f n) = ctsind_δ(est(X_n)
> s)`, and an e.c. quote `Z'` of `est(X_n) · w (f n)`: `𝔼^P_n(XW_n) − s·𝔼^P_n(W_n) ≳ₙ 0`. Route:
the premise at the package `(XW, Z')` (step 1), the bet (step 2, `betEst`), transport (step 3).
Grade: per-day. Direction: `P` reads the expert whose estimate is `est`. Weight class:
`P`-generable (`hgen`).
Source: trust-lab-009; [[deference-in-logical-induction-v2]] §10.1–10.2 (line 3 = the premise;
the threshold inequality from `ccee` + `expprovind`); `def-self-trust` `selfSoftTotalTrustAbove`
Kind: C
Fidelity: variant: `Est` form; product within the quote's slack; premise on `{X}` (repair r1)
Hyps: (c) `hprem` — the cross-agent §10 premise on the quoted family (no FAF theorem supplies it
for a distinct expert; T4); (c) `Z'` — a same-day product quote in `P`'s language (FAF's lane
emits deferred-day products); `hgen` is (a) at the ledger instance
(`ledgerRampWeight_pgenerable`) -/
theorem thresholdIneqAboveEst_of_condTowerEst_at {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (est : (ℕ → LUV) → ℕ → ℝ) (X : ℕ → LUV)
    (hprem : CondTowerEstOn P DP f est {X})
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (hX : LUV.MachineThresholdCodeSeq X)
    (W XW : ℕ → LUV) (q : WeightQuoteEst DP est X (rampAbove δ s) W XW)
    (w : ℕ → ℚ) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hgen : PGenerableRat P w)
    (hw : ∀ n, (w (f n) : ℝ) = ctsInd δ (est X n) s)
    (Z' : ℕ → LUV) (hZ' : LUV.MachineThresholdCodeSeq Z')
    (hZ'r : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Z' n) (est X n * (w (f n) : ℝ))) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  have cq : CondQuoteEst DP f est X w XW Z' :=
    { left_codes := q.product_codes
      right_codes := hZ'
      slack := q.slack
      slack_tendsto := q.slack_tendsto
      source_valued := q.source_valued
      left_reflected := fun n v hv x hx => by
        obtain ⟨z, hz, hb⟩ := q.product_reflected n v hv x hx
        exact ⟨z, hz, by rwa [hw n]⟩
      right_reflected := hZ'r }
  have h1 : (fun n => (XW n).expect P n) ≈ₙ (fun n => (Z' n).expect P n) :=
    hprem X w (Set.mem_singleton X) hmem hgen hX XW Z' cq
  have h2 := betEst (P := P) hworld est X hδ s f w hw W Z' q.weight_codes hZ'
    (fun n v hv => q.weight_reflected n v hv) hZ'r
  exact asympGE_zero_of_asympEq_pair (s : ℝ) h1 (AsympEq.refl _) h2

/-- **T5 (headline, per quoted instance). `H` endorses `B` on the hedged two-option menu:**
under the hypotheses of `thresholdIneqAboveEst_of_condTowerEst_at`, the hedged strategy
`X·w + s(1 − w)` (`def-lattice`'s `twoOptionComb`) is worth at least the constant option in
the limit, `𝔼^H_n(twoOptionComb s XW W n) ≳ₙ s` — Value (LI form, two-option grade) with
expert `B`, by `twoOptionComb_value_iff_productForm` (an iff, so this is the threshold
inequality restated on the hedged combination; the content is in the engine).
Grade: per-day. Direction: `H` reads `B` (`partial: over the OPEN pair` once `B` is `A`'s
expectation of `H`'s quote; the one-way shadow has `hprem` bare (c)). Weight class: `H`-generable.
Source: trust-lab-009 ("`𝔼^H_t(Ŝ_t) ≳_w 𝔼^H_t(O^i_t)` … given `H`'s own coherence plus
LUV-Total-Trust `H → B`"); [[merging-inductors-model]] §(b.1) boxed statement (at two-option
grade, against the constant); [[deference-in-logical-induction-v2]] §10.2
Kind: C
Fidelity: weaker: two-option menus only, δ-hedged, against the constant (the `k`-option softmax
form is `def-squeeze-diamond`'s); `Est` form; per-day grade (the source's `≳_w` averaged form is
T6); premise on the quoted family `{X}` (repair r1)
Hyps: (c) `hprem` (on `{X}`); (c) `Z'`; `hgen` (a) at the ledger instance; all else (a) -/
theorem merge_twoOptionValue_of_crossTrust_at {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (est : (ℕ → LUV) → ℕ → ℝ) (X : ℕ → LUV)
    (hprem : CondTowerEstOn P DP f est {X})
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (hX : LUV.MachineThresholdCodeSeq X)
    (W XW : ℕ → LUV) (q : WeightQuoteEst DP est X (rampAbove δ s) W XW)
    (w : ℕ → ℚ) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hgen : PGenerableRat P w)
    (hw : ∀ n, (w (f n) : ℝ) = ctsInd δ (est X n) s)
    (Z' : ℕ → LUV) (hZ' : LUV.MachineThresholdCodeSeq Z')
    (hZ'r : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (Z' n) (est X n * (w (f n) : ℝ))) :
    (fun n => (twoOptionComb s XW W n).expect P n) ≳ₙ (fun _ => (s : ℝ)) :=
  (twoOptionComb_value_iff_productForm P s XW W).mpr
    (thresholdIneqAboveEst_of_condTowerEst_at hworld f est X hprem hδ s hX W XW q w hmem hgen hw
      Z' hZ' hZ'r)

/-- **The T5 conclusion is free at `s ≤ 0`** (audit r2 adversarial N2, probe ported): on any
`[0,1]`-valued history, `𝔼_n(twoOptionComb s XW W n) ≳ₙ s` holds for `s ≤ 0` with no premise,
since the product form `𝔼(XW) − s·𝔼(W)` is `≥ 0 ≥ s`. The T5 headlines therefore have content
only for `0 < s`; the dependents' rule takes `0 < δ` and should be read with `0 < s` too.
Source: audit r2 adversarial N2 (probe `NonposThresholdTrivial.lean`)
Kind: T (the trivial range of T5, disclosed)
Fidelity: n/a
Hyps: n/a -/
theorem twoOptionValue_trivial_of_nonpos (P : History) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (s : ℚ) (hs : s ≤ 0) (XW W : ℕ → LUV) :
    (fun n => (twoOptionComb s XW W n).expect P n) ≳ₙ (fun _ => (s : ℝ)) := by
  rw [twoOptionComb_value_iff_productForm]
  intro ε hε
  filter_upwards with n
  have h1 := (LUV.expect_mem_Icc P n (XW n) (hP n)).1
  have h2 := (LUV.expect_mem_Icc P n (W n) (hP n)).1
  have hs' : (s : ℝ) ≤ 0 := by exact_mod_cast hs
  nlinarith

/-! ## The ledger instance: the ramp weight is generable, derived -/

/-- **`H`'s exact rational day-`n` expectation of the ledger LUV** `α_{j,n}` (FAF's
`MarketComputation.expectQuote`): the rational whose cast is `readEst H (ledgerLuv j) · n`.
Source: `li-quote-lane` F2/F4 (the reader's estimate of the published number); FAF
`MarketComputation.expectQuote`
Kind: D
Fidelity: exact -/
def ledgerReadRat {H : History} (M : MarketComputation H) (j n : ℕ) : ℚ :=
  M.expectQuote (fun n => ledgerLuv j n) n

/-- The cast identity: `ledgerReadRat` is the reader's estimate of the ledger quote.
Source: none: infrastructure (FAF `expectQuote_cast`)
Kind: L
Fidelity: n/a -/
theorem ledgerReadRat_cast {H : History} (M : MarketComputation H) (j : ℕ) (X : ℕ → LUV)
    (n : ℕ) : ((ledgerReadRat M j n : ℚ) : ℝ) = readEst H (fun _ n => ledgerLuv j n) X n :=
  (M.expectQuote_cast (fun n => ledgerLuv j n) n).symm

/-- **The reader's estimate of the ledger quote is a `P`-generable rational sequence**:
`def-self-trust`'s `expectFeature` on the ledger family (`expectFeature_pgenerable` with
`ledgerLuv_thresholdCodes`), denoting `𝔼^H_n(α_{j,n}) = ledgerReadRat M j n`.
Source: `li-quote-lane` `ledgerFeature_pgenerable` (the same fact at the `EF` level); mandate
T1 ("prove the lemma `observable_estimate_pgenerable` for the ledger instance")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerReadRat_pgenerable {H : History} (M : MarketComputation H) (j : ℕ) :
    PGenerableRat H (ledgerReadRat M j) :=
  ⟨expectFeature (fun n => ledgerLuv j n),
    (expectFeature_pgenerable (ledgerLuv_thresholdCodes j)).toGeneratedRatFeature
      (fun n => by rw [expectFeature_denote, M.expectQuote_cast]; rfl)⟩

/-- **The ramp weight of `B`'s published estimate as `H` reads it**, pulled back along `f`:
`ledgerRampWeight M f j δ s (f n) = ctsind_δ(𝔼^H_n(α_{j,n}) > s)`, `0` off the image. This is
the weight the mandate derives from `ledgerRamp_pgenerable` + `pullBack_pgenerable`, in
`def-self-trust`'s rational vocabulary (`pullbackWeight`), so that it feeds `CondTowerEst`'s
`PGenerableRat` directly.
Source: mandate T5 ("the generability of the ramp of `B`'s published estimate on `H`'s market,
derived"); [[route-recurring-ccee]] §2 (R2)
Kind: D
Fidelity: exact -/
def ledgerRampWeight {H : History} (M : MarketComputation H) (f : DeferralFunction) (j : ℕ)
    (δ s : ℚ) : ℕ → ℚ :=
  pullbackWeight f (fun n => ratCtsInd δ (ledgerReadRat M j n) s)

/-- **The ledger ramp weight is `H`-generable** — derived, not assumed: ramp of a generable
rational (`pgenerableRat_ratCtsInd_left`), pulled back (`pullbackWeight_pgenerable`).
Source: mandate T5; `li-quote-lane` `ledgerRamp_pgenerable`; `def-self-trust`
`pullbackWeight_pgenerable`
Kind: C
Fidelity: exact
Hyps: (a); `hinj` (injectivity of `f`, as in `def-self-trust`) -/
theorem ledgerRampWeight_pgenerable {H : History} (M : MarketComputation H)
    (f : DeferralFunction) (hinj : Function.Injective f.f) (j : ℕ) {δ : ℚ} (hδ : 0 < δ)
    (s : ℚ) : PGenerableRat H (ledgerRampWeight M f j δ s) :=
  pullbackWeight_pgenerable f hinj (pgenerableRat_ratCtsInd_left (ledgerReadRat_pgenerable M j) hδ s)

/-- The ledger ramp weight lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ledgerRampWeight_mem {H : History} (M : MarketComputation H) (f : DeferralFunction)
    (j : ℕ) (δ s : ℚ) (m : ℕ) :
    0 ≤ ledgerRampWeight M f j δ s m ∧ ledgerRampWeight M f j δ s m ≤ 1 :=
  pullbackWeight_mem f (fun n => ratCtsInd_mem_Icc δ (ledgerReadRat M j n) s) m

/-- On the image of `f` the ledger ramp weight is the ramp of the reader's estimate:
`ledgerRampWeight M f j δ s (f n) = ctsind_δ(readEst(α_{j,n}) > s)`, as a real.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ledgerRampWeight_at_cast {H : History} (M : MarketComputation H) (f : DeferralFunction)
    (hinj : Function.Injective f.f) (j : ℕ) (δ s : ℚ) (X : ℕ → LUV) (n : ℕ) :
    ((ledgerRampWeight M f j δ s (f n) : ℚ) : ℝ) =
      ctsInd δ (readEst H (fun _ n => ledgerLuv j n) X n) (s : ℝ) := by
  unfold ledgerRampWeight ledgerReadRat
  rw [pullbackWeight_at f hinj, ← ratCtsInd_cast, readEst, M.expectQuote_cast]

/-- **T5 (headline, the ledger instance). `H` endorses `B` as it reads it, about the quoted
family, with the weight's generability derived:** for `H` an inductor over any process `DPH`,
`M` its market program, the merge estimate read through item `j` of `H`'s ledger
(`readEst H (ledgerLuv j)`, the same number for every source — which is why the premise is on
`{X}`), the §10 premise toward that estimate **about `X`** (`hprem : CondTowerEstOn … {X}`, (c)),
a ramp `WeightQuoteEst` `(W, XW)` and an e.c. quote `Z'` of `readEst(X_n) · w (f n)` ((c)),
hedged two-option Value holds: `𝔼^H_n(twoOptionComb s XW W n) ≳ₙ s`. The weight is
`ledgerRampWeight M f j δ s`, `H`-generable by `ledgerRampWeight_pgenerable` — hypothesis (a).
The round-0 form with the universal premise `CondTowerEst` is degenerate — its hypotheses force
the gate to die and, given a same-day quote, contradict `thm:expprovind` (`MergeUniversal.lean`);
no instance of the restricted premise is exhibited either (the premise is the OPEN content, T4).
Grade: per-day. Direction: `H` reads `B` through its ledger (`partial: over the OPEN pair`
when the ledger's table is `A`'s expectation of `H`'s quote; one-way shadow at a fixed `A`).
Weight class: `H`-generable, derived. The estimate is the *reader's* estimate of the published
number; `readEst ≈ₙ B` per day is `readability` and costs (L).
Three disclosures from audit r2 (adversarial N1–N3). `DPH` is **unconstrained**: nothing ties
`ledgerLuv j` to a ledger process or its table to `B` — `ledgerLuv j` enters only as an e.c.
family (which is what makes `hgen` derivable), so this is the generic instance at `H`'s
expectation of any e.c. LUV family, and the "ledger"/"`B`" reading is the instantiation
`DPH := ledgerProcess base (A's table) σ`, which the statement permits but does not mention.
Content only for `0 < s` (`twoOptionValue_trivial_of_nonpos`). And the two (c) hypotheses stand
or fall **together**: `CondTowerEstOn … {X}` is vacuous unless some e.c. family is valued at
`est X n · w (f n)` exactly in every completed-theory world — which is what `Z'` is — so both
are conditional on the same-day product quote (F-API 2), not two independent (c)s.
Source: trust-lab-009; [[merging-inductors-model]] §(b.1); mandate T5; audit r1 B1; audit r2
adversarial N1–N3
Kind: C
Fidelity: weaker: two-option, δ-hedged, against the constant; at the reader's estimate of `B`
(not `B`); `Est` form; the premise on the quoted family `{X}` only
Hyps: (c) `hprem` (on `{X}`; no instance exhibited); (c) `Z'`; `hinj`; all else (a) -/
theorem merge_twoOptionValue_of_crossTrust {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (M : MarketComputation H) (f : DeferralFunction) (hinj : Function.Injective f.f) (j : ℕ)
    (X : ℕ → LUV)
    (hprem : CondTowerEstOn H DPH f (readEst H (fun _ n => ledgerLuv j n)) {X})
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (hX : LUV.MachineThresholdCodeSeq X)
    (W XW : ℕ → LUV)
    (q : WeightQuoteEst DPH (readEst H (fun _ n => ledgerLuv j n)) X (rampAbove δ s) W XW)
    (Z' : ℕ → LUV) (hZ' : LUV.MachineThresholdCodeSeq Z')
    (hZ'r : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
      v.ValuesAt (Z' n) (readEst H (fun _ n => ledgerLuv j n) X n *
        (ledgerRampWeight M f j δ s (f n) : ℝ))) :
    (fun n => (twoOptionComb s XW W n).expect H n) ≳ₙ (fun _ => (s : ℝ)) :=
  merge_twoOptionValue_of_crossTrust_at hworld f _ X hprem hδ s hX W XW q
    (ledgerRampWeight M f j δ s) (ledgerRampWeight_mem M f j δ s)
    (ledgerRampWeight_pgenerable M f hinj j hδ s)
    (fun n => ledgerRampWeight_at_cast M f hinj j δ s X n) Z' hZ' hZ'r

end

end Cleanroom.Trust.TrustMerge
