import Cleanroom.Trust.TrustMerge.Merge

/-!
# `trust-merge` · MergeUniversal: the universal premise at a source-independent estimate is
degenerate (audit r1 B1, proved as package theorems)

Round 0's T5 ledger instance took the §10 premise over **every** e.c. source,
`hprem : CondTowerEst H DPH f (readEst H (fun _ n => ledgerLuv j n))`, at an estimate that does
not depend on the source (`readEst … X n = 𝔼^H_n(α_{j,n})` for every `X`). Both round-1 auditors
found the consequence; this file carries it into the library so that the restriction to the
quoted family in `Merge.lean` (`CondTowerEstOn … {X}`) is justified by kernel-checked facts, not
by prose:

* `universalPremise_gate_eq_quote`: `hprem` at a source valued `1` everywhere (its left product
  at the ramp weight is the weight quote `W` itself) gives `𝔼^H_n(W_n) ≈ₙ 𝔼^H_n(Z'_n)`;
* `universalPremise_zero_eq_quote`: `hprem` at a source valued `0` everywhere (its own left
  product) gives `𝔼^H_n(X⁰_n) ≈ₙ 𝔼^H_n(Z'_n)`;
* `universalPremise_gate_dies`: hence `𝔼^H_n(W_n) → 0` under round 0's full hypothesis package —
  the hedged gate is dead, and the round-0 conclusion `𝔼^H_n(twoOptionComb s XW W n) ≳ₙ s` was
  `s + o(1) ≳ s`;
* `universalPremise_refuted`: at `(δ, s) = (1, −1)` the ramp is identically `1` on `[0,1]`-valued
  estimates, the weight-quote package is inhabited by the constant-1 source itself, and the
  round-0 `Z'` hypothesis is a same-day quote of `𝔼^H_n(α_{j,n})`; then `𝔼^H(X¹) → 0` against
  `thm:expprovind`'s `𝔼^H(X¹) ≳ₙ 1`: **the universal premise is false for every inductor whose
  language has that same-day quote** — the F-API 2 object the report says is constructible over
  `paperDP T ⊕ ledger`;
* `universalPremise_refuted_literal`: the constant sources are `literalIndicator ⊤` and
  `literalIndicator ⊥`, e.c. (constant sentence families) and valued `1` / `0` in every world of
  every process, so the refutation needs only the same-day quote.

The generic theorems `thresholdIneqAboveEst_of_condTowerEst_at` /
`merge_twoOptionValue_of_crossTrust_at` now take the premise on `{X}` and do not inherit this.
Ported from the round-1 adversarial probe `run/wp/trust-merge/audit-r1-probes/T5GateDies.lean`
(same proofs; the constant sources discharged here).
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc Cleanroom.Found.LiQuoteLane
open Cleanroom.Deference.DefSelfTrust

noncomputable section

/-- Under round 0's ledger-instance package, the universal premise at a source valued `1`
everywhere gives `𝔼^H_n(W_n) ≈ₙ 𝔼^H_n(Z'_n)`: the weight quote is the left product of the
constant-1 source.
Source: audit r1 B1 (adversarial probe `gate_eq_quote`)
Kind: L
Fidelity: exact
Hyps: (a) none beyond round 0's package -/
theorem universalPremise_gate_eq_quote {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH]
    (M : MarketComputation H) (f : DeferralFunction) (hinj : Function.Injective f.f) (j : ℕ)
    (hprem : CondTowerEst H DPH f (readEst H (fun _ n => ledgerLuv j n)))
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (X : ℕ → LUV) (W XW : ℕ → LUV)
    (q : WeightQuoteEst DPH (readEst H (fun _ n => ledgerLuv j n)) X (rampAbove δ s) W XW)
    (Z' : ℕ → LUV) (hZ' : LUV.MachineThresholdCodeSeq Z')
    (hZ'r : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
      v.ValuesAt (Z' n) (readEst H (fun _ n => ledgerLuv j n) X n *
        (ledgerRampWeight M f j δ s (f n) : ℝ)))
    (X1 : ℕ → LUV) (hX1 : LUV.MachineThresholdCodeSeq X1)
    (hX1v : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → v.ValuesAt (X1 n) 1) :
    (fun n => (W n).expect H n) ≈ₙ (fun n => (Z' n).expect H n) := by
  have hw : ∀ n, ((ledgerRampWeight M f j δ s (f n) : ℚ) : ℝ) =
      ctsInd δ (readEst H (fun _ n => ledgerLuv j n) X1 n) (s : ℝ) :=
    fun n => ledgerRampWeight_at_cast M f hinj j δ s X1 n
  have cq : CondQuoteEst DPH f (readEst H (fun _ n => ledgerLuv j n)) X1
      (ledgerRampWeight M f j δ s) W Z' :=
    { left_codes := q.weight_codes
      right_codes := hZ'
      slack := fun _ => 0
      slack_tendsto := tendsto_const_nhds
      source_valued := fun n v hv => ⟨1, hX1v n v hv⟩
      left_reflected := fun n v hv x hx => by
        have hx1 : x = 1 := hx.eq (hX1v n v hv)
        refine ⟨ctsInd δ (readEst H (fun _ n => ledgerLuv j n) X1 n) (s : ℝ), ?_, ?_⟩
        · exact q.weight_reflected n v hv
        · rw [hx1, one_mul, hw n, sub_self, abs_zero]
      right_reflected := fun n v hv => hZ'r n v hv }
  exact hprem X1 (ledgerRampWeight M f j δ s) (ledgerRampWeight_mem M f j δ s)
    (ledgerRampWeight_pgenerable M f hinj j hδ s) hX1 W Z' cq

/-- Under the same package, the universal premise at a source valued `0` everywhere gives
`𝔼^H_n(X⁰_n) ≈ₙ 𝔼^H_n(Z'_n)`: the source is its own left product.
Source: audit r1 B1 (adversarial probe `zero_eq_quote`)
Kind: L
Fidelity: exact
Hyps: (a) none beyond round 0's package -/
theorem universalPremise_zero_eq_quote {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH]
    (M : MarketComputation H) (f : DeferralFunction) (hinj : Function.Injective f.f) (j : ℕ)
    (hprem : CondTowerEst H DPH f (readEst H (fun _ n => ledgerLuv j n)))
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (X : ℕ → LUV)
    (Z' : ℕ → LUV) (hZ' : LUV.MachineThresholdCodeSeq Z')
    (hZ'r : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
      v.ValuesAt (Z' n) (readEst H (fun _ n => ledgerLuv j n) X n *
        (ledgerRampWeight M f j δ s (f n) : ℝ)))
    (X0 : ℕ → LUV) (hX0 : LUV.MachineThresholdCodeSeq X0)
    (hX0v : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → v.ValuesAt (X0 n) 0) :
    (fun n => (X0 n).expect H n) ≈ₙ (fun n => (Z' n).expect H n) := by
  have cq : CondQuoteEst DPH f (readEst H (fun _ n => ledgerLuv j n)) X0
      (ledgerRampWeight M f j δ s) X0 Z' :=
    { left_codes := hX0
      right_codes := hZ'
      slack := fun _ => 0
      slack_tendsto := tendsto_const_nhds
      source_valued := fun n v hv => ⟨0, hX0v n v hv⟩
      left_reflected := fun n v hv x hx => by
        have hx0 : x = 0 := hx.eq (hX0v n v hv)
        exact ⟨0, hX0v n v hv, by rw [hx0, zero_mul, sub_zero, abs_zero]⟩
      right_reflected := fun n v hv => hZ'r n v hv }
  exact hprem X0 (ledgerRampWeight M f j δ s) (ledgerRampWeight_mem M f j δ s)
    (ledgerRampWeight_pgenerable M f hinj j hδ s) hX0 X0 Z' cq

/-- A source valued `0` in every completed-theory world has expectation `→ 0`
(`thm:expprovind`, `≤` form, plus nonnegativity of prices).
Source: FAF `lic_expect_combination_provind_le`; audit r1 B1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem constSource_zero_expect_tendsto {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (X0 : ℕ → LUV) (hX0 : LUV.MachineThresholdCodeSeq X0)
    (hX0v : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → v.ValuesAt (X0 n) 0) :
    Tendsto (fun n => (X0 n).expect H n) atTop (𝓝 0) := by
  set terms : List (ℚ × (ℕ → LUV)) := [(1, X0)] with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [hp]
    exact hX0
  have hwv : LUVCombination.WorldValued (constComb 0 terms) DPH := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hq]
    exact valuesAt_worldValue (hX0v n v hv)
  have hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        (constComb 0 terms n).value H ν ≤ 0 := by
    intro n v hv ν hν
    have e₁ := (hν (EF.const 1, X0 n) (by simp [constComb, hterms])).eq (hX0v n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁]
    push_cast
    ring_nf
    exact le_refl _
  have h := lic_expect_combination_provind_le (constComb_boundedSequence H 0 terms hcodes) hwv 0
    hval hworld
  have hE : (fun n => (constComb 0 terms n).expect H n) = (fun n => (X0 n).expect H n) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rw [hE] at h
  have hnn : ∀ n, 0 ≤ (X0 n).expect H n := fun n =>
    (LUV.expect_mem_Icc H n (X0 n) (fun φ => IsLogicalInductor.price_mem_Icc (P := H) (DP := DPH) n φ)).1
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h (ε / 2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn n)]
  linarith

/-- A source valued `1` in every completed-theory world has expectation `≳ₙ 1`
(`thm:expprovind`, `≥` form).
Source: FAF `lic_expect_combination_provind_ge`; audit r1 B1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem constSource_one_expect_ge {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (X1 : ℕ → LUV) (hX1 : LUV.MachineThresholdCodeSeq X1)
    (hX1v : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → v.ValuesAt (X1 n) 1) :
    (fun n => (X1 n).expect H n) ≳ₙ (fun _ => (1 : ℝ)) := by
  set terms : List (ℚ × (ℕ → LUV)) := [(1, X1)] with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [hp]
    exact hX1
  have hwv : LUVCombination.WorldValued (constComb 0 terms) DPH := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hq]
    exact valuesAt_worldValue (hX1v n v hv)
  have hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        (1 : ℝ) ≤ (constComb 0 terms n).value H ν := by
    intro n v hv ν hν
    have e₁ := (hν (EF.const 1, X1 n) (by simp [constComb, hterms])).eq (hX1v n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁]
    push_cast
    ring_nf
    exact le_refl _
  have h := lic_expect_combination_provind_ge (constComb_boundedSequence H 0 terms hcodes) hwv 1
    hval hworld
  have hE : (fun n => (constComb 0 terms n).expect H n) = (fun n => (X1 n).expect H n) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rwa [hE] at h

/-- **The gate dies under round 0's package.** Under the full hypothesis list of round 0's
`merge_twoOptionValue_of_crossTrust` (the universal premise at the `X`-independent ledger
estimate), plus e.c. sources valued `0` and `1` everywhere (which every FAF process has,
`universalPremise_refuted_literal`), `𝔼^H_n(W_n) → 0`: the hedged gate is dead, and the round-0
conclusion `𝔼^H_n(twoOptionComb s XW W n) ≳ₙ s` was `s + o(1) ≳ s` — true for a reason the
source did not intend. This is why `Merge.lean`'s headline now takes the premise on `{X}`.
Source: audit r1 B1 (both lenses; adversarial probe `gate_dies`); mandate T5 trap ("a theorem
whose only instance is `δ = 0` is a stub") and T8 trap ("a refutation must exhibit positive gate
mass")
Kind: C (the two `L` identifications chained with `thm:expprovind`; relabelled from P in repair r2, audit r2 fidelity N2)
Fidelity: exact (about round 0's statement)
Hyps: (a) none beyond round 0's package and the constant sources -/
theorem universalPremise_gate_dies {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (M : MarketComputation H) (f : DeferralFunction) (hinj : Function.Injective f.f) (j : ℕ)
    (hprem : CondTowerEst H DPH f (readEst H (fun _ n => ledgerLuv j n)))
    {δ : ℚ} (hδ : 0 < δ) (s : ℚ) (X : ℕ → LUV) (W XW : ℕ → LUV)
    (q : WeightQuoteEst DPH (readEst H (fun _ n => ledgerLuv j n)) X (rampAbove δ s) W XW)
    (Z' : ℕ → LUV) (hZ' : LUV.MachineThresholdCodeSeq Z')
    (hZ'r : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
      v.ValuesAt (Z' n) (readEst H (fun _ n => ledgerLuv j n) X n *
        (ledgerRampWeight M f j δ s (f n) : ℝ)))
    (X1 : ℕ → LUV) (hX1 : LUV.MachineThresholdCodeSeq X1)
    (hX1v : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → v.ValuesAt (X1 n) 1)
    (X0 : ℕ → LUV) (hX0 : LUV.MachineThresholdCodeSeq X0)
    (hX0v : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → v.ValuesAt (X0 n) 0) :
    Tendsto (fun n => (W n).expect H n) atTop (𝓝 0) := by
  have h1 := universalPremise_gate_eq_quote M f hinj j hprem hδ s X W XW q Z' hZ' hZ'r X1 hX1 hX1v
  have h2 := universalPremise_zero_eq_quote M f hinj j hprem hδ s X Z' hZ' hZ'r X0 hX0 hX0v
  have h0 := constSource_zero_expect_tendsto (H := H) hworld X0 hX0 hX0v
  have h12 : (fun n => (W n).expect H n) ≈ₙ (fun n => (X0 n).expect H n) := h1.trans h2.symm
  unfold AsympEq at h12
  have := h12.add h0
  simpa using this

/-- **The universal premise is refutable.** At `(δ, s) = (1, −1)` the ramp `ctsind_1(c > −1)`
is identically `1` on `[0,1]`-valued estimates, so round 0's weight-quote package is inhabited by
the constant-1 source itself, and round 0's `Z'` hypothesis is a same-day quote of
`c_n = 𝔼^H_n(α_{j,n})` (the F-API 2 object the report says is constructible over
`paperDP T ⊕ ledger`). Then `universalPremise_gate_dies` gives `𝔼^H_n(X¹_n) → 0` while
`thm:expprovind` gives `𝔼^H_n(X¹_n) ≳ₙ 1`:
**`CondTowerEst H DPH f (readEst H (fun _ n => ledgerLuv j n))` is false for every inductor `H`
whose language has that same-day quote.** The §10 premise *as a universal over sources* cannot
be stated at a single ledger item (F-T5).
Source: audit r1 B1 (adversarial probe `hprem_refuted_of_sameDayQuote`); F-T5
Kind: P
Fidelity: exact (a refutation of round 0's premise, given the same-day quote)
Hyps: (c) the same-day quote `Z'` (not built, F-API 2); the constant sources (discharged in
`universalPremise_refuted_literal`); all else (a) -/
theorem universalPremise_refuted {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (M : MarketComputation H) (f : DeferralFunction) (hinj : Function.Injective f.f) (j : ℕ)
    (X1 : ℕ → LUV) (hX1 : LUV.MachineThresholdCodeSeq X1)
    (hX1v : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → v.ValuesAt (X1 n) 1)
    (X0 : ℕ → LUV) (hX0 : LUV.MachineThresholdCodeSeq X0)
    (hX0v : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → v.ValuesAt (X0 n) 0)
    (Z' : ℕ → LUV) (hZ' : LUV.MachineThresholdCodeSeq Z')
    (hZ'r : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
      v.ValuesAt (Z' n) (readEst H (fun _ n => ledgerLuv j n) X1 n *
        (ledgerRampWeight M f j 1 (-1) (f n) : ℝ))) :
    ¬ CondTowerEst H DPH f (readEst H (fun _ n => ledgerLuv j n)) := by
  intro hprem
  -- the estimate lies in `[0,1]`, so the ramp at `(1, −1)` is identically `1`
  have hc : ∀ n, 0 ≤ readEst H (fun _ n => ledgerLuv j n) X1 n := fun n =>
    (LUV.expect_mem_Icc H n (ledgerLuv j n)
      (fun φ => IsLogicalInductor.price_mem_Icc (P := H) (DP := DPH) n φ)).1
  have hramp : ∀ n, rampAbove 1 (-1) (readEst H (fun _ n => ledgerLuv j n) X1 n) = 1 := by
    intro n
    have h0 := hc n
    simp only [rampAbove, ctsInd]
    push_cast
    rw [div_one]
    have h1 : (0 : ℝ) ≤ readEst H (fun _ n => ledgerLuv j n) X1 n - -1 := by linarith
    rw [max_eq_right h1]
    apply min_eq_left
    linarith
  -- round 0's weight-quote package, inhabited by the constant-1 source itself
  have q : WeightQuoteEst DPH (readEst H (fun _ n => ledgerLuv j n)) X1 (rampAbove 1 (-1))
      X1 X1 :=
    { weight_codes := hX1
      product_codes := hX1
      slack := fun _ => 0
      slack_tendsto := tendsto_const_nhds
      source_valued := fun n v hv => ⟨1, hX1v n v hv⟩
      weight_reflected := fun n v hv => by rw [hramp n]; exact hX1v n v hv
      product_reflected := fun n v hv x hx => by
        have hx1 : x = 1 := hx.eq (hX1v n v hv)
        exact ⟨1, hX1v n v hv, by rw [hx1, hramp n, one_mul, sub_self, abs_zero]⟩ }
  have hdead := universalPremise_gate_dies hworld M f hinj j hprem (by norm_num : (0 : ℚ) < 1)
    (-1) X1 X1 X1 q Z' hZ' hZ'r X1 hX1 hX1v X0 hX0 hX0v
  have hone := constSource_one_expect_ge (H := H) hworld X1 hX1 hX1v
  -- `𝔼(X¹) → 0` and `𝔼(X¹) ≳ 1` contradict
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hone (1 / 4) (by norm_num))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    ((Metric.tendsto_nhds.1 hdead) (1 / 4) (by norm_num))
  have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
  have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
  rw [Real.dist_eq, sub_zero] at h2
  have := (abs_lt.1 h2).2
  linarith

/-- `literalIndicator ⊤` is valued `1` in every completed-theory world of every process.
Source: none: infrastructure (`def-lattice` `literalIndicator_valuesAt`)
Kind: L
Fidelity: n/a -/
theorem literalIndicator_top_valuesAt (DPH : DeductiveProcess) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory DPH) :
    v.ValuesAt ((fun _ : ℕ => literalIndicator (⊤ : Sentence)) n) 1 := by
  have h := literalIndicator_valuesAt (⊤ : Sentence) DPH hv
  have hp : v.payout (⊤ : Sentence) = 1 := by
    simp [PCWorld.payout, PCWorld.holds_top]
  rwa [hp] at h

/-- `literalIndicator ⊥` is valued `0` in every completed-theory world of every process.
Source: none: infrastructure (`def-lattice` `literalIndicator_valuesAt`)
Kind: L
Fidelity: n/a -/
theorem literalIndicator_bot_valuesAt (DPH : DeductiveProcess) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory DPH) :
    v.ValuesAt ((fun _ : ℕ => literalIndicator (⊥ : Sentence)) n) 0 := by
  have h := literalIndicator_valuesAt (⊥ : Sentence) DPH hv
  have hbot : ¬ v.Holds (⊥ : Sentence) := by
    simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  have hp : v.payout (⊥ : Sentence) = 0 := by
    simp [PCWorld.payout, hbot]
  rwa [hp] at h

/-- **The universal premise is refutable, constant sources discharged:** the sources valued `1`
and `0` everywhere are `literalIndicator ⊤` and `literalIndicator ⊥` (e.c. as constant sentence
families), so the only hypothesis beyond the inductor is the same-day quote `Z'` of
`𝔼^H_n(α_{j,n})` at `(δ, s) = (1, −1)`.
Source: audit r1 B1; F-T5
Kind: C (`universalPremise_refuted` with the constant sources discharged; relabelled from P in repair r2, audit r2 fidelity N2)
Fidelity: exact (a refutation of round 0's premise, given the same-day quote)
Hyps: (c) the same-day quote `Z'` (F-API 2); all else (a) -/
theorem universalPremise_refuted_literal {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (M : MarketComputation H) (f : DeferralFunction) (hinj : Function.Injective f.f) (j : ℕ)
    (Z' : ℕ → LUV) (hZ' : LUV.MachineThresholdCodeSeq Z')
    (hZ'r : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH →
      v.ValuesAt (Z' n) (readEst H (fun _ n => ledgerLuv j n)
        (fun _ => literalIndicator (⊤ : Sentence)) n *
        (ledgerRampWeight M f j 1 (-1) (f n) : ℝ))) :
    ¬ CondTowerEst H DPH f (readEst H (fun _ n => ledgerLuv j n)) :=
  universalPremise_refuted hworld M f hinj j
    (fun _ => literalIndicator (⊤ : Sentence))
    (literalIndicator_machineThresholdCodeSeq (MachineSentenceCodes.const (⊤ : Sentence)))
    (literalIndicator_top_valuesAt DPH)
    (fun _ => literalIndicator (⊥ : Sentence))
    (literalIndicator_machineThresholdCodeSeq (MachineSentenceCodes.const (⊥ : Sentence)))
    (literalIndicator_bot_valuesAt DPH) Z' hZ' hZ'r

end

end Cleanroom.Trust.TrustMerge
