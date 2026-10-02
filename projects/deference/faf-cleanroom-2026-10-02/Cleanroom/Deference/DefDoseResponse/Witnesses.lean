import Cleanroom.Deference.DefDoseResponse.Steering
import Cleanroom.Deference.DefDoseResponse.Variants
import Cleanroom.Deference.DefDoseResponse.Thinned
import Cleanroom.Deference.DefDoseResponse.Sampling
import Cleanroom.Li.LiPseudorandom.Family
import Cleanroom.Li.LiProjection.Witnesses
import Cleanroom.Fa.FaForcingTrader.A.Witnesses
import Cleanroom.Fa.FaForcingTrader.Schedule
import Cleanroom.Fa.FaTheoremA.LemmaP
import Cleanroom.Deference.DefTrackingPin.Column
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `def-dose-response` · Witnesses: the N+ packages over FAF's paper LIA

**`paperArms` (T6/T2, N+).** Over `paperDP 𝗜𝚺₁`, two coins — `coinFull ≡ true` (dose `1`) and
`coinHalf n := (n % 2 == 0)` (dose `½`) — the window `N = 4`, the target `v = 1`, `γ = ½`, the
committed stream `streamOne ≡ 1` (so `a_j = 1` on every steering day, as the steered advisor
produces when `v = 1`, which is exact at every mesh). Both arms inhabit the full hypothesis package
of `arm_isLogicalInductor` (every clause discharged — `paperArms_package`; the inductor conclusion
`paperArm_inductor` rests on `li-projection` (A), as the theorem does); their weights differ
(`3/4` vs `5/8`), their destinations on `u` are `3/4` and `5/8` (`paperArm_full_destination`,
`paperArm_half_destination`, grade (a)), the cross-arm audit tends to `1/8` and does not pass
(`paperArms_audit_fires`, grade (a)). Real LIA, real ledgers, non-constant weights, two distinct
destinations.

**T3 soundness witness (N+, grade (a)).** The same two arms on a `u`-free sentence decided by the
base — the indicator of `paperPrimeDecompose σ` for a provable `σ` — have destination `1` on both
sides and every cross-arm audit on it passes (`paperArms_decided_auto_passes`), through
`arm_restrict` (the arms price `u`-free sentences as their bases) and T3.5 at the bases. N+
because the arms differ (distinct destinations on `u`) while agreeing on `X`.

**`paperSteeredAdvisor` (T2(b-half)/(c), N+).** The steered advisor `steeredAdvisor A 1 4` over
FAF's LIA `A` on the mirror ledger of the dose-`1` arm is an inductor exactly
(`paperSteeredAdvisor_inductor`), quotes `1` on days `< 4` (`paperSteeredAdvisor_quotes`), and
its quote stream tends to `3/4` (`paperSteeredAdvisor_quote_tendsto`); any market program `M` for
the arm exists at grade (a) (`paperArm_full_marketComputation`).

**The thinned same-market instance (T1, N−).** `fa-forcing-trader`'s `A.theoremSS_paper_self`
thinned by `fa-theorem-a`'s even-day indicator on the even schedule `linearSchedule 0` (fixed in
repair round 1 — with a free schedule the odd days made `hdiv` false outright): the package
objects are real, but `hdiv` is not discharged — on the even schedule it is exactly
`fa-forcing-trader`'s own open divergence hypothesis (`thinned_evenDays_linear_divergent_iff`) —
`CA` is OPEN there, and `hL` is free only because `A = H` (the two-market gap is
`fa-forcing-trader`'s T11). `coinIndicator_coinHalf` ties the arms' witness coin to the indicator.

**T4's package inhabited (N+ package / N− content, repair round 1).** `sampling_lemma_truthStar`:
the full hypothesis package of the Sampling Lemma at `li-pseudorandom`'s `truthStar` coin
(pseudorandom for every deferral relative to FAF's LIA over `atomDP`), the constant weighting and
the constant feature `X ≡ 1`, with `succDeferral` — every hypothesis discharged; at `X ≡ 1` the
conclusion is the pseudorandom frequency restated, so the content (a non-constant,
price-reading `X`) is not exercised, as the ledger says.
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefTrackingPin
  Cleanroom.Fa.FaTheoremA Cleanroom.Fa.FaForcingTrader Cleanroom.Li.LiPseudorandom
open Filter Topology

/-! ## The paper arms -/

/-- The base process of the witnesses: FAF's `paperDP 𝗜𝚺₁`.
Source: mandate § Witness (`paperArms`)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperBase : DeductiveProcess := paperDP 𝗜𝚺₁

/-- The dose-`1` coin.
Source: mandate § Witness
Kind: D
Fidelity: n/a -/
def coinFull : ℕ → Bool := fun _ => true

/-- The dose-`½` coin: exposed on even days.
Source: mandate § Witness
Kind: D
Fidelity: n/a -/
def coinHalf : ℕ → Bool := fun n => (n % 2 == 0)

/-- The committed stream of the witness: `1` every day (the steered advisor's output at `v = 1`).
Source: mandate § Witness ("any stream with `a j = 1` for `j < 4`")
Kind: D
Fidelity: n/a -/
def streamOne : ℕ → ℚ := fun _ => 1

/-- `coinFull_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem coinFull_computable : Computable coinFull := Computable.const true

/-- `coinHalf_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem coinHalf_computable : Computable coinHalf :=
  (Primrec₂.comp Primrec.beq (Primrec₂.comp Primrec.nat_mod Primrec.id (Primrec.const 2))
    (Primrec.const 0)).to_comp

/-- `streamOne_computable`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem streamOne_computable : Computable streamOne := Computable.const 1

/-- `streamOne_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem streamOne_mem : ∀ n, 0 ≤ streamOne n ∧ streamOne n ≤ 1 := fun _ => by simp [streamOne]

/-- The steered prefix of the witness stream.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem streamOne_prefix : ∀ j < 4, streamOne j = 1 := fun _ _ => rfl

/-- The witness arm at a coin: `M(½, 4)` on the ledger `(c, streamOne)` over `paperDP 𝗜𝚺₁`.
Source: mandate § Witness (`paperArms`)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperArm (c : ℕ → Bool) : History := arm paperBase (1 / 2) 4 c streamOne

/-- Every stage of the witness arms' exposure ledgers is satisfiable.
Source: mandate § Witness
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem paperArm_hworld (c : ℕ → Bool) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess paperBase c streamOne).D n) :=
  armProcess_hworld_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) c streamOne

/-- The witness arms' bases are logical inductors (FAF's LIA over the computable ledger).
Source: mandate § Witness
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem paperArmBase_inductor (c : ℕ → Bool) (hc : Computable c) :
    IsLogicalInductor (armBase paperBase c streamOne) (armProcess paperBase c streamOne) :=
  armBase_isLogicalInductor (paperDP_computable 𝗜𝚺₁) hc streamOne_computable

/-- Realized dose of the full coin over the window: `1`.
Source: mandate § Witness
Kind: L
Fidelity: n/a -/
theorem realizedDose_coinFull : realizedDose coinFull 4 = 1 := by
  simp [realizedDose, coinFull]

/-- Realized dose of the half coin over the window: `½`.
Source: mandate § Witness
Kind: L
Fidelity: n/a -/
theorem realizedDose_coinHalf : realizedDose coinHalf 4 = 1 / 2 := by
  simp [realizedDose, coinHalf]
  rw [show ((Finset.range 4).filter fun x => x % 2 = 0).card = 2 by decide]
  norm_num

/-- The full arm's jump target: `3/4`.
Source: mandate § Witness ("`armWeight … c₁ a 4 = 3/4`")
Kind: L
Fidelity: n/a -/
theorem armWeight_coinFull : armWeight (1 / 2) 4 coinFull streamOne 4 = 3 / 4 := by
  simp [armWeight, response, testimony, coinFull, streamOne]
  norm_num

/-- The half arm's jump target: `5/8`.
Source: mandate § Witness ("`armWeight … c₂ a 4 = 5/8`")
Kind: L
Fidelity: n/a -/
theorem armWeight_coinHalf : armWeight (1 / 2) 4 coinHalf streamOne 4 = 5 / 8 := by
  simp [armWeight, response, testimony, coinHalf, streamOne, Finset.sum_range_succ]
  norm_num

/-- **T6 witness package (N+).** Every hypothesis of `arm_isLogicalInductor` discharged for both
coins over `paperDP 𝗜𝚺₁`, with the realized doses distinct and the weights non-constant.
Source: mandate § Witness (`paperArms`); [[anson-2-inventory]] 028/029 (a second N+ instance of Lemma A over a ledger process)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperArms_package :
    ComputableDeductiveProcess paperBase ∧ AtomFreeProcess protAtom paperBase ∧
      (0 : ℚ) < 1 / 2 ∧ (1 / 2 : ℚ) < 1 ∧ Computable coinFull ∧ Computable coinHalf ∧
      Computable streamOne ∧ (∀ n, 0 ≤ streamOne n ∧ streamOne n ≤ 1) ∧
      realizedDose coinFull 4 ≠ realizedDose coinHalf 4 ∧
      armWeight (1 / 2) 4 coinFull streamOne 0 ≠ armWeight (1 / 2) 4 coinFull streamOne 4 ∧
      armWeight (1 / 2) 4 coinFull streamOne 4 ≠ armWeight (1 / 2) 4 coinHalf streamOne 4 :=
  ⟨paperDP_computable 𝗜𝚺₁, paperDP_atomFree 𝗜𝚺₁ 0, by norm_num, by norm_num, coinFull_computable,
   coinHalf_computable, streamOne_computable, streamOne_mem,
   by rw [realizedDose_coinFull, realizedDose_coinHalf]; norm_num,
   by rw [armWeight_of_lt _ _ _ _ (by norm_num), armWeight_coinFull]; norm_num,
   by rw [armWeight_coinFull, armWeight_coinHalf]; norm_num⟩

/-- **The witness arms are logical inductors** over their exposure ledgers (T6 at the package;
rests on `li-projection` (A)).
Source: mandate § Witness
Kind: N+
Fidelity: n/a
Hyps: (a) none; rests on the OPEN rewriters through `arm_isLogicalInductor` -/
theorem paperArm_inductor (c : ℕ → Bool) (hc : Computable c) :
    IsLogicalInductor (paperArm c) (armProcess paperBase c streamOne) :=
  arm_isLogicalInductor (paperDP_computable 𝗜𝚺₁) (paperDP_atomFree 𝗜𝚺₁ 0) (by norm_num)
    (by norm_num) 4 hc streamOne_computable streamOne_mem

/-- **The full arm settles at `3/4`** (grade (a)).
Source: mandate § Witness ("`limitingBelief (arm …) u` takes the two values")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperArm_full_destination : limitingBelief (paperArm coinFull) protSentence = 3 / 4 := by
  haveI := paperArmBase_inductor coinFull coinFull_computable
  rw [dose_graded_destination (paperArm_hworld coinFull) (1 / 2) (by norm_num) streamOne_prefix,
    realizedDose_coinFull]
  norm_num

/-- **The half arm settles at `5/8`** (grade (a)).
Source: mandate § Witness
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperArm_half_destination : limitingBelief (paperArm coinHalf) protSentence = 5 / 8 := by
  haveI := paperArmBase_inductor coinHalf coinHalf_computable
  rw [dose_graded_destination (paperArm_hworld coinHalf) (1 / 2) (by norm_num) streamOne_prefix,
    realizedDose_coinHalf]
  norm_num

/-- The two witness arms are different markets.
Source: mandate § Witness (N+ grounds)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperArms_differ : paperArm coinFull ≠ paperArm coinHalf := by
  intro h
  have := congrArg (fun P => limitingBelief P protSentence) h
  simp only [paperArm_full_destination, paperArm_half_destination] at this
  norm_num at this

/-- **T2(d) at the witness: the audit tends to `1/8`** (grade (a)).
Source: mandate § Witness ("audit limit `1/8`")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperArms_audit_fires :
    Tendsto (crossArmAudit (paperArm coinFull) (paperArm coinHalf) (LUV.indicatorOf protSentence))
      atTop (𝓝 (1 / 8)) := by
  haveI := paperArmBase_inductor coinFull coinFull_computable
  haveI := paperArmBase_inductor coinHalf coinHalf_computable
  have h := cross_arm_audit_fires (paperArm_hworld coinFull) (paperArm_hworld coinHalf) (1 / 2)
    (by norm_num : 0 < 4) streamOne_prefix
  rw [realizedDose_coinFull, realizedDose_coinHalf] at h
  convert h using 2
  norm_num

/-- **T2(d) at the witness: the uniform audit does not pass.**
Source: mandate § Witness
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperArms_audit_not_pass :
    ¬ Tendsto (crossArmAudit (paperArm coinFull) (paperArm coinHalf)
      (LUV.indicatorOf protSentence)) atTop (𝓝 0) := by
  haveI := paperArmBase_inductor coinFull coinFull_computable
  haveI := paperArmBase_inductor coinHalf coinHalf_computable
  exact cross_arm_audit_fires_ne (paperArm_hworld coinFull) (paperArm_hworld coinHalf)
    (by norm_num : 0 < 4) streamOne_prefix (by norm_num)
    (by rw [realizedDose_coinFull, realizedDose_coinHalf]; norm_num)

/-- **T2(e) at the witness**: the half arm *is* the content-blind arm with slope `1/4`.
Source: mandate § Witness; [[dose-response]] §6.3 T2(e)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperArm_half_eq_blind : paperArm coinHalf = armBlind paperBase (1 / 4) 4 coinHalf streamOne := by
  have h := non_attribution paperBase (1 / 2) (by norm_num : 0 < 4) (c := coinHalf) (v := 1)
    (fun j hj _ => streamOne_prefix j hj)
  convert h using 2
  norm_num

/-! ## T3 soundness witness: base-decided content, grade (a) -/

/-- An arm's expectation of the indicator of a `u`-free sentence is its base's (the thresholds
`φ ⋏ ∼∼φ` are `u`-free; `arm_restrict`).
Source: [[dose-response]] §6.1 Lemma A (restriction)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem indicatorOf_expect_arm_eq (base : DeductiveProcess) (γ : ℚ) (N : ℕ) (c : ℕ → Bool)
    (a : ℕ → ℚ) (n : ℕ) {φ : Sentence} (hφ : AtomFreeSentence protAtom φ) :
    (LUV.indicatorOf φ).expect (arm base γ N c a) n =
      (LUV.indicatorOf φ).expect (armBase base c a) n := by
  rw [indicatorOf_expect_eq, indicatorOf_expect_eq,
    arm_restrict base γ N c a n (hφ.and hφ.neg.neg)]

/-- The indicator of a provable sentence's decomposition is determined via `paperDP 𝗜𝚺₁` at `1`
(FAF's coverage of provable sentences; `def-tracking-pin`'s `indicatorOf_valuesAt_one`).
Source: [[dose-response]] §7 Cor T3.5 ("`X` is determined via `Γ_0` with its value decided")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem paperPrime_determined (σ : LO.FirstOrder.ArithmeticSentence) (hσ : 𝗜𝚺₁ ⊢ σ) :
    LUV.DeterminedVia (LUV.indicatorOf (paperPrimeDecompose σ)) paperBase 1 :=
  fun _ hv => indicatorOf_valuesAt_one hv (hv.holds_of_mem_stage
    (paperDP_covers_of_paperTheoryDP 𝗜𝚺₁ (paperTheoryDP_covers_outer_provable 𝗜𝚺₁ σ hσ)))

/-- **T3 soundness / T3.5 at the witness (N+, grade (a)).** On the indicator of a base-decided
`u`-free sentence, the two witness arms — which differ on `u` — have every cross-arm audit pass,
over every battery and at the uniform weighting. Through `arm_restrict` the arms' expectations
are their bases', and T3.5 at the bases (grade (a)) does the rest; no (A).
Source: mandate § Witnesses (T3 soundness); [[dose-response]] §7 Cor T3.5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperArms_decided_auto_passes (σ : LO.FirstOrder.ArithmeticSentence) (hσ : 𝗜𝚺₁ ⊢ σ) :
    (∀ w, IsBattery w → passes w (paperArm coinFull) (paperArm coinHalf)
        (LUV.indicatorOf (paperPrimeDecompose σ))) ∧
      Tendsto (crossArmAudit (paperArm coinFull) (paperArm coinHalf)
        (LUV.indicatorOf (paperPrimeDecompose σ))) atTop (𝓝 0) := by
  haveI := paperArmBase_inductor coinFull coinFull_computable
  haveI := paperArmBase_inductor coinHalf coinHalf_computable
  have h := decided_content_auto_passes_arms (Pi := armBase paperBase coinFull streamOne)
    (Pj := armBase paperBase coinHalf streamOne) (indicatorOf_machineThresholdCodes _)
    (paperArm_hworld coinFull) (paperArm_hworld coinHalf) (paperPrime_determined σ hσ)
  have hfree : AtomFreeSentence protAtom (paperPrimeDecompose σ) :=
    atomFreeSentence_paperPrimeDecompose 0 σ
  have hgap : crossArmGap (paperArm coinFull) (paperArm coinHalf)
      (LUV.indicatorOf (paperPrimeDecompose σ)) =
      crossArmGap (armBase paperBase coinFull streamOne) (armBase paperBase coinHalf streamOne)
        (LUV.indicatorOf (paperPrimeDecompose σ)) := by
    funext n
    unfold crossArmGap
    rw [indicatorOf_expect_arm_eq _ _ _ _ _ _ hfree, indicatorOf_expect_arm_eq _ _ _ _ _ _ hfree]
  refine ⟨fun w hw => ?_, ?_⟩
  · unfold passes
    rw [hgap]
    exact h.1 w hw
  · unfold crossArmAudit
    rw [hgap]
    exact h.2

/-! ## The steered advisor over the mirror ledger -/

/-- The full arm is a `ComputableMarket` outright.
Source: mandate § Witness (`paperSteeredAdvisor`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem paperArm_full_computableMarket : ComputableMarket (paperArm coinFull) :=
  haveI := paperArmBase_inductor coinFull coinFull_computable
  arm_computableMarket (by norm_num) (by norm_num) 4 streamOne_mem

/-- A market program for the full arm exists.
Source: mandate § Witness
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem paperArm_full_marketComputation : Nonempty (MarketComputation (paperArm coinFull)) :=
  paperArm_full_computableMarket.nonemptyComputation

/-- The mirror ledger process of the full arm: `A`'s process records the arm's realized next-day
expectations of `𝟙u`, published next day.
Source: mandate § Witness; `li-quote-lane` T2.4
Kind: D
Fidelity: n/a -/
noncomputable abbrev mirrorProcess (M : MarketComputation (paperArm coinFull)) : DeductiveProcess :=
  ledgerProcess paperBase (realizedExpectation M protX succDeferral) armSchedule

/-- FAF's LIA over the mirror ledger is an inductor (`li-quote-lane`'s `mirrorPair_inductor`).
Source: mandate § Witness
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem mirror_inductor (M : MarketComputation (paperArm coinFull)) :
    IsLogicalInductor (liaHistory (mirrorProcess M)) (mirrorProcess M) :=
  mirrorPair_inductor M protX (machineThresholdCodeSeq_const (indicatorOf_machineThresholdCodes _))
    succDeferral paperBase (paperDP_computable 𝗜𝚺₁) armSchedule armSchedule_computable

/-- Every stage of the mirror ledger is satisfiable.
Source: mandate § Witness
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem mirror_hworld (M : MarketComputation (paperArm coinFull)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((mirrorProcess M).D n) :=
  ledgerProcess_hworld (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁)

/-- **The steered advisor of the witness**: FAF's LIA over the mirror ledger, steered to `1` on
days `< 4`.
Source: mandate § Witness (`paperSteeredAdvisor`)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperSteeredAdvisor (M : MarketComputation (paperArm coinFull)) : History :=
  steeredAdvisor (liaHistory (mirrorProcess M)) 1 4

/-- **The steered advisor is an inductor exactly** (N+ for T2(c)'s neighbour).
Source: mandate § Witness ("an inductor exactly (`prescribe_finiteSupport`)")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSteeredAdvisor_inductor (M : MarketComputation (paperArm coinFull)) :
    IsLogicalInductor (paperSteeredAdvisor M) (mirrorProcess M) :=
  haveI := mirror_inductor M
  steeredAdvisor_isLogicalInductor _ _ 1 4

/-- **The steered advisor quotes `1` on days `< 4`.**
Source: mandate § Witness ("quotes `1` on days `< 4`")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSteeredAdvisor_quotes (M : MarketComputation (paperArm coinFull)) {n : ℕ}
    (hn : n < 4) : quoteStreamR (paperSteeredAdvisor M) n = 1 := by
  have h := steeredAdvisor_quote_exact (liaHistory (mirrorProcess M)) (v := 1) hn (k := n + 1)
    le_rfl (by push_cast; field_simp)
  simpa using h

/-- **The advisor's quote stream tends to the full arm's destination `3/4`** (T2(b-half) at the
witness, grade (a)).
Source: mandate § Witness ("`quoteStream → 3/4`")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paper_production_quote_tendsto (M : MarketComputation (paperArm coinFull)) :
    Tendsto (quoteStreamR (liaHistory (mirrorProcess M))) atTop (𝓝 (3 / 4)) := by
  haveI := paperArmBase_inductor coinFull coinFull_computable
  haveI := mirror_inductor M
  have h := production_quote_tendsto (paperArm_hworld coinFull) (1 / 2) (by norm_num : 0 < 4)
    streamOne_prefix M succDeferral paperBase armSchedule (liaHistory (mirrorProcess M))
    (mirror_hworld M)
  rw [realizedDose_coinFull] at h
  convert h using 2
  norm_num

/-- The steered advisor's own quote stream also tends to `3/4` (it is unmodified from day `4`).
Source: mandate § Witness
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSteeredAdvisor_quote_tendsto (M : MarketComputation (paperArm coinFull)) :
    Tendsto (quoteStreamR (paperSteeredAdvisor M)) atTop (𝓝 (3 / 4)) := by
  refine (paper_production_quote_tendsto M).congr' ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  unfold quoteStreamR
  simp only [LUV.expect, LUV.expectApprox]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (steeredAdvisor_unmodified _ 1 hn _).symm

/-! ## The thinned same-market instance -/

/-- The even-day indicator is an exposure indicator on every market.
Source: mandate T1 witness ("`C n := EF.const (if n % 2 = 0 then 1 else 0)`")
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem evenDays_exposureIndicator (P : History) : ExposureIndicator P evenDays :=
  ⟨evenDays_pgenerable, fun n => by rw [evenDays_denote]; split_ifs <;> simp⟩

/-- The T6/T2 witness coin `coinHalf` read as a feature (`coinIndicator`, `Thinned.lean`) *is*
`fa-theorem-a`'s `evenDays`: the arms' coin and T1's exposure indicator are one object in the
witnesses (fidelity audit r1, N4).
Source: mandate D6; fidelity audit r1 N4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem coinIndicator_coinHalf : coinIndicator coinHalf = evenDays := by
  funext n
  unfold coinIndicator evenDays coinHalf
  by_cases h : n % 2 = 0 <;> simp [h]

/-- **On the even schedule the even-day thinning is invisible**: `linearSchedule 0` is the even
days `2, 4, 6, …`, on which `evenDays` is `1`, so the thinned gate denotes exactly as
`fa-forcing-trader`'s bare `schedGate` on that schedule.
Source: mandate T1 witness trap (ii) ("the witness needs a coin of positive density on the schedule"); adversarial audit r1 B2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem thinnedGate_evenDays_linear_denote (Y : ℕ → LUV) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (A : History) (n : ℕ) :
    (thinnedGate evenDays Y (linearSchedule 0) t δ n).denote A =
      (schedGate Y (linearSchedule 0) t δ n).denote A := by
  rw [thinnedGate_denote evenDays Y _ t hδ A n, schedGate_denote Y _ t hδ A n, evenDays_denote]
  by_cases h : ∃ k, (linearSchedule 0).f k = n
  · obtain ⟨k, hk⟩ := h
    have h2 : n % 2 = 0 := by
      rw [← hk, linearSchedule_apply]
      omega
    rw [if_pos h2, one_mul]
  · rw [schedInd_of_not_mem _ (fun k hk => h ⟨k, hk⟩)]
    ring

/-- **So the witness's `hdiv` is `fa-forcing-trader`'s own**: on the even schedule the thinned
gate is a divergent weighting iff the bare scheduled gate is. The hypothesis the witness below
leaves open is therefore exactly the one `A.theoremSS_paper_self` leaves open there — a fact
about the LIA's quotes of `selfY` on the even days that nothing in either package evaluates.
Source: adversarial audit r1 B2 (fix (i)); mandate T1 witness trap (ii)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem thinned_evenDays_linear_divergent_iff (Y : ℕ → LUV) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (A : History) :
    DivergentWeighting (thinnedGate evenDays Y (linearSchedule 0) t δ) A ↔
      DivergentWeighting (schedGate Y (linearSchedule 0) t δ) A := by
  have hfun := thinnedGate_evenDays_linear_denote Y t hδ A
  have hps : prefixSum (fun n => (thinnedGate evenDays Y (linearSchedule 0) t δ n).denote A) =
      prefixSum (fun n => (schedGate Y (linearSchedule 0) t δ n).denote A) := by
    congr 1
    funext n
    exact hfun n
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun n => ?_, ?_⟩
    · rw [← hfun n]
      exact h1 n
    · rwa [hps] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun n => ?_, ?_⟩
    · rw [hfun n]
      exact h1 n
    · rwa [← hps] at h2

/-- **T1's limit-point grade at the same-market instance, thinned by the even-day indicator on
the even schedule** `linearSchedule 0`. Grade **N−** (repair round 1, adversarial B2): the
package objects are real (FAF's paper LIA, FAF's Σ₁ quote family `selfY`, a genuine `{0,1}`
indicator, an admissible window-disjoint schedule on which the indicator has density `1`), but
`hdiv` is not discharged — it is `fa-forcing-trader`'s own open divergence hypothesis
(`thinned_evenDays_linear_divergent_iff`), a fact about the LIA's quotes on the even days that is
not evaluated here — and `hL` is free only because `A = H`. The schedule is fixed so that the
thinning cannot kill the gate: with the earlier free `d`, an odd schedule made `hdiv` false
outright (the audit's probe `ThinnedOddSchedule.lean`).
Source: mandate T1 witness; `fa-forcing-trader` `A.theoremSS_paper_self`; adversarial audit r1 B2
Kind: N-
Fidelity: n/a
Hyps: (a) `hdiv` (not discharged — see above) -/
theorem thinned_paper_self (t δ : ℚ)
    (hdiv : DivergentWeighting (thinnedGate evenDays A.selfY (linearSchedule 0) t δ) A.selfH) :
    HasLimitPoint (weightedBias
      (fun n => (thinnedGate evenDays A.selfY (linearSchedule 0) t δ n).denote A.selfH)
      (quoteSeq A.selfY A.selfH) (fun n => (cleanX n).expect A.selfH n)) 0 :=
  haveI := w1_inductorH
  thinned_forcing_limitPoint A.self_pkg cleanX_codes (paperDP_hworld 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)
    (fun n v hv => indicatorOf_valued (witnessQuoted 0 n) _ v hv) (windowDisjoint_succ_linear 0)
    evenDays_pgenerable t δ
    ⟨_, thinnedGate_pgenerable evenDays_pgenerable A.self_pkg.quote_codes _ t δ, fun _ => rfl⟩
    hdiv

/-- **T1's gated form at the same-market instance, thinned, on the even schedule**, under a
certificate `CA` (OPEN inhabitant in `fa-forcing-trader`). Grade **N−** for the same reasons as
`thinned_paper_self`, plus `CA`.
Source: mandate T1 witness; adversarial audit r1 B2
Kind: N-
Fidelity: n/a
Hyps: (a) `hdiv` (not discharged); (b) `CA` -/
theorem thinned_paper_self_gated (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hdiv : DivergentWeighting (thinnedGate evenDays A.selfY (linearSchedule 0) t δ) A.selfH)
    (CA : QuoteCertificate A.selfH (paperDP 𝗜𝚺₁) A.selfY (paperDP_hworld 𝗜𝚺₁)
      (linearSchedule 0)) :
    SchedThresholdAboveEv
      (fun n => (thinnedGate evenDays A.selfY (linearSchedule 0) t δ n).denote A.selfH)
      (fun n => (cleanX n).expect A.selfH n) t :=
  haveI := w1_inductorH
  thinned_forcing_gated A.self_pkg cleanX_codes (paperDP_hworld 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)
    (fun n v hv => indicatorOf_valued (witnessQuoted 0 n) _ v hv) (windowDisjoint_succ_linear 0)
    (evenDays_exposureIndicator _) t hδ
    ⟨_, thinnedGate_pgenerable evenDays_pgenerable A.self_pkg.quote_codes _ t δ, fun _ => rfl⟩
    hdiv CA

/-! ## T4's hypothesis package inhabited -/

/-- The prefix sums of the constant weight `1` are `n + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem prefixSum_const_one (n : ℕ) : prefixSum (fun _ => (1 : ℝ)) n = (n : ℝ) + 1 := by
  simp [prefixSum]

/-- The constant weighting `1` is a divergent weighting on every market.
Source: none: infrastructure (T4 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem constOne_divergent (P : History) : DivergentWeighting (fun _ => EF.const 1) P := by
  refine ⟨fun n => by simp, ?_⟩
  show Tendsto (prefixSum fun _ => (EF.const (1 : ℚ)).denote P) atTop atTop
  have h1 : (fun _ : ℕ => (EF.const (1 : ℚ)).denote P) = fun _ => (1 : ℝ) := by
    funext n
    simp
  rw [h1]
  have h2 : (prefixSum fun _ => (1 : ℝ)) = fun n : ℕ => (n : ℝ) + 1 := funext prefixSum_const_one
  rw [h2]
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- The constant weighting `1` is `succ`-patient on every market (window sums are `2`).
Source: none: infrastructure (T4 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem constOne_patient_succ (P : History) :
    DeferralPatient succDeferral (fun _ => EF.const 1) P := by
  refine ⟨2, fun n => ?_⟩
  simp only [EF.denote_const, Rat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : (Finset.Icc n (succDeferral.f n)).card = 2 := by
    show (Finset.Icc n (n + 1)).card = 2
    rw [Nat.card_Icc]
    omega
  rw [hc]
  norm_num

/-- **T4's package is inhabited** at `li-pseudorandom`'s `truthStar` coin (FAF's
`PseudorandomFrequency` for every deferral relative to FAF's LIA over `atomDP`,
`truthStar_pseudorandom`), the constant weighting, the constant feature `X ≡ 1` and
`succDeferral`: every hypothesis of `sampling_lemma` discharged. **N− for content**: at `X ≡ 1`
the conclusion `(∑_{n≤N} c_n − p(N+1))/(N+1) → 0` is the pseudorandom frequency restated; a
price-reading `X` on that market is not instantiated (ledger § T4).
Source: mandate T4 witness; fidelity audit r1 N6 / adversarial N5
Kind: N+ (package) / N- (content)
Fidelity: n/a
Hyps: (a) none -/
theorem sampling_lemma_truthStar (a g : ℕ → ℕ) (hg : ∀ j, j < g j) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    Tendsto (fun N => (prefixSum (truthR (truthStar a g p)) N - p * ((N : ℝ) + 1)) /
      ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have h := sampling_lemma hp (truthStar_pseudorandom a g hg p hp succDeferral)
    (pgenerableWeighting_const 1) (constOne_divergent _) (constOne_patient_succ _)
    (pgenerableWeighting_const 1) (fun n => by simp)
  simp only [EF.denote_const, Rat.cast_one, one_mul, mul_one, prefixSum_const_one] at h
  exact h

end Cleanroom.Deference.DefDoseResponse
