import Cleanroom.Deference.DefObstruction.Tracking
import Cleanroom.Found.LiQuoteLane.Readability

/-!
# `def-obstruction` · Tower: the tower reduces to tracking; no timely tower on the diagonal (T4)

**The reduction (T4(c)).** Over FAF's `≈ₙ`: a tower instance `𝔼^H(X) ≈ₙ 𝔼^H(⌜a⌝)`, the read-off
`𝔼^H(⌜a⌝) ≈ₙ a`, self-trust `𝔼^H(X) ≈ₙ 𝔼^H(⌜Y⌝)` and present-accuracy `𝔼^H(⌜Y⌝) ≈ₙ Y` give
tracking `a ≈ₙ Y` (`tower_imp_tracking`, pure `≈ₙ` algebra, kind L — the earlier Lean's content,
re-founded on FAF's relation); so where tracking fails the tower fails (`pointwise_tower_fails`).
The present-credence form `(Tower) ↔ a ≈ₙ 𝔼^H(X)` under read-off is `tower_iff_present`.

**The deferred-day read-off (the right corner-quote).** `𝔼^H_{F n}(α_{0,n}) ≈ₙ a 0 n`
(`readoff_deferred`) is `li-quote-lane`'s L4 (`readability_ofApprox`) along the deferral: the
padded ledger family `padLedger F m := α_{0, F⁻¹(m)}` read at day `m`. It needs two certificates:
`hL`, the e.c. certificate of the padded ledger family (`(a)` at `succDeferral`:
`padLedger_codes_succ` from `ledgerLuv_thresholdCodes`), and **`hz`, the `P`-generability of the
table along the deferral** — the mandate expected `hL` alone to suffice; it does not: FAF's
`thm:expprovind` is stated at a *constant* value, and reaching the varying value `a 0 n` means
subtracting an e.c. rational stream, i.e. reading the table. This is exactly `li-quote-lane`'s
`hL` of L4 (its finding F2), the same cost model as `hR`/`hR'` (findings F-ReadOff). The engine is
the general lemma `expect_asympEq_of_determinedVia_generable`: expectation provability induction
at a generable approximant of a determined value, for any e.c. LUV family over any process — a
FAF API request (FAF's `lic_expect_combination_provind_*` take a constant).

**T4(a) (headline 3).** Over the table-only carrier with the certificates, the deferred-day tower
instance fails by `½` on the diagonal: `∀ ε > 0, ∀ᶠ n, ½ − ε ≤ |𝔼^H_{F n}(𝟙 g_n) − 𝔼^H_{F n}(α_{0,n})|`
(`tower_fails_diagonal`). Composition: `lemmaB_expect_table` (left corner-quote → the side),
`readoff_deferred` (right corner-quote → the quote), `exact_defect` (Lemma 2.1), two triangle
inequalities.

**T4(b), the same-day form.** The notes' literal `𝔼^H_n(g_n) ≈ₙ 𝔼^H_n(⌜a_n⌝)` fails by `½` too
(`tower_fails_diagonal_sameDay`), with the day-`n` certificates (`trueSide`/`falseSide` e.c.,
`hL` for the table at day `n` — `li-quote-lane`'s `readability` itself) and **no publication
hypothesis**: the mandate expected `PublicationSchedule.sameDay` to be needed for the day-`n`
form; it is not, since Lemma B is a completed-theory provability induction (findings F-Regimes,
F-IndexBookkeeping: the notes' "decided at stage `n`" vs "recorded by `n+1`" slip is real as a
description of the process and immaterial to the theorem).

**T4(d).** `def-lattice`'s `Expert`/`Tower` have the shape "the expert's deferred expectation of
`X`"; the obstruction's expert is "the predictor's day-`n` expectation of a quote of the reader's
deferred expectation". The shapes differ; `Tower E` cannot state `Mart(H→A)`. Findings F-Expert;
the stretch row S3 (`PredictorExpert`) is not built.

Scope: one-way throughout.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. The reduction over FAF's `≈ₙ` (T4(c)) -/

/-- **The tower reduces to tracking** (pure `≈ₙ` algebra): from a tower instance `EhX ≈ₙ Eha`,
the read-off `Eha ≈ₙ a`, self-trust `EhX ≈ₙ EhY` and present-accuracy `EhY ≈ₙ Y`, tracking
`a ≈ₙ Y`. The four inputs are the corner-quote collapses of [[no-timely-pointwise-tower]] §2;
over the diagonal, read-off is `readoff_deferred` and the composite of self-trust with
present-accuracy is Lemma B — the theorems below do not route through this lemma, which is kept
as the re-founded form of the earlier Lean's `tower_imp_tracking`.
Scope: real sequences.
Source: [[no-timely-pointwise-tower]] §2 (anson-013); `TowerAndAcceleration.lean:tower_imp_tracking` (lean-deference-027); root-deference-033; root-fa-037
Kind: L
Fidelity: exact (over FAF's `AsympEq`)
Hyps: the four `≈ₙ` inputs (this is the abstract reduction; the headline that discharges them is `tower_fails_diagonal`) -/
theorem tower_imp_tracking {EhX Eha EhY a Y : ℕ → ℝ}
    (hTower : EhX ≈ₙ Eha) (hRead : Eha ≈ₙ a) (hCee : EhX ≈ₙ EhY) (hAcc : EhY ≈ₙ Y) :
    a ≈ₙ Y :=
  ((hRead.symm.trans hTower.symm).trans hCee).trans hAcc

/-- **The pointwise tower is false wherever tracking is** (contrapositive of the reduction).
Scope: real sequences.
Source: [[no-timely-pointwise-tower]] §1; `TowerAndAcceleration.lean:pointwise_tower_fails`
Kind: L
Fidelity: exact
Hyps: as `tower_imp_tracking`, plus `¬ (a ≈ₙ Y)` -/
theorem pointwise_tower_fails {EhX Eha EhY a Y : ℕ → ℝ}
    (hRead : Eha ≈ₙ a) (hCee : EhX ≈ₙ EhY) (hAcc : EhY ≈ₙ Y) (hTrackingFails : ¬ (a ≈ₙ Y)) :
    ¬ (EhX ≈ₙ Eha) :=
  fun hTower => hTrackingFails (tower_imp_tracking hTower hRead hCee hAcc)

/-- **The present-credence form**: under read-off, the tower instance is equivalent to `A`'s quote
matching the reader's present credence, `(Tower) ↔ a ≈ₙ 𝔼^H(X)`.
Scope: real sequences.
Source: [[no-timely-pointwise-tower]] §2 ("(Tower) ⟺ `a_n ≈_n ℙ^H_n(P^{(n)})`"); anson-013
Kind: L
Fidelity: exact
Hyps: `hRead` (read-off) -/
theorem tower_iff_present {EhX Eha a : ℕ → ℝ} (hRead : Eha ≈ₙ a) :
    (EhX ≈ₙ Eha) ↔ (a ≈ₙ EhX) :=
  ⟨fun h => (h.trans hRead).symm, fun h => h.symm.trans hRead.symm⟩

/-! ## B. Expectation provability induction at a generable approximant (FAF API request) -/

/-- **Expectation provability induction at a generable approximant of a determined value.** For
an e.c. LUV family `X` determined, in `DP`'s completed theory, at `[0,1]`-values `val n`, and a
`P`-generable rational stream `ẑ` with `ẑ_n − val_n → 0`: `𝔼^P_n(X_n) ≈ₙ val_n`. This is
`li-quote-lane`'s `readability_ofApprox` with the ledger LUV replaced by any e.c. family and the
table by any determined value; the route is FAF's vanishing-error affine provability induction on
`mesh_n(X_n) − ⟨ẑ_n⟩`. FAF's `lic_expect_combination_provind_*` take a *constant* value; this is
the varying-value form, which needs the approximant to be generable — the hypothesis that carries
the cost model.
Scope: one process.
Source: LI `thm:expprovind` (varying value); `li-quote-lane` `readability_ofApprox` (the proof generalized); mandate T4(a)
Kind: C
Fidelity: n/a (infrastructure; FAF API request)
Hyps: (c) `hz` — generability of the approximant in FAF's fixed class; all else (a) -/
theorem expect_asympEq_of_determinedVia_generable (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X) (val : ℕ → ℝ)
    (hdet : ∀ n, LUV.DeterminedVia (X n) DP (val n))
    (hval : ∀ n, 0 ≤ val n ∧ val n ≤ 1)
    (zhat : ℕ → ℚ) (hz : PGenerableRat P zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - val n) atTop (𝓝 0)) :
    (fun n => (X n).expect P n) ≈ₙ val := by
  obtain ⟨feat, hfeat⟩ := hz
  have hneg : PGenerableWeighting (fun n => EF.mul (EF.const (-1)) (feat n)) :=
    PGenerableWeighting.mul (pgenerableWeighting_const (-1)) hfeat.toWeighting
  set As : ℕ → AffineCombination := fun n =>
    ((X n).expectAffine (n + 1)).addConstEF (EF.mul (EF.const (-1)) (feat n)) with hAs
  have hpoly : AffineCombination.PolySequence As :=
    polySequence_addConstEF (LUV.expectAffineSeq_polySequence X hX) _ hneg
  have hprices : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hconst : ∀ n, (EF.mul (EF.const (-1)) (feat n)).denote P = -(zhat n : ℝ) := by
    intro n
    simp [hfeat.denote n]
  have hvalue : ∀ n (w : Valuation),
      (As n).value P w = (X n).expectApprox w (n + 1) - zhat n := by
    intro n w
    rw [hAs]
    dsimp only
    rw [AffineCombination.addConstEF_value, LUV.expectAffine_value, hconst]
    ring
  have hprice : ∀ n, (As n).price P n = (X n).expect P n - zhat n := by
    intro n
    rw [AffineCombination.price, hvalue]
    rfl
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n, |(zhat n : ℝ) - val n| ≤ B := by
    obtain ⟨B, hB⟩ := (hlim.abs).bddAbove_range
    exact ⟨B, fun n => hB (Set.mem_range_self n)⟩
  have hbounded : BoundedAffinePrices As P := by
    refine ⟨2 + B, ?_, fun n m => ?_⟩
    · have h0 := hB 0
      have h0' := abs_nonneg ((zhat 0 : ℝ) - val 0)
      linarith
    rw [AffineCombination.price, hvalue]
    have h1 := (X n).expectApprox_nonneg (P m) (n + 1) (fun s => (hprices m s).1)
    have h2 := (X n).expectApprox_le_one (P m) (n + 1) (fun s => (hprices m s).2)
    obtain ⟨h3, h4⟩ := hval n
    obtain ⟨h5, h6⟩ := abs_le.mp (hB n)
    rw [abs_le]
    constructor <;> linarith
  have hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C := by
    refine ⟨1, fun n => ?_⟩
    rw [hAs]
    dsimp only
    rw [AffineCombination.addConstEF_magnitude]
    exact LUV.expectAffine_magnitude_le_one _ P _
  have hvalb : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWithTheory DP → |(As n).value P v.payout| ≤ ε := by
    intro ε hε
    have hlim1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim2 : Tendsto (fun n => |(zhat n : ℝ) - val n|) atTop (𝓝 0) := by
      have := hlim.abs
      rwa [abs_zero] at this
    filter_upwards [hlim1.eventually (eventually_le_nhds (half_pos hε)),
      hlim2.eventually (eventually_le_nhds (half_pos hε))] with n hn1 hn2 v hv
    rw [hvalue]
    have hd := hdet n v hv
    have hgrid : ∀ i : ℕ, i < n + 1 →
        (((i : ℝ) / ((n + 1 : ℕ) : ℝ) < val n →
            v.Holds ((X n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)))) ∧
          (val n < (i : ℝ) / ((n + 1 : ℕ) : ℝ) →
            ¬ v.Holds ((X n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))))) := by
      intro i _
      have hc : (((i : ℚ) / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      have := hd.2.2 ((i : ℚ) / ((n + 1 : ℕ) : ℚ))
      rw [hc] at this
      exact this
    have hnear := PCWorld.expectApprox_near_ofGrid hd.1 hd.2.1 (Nat.succ_pos n) hgrid
    calc |(X n).expectApprox v.payout (n + 1) - zhat n|
        = |((X n).expectApprox v.payout (n + 1) - val n) + (val n - zhat n)| := by
          congr 1
          ring
      _ ≤ |(X n).expectApprox v.payout (n + 1) - val n| + |val n - zhat n| :=
          abs_add_le _ _
      _ = |(X n).expectApprox v.payout (n + 1) - val n| + |(zhat n : ℝ) - val n| := by
          rw [abs_sub_comm (val n) (zhat n : ℝ)]
      _ ≤ 1 / ((n + 1 : ℕ) : ℝ) + |(zhat n : ℝ) - val n| := by gcongr
      _ = 1 / ((n : ℝ) + 1) + |(zhat n : ℝ) - val n| := by push_cast; rfl
      _ ≤ ε / 2 + ε / 2 := by gcongr
      _ = ε := by ring
  have hlim0 := hpoly.affine_provind_theory_tendsto_zero P DP hbounded hmag hworld hvalb
  unfold AsympEq at hlim0 ⊢
  have h1 : Tendsto (fun n => (X n).expect P n - zhat n) atTop (𝓝 0) := by
    refine hlim0.congr fun n => ?_
    dsimp only
    rw [hprice, sub_zero]
  have h3 := h1.add hlim
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  ring

/-! ## C. The deferred-day read-off (the right corner-quote) -/

open Classical in
/-- **The inverse of a deferral on its image**: `invDef F m` is the `k` with `F k = m`, and `0`
off the image.
Scope: schedule.
Source: none: infrastructure (the padding device of `li-diagonal`'s `padG`)
Kind: D
Fidelity: n/a -/
noncomputable def invDef (F : DeferralFunction) (m : ℕ) : ℕ :=
  if h : ∃ k, F k = m then Nat.find h else 0

/-- `invDef_apply`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem invDef_apply (F : DeferralFunction) (hf : Function.Injective F.f) (n : ℕ) :
    invDef F (F n) = n := by
  unfold invDef
  have h : ∃ k, F k = F n := ⟨n, rfl⟩
  rw [dif_pos h]
  exact hf (Nat.find_spec h)

/-- At `succDeferral` the inverse is the predecessor (`0 ↦ 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem invDef_succ (m : ℕ) : invDef succDeferral m = m - 1 := by
  cases m with
  | zero =>
    unfold invDef
    rw [dif_neg]
    rintro ⟨k, hk⟩
    exact Nat.succ_ne_zero k hk
  | succ k =>
    have := invDef_apply succDeferral (fun _ _ h => Nat.succ_injective h) k
    rw [Nat.add_sub_cancel]
    exact this

/-- **The padded ledger family along `F`**: the day-`F⁻¹(m)` ledger LUV of item `0`, read at day
`m` (the day-`0` LUV off the image — every ledger LUV is determined, so no `⊤`-padding is needed).
Scope: one-way.
Source: mandate T4(a) ("the padded ledger family")
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def padLedger (F : DeferralFunction) (m : ℕ) : LUV := ledgerLuv 0 (invDef F m)

/-- `padLedger_apply`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem padLedger_apply (F : DeferralFunction) (hf : Function.Injective F.f) (n : ℕ) :
    padLedger F (F n) = ledgerLuv 0 n := by
  unfold padLedger
  rw [invDef_apply F hf n]

/-- **The padded ledger family is e.c. at `succDeferral`** (`ledgerLuv_thresholdCodes` composed
with the day ruler `m ↦ m − 1` inside the threshold index).
Scope: one-way.
Source: mandate T4(a) (`hL` "(a) at `succ` from `ledgerLuv_thresholdCodes`")
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padLedger_codes_succ : LUV.MachineThresholdCodeSeq (padLedger succDeferral) := by
  have h := ledgerLuv_thresholdCodes 0
  unfold LUV.MachineThresholdCodeSeq at h ⊢
  have hr : UnaryRuler (fun m : ℕ => Nat.pair (m.unpair.1 - 1) m.unpair.2) :=
    (UnaryRuler.unpairFst.sub (UnaryRuler.const 1)).pair UnaryRuler.unpairSnd
  refine MachineSentenceCodes.of_eq (MachineSentenceCodes.comp h hr) fun m => ?_
  simp only [Nat.unpair_pair, padLedger, invDef_succ]

/-- **The deferred-day read-off**: `𝔼^H_{F n}(α_{0,n}) ≈ₙ a 0 n` — the reader's day-`F n`
expectation of the ledger LUV recording the day-`n` quote tends to the quote. Hypotheses: the e.c.
certificate of the padded ledger family (`hL`) and the `P`-generability of the table along the
deferral (`hz`; the cost model again). `li-quote-lane`'s L4 along `F`.
Scope: one-way; deferral `F` (injective).
Source: [[no-timely-pointwise-tower]] §2 ("read-off"); anson-013; `li-quote-lane` `readability_ofApprox` (L4); mandate T4(a)
Kind: C
Fidelity: variant: at the deferred day `F n` (the notes' day-`n` read-off is `readability` itself); plain trader class (`hz` renders the source's `𝒞_H`-readability of the quote as `P`-generability in FAF's fixed class)
Hyps: (c) `hL` (e.c. padded ledger family; (a) at `succDeferral`), (c) `hz` (generability of the table along `F`; (a) for e.c. tables such as `aAlt`); `hf` — scope: injective deferral -/
theorem readoff_deferred (T : TablePair) (F : DeferralFunction) (hf : Function.Injective F.f)
    (hL : LUV.MachineThresholdCodeSeq (padLedger F))
    (hz : PGenerableRat T.H (fun m => T.a 0 (invDef F m))) :
    (fun n => (ledgerLuv 0 n).expect T.H (F n)) ≈ₙ (fun n => (T.a 0 n : ℝ)) := by
  haveI := T.H_inductor
  have h := expect_asympEq_of_determinedVia_generable T.H T.process T.hworld (padLedger F) hL
    (fun m => (T.a 0 (invDef F m) : ℝ)) (fun m => T.determined 0 (invDef F m))
    (fun m => ⟨by exact_mod_cast (T.range 0 _).1, by exact_mod_cast (T.range 0 _).2⟩)
    (fun m => T.a 0 (invDef F m)) hz (by simp only [sub_self]; exact tendsto_const_nhds)
  unfold AsympEq at h ⊢
  have h' := h.comp F.tendsto_atTop
  refine h'.congr fun n => ?_
  simp only [Function.comp, padLedger_apply F hf n, invDef_apply F hf n]

/-! ## D. T4(a): no timely tower on the diagonal, deferred-day form -/

/-- **T4(a) (headline 3). The deferred-day tower instance fails by `½` on the diagonal**: over a
table-only pair with the certificates, for every `ε > 0` eventually
`½ − ε ≤ |𝔼^H_{F n}(𝟙 g_n) − 𝔼^H_{F n}(α_{0,n})|`. Left corner-quote: Lemma B
(`lemmaB_expect_table`, `→ s_n`); right corner-quote: the read-off (`readoff_deferred`, `→ a_n`);
Lemma 2.1 (`exact_defect`); two triangle inequalities. This is anson-014's theorem with the
index honest: at the deferred day `F n`, not at day `n` (for the day-`n` form see
`tower_fails_diagonal_sameDay`).
Scope: one-way; deferral `F` (injective).
Source: [[no-timely-pointwise-tower]] §3 (Theorem, anson-014); anson-013; root-deference-033; lean-deference-027; root-fa-037; bli-slides-016; [[deference-in-logical-induction-v6]] §4.8
Kind: C
Fidelity: variant: at the deferred day; `∀ε` form in place of `liminf`; exact ledger; both corner-quotes derived under certificates
Hyps: (c) `hR`, `hR'`, `hG` (Lemma B's cost model), (c) `hL`, `hz` (the read-off's cost model); `hf` — scope: injective deferral; all (a) on `aAlt` at `succDeferral` (`TowerWitness.lean`) -/
theorem tower_fails_diagonal (T : TablePair) (F : DeferralFunction) (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F))
    (hL : LUV.MachineThresholdCodeSeq (padLedger F))
    (hz : PGenerableRat T.H (fun m => T.a 0 (invDef F m))) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      1 / 2 - ε ≤ |T.Y F n - (ledgerLuv 0 n).expect T.H (F n)| := by
  intro ε hε
  have hB := lemmaB_expect_table T F hf hR hR' hG
  have hRd := readoff_deferred T F hf hL hz
  unfold AsympEq at hRd
  have hRd' : Tendsto (fun n => |(ledgerLuv 0 n).expect T.H (F n) - T.a 0 n|) atTop (𝓝 0) := by
    simpa using hRd.abs
  filter_upwards [hB.eventually (Iio_mem_nhds (half_pos hε)),
    hRd'.eventually (Iio_mem_nhds (half_pos hε))] with n hn1 hn2
  have hn1' : |T.Y F n - side (T.a 0) n| < ε / 2 := hn1
  have hn2' : |(ledgerLuv 0 n).expect T.H (F n) - T.a 0 n| < ε / 2 := hn2
  have h0 := exact_defect T n
  have t1 : |(T.a 0 n : ℝ) - side (T.a 0) n| ≤
      |(T.a 0 n : ℝ) - (ledgerLuv 0 n).expect T.H (F n)| +
        |(ledgerLuv 0 n).expect T.H (F n) - side (T.a 0) n| := abs_sub_le _ _ _
  have t2 : |(ledgerLuv 0 n).expect T.H (F n) - side (T.a 0) n| ≤
      |(ledgerLuv 0 n).expect T.H (F n) - T.Y F n| + |T.Y F n - side (T.a 0) n| :=
    abs_sub_le _ _ _
  have t3 : |(ledgerLuv 0 n).expect T.H (F n) - T.Y F n| =
      |T.Y F n - (ledgerLuv 0 n).expect T.H (F n)| := abs_sub_comm _ _
  have t4 : |(T.a 0 n : ℝ) - (ledgerLuv 0 n).expect T.H (F n)| =
      |(ledgerLuv 0 n).expect T.H (F n) - T.a 0 n| := abs_sub_comm _ _
  linarith

/-- **T4(a) as `¬ Tower`**: the deferred-day tower instance does not hold on the diagonal, over
FAF's `≈ₙ`.
Scope: one-way; deferral `F` (injective).
Source: [[no-timely-pointwise-tower]] §1, §3; anson-014
Kind: C
Fidelity: variant: at the deferred day
Hyps: (c) as `tower_fails_diagonal`; `hf` — scope: injective deferral -/
theorem not_tower_diagonal (T : TablePair) (F : DeferralFunction) (hf : Function.Injective F.f)
    (hR : MachineSentenceCodes (padTrueSide T.a F))
    (hR' : MachineSentenceCodes (padFalseSide T.a F))
    (hG : MachineSentenceCodes (padG F))
    (hL : LUV.MachineThresholdCodeSeq (padLedger F))
    (hz : PGenerableRat T.H (fun m => T.a 0 (invDef F m))) :
    ¬ (T.Y F ≈ₙ fun n => (ledgerLuv 0 n).expect T.H (F n)) := by
  intro h
  unfold AsympEq at h
  have h1 : Tendsto (fun n => |T.Y F n - (ledgerLuv 0 n).expect T.H (F n)|) atTop (𝓝 0) := by
    simpa using h.abs
  have h2 := h1.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have h3 := tower_fails_diagonal T F hf hR hR' hG hL hz (1 / 4) (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := (h3.and h2).exists
  have hn2' : |T.Y F n - (ledgerLuv 0 n).expect T.H (F n)| < 1 / 4 := hn2
  linarith

/-! ## E. T4(b): the same-day form, with the day-`n` certificates -/

/-- **Lemma B at day `n`** (no deferral): `|H_n(g_n) − s_n| → 0`, by `lic_provind` on the
unpadded side families `trueSide a`, `falseSide a`. Needs their e.c. certificates and **no
publication hypothesis** (completed-theory truth; F-Regimes).
Scope: one-way.
Source: [[no-timely-pointwise-tower]] §3 (the day-`n` convergence the proof asserts); anson-014; mandate T4(b)
Kind: C
Fidelity: exact (price reading at day `n`)
Hyps: (c) `hR`, `hR'` — the day-`n` cost model (e.c. side families) -/
theorem lemmaB_sameDay (T : TablePair)
    (hR : MachineSentenceCodes (trueSide T.a)) (hR' : MachineSentenceCodes (falseSide T.a)) :
    Tendsto (fun n => |T.H n (gDiag n) - side (T.a 0) n|) atTop (𝓝 0) := by
  haveI := T.H_inductor
  have hboth := lic_provind T.H T.process (trueSide T.a) (falseSide T.a) hR hR'
    (fun n v hv => trueSide_holds_table T.DPH T.a T.e n v hv)
    (fun n v hv => falseSide_refuted_table T.DPH T.a T.e n v hv) T.hworld
  have h1 : Tendsto (fun n => T.H n (trueSide T.a n) - 1) atTop (𝓝 0) := hboth.1
  have h0 : Tendsto (fun n => T.H n (falseSide T.a n) - 0) atTop (𝓝 0) := hboth.2
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1' := (Metric.tendsto_nhds.1 h1) ε hε
  have h0' := (Metric.tendsto_nhds.1 h0) ε hε
  filter_upwards [h1', h0'] with n hn1 hn0
  rw [Real.dist_eq, sub_zero] at hn1 hn0 ⊢
  rw [abs_abs]
  unfold trueSide at hn1
  unfold falseSide at hn0
  by_cases h : T.a 0 n ≤ 1 / 2
  · rw [if_pos h] at hn1
    rw [(side_eq_one_iff _ _).2 h]
    exact hn1
  · rw [if_neg h] at hn0
    rw [(side_eq_zero_iff _ _).2 (not_le.mp h)]
    simpa using hn0

/-- **Lemma B at day `n`, expectation form**: `|𝔼^H_n(𝟙 g_n) − s_n| → 0`; the `thm:ei` bridge is
on `gDiag` itself, whose certificate is `li-diagonal`'s `gDiag_codes` (a).
Scope: one-way.
Source: anson-014; mandate T4(b)
Kind: C
Fidelity: exact (expectation reading at day `n`)
Hyps: (c) `hR`, `hR'` — the day-`n` cost model -/
theorem lemmaB_expect_sameDay (T : TablePair)
    (hR : MachineSentenceCodes (trueSide T.a)) (hR' : MachineSentenceCodes (falseSide T.a)) :
    Tendsto (fun n => |(LUV.indicatorOf (gDiag n)).expect T.H n - side (T.a 0) n|)
      atTop (𝓝 0) := by
  haveI := T.H_inductor
  have hei := lic_expectation_indicator T.H T.process gDiag gDiag_codes
    (fun n => LUV.indicatorOf (gDiag n)) (LUV.indicatorOf_machineThresholdCodeSeq gDiag_codes)
    T.hworld (fun n => LUV.indicatorOf_isIndicator _ _)
  unfold AsympEq at hei
  have hB := lemmaB_sameDay T hR hR'
  have hsum : Tendsto (fun n =>
      |(LUV.indicatorOf (gDiag n)).expect T.H n - T.H n (gDiag n)| +
        |T.H n (gDiag n) - side (T.a 0) n|) atTop (𝓝 0) := by
    simpa using hei.abs.add hB
  refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hsum
  exact abs_sub_le _ _ _

/-- **T4(b). The same-day tower instance fails by `½` on the diagonal** — the notes' literal
`𝔼^H_n(g_n) ≈ₙ 𝔼^H_n(⌜a_n⌝)`: for every `ε > 0` eventually
`½ − ε ≤ |𝔼^H_n(𝟙 g_n) − 𝔼^H_n(α_{0,n})|`. Right corner-quote: `li-quote-lane`'s `readability`
(L4 at day `n`, under `hz`, the day-`n` generability of the table — named `hz` as in
`tower_fails_diagonal`, where `hL` is the ledger family's *codes* certificate; repair round 1,
audit N4). **No `sameDay` publication hypothesis** (module docstring, F-IndexBookkeeping).
Scope: one-way.
Source: [[no-timely-pointwise-tower]] §3 (anson-014, the day-`n` statement); anson-013's index flag; mandate T4(b)
Kind: C
Fidelity: exact (the notes' day-`n` indices), under the day-`n` certificates
Hyps: (c) `hR`, `hR'` (day-`n` side certificates), (c) `hz` (`P`-generability of the table at day `n`, `li-quote-lane`'s L4 hypothesis) -/
theorem tower_fails_diagonal_sameDay (T : TablePair)
    (hR : MachineSentenceCodes (trueSide T.a)) (hR' : MachineSentenceCodes (falseSide T.a))
    (hz : PGenerableRat T.H (fun n => T.a 0 n)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      1 / 2 - ε ≤ |(LUV.indicatorOf (gDiag n)).expect T.H n - (ledgerLuv 0 n).expect T.H n| := by
  intro ε hε
  haveI := T.H_inductor
  have hB := lemmaB_expect_sameDay T hR hR'
  have hRd := readability T.H T.DPH T.a T.e T.hworld T.range 0 hz
  unfold AsympEq at hRd
  have hRd' : Tendsto (fun n => |(ledgerLuv 0 n).expect T.H n - T.a 0 n|) atTop (𝓝 0) := by
    simpa using hRd.abs
  filter_upwards [hB.eventually (Iio_mem_nhds (half_pos hε)),
    hRd'.eventually (Iio_mem_nhds (half_pos hε))] with n hn1 hn2
  have hn1' : |(LUV.indicatorOf (gDiag n)).expect T.H n - side (T.a 0) n| < ε / 2 := hn1
  have hn2' : |(ledgerLuv 0 n).expect T.H n - T.a 0 n| < ε / 2 := hn2
  have h0 := exact_defect T n
  have t1 : |(T.a 0 n : ℝ) - side (T.a 0) n| ≤
      |(T.a 0 n : ℝ) - (ledgerLuv 0 n).expect T.H n| +
        |(ledgerLuv 0 n).expect T.H n - side (T.a 0) n| := abs_sub_le _ _ _
  have t2 : |(ledgerLuv 0 n).expect T.H n - side (T.a 0) n| ≤
      |(ledgerLuv 0 n).expect T.H n - (LUV.indicatorOf (gDiag n)).expect T.H n| +
        |(LUV.indicatorOf (gDiag n)).expect T.H n - side (T.a 0) n| := abs_sub_le _ _ _
  have t3 : |(ledgerLuv 0 n).expect T.H n - (LUV.indicatorOf (gDiag n)).expect T.H n| =
      |(LUV.indicatorOf (gDiag n)).expect T.H n - (ledgerLuv 0 n).expect T.H n| :=
    abs_sub_comm _ _
  have t4 : |(T.a 0 n : ℝ) - (ledgerLuv 0 n).expect T.H n| =
      |(ledgerLuv 0 n).expect T.H n - T.a 0 n| := abs_sub_comm _ _
  linarith

end Cleanroom.Deference.DefObstruction
