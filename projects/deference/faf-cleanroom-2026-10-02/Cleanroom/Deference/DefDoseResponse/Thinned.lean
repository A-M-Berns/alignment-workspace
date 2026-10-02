import Cleanroom.Deference.DefDoseResponse.Defs
import Cleanroom.Fa.FaForcingTrader.TheoremSS
import LogicalInduction.Construction.Quotation.DeferralFibre

/-!
# `def-dose-response` · Thinned: thinned forcing at an e.c. exposure indicator (T1, D6)

The note's T1 (§5): forced trust survives the design on the exposed days. Over
`fa-forcing-trader`'s setting (one-way, a fixed `X`, window-disjoint schedule `d`, the quote
package `pkg` and the certificate `CA`), the **thinned gate** (D6) is
`G_n := c_n · 1[n ∈ im d] · Ind_δ(a_n − t)` with `C : ℕ → EF` an **e.c. exposure indicator** — a
`PGenerableWeighting` with `{0,1}` denotation on `A` (`fa-forcing-trader`'s `scheduleIndicator`
and `fa-theorem-a`'s `evenDays` are the models: `EF.const` of a poly-time computable bit). Then
`G` is `A`-generable (`PGenerableWeighting.mul`), supported on `im d`, and Theorem SS applies
verbatim:

* `thinned_agreement`: the `G`-weighted average of `a_n − 𝔼^H_n(X_n)` tends to `0`
  (`theoremSS_fullLimit_general_oneCert`, one application);
* **`thinned_forcing_gated`**: the `G`-weighted average of `𝔼^H_n(X_n)` is eventually
  `≥ t − ρ` for every `ρ > 0` (`schedThresholdAboveEv_of_weightedApprox` on the gate's positivity);
* `thinned_forcing_limitPoint`: the limit-point grade with no certificate
  (`theoremSS_limitPoint_general`).

**Where the sparsity lives.** `hwd : WindowDisjoint f d` is *consumed* — `hSideBridge`'s
one-open-position accounting inside Theorem SS needs it — and it is **unsatisfiable** for an
identity-like schedule: `WindowDisjoint f d` asks `f (d k) < d (k+1)`, which at `d k = k` would
say `f k < k + 1` against `k < f k` (and `id` is not even a `DeferralFunction`, lacking `lt` and
`graph_fp`). So the statement type-checks but has no instance at `d = id`. `WindowDisjoint` is
marginally stronger than the note's `f`-sparsity (disjoint windows `[n+1, f n]` ⟺ `f n ≤ n'`):
the boundary `f (d k) = d (k+1)` is excluded — inherited from `fa-forcing-trader`. This is
exactly where the zip's `thinned_forcing` was sparsity-blind (zip AUDIT §3.1): there the schedule
was an `IsIndicator S` with `S ≡ 1` allowed, and the open unrestricted claim was an instance.

**Hypotheses, copied from `fa-forcing-trader`** (its ledger's convention): (c) `pkg.reflected`
(Σ₁-completeness of `Γ_A` about `H`, `li-quote-lane`); (c) `hL : LegibleOn H (G·A)` — the gate
must be a legal feature of `H`'s market. At the thinned gate `hL` *reduces* to readability of
the exposure table by the arm: by `thinnedGate_denote_recorded`, `G_n = 1[n ∈ im d] · Ind_δ(c_n a_n − t)`
for `t ≥ 0` — a ramp of the recorded item-`0` number — so `hL` is `li-quote-lane`'s
`ledgerRamp` + `readability_ofApprox`'s `hz` on the exposure table, the same (c) as
`fa-forcing-trader`'s T11, **not a new one**; it is not discharged here by
`legibleOn_of_pgenerableRat` at a constant table (that would be N− and is not claimed). (b) `CA`:
the corrected 4.8.16 timing certificate, OPEN in `fa-forcing-trader`
(`exists_gridCertificate_of_marketComputation`). The `A`-side input is `quoteSide_fullLimit` =
FAF's `wubexp` *with* the support condition — anson-2-027's re-founding; the note's "conservative
reading carrying the support condition" is FAF's PE2 (findings F3).

**Cor T1.1 (design non-interference)**: at `C ≡ EF.const 1` the thinned gate denotes as
`schedGate` (`thinnedGate_one_denote`) and T1 *is* `fa-forcing-trader`'s T6′/T7′ — a definitional
lemma (anson-2-030), `thinned_forcing_gated_one`.

**F1, recorded, not worked around**: the note's T1 proof hands `A` the weighting `w^S` with
"every factor in `A`'s production feedback"; but `PGenerableWeighting` has `rank_le : rank ≤ n`,
and the design's commit-before-coin makes the day-`n` coin day-`(n+σ)` information for `A`. A
pseudorandom coin relative to `A` is by definition not a rank-`n` feature of `A`. So T1 is proved
here for an e.c. exposure indicator, where it is a corollary of Theorem SS; the pseudorandom-coin
reading is ill-typed as a `PGenerableWeighting` of `A` (findings F1; the (β) design change is
recorded in `Open.lean`).
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Fa.FaTheoremA
  Cleanroom.Fa.FaForcingTrader Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.DefLattice
open Filter Topology

/-! ## D6 — the thinned gate -/

/-- **An e.c. exposure indicator** on `A`'s market: a `PGenerableWeighting` whose denotation at
`A` is `0` or `1` on every day. `fa-forcing-trader`'s `scheduleIndicator d` and `fa-theorem-a`'s
`evenDays` are instances, and `coinIndicator c` (below) is the design's reading — `EF.const` of a
computable bit, under a `MachineSpliceStream` certificate. **Broader than "e.c. coin"**: any
`A`-generable `{0,1}` feature qualifies, including one that reads `A`'s own day-`n` prices
(exposure decided by the quote's content); T1 below is correspondingly *stronger* than its
"e.c. exposure indicator" wording suggests (fidelity audit r1, N5). In every case the indicator is
an `A`-feature of rank `≤ n`, which is the regime change from the note's post-commit pseudorandom
coin (F1).
Source: mandate D6 ("`C : ℕ → EF` a `{0,1}`-valued `PGenerableWeighting`"); [[dose-response]] §5 (T1's `c_n`)
Kind: D
Fidelity: variant: an e.c. indicator in place of the note's pseudorandom coin (F1)
Hyps: n/a -/
structure ExposureIndicator (A : History) (C : ℕ → EF) : Prop where
  /-- The indicator is a legal feature progression of `A`'s market. -/
  pgen : PGenerableWeighting C
  /-- Its denotation at `A` is a bit. -/
  bool : ∀ n, (C n).denote A = 0 ∨ (C n).denote A = 1

/-- **The thinned gate** (D6): `c_n · 1[n ∈ im d] · Ind_δ(a_n − t)` as an `EF`, the product of the
exposure indicator with `fa-forcing-trader`'s `schedGate`.
Source: [[dose-response]] §5 ("the thinned gate `g_n := c_n Ind_δ(a_n(X) − t)`", on the schedule `S`); mandate D6
Kind: D
Fidelity: exact (the schedule as a `DeferralFunction`, as `fa-forcing-trader`)
Hyps: n/a -/
def thinnedGate (C : ℕ → EF) (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (n : ℕ) : EF :=
  EF.mul (C n) (schedGate Y d t δ n)

/-- The thinned gate is `A`-generable when the indicator and the quote family are
(`PGenerableWeighting.mul` on `schedGate_pgenerable`).
Source: [[dose-response]] §5 ("`w^S` is `A`-generable"); mandate T1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem thinnedGate_pgenerable {C : ℕ → EF} (hC : PGenerableWeighting C) {Y : ℕ → LUV}
    (hY : LUV.MachineThresholdCodeSeq Y) (d : DeferralFunction) (t δ : ℚ) :
    PGenerableWeighting (thinnedGate C Y d t δ) :=
  PGenerableWeighting.mul hC (schedGate_pgenerable Y hY d t δ)

/-- The thinned gate denotes `c_n · (1[n ∈ im d] · Ind_δ(a_n − t))`.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem thinnedGate_denote (C : ℕ → EF) (Y : ℕ → LUV) (d : DeferralFunction) (t : ℚ) {δ : ℚ}
    (hδ : 0 < δ) (A : History) (n : ℕ) :
    (thinnedGate C Y d t δ n).denote A =
      (C n).denote A * (schedInd d n * rampAbove δ t (quoteSeq Y A n)) := by
  unfold thinnedGate
  rw [EF.denote_mul, Pi.mul_apply, schedGate_denote Y d t hδ]

/-- The thinned gate is supported on the schedule.
Source: [[dose-response]] §5 ("`supp(w^S) ⊆ S`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem thinnedGate_supported (C : ℕ → EF) (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ)
    (A : History) : WeightingSupportedOnDeferralImage (thinnedGate C Y d t δ) A d := by
  intro n hn
  unfold thinnedGate at hn
  rw [EF.denote_mul, Pi.mul_apply] at hn
  exact schedGate_supported Y d t δ A n (right_ne_zero_of_mul hn)

/-- A positive thinned gate means: exposed, scheduled, quote above the threshold.
Source: [[dose-response]] §5 ("`w_n > 0 ⇒ c_n = 1, a_n(X) > t`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem thinnedGate_pos_imp {C : ℕ → EF} {A : History} (hC : ExposureIndicator A C) (Y : ℕ → LUV)
    (d : DeferralFunction) (t : ℚ) {δ : ℚ} (hδ : 0 < δ) (n : ℕ)
    (h : 0 < (thinnedGate C Y d t δ n).denote A) :
    (C n).denote A = 1 ∧ (∃ k, d.f k = n) ∧ (t : ℝ) < quoteSeq Y A n := by
  unfold thinnedGate at h
  rw [EF.denote_mul, Pi.mul_apply] at h
  rcases hC.bool n with h0 | h1
  · rw [h0, zero_mul] at h
    exact absurd h (lt_irrefl 0)
  · rw [h1, one_mul] at h
    exact ⟨h1, (schedGate_pos_iff Y d t hδ A n).mp h⟩

/-- **The D6 ramp identity**: for a `{0,1}` bit `c` and `t ≥ 0`, `c · Ind_δ(a − t) = Ind_δ(c·a − t)`
— the thinned ramp is the ramp of the *recorded* number `c·a`.
Source: mandate D6 ("`c_n · Ind_δ(a_n − t) = Ind_δ(c_n a_n − t)`"); [[dose-response]] §5 ("computed from the recorded pair `(c_n, c_n a_n(X))`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem exposure_ramp_eq {c : ℝ} (hc : c = 0 ∨ c = 1) {t : ℚ} (ht : 0 ≤ t) {δ : ℚ} (hδ : 0 < δ)
    (a : ℝ) : c * rampAbove δ t a = rampAbove δ t (c * a) := by
  rcases hc with rfl | rfl
  · rw [zero_mul, zero_mul]
    unfold rampAbove ctsInd
    have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
    have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
    have : (0 - (t : ℝ)) / (δ : ℝ) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    rw [max_eq_left this, min_eq_right zero_le_one]
  · rw [one_mul, one_mul]

/-- **The thinned gate reads the recorded number**: for `t ≥ 0`, `G_n = 1[n ∈ im d] · Ind_δ(c_n a_n − t)`.
This is what makes the gate legible to an arm that sees only `c_n a_n` — `hL` at the thinned gate
is readability of the exposure table (module docstring).
Source: mandate T1 fake-success trap (i); [[dose-response]] §5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem thinnedGate_denote_recorded {C : ℕ → EF} {A : History} (hC : ExposureIndicator A C)
    (Y : ℕ → LUV) (d : DeferralFunction) {t : ℚ} (ht : 0 ≤ t) {δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    (thinnedGate C Y d t δ n).denote A =
      schedInd d n * rampAbove δ t ((C n).denote A * quoteSeq Y A n) := by
  rw [thinnedGate_denote C Y d t hδ A n, ← exposure_ramp_eq (hC.bool n) ht hδ]
  ring

/-! ## T1 — thinned forcing -/

section T1

variable {H A : History} {DPA DPH : DeductiveProcess} [IsLogicalInductor A DPA]
  [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}

/-- **T1, the agreement form.** Over `fa-forcing-trader`'s setting with the thinned gate `G`
(`C` an `A`-generable indicator, `hL` the legibility of `G` on `H`, `G` divergent on `A`, `CA` the
certificate): the `G`-weighted average of `a_n − 𝔼^H_n(X_n)` tends to `0`. One application of
`theoremSS_fullLimit_general_oneCert`. Scope: one-way; e.c. exposure indicator, window-disjoint
schedule, fixed `X`.
Source: [[dose-response]] §5 T1 (the display (II^S) and the trader step); anson-053; anson-2-026; anson-2-027
Kind: C
Fidelity: exact (the full-limit, two-sided agreement form)
Hyps: (c) `pkg.reflected`; (c) `hL`; (b) `CA` — inherited verbatim from `fa-forcing-trader`'s `theoremSS_fullLimit_oneCert` -/
theorem thinned_agreement (pkg : CrossQuotePackage H DPA f X Y)
    (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) {C : ℕ → EF} (hC : PGenerableWeighting C)
    (t δ : ℚ) (hL : LegibleOn H (fun n => (thinnedGate C Y d t δ n).denote A))
    (hdiv : DivergentWeighting (thinnedGate C Y d t δ) A)
    (CA : QuoteCertificate A DPA Y hworldA d) :
    WeightedApprox (fun n => (thinnedGate C Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n) :=
  theoremSS_fullLimit_general_oneCert pkg hcode hworldA hworldH hval hwd
    (thinnedGate_pgenerable hC pkg.quote_codes d t δ) (thinnedGate_supported C Y d t δ A) hL hdiv
    CA

/-- **T1, thinned forcing, gated classwise form (headline).** On the thinned gate the arm's
present credence averages to `≥ t − ρ` eventually, for every `ρ > 0`: the note's "Hence" clause.
From `thinned_agreement` and the gate's no-false-positives (`thinnedGate_pos_imp`). Scope:
one-way; e.c. exposure indicator, window-disjoint schedule, fixed `X`. `t ∈ [0,1]` is the
meaningful range: at `t < 0` the conclusion `≥ t − ρ` is trivial for a `[0,1]`-valued credence,
at `t > 1` the ramp `Ind_δ(a − t)` vanishes on `[0,1]`-valued quotes and `hdiv` is unsatisfiable
(adversarial audit r2 N5; inherited from `fa-forcing-trader`).
Source: [[dose-response]] §5 T1 ("gated classwise form … `≥ t − ε − o(1)`"); anson-053; anson-2-026; anson-2-027
Kind: C
Fidelity: variant: averaged along the gate, scheduled, eventually (as `fa-forcing-trader`'s T7′), on the two-factor gate `c·1[im d]·Ind_δ(a − t)` rather than the three-factor violation weight; **stronger** in one clause: `≥ t − ρ` eventually for *every* `ρ > 0`, where the note's `≥ t − ε − o(1)` keeps the fixed `ε` of its violation weight (fidelity audit r2 N3)
Hyps: (c) `pkg.reflected`; (c) `hL`; (b) `CA` — inherited from `fa-forcing-trader` -/
theorem thinned_forcing_gated (pkg : CrossQuotePackage H DPA f X Y)
    (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) {C : ℕ → EF} (hC : ExposureIndicator A C)
    (t : ℚ) {δ : ℚ} (hδ : 0 < δ) (hL : LegibleOn H (fun n => (thinnedGate C Y d t δ n).denote A))
    (hdiv : DivergentWeighting (thinnedGate C Y d t δ) A)
    (CA : QuoteCertificate A DPA Y hworldA d) :
    SchedThresholdAboveEv (fun n => (thinnedGate C Y d t δ n).denote A)
      (fun n => (X n).expect H n) t :=
  schedThresholdAboveEv_of_weightedApprox (fun i => (hdiv.1 i).1) hdiv.2
    (fun i hi => (thinnedGate_pos_imp hC Y d t hδ i hi).2.2.le)
    (thinned_agreement pkg hcode hworldA hworldH hval hwd hC.pgen t δ hL hdiv CA)

/-- **T1 at the limit-point grade, no certificate**: `0` is a limit point of the thinned-gate
weighted bias of `a_n` against `𝔼^H_n(X_n)` (`theoremSS_limitPoint_general`).
Source: [[dose-response]] §5 T1; `fa-forcing-trader` T6
Kind: C
Fidelity: weaker: limit point
Hyps: (c) `pkg.reflected`; (c) `hL` -/
theorem thinned_forcing_limitPoint (pkg : CrossQuotePackage H DPA f X Y)
    (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) {C : ℕ → EF} (hC : PGenerableWeighting C)
    (t δ : ℚ) (hL : LegibleOn H (fun n => (thinnedGate C Y d t δ n).denote A))
    (hdiv : DivergentWeighting (thinnedGate C Y d t δ) A) :
    HasLimitPoint (weightedBias (fun n => (thinnedGate C Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n)) 0 :=
  theoremSS_limitPoint_general pkg hcode hworldA hworldH hval hwd
    (thinnedGate_pgenerable hC pkg.quote_codes d t δ)
    (fun n hn => thinnedGate_supported C Y d t δ A n hn) hL hdiv

end T1

/-! ## Cor T1.1 — design non-interference -/

/-- The undosed indicator `c ≡ 1` is an exposure indicator on every market.
Source: [[dose-response]] §5 ("the undosed case `c ≡ 1` is allowed")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem exposureIndicator_one (A : History) : ExposureIndicator A (fun _ => EF.const 1) :=
  ⟨pgenerableWeighting_const 1, fun _ => Or.inr (by simp)⟩

/-! ## The design's coin as a feature: `coinIndicator` -/

/-- **The design's coin as a feature**: `EF.const (if c n then 1 else 0)` — the `c : ℕ → Bool` of
T6/T2's arms read as a `{0,1}` feature progression, so that T1's exposure indicator and the arms'
coin are the same object (fidelity audit r1, N4: the two halves were disconnected).
Source: mandate D6 ("the e.c. coin as a feature"); [[dose-response]] §5 (T1's `c_n`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def coinIndicator (c : ℕ → Bool) (n : ℕ) : EF := EF.const (if c n then 1 else 0)

/-- `coinIndicator c` denotes the coin's bit in every market.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem coinIndicator_denote (c : ℕ → Bool) (A : History) (n : ℕ) :
    (coinIndicator c n).denote A = if c n then 1 else 0 := by
  unfold coinIndicator
  split_ifs <;> simp

/-- **A coin with a machine certificate is an exposure indicator** on every market: the
`MachineSpliceStream` certificate of the constant stream `n ↦ (if c n then 1 else 0)` is FAF's
e.c. requirement on the coin (a poly-time `c`; `fa-theorem-a`'s `evenDays_pgenerable` builds one
for the parity coin by `MachineSpliceStream.ifZero`), and the rank is `0`. This is the lemma that
feeds a T6/T2 coin `c` into T1's `thinnedGate (coinIndicator c)`.
Source: mandate D6; [[dose-response]] §5 ("`c_n` … e.c."); fidelity audit r1 N4
Kind: L
Fidelity: exact (the certificate is the hypothesis; no poly-time bound is asserted of a bare `c`)
Hyps: hypothesis: the `MachineSpliceStream` certificate `hc` — FAF's e.c. requirement on the coin, assumed, not (a)-derived (adversarial audit r2 N6) -/
theorem coinIndicator_exposureIndicator {c : ℕ → Bool}
    (hc : MachineSpliceStream (fun n => (coinIndicator c n).serialize)) (A : History) :
    ExposureIndicator A (coinIndicator c) :=
  ⟨⟨hc, fun n => by simp [coinIndicator], fun n ρ V => by simp [coinIndicator, EF.denote]⟩,
    fun n => by
      rw [coinIndicator_denote]
      split_ifs <;> simp⟩

/-- **Cor T1.1, design non-interference**: at `c ≡ 1` the thinned gate denotes as
`fa-forcing-trader`'s `schedGate` on every market — T1 at dose `1` *is* Theorem SS's scheduled
gate form, by definition.
Source: [[dose-response]] §5 Cor T1.1 ("At `p_1 = 1`, `c ≡ 1`, T1 is `faithful-acceleration.md` §5 verbatim"); anson-2-030
Kind: L
Fidelity: exact (a definitional lemma, not a theorem — zip AUDIT §3.5)
Hyps: (a) none -/
theorem thinnedGate_one_denote (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (A : History)
    (n : ℕ) :
    (thinnedGate (fun _ => EF.const 1) Y d t δ n).denote A = (schedGate Y d t δ n).denote A := by
  unfold thinnedGate
  rw [EF.denote_mul, Pi.mul_apply, EF.denote_const]
  simp

/-- **Cor T1.1 as a theorem instance**: T1 at `c ≡ 1` is `fa-forcing-trader`'s
`schedThresholdAboveEv_oneCert` restated over the thinned gate.
Source: [[dose-response]] §5 Cor T1.1; anson-2-030
Kind: L
Fidelity: exact
Hyps: (c) `pkg.reflected`; (c) `hL`; (b) `CA` — inherited -/
theorem thinned_forcing_gated_one {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGate Y d t δ) A)
    (CA : QuoteCertificate A DPA Y hworldA d) :
    SchedThresholdAboveEv (fun n => (thinnedGate (fun _ => EF.const 1) Y d t δ n).denote A)
      (fun n => (X n).expect H n) t := by
  have h := schedThresholdAboveEv_oneCert pkg hcode hworldA hworldH hval hwd t hδ hL hdiv CA
  have heq : (fun n => (thinnedGate (fun _ => EF.const 1) Y d t δ n).denote A) =
      fun n => (schedGate Y d t δ n).denote A := funext (thinnedGate_one_denote Y d t δ A)
  rw [heq]
  exact h

end Cleanroom.Deference.DefDoseResponse
