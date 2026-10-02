import Cleanroom.Corrigibility.CorrLiShutdown.WitnessesA
import Cleanroom.Corrigibility.CorrLiShutdown.Identity
import Cleanroom.Corrigibility.CorrLiShutdown.Reports
import LogicalInduction.Construction.Statistics.FeedbackTruth

/-!
# `corr-li-shutdown` — WitnessesB: full-package witnesses for the feedback rows, T5(⇐), T1(b)

Audit round 1 (fidelity B2, adversarial B1, N3, N4): the feedback rows T4(c)(d) named a witness
that does not inhabit them (FAF's `ordinaryFeedbackTruthComputation` is typed at the constant
truth `1`; the support premise `h0` at `succDeferral` was undischarged on every shipped pair),
T5(⇐) shipped no witness, and the T1(b) witness cell named an instantiation that was not built.
This file supplies them, all **N−** on the always-press pairs of `WitnessesA.lean`:

* `dropDayZero W := n ↦ const (if n = 0 then 0 else 1) · W n` — a weighting that vanishes on day
  `0` *by construction*, hence is supported on the image of `succDeferral`; its generability is
  a theorem (`dropDayZero_pgenerable`: one `serialize_const_write` of a two-valued digit stream
  from `UnaryRuler.ifZero`, times the given certificate), divergence transfers
  (`dropDayZero_divergent`), and its support lies inside the original's.
* Feedback computations for the constant streams: FAF's ordinary computation transported to
  the always-wrong stream (`constTrueFeedback`), and a zero computation built here for the
  never-wrong stream (`zeroFeedbackTruthComputation`, `constFalseFeedback`).
* `witnessB_defiance_feedback`, `witnessB_compliance_feedback`, `witnessB_hybrid_feedback`: the
  full packages of `defiance_calibrated_feedback_class`, `compliance_calibrated_feedback_class`
  and `hybrid_credence_iff_realized_feedback` at `v := dropDayZero u^def` (resp. `u^com`),
  `f := succDeferral`, on the never-wrong (resp. always-wrong) pair.
* `witnessB_mostly_false`: T5(⇐)'s full package on the never-wrong pair with `v := u^def`,
  `η := 4δ` — the circular instance the theorem's docstring warns about; it shows the package is
  consistent, not that the theorem has content there.
* `witnessB_toyX_expect_asymp`: T1(b) on the always-press pair.
* T12(a) (`report_trust`) inhabited (audit r1 adversarial N7): on the always-press pair, where
  the report item *is* the press (`ofTable` puts one table on every item), and on
  `twoTablePair y r` (`ShutdownPair.ofTables`: item `0` the always-press, item `1` the board's
  report stream `r`, any primitive recursive Boolean stream, independent of the verdict stream
  `y`), where `reportTruth = truthR r` (`twoTablePair_reportTruth`) — so the agent is
  recurringly unbiased about the *reports* whether `r` tracks the world (`r = y`), contradicts
  it, or ignores it: finding F8 (the report → truth link is not forced) made concrete. The
  weighting is the constant `1` (`constOneW_pgenerable`, `constOne_divergent`).

Grade N− throughout (constant verdicts; `thm:provind` alone drives the credences; the realized
wrongness on the support is `0`, resp. `1`). The feedback computations here are at `succDeferral`,
the collapsed regime of F17 (`Collision.lean`): these witnesses inhabit the packages, and the
packages' content at `succ` is exactly what F17 says it is. Probes of record:
`run/wp/corr-li-shutdown/audit-r1-probes/{FeedbackPackage,MostlyFalseInhabited}.lean`.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LogicalInduction.FeedbackTruth Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiPseudorandom
open Filter Topology

/-! ## A. A weighting that vanishes on day `0` by construction -/

/-- The day-`0` mask `const (if n = 0 then 0 else 1)`.
Source: none: infrastructure (audit r1 adversarial B1, fix (b))
Kind: D
Fidelity: n/a -/
def dayZeroMask (n : ℕ) : EF := EF.const (if n = 0 then 0 else 1)

/-- The digit stream of the day-`0` mask is machine-metered (`UnaryRuler.ifZero` on the day).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dayZeroMask_digits :
    MachineDigits (fun n => Encodable.encode (if n = 0 then (0 : ℚ) else 1)) := by
  have h : UnaryRuler (fun n => if n = 0 then Encodable.encode (0 : ℚ)
      else Encodable.encode (1 : ℚ)) :=
    UnaryRuler.ifZero UnaryRuler.id (UnaryRuler.const _) (UnaryRuler.const _)
  exact (MachineDigits.ofUnaryRuler h).of_eq (fun n => by split_ifs <;> rfl)

/-- **`dropDayZero W`**: the weighting `W` with its day-`0` weight replaced by `0` (as a feature:
the mask times `W n`), so that it is supported on the image of `succDeferral` by construction.
Source: none: infrastructure (audit r1 adversarial B1, fix (b))
Kind: D
Fidelity: n/a -/
def dropDayZero (W : ℕ → EF) (n : ℕ) : EF := EF.mul (dayZeroMask n) (W n)

/-- **`dropDayZero` preserves P-generability** — a theorem: the mask's stream is one
`serialize_const_write`, the product one `serialize_mul`.
Source: none: infrastructure
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem dropDayZero_pgenerable {W : ℕ → EF} (hW : PGenerableWeighting W) :
    PGenerableWeighting (dropDayZero W) where
  polySeg := (MachineSpliceStream.serialize_mul
    (MachineSpliceStream.serialize_const_write dayZeroMask_digits) hW.polySeg).of_eq
    (fun _ => rfl)
  rank_le n := by
    show (EF.mul (EF.const _) (W n)).rank ≤ n
    simpa using hW.rank_le n
  closed n ρ V := by
    show (EF.mul (EF.const _) (W n)).denoteWith ρ V = (EF.mul (EF.const _) (W n)).denote V
    simp [hW.closed n ρ V]

/-- `dropDayZero W` denotes `0` on day `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dropDayZero_denote_zero (W : ℕ → EF) (P : History) : (dropDayZero W 0).denote P = 0 := by
  simp [dropDayZero, dayZeroMask]

/-- `dropDayZero W` denotes `W (n+1)` on day `n + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dropDayZero_denote_succ (W : ℕ → EF) (P : History) (n : ℕ) :
    (dropDayZero W (n + 1)).denote P = (W (n + 1)).denote P := by
  simp [dropDayZero, dayZeroMask]

/-- A positive `dropDayZero` weight is a positive `W` weight (the support shrinks).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dropDayZero_pos_imp {W : ℕ → EF} {P : History} {n : ℕ}
    (h : 0 < (dropDayZero W n).denote P) : 0 < (W n).denote P := by
  cases n with
  | zero => rw [dropDayZero_denote_zero] at h; exact absurd h (lt_irrefl 0)
  | succ k => rwa [dropDayZero_denote_succ] at h

/-- `prefixSum (dropDayZero W) N = prefixSum W N − W 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_dropDayZero (W : ℕ → EF) (P : History) (N : ℕ) :
    prefixSum (fun i => (dropDayZero W i).denote P) N =
      prefixSum (fun i => (W i).denote P) N - (W 0).denote P := by
  unfold prefixSum
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun i => (W i).denote P)]
  simp only [dropDayZero_denote_succ, dropDayZero_denote_zero]
  ring

/-- **`dropDayZero` preserves divergence**: the prefix sums differ by the constant `W 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dropDayZero_divergent {W : ℕ → EF} {P : History} (hdiv : DivergentWeighting W P) :
    DivergentWeighting (dropDayZero W) P := by
  refine ⟨fun n => ?_, ?_⟩
  · cases n with
    | zero => rw [dropDayZero_denote_zero]; exact ⟨le_rfl, zero_le_one⟩
    | succ k => rw [dropDayZero_denote_succ]; exact hdiv.1 (k + 1)
  · have h := Filter.tendsto_atTop_add_const_right atTop (-(W 0).denote P) hdiv.2
    refine h.congr fun N => ?_
    rw [prefixSum_dropDayZero, sub_eq_add_neg]

/-- **`dropDayZero W` is supported on the image of `succDeferral`** (FAF's premise discharged by
construction).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dropDayZero_supported_succ (W : ℕ → EF) (P : History) :
    WeightingSupportedOnDeferralImage (dropDayZero W) P succDeferral :=
  (supportedOnSucc_iff _ _).mpr (dropDayZero_denote_zero W P)

/-! ## B. Feedback computations for the constant streams -/

/-- `truthR (constStream true)` is the constant `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthR_constTrue : truthR (constStream true) = fun _ => (1 : ℝ) := by
  funext n; simp [truthR, constStream]

/-- `truthR (constStream false)` is the constant `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthR_constFalse : truthR (constStream false) = fun _ => (0 : ℝ) := by
  funext n; simp [truthR, constStream]

/-- FAF's ordinary feedback computation (typed at the constant truth `1`), transported to the
always-wrong stream.
Source: none: infrastructure (FAF `ordinaryFeedbackTruthComputation`)
Kind: L
Fidelity: n/a -/
noncomputable def constTrueFeedback :
    FeedbackTruthComputation (truthR (constStream true)) succDeferral := by
  rw [truthR_constTrue]; exact ordinaryFeedbackTruthComputation succDeferral

/-- A feedback computation for the constant truth `0` along any deferral (FAF ships only the
constant `1`): value `0`, code the constant digit `⌜0⌝`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def zeroFeedbackTruthComputation (f : DeferralFunction) :
    FeedbackTruthComputation (fun _ => (0 : ℝ)) f where
  value _ := 0
  code _ := Encodable.encode (0 : ℚ)
  computes := MachineDigits.const _
  computes_at _ := rfl
  agrees k := by norm_num

/-- The zero computation transported to the never-wrong stream.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
noncomputable def constFalseFeedback :
    FeedbackTruthComputation (truthR (constStream false)) succDeferral := by
  rw [truthR_constFalse]; exact zeroFeedbackTruthComputation succDeferral

/-! ## C. The feedback rows' full packages inhabited (N−) -/

/-- **T4(c)'s full package inhabited** (N−): `defiance_calibrated_feedback_class` on the
always-press never-wrong pair at `v := dropDayZero u^def`, `f := succDeferral`, with the zero
feedback computation. The realized wrongness is identically `0`, so the conclusion is met without
content; every hypothesis — generability, divergence, the support condition, `TheoryTruth`,
strict monotonicity, the feedback computation, support on the image — is discharged.
Source: mandate T4 (witness obligation); audit r1 fidelity B2 / adversarial B1
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem witnessB_defiance_feedback {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2) (hq : 2 * δ < q)
    (hq1 : q < 1) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      rho (realized (constPressPair (constStream false) (Primrec.const false))
        (dropDayZero (uDef (constPressPair (constStream false) (Primrec.const false)) q δ)))
        (truthR (constStream false)) N ≤ (q : ℝ) - δ + ε :=
  defiance_calibrated_feedback_class _ q (dropDayZero_pgenerable (uDef_pgenerable _ q δ))
    (dropDayZero_divergent (constFalse_uDef_divergent hδ hδh hq hq1))
    (fun i hi => ((uDef_pos_iff _ hδ q i _).mp (dropDayZero_pos_imp hi)).2.le)
    (constPressPair_theoryTruth _ _) succDeferral succDeferral_strictlyIncreasing
    constFalseFeedback (dropDayZero_supported_succ _ _)

/-- **T4(c)'s full package inhabited, mirror** (N−): `compliance_calibrated_feedback_class` on
the always-press always-wrong pair at `v := dropDayZero u^com` with FAF's ordinary computation.
Source: mandate T4 (witness obligation); audit r1 fidelity B2 / adversarial B1
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem witnessB_compliance_feedback {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2)
    (hq : q + 2 * δ < 1) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      (q : ℝ) + δ - ε ≤ rho (realized (constPressPair (constStream true) (Primrec.const true))
        (dropDayZero (uCom (constPressPair (constStream true) (Primrec.const true)) q δ)))
        (truthR (constStream true)) N :=
  compliance_calibrated_feedback_class _ q (dropDayZero_pgenerable (uCom_pgenerable _ q δ))
    (dropDayZero_divergent (constTrue_uCom_divergent hδ hδh hq))
    (fun i hi => ((uCom_pos_iff _ hδ q i _).mp (dropDayZero_pos_imp hi)).2.le)
    (constPressPair_theoryTruth _ _) succDeferral succDeferral_strictlyIncreasing
    constTrueFeedback (dropDayZero_supported_succ _ _)

/-- **T4(d)'s full package inhabited** (N−): the hybrid iff on the never-wrong pair at
`v := dropDayZero u^def`.
Source: mandate T4 (witness obligation); audit r1 fidelity B2 / adversarial B1
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem witnessB_hybrid_feedback {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2) (hq : 2 * δ < q)
    (hq1 : q < 1) :
    (∀ ε > 0, ∀ᶠ N in atTop, (q : ℝ) - ε ≤
      rhoHat (constPressPair (constStream false) (Primrec.const false))
        (realized (constPressPair (constStream false) (Primrec.const false))
          (dropDayZero (uDef (constPressPair (constStream false) (Primrec.const false)) q δ))) N)
      ↔ (∀ ε > 0, ∀ᶠ N in atTop, (q : ℝ) - ε ≤
      rho (realized (constPressPair (constStream false) (Primrec.const false))
        (dropDayZero (uDef (constPressPair (constStream false) (Primrec.const false)) q δ)))
        (truthR (constStream false)) N) :=
  hybrid_credence_iff_realized_feedback _ q (dropDayZero_pgenerable (uDef_pgenerable _ q δ))
    (dropDayZero_divergent (constFalse_uDef_divergent hδ hδh hq hq1))
    (constPressPair_theoryTruth _ _) succDeferral succDeferral_strictlyIncreasing
    constFalseFeedback (dropDayZero_supported_succ _ _)

/-! ## D. T5(⇐) and T1(b): packages inhabited (N−) -/

/-- The realized frequency against the constant-`0` truth is `0` (including FAF's junk `0` at
zero mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rho_constFalse_eq_zero (v : ℕ → ℝ) (N : ℕ) :
    rho v (truthR (constStream false)) N = 0 := by
  simp [rho, weightedAverage, prefixSum, truthR, constStream]

/-- **T5(⇐)'s full package inhabited** (N−, the circular instance): on the always-press
never-wrong pair with `v := u^def`, `η := 4δ`, the realized wrongness is identically `0`, so
"mostly false" holds at every margin `≤ q`; the conclusion is `constFalse_uDef_divergent`. It
shows the package is consistent, not that `mostly_false_forces_defiance` has content on it (the
docstring's own warning).
Source: audit r1 adversarial N3 (probe `MostlyFalseInhabited.lean`); fidelity N5
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem witnessB_mostly_false {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2) (hq : 4 * δ ≤ q)
    (hq1 : q < 1) :
    Tendsto (prefixSum (realized (constPressPair (constStream false) (Primrec.const false))
      (uDef (constPressPair (constStream false) (Primrec.const false)) q δ))) atTop atTop := by
  have hq0 : 0 < q := by linarith
  have hq2 : 2 * δ < q := by linarith
  refine mostly_false_forces_defiance (constPressPair (constStream false) (Primrec.const false))
    hq0 hδ (le_refl (4 * δ)) hq (uDef_pressClass _ q hδ)
    (constFalse_uDef_divergent hδ hδh hq2 hq1) (constPressPair_theoryTruth _ _) ?_
  intro ε hε
  refine Filter.Eventually.of_forall fun N => ?_
  rw [rho_constFalse_eq_zero]
  have : ((4 * δ : ℚ) : ℝ) ≤ q := by exact_mod_cast hq
  push_cast at this ⊢
  linarith

/-- **T1(b) instantiated** (N−): `toyX_expect_asymp` over the always-press pair's agent and
process, for any verdict stream `y`.
Source: audit r1 fidelity N4 (the ledger's witness cell, now built)
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem witnessB_toyX_expect_asymp (y : ℕ → Bool) (hy : Primrec y) (c h : ℚ) :
    (fun n => (toyX c h (constPressPair y hy).φ n).expect (constPressPair y hy).agent n) ≈ₙ
      (fun n => (c : ℝ) - ((c : ℝ) + h) * (constPressPair y hy).agent n ((constPressPair y hy).φ n)) :=
  toyX_expect_asymp (constPressPair y hy).agent (constPressPair y hy).agentProcess c h
    (constPressPair y hy).φ (constPressPair y hy).φ_codes (constPressPair y hy).hworld

/-! ## E. T12(a): trust in reports inhabited; a pair whose report is not the press -/

/-- The constant weighting `1` is P-generable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constOneW_pgenerable : PGenerableWeighting (fun _ : ℕ => EF.const 1) :=
  { polySeg := MachineSpliceStream.serialize_const 1
    rank_le := fun n => by simp
    closed := fun n ρ V => by simp [EF.denoteWith, EF.denote] }

/-- The constant weighting `1` is divergent at every market.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constOne_divergent (P : History) : DivergentWeighting (fun _ : ℕ => EF.const 1) P := by
  refine ⟨fun _ => by simp, ?_⟩
  have h : (fun n : ℕ => (EF.const (1 : ℚ)).denote P) = fun _ => (1 : ℝ) := by
    funext n; simp
  rw [h]
  refine tendsto_atTop_atTop.mpr fun M => ⟨⌈M⌉₊, fun n hn => ?_⟩
  rw [prefixSum_one]
  calc M ≤ ⌈M⌉₊ := Nat.le_ceil M
    _ ≤ n := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith

/-- **T12(a) inhabited on the always-press pair** (N−): Recurring Unbiasedness on the report
atoms at the constant weighting. On an `ofTable` pair every ledger item carries the press table,
so here the report item is the press itself (`reportTruth ≡ 1`).
Source: T12(a) witness obligation; audit r1 adversarial N7
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem witnessB_report_trust_constPress (y : ℕ → Bool) (hy : Primrec y) :
    HasLimitPoint (weightedBias (realized (constPressPair y hy) (fun _ => EF.const 1))
      (fun i => (constPressPair y hy).agent i (reportAtom i)) (reportTruth (constPressPair y hy)))
      0 :=
  report_trust _ constOneW_pgenerable (constOne_divergent _)

/-- **The two-item table**: item `0` the always-press `1`, item `1` the board's report stream
`1[r n]` (any Boolean stream; truthful if `r = y`, lying if `r = !y`, arbitrary otherwise).
Source: audit r1 adversarial N7; findings F8
Kind: D
Fidelity: n/a -/
def twoTable (r : ℕ → Bool) (j n : ℕ) : ℚ := if j = 0 then 1 else if r n then 1 else 0

/-- The two-item table is computable for a primitive recursive report stream.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoTable_computable (r : ℕ → Bool) (hr : Primrec r) :
    Computable fun p : ℕ × ℕ => twoTable r p.1 p.2 :=
  (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 1)
    (Primrec.ite (Primrec.eq.comp (hr.comp Primrec.snd) (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0))).to_comp

/-- The two-item table lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoTable_mem (r : ℕ → Bool) (j n : ℕ) : 0 ≤ twoTable r j n ∧ twoTable r j n ≤ 1 := by
  unfold twoTable
  split_ifs <;> norm_num

/-- **The two-table shutdown pair**: FAF's LIA over the tag-`0` verdict process of `y` plus the
same-day ledger of the two-item table (press `1`, report `1[r n]`); the report stream `r` is
independent of the verdict stream `y`.
Source: audit r1 adversarial N7; mandate design decision 6(i) (the base)
Kind: N−
Fidelity: n/a
Hyps: (a) (`hy`, `hr`: primitive recursive streams) -/
noncomputable def twoTablePair (y r : ℕ → Bool) (hy : Primrec y) (hr : Primrec r) :
    ShutdownPair :=
  ShutdownPair.ofTables (verdictDP y) (atomDP_succ_computable tagZero_primrec hy)
    (atomFamily tagZero) tagZero_codes (twoTable r) (twoTable_computable r hr) (twoTable_mem r)
    (processFreeOf_ledgerSchedule_of_tagFree (verdictDP_tagFree y))
    (atomDP_hworld tagZero_injective y _)

/-- The two-table pair presses every day (item `0` is `1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twoTablePair_press (y r : ℕ → Bool) (hy : Primrec y) (hr : Primrec r) (n : ℕ) :
    (twoTablePair y r hy hr).press n = 1 := by
  show twoTable r 0 n = 1
  simp [twoTable]

/-- **The report ledger of the two-table pair is the report stream**: `reportTruth = truthR r`.
Source: none: infrastructure
Kind: L
Fidelity: exact -/
theorem twoTablePair_reportTruth (y r : ℕ → Bool) (hy : Primrec y) (hr : Primrec r) :
    reportTruth (twoTablePair y r hy hr) = truthR r := by
  funext n
  show (if (1 / 2 : ℚ) < twoTable r 1 n then (1 : ℝ) else 0) = truthR r n
  cases hrn : r n <;> norm_num [twoTable, truthR, hrn]

/-- The verdict ledger of the two-table pair is a `TheoryTruth` at `truthR y` (derived from the
stages, as for `constPressPair`).
Source: none: infrastructure
Kind: L
Fidelity: exact -/
theorem twoTablePair_theoryTruth (y r : ℕ → Bool) (hy : Primrec y) (hr : Primrec r) :
    AffineCombination.TheoryTruth (twoTablePair y r hy hr).φ (twoTablePair y r hy hr).agentProcess
      (truthR y) :=
  theoryTruth_ledgerProcess (atomDP_theoryTruth (fun j => Nat.lt_succ_self j) y)

/-- **T12(a) inhabited on a pair whose report is not the press** (N−): on `twoTablePair y r`
the agent's prices of the report atoms are recurringly unbiased against the report stream `r`
at the constant weighting — for every primitive recursive `r`, whether or not it tracks the
verdict stream `y`. This is finding F8 in Lean: trust in the *reports* is forced, the report →
truth link is not (take `r := fun n => !y n`).
Source: T12(a) witness obligation; audit r1 adversarial N7; findings F8
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem witnessB_report_trust_twoTable (y r : ℕ → Bool) (hy : Primrec y) (hr : Primrec r) :
    HasLimitPoint (weightedBias (realized (twoTablePair y r hy hr) (fun _ => EF.const 1))
      (fun i => (twoTablePair y r hy hr).agent i (reportAtom i)) (truthR r)) 0 := by
  have h := report_trust (twoTablePair y r hy hr) constOneW_pgenerable (constOne_divergent _)
  rwa [twoTablePair_reportTruth] at h

end Cleanroom.Corrigibility.CorrLiShutdown
