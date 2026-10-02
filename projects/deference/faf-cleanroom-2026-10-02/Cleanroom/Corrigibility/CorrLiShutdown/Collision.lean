import Cleanroom.Corrigibility.CorrLiShutdown.SignedError
import Cleanroom.Corrigibility.CorrLiShutdown.WitnessesB

/-!
# `corr-li-shutdown` — Collision: good feedback at `succDeferral` is never pseudorandom

**Finding F17 (audit r1, fidelity B1; blocking for the sources' Statement 1(c′) at every
deferral with `f(k+1) ≤ poly(f(k))`).** FAF's "good feedback" `FeedbackTruthComputation truth f`
carries `computes_at k : code (Nat.pair k (f (k+1))) = ⌜value k⌝` on a machine-metered digit
stream (`computes : MachineDigits code`), with `value k = truth (f k)`. At `f = succDeferral`
this makes the verdict stream *poly-time readable on its own day*: the constant feature
progression `W m := const (value (m − 1))`, which denotes `truth m` for every `m ≥ 1`, is a
`PGenerableWeighting` (`sameDayW_pgenerable`: the digits of `code` read at the unary ruler
`m ↦ Nat.pair (m − 1) (m + 1)`, then one `bigPayload`). If `truth` is `1` infinitely often, `W` is
divergent, `succ`-patient (`deferralPatient_succ`) and averages `truth` to `1`; if `truth` is
eventually `0`, the constant weighting `1` averages it to `0`. So **no Boolean stream with good
feedback at `succDeferral` is pseudorandom with a frequency in `(0,1)` over all P-generable
divergent weightings** (`succFeedback_not_pseudorandom`, P), and the hypothesis package of
`signedError_unbounded` (T6, the FAF-facing form) is unsatisfiable
(`signedError_unbounded_package_unsat`): that theorem is **vacuous** as stated, independently of
the OPEN certificate it rests on.

This is the LI paper's own regime boundary, not a FAF artifact: `thm:wub` (`main.tex:1249`)
defines good feedback as "`Thm(φ_{f(n)})` computable in `O(f(n+1))` time", and at `f = succ` that
is a linear-time Boolean stream, for which Def. 4.4.1 (pseudorandom over *all* generable
divergent weightings) fails by the same `W`. The same collapse holds for every deferral with
`f(k+1) ≤ poly(f(k))` (`n + c`, `2n`, `2^n`), since the day-`f(k)` trader's budget covers
`poly(f(k+1))`; only a deferral growing faster than every polynomial iterate escapes it
(argument, not formalized). The sources' Statement 1(c′) (`li-final.md` l. 64, proof l. 104–112)
states the two hypotheses together at a general `f`; what its ledger picture needs is *decided*
feedback (the verdict of day `f(i)` enters the deductive process by day `f(i+1)` as a decided
atom), a different hypothesis with no FAF object yet. Probe of record:
`run/wp/corr-li-shutdown/audit-r1-probes/T6PackageUnsat.lean` (the fidelity auditor's; this file
lifts it, docstrings added, names changed).
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LogicalInduction.FeedbackTruth Filter Topology
open Cleanroom.Found.LiAsympCalc

/-- The ruler `m ↦ Nat.pair (m − 1) (succDeferral ((m − 1) + 1))`: the index at which a
`succDeferral` feedback computation's digit stream carries the canonical code of
`value (m − 1)` (its `computes_at (m − 1)`).
Source: none: infrastructure (audit r1 fidelity B1, probe `T6PackageUnsat.lean`)
Kind: L
Fidelity: n/a -/
lemma unaryRuler_sameDayIndex :
    UnaryRuler (fun m => Nat.pair (m - 1) (succDeferral (m - 1 + 1))) :=
  ((UnaryRuler.id.sub (UnaryRuler.const 1)).pair
    ((UnaryRuler.id.sub (UnaryRuler.const 1)).add (UnaryRuler.const 2))).of_eq
    (fun _ => rfl)

/-- **The same-day feedback weighting** `W m := const (value (m − 1))` of a `succDeferral`
feedback computation: it denotes `truth m` for every `m ≥ 1` (`sameDayW_denote`).
Source: none: infrastructure (audit r1 fidelity B1)
Kind: D
Fidelity: n/a -/
def sameDayW {truth : ℕ → ℝ} (C : FeedbackTruthComputation truth succDeferral) (m : ℕ) : EF :=
  EF.const (C.value (m - 1))

/-- **The same-day feedback weighting is P-generable**: its digits are `C.code` read at
`Nat.pair (m − 1) (m + 1)` — a machine-metered stream composed with a unary ruler — written out
by one `bigPayload`. This is the same digit-reading construction FAF uses in
`feedbackResidualSeqPoly` (`FeedbackTruth.lean`, `hrawConst`).
Source: none: infrastructure (audit r1 fidelity B1); FAF `MachineDigits.comp`, `MachineSpliceStream.bigPayload`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma sameDayW_pgenerable {truth : ℕ → ℝ} (C : FeedbackTruthComputation truth succDeferral) :
    PGenerableWeighting (sameDayW C) := by
  have hdig : MachineDigits (fun m => C.code (Nat.pair (m - 1) (succDeferral (m - 1 + 1)))) :=
    C.computes.comp unaryRuler_sameDayIndex
  have hdig' : MachineDigits (fun m => Encodable.encode (C.value (m - 1))) :=
    hdig.of_eq (fun m => C.computes_at (m - 1))
  exact
    { polySeg := (MachineSpliceStream.bigPayload 1 (Or.inl rfl) hdig').of_eq (fun _ => rfl)
      rank_le := fun n => by simp [sameDayW]
      closed := fun n ρ V => by simp [sameDayW, EF.denote] }

/-- `sameDayW` denotes `truth m` for `m ≥ 1` (`C.agrees`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sameDayW_denote {truth : ℕ → ℝ} (C : FeedbackTruthComputation truth succDeferral)
    (P : History) {m : ℕ} (hm : 1 ≤ m) : (sameDayW C m).denote P = truth m := by
  simp only [sameDayW, EF.denote_const]
  rw [C.agrees (m - 1)]
  congr 1
  show m - 1 + 1 = m
  omega

/-- `sameDayW` denotes `truth 1` on day `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sameDayW_denote_zero {truth : ℕ → ℝ} (C : FeedbackTruthComputation truth succDeferral)
    (P : History) : (sameDayW C 0).denote P = truth 1 := by
  simp only [sameDayW, EF.denote_const]
  exact C.agrees 0

/-- **Good feedback at `succDeferral` is never pseudorandom** (F17, P): a Boolean stream with a
FAF `FeedbackTruthComputation` at `succDeferral` is poly-time readable on the day, hence not
`PseudorandomFrequency` with any frequency `p ∈ (0,1)` over the P-generable divergent weightings
of any market `P`. Case A (`truth = 1` infinitely often): the same-day weighting `sameDayW C` is
generable, divergent and `succ`-patient, and its `truth`-weighted average is `≥ 1 − 1/mass → 1`,
not `p`. Case B (`truth` eventually `0`): the constant weighting `1` averages `truth` to `0`.
Source: audit r1 fidelity B1 (probe `T6PackageUnsat.lean`); LI paper `thm:wub` vs `def:pseudorandom` (`main.tex:1249–1283`)
Kind: P
Fidelity: exact (the refutation of the joint hypothesis; the stream, the frequency and the market are arbitrary)
Hyps: (a) -/
theorem succFeedback_not_pseudorandom (P : History) {truth : ℕ → ℝ} {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (htruth : ∀ i, truth i = 0 ∨ truth i = 1)
    (hpseudo : PseudorandomFrequency truth p succDeferral P)
    (C : FeedbackTruthComputation truth succDeferral) : False := by
  have hB : ∀ i, 0 ≤ truth i ∧ truth i ≤ 1 := fun i => by
    rcases htruth i with h | h <;> simp [h]
  have hBsq : ∀ i, truth i * truth i = truth i := fun i => by
    rcases htruth i with h | h <;> simp [h]
  by_cases hfreq : ∃ᶠ m in atTop, truth m = 1
  · -- Case A: `truth` is `1` infinitely often; the same-day weighting has frequency `1`.
    set w : ℕ → ℝ := fun m => (sameDayW C m).denote P with hw
    have hwmem : ∀ m, 0 ≤ w m ∧ w m ≤ 1 := by
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [hw]; rw [sameDayW_denote_zero]; exact hB 1
      · simp only [hw]; rw [sameDayW_denote C P hm]; exact hB m
    have hone : ∃ᶠ m in atTop, 1 ≤ w m := by
      refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono ?_
      rintro m ⟨h1, hm⟩
      simp only [hw]; rw [sameDayW_denote C P hm, h1]
    have hdivT : Tendsto (prefixSum w) atTop atTop :=
      tendsto_prefixSum_of_frequently_one (fun i => (hwmem i).1) hone
    have hdiv : DivergentWeighting (sameDayW C) P := ⟨hwmem, hdivT⟩
    have hps := hpseudo _ (sameDayW_pgenerable C) hdiv (deferralPatient_succ hwmem)
    -- `prefixSum w N − 1 ≤ prefixSum (w · truth) N`
    have hnum : ∀ N, prefixSum w N - 1 ≤ prefixSum (fun i => w i * truth i) N := by
      intro N
      unfold prefixSum
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hterm : ∀ i, w (i + 1) * truth (i + 1) = w (i + 1) := by
        intro i
        have : w (i + 1) = truth (i + 1) := by
          simp only [hw]; exact sameDayW_denote C P (Nat.le_add_left 1 i)
        rw [this, hBsq]
      simp only [hterm]
      have h0 : w 0 * truth 0 ≥ w 0 - 1 := by
        have := hB 0; have := hwmem 0; nlinarith
      linarith
    have hev1 : ∀ᶠ N in atTop, 2 / (1 - p) < prefixSum w N :=
      hdivT.eventually (eventually_gt_atTop _)
    have hev2 : ∀ᶠ N in atTop, |weightedAverage w truth N - p| < (1 - p) / 2 := by
      have := (Metric.tendsto_nhds.mp hps) ((1 - p) / 2) (by linarith)
      filter_upwards [this] with N hN
      rwa [Real.dist_eq, sub_zero] at hN
    obtain ⟨N, hN1, hN2⟩ := (hev1.and hev2).exists
    have hpos : 0 < prefixSum w N := lt_trans (by positivity) hN1
    have havg : 1 - 1 / prefixSum w N ≤ weightedAverage w truth N := by
      rw [weightedAverage_eq_div hpos.ne', le_div_iff₀ hpos]
      have := hnum N
      rw [sub_mul, one_div_mul_cancel hpos.ne']
      linarith
    have hinv : 1 / prefixSum w N < (1 - p) / 2 := by
      rw [div_lt_iff₀ hpos]
      have h1p : (1 - p) ≠ 0 := by linarith
      have h2 : 2 / (1 - p) * ((1 - p) / 2) = 1 := by field_simp
      nlinarith [hN1, h2]
    rw [abs_lt] at hN2
    linarith [hN2.2, havg, hinv]
  · -- Case B: `truth` is eventually `0`; the constant weighting `1` has frequency `0`.
    have hev0 : ∀ᶠ m in atTop, truth m = 0 := by
      rw [Filter.not_frequently] at hfreq
      filter_upwards [hfreq] with m hm
      rcases htruth m with h | h
      · exact h
      · exact absurd h hm
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev0
    have hconst : ∀ N, N₀ ≤ N → prefixSum truth N = prefixSum truth N₀ := by
      intro N hN
      induction N with
      | zero => have : N₀ = 0 := Nat.le_zero.mp hN; rw [this]
      | succ k ih =>
        rcases Nat.of_le_succ hN with h | h
        · rw [prefixSum_succ, ih h, hN₀ (k + 1) (by omega), add_zero]
        · rw [h]
    set K := prefixSum truth N₀ with hK
    have hwmem : ∀ _m : ℕ, 0 ≤ (EF.const (1 : ℚ)).denote P ∧ (EF.const (1 : ℚ)).denote P ≤ 1 := by
      intro _; simp
    have hone : ∃ᶠ (_m : ℕ) in atTop, (1 : ℝ) ≤ (EF.const (1 : ℚ)).denote P :=
      Filter.Frequently.of_forall (fun _ => by simp)
    have hdivT : Tendsto (prefixSum (fun _ => (EF.const (1 : ℚ)).denote P)) atTop atTop :=
      tendsto_prefixSum_of_frequently_one (fun i => (hwmem i).1) hone
    have hdiv : DivergentWeighting (fun _ : ℕ => EF.const 1) P := ⟨hwmem, hdivT⟩
    have hps := hpseudo _ constOneW_pgenerable hdiv (deferralPatient_succ hwmem)
    have hden : ∀ N, prefixSum (fun _ => (EF.const (1 : ℚ)).denote P) N = (N : ℝ) + 1 := by
      intro N; simp [prefixSum]
    have hnum : ∀ N, prefixSum (fun i => (EF.const (1 : ℚ)).denote P * truth i) N =
        prefixSum truth N := by
      intro N; simp [prefixSum]
    have hev1 : ∀ᶠ (N : ℕ) in atTop, K / (p / 2) < (N : ℝ) + 1 := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventually_gt_atTop (K / (p / 2)))
      filter_upwards [h] with N hN
      linarith
    have hev2 : ∀ᶠ (N : ℕ) in atTop,
        |weightedAverage (fun _ => (EF.const (1 : ℚ)).denote P) truth N - p| < p / 2 := by
      have := (Metric.tendsto_nhds.mp hps) (p / 2) (by linarith)
      filter_upwards [this] with N hN
      rwa [Real.dist_eq, sub_zero] at hN
    obtain ⟨N, ⟨hN1, hN2⟩, hN3⟩ := ((hev1.and hev2).and (eventually_ge_atTop N₀)).exists
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have havg : weightedAverage (fun _ => (EF.const (1 : ℚ)).denote P) truth N =
        K / ((N : ℝ) + 1) := by
      rw [weightedAverage_eq_div (by rw [hden]; exact hpos.ne'), hden, hnum, hconst N hN3]
    have hKnn : 0 ≤ K := prefixSum_nonneg (fun i => (hB i).1) N₀
    have hsmall : K / ((N : ℝ) + 1) < p / 2 := by
      rw [div_lt_iff₀ hpos]
      have hp2 : 0 < p / 2 := by linarith
      rw [div_lt_iff₀ hp2] at hN1
      linarith
    rw [havg, abs_lt] at hN2
    linarith [hN2.1, hsmall]

/-- **`signedError_unbounded`'s hypothesis package is unsatisfiable** (F17): its hypotheses
(minus `hφ`, which is not needed) imply `False`. T6's FAF-facing theorem is therefore vacuous
as stated: at `succDeferral`, FAF's good feedback and FAF's pseudorandomness collide. The
real-sequence core `signedError_core` is unaffected (its abstract clause is restricted to the
running-sum ramps and is satisfiable).
Source: audit r1 fidelity B1; [[corr-wf14-inventory]] 083 (Statement 1(c′), whose hypotheses these are at `f = succ`)
Kind: P
Fidelity: exact (the package of `signedError_unbounded`, verbatim)
Hyps: (a) -/
theorem signedError_unbounded_package_unsat (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) {truth : ℕ → ℝ}
    (htruth : AffineCombination.TheoryTruth φ DP truth) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpseudo : PseudorandomFrequency truth p succDeferral P)
    (C : FeedbackTruthComputation truth succDeferral)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : False :=
  succFeedback_not_pseudorandom P hp0 hp1 (fun i => htruth.isBoolean hworld i) hpseudo C

end Cleanroom.Corrigibility.CorrLiShutdown
