import Cleanroom.Corrigibility.CorrLiShutdown.Dichotomy
import Cleanroom.Corrigibility.CorrLiShutdown.WitnessesA
import LogicalInduction.Construction.Statistics.FeedbackTruth
import Mathlib.Order.LiminfLimsup

/-!
# `corr-li-shutdown` — SignedError (T6): Statement 1(c′), the realized signed error is unbounded

**The real-sequence core** (`signedError_core`, P): let `price i → p ∈ (0,1)`, `truth i ∈ {0,1}`,
`e i := price i − truth i`, `T N := ∑_{i ≤ N} e i`. If every *ramp of the running sum*
weighting `v_{N+1} := 1[N ≥ N₀]·Ind_{η'}(T_N > M')` (rational `η' > 0`, `M'`) that has divergent
mass averages `truth` to `p`, then **`T` is not bounded**. The argument is the sources' with the
hard indicator `1[T_N > M']` replaced by the ramp (the hard indicator of a computed-from-prices
quantity is not an `EF`, finding F1): with `M := limsup T` (finite because `T` is bounded),
`η := p/4`, `M' ∈ (M − η, M − 3η/4)` rational, `η' < η/4` rational, and `N₀` such that
`T_N < M + η/2` and `price_N > 2η` beyond it: on the support `T_N > M'`, `e_{N+1} < 3η/2 < 2η`
forces `truth (N+1) = 1`; `T_N > M − η/2` infinitely often (limsup) saturates the ramp, so the
mass diverges; the weighted truth frequency on the support is `1 ≠ p`.

**Finding F11 (local error in the sources' proof; conclusion weakened; the two-sided form
refuted over the Lean's clause — repair round 2).** The sources conclude
`sup_N T_N = +∞ ∧ inf_N T_N = −∞`, but their proof ("suppose also `inf T > −∞`, and let
`M := limsup T`, finite") uses boundedness on *both* sides to make `limsup T` finite; the case
`T` bounded above with `T → −∞` is never closed. What the argument proves is
`¬(BddAbove ∧ BddBelow)` — the realized signed error is unbounded — and, pushed one step, the
**dichotomy** `BddAbove T → T → −∞` (`signedError_bddAbove_tendsto_atBot`: `limsup T` is finite
as soon as `T` is bounded above and does not tend to `−∞`), with the mirror under the downward
ramps (`signedError_bddBelow_tendsto_atTop`) and the **trichotomy** `T → −∞ ∨ T → +∞ ∨`
unbounded on both sides (`signedError_trichotomy`). The two-sided form over the Lean's clause —
round 0's OPEN `signedError_two_sided_open` — is **false** (audit r2 fidelity B1;
`signedError_two_sided_refuted`): `price ≡ 1/2`, `truth ≡ 1` satisfies the clause vacuously
(every upward ramp of a running sum tending to `−∞` is eventually `0`) with `T` bounded above.
The counterexample does not satisfy Def. 4.4.1 (the constant weighting averages `truth ≡ 1` to
`1`), so the sources' two-sided claim over their own hypothesis is untouched; but no clause over
functions of the running sum alone can recover it: a slow drift `T → −∞` with truth density `1/2`
satisfies **both** ramp clauses — built in `Drift.lean` (`driftTruth`,
`signedError_trichotomy_atBot_realized`, repair round 3: the trichotomy's first two cases are
realized under the two-sided clause) — and its FAF-facing form at `succ` is vacuous (F17). It is
recorded as a question, not listed OPEN.

**The FAF layer.** `runningSumFeature` is the running sum as an expressible feature of the
inductor's prices with the feedback values as constants (`FeedbackTruthComputation.value`),
`runningSumRampFeature` the ramp weighting, `runningSumRampFeature_denote` its denotation;
**`runningSumRampFeature_pgenerable` is OPEN** (the `MachineSpliceStream` certificate of a
growing affine sum with digits read from `C`; model: FAF's `FeedbackTraderEmissionSigns`).
`signedError_unbounded` is the FAF-facing theorem over `PseudorandomFrequency truth p succDeferral
P`, resting on that certificate (`partial`). `DeferralPatient succDeferral` is discharged with
`C = 2` (`deferralPatient_succ`).

**Audit r1, fidelity B1 — `signedError_unbounded` is vacuous (F17, `Collision.lean`).** Its two
named hypotheses collide: `C : FeedbackTruthComputation truth succDeferral` makes the verdict
stream poly-time readable on its own day, so the constant weighting `const (C.value (m − 1))`
is P-generable and averages `truth` to `1` (or the constant `1` averages it to `0`), against
`PseudorandomFrequency truth p succDeferral P` with `p ∈ (0,1)`
(`signedError_unbounded_package_unsat`, P). The theorem is kept as the record of the route the
mandate specified, with its status `vacuous`; completing the OPEN certificate below would
complete a theorem that says nothing, so it is deprioritized. The real-sequence core is
unaffected. A non-vacuous FAF-facing form needs either a super-polynomially growing deferral
`f` (good feedback along `f`, pseudorandomness at `succ`, the running sum along `f`) or
*decided* rather than *computed* feedback — neither has an FAF object yet; see the report.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LogicalInduction.FeedbackTruth Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. The ramp-of-the-running-sum weighting (real form) -/

/-- **The ramp-of-the-running-sum weighting** `v_0 := 0`, `v_{N+1} := 1[N ≥ N₀]·Ind_{η'}(T_N > M')`
with `T_N := ∑_{i ≤ N} e_i` — the repaired form of the sources' hard-indicator weighting.
Source: [[corr-wf14-inventory]] 083 (`li-final.md` §Proof of Statement 1(c′)); mandate T6 (the repair)
Kind: D
Fidelity: variant: ramp of width `η'` in place of the hard indicator; finite cutoff `N₀`
Hyps: n/a -/
noncomputable def runningSumRamp (e : ℕ → ℝ) (η' M' : ℚ) (N₀ : ℕ) : ℕ → ℝ
  | 0 => 0
  | N + 1 => if N₀ ≤ N then ctsInd η' (prefixSum e N) M' else 0

/-- The weighting lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma runningSumRamp_mem (e : ℕ → ℝ) (η' M' : ℚ) (N₀ : ℕ) (n : ℕ) :
    0 ≤ runningSumRamp e η' M' N₀ n ∧ runningSumRamp e η' M' N₀ n ≤ 1 := by
  cases n with
  | zero => simp [runningSumRamp]
  | succ N =>
    simp only [runningSumRamp]
    split_ifs
    · exact ⟨ctsInd_nonneg _ _ _, ctsInd_le_one _ _ _⟩
    · simp

/-- Prefix sums of a nonnegative sequence that is `≥ 1` infinitely often tend to `∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_prefixSum_of_frequently_one {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hfreq : ∃ᶠ n in atTop, 1 ≤ w n) : Tendsto (prefixSum w) atTop atTop := by
  have hmono := prefixSum_mono_of_nonneg hw
  have hclaim : ∀ K : ℕ, ∃ N, (K : ℝ) ≤ prefixSum w N := by
    intro K
    induction K with
    | zero => exact ⟨0, by simpa using prefixSum_nonneg hw 0⟩
    | succ K ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨N', hN'1, hN'2⟩ := (frequently_atTop.mp hfreq) (N + 1)
      refine ⟨N', ?_⟩
      obtain ⟨M, rfl⟩ : ∃ M, N' = M + 1 := ⟨N' - 1, by omega⟩
      rw [prefixSum_succ]
      have := hmono (show N ≤ M by omega)
      push_cast
      linarith
  rw [tendsto_atTop_atTop]
  intro M
  obtain ⟨N, hN⟩ := hclaim ⌈M⌉₊
  exact ⟨N, fun n hn => (Nat.le_ceil M).trans (hN.trans (hmono hn))⟩

/-- A frequently-true predicate on `N` gives a frequently-true predicate on `N + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frequently_succ_of_frequently {P : ℕ → Prop} (h : ∃ᶠ N in atTop, P N) :
    ∃ᶠ n in atTop, ∃ N, n = N + 1 ∧ P N := by
  rw [frequently_atTop] at h ⊢
  intro K
  obtain ⟨N, hN, hP⟩ := h K
  exact ⟨N + 1, by omega, N, rfl, hP⟩

/-! ## B. The real-sequence core, its dichotomy, and the refutation of the two-sided form -/

/-- **The core's argument, factored.** From `T` bounded above *and cobounded above* (`T` does not
tend to `−∞`) — exactly what makes `limsup T` a finite real that `T` approaches from below
infinitely often — the upward-ramp clause yields `False`. `signedError_core` uses it with
coboundedness from `BddBelow`; the dichotomy `signedError_bddAbove_tendsto_atBot` with
coboundedness from `¬ (T → −∞)`.
Source: [[corr-wf14-inventory]] 083 (§Proof of Statement 1(c′), the margin argument), factored
Kind: P
Fidelity: n/a (the engine of the two theorems below)
Hyps: as `signedError_core` -/
theorem signedError_core_aux {price truth : ℕ → ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hprice : Tendsto price atTop (𝓝 p)) (htruth : ∀ i, truth i = 0 ∨ truth i = 1)
    (hpseudo : ∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => price i - truth i) η' M' N₀)) atTop atTop →
      weightedAverage (runningSumRamp (fun i => price i - truth i) η' M' N₀) truth ≈ₙ
        fun _ => p)
    (hbddA : IsBoundedUnder (· ≤ ·) atTop (prefixSum (fun i => price i - truth i)))
    (hcobdd : IsCoboundedUnder (· ≤ ·) atTop (prefixSum (fun i => price i - truth i))) :
    False := by
  set e : ℕ → ℝ := fun i => price i - truth i with he
  set T := prefixSum e with hT
  set M := Filter.limsup T atTop with hM
  set η : ℝ := p / 4 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  obtain ⟨M', hM'1, hM'2⟩ := exists_rat_btwn (show M - η < M - 3 * η / 4 by linarith)
  obtain ⟨η', hη'0, hη'1⟩ := exists_rat_btwn (show (0 : ℝ) < η / 4 by linarith)
  have hη'Q : 0 < η' := by exact_mod_cast hη'0
  -- eventually `T_N < M + η/2` and `price_N > 2η`
  have hev1 : ∀ᶠ N in atTop, T N < M + η / 2 :=
    Filter.eventually_lt_of_limsup_lt (by linarith) hbddA
  have hev2 : ∀ᶠ N in atTop, 2 * η < price N := by
    have := (Metric.tendsto_nhds.mp hprice) (p - 2 * η) (by linarith)
    filter_upwards [this] with N hN
    rw [Real.dist_eq, abs_lt] at hN
    linarith [hN.1]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hev1.and hev2)
  set v := runningSumRamp e η' M' N₀ with hv
  have hvmem : ∀ n, 0 ≤ v n ∧ v n ≤ 1 := runningSumRamp_mem e η' M' N₀
  -- on the support, the next verdict is `1`
  have hsupp : ∀ N, 0 < v (N + 1) → truth (N + 1) = 1 := by
    intro N hpos
    simp only [hv, runningSumRamp] at hpos
    split_ifs at hpos with hN
    · have hTN : (M' : ℝ) < T N := (ctsInd_pos_iff hη'Q _ _).mp hpos
      rcases htruth (N + 1) with h0 | h1
      · exfalso
        have h1' := (hN₀ (N + 1) (by omega)).1
        have h2' := (hN₀ (N + 1) (by omega)).2
        have hstep : T (N + 1) = T N + e (N + 1) := prefixSum_succ e N
        have : e (N + 1) = price (N + 1) := by simp [he, h0]
        linarith
      · exact h1
    · exact absurd hpos (lt_irrefl 0)
  -- the ramp is saturated infinitely often
  have hfreq : ∃ᶠ N in atTop, M - η / 2 < T N :=
    Filter.frequently_lt_of_lt_limsup hcobdd (by linarith)
  have hone : ∃ᶠ n in atTop, 1 ≤ v n := by
    have h := frequently_succ_of_frequently (hfreq.and_eventually (eventually_ge_atTop N₀))
    refine h.mono ?_
    rintro n ⟨N, rfl, hTN, hN⟩
    simp only [hv, runningSumRamp, if_pos hN]
    have hone' : ctsInd η' (prefixSum e N) (M' : ℝ) = 1 := by
      rw [ctsInd_eq_one_iff hη'Q]
      have : prefixSum e N = T N := rfl
      rw [this]
      linarith
    rw [hone']
  have hdiv : Tendsto (prefixSum v) atTop atTop :=
    tendsto_prefixSum_of_frequently_one (fun i => (hvmem i).1) hone
  have hps := hpseudo η' M' N₀ hη'Q hdiv
  have hev3 : ∀ᶠ N in atTop, 0 < prefixSum v N := eventually_prefixSum_pos hdiv
  have hclose := (Metric.tendsto_nhds.mp hps) (1 - p) (by linarith)
  obtain ⟨N, hN1, hN2⟩ := (hclose.and hev3).exists
  have hwa : weightedAverage v truth N = 1 := by
    refine le_antisymm (weightedAverage_le_one (fun i => (hvmem i).1) (fun i => ?_) N) ?_
    · rcases htruth i with h | h <;> simp [h]
    · refine le_weightedAverage_of_support (fun i => (hvmem i).1) (fun i hi => ?_) hN2
      cases i with
      | zero => simp [hv, runningSumRamp] at hi
      | succ i => rw [hsupp i hi]
  rw [hwa, Real.dist_eq, sub_zero] at hN1
  rw [abs_of_pos (by linarith)] at hN1
  linarith

/-- **Statement 1(c′), real-sequence core: the realized signed error is unbounded** (T6, P).
Hypotheses: `price → p ∈ (0,1)`; `truth ∈ {0,1}`; and the abstract pseudorandomness clause: every
**upward** ramp-of-the-running-sum weighting with divergent mass averages `truth` to `p`.
Conclusion: `T_N := ∑_{i ≤ N} (price_i − truth_i)` is not bounded. The two-sided form
`sup = +∞ ∧ inf = −∞` is **false under this clause** (`signedError_two_sided_refuted`, audit r2
fidelity B1); what the clause gives beyond unboundedness is the dichotomy
`signedError_bddAbove_tendsto_atBot`, and with the downward ramps the trichotomy
`signedError_trichotomy`.
Source: [[corr-wf14-inventory]] 083 (Statement 1(c′), repaired here with the ramp); [[corr-wf14-2-inventory]] 2-027 (b)
Kind: P
Fidelity: weaker: `¬(BddAbove ∧ BddBelow)` in place of the sources' `sup = +∞ ∧ inf = −∞` (F11; sharp for this clause, `signedError_two_sided_refuted`); ramp in place of the hard indicator (F1); **weaker hypothesis** too: the clause quantifies over the upward ramps of the running sum only, not over all P-generable divergent weightings (Def. 4.4.1) — which is what makes the conclusion sharp
Hyps: (a) `hprice`, `htruth`; (c) `hpseudo` is the abstract clause — consistent (`signedError_core_package_inhabited`, N−: at `price ≡ p`, `truth ≡ 1` no upward ramp diverges; the conclusion there holds for the trivial reason `T → −∞`); an instance that exercises the content (an i.i.d. Bernoulli(`p`) truth priced at `p`) is argued, not machine-checked (audit r1 adversarial N5, r2 adversarial N2) — FAF's `PseudorandomFrequency` discharges it in `signedError_unbounded` only vacuously at `succ` (F17: that package is unsatisfiable) -/
theorem signedError_core {price truth : ℕ → ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hprice : Tendsto price atTop (𝓝 p)) (htruth : ∀ i, truth i = 0 ∨ truth i = 1)
    (hpseudo : ∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => price i - truth i) η' M' N₀)) atTop atTop →
      weightedAverage (runningSumRamp (fun i => price i - truth i) η' M' N₀) truth ≈ₙ
        fun _ => p) :
    ¬ (BddAbove (Set.range (prefixSum (fun i => price i - truth i))) ∧
        BddBelow (Set.range (prefixSum (fun i => price i - truth i)))) := by
  rintro ⟨⟨A, hA⟩, ⟨B, hB⟩⟩
  have hbddB : IsBoundedUnder (· ≥ ·) atTop (prefixSum (fun i => price i - truth i)) :=
    Filter.isBoundedUnder_of ⟨B, fun n => hB ⟨n, rfl⟩⟩
  exact signedError_core_aux hp0 hp1 hprice htruth hpseudo
    (Filter.isBoundedUnder_of ⟨A, fun n => hA ⟨n, rfl⟩⟩) hbddB.isCoboundedUnder_flip

/-- **The dichotomy** (repair round 2; what the upward-ramp clause gives beyond
`signedError_core`): under the same hypotheses, if the running sum is bounded above then it
tends to `−∞`. The sources' argument needs only `limsup T` finite, which holds as soon as `T` is
bounded above and does not tend to `−∞` — so the case their proof never closes (F11) is the
*only* way a bounded-above `T` can satisfy the clause, and it is realized
(`signedError_two_sided_refuted`).
Source: [[corr-wf14-inventory]] 083 (§Proof of Statement 1(c′)), pushed one step (F11)
Kind: P
Fidelity: stronger: than `signedError_core` (which it implies); still one-sided (the clause has only the upward ramps)
Hyps: as `signedError_core` -/
theorem signedError_bddAbove_tendsto_atBot {price truth : ℕ → ℝ} {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hprice : Tendsto price atTop (𝓝 p)) (htruth : ∀ i, truth i = 0 ∨ truth i = 1)
    (hpseudo : ∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => price i - truth i) η' M' N₀)) atTop atTop →
      weightedAverage (runningSumRamp (fun i => price i - truth i) η' M' N₀) truth ≈ₙ
        fun _ => p)
    (hA : BddAbove (Set.range (prefixSum (fun i => price i - truth i)))) :
    Tendsto (prefixSum (fun i => price i - truth i)) atTop atBot := by
  by_contra hnot
  obtain ⟨A, hA'⟩ := hA
  have hfreq : ∃ b : ℝ, ∃ᶠ n in atTop, b ≤ prefixSum (fun i => price i - truth i) n := by
    rw [tendsto_atTop_atBot] at hnot
    push Not at hnot
    obtain ⟨b, hb⟩ := hnot
    refine ⟨b, frequently_atTop.mpr fun K => ?_⟩
    obtain ⟨a, haK, hlt⟩ := hb K
    exact ⟨a, haK, hlt.le⟩
  obtain ⟨b, hb⟩ := hfreq
  exact signedError_core_aux hp0 hp1 hprice htruth hpseudo
    (Filter.isBoundedUnder_of ⟨A, fun n => hA' ⟨n, rfl⟩⟩)
    (IsCoboundedUnder.of_frequently_ge hb)

/-- A constant error `e ≡ c` has running sum `T_N = (N + 1)·c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_const (c : ℝ) (N : ℕ) : prefixSum (fun _ : ℕ => c) N = ((N : ℝ) + 1) * c := by
  unfold prefixSum
  rw [Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- For a negative constant error every upward ramp of the running sum is eventually `0`
(`T_N = (N + 1)·c ≤ M'` once `N + 1 ≥ M'/c`).
Source: audit r2 fidelity B1 (probe `TwoSidedRefuted.lean`), generalized; audit r2 adversarial N2
Kind: L
Fidelity: n/a -/
lemma runningSumRamp_const_eventually_zero {c : ℝ} (hc : c < 0) (η' M' : ℚ) (hη' : 0 < η')
    (N₀ : ℕ) : ∀ᶠ n in atTop, runningSumRamp (fun _ => c) η' M' N₀ n = 0 := by
  obtain ⟨K, hK⟩ := exists_nat_ge ((M' : ℝ) / c)
  filter_upwards [eventually_ge_atTop (K + 1)] with n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  simp only [runningSumRamp]
  split_ifs with h
  · rw [prefixSum_const, ctsInd_eq_zero_iff hη']
    have hKN : (K : ℝ) ≤ N := by exact_mod_cast (by omega : K ≤ N)
    have h1 : (M' : ℝ) / c ≤ (N : ℝ) + 1 := by linarith
    have h2 : ((N : ℝ) + 1) * c ≤ (M' : ℝ) / c * c := mul_le_mul_of_nonpos_right h1 hc.le
    rw [div_mul_cancel₀ _ hc.ne] at h2
    exact h2
  · rfl

/-- Hence no upward ramp has divergent mass on a negative constant error: the abstract clause
of `signedError_core` holds vacuously there.
Source: audit r2 fidelity B1 (probe), generalized
Kind: L
Fidelity: n/a -/
lemma runningSumRamp_const_not_divergent {c : ℝ} (hc : c < 0) (η' M' : ℚ) (hη' : 0 < η')
    (N₀ : ℕ) : ¬ Tendsto (prefixSum (runningSumRamp (fun _ => c) η' M' N₀)) atTop atTop := by
  intro htend
  obtain ⟨K, hK⟩ := (runningSumRamp_const_eventually_zero hc η' M' hη' N₀).exists_forall_of_atTop
  set v := runningSumRamp (fun _ => c) η' M' N₀ with hv
  have hconst : ∀ n, K ≤ n → prefixSum v n = prefixSum v K := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [prefixSum_succ, hK (m + 1) (by omega), add_zero, ih]
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp htend (prefixSum v K + 1)
  have h1 := hN (max N K) (le_max_left _ _)
  rw [hconst (max N K) (le_max_right _ _)] at h1
  linarith

/-- **`signedError_core`'s hypothesis package is consistent** (N−): at `price ≡ p`, `truth ≡ 1`
every hypothesis holds — the clause vacuously, since no upward ramp of a running sum tending
to `−∞` has divergent mass. Disclosure: the conclusion holds there for the trivial reason
`T_N = (N + 1)(p − 1) → −∞`; the theorem's content (from a bounded `T`, manufacture a divergent
ramp with truth-frequency `1`) is exercised by no shipped instance.
Source: audit r2 adversarial N2 (probe `SignedErrorCorePackage.lean`), lifted
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem signedError_core_package_inhabited {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < p ∧ p < 1 ∧
    Tendsto (fun _ : ℕ => p) atTop (𝓝 p) ∧ (∀ i : ℕ, (fun _ : ℕ => (1 : ℝ)) i = 0 ∨
      (fun _ : ℕ => (1 : ℝ)) i = 1) ∧
    ∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => (fun _ : ℕ => p) i - (fun _ : ℕ => (1 : ℝ)) i)
        η' M' N₀)) atTop atTop →
      weightedAverage (runningSumRamp (fun i => (fun _ : ℕ => p) i - (fun _ : ℕ => (1 : ℝ)) i)
        η' M' N₀) (fun _ => (1 : ℝ)) ≈ₙ fun _ => p :=
  ⟨hp0, hp1, tendsto_const_nhds, fun _ => Or.inr rfl, fun η' M' N₀ hη' htend =>
    absurd htend (runningSumRamp_const_not_divergent (by linarith : p - 1 < 0) η' M' hη' N₀)⟩

/-- **The two-sided form is false under the upward-ramp clause** (audit r2 fidelity B1): the
statement "under `signedError_core`'s hypotheses, `sup T = +∞ ∧ inf T = −∞`" — the sources'
conclusion over the Lean's clause, which round 0 had listed OPEN — has a counterexample:
`price ≡ 1/2`, `truth ≡ 1`, `p = 1/2`. Every hypothesis holds (the clause vacuously), and
`T_N = −(N + 1)/2` is bounded above by `0`. The counterexample does **not** touch the sources'
Statement 1(c′): their hypothesis (Def. 4.4.1) quantifies over *all* P-generable divergent
weightings, and the constant weighting `1` averages `truth ≡ 1` to `1 ≠ 1/2`. It shows that the
Lean's clause is strictly weaker than Def. 4.4.1 and that `signedError_core`'s conclusion is
sharp for it (the dichotomy `signedError_bddAbove_tendsto_atBot` is the most that follows).
Source: audit r2 fidelity B1 (probe `TwoSidedRefuted.lean`), lifted; [[corr-wf14-inventory]] 083 (Statement 1(c′) as stated) — refuted over the abstract clause, not over Def. 4.4.1
Kind: P
Fidelity: exact (the refutation of the round-0 open statement, its implicit arguments made explicit)
Hyps: (a) -/
theorem signedError_two_sided_refuted :
    ¬ (∀ (price truth : ℕ → ℝ) (p : ℝ), 0 < p → p < 1 →
        Tendsto price atTop (𝓝 p) → (∀ i, truth i = 0 ∨ truth i = 1) →
        (∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
          Tendsto (prefixSum (runningSumRamp (fun i => price i - truth i) η' M' N₀)) atTop atTop →
          weightedAverage (runningSumRamp (fun i => price i - truth i) η' M' N₀) truth ≈ₙ
            fun _ => p) →
        ¬ BddAbove (Set.range (prefixSum (fun i => price i - truth i))) ∧
          ¬ BddBelow (Set.range (prefixSum (fun i => price i - truth i)))) := by
  intro H
  have h := H (fun _ => (1 / 2 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) (by norm_num) (by norm_num)
    tendsto_const_nhds (fun _ => Or.inr rfl)
    (fun η' M' N₀ hη' htend => absurd htend
      (runningSumRamp_const_not_divergent (by norm_num : (1 / 2 : ℝ) - 1 < 0) η' M' hη' N₀))
  refine h.1 ⟨0, ?_⟩
  rintro _ ⟨N, rfl⟩
  show prefixSum (fun _ : ℕ => (1 / 2 : ℝ) - 1) N ≤ 0
  rw [prefixSum_const]
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/-- Weighted average of `1 − t` is `1` minus the weighted average of `t` (at nonzero mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma weightedAverage_one_sub (w t : ℕ → ℝ) {n : ℕ} (hden : prefixSum w n ≠ 0) :
    weightedAverage w (fun i => 1 - t i) n = 1 - weightedAverage w t n := by
  rw [weightedAverage_sub w (fun _ => 1) t hden, weightedAverage_const w 1 hden]

/-- Prefix sums of the negated sequence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_neg (e : ℕ → ℝ) (N : ℕ) : prefixSum (fun i => -e i) N = -prefixSum e N := by
  simp [prefixSum, Finset.sum_neg_distrib]

/-- **The mirror dichotomy** under the **downward** ramps — the ramps of the running sum of the
*negated* error, `runningSumRamp (truth − price) η' M' N₀ (N+1) = Ind_{η'}(−T_N > M')`, i.e.
`Ind_{η'}(T_N < −M')`: if the running sum is bounded below then it tends to `+∞`. Proved from
`signedError_bddAbove_tendsto_atBot` by the symmetry `price ↦ 1 − price`, `truth ↦ 1 − truth`,
`p ↦ 1 − p`, under which `T ↦ −T` and the downward ramps become the upward ones.
Source: [[corr-wf14-inventory]] 083 (the mirror half of Statement 1(c′)'s proof), pushed one step (F11)
Kind: C
Fidelity: stronger: than the mirror of `signedError_core`; one-sided (the clause has only the downward ramps)
Hyps: (a) `hprice`, `htruth`; (c) `hpseudo`: the abstract clause over the downward ramps (the mirror of `signedError_core`'s) -/
theorem signedError_bddBelow_tendsto_atTop {price truth : ℕ → ℝ} {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hprice : Tendsto price atTop (𝓝 p)) (htruth : ∀ i, truth i = 0 ∨ truth i = 1)
    (hpseudo : ∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => truth i - price i) η' M' N₀)) atTop atTop →
      weightedAverage (runningSumRamp (fun i => truth i - price i) η' M' N₀) truth ≈ₙ
        fun _ => p)
    (hB : BddBelow (Set.range (prefixSum (fun i => price i - truth i)))) :
    Tendsto (prefixSum (fun i => price i - truth i)) atTop atTop := by
  have hfun : (fun i => (1 - price i) - (1 - truth i)) = fun i => truth i - price i := by
    funext i; ring
  have hneg : (fun i => truth i - price i) = fun i => -(price i - truth i) := by
    funext i; ring
  have hpre : prefixSum (fun i => truth i - price i) =
      fun N => -prefixSum (fun i => price i - truth i) N := by
    rw [hneg]; exact funext (prefixSum_neg _)
  have hmain := signedError_bddAbove_tendsto_atBot (price := fun i => 1 - price i)
    (truth := fun i => 1 - truth i) (p := 1 - p) (by linarith) (by linarith)
    (tendsto_const_nhds.sub hprice)
    (fun i => by rcases htruth i with h | h <;> simp [h]) ?_ ?_
  · rw [hfun, hpre] at hmain
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨i, hi⟩ := tendsto_atTop_atBot.mp hmain (-b)
    exact ⟨i, fun a ha => by have := hi a ha; linarith⟩
  · intro η' M' N₀ hη' htend
    rw [hfun] at htend ⊢
    have h := hpseudo η' M' N₀ hη' htend
    have hpos := eventually_prefixSum_pos htend
    unfold AsympEq at h ⊢
    have heq : (fun N => weightedAverage (runningSumRamp (fun i => truth i - price i) η' M' N₀)
        (fun i => 1 - truth i) N - (1 - p)) =ᶠ[atTop]
        fun N => -(weightedAverage (runningSumRamp (fun i => truth i - price i) η' M' N₀)
          truth N - p) := by
      filter_upwards [hpos] with N hN
      rw [weightedAverage_one_sub _ _ hN.ne']
      ring
    have h' := h.neg
    rw [neg_zero] at h'
    exact h'.congr' heq.symm
  · rw [hfun, hpre]
    obtain ⟨b, hb⟩ := hB
    refine ⟨-b, ?_⟩
    rintro _ ⟨N, rfl⟩
    have := hb ⟨N, rfl⟩
    show -prefixSum (fun i => price i - truth i) N ≤ -b
    linarith

/-- **`signedError_bddBelow_tendsto_atTop`'s hypothesis package is consistent** (N−): at
`price ≡ p`, `truth ≡ 0` every hypothesis holds — the downward clause vacuously, since the running
sum of `truth − price ≡ −p` tends to `−∞` and no downward ramp of it has divergent mass — and
`T_N = (N + 1)·p` is bounded below by `0`. Disclosure: the conclusion `T → +∞` holds there for the
trivial reason; the mirror of `signedError_core_package_inhabited`.
Source: audit r3 adversarial N1 (probe `TrichotomyPackage.lean`, `probe_mirror_package_inhabited`), lifted and generalized to every `p`
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem signedError_mirror_package_inhabited {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < p ∧ p < 1 ∧
    Tendsto (fun _ : ℕ => p) atTop (𝓝 p) ∧
    (∀ i : ℕ, (fun _ : ℕ => (0 : ℝ)) i = 0 ∨ (fun _ : ℕ => (0 : ℝ)) i = 1) ∧
    (∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => (fun _ : ℕ => (0 : ℝ)) i - (fun _ : ℕ => p) i)
        η' M' N₀)) atTop atTop →
      weightedAverage (runningSumRamp (fun i => (fun _ : ℕ => (0 : ℝ)) i - (fun _ : ℕ => p) i)
        η' M' N₀) (fun _ => (0 : ℝ)) ≈ₙ fun _ => p) ∧
    BddBelow (Set.range (prefixSum (fun i => (fun _ : ℕ => p) i - (fun _ : ℕ => (0 : ℝ)) i))) :=
  ⟨hp0, hp1, tendsto_const_nhds, fun _ => Or.inl rfl,
   fun η' M' N₀ hη' htend => absurd htend
     (runningSumRamp_const_not_divergent (by linarith : (0 : ℝ) - p < 0) η' M' hη' N₀),
   ⟨0, by
     rintro _ ⟨N, rfl⟩
     show (0 : ℝ) ≤ prefixSum (fun _ : ℕ => p - 0) N
     rw [prefixSum_const]
     exact mul_nonneg (by positivity) (by linarith)⟩⟩

/-- **The trichotomy** (repair round 2): under `price → p ∈ (0,1)`, Boolean `truth`, and the
abstract clause over the upward **and** the downward ramps of the running sum, one of `T → −∞`,
`T → +∞`, or `T` unbounded on both sides (the statement is the disjunction; exclusivity is
trivial and not part of it). This is the sharpest consequence of the ramp clauses: its first two
cases are realized **under the two-sided clause** by F11's drift instance and its mirror
(`Drift.lean`: `signedError_trichotomy_atBot_realized`, `signedError_trichotomy_atTop_realized`,
machine-checked in repair round 3 — audit r3 adversarial B1 found that the instances the
round-2 docstring cited, `signedError_two_sided_refuted`'s and its mirror, satisfy only their
respective *one-sided* clause and violate the other), so the sources' `sup = +∞ ∧ inf = −∞` does
not follow from any clause that quantifies only over functions of the running sum (findings F11).
Case 3 under both clauses is argued (i.i.d. Bernoulli; the block-alternating stream), not built.
Source: [[corr-wf14-inventory]] 083 (Statement 1(c′)); F11
Kind: C
Fidelity: variant: trichotomy in place of the sources' two-sided conclusion, over the two-sided ramp clause
Hyps: (a) `hprice`, `htruth`; (c) `hup`, `hdown`: the abstract clauses over the upward resp. downward ramps -/
theorem signedError_trichotomy {price truth : ℕ → ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hprice : Tendsto price atTop (𝓝 p)) (htruth : ∀ i, truth i = 0 ∨ truth i = 1)
    (hup : ∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => price i - truth i) η' M' N₀)) atTop atTop →
      weightedAverage (runningSumRamp (fun i => price i - truth i) η' M' N₀) truth ≈ₙ
        fun _ => p)
    (hdown : ∀ (η' M' : ℚ) (N₀ : ℕ), 0 < η' →
      Tendsto (prefixSum (runningSumRamp (fun i => truth i - price i) η' M' N₀)) atTop atTop →
      weightedAverage (runningSumRamp (fun i => truth i - price i) η' M' N₀) truth ≈ₙ
        fun _ => p) :
    Tendsto (prefixSum (fun i => price i - truth i)) atTop atBot ∨
      Tendsto (prefixSum (fun i => price i - truth i)) atTop atTop ∨
      (¬ BddAbove (Set.range (prefixSum (fun i => price i - truth i))) ∧
        ¬ BddBelow (Set.range (prefixSum (fun i => price i - truth i)))) := by
  by_cases hA : BddAbove (Set.range (prefixSum (fun i => price i - truth i)))
  · exact Or.inl (signedError_bddAbove_tendsto_atBot hp0 hp1 hprice htruth hup hA)
  · by_cases hB : BddBelow (Set.range (prefixSum (fun i => price i - truth i)))
    · exact Or.inr (Or.inl (signedError_bddBelow_tendsto_atTop hp0 hp1 hprice htruth hdown hB))
    · exact Or.inr (Or.inr ⟨hA, hB⟩)

/-! ## C. The FAF layer: the weighting as a feature, the certificate OPEN -/

/-- **The running sum as a feature**: `∑_{i ≤ N} (price (φ (i+1)) (i+1) − const (c i))`, with
`c i` the feedback value of the verdict at the deferred day `i + 1` (`FeedbackTruthComputation.
value` at `succDeferral`).
Source: mandate T6 (the repair: "the affine feature `∑_{i ≤ N} (EF.price (φ (f i)) (f i) − EF.const (truth (f i)))`")
Kind: D
Fidelity: exact (at `succDeferral`)
Hyps: n/a -/
def runningSumFeature (φ : ℕ → Sentence) (c : ℕ → ℚ) : ℕ → EF
  | 0 => EF.add (EF.price (φ 1) 1) (EF.const (-c 0))
  | N + 1 => EF.add (runningSumFeature φ c N)
      (EF.add (EF.price (φ (N + 2)) (N + 2)) (EF.const (-c (N + 1))))

/-- The running-sum feature denotes the running sum of `price (i+1) (φ (i+1)) − c i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma runningSumFeature_denote (φ : ℕ → Sentence) (c : ℕ → ℚ) (P : History) (N : ℕ) :
    (runningSumFeature φ c N).denote P =
      prefixSum (fun i => P (i + 1) (φ (i + 1)) - (c i : ℝ)) N := by
  induction N with
  | zero => simp [runningSumFeature, prefixSum, sub_eq_add_neg]
  | succ N ih =>
    rw [prefixSum_succ, ← ih]
    simp [runningSumFeature]
    ring

/-- The one-day shift of a real weighting: `shift v 0 = 0`, `shift v (i+1) = v i` — the day-`m`
weight is the index-`(m−1)` weight of the core (the core pairs index `i` with day `i + 1`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def shift (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => v i

/-- `prefixSum (shift v) (M+1) = prefixSum v M`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_shift (v : ℕ → ℝ) (M : ℕ) : prefixSum (shift v) (M + 1) = prefixSum v M := by
  unfold prefixSum
  rw [Finset.sum_range_succ']
  simp [shift]

/-- `prefixSum (fun m => shift v m * t m) (M+1) = prefixSum (fun i => v i * t (i+1)) M`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_shift_mul (v t : ℕ → ℝ) (M : ℕ) :
    prefixSum (fun m => shift v m * t m) (M + 1) = prefixSum (fun i => v i * t (i + 1)) M := by
  unfold prefixSum
  rw [Finset.sum_range_succ']
  simp [shift]

/-- The weighted average along the shifted weighting at day `M + 1` is the core's weighted
average at index `M`, with `truth` read one day ahead.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma weightedAverage_shift (v t : ℕ → ℝ) (M : ℕ) :
    weightedAverage (shift v) t (M + 1) = weightedAverage v (fun i => t (i + 1)) M := by
  unfold weightedAverage
  rw [prefixSum_shift, prefixSum_shift_mul]

/-- **The ramp-of-the-running-sum weighting as a feature progression, by day**: `W_0 := W_1 := 0`,
`W_{N+2} := 1[N ≥ N₀]·rampFeature η' (runningSum N) (const M')` — the weight of the day
`N + 2 = succDeferral (N + 1)` is the ramp of the running sum through index `N`, as in the
sources' `v_{f(N+1)} := 1[T_N > M']`.
Source: mandate T6 (the repair)
Kind: D
Fidelity: variant: ramp of width `η'`; finite cutoff `N₀`
Hyps: n/a -/
def runningSumRampFeature (φ : ℕ → Sentence) (c : ℕ → ℚ) (η' M' : ℚ) (N₀ : ℕ) : ℕ → EF
  | 0 => EF.const 0
  | 1 => EF.const 0
  | N + 2 => if N₀ ≤ N then rampFeature η' (runningSumFeature φ c N) (EF.const M') else EF.const 0

/-- The feature weighting denotes the shift of the real weighting `runningSumRamp` at the
inductor's prices and the feedback values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma runningSumRampFeature_denote (φ : ℕ → Sentence) (c : ℕ → ℚ) {η' : ℚ} (hη' : 0 < η')
    (M' : ℚ) (N₀ : ℕ) (P : History) :
    (fun m => (runningSumRampFeature φ c η' M' N₀ m).denote P) =
      shift (runningSumRamp (fun i => P (i + 1) (φ (i + 1)) - (c i : ℝ)) η' M' N₀) := by
  funext m
  match m with
  | 0 => simp [runningSumRampFeature, shift]
  | 1 => simp [runningSumRampFeature, shift, runningSumRamp]
  | N + 2 =>
    simp only [runningSumRampFeature, shift, runningSumRamp]
    split_ifs
    · rw [rampFeature_denote hη', runningSumFeature_denote]
      simp
    · simp

/-- **The generability certificate of the running-sum ramp — OPEN** (T6's certificate, listed in
`corr-li-shutdown-open.txt`): a `MachineSpliceStream` for a growing affine sum of price features
with digits read from the feedback computation `C` (model: FAF's `FeedbackTraderEmissionSigns`
emission in `Construction/Statistics/FeedbackTruth.lean`). Not built within budget; everything
above it is proved and everything below it rests on it (`partial`). **Deprioritized after
audit r1 (F17):** the only consumer, `signedError_unbounded`, has an unsatisfiable hypothesis
package, so proving this certificate completes a vacuous theorem; the statement itself (a
generability certificate) remains a legitimate open step, and the same-day digit-reading
sub-construction is `Collision.lean`'s `sameDayW_pgenerable`.
Source: mandate T6 ("this is the certificate: a `MachineSpliceStream` of a growing affine sum with digits read from `C`")
Kind: OPEN
Fidelity: n/a
Hyps: (b) `C` -/
theorem runningSumRampFeature_pgenerable (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    {truth : ℕ → ℝ} (C : FeedbackTruthComputation truth succDeferral) (η' M' : ℚ) (N₀ : ℕ) :
    PGenerableWeighting (runningSumRampFeature φ C.value η' M' N₀) := by
  sorry

/-- Any `[0,1]` weighting is `succDeferral`-patient with constant `2`.
Source: none: infrastructure (mandate known issue 3)
Kind: L
Fidelity: n/a -/
lemma deferralPatient_succ {W : ℕ → EF} {P : History}
    (hmem : ∀ n, 0 ≤ (W n).denote P ∧ (W n).denote P ≤ 1) :
    DeferralPatient succDeferral W P := by
  refine ⟨2, fun n => ?_⟩
  have hIcc : Finset.Icc n (succDeferral n) = {n, n + 1} := by
    show Finset.Icc n (n + 1) = {n, n + 1}
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hIcc, Finset.sum_pair (by omega)]
  linarith [(hmem n).2, (hmem (n + 1)).2]

/-- **Statement 1(c′) over FAF — VACUOUS as stated** (T6, the FAF-facing form; F17, audit r1
fidelity B1: the hypotheses `hpseudo` and `C` are jointly unsatisfiable,
`signedError_unbounded_package_unsat` in `Collision.lean`; also `partial`: rests on the OPEN
certificate `runningSumRampFeature_pgenerable`). Kept as the record of the mandate's route; it
proves nothing about any inductor. Statement as written: over any inductor, for an e.c. decidable family
`φ` with `TheoryTruth`, pseudorandom with frequency `p ∈ (0,1)` at `succDeferral`, with good
feedback `C`, the realized signed error `T_N := ∑_{i ≤ N} (P_{i+1}(φ_{i+1}) − truth (i+1))` is
not bounded. `thm:benford` supplies `P_{i+1}(φ_{i+1}) → p` (the deferred index is a subsequence of
the diagonal); the abstract clause of `signedError_core` is discharged by `PseudorandomFrequency`
at the feature weighting (its denotation `runningSumRampFeature_denote`, divergence from the
core, patience `deferralPatient_succ`, generability OPEN).
Source: [[corr-wf14-inventory]] 083; [[corr-wf14-2-inventory]] 2-027 (b); audit r1 fidelity B1
Kind: C
Fidelity: weaker: as `signedError_core` (F11, F1); **vacuous** (F17)
Hyps: (b) `C` (LI §4.3.8 good feedback) — at `succDeferral` it contradicts `hpseudo` (F17); the OPEN certificate -/
theorem signedError_unbounded (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) {truth : ℕ → ℝ}
    (htruth : AffineCombination.TheoryTruth φ DP truth) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hpseudo : PseudorandomFrequency truth p succDeferral P)
    (C : FeedbackTruthComputation truth succDeferral)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ (BddAbove (Set.range (prefixSum (fun i => P (i + 1) (φ (i + 1)) - truth (i + 1)))) ∧
        BddBelow (Set.range (prefixSum (fun i => P (i + 1) (φ (i + 1)) - truth (i + 1))))) := by
  -- `thm:benford` on the diagonal, shifted by one
  have hdiag := lic_learning_pseudorandom_frequency P DP φ hφ truth htruth p ⟨hp0.le, hp1.le⟩
    hworld succDeferral hpseudo
  have hprice : Tendsto (fun i => P (i + 1) (φ (i + 1))) atTop (𝓝 p) := by
    have h := (tendsto_sub_nhds_zero_iff.mp hdiag).comp (tendsto_add_atTop_nat 1)
    exact h
  have htruthB : ∀ i, truth (i + 1) = 0 ∨ truth (i + 1) = 1 :=
    fun i => htruth.isBoolean hworld (i + 1)
  -- the feedback values are the truths at the deferred days
  have hc : ∀ i, ((C.value i : ℚ) : ℝ) = truth (i + 1) := fun i => C.agrees i
  have hcfun : (fun i => P (i + 1) (φ (i + 1)) - ((C.value i : ℚ) : ℝ)) =
      fun i => P (i + 1) (φ (i + 1)) - truth (i + 1) := by
    funext i; rw [hc]
  refine signedError_core (price := fun i => P (i + 1) (φ (i + 1)))
    (truth := fun i => truth (i + 1)) hp0 hp1 hprice htruthB ?_
  intro η' M' N₀ hη' hdiv
  have hden := runningSumRampFeature_denote φ C.value hη' M' N₀ P
  rw [hcfun] at hden
  set v := runningSumRamp (fun i => P (i + 1) (φ (i + 1)) - truth (i + 1)) η' M' N₀ with hv
  have hvmem := runningSumRamp_mem (fun i => P (i + 1) (φ (i + 1)) - truth (i + 1)) η' M' N₀
  have hmem : ∀ n, 0 ≤ (runningSumRampFeature φ C.value η' M' N₀ n).denote P ∧
      (runningSumRampFeature φ C.value η' M' N₀ n).denote P ≤ 1 := by
    intro n
    rw [show (runningSumRampFeature φ C.value η' M' N₀ n).denote P = shift v n from
      congrFun hden n]
    cases n with
    | zero => simp [shift]
    | succ i => exact hvmem i
  have hdivW : DivergentWeighting (runningSumRampFeature φ C.value η' M' N₀) P := by
    refine ⟨hmem, ?_⟩
    rw [hden]
    have hmono : Monotone (prefixSum (shift v)) := prefixSum_mono_of_nonneg fun i => by
      cases i with
      | zero => simp [shift]
      | succ i => exact (hvmem i).1
    rw [tendsto_atTop_atTop] at hdiv ⊢
    intro K
    obtain ⟨N, hN⟩ := hdiv K
    refine ⟨N + 1, fun n hn => ?_⟩
    calc K ≤ prefixSum v N := hN N le_rfl
      _ = prefixSum (shift v) (N + 1) := (prefixSum_shift v N).symm
      _ ≤ prefixSum (shift v) n := hmono hn
  have h := hpseudo _ (runningSumRampFeature_pgenerable φ hφ C η' M' N₀) hdivW
    (deferralPatient_succ hmem)
  rw [hden] at h
  -- reindex: day `M + 1` ↔ index `M`
  have h' := (tendsto_sub_nhds_zero_iff.mp h).comp (tendsto_add_atTop_nat 1)
  refine tendsto_sub_nhds_zero_iff.mpr ?_
  refine h'.congr fun M => ?_
  simp only [Function.comp, weightedAverage_shift]

end Cleanroom.Corrigibility.CorrLiShutdown
