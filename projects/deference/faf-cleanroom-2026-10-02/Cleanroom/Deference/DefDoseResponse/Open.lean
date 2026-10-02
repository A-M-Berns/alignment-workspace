import Cleanroom.Deference.DefDoseResponse.Steering
import Cleanroom.Deference.DefDoseResponse.Thinned
import Cleanroom.Fa.FaForcingTrader.Schedule
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `def-dose-response` · Open: the open statements of record

* **T2.OPEN — the two-way closure of T2(b)/(c)** (`twoWay_closure_exists`): the stream the arms
  read *is* the quote stream of an advisor who reads arm 1 — the coupled fixed point, under the
  design's admissibility hypotheses (computable base/coin, `γ ∈ (0,1)`, `v ∈ [0,1]` mesh-exact on
  every steering day — added in repair round 1: without them the statement was refutable at
  `v = 2`; a computable publication schedule `σ` for the mirror ledger, and `0 < N` — added in
  repair round 2: without the first the statement was refutable at a non-computable `σ`, B2 of
  both r2 audits, and at `N = 0` it was about the junk arm). Everything in T2 (a)/(b-half)/(d)/(e)
  is one-way and does not need it. Status `partial: over the OPEN pair`; pointer
  `li-coupled-pair`. Stated, not attempted.
* **T7.1 — unrestricted thinned forcing** (`unrestricted_thinned_forcing`): T1's summability
  display with no schedule — over the T1 package *minus* `WindowDisjoint`, the exposure-thinned
  doubly-soft violation weight is summable over all days. Shared with
  [[faithful-acceleration]] §5's boxed claim; the thinning step "to a sparse schedule with
  divergent sum" is unavailable in general. Three N+ rows say exactly what fails and what does
  not: `harmonic_summable_on_dyadic_cover` (the cover remark: a divergent series summable on every
  member of a countable sparse cover), `harmonic_summable_on_every_doubling_schedule` /
  `thinning_step_fails_at_doubling` (at a lookahead `f n ≥ 2n + 1`, *every* window-disjoint
  schedule carries summable harmonic mass — the step has no instance), and
  `harmonic_not_summable_on_linearSchedule_zero` (at bounded lag the even days carry divergent
  harmonic mass — the step is available there). Lookahead speed, not sparsity, is the obstacle.
* **(β)**, the pseudorandom-coin reading of T1 through a delayed-feedback design, is *recorded*
  in the findings (F1, F-β), not stated here: the mandate's own analysis says the natural builder
  is not causal for the delay it needs, so there is no precise believed-true statement to list.

Each OPEN carries `sorry` and is listed in `def-dose-response-open.txt` with its reason.
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaForcingTrader
  Cleanroom.Fa.FaTheoremA
open Filter Topology

/-! ## T2.OPEN — the two-way closure -/

/-- **OPEN (T2.OPEN): the two-way closure of the steered system.** Under the admissibility of the
design — computable `base`, `baseA` and coin, `γ ∈ (0,1)`, a target `v ∈ [0,1]` that is exact at
every steering mesh (`v = k/(n+1)` for each `n < N`, which is what D4's steered advisor can
deliver exactly, `steeredAdvisor_quote_exact`; F6) — there is a committed stream `a`, a market
program `M` for the production arm built on `a`, and an inductor `A` over the mirror ledger of
that arm (with a market program `MA`) whose steered prefix is `v` and whose quote stream *is* `a`
— the stream the arms read is the quotes of the advisor who reads arm 1. Scope: **two-way** (the
coupled fixed point). Neither proved nor refuted here *as now stated* (the `v`-free form of
round 0 and the `σ`-free form of round 1 were refuted — below); `li-coupled-pair` owns the pair.

*Why the hypotheses (repair round 1, B1 of both audits; repair round 2, B2 of both audits).* As
first stated, with `v : ℚ` free, the statement was **false**: the quote stream is `[0,1]`-valued
(`quoteStream_mem`), so at `v = 2`, `N = 1` the existential fails (the r1 audits' probes
`TwoWayRange.lean` / `TwoWayClosureRange.lean`). `MarketComputation` carries `price_mem_Icc` and
`IsLogicalInductor` carries `processComputable`, so a non-computable `base`/`baseA`/`c` or a `γ`
outside `(0,1)` also makes a conjunct impossible. After round 1 the mirror ledger's publication
schedule `σ` was still free, and `processComputable` forces the mirror ledger
`ledgerProcess baseA (realizedExpectation M protX f) σ` to be a computable process for *every*
`σ` (the r2 fidelity audit's probe `TwoWaySigmaForcing.lean`); a `σ` whose item-`0` publication
stage encodes a non-recursive set (`e n = n` if `n ∈ K`, else `n + 1`) puts the day-`n` item-`0`
literal in stage `n` iff `n ∈ K`, so that ledger is not computable, no inductor exists over it,
and the existential fails — `hσ` below is exactly the hypothesis `li-quote-lane`'s
`ledgerProcess_computable` / `mirrorPair_inductor` take, satisfied by the witnesses'
`armSchedule` (`armSchedule_computable`). `0 < N` is carried as every evaluating T2 row carries
it: at `N = 0` the arm's weight is the junk value `½ − γ/2` (`testimony` divides by `N`). The
hypotheses are now those of `arm_isLogicalInductor` / `arm_computableMarket`, the mirror pair's
own schedule hypothesis, the mesh-exactness `quoteStream_steeredAdvisor_exact` needs, and
`0 < N`.

*Why it is not trivially satisfiable.* By T2(b-half) (`production_quote_tendsto`) *every*
inductor `A` over the mirror ledger of the arm built on `a` has quote stream converging to
`½ + γ(v − ½)·p̂`, so a solution `a` must converge there too: the fixed point is a genuine
coupling of the arm's destination with the stream it is built on, not a free choice. The
one-way halves are proved (`steeredAdvisor_quote_exact` for the prefix, `mirror_quote_tendsto`
for the limit); what is open is the exact-at-every-day identity `quoteStream MA = a` with `MA`'s
market reading the arm built on that very `a`.
Source: [[dose-response]] §2.3 ("coupled existence by the one-stage-delay recursion"), §6.3 T2(b)/(c); mandate T2 (b)/(c) two-way closure; `li-coupled-pair`
Kind: OPEN
Fidelity: exact (the coupled statement, under the design's admissibility hypotheses)
Hyps: n/a (OPEN) -/
theorem twoWay_closure_exists {base baseA : DeductiveProcess}
    (hbase : ComputableDeductiveProcess base) (hbaseA : ComputableDeductiveProcess baseA)
    {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (N : ℕ) (hN : 0 < N) {v : ℚ} (hv01 : 0 ≤ v ∧ v ≤ 1)
    (hmesh : ∀ n < N, ∃ k ≤ n + 1, v = (k : ℚ) / ((n : ℚ) + 1))
    {c : ℕ → Bool} (hc : Computable c) (f : DeferralFunction) (σ : ℕ → PublicationSchedule)
    (hσ : Computable fun p : ℕ × ℕ => (σ p.1).e p.2) :
    ∃ (a : ℕ → ℚ) (M : MarketComputation (arm base γ N c a)) (A : History)
      (MA : MarketComputation A),
      IsLogicalInductor A (ledgerProcess baseA (realizedExpectation M protX f) σ) ∧
        (∀ j < N, quoteStream MA j = v) ∧ ∀ n, quoteStream MA n = a n := by
  sorry

/-! ## T7.1 — unrestricted thinned forcing -/

/-- **The exposure-thinned violation weight on all days**: `c_n · dsWeight(t, ε, δ; a_n, 𝔼^H_n(X_n))`
— the note's `w_n` with no schedule.
Source: [[dose-response]] §5 ("the thinned doubly-soft violation weight `w_n`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def thinnedViolation (C : ℕ → EF) (A H : History) (X Y : ℕ → LUV) (t ε : ℚ)
    (δ : ℚ) (n : ℕ) : ℝ :=
  (C n).denote A * dsWeight t ε δ (quoteSeq Y A n) ((X n).expect H n)

/-- **OPEN (T7.1): unrestricted thinned forcing.** Over the T1 package *without* a schedule (no
`WindowDisjoint`), the exposure-thinned violation weight is summable over all of `ℕ`. The
note records it open (§8 problem 1); the obligation is shared with [[faithful-acceleration]]
§5's boxed claim, whose thinning step "thin to a sparse schedule, still with divergent sum" is
unavailable in general: at a doubling lookahead *every* window-disjoint schedule carries summable
harmonic mass (`harmonic_summable_on_every_doubling_schedule`), while at bounded lag the step is
available (`harmonic_not_summable_on_linearSchedule_zero`). The legibility of the unrestricted
weight on `H` is carried as the (c) `hL` it would need. Scope: one-way. Day index: the Lean
`(X n).expect H n` is the note's `𝔼^H_{n+1}(X)` (FAF's convention, Lean day `n` = paper day
`n+1`, as `fa-forcing-trader`'s `violW`).
Source: [[dose-response]] §5 Remark ("the display at `S = ℕ` … remains **open**"), §8 problem 1; anson-057; [[faithful-acceleration]] §5
Kind: OPEN
Fidelity: exact (the note's unrestricted display, over the e.c. exposure indicator)
Hyps: n/a (OPEN; (c) `pkg.reflected`, (c) `hL` would be carried) -/
theorem unrestricted_thinned_forcing {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {C : ℕ → EF} (hC : ExposureIndicator A C) (t ε : ℚ) (hε : 0 < ε) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (thinnedViolation C A H X Y t ε δ)) :
    Summable (thinnedViolation C A H X Y t ε δ) := by
  sorry

/-! ## N+: a divergent series summable on every member of a countable sparse cover -/

/-- The dyadic cover: member `j` of schedule `k` is the day `2^j + k`. Each schedule is strictly
increasing with gaps `2^j`, so it is window-disjoint for `succDeferral` from `j ≥ 1`; and every
day `n ≥ 1` is `2^j + k` for `j := ⌊log₂ n⌋`, `k := n − 2^j`.
Source: [[dose-response]] §5 Remark ("a divergent series can converge on every member of a countable sparse cover"); mandate T7.1
Kind: D
Fidelity: exact
Hyps: n/a -/
def dyadicCover (k j : ℕ) : ℕ := 2 ^ j + k

/-- The dyadic cover covers every positive day.
Source: mandate T7.1 (the cover)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dyadicCover_covers (n : ℕ) (hn : 1 ≤ n) : ∃ k j, dyadicCover k j = n := by
  refine ⟨n - 2 ^ Nat.log 2 n, Nat.log 2 n, ?_⟩
  unfold dyadicCover
  have h := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  omega

/-- Each schedule of the dyadic cover is strictly increasing.
Source: mandate T7.1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dyadicCover_strictMono (k : ℕ) : StrictMono (dyadicCover k) := by
  intro i j hij
  unfold dyadicCover
  have : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) hij
  omega

/-- **N+ (the cover remark behind T7.1): the harmonic series diverges but is summable along every
schedule of the dyadic cover.** This defeats the *pigeonhole-over-a-cover* justification of "thin
to a sparse schedule, still with divergent sum": a weight can be non-summable overall and
summable on each of countably many sparse schedules covering the days. It does **not** by itself
show the thinning step fails — the even days are `succ`-sparse and carry divergent harmonic mass
(`harmonic_not_summable_on_linearSchedule_zero`); what refutes the step is lookahead speed,
`harmonic_summable_on_every_doubling_schedule` (repair round 1, N2 of both audits).
Source: [[dose-response]] §5 Remark; [[faithful-acceleration]] §5 (the thinning step); mandate T7.1
Kind: N+
Fidelity: exact (the cover remark; the step's failure is the next theorem)
Hyps: (a) none -/
theorem harmonic_summable_on_dyadic_cover :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ∧
      ∀ k, Summable (fun j : ℕ => (1 : ℝ) / ((dyadicCover k j : ℝ) + 1)) := by
  constructor
  · intro hs
    apply Real.not_summable_one_div_natCast
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
      refine hs.congr fun n => ?_
      push_cast
      rfl
    exact (summable_nat_add_iff 1).mp h2
  · intro k
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) summable_geometric_two
    unfold dyadicCover
    rw [one_div_pow]
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    have : (0 : ℝ) ≤ k := by positivity
    linarith

/-- **N+ (the thinning step fails at a doubling lookahead).** For a lookahead `f` with
`2n + 1 ≤ f n`, window-disjointness `f (d k) < d (k+1)` forces `2 d_k < d_{k+1}`, hence
`d_k + 1 ≥ 2^k`, so along **every** `f`-window-disjoint schedule the harmonic weights are
summable although `∑ 1/(n+1)` diverges (`harmonic_summable_on_dyadic_cover.1`). So "thin to a
sparse schedule, still with divergent sum" has no instance at such a lookahead: the row of record
behind T7.1 (repair round 1, N2 of both audits; the fidelity audit's probe `DoublingSchedule.lean`).
Source: [[dose-response]] §5 Remark; [[faithful-acceleration]] §5 (the thinning step); mandate T7.1
Kind: N+
Fidelity: exact (over `fa-forcing-trader`'s `WindowDisjoint`)
Hyps: (a) none -/
theorem harmonic_summable_on_every_doubling_schedule {f d : DeferralFunction}
    (hf : ∀ n, 2 * n + 1 ≤ f.f n) (hwd : WindowDisjoint f d) :
    Summable (fun k : ℕ => (1 : ℝ) / ((d.f k : ℝ) + 1)) := by
  have hk : ∀ k, 2 ^ k ≤ d.f k + 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hwd.2 k
      have h2 := hf (d.f k)
      rw [pow_succ]
      omega
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) summable_geometric_two
  rw [one_div_pow]
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast hk k

/-- **The thinning step fails outright at a doubling lookahead**: the harmonic series diverges,
yet no `f`-window-disjoint schedule carries a divergent harmonic sum when `2n + 1 ≤ f n`.
Source: [[dose-response]] §5 Remark; [[faithful-acceleration]] §5; mandate T7.1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem thinning_step_fails_at_doubling {f : DeferralFunction} (hf : ∀ n, 2 * n + 1 ≤ f.f n) :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ∧
      ∀ d : DeferralFunction, WindowDisjoint f d →
        Summable (fun k : ℕ => (1 : ℝ) / ((d.f k : ℝ) + 1)) :=
  ⟨harmonic_summable_on_dyadic_cover.1, fun _ hwd =>
    harmonic_summable_on_every_doubling_schedule hf hwd⟩

/-- **The doubling lookahead is inhabited** by a `DeferralFunction` FAF admits:
`fa-forcing-trader`'s `linearSchedule 0` has `f n = 2n + 2 ≥ 2n + 1`, so the two rows above have
an instance and are not vacuous over FAF's `graph_fp` certificate (adversarial audit r2 N3, its
probe `DoublingInhabited.lean`). `linearSchedule 0` plays two roles in this file: the lookahead
`f` here, the schedule `d` in `harmonic_not_summable_on_linearSchedule_zero`.
Source: mandate T7.1; adversarial audit r2 N3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem linearSchedule_zero_doubling : ∀ n, 2 * n + 1 ≤ (linearSchedule 0).f n := by
  intro n
  rw [linearSchedule_apply]
  omega

/-- **The thinning step fails at a lookahead FAF's `DeferralFunction` admits**: at the lookahead
`linearSchedule 0`, no window-disjoint schedule carries a divergent harmonic sum.
Source: mandate T7.1; adversarial audit r2 N3
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem thinning_step_fails_at_linearSchedule_zero :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ∧
      ∀ d : DeferralFunction, WindowDisjoint (linearSchedule 0) d →
        Summable (fun k : ℕ => (1 : ℝ) / ((d.f k : ℝ) + 1)) :=
  thinning_step_fails_at_doubling linearSchedule_zero_doubling

/-- **The converse at bounded lag**: for the successor lookahead the step *is* available — the
even days `linearSchedule 0` (`2, 4, 6, …`) are `succ`-window-disjoint
(`windowDisjoint_succ_linear 0`) and carry divergent harmonic mass (`1/(2k+3) ≥ (1/3)/(k+1)`).
So the failure of the thinning step is a fact about lookahead speed, not about sparsity.
Source: [[dose-response]] §5 Remark; mandate T7.1; repair round 1 (fidelity N2's pigeonhole remark, made concrete)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem harmonic_not_summable_on_linearSchedule_zero :
    ¬ Summable (fun k : ℕ => (1 : ℝ) / (((linearSchedule 0).f k : ℝ) + 1)) := by
  intro hs
  apply harmonic_summable_on_dyadic_cover.1
  have h3 : Summable (fun k : ℕ => (1 / 3 : ℝ) * (1 / ((k : ℝ) + 1))) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
    rw [linearSchedule_apply]
    push_cast
    rw [← mul_div_assoc, mul_one, div_div]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have := h3.mul_left 3
  refine this.congr fun k => ?_
  ring

end Cleanroom.Deference.DefDoseResponse
