import Cleanroom.Corrigibility.CorrLiShutdown.Calibrated

/-!
# `corr-li-shutdown` — Dichotomy (T5): the defiance dichotomy, split by ledger

(⇒) `infinite_defiance_certifies`: infinite defiance mass makes `u^def` a divergent press class
that is world-mostly-false at the margin (T4(a) repackaged). (⇐)
`mostly_false_forces_defiance`: if **some** generable divergent press class `v` is mostly
false on the **hybrid** ledger (`limsup ρ^h_v ≤ q − η`), then for every margin `δ ≤ η/4` the
defiance mass `∑ u^def_n` diverges. The engine is the **mass-fraction lemma**
(`mass_fraction`, P, real sequences): a weighted average of `[0,1]` values `≤ s < t` puts at
least a `(t − s)/t` fraction of the mass on values `< t`; on those days the credence ramp in
`u^def` is saturated and `π̃ ≥ v`, so `u^def ≥ v` there. Corollary 4.1 (J2 in LI form) is the
contrapositive; Corollary 4.3 is the limit of the compliance threshold; T3's base-rate identity
(`rho_mul_mass` in sum form, `rho_eq_posterior` with the class frequencies `ε, α, β` defined,
`posterior_ge_iff_odds` the abstract arithmetic, `rho_ge_q_iff_odds` their composition) closes
the file.

Scope: one-way; the (⇐) hypothesis is on the hybrid ledger (a press class may contain heeded
days); averaged grade; `v := u^def` in (⇐) would be circular and is not what is proved.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.CorrThreeStep
open Filter Topology Finset

/-! ## A. Real-sequence lemmas -/

/-- **The mass-fraction lemma** (the named machine-check candidate of T5): for nonnegative
weights `w` and nonnegative values `x`, if the weighted sum through `N` is at most `s` times the
mass, then the mass on `{i : x i < t}` is at least `((t − s)/t)` of the total, for every `t > s`
with `0 < t`. (No division: stated as `(t − s)·M ≤ t·L`.)
Source: [[corr-wf14-inventory]] 087 (`li-final.md` Statement 4(⇐), "the mass `B_k` of days with credence `≥ q − η/2` …")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem mass_fraction {w x : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) {N : ℕ} {s t : ℝ}
    (hsum : prefixSum (fun i => w i * x i) N ≤ s * prefixSum w N) :
    (t - s) * prefixSum w N ≤ t * prefixSum (fun i => if x i < t then w i else 0) N := by
  -- split the mass into the low part `L` and the high part `B`
  have hsplit : prefixSum w N =
      prefixSum (fun i => if x i < t then w i else 0) N +
        prefixSum (fun i => if x i < t then 0 else w i) N := by
    rw [← prefixSum_add]
    unfold prefixSum
    apply Finset.sum_congr rfl
    intro i _
    show w i = (if x i < t then w i else 0) + (if x i < t then 0 else w i)
    split_ifs <;> simp
  -- the high part is dominated by the weighted sum: `t·B ≤ ∑ w x`
  have hB : t * prefixSum (fun i => if x i < t then 0 else w i) N ≤
      prefixSum (fun i => w i * x i) N := by
    unfold prefixSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · simp only [mul_zero]; exact mul_nonneg (hw i) (hx i)
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (not_lt.mp hi) (hw i)
  have key : t * prefixSum (fun i => if x i < t then 0 else w i) N ≤ s * prefixSum w N :=
    hB.trans hsum
  calc (t - s) * prefixSum w N = t * (prefixSum (fun i => if x i < t then w i else 0) N +
        prefixSum (fun i => if x i < t then 0 else w i) N) - s * prefixSum w N := by
        rw [hsplit]; ring
    _ ≤ t * prefixSum (fun i => if x i < t then w i else 0) N := by
        have : t * (prefixSum (fun i => if x i < t then w i else 0) N +
            prefixSum (fun i => if x i < t then 0 else w i) N) =
            t * prefixSum (fun i => if x i < t then w i else 0) N +
              t * prefixSum (fun i => if x i < t then 0 else w i) N := by ring
        linarith [key, this]

/-- Prefix sums of a nonnegative sequence are monotone.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_mono_of_nonneg {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) : Monotone (prefixSum w) := by
  intro a b hab
  induction b with
  | zero =>
    have : a = 0 := Nat.le_zero.mp hab
    subst this; exact le_rfl
  | succ k ih =>
    rcases Nat.of_le_succ hab with h | h
    · exact (ih h).trans (by rw [prefixSum_succ]; linarith [hw (k + 1)])
    · subst h; exact le_rfl

/-- A monotone sequence that frequently dominates `c · M N` for a sequence `M → ∞` and `c > 0`
tends to `∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_atTop_of_frequently_ge {u M : ℕ → ℝ} (hu : Monotone u) {c : ℝ} (hc : 0 < c)
    (hM : Tendsto M atTop atTop) (hfreq : ∃ᶠ N in atTop, c * M N ≤ u N) :
    Tendsto u atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  have hev : ∀ᶠ N in atTop, K / c ≤ M N := tendsto_atTop.mp hM (K / c)
  obtain ⟨N₁, hN₁, hK⟩ := (hfreq.and_eventually hev).exists
  refine ⟨N₁, fun N hN => ?_⟩
  have : K ≤ c * M N₁ := by
    rw [div_le_iff₀ hc] at hK
    linarith [hK]
  exact this.trans (hN₁.trans (hu hN))

/-! ## B. T5: the dichotomy -/

/-- **(⇒) Infinite defiance certifies a world-mostly-false press class** (T5(⇒), Statement 4(⇒)):
if the defiance mass `∑ u^def_n` diverges, then `u^def` is a generable press class with divergent
mass and (T4(a)) `liminf ρ^w_{u^def} ≤ q − δ` — the world ledger, since the support is the
agent's defied days. Scope: one-way; averaged grade.
Source: [[corr-wf14-inventory]] 087 (Statement 4(⇒)); [[corr-wf14-2-inventory]] 2-035 (the reading)
Kind: L
Fidelity: weaker: as `defiance_calibrated`
Hyps: (a); (c) world-ledger reading of `truth` -/
theorem infinite_defiance_certifies (S : ShutdownPair) (q : ℚ) {δ : ℚ} (hδ : 0 < δ)
    {truth : ℕ → ℝ} (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hmass : Tendsto (prefixSum (realized S (uDef S q δ))) atTop atTop) :
    PressClass S q δ (uDef S q δ) ∧ DivergentWeighting (uDef S q δ) S.agent ∧
      ∀ ε > 0, ∃ᶠ N in atTop, rho (realized S (uDef S q δ)) truth N ≤ (q : ℝ) - δ + ε := by
  have hdiv : DivergentWeighting (uDef S q δ) S.agent :=
    ⟨fun n => uDef_mem_Icc S hδ q n S.agent, hmass⟩
  exact ⟨uDef_pressClass S q hδ, hdiv, defiance_calibrated S q hδ htruth hdiv⟩

/-- **(⇐) A mostly-false press class forces infinite defiance** (T5(⇐), Statement 4(⇐)): if some
generable divergent press class `v` has `limsup_N ρ^h_v(N) ≤ q − η` (ε-form: eventually
`ρ_v(N) ≤ q − η + ε` for every `ε > 0`) — on the **hybrid** ledger, since `v` may contain heeded
days — then for every margin `δ` with `4δ ≤ η` the defiance mass `∑ u^def_n` diverges. Route:
Recurring Unbiasedness on `v` gives a subsequence with `ρ̂_v ≤ q − 3η/4`; the mass-fraction
lemma puts a fixed fraction of `v`'s mass on days with `A_i(φ_i) < q − η/2 ≤ q − 2δ`, where the
credence ramp of `u^def` is saturated and `π̃_i ≥ v_i`; so `u^def ≥ v` on that fraction and its
prefix sums diverge. Needs `0 < q` and `η ≤ q` (so that `q − η/2 > 0`), both stated.
Scope: one-way; averaged grade; hybrid ledger.
Source: [[corr-wf14-inventory]] 087 (Statement 4(⇐), "checked by the adversary by hand"); [[corr-wf14-2-inventory]] 2-035
Kind: C
Fidelity: exact (ε-form of the limsup hypothesis; the band at `q − η/2` as the source)
Hyps: (a) `hv`, `hdiv`, `htruth`, `hfalse` named; (c) hybrid-ledger reading of `truth` -/
theorem mostly_false_forces_defiance (S : ShutdownPair) {q δ η : ℚ} (hq : 0 < q) (hδ : 0 < δ)
    (hδη : 4 * δ ≤ η) (hηq : η ≤ q) {v : ℕ → EF} (hv : PressClass S q δ v)
    (hdiv : DivergentWeighting v S.agent) {truth : ℕ → ℝ}
    (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth)
    (hfalse : ∀ ε > 0, ∀ᶠ N in atTop, rho (realized S v) truth N ≤ (q : ℝ) - η + ε) :
    Tendsto (prefixSum (realized S (uDef S q δ))) atTop atTop := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hηR : (0 : ℝ) < η := by
    have : (0 : ℝ) < 4 * δ := by linarith
    have h' : ((4 * δ : ℚ) : ℝ) ≤ η := by exact_mod_cast hδη
    push_cast at h'
    linarith
  have hδηR : 4 * (δ : ℝ) ≤ η := by exact_mod_cast hδη
  have hηqR : (η : ℝ) ≤ q := by exact_mod_cast hηq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set t : ℝ := (q : ℝ) - η / 2 with ht
  have htpos : 0 < t := by rw [ht]; linarith
  -- recurring unbiasedness on `v`
  have hlp := AffineCombination.recurringunbiasedness S.φ
    (AffineCombination.sentenceAffine_polySequence S.φ S.φ_codes) hv.1 htruth hdiv S.hworld
  have hfreq := hasLimitPoint_zero_iff.mp hlp (η / 8) (by linarith)
  have hpos : ∀ᶠ N in atTop, 0 < prefixSum (realized S v) N := hdiv.eventually_prefixSum_pos
  have hfalse' := hfalse (η / 8) (by linarith)
  -- the frequent lower bound on the defiance mass
  have hbound : ∃ᶠ N in atTop,
      (η / 4 / t) * prefixSum (realized S v) N ≤ prefixSum (realized S (uDef S q δ)) N := by
    refine ((hfreq.and_eventually hfalse').and_eventually hpos).mono ?_
    rintro N ⟨⟨hb, hf⟩, hposN⟩
    have hsub := weightedBias_eq_market_sub_truth (realized S v)
      (fun i => S.agent i (S.φ i)) truth hposN.ne'
    rw [abs_lt] at hb
    -- `ρ̂_v(N) ≤ q − 3η/4`
    have hhat : weightedAverage (realized S v) (fun i => S.agent i (S.φ i)) N ≤
        (q : ℝ) - 3 * η / 4 := by
      simp only [rho] at hf
      linarith [hb.1, hb.2, hsub]
    have hsum : prefixSum (fun i => realized S v i * S.agent i (S.φ i)) N ≤
        ((q : ℝ) - 3 * η / 4) * prefixSum (realized S v) N := by
      rw [weightedAverage_eq_div hposN.ne', div_le_iff₀ hposN] at hhat
      exact hhat
    have hwv : ∀ i, 0 ≤ realized S v i := fun i => (hdiv.1 i).1
    have hmf := mass_fraction (t := t) hwv (fun i => (S.agent_mem_Icc i (S.φ i)).1) hsum
    -- on the low days, `u^def ≥ v`
    have hdom : prefixSum (fun i => if S.agent i (S.φ i) < t then realized S v i else 0) N ≤
        prefixSum (realized S (uDef S q δ)) N := by
      unfold prefixSum
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · -- saturated credence ramp, proxy dominates `v`
        have hsat : ctsInd δ ((q : ℝ) - δ) (S.agent i (S.φ i)) = 1 := by
          rw [ctsInd_eq_one_iff hδ]
          rw [ht] at hi
          linarith
        show realized S v i ≤ (uDef S q δ i).denote S.agent
        rw [uDef_denote S hδ, hsat, mul_one]
        have := hv.2 i
        rw [proxy_denote hδ] at this
        exact this
      · exact (uDef_mem_Icc S hδ q i S.agent).1
    have ht' : t - ((q : ℝ) - 3 * η / 4) = η / 4 := by rw [ht]; ring
    rw [ht'] at hmf
    rw [div_mul_eq_mul_div, div_le_iff₀ htpos]
    have hprod := mul_le_mul_of_nonneg_left hdom htpos.le
    linarith [hmf, hdom, hprod]
  exact tendsto_atTop_of_frequently_ge
    (prefixSum_mono_of_nonneg fun i => (uDef_mem_Icc S hδ q i S.agent).1)
    (div_pos (by linarith) htpos) hdiv.2 hbound

/-- **Corollary 4.1 — J2 in LI form** (the (⇐) contrapositive): if the defiance mass is bounded,
then **no** generable divergent press class is mostly false on the hybrid ledger at any margin
`η ≥ 4δ` with `η ≤ q`: for every such class, `ρ^h_v(N) > q − η + ε` infinitely often for some
`ε`. This is the LI rendering of "the overseers' false-press rate falls at least as fast as the
agent's error rate": rate-free, class-relative, averaged grade.
Source: [[corr-wf14-inventory]] 087 (Corollary 4.1); [[corr-wf14-2-inventory]] 2-035
Kind: L
Fidelity: variant: the source's rate condition becomes a class-wise liminf condition (as the source itself says)
Hyps: (a); (c) hybrid-ledger reading -/
theorem j2_no_generable_class_mostly_false (S : ShutdownPair) {q δ η : ℚ} (hq : 0 < q)
    (hδ : 0 < δ) (hδη : 4 * δ ≤ η) (hηq : η ≤ q)
    (hbdd : BddAbove (Set.range (prefixSum (realized S (uDef S q δ))))) {v : ℕ → EF}
    (hv : PressClass S q δ v) (hdiv : DivergentWeighting v S.agent) {truth : ℕ → ℝ}
    (htruth : AffineCombination.TheoryTruth S.φ S.agentProcess truth) :
    ∃ ε > 0, ∃ᶠ N in atTop, (q : ℝ) - η + ε < rho (realized S v) truth N := by
  by_contra h
  have hfalse : ∀ ε > 0, ∀ᶠ N in atTop, rho (realized S v) truth N ≤ (q : ℝ) - η + ε := by
    intro ε hε
    by_contra hne
    exact h ⟨ε, hε, (Filter.not_eventually.mp hne).mono fun N hN => not_le.mp hN⟩
  have := mostly_false_forces_defiance S hq hδ hδη hηq hv hdiv htruth hfalse
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp this (M + 1)).imp fun N hN => hN N le_rfl
  have := hM ⟨N, rfl⟩
  linarith

/-- **Corollary 4.3 — whole-line `c`**: the compliance threshold `c/(c+h)` tends to `1` as the
gain-to-harm ratio `c/h` tends to infinity (`h > 0` fixed).
Source: [[corr-wf14-inventory]] 087 (Corollary 4.3)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem complianceThreshold_tendsto_one {h : ℝ} (hh : 0 < h) :
    Tendsto (fun c : ℝ => complianceThreshold c h) atTop (𝓝 1) := by
  have h1 : Tendsto (fun c : ℝ => h / (c + h)) atTop (𝓝 0) := by
    have := (tendsto_atTop_add_const_right atTop h tendsto_id).inv_tendsto_atTop
    simpa [div_eq_mul_inv] using this.const_mul h
  have heq : ∀ᶠ c : ℝ in atTop, complianceThreshold c h = 1 - h / (c + h) := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    unfold complianceThreshold
    field_simp
    ring
  rw [tendsto_congr' heq]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1

/-! ## C. T3: the base-rate identity on a class at finite `N` -/

/-- **The realized frequency is a posterior** (T3): on a class `v` with the all-days reference
weighting, write `ε := ∑ truth / (N+1)` (realized wrongness over all days), `β := ∑ v·truth /
∑ truth` (press mass on wrong days per wrong day), `α := ∑ v·(1 − truth) / ∑ (1 − truth)` (press
mass on right days per right day). Then `ρ_v(N) = εβ / (εβ + (1 − ε)α)` whenever both
`∑ truth` and `∑ (1 − truth)` are positive. Stated with the sums explicit (no division by a
possibly-zero denominator): `ρ_v(N)·(∑ v·truth + ∑ v·(1 − truth)) = ∑ v·truth`, which is the
posterior identity after the substitutions, with the zero-denominator cases disclosed in the
docstring rather than hidden in junk values.
Source: [[corr-wf13-inventory]] 063 (I13.1, "`ρ_v ≥ q ⟺ α_v/β_v ≤ (ε_v/(1−ε_v))(h/c)` exactly"); `li-scratch/baserate_trajectory.py` (1)
Kind: L
Fidelity: exact (sum form)
Hyps: (a) -/
theorem rho_mul_mass (v truth : ℕ → ℝ) (N : ℕ) (hpos : 0 < prefixSum v N) :
    rho v truth N * (prefixSum (fun i => v i * truth i) N +
      prefixSum (fun i => v i * (1 - truth i)) N) = prefixSum (fun i => v i * truth i) N := by
  have hmass : prefixSum (fun i => v i * truth i) N + prefixSum (fun i => v i * (1 - truth i)) N =
      prefixSum v N := by
    rw [← prefixSum_add]
    unfold prefixSum
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmass]
  simp only [rho]
  rw [weightedAverage_eq_div hpos.ne', div_mul_cancel₀ _ hpos.ne']

/-- **The base-rate inequality as an iff** (T3, the arithmetic of `corr-three-step`'s
`twoState_deltaMinus_nonneg_iff_odds` on realized class frequencies): for `ε ∈ (0,1)`, `α, β > 0`
and `c, h > 0`, the posterior `εβ/(εβ + (1 − ε)α)` is at least the compliance threshold
`c/(c + h)` iff `α/β ≤ (ε/(1 − ε))·(h/c)`.
Source: [[corr-wf13-inventory]] 063 (I13.1); `corr-three-step` `twoState_deltaMinus_nonneg_iff_odds`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem posterior_ge_iff_odds {ε α β c h : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hα : 0 < α)
    (hβ : 0 < β) (hc : 0 < c) (hh : 0 < h) :
    complianceThreshold c h ≤ ε * β / (ε * β + (1 - ε) * α) ↔
      α / β ≤ (ε / (1 - ε)) * (h / c) := by
  have h1ε : 0 < 1 - ε := by linarith
  have hden : 0 < ε * β + (1 - ε) * α := by positivity
  unfold complianceThreshold
  rw [div_le_div_iff₀ (by linarith) hden, div_le_iff₀ hβ, div_mul_div_comm,
    div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  constructor <;> intro H <;> nlinarith [H, hε0, h1ε, hα, hβ, hc, hh]

/-- `∑_{i ≤ N} (1 − truth i) = (N + 1) − ∑_{i ≤ N} truth i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_one_sub (truth : ℕ → ℝ) (N : ℕ) :
    prefixSum (fun i => 1 - truth i) N = (N : ℝ) + 1 - prefixSum truth N := by
  unfold prefixSum
  rw [Finset.sum_sub_distrib]
  simp

/-- `∑ v·truth + ∑ v·(1 − truth) = ∑ v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_mul_truth_add (v truth : ℕ → ℝ) (N : ℕ) :
    prefixSum (fun i => v i * truth i) N + prefixSum (fun i => v i * (1 - truth i)) N =
      prefixSum v N := by
  rw [← prefixSum_add]
  unfold prefixSum
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **The realized frequency is the posterior, with the class frequencies defined** (T3, audit
r1 fidelity N3): with `ε := ∑ truth/(N+1)`, `β := ∑ v·truth / ∑ truth`, `α := ∑ v·(1 − truth) /
∑ (1 − truth)`, `ρ_v(N) = εβ / (εβ + (1 − ε)α)` whenever the press mass, the number of wrong days
and the number of right days through `N` are all positive.
Source: [[corr-wf13-inventory]] 063 (I13.1: "`ρ_v` is the posterior `εβ/(εβ + (1−ε)α)`"); `li-scratch/baserate_trajectory.py` (1)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem rho_eq_posterior (v truth : ℕ → ℝ) (N : ℕ) (hpos : 0 < prefixSum v N)
    (hT : 0 < prefixSum truth N) (hF : 0 < prefixSum (fun i => 1 - truth i) N) :
    rho v truth N =
      (prefixSum truth N / ((N : ℝ) + 1)) *
          (prefixSum (fun i => v i * truth i) N / prefixSum truth N) /
        ((prefixSum truth N / ((N : ℝ) + 1)) *
            (prefixSum (fun i => v i * truth i) N / prefixSum truth N) +
          (1 - prefixSum truth N / ((N : ℝ) + 1)) *
            (prefixSum (fun i => v i * (1 - truth i)) N /
              prefixSum (fun i => 1 - truth i) N)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [prefixSum_one_sub] at hF ⊢
  have hmass := prefixSum_mul_truth_add v truth N
  have e1 : prefixSum truth N / ((N : ℝ) + 1) *
      (prefixSum (fun i => v i * truth i) N / prefixSum truth N) =
      prefixSum (fun i => v i * truth i) N / ((N : ℝ) + 1) := by
    field_simp
  have e2 : (1 - prefixSum truth N / ((N : ℝ) + 1)) *
      (prefixSum (fun i => v i * (1 - truth i)) N / ((N : ℝ) + 1 - prefixSum truth N)) =
      prefixSum (fun i => v i * (1 - truth i)) N / ((N : ℝ) + 1) := by
    have hne : (N : ℝ) + 1 - prefixSum truth N ≠ 0 := hF.ne'
    field_simp
  rw [e1, e2]
  simp only [rho]
  rw [weightedAverage_eq_div hpos.ne', ← hmass]
  have hsum : prefixSum (fun i => v i * truth i) N + prefixSum (fun i => v i * (1 - truth i)) N
      ≠ 0 := by rw [hmass]; exact hpos.ne'
  field_simp

/-- **The base-rate inequality on a class, as an iff with the class frequencies defined** (T3,
the mandate's `rho_ge_q_iff_odds`): for `c, h > 0`, when the press mass, the number of wrong
days, the number of right days, the press mass on wrong days and the press mass on right days
through `N` are all positive, `c/(c+h) ≤ ρ_v(N)` iff `α/β ≤ (ε/(1−ε))·(h/c)` with
`ε, α, β` the realized class frequencies of `rho_eq_posterior`.
Source: [[corr-wf13-inventory]] 063 (I13.1: "`ρ_v ≥ q ⟺ α_v/β_v ≤ (ε_v/(1−ε_v))(h/c)` exactly"); mandate T3
Kind: C
Fidelity: exact (at finite `N`, positive denominators named)
Hyps: (a) -/
theorem rho_ge_q_iff_odds (v truth : ℕ → ℝ) (N : ℕ) {c h : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hpos : 0 < prefixSum v N) (hT : 0 < prefixSum truth N)
    (hF : 0 < prefixSum (fun i => 1 - truth i) N)
    (hA : 0 < prefixSum (fun i => v i * truth i) N)
    (hB : 0 < prefixSum (fun i => v i * (1 - truth i)) N) :
    complianceThreshold c h ≤ rho v truth N ↔
      (prefixSum (fun i => v i * (1 - truth i)) N / prefixSum (fun i => 1 - truth i) N) /
          (prefixSum (fun i => v i * truth i) N / prefixSum truth N) ≤
        ((prefixSum truth N / ((N : ℝ) + 1)) / (1 - prefixSum truth N / ((N : ℝ) + 1))) *
          (h / c) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hε1 : prefixSum truth N / ((N : ℝ) + 1) < 1 := by
    rw [div_lt_one hN]
    rw [prefixSum_one_sub] at hF
    linarith
  rw [rho_eq_posterior v truth N hpos hT hF]
  exact posterior_ge_iff_odds (by positivity) hε1 (by positivity) (by positivity) hc hh

end Cleanroom.Corrigibility.CorrLiShutdown
