import Cleanroom.Found.LiAsympCalc.Ramp
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# E. The compactness lemma

Target E of [[li-asymp-calc-mandate]] (root-fa-014, [[fa-positive-results-corrected-v2]] §5.5,
[[fa-positive-results-corrected-v3]] §5). For a bounded quote stream `a` (in `[0,1]`) and any
stream `e`, the countable family of doubly-soft violation weights
`viol e a t ε δ n = dsWeight t ε δ (a n) (e n)` over **rational** `t, ε, δ` (`ε, δ > 0`)
all vanish at infinity iff `e` eventually dominates `a - c` for every `c > 0`, iff
`0 ≤ liminf (e - a)` (when both streams are in `[0,1]`); and the summability packaging is
equivalent to the same dominance. Rationality of the parameters is statement content (the
countable family dependents quantify over); a real-parameter quantification would be a weaker
hypothesis and is not the corpus's statement. No `Nat` subtraction, no `ℝ≥0` truncation.
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology

/-- The violation weight at day `n`: the doubly-soft gate `Ind_δ(a n > t) · Ind_δ(e n < t - ε)`
with rational parameters.
Source: [[fa-positive-results-corrected-v2]] §5.5; root-fa-014
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def viol (e a : ℕ → ℝ) (t ε δ : ℚ) (n : ℕ) : ℝ :=
  dsWeight (t : ℝ) (ε : ℝ) δ (a n) (e n)

/-- Dominance for every margin: `∀ c > 0, ∀ᶠ n, a n - c < e n`.
Source: [[fa-positive-results-corrected-v3]] §5
Kind: D
Fidelity: exact
Hyps: n/a -/
def Dominates (e a : ℕ → ℝ) : Prop := ∀ c > 0, ∀ᶠ n in atTop, a n - c < e n

/-- Under dominance, each violation weight is eventually `0` (the easy direction, no bounds).
Source: [[fa-positive-results-corrected-v3]] §5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem Dominates.viol_eventually_zero {e a : ℕ → ℝ} (hdom : Dominates e a) (t : ℚ)
    {ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) : ∀ᶠ n in atTop, viol e a t ε δ n = 0 := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  filter_upwards [hdom ε hεR] with n hn
  by_contra hne
  have hpos : 0 < viol e a t ε δ n := lt_of_le_of_ne (dsWeight_nonneg _ _ _ _ _) (Ne.symm hne)
  obtain ⟨h1, h2⟩ := dsWeight_pos_imp hδ hpos
  linarith

/-- Under dominance every violation weight tends to `0`.
Source: [[fa-positive-results-corrected-v3]] §5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem Dominates.tendsto_viol {e a : ℕ → ℝ} (hdom : Dominates e a) (t : ℚ) {ε δ : ℚ}
    (hε : 0 < ε) (hδ : 0 < δ) : Tendsto (viol e a t ε δ) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' ((hdom.viol_eventually_zero t hε hδ).mono (fun _ h => h.symm))

/-- Under dominance every violation weight is summable (it is eventually `0`).
Source: [[fa-positive-results-corrected-v3]] §5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem Dominates.summable_viol {e a : ℕ → ℝ} (hdom : Dominates e a) (t : ℚ) {ε δ : ℚ}
    (hε : 0 < ε) (hδ : 0 < δ) : Summable (viol e a t ε δ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hdom.viol_eventually_zero t hε hδ)
  exact summable_of_ne_finset_zero (s := Finset.range N)
    (fun n hn => hN n (not_lt.1 (fun h => hn (Finset.mem_range.2 h))))

/-- **Compactness direction** (E1 ⟹): if every rational-parameter violation weight tends to
`0` and `a` is `[0,1]`-valued, then `e` eventually dominates `a - c` for every `c > 0`. Proof:
otherwise `e n ≤ a n - c` infinitely often; along a subsequence `a → q*`; rational
`t ∈ (q* - c/2, q* - c/4)` and `ε, δ ∈ (c/16, c/8)` make both ramps `1` on a tail, so the
violation weight is `1` there.
Source: root-fa-014; [[fa-positive-results-corrected-v2]] §5.5
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem dominates_of_tendsto_viol {e a : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ t ε δ : ℚ, 0 < ε → 0 < δ → Tendsto (viol e a t ε δ) atTop (𝓝 0)) :
    Dominates e a := by
  intro c hc
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hcon' : ∃ᶠ n in atTop, e n ≤ a n - c := hcon.mono (fun n hn => not_lt.1 hn)
  obtain ⟨φ, hφ, hφv⟩ := extraction_of_frequently_atTop hcon'
  obtain ⟨q, hq, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq (fun k => ha (φ k))
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show q - c / 2 < q - c / 4 by linarith)
  obtain ⟨ε, hε1, hε2⟩ := exists_rat_btwn (show c / 16 < c / 8 by linarith)
  have hε : 0 < ε := by
    have : (0 : ℝ) < ε := by linarith
    exact_mod_cast this
  have hviol := (hv t ε ε hε hε).comp (hφ.comp hψ).tendsto_atTop
  have hlt1 := hviol.eventually (gt_mem_nhds (zero_lt_one' ℝ))
  have hnear1 := hlim.eventually (gt_mem_nhds (show q < q + c / 8 by linarith))
  have hnear2 := hlim.eventually (lt_mem_nhds (show q - c / 8 < q by linarith))
  obtain ⟨k, hk1, hk2, hk3⟩ := (hlt1.and (hnear1.and hnear2)).exists
  simp only [Function.comp] at hk1 hk2 hk3
  have hv_k := hφv (ψ k)
  have hone : viol e a t ε ε (φ (ψ k)) = 1 := by
    unfold viol
    apply dsWeight_eq_one hε
    · linarith
    · linarith
  rw [hone] at hk1
  exact lt_irrefl _ hk1

/-- **Compactness lemma** (E1): for `[0,1]`-valued `a`, all rational-parameter violation
weights tend to `0` iff `e` dominates `a - c` eventually for every `c > 0`.
Source: root-fa-014; [[fa-positive-results-corrected-v2]] §5.5; v3 §5
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_viol_iff_dominates {e a : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) :
    (∀ t ε δ : ℚ, 0 < ε → 0 < δ → Tendsto (viol e a t ε δ) atTop (𝓝 0)) ↔ Dominates e a :=
  ⟨dominates_of_tendsto_viol ha, fun hdom t _ _ hε hδ => hdom.tendsto_viol t hε hδ⟩

/-- **Summability packaging** (E1): all rational-parameter violation weights are summable iff
`e` dominates `a - c` eventually for every `c > 0` — the same dominance, so the two packagings
of [[fa-positive-results-corrected-v3]] §5 are equivalent.
Source: [[fa-positive-results-corrected-v3]] §5 ("the two packagings are equivalent")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem summable_viol_iff_dominates {e a : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) :
    (∀ t ε δ : ℚ, 0 < ε → 0 < δ → Summable (viol e a t ε δ)) ↔ Dominates e a :=
  ⟨fun hs => dominates_of_tendsto_viol ha
      (fun t ε δ hε hδ => (hs t ε δ hε hδ).tendsto_atTop_zero),
    fun hdom t _ _ hε hδ => hdom.summable_viol t hε hδ⟩

/-- Dominance is `0 ≤ liminf (e - a)` when both streams are `[0,1]`-valued (so the `liminf` is
a genuine real, not a junk `sSup`).
Source: [[fa-positive-results-corrected-v2]] §5.5 (the corpus's headline form
`liminf (E^H_n(X) - a_n) ≥ 0`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dominates_iff_liminf {e a : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (he : ∀ n, e n ∈ Set.Icc (0 : ℝ) 1) :
    Dominates e a ↔ 0 ≤ liminf (fun n => e n - a n) atTop := by
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => e n - a n) :=
    isBoundedUnder_of ⟨-1, fun n => by linarith [(ha n).2, (he n).1]⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop (fun n => e n - a n) :=
    (isBoundedUnder_of ⟨1, fun n => by linarith [(ha n).1, (he n).2]⟩ :
      IsBoundedUnder (· ≤ ·) atTop (fun n => e n - a n)).isCoboundedUnder_ge
  constructor
  · intro hdom
    refine le_of_forall_pos_lt_add (fun c hc => ?_)
    have h := le_liminf_of_le hcobdd ((hdom (c / 2) (by linarith)).mono
      (fun n hn => by linarith : ∀ n, a n - c / 2 < e n → -(c / 2) ≤ e n - a n))
    linarith
  · intro hlim c hc
    have := eventually_lt_of_lt_liminf (show -c < liminf (fun n => e n - a n) atTop by
      linarith) hbdd
    exact this.mono (fun n hn => by linarith)

/-- **Schedule-restricted form**: E1 along any subsequence `d` (no monotonicity needed: it is
E1 for `e ∘ d`, `a ∘ d`). Stated once for `tt-ladder` and `fa-theorem-a`.
Source: root-fa-2-005; [[li-asymp-calc-mandate]] E1
Kind: L
Fidelity: stronger: `d` need not be strictly increasing
Hyps: (a) none -/
theorem tendsto_viol_iff_dominates_along {e a : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (d : ℕ → ℕ) :
    (∀ t ε δ : ℚ, 0 < ε → 0 < δ → Tendsto (fun k => viol e a t ε δ (d k)) atTop (𝓝 0)) ↔
      ∀ c > 0, ∀ᶠ k in atTop, a (d k) - c < e (d k) :=
  tendsto_viol_iff_dominates (e := e ∘ d) (a := a ∘ d) (fun k => ha (d k))

/-! ### Witnesses -/

/-- **E1 witness (N+, dominance with strict violation)**: `a ≡ 1/2`, `e n = 1/2 - 1/(n+2)`:
`e n < a n` on every day, yet dominance holds, so every violation weight tends to `0`. The
lemma is not "`e ≥ a`".
Source: [[li-asymp-calc-mandate]] E1
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem compactness_witness_dominance :
    (∀ n, (fun _ : ℕ => (1 / 2 : ℝ)) n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, (fun n : ℕ => 1 / 2 - 1 / ((n : ℝ) + 2)) n < (fun _ : ℕ => (1 / 2 : ℝ)) n) ∧
      Dominates (fun n : ℕ => 1 / 2 - 1 / ((n : ℝ) + 2)) (fun _ => 1 / 2) ∧
      ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
        Tendsto (viol (fun n : ℕ => 1 / 2 - 1 / ((n : ℝ) + 2)) (fun _ => 1 / 2) t ε δ)
          atTop (𝓝 0) := by
  have hdom : Dominates (fun n : ℕ => 1 / 2 - 1 / ((n : ℝ) + 2)) (fun _ => 1 / 2) := by
    intro c hc
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      refine (this.comp (tendsto_add_atTop_nat 1)).congr (fun n => ?_)
      simp only [Function.comp]
      push_cast
      ring
    filter_upwards [h.eventually (gt_mem_nhds hc)] with n hn
    try simp only
    linarith
  refine ⟨fun _ => ⟨by norm_num, by norm_num⟩, fun n => ?_, hdom,
    fun t _ _ hε hδ => hdom.tendsto_viol t hε hδ⟩
  try simp only
  have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  linarith

/-- Alternating quote stream: `3/4` on even days, `1/4` on odd days (non-convergent, so the
compactness step's subsequence extraction is exercised).
Source: [[li-asymp-calc-mandate]] E1; audit round 1, adversarial probe 3
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def altQuote (n : ℕ) : ℝ := if Even n then 3 / 4 else 1 / 4

/-- Alternating expectation stream: `0` on even days, `1` on odd days.
Source: [[li-asymp-calc-mandate]] E1; audit round 1, adversarial probe 3
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def altExp (n : ℕ) : ℝ := if Even n then 0 else 1

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma viol_alt_even {n : ℕ} (hn : Even n) :
    viol altExp altQuote (1 / 4) (1 / 8) (1 / 16) n = 1 := by
  unfold viol
  apply dsWeight_eq_one (by norm_num)
  · simp only [altQuote, if_pos hn]
    push_cast
    norm_num
  · simp only [altExp, if_pos hn]
    push_cast
    norm_num

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma viol_alt_odd {n : ℕ} (hn : ¬ Even n) :
    viol altExp altQuote (1 / 4) (1 / 8) (1 / 16) n = 0 := by
  unfold viol dsWeight
  simp only [altQuote, if_neg hn]
  have hq : ((1 / 4 : ℚ) : ℝ) = (1 / 4 : ℝ) := by norm_num
  rw [hq, ctsInd_self, zero_mul]

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma frequently_even : ∃ᶠ (n : ℕ) in atTop, Even n :=
  frequently_atTop.2 (fun a => ⟨2 * a, by omega, even_two_mul a⟩)

/-- **E1 witness (N+, violation, non-constant)**: `a = altQuote` (`3/4`, `1/4` alternating: no
limit, so the compactness step's extraction is exercised) and `e = altExp` (`0`, `1`
alternating), both `[0,1]`-valued and non-constant. At `(t, ε, δ) = (1/4, 1/8, 1/16)` the
violation weight is `1` on every even day and `0` on every odd day — so it is frequently `1`
and frequently `0`, neither tends to `0` nor is summable — and dominance fails at `c = 1/4` on
the even days. Replaces the all-constant witness of the first version (audit round 1, B2).
Source: [[li-asymp-calc-mandate]] E1
Kind: N+
Fidelity: n/a
Hyps: n/a -/
theorem compactness_witness_violation :
    (∀ n, altQuote n ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, altExp n ∈ Set.Icc (0 : ℝ) 1) ∧
      altQuote 0 ≠ altQuote 1 ∧ altExp 0 ≠ altExp 1 ∧
      (∃ᶠ n in atTop, viol altExp altQuote (1 / 4) (1 / 8) (1 / 16) n = 1) ∧
      (∃ᶠ n in atTop, viol altExp altQuote (1 / 4) (1 / 8) (1 / 16) n = 0) ∧
      ¬ Tendsto (viol altExp altQuote (1 / 4) (1 / 8) (1 / 16)) atTop (𝓝 0) ∧
      ¬ Summable (viol altExp altQuote (1 / 4) (1 / 8) (1 / 16)) ∧
      ¬ Dominates altExp altQuote := by
  have hfreq1 : ∃ᶠ n in atTop, viol altExp altQuote (1 / 4) (1 / 8) (1 / 16) n = 1 :=
    frequently_even.mono (fun n hn => viol_alt_even hn)
  have hfreq0 : ∃ᶠ n in atTop, viol altExp altQuote (1 / 4) (1 / 8) (1 / 16) n = 0 := by
    rw [frequently_atTop]
    intro a
    refine ⟨2 * a + 1, by omega, viol_alt_odd ?_⟩
    rw [Nat.not_even_iff_odd]
    exact odd_two_mul_add_one a
  have hnot : ¬ Tendsto (viol altExp altQuote (1 / 4) (1 / 8) (1 / 16)) atTop (𝓝 0) := by
    intro h
    have hev := h.eventually (gt_mem_nhds (zero_lt_one' ℝ))
    obtain ⟨n, hn1, hn2⟩ := (hfreq1.and_eventually hev).exists
    rw [hn1] at hn2
    exact lt_irrefl _ hn2
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_, hfreq1, hfreq0, hnot,
    fun hs => hnot hs.tendsto_atTop_zero, fun hdom => ?_⟩
  · unfold altQuote; split_ifs <;> constructor <;> norm_num
  · unfold altExp; split_ifs <;> constructor <;> norm_num
  · norm_num [altQuote]
  · norm_num [altExp]
  · obtain ⟨n, hn, hlt⟩ := (frequently_even.and_eventually (hdom (1 / 4) (by norm_num))).exists
    simp only [altQuote, altExp, if_pos hn] at hlt
    norm_num at hlt

/-! ### The `t ∈ [0,1]` family suffices -/

/-- Outside `t ∈ [0,1]` every violation weight vanishes identically when both streams are
`[0,1]`-valued: for `t ≥ 1` the quote ramp is off (`a n ≤ 1 ≤ t`), for `t ≤ 0` the expectation
ramp is off (`t - ε < 0 ≤ e n`).
Source: none: infrastructure (audit round 1, fidelity §3.8)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem viol_eq_zero_of_not_mem_Icc {e a : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (he : ∀ n, e n ∈ Set.Icc (0 : ℝ) 1) {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ)
    (ht : t ∉ Set.Icc (0 : ℚ) 1) (n : ℕ) : viol e a t ε δ n = 0 := by
  unfold viol dsWeight
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · have htR : (t : ℝ) < 0 := by exact_mod_cast ht
    have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
    rw [(ctsInd_eq_zero_iff hδ _ _).2 (by linarith [(he n).1] : (t : ℝ) - ε ≤ e n), mul_zero]
  · have htR : (1 : ℝ) < t := by exact_mod_cast ht
    rw [(ctsInd_eq_zero_iff hδ _ _).2 (by linarith [(ha n).2] : a n ≤ (t : ℝ)), zero_mul]

/-- **E1 with the threshold family restricted to `t ∈ [0,1] ∩ ℚ`** (what a countable trader
family over `[0,1]`-valued streams supplies): for `[0,1]`-valued `e` and `a`, the violation
weights over rational `t ∈ [0,1]`, `ε, δ > 0` all tend to `0` iff `e` dominates `a - c`
eventually for every `c > 0`. The extension to all rational `t` is `viol_eq_zero_of_not_mem_Icc`.
Source: root-fa-014; [[fa-positive-results-corrected-v3]] §5 (the corpus's `t ∈ [0,1]` family); audit round 1, fidelity §3.8
Kind: L
Fidelity: exact (the corpus's parameter range)
Hyps: (a) none -/
theorem tendsto_viol_iff_dominates_Icc {e a : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (he : ∀ n, e n ∈ Set.Icc (0 : ℝ) 1) :
    (∀ t ε δ : ℚ, t ∈ Set.Icc (0 : ℚ) 1 → 0 < ε → 0 < δ →
        Tendsto (viol e a t ε δ) atTop (𝓝 0)) ↔ Dominates e a := by
  rw [← tendsto_viol_iff_dominates ha]
  constructor
  · intro h t ε δ hε hδ
    by_cases ht : t ∈ Set.Icc (0 : ℚ) 1
    · exact h t ε δ ht hε hδ
    · have : viol e a t ε δ = fun _ => 0 :=
        funext (viol_eq_zero_of_not_mem_Icc ha he hε hδ ht)
      rw [this]
      exact tendsto_const_nhds
  · intro h t ε δ _ hε hδ
    exact h t ε δ hε hδ

end Cleanroom.Found.LiAsympCalc
