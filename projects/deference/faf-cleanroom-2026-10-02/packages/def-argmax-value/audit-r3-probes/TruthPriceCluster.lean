import Cleanroom.Deference.DefArgmaxValue.TruthTeller

/-!
# audit r3 (fidelity) probe: the package already constrains the truth-teller's price — its limit
points lie in `{0, s, 1}` — so the one OPEN `truthPrice_frequently_interior` is exactly
"`s` is a cluster point of `P_{f n}(τ_n)`"

`Open.lean` states the package's one OPEN, `truthPrice_frequently_interior`
(`∃ c > 0, ∃ᶠ n, c ≤ P_{f n}(τ_n) ≤ 1 − c`), with the register "truth value unknown: `p_n → 1` and
`p_n → 0` are each consistent with everything proved in the package". True — but the package proves
more about `p_n := P_{f n}(τ_n)` than the docstring records. `concentrates_self` on `truthMenu` with
`selectionPackage_self` says, for every `ε > 0`:

* at `j = 1`: `E*(I^1_n) · 1[m^1_n ≤ M_n − ε] → 0`, i.e. (with `E*(I^1) ≈ₙ 1 − p_n`,
  `m^0 = p_n`, `m^1 = s_{f n}`) `(1 − p_n) · 1[s_{f n} + ε ≤ p_n] → 0`: **along the days on which
  the price is `ε` above the threshold, the price tends to `1`** (`truthPrice_above_tendsto_one`);
* at `j = 0`: `p_n · 1[p_n ≤ s_{f n} − ε] → 0`: **along the days on which the price is `ε` below
  the threshold, it tends to `0`** (`truthPrice_below_tendsto_zero`).

So every limit point of `p_n` lies in `{0, s, 1}` (the threshold `s_{f n} → s`), and the OPEN is
equivalent (`truthPrice_interior_iff_cluster_at_s`) to: **`s` is a cluster point of `P_{f n}(τ_n)`**
— for every `ε > 0`, `|p_n − s| < ε` frequently. In words: the truth-teller is the positive-feedback
fixed point whose only interior rest point is the unstable one at `s`; "the price stays interior"
means "the price keeps returning to `s`", not "the price wanders in `(0,1)`". This is the same
mechanism audit r1 N1 used on the punishing menu (`punishing_quotes_tie`); nothing here decides the
OPEN, which stays open. Not imported by the library.
-/

namespace Cleanroom.Deference.DefArgmaxValue.AuditR3

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open Cleanroom.Deference.DefArgmaxValue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (s : ℚ)

/-- A bounded multiplier does not disturb a null sequence: `a n → 0`, `|u n| ≤ 1` ⟹ `a n * u n → 0`. -/
theorem tendsto_mul_bounded_of_tendsto_zero {a u : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    (hu : ∀ n, |u n| ≤ 1) : Tendsto (fun n => a n * u n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at ha ⊢
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) ha
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by simpa [Real.norm_eq_abs] using hu n)

/-- **Above the threshold the price goes to `1`**: `(1 − p_n) · 1[s_{f n} + ε ≤ p_n] → 0`, from
`concentrates_self` at `j = 1` on the truth-teller menu. -/
theorem truthPrice_above_tendsto_one (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (1 - (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)) *
      (if ((probeThreshold T f s n : ℚ) : ℝ) + ε ≤
          (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) then (1 : ℝ) else 0))
      atTop (𝓝 0) := by
  have hc := concentrates_self T f hf (truthMenu T f s hs.1)
    (selectionPackage_self T f (truthMenu T f s hs.1)) ε hε 1
  have key : ∀ n, ((truthMenu T f s hs.1).quote (selfExpert T f) 1 n ≤
      (truthMenu T f s hs.1).maxQuote (selfExpert T f) n - ε) ↔
      (((probeThreshold T f s n : ℚ) : ℝ) + ε ≤
        (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n)) := by
    intro n
    rw [Menu.maxQuote_two, truthMenu_quote_zero, truthMenu_quote_one]
    constructor
    · intro h
      rcases le_total ((liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n))
          ((probeThreshold T f s n : ℚ) : ℝ) with hle | hle
      · rw [max_eq_right hle] at h; linarith
      · rw [max_eq_left hle] at h; linarith
    · intro h
      rw [max_eq_left (by linarith)]
      linarith
  simp only [key] at hc
  have hI1 := truth_selI_one_estimate T f s hf hs
  unfold AsympEq at hI1
  have h2 := tendsto_mul_bounded_of_tendsto_zero hI1
    (u := fun n => (if ((probeThreshold T f s n : ℚ) : ℝ) + ε ≤
      (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) then (1 : ℝ) else 0))
    (fun n => by split_ifs <;> simp)
  have := hc.sub h2
  refine (tendsto_congr (fun n => ?_)).mp (by simpa only [_root_.sub_zero] using this)
  ring

/-- **Below the threshold the price goes to `0`**: `p_n · 1[p_n ≤ s_{f n} − ε] → 0`, from
`concentrates_self` at `j = 0`. -/
theorem truthPrice_below_tendsto_zero (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) *
      (if (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) ≤
          ((probeThreshold T f s n : ℚ) : ℝ) - ε then (1 : ℝ) else 0))
      atTop (𝓝 0) := by
  have hc := concentrates_self T f hf (truthMenu T f s hs.1)
    (selectionPackage_self T f (truthMenu T f s hs.1)) ε hε 0
  have key : ∀ n, ((truthMenu T f s hs.1).quote (selfExpert T f) 0 n ≤
      (truthMenu T f s hs.1).maxQuote (selfExpert T f) n - ε) ↔
      ((liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) ≤
        ((probeThreshold T f s n : ℚ) : ℝ) - ε) := by
    intro n
    rw [Menu.maxQuote_two, truthMenu_quote_zero, truthMenu_quote_one]
    constructor
    · intro h
      rcases le_total ((liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n))
          ((probeThreshold T f s n : ℚ) : ℝ) with hle | hle
      · rw [max_eq_right hle] at h; linarith
      · rw [max_eq_left hle] at h; linarith
    · intro h
      rw [max_eq_right (by linarith)]
      linarith
  simp only [key] at hc
  have hI0 := truth_selI_zero_estimate T f s hf hs
  unfold AsympEq at hI0
  have h2 := tendsto_mul_bounded_of_tendsto_zero hI0
    (u := fun n => (if (liaHistory (paperDP T)) (f n) (truthSentence T f s hs.1 n) ≤
      ((probeThreshold T f s n : ℚ) : ℝ) - ε then (1 : ℝ) else 0))
    (fun n => by split_ifs <;> simp)
  have := hc.sub h2
  refine (tendsto_congr (fun n => ?_)).mp (by simpa only [_root_.sub_zero] using this)
  ring

/-- **The OPEN is the cluster-point question**: for `s ∈ (0,1)`,
`∃ c > 0, ∃ᶠ n, c ≤ P_{f n}(τ_n) ≤ 1 − c` (the statement of `truthPrice_frequently_interior`)
⟺ `∀ ε > 0, ∃ᶠ n, |P_{f n}(τ_n) − s| < ε`. -/
theorem truthPrice_interior_iff_cluster_at_s (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    (∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop,
        c ≤ (liaHistory (paperDP T)) (f n) (truthSentence T f s hs0.le n) ∧
          (liaHistory (paperDP T)) (f n) (truthSentence T f s hs0.le n) ≤ 1 - c) ↔
      (∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop,
        |(liaHistory (paperDP T)) (f n) (truthSentence T f s hs0.le n) - s| < ε) := by
  have hs : 0 ≤ s ∧ s ≤ 1 := ⟨hs0.le, hs1.le⟩
  constructor
  · rintro ⟨c, hc, hfreq⟩ ε hε
    have hA := (truthPrice_above_tendsto_one T f s hf hs (ε / 2) (by linarith)).eventually
      (gt_mem_nhds (show (0 : ℝ) < c / 2 by linarith))
    have hB := (truthPrice_below_tendsto_zero T f s hf hs (ε / 2) (by linarith)).eventually
      (gt_mem_nhds (show (0 : ℝ) < c / 2 by linarith))
    have hthr := (Metric.tendsto_nhds.mp (probeThreshold_tendsto T f s hs)) (ε / 2) (by linarith)
    refine (hfreq.and_eventually (hA.and (hB.and hthr))).mono ?_
    rintro n ⟨⟨hn1, hn2⟩, hnA, hnB, hnT⟩
    rw [Real.dist_eq, abs_lt] at hnT
    rw [abs_lt]
    constructor
    · by_contra hcon
      push Not at hcon
      have hcond : (liaHistory (paperDP T)) (f n) (truthSentence T f s hs0.le n) ≤
          ((probeThreshold T f s n : ℚ) : ℝ) - ε / 2 := by linarith
      rw [if_pos hcond, mul_one] at hnB
      linarith
    · by_contra hcon
      push Not at hcon
      have hcond : ((probeThreshold T f s n : ℚ) : ℝ) + ε / 2 ≤
          (liaHistory (paperDP T)) (f n) (truthSentence T f s hs0.le n) := by linarith
      rw [if_pos hcond, mul_one] at hnA
      linarith
  · intro hcl
    have h0 : (0 : ℝ) < s := by exact_mod_cast hs0
    have h1 : (s : ℝ) < 1 := by exact_mod_cast hs1
    refine ⟨min (s : ℝ) (1 - s) / 2, by positivity, ?_⟩
    refine (hcl (min (s : ℝ) (1 - s) / 2) (by positivity)).mono (fun n hn => ?_)
    rw [abs_lt] at hn
    have hm1 : min (s : ℝ) (1 - s) ≤ s := min_le_left _ _
    have hm2 : min (s : ℝ) (1 - s) ≤ 1 - s := min_le_right _ _
    constructor <;> linarith

/-- Instance line at `𝗣𝗔`, `succDeferral`, `s = ½`: the OPEN at the default instance is "`½` is a
cluster point of `P_{n+1}(τ_n)`". -/
example :
    (∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop,
        c ≤ (liaHistory (paperDP 𝗣𝗔)) (succDeferral n)
            (truthSentence 𝗣𝗔 succDeferral (1 / 2) (by norm_num) n) ∧
          (liaHistory (paperDP 𝗣𝗔)) (succDeferral n)
            (truthSentence 𝗣𝗔 succDeferral (1 / 2) (by norm_num) n) ≤ 1 - c) ↔
      (∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop,
        |(liaHistory (paperDP 𝗣𝗔)) (succDeferral n)
            (truthSentence 𝗣𝗔 succDeferral (1 / 2) (by norm_num) n) - ((1 / 2 : ℚ) : ℝ)| < ε) :=
  truthPrice_interior_iff_cluster_at_s 𝗣𝗔 succDeferral (1 / 2)
    Cleanroom.Found.LiQuoteLane.succDeferral_strict (by norm_num) (by norm_num)

end

#print axioms truthPrice_above_tendsto_one
#print axioms truthPrice_below_tendsto_zero
#print axioms truthPrice_interior_iff_cluster_at_s

end Cleanroom.Deference.DefArgmaxValue.AuditR3
