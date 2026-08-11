/-
# Faithful acceleration over the pinned market model — round `2026-08-11-faithful-acceleration`

Provisional namespace and provisional names (`AGENTS.md` §6): every declaration below is
proposed, not canonical.

## What this file is

Two layers, kept separate on purpose.

**Layer 1 — the ported arithmetic.** The inherited development's faithful-acceleration
core (`projects/deference/note-dump-2026-06-27/lean/FaithfulAcceleration.lean`,
declarations `round_profit_ge`, `profit_partial_sum_ge`, `profit_diverges`,
`violation_not_persistent`), restated and re-proved against *this* repository's toolchain
and Mathlib pin. The statements are the inherited ones; nothing is strengthened. Their
inherited status was attested by an audit, not rebuilt here, so re-elaborating them is the
confirmation `PRIORITIES.md` item 14 asks for.

**Layer 2 — the market bridge (new).** The inherited chain leaves two hypotheses named:
`hbias` (A's calibration) and `hbdd` ("the no-Dutch-book criterion bounds the trader's
banked value"). The inherited audit's §3.1 records that the second is a *modelling
substitution*: no trader, market, price or cash accounting is modelled anywhere in that
corpus, so the criterion's application is assumed rather than derived.

Against the pinned Formalized-Agent-Foundations dependency the trader *is* modelled. Layer
2 therefore

* builds the doubly-soft gate as an actual `LogicalInduction.EF` expressible feature of
  rank `n` (`weightEF`, `weightEF_rank`), which discharges the inherited "continuous ⇒
  legal `𝒞`-expressible feature" modelling step for this weight — the `EF` grammar already
  contains the clipped ramp;
* builds the round-trip trader as an actual `LogicalInduction.Trader` (`accelTrader`);
* proves the exact accounting identity `netWorth = open position + banked partial sum`
  (`accelTrader_netWorth_eq`);
* derives the bounded-value input from `IsLogicalInductor` instead of assuming it
  (`weight_not_divergent`).

## What remains named, exactly

* `EfficientlyComputable (accelTrader …)` — the emission certificate. FAF's
  `hystTrader_ecTok` is the pattern for a market-price gate; the extra content here is the
  exogenous rational sequence `a` (A's published quotes), which must be emitted under the
  same polynomial clock. Not attempted in this round.
* `hbias` — A's calibration. A *cross-process* statement (A's prices forecasting H's future
  prices). FAF's calibration development is single-market, so there is no endpoint to
  instantiate it from.
* `hworld` — each deductive stage admits a propositionally consistent world. FAF's
  `DeductiveProcess` does not carry this as a field; FAF's own `oscillation_exploitable_hyst`
  states it the same way.

Because `EfficientlyComputable` is not discharged, `weight_not_divergent` ships **without**
a term inhabiting its full hypothesis package: it is `unverified-nonvacuous` in the sense of
`AGENTS.md`'s Lean regime and is not promotable to the record as it stands.

## Deliberate restriction

Layer 2 fixes the lookahead at one day (`v n = P (n+1) φ`). The inherited statement carries a
general lookahead `f`. See this round's `REPORT.md` §4: with general `f` the open-position
remainder is bounded by the number of simultaneously open round trips, which is `1` exactly
when `f n = n + 1`.
-/
import LogicalInduction.Properties.Hysteresis
import Mathlib.Topology.Order.LiminfLimsup

namespace Workspace.Deference.Contrib.FaithfulAcceleration

open Filter Topology LogicalInduction

/-! ## Layer 1 — the ported inherited arithmetic

Statements as inherited. Provisional names carry this file's namespace; the inherited
declaration each one restates is named in its docstring.
-/

/-- Ported from inherited `FaithfulAccel.round_profit_ge`.

On a day where the trade fires (`0 < w`), A forecasts high (`t < a`) and H is currently low
(`p < t - ε`); the weighted round trip nets at least the day's forecast-bias term plus
`ε * w`. -/
theorem roundProfit_ge (w v p a t ε : ℝ) (hw : 0 ≤ w)
    (hone : 0 < w → t < a) (hmis : 0 < w → p < t - ε) :
    w * (v - a) + ε * w ≤ w * (v - p) := by
  rcases eq_or_lt_of_le hw with h | h
  · simp [← h]
  · have ha := hone h
    have hp := hmis h
    have key : 0 < w * (a - p - ε) := mul_pos h (by linarith)
    nlinarith [key]

/-- Ported from inherited `FaithfulAccel.profit_partial_sum_ge`. -/
theorem profitPartialSum_ge (w v p a : ℕ → ℝ) (t ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hone : ∀ i, 0 < w i → t < a i)
    (hmis : ∀ i, 0 < w i → p i < t - ε) (n : ℕ) :
    (∑ i ∈ Finset.range n, w i * (v i - a i)) + ε * (∑ i ∈ Finset.range n, w i)
      ≤ ∑ i ∈ Finset.range n, w i * (v i - p i) := by
  have h1 :
      (∑ i ∈ Finset.range n, w i * (v i - a i)) + ε * (∑ i ∈ Finset.range n, w i)
        = ∑ i ∈ Finset.range n, (w i * (v i - a i) + ε * w i) := by
    simp only [Finset.mul_sum, Finset.sum_add_distrib]
  rw [h1]
  exact Finset.sum_le_sum (fun i _ =>
    roundProfit_ge (w i) (v i) (p i) (a i) t ε (hw i) (hone i) (hmis i))

/-- The eventual lower bound inside the inherited `FaithfulAccel.profit_diverges`, split out
because Layer 2 uses it on its own. -/
theorem eventually_half_weight_le (P C W : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hPC : ∀ n, C n + ε * W n ≤ P n)
    (hbias : Tendsto (fun n => C n / W n) atTop (𝓝 0))
    (hW : Tendsto W atTop atTop) :
    ∀ᶠ n in atTop, (ε / 2) * W n ≤ P n := by
  have hWpos : ∀ᶠ n in atTop, 0 < W n := hW.eventually_gt_atTop 0
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hbias (ε / 2) (by linarith)
  filter_upwards [hWpos, eventually_atTop.2 ⟨N, hN⟩] with n hWn hclose
  simp only [Real.dist_eq, sub_zero] at hclose
  have hcw : -(ε / 2) < C n / W n := (abs_lt.1 hclose).1
  have hC : -(ε / 2) * W n < C n := by
    have hmul := mul_lt_mul_of_pos_right hcw hWn
    rwa [div_mul_cancel₀ _ (ne_of_gt hWn)] at hmul
  have hring : -(ε / 2) * W n + ε * W n = (ε / 2) * W n := by ring
  linarith [hPC n]

/-- Ported from inherited `FaithfulAccel.profit_diverges`. -/
theorem profitDiverges (P C W : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hPC : ∀ n, C n + ε * W n ≤ P n)
    (hbias : Tendsto (fun n => C n / W n) atTop (𝓝 0))
    (hW : Tendsto W atTop atTop) :
    Tendsto P atTop atTop :=
  tendsto_atTop_mono' atTop (eventually_half_weight_le P C W ε hε hPC hbias hW)
    (Tendsto.const_mul_atTop (by linarith) hW)

/-- Ported from inherited `FaithfulAccel.violation_not_persistent` — **the inherited theorem
of record for Movement I**. `hbdd` is the named no-Dutch-book input; Layer 2 replaces it. -/
theorem violationNotPersistent (P C W : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hPC : ∀ n, C n + ε * W n ≤ P n)
    (hbias : Tendsto (fun n => C n / W n) atTop (𝓝 0))
    (hbdd : ∃ M, ∀ n, P n ≤ M) :
    ¬ Tendsto W atTop atTop := by
  intro hW
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨n, hn⟩ := (tendsto_atTop.1 (profitDiverges P C W ε hε hPC hbias hW) (M + 1)).exists
  linarith [hM n]

/-- Ported from inherited `FaithfulAccel.profit_diverges_nonvacuous`: the divergence
hypotheses are jointly satisfiable, with a non-constant witness. -/
theorem profitDiverges_nonvacuous :
    ∃ (P C W : ℕ → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ n, C n + ε * W n ≤ P n) ∧
      Tendsto (fun n => C n / W n) atTop (𝓝 0) ∧
      Tendsto W atTop atTop ∧
      Tendsto P atTop atTop := by
  refine ⟨(fun n => (n : ℝ)), (fun _ => 0), (fun n => (n : ℝ)), 1/4, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro n
    have h : (0 : ℝ) ≤ (n : ℝ) := by positivity
    show (0 : ℝ) + 1 / 4 * (n : ℝ) ≤ (n : ℝ)
    linarith
  · simp
  · exact tendsto_natCast_atTop_atTop
  · exact tendsto_natCast_atTop_atTop

/-! ## Layer 2 — the same argument over the pinned market model -/

/-! ### The weight, as an expressible feature -/

/-- A's day-`n` quote enters H's market as a rational constant; the gate is positive exactly
when `t < a n`. Rank `0`.

**Modelling note (type `(c)`).** `EF`'s grammar is single-market: `EF.price` reads the
history the trader trades against. A's forecast is therefore not a price feature here but an
exogenous rational sequence the trader hard-codes. That is faithful to "H reads A's published
quote before day `n`", and it is what makes the emission certificate depend on `a` being
computable under a polynomial clock. -/
def gateA (t δ : ℚ) (a : ℕ → ℚ) (n : ℕ) : EF := clip01 (.const ((a n - t) / δ))

/-- H's day-`n` price gate: positive exactly when `P n φ < t - ε`. Rank `n`. -/
def gateH (φ : Sentence) (t ε δ : ℚ) (n : ℕ) : EF :=
  clip01 (.mul (.add (.const (t - ε)) (.mul (.const (-1)) (.price φ n))) (.const (1 / δ)))

/-- The doubly-soft weight of the inherited §5, as an expressible feature. This declaration
is what discharges the inherited audit's finding 7 ("continuous ⇒ legal `𝒞`-expressible
feature", left as a modelling step) *for this weight*: it is literally an `EF`, and
`weightEF_rank` certifies it is legal on its own day. -/
def weightEF (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (n : ℕ) : EF :=
  .mul (gateA t δ a n) (gateH φ t ε δ n)

@[simp] theorem gateA_rank (t δ : ℚ) (a : ℕ → ℚ) (n : ℕ) : (gateA t δ a n).rank = 0 := by
  simp [gateA, clip01, efMin]

@[simp] theorem gateH_rank (φ : Sentence) (t ε δ : ℚ) (n : ℕ) :
    (gateH φ t ε δ n).rank = n := by
  simp [gateH, clip01, efMin]

@[simp] theorem weightEF_rank (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (n : ℕ) :
    (weightEF φ t ε δ a n).rank = n := by
  simp [weightEF]

/-- The soft (continuous) indicator of the inherited development: a clamp ramping `0 → 1`
over `[0, δ]`. It is FAF's `clip01` value at `x / δ`, so FAF's real-side clip facts
(`clipVal_nonneg`, `clipVal_le_one`, `clipVal_pos_imp`) apply directly. -/
noncomputable def softInd (δ x : ℝ) : ℝ := max 0 (min 1 (x / δ))

theorem softInd_nonneg (δ x : ℝ) : 0 ≤ softInd δ x := clipVal_nonneg _

theorem softInd_le_one (δ x : ℝ) : softInd δ x ≤ 1 := clipVal_le_one _

theorem softInd_pos_imp {δ x : ℝ} (hδ : 0 < δ) (h : 0 < softInd δ x) : 0 < x := by
  have hx := clipVal_pos_imp h
  have hmul := mul_pos hx hδ
  rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at hmul

/-- The doubly-soft weight as a real-valued function of the two prices. Ported from the
inherited `FaithfulAccel.dsWeight`. -/
noncomputable def dsWeight (t ε δ av p : ℝ) : ℝ :=
  softInd δ (av - t) * softInd δ (t - ε - p)

theorem dsWeight_nonneg (t ε δ av p : ℝ) : 0 ≤ dsWeight t ε δ av p :=
  mul_nonneg (softInd_nonneg _ _) (softInd_nonneg _ _)

theorem dsWeight_le_one (t ε δ av p : ℝ) : dsWeight t ε δ av p ≤ 1 := by
  have h1 := softInd_nonneg δ (av - t)
  have h2 := softInd_nonneg δ (t - ε - p)
  have h3 := softInd_le_one δ (av - t)
  have h4 := softInd_le_one δ (t - ε - p)
  simp only [dsWeight]
  nlinarith

theorem dsWeight_pos_imp_fst {t ε δ av p : ℝ} (hδ : 0 < δ) (h : 0 < dsWeight t ε δ av p) :
    t < av := by
  have hf : 0 < softInd δ (av - t) := by
    rcases mul_pos_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 (not_lt.2 (softInd_nonneg _ _))
  linarith [softInd_pos_imp hδ hf]

theorem dsWeight_pos_imp_snd {t ε δ av p : ℝ} (hδ : 0 < δ) (h : 0 < dsWeight t ε δ av p) :
    p < t - ε := by
  have hs : 0 < softInd δ (t - ε - p) := by
    rcases mul_pos_iff.1 h with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact absurd h2 (not_lt.2 (softInd_nonneg _ _))
  linarith [softInd_pos_imp hδ hs]

theorem gateA_denote (t δ : ℚ) (a : ℕ → ℚ) (n : ℕ) (P : History) :
    (gateA t δ a n).denote P = softInd (δ : ℝ) ((a n : ℝ) - (t : ℝ)) := by
  simp only [gateA, clip01_denote, EF.denote_const, softInd]
  norm_num

theorem gateH_denote (φ : Sentence) (t ε δ : ℚ) (n : ℕ) (P : History) :
    (gateH φ t ε δ n).denote P
      = softInd (δ : ℝ) ((t : ℝ) - (ε : ℝ) - P n φ) := by
  simp only [gateH, clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const,
    EF.denote_price, Pi.mul_apply, Pi.add_apply, softInd]
  congr 2
  push_cast
  ring

/-- The expressible feature denotes the doubly-soft weight: the join between the ported
arithmetic (about the real number) and the market model (about the syntax the trader may
legally use). -/
theorem weightEF_denote (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (n : ℕ) (P : History) :
    (weightEF φ t ε δ a n).denote P
      = dsWeight (t : ℝ) (ε : ℝ) (δ : ℝ) (a n : ℝ) (P n φ) := by
  simp only [weightEF, EF.denote_mul, Pi.mul_apply, gateA_denote, gateH_denote, dsWeight]

/-! ### The trader -/

/-- The holdings chain: hold nothing before day `0`, and hold `weightEF n` between day `n`
and day `n + 1`. Rank `≤ k - 1`, so the day-`k` trade coefficient is legal on day `k`. -/
def holdEF (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) : ℕ → EF
  | 0 => .const 0
  | (k + 1) => weightEF φ t ε δ a k

theorem holdEF_rank (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) :
    ∀ k, (holdEF φ t ε δ a k).rank ≤ k - 1
  | 0 => by simp [holdEF]
  | (k + 1) => by simp [holdEF]

/-- The day-`n` trade coefficient: the position change. Buying `weightEF n` and unwinding the
previous day's position is exactly the inherited note's one-day round trip. -/
def tradeEF (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (n : ℕ) : EF :=
  .add (holdEF φ t ε δ a (n + 1)) (.mul (.const (-1)) (holdEF φ t ε δ a n))

theorem tradeEF_rank (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (n : ℕ) :
    (tradeEF φ t ε δ a n).rank ≤ n := by
  have h1 := holdEF_rank φ t ε δ a (n + 1)
  have h2 := holdEF_rank φ t ε δ a n
  simp only [tradeEF, EF.rank_add, EF.rank_mul, EF.rank_const, Nat.max_le]
  omega

/-- **The faithful-acceleration trader**, as an actual `LogicalInduction.Trader`: each day it
moves its `φ`-position to the doubly-soft gate's current value. -/
def accelTrader (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) : Trader where
  strat n :=
    { trades := [(tradeEF φ t ε δ a n, φ)]
      rank_le := by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact tradeEF_rank φ t ε δ a n }

/-! ### The accounting identity -/

/-- Summation by parts for a position chain started at zero: the running value of the chain
is the currently open position plus the banked price movements. Pure real algebra; no market
content. -/
theorem position_sum_eq (h p : ℕ → ℝ) (y : ℝ) (h0 : h 0 = 0) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (h (i + 1) - h i) * (y - p i))
      = h (n + 1) * (y - p n) + ∑ i ∈ Finset.range n, h (i + 1) * (p (i + 1) - p i) := by
  induction n with
  | zero => simp [h0]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih,
        Finset.sum_range_succ (f := fun i => h (i + 1) * (p (i + 1) - p i)) k]
      ring

/-- The trader's banked value: the inherited `P n`, with `v i = P (i+1) φ`, `p i = P i φ`. -/
noncomputable def banked (P : History) (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    dsWeight (t : ℝ) (ε : ℝ) (δ : ℝ) (a i : ℝ) (P i φ) * (P (i + 1) φ - P i φ)

/-- The trader's weighted forecast bias: the inherited `C n`. -/
noncomputable def bias (P : History) (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    dsWeight (t : ℝ) (ε : ℝ) (δ : ℝ) (a i : ℝ) (P i φ) * (P (i + 1) φ - (a i : ℝ))

/-- The accumulated violation weight: the inherited `W n`. -/
noncomputable def weight (P : History) (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, dsWeight (t : ℝ) (ε : ℝ) (δ : ℝ) (a i : ℝ) (P i φ)

/-- **The accounting identity.** The trader's `def:exploitation` net worth after day `n`, in
every world, is the still-open position plus exactly the inherited partial sum. This is the
bridge the inherited corpus lacked: it says what the no-Dutch-book criterion actually bounds,
and how that differs from what the inherited `hbdd` assumed it bounds. -/
theorem accelTrader_netWorth_eq (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ)
    (P : History) (v : PCWorld) (n : ℕ) :
    (accelTrader φ t ε δ a).netWorth P v n
      = dsWeight (t : ℝ) (ε : ℝ) (δ : ℝ) (a n : ℝ) (P n φ) * (v.payout φ - P n φ)
        + banked P φ t ε δ a n := by
  have hval : ∀ i : ℕ, ((accelTrader φ t ε δ a).strat i).value P v.payout
      = ((holdEF φ t ε δ a (i + 1)).denote P - (holdEF φ t ε δ a i).denote P)
          * (v.payout φ - P i φ) := by
    intro i
    simp only [accelTrader, Strategy.value, tradeEF, EF.denote_add, EF.denote_mul,
      EF.denote_const, Pi.add_apply, Pi.mul_apply, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    push_cast
    ring
  have hzero : (holdEF φ t ε δ a 0).denote P = 0 := by simp [holdEF]
  have hsucc : ∀ k, (holdEF φ t ε δ a (k + 1)).denote P
      = dsWeight (t : ℝ) (ε : ℝ) (δ : ℝ) (a k : ℝ) (P k φ) := by
    intro k
    simpa [holdEF] using weightEF_denote φ t ε δ a k P
  calc (accelTrader φ t ε δ a).netWorth P v n
      = ∑ i ∈ Finset.range (n + 1),
          ((holdEF φ t ε δ a (i + 1)).denote P - (holdEF φ t ε δ a i).denote P)
            * (v.payout φ - P i φ) := by
        simp only [Trader.netWorth]
        exact Finset.sum_congr rfl (fun i _ => hval i)
    _ = (holdEF φ t ε δ a (n + 1)).denote P * (v.payout φ - P n φ)
          + ∑ i ∈ Finset.range n,
              (holdEF φ t ε δ a (i + 1)).denote P * (P (i + 1) φ - P i φ) :=
        position_sum_eq (fun k => (holdEF φ t ε δ a k).denote P) (fun i => P i φ)
          (v.payout φ) hzero n
    _ = _ := by
        rw [hsucc n, banked]
        exact congrArg _ (Finset.sum_congr rfl (fun i _ => by rw [hsucc i]))

/-- The open position is worth at most one unit of cash either way: weights, payouts and
prices all lie in `[0,1]`. -/
theorem netWorth_sub_banked_abs_le (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ)
    (P : History) (hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1) (v : PCWorld) (n : ℕ) :
    |(accelTrader φ t ε δ a).netWorth P v n - banked P φ t ε δ a n| ≤ 1 := by
  rw [accelTrader_netWorth_eq]
  have hw0 := dsWeight_nonneg (t : ℝ) (ε : ℝ) (δ : ℝ) (a n : ℝ) (P n φ)
  have hw1 := dsWeight_le_one (t : ℝ) (ε : ℝ) (δ : ℝ) (a n : ℝ) (P n φ)
  have hp := hP n φ
  have hy : 0 ≤ v.payout φ ∧ v.payout φ ≤ 1 := by
    unfold PCWorld.payout
    by_cases h : v.Holds φ <;> simp [h]
  rw [abs_le]
  constructor <;> nlinarith [hy.1, hy.2, hp.1, hp.2]

/-- The per-day hypotheses of the ported chain, discharged from the construction: the weight
is nonnegative, and where it fires A is high and H is low. -/
theorem accel_partial_sum_ge (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (P : History)
    (hδ : (0 : ℝ) < (δ : ℝ)) (n : ℕ) :
    bias P φ t ε δ a n + (ε : ℝ) * weight P φ t ε δ a n ≤ banked P φ t ε δ a n :=
  profitPartialSum_ge
    (fun i => dsWeight (t : ℝ) (ε : ℝ) (δ : ℝ) (a i : ℝ) (P i φ))
    (fun i => P (i + 1) φ) (fun i => P i φ) (fun i => (a i : ℝ)) (t : ℝ) (ε : ℝ)
    (fun _ => dsWeight_nonneg _ _ _ _ _)
    (fun _ h => dsWeight_pos_imp_fst hδ h)
    (fun _ h => dsWeight_pos_imp_snd hδ h)
    n

/-- A real sequence diverging to `+∞` has a uniform lower bound. -/
theorem exists_lower_bound_of_tendsto_atTop {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    ∃ c : ℝ, ∀ n, c ≤ f n := by
  have hb : IsBoundedUnder (· ≥ ·) atTop f := ⟨0, hf.eventually_ge_atTop 0⟩
  obtain ⟨c, hc⟩ := hb.bddBelow_range
  exact ⟨c, fun n => hc (Set.mem_range_self n)⟩

/-! ### The criterion, applied

The step the inherited corpus assumed. `hbdd` is gone: what bounds the banked value is the
`IsLogicalInductor` instance, through the accounting identity.
-/

/-- **The criterion forces the exploitation branch shut.** Under the Logical Induction
Criterion for H's market, with the acceleration trader efficiently computable and A
calibrated, the weight accumulated where "A forecasts above `t` while H prices below
`t - ε`" cannot diverge.

Relative to the inherited `violationNotPersistent` this replaces the named hypothesis
`hbdd : ∃ M, ∀ n, P n ≤ M` by `IsLogicalInductor`, at the cost of three explicitly named
inputs: the emission certificate `hEC`, the consistency of the deductive stages `hworld`,
and calibration `hbias` — the last two being the same class of input the inherited statement
carried.

Kind `C` (composition). Provenance: the per-day and summation steps are (a), derived above;
`hbias` is (b), a Logical-Induction citation about A's market; `hEC` is (c), the disclosed
`dd:fuel` efficiency model of the pinned dependency, undischarged here; `hworld` is (a) for
any concrete process and (b) in general. **No inhabitation witness ships with this
statement**, so it is `unverified-nonvacuous`. -/
theorem weight_not_divergent (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ)
    (P : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor P DP]
    (hε : (0 : ℝ) < (ε : ℝ)) (hδ : (0 : ℝ) < (δ : ℝ))
    (hEC : EfficientlyComputable (accelTrader φ t ε δ a))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hbias : Tendsto
      (fun n => bias P φ t ε δ a n / weight P φ t ε δ a n) atTop (𝓝 0)) :
    ¬ Tendsto (weight P φ t ε δ a) atTop atTop := by
  intro hW
  refine hLI.noExploit _ hEC ?_
  have hprice : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have hbanked : Tendsto (banked P φ t ε δ a) atTop atTop :=
    profitDiverges _ _ _ (ε : ℝ) hε (accel_partial_sum_ge φ t ε δ a P hδ) hbias hW
  obtain ⟨c, hc⟩ := exists_lower_bound_of_tendsto_atTop hbanked
  constructor
  · refine ⟨c - 1, ?_⟩
    rintro x ⟨n, v, -, rfl⟩
    have habs := abs_le.mp (netWorth_sub_banked_abs_le φ t ε δ a P hprice v n)
    linarith [hc n, habs.1]
  · rintro ⟨M, hM⟩
    obtain ⟨n, hn⟩ := (tendsto_atTop.1 hbanked (M + 2)).exists
    obtain ⟨v, hv⟩ := hworld n
    have hmem : (accelTrader φ t ε δ a).netWorth P v n
        ∈ (accelTrader φ t ε δ a).plausibleAssessments P DP := ⟨n, v, hv, rfl⟩
    have habs := abs_le.mp (netWorth_sub_banked_abs_le φ t ε δ a P hprice v n)
    linarith [hM hmem, habs.2]

/-! ### Non-vacuity, as far as it goes -/

/-- The gate is not identically zero: there are parameters and prices at which the trader
actually trades. Guards against the degenerate reading in which `weight_not_divergent` holds
because the constructed trader never moves. -/
theorem dsWeight_pos_witness :
    0 < dsWeight (1/2 : ℝ) (1/8 : ℝ) (1/4 : ℝ) (1 : ℝ) (0 : ℝ) := by
  have h1 : softInd (1/4 : ℝ) ((1 : ℝ) - 1/2) = 1 := by
    simp only [softInd]
    norm_num
  have h2 : softInd (1/4 : ℝ) ((1/2 : ℝ) - 1/8 - 0) = 1 := by
    simp only [softInd]
    norm_num
  simp only [dsWeight, h1, h2]
  norm_num

/-- The open-position remainder in `accelTrader_netWorth_eq` is not removable: there is a
market, a world and a day at which the trader's net worth differs from the banked partial
sum. This is the necessity witness for the correction term — and the reason the inherited
`hbdd` (a bound on the partial sum) is not literally what the criterion delivers. -/
theorem netWorth_ne_banked_witness :
    ∃ (φ : Sentence) (t ε δ : ℚ) (a : ℕ → ℚ) (P : History) (v : PCWorld) (n : ℕ),
      (accelTrader φ t ε δ a).netWorth P v n ≠ banked P φ t ε δ a n := by
  refine ⟨LO.Propositional.Formula.atom 0, 1/2, 1/8, 1/4, fun _ => 1,
    fun _ _ => 0, fun _ => True, 0, ?_⟩
  have hpay : PCWorld.payout (fun _ => True) (LO.Propositional.Formula.atom 0) = 1 := by
    simp [PCWorld.payout, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  rw [accelTrader_netWorth_eq, hpay]
  norm_num [banked, dsWeight, softInd]

#print axioms roundProfit_ge
#print axioms profitPartialSum_ge
#print axioms eventually_half_weight_le
#print axioms profitDiverges
#print axioms violationNotPersistent
#print axioms profitDiverges_nonvacuous
#print axioms weightEF_rank
#print axioms weightEF_denote
#print axioms dsWeight_pos_imp_fst
#print axioms dsWeight_pos_imp_snd
#print axioms tradeEF_rank
#print axioms position_sum_eq
#print axioms accelTrader_netWorth_eq
#print axioms netWorth_sub_banked_abs_le
#print axioms accel_partial_sum_ge
#print axioms exists_lower_bound_of_tendsto_atTop
#print axioms weight_not_divergent
#print axioms dsWeight_pos_witness
#print axioms netWorth_ne_banked_witness

end Workspace.Deference.Contrib.FaithfulAcceleration
