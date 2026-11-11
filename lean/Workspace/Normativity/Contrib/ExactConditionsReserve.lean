/-
# Certifying an account: prefix reserves and the conditional bridge

Round `projects/normativity/rounds/2026-11-10-exact-conditions-capital/`.

Two ways to obtain the hypothesis of `DualCertifiedMarket.no_efficient_trader_exploits`
— an account bounded below over live prefixes.

* `reserve_sum_bound` — the inequality on real sequences behind A4.
* `PrefixReserve`, `DualCertifiedMarket.reserve_bound` — **the prefix reserve bound** (A4):
  a shrinking mass on world profiles, each day's mass on worlds live that day and
  averaging every row of that day to a nonnegative value, bounds the account below at
  every profile it still holds mass on.
* `DualCertifiedMarket.accountBounded_of_reserve` — a uniform lower bound on retained
  mass gives the hypothesis of A2.
* `DualCertifiedMarket.account_ge_neg_odds` — the constant two-point reserve, which is
  the shape of `OddsBankroll.Account.netWorth_ge_neg_odds`.
* `Bridge.bridge` — **the conditional bridge** (A7) on sequences, and
  `DualCertifiedMarket.accountBounded_of_frequency`, its instance for one floor per day.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ExactConditions

namespace Workspace.Normativity.Contrib.ExactConditions

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess

/-! ## A4 — the prefix reserve bound -/

/-- **The reserve inequality on sequences.**  `r n` is a mass on a finite profile space,
nonincreasing in `n` and of total mass one on day `0`; each day's mass averages that day's
increment `q n` to a nonnegative value; the cumulative sum is at most `U` wherever mass is
released and, on the last day, wherever mass other than `ω`'s remains.  Then the
cumulative sum at `ω` is at least `-U (1 - r N ω) / r N ω`. -/
theorem reserve_sum_bound {Ω : Type*} [Fintype Ω] (N : ℕ) (r q : ℕ → Ω → ℝ) (U : ℝ)
    (hr0 : ∀ n, n ≤ N → ∀ ω, 0 ≤ r n ω)
    (hanti : ∀ n, n < N → ∀ ω, r (n + 1) ω ≤ r n ω)
    (hmass : ∑ ω, r 0 ω = 1)
    (hrow : ∀ n, n ≤ N → 0 ≤ ∑ ω, r n ω * q n ω)
    (ω : Ω)
    (hrel : ∀ n, n < N → ∀ ω', r (n + 1) ω' < r n ω' →
      ∑ i ∈ Finset.range (n + 1), q i ω' ≤ U)
    (hfin : ∀ ω', ω' ≠ ω → 0 < r N ω' → ∑ i ∈ Finset.range (N + 1), q i ω' ≤ U)
    (hω : 0 < r N ω) :
    -(U * (1 - r N ω) / r N ω) ≤ ∑ i ∈ Finset.range (N + 1), q i ω := by
  classical
  have key : ∀ n, n ≤ N →
      0 ≤ ∑ ω', r n ω' * ∑ i ∈ Finset.range (n + 1), q i ω' + U * (1 - ∑ ω', r n ω') := by
    intro n
    induction n with
    | zero =>
        intro _
        have h := hrow 0 (Nat.zero_le _)
        simp only [zero_add, Finset.sum_range_one, hmass]
        linarith
    | succ n ih =>
        intro hn
        have h1 := ih (Nat.le_of_succ_le hn)
        have h2 := hrow (n + 1) hn
        have h3 : ∑ ω', (r n ω' - r (n + 1) ω') * ∑ i ∈ Finset.range (n + 1), q i ω' ≤
            ∑ ω', (r n ω' - r (n + 1) ω') * U := by
          refine Finset.sum_le_sum fun ω' _ => ?_
          rcases (hanti n hn ω').eq_or_lt with heq | hlt
          · rw [heq]; simp
          · exact mul_le_mul_of_nonneg_left (hrel n hn ω' hlt) (by linarith)
        have h4 : ∑ ω', r (n + 1) ω' * ∑ i ∈ Finset.range (n + 1 + 1), q i ω' =
            ∑ ω', r (n + 1) ω' * ∑ i ∈ Finset.range (n + 1), q i ω' +
              ∑ ω', r (n + 1) ω' * q (n + 1) ω' := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun ω' _ => ?_
          rw [Finset.sum_range_succ _ (n + 1)]
          ring
        simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul] at h3
        rw [h4]
        linarith
  have hN := key N le_rfl
  have hsplit : ∑ ω', r N ω' * ∑ i ∈ Finset.range (N + 1), q i ω' ≤
      r N ω * ∑ i ∈ Finset.range (N + 1), q i ω + U * (∑ ω', r N ω' - r N ω) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ω),
      ← Finset.add_sum_erase Finset.univ (r N) (Finset.mem_univ ω)]
    have : ∑ ω' ∈ Finset.univ.erase ω, r N ω' * ∑ i ∈ Finset.range (N + 1), q i ω' ≤
        ∑ ω' ∈ Finset.univ.erase ω, r N ω' * U := by
      refine Finset.sum_le_sum fun ω' hω' => ?_
      rcases (hr0 N le_rfl ω').eq_or_lt with heq | hlt
      · rw [← heq]; simp
      · exact mul_le_mul_of_nonneg_left (hfin ω' (Finset.ne_of_mem_erase hω') hlt) hlt.le
    rw [← Finset.sum_mul] at this
    linarith
  have hfinal : 0 ≤ r N ω * ∑ i ∈ Finset.range (N + 1), q i ω + U * (1 - r N ω) := by
    linarith
  rw [neg_le_iff_add_nonneg]
  have : ∑ i ∈ Finset.range (N + 1), q i ω + U * (1 - r N ω) / r N ω =
      (r N ω * ∑ i ∈ Finset.range (N + 1), q i ω + U * (1 - r N ω)) / r N ω := by
    field_simp
  rw [this]
  exact div_nonneg hfinal hω.le

/-- **A prefix reserve** through day `N`, against an assessment and a condition: a mass on
finitely many world profiles, shrinking day by day, each day's mass sitting on worlds live
*that day* and giving every row of that day a nonnegative average. -/
structure PrefixReserve (L : Assessment) (C : Condition) (N : ℕ) where
  /-- The profiles. -/
  Ω : Type
  [fintype : Fintype Ω]
  /-- The world each profile stands for. -/
  world : Ω → PCWorld
  /-- The day-`n` mass. -/
  r : ℕ → Ω → ℝ
  nonneg : ∀ n, n ≤ N → ∀ ω, 0 ≤ r n ω
  anti : ∀ n, n < N → ∀ ω, r (n + 1) ω ≤ r n ω
  mass : ∑ ω, r 0 ω = 1
  /-- Day-`n` mass sits on worlds live at day `n`. -/
  live : ∀ n, n ≤ N → ∀ ω, 0 < r n ω → L.Live n (world ω)
  /-- Every row of day `n` has nonnegative day-`n` average. -/
  row : ∀ n, n ≤ N → ∀ j, j < C.count n →
    0 ≤ ∑ ω, r n ω * (C.bet n j).eval (world ω).payout

attribute [instance] PrefixReserve.fintype

namespace DualCertifiedMarket

variable (M : DualCertifiedMarket)

/-- **The prefix reserve bound** (A4).  At a profile the reserve still holds mass on at
day `N`, the account is at least `-U (1 - r_N) / r_N`. -/
theorem reserve_bound {N : ℕ} (R : PrefixReserve M.L M.C N) (ω : R.Ω)
    (hω : 0 < R.r N ω) :
    -(M.U * (1 - R.r N ω) / R.r N ω) ≤ M.C.account M.mu N (R.world ω).payout := by
  refine reserve_sum_bound N R.r (fun n ω' => M.C.stake M.mu n (R.world ω').payout) M.U
    R.nonneg R.anti R.mass (fun n hn => ?_) ω (fun n hn ω' hlt => ?_)
    (fun ω' _ hpos => ?_) hω
  · simp only [Condition.stake, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun j hj => ?_
    have h := mul_nonneg (M.mu_nonneg n j (Finset.mem_range.mp hj))
      (R.row n hn j (Finset.mem_range.mp hj))
    rw [Finset.mul_sum] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun ω' _ => ?_))
    ring
  · exact M.account_le n _ (R.live n hn.le ω'
      (lt_of_le_of_lt (R.nonneg (n + 1) hn ω') hlt))
  · exact M.account_le N _ (R.live N le_rfl ω' hpos)

/-- **Retained mass gives the hypothesis of A2.**  If every world live at `N` is a profile
of some prefix reserve through `N` retaining mass at least `ρ > 0` on it, the account is
bounded below by `-U (1 - ρ) / ρ`. -/
theorem accountBounded_of_reserve (ρ : ℝ) (hρ : 0 < ρ)
    (h : ∀ N v, M.L.Live N v → ∃ (R : PrefixReserve M.L M.C N) (ω : R.Ω),
      R.world ω = v ∧ ρ ≤ R.r N ω) :
    M.AccountBounded (M.U * (1 - ρ) / ρ) := by
  intro N v hv
  obtain ⟨R, ω, rfl, hle⟩ := h N _ hv
  have hpos : 0 < R.r N ω := lt_of_lt_of_le hρ hle
  refine le_trans (neg_le_neg ?_) (M.reserve_bound R ω hpos)
  rw [div_le_div_iff₀ hpos hρ]
  nlinarith [mul_nonneg M.U_pos.le (sub_nonneg.mpr hle)]

/-- **The odds form.**  If a world `v'` live at `N` clears every row of every day through
`N` with a surplus that, scaled by `ρ`, covers the deficit of `w` on that row, the account
at `w` is at least `-ρ U`.  This is the constant two-point reserve
`(ρ / (1 + ρ), 1 / (1 + ρ))`, and the statement has the shape of
`OddsBankroll.Account.netWorth_ge_neg_odds` with the cap replaced by the ceiling. -/
theorem account_ge_neg_odds (ρ : ℝ) (hρ : 0 ≤ ρ) (N : ℕ) (v' w : PCWorld)
    (hv' : M.L.Live N v')
    (hdom : ∀ n, n ≤ N → ∀ j, j < M.C.count n →
      0 ≤ ρ * (M.C.bet n j).eval v'.payout + (M.C.bet n j).eval w.payout) :
    -(ρ * M.U) ≤ M.C.account M.mu N w.payout := by
  have h1ρ : 0 < 1 + ρ := by linarith
  let r : ℕ → Bool → ℝ := fun _ b => if b then ρ / (1 + ρ) else 1 / (1 + ρ)
  let wd : Bool → PCWorld := fun b => if b then v' else w
  have hmain := reserve_sum_bound N r
    (fun n b => M.C.stake M.mu n (wd b).payout) M.U
    (fun n _ b => by
      cases b
      · change 0 ≤ 1 / (1 + ρ); positivity
      · change 0 ≤ ρ / (1 + ρ); positivity)
    (fun n _ b => le_rfl)
    (by
      rw [Fintype.sum_bool]
      change ρ / (1 + ρ) + 1 / (1 + ρ) = 1
      rw [← add_div, div_eq_one_iff_eq h1ρ.ne']
      ring)
    (fun n hn => by
      rw [Fintype.sum_bool]
      change 0 ≤ ρ / (1 + ρ) * M.C.stake M.mu n v'.payout +
        1 / (1 + ρ) * M.C.stake M.mu n w.payout
      simp only [Condition.stake, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_nonneg fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      have h := mul_nonneg (mul_nonneg (M.mu_nonneg n j hj') (inv_nonneg.mpr h1ρ.le))
        (hdom n hn j hj')
      refine h.trans (le_of_eq ?_)
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring)
    false
    (fun n _ b hlt => absurd hlt (lt_irrefl _))
    (fun b hb _ => by
      cases b
      · exact absurd rfl hb
      · exact M.account_le N v' hv')
    (by change 0 < 1 / (1 + ρ); exact div_pos one_pos h1ρ)
  have hval : M.U * (1 - r N false) / r N false = ρ * M.U := by
    change M.U * (1 - 1 / (1 + ρ)) / (1 / (1 + ρ)) = ρ * M.U
    have h : 1 - 1 / (1 + ρ) = ρ * (1 / (1 + ρ)) := by
      rw [eq_comm, mul_one_div, div_eq_iff h1ρ.ne', sub_mul, one_div,
        inv_mul_cancel₀ h1ρ.ne']
      ring
    rw [h, ← mul_assoc, mul_div_assoc, div_self (div_pos one_pos h1ρ).ne', mul_one, mul_comm]
  rw [hval] at hmain
  exact hmain

end DualCertifiedMarket

/-! ## A7 — the conditional bridge, on sequences

One stake `mu n ≥ 0` a day on a bet paying `x n - c`, with `x n ∈ [0, 1]`.  `prior n` is
the account before day `n`; `margin n = U + 1 - prior n` is the distance to the ceiling
plus one; `ratio n = mu n / margin n` is the normalized stake. -/

namespace Bridge

variable (c U : ℝ) (x mu : ℕ → ℝ)

/-- The account before day `n`. -/
def prior (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, mu i * (x i - c)

/-- One plus the distance from the account before day `n` to the ceiling. -/
def margin (n : ℕ) : ℝ := U + 1 - prior c x mu n

/-- The normalized stake. -/
noncomputable def ratio (n : ℕ) : ℝ := mu n / margin c U x mu n

variable {c U x mu}

lemma prior_succ (n : ℕ) : prior c x mu (n + 1) = prior c x mu n + mu n * (x n - c) := by
  simp [prior, Finset.sum_range_succ]

/-- The frequency hypothesis: if the normalized stakes diverge, their `x`-weighted partial
sums eventually exceed the `c + γ` fraction. -/
def Frequency (c U γ : ℝ) (x mu : ℕ → ℝ) : Prop :=
  ¬ Summable (ratio c U x mu) → ∃ N₀, ∀ N, N₀ ≤ N →
    (c + γ) * ∑ i ∈ Finset.range N, ratio c U x mu i ≤
      ∑ i ∈ Finset.range N, ratio c U x mu i * x i

/-- **The conditional bridge** (A7), on sequences.  Under the per-day ceiling and the
frequency hypothesis, the normalized stakes are summable, the margin is bounded, the
stakes are summable, and every finite sub-sum of the account is at least `-c ∑ mu`. -/
theorem bridge {γ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hγ : 0 < γ)
    (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1) (hmu : ∀ n, 0 ≤ mu n)
    (hceil : ∀ n, prior c x mu n + mu n * (1 - c) ≤ U)
    (hfreq : Frequency c U γ x mu) :
    Summable (ratio c U x mu) ∧ (∃ Ymax, ∀ n, margin c U x mu n ≤ Ymax) ∧ Summable mu ∧
      ∀ (S : Finset ℕ) (y : ℕ → ℝ), (∀ n, 0 ≤ y n) →
        -(c * ∑' i, mu i) ≤ ∑ i ∈ S, mu i * (y i - c) := by
  have hprior : ∀ n, prior c x mu n ≤ U := by
    intro n
    induction n with
    | zero =>
        have h := hceil 0
        have : 0 ≤ mu 0 * (1 - c) := mul_nonneg (hmu 0) (by linarith)
        simp only [prior, Finset.range_zero, Finset.sum_empty] at h ⊢
        linarith
    | succ n ih =>
        rw [prior_succ]
        have : mu n * (x n - c) ≤ mu n * (1 - c) :=
          mul_le_mul_of_nonneg_left (by linarith [(hx n).2]) (hmu n)
        linarith [hceil n]
  have hY : ∀ n, 1 ≤ margin c U x mu n := fun n => by
    unfold margin; linarith [hprior n]
  have hYpos : ∀ n, 0 < margin c U x mu n := fun n => lt_of_lt_of_le one_pos (hY n)
  have hv0 : ∀ n, 0 ≤ ratio c U x mu n := fun n => div_nonneg (hmu n) (hYpos n).le
  have hvY : ∀ n, ratio c U x mu n * margin c U x mu n = mu n := fun n => by
    unfold ratio; field_simp [(hYpos n).ne']
  have hstep : ∀ n, margin c U x mu (n + 1) =
      margin c U x mu n * (1 - ratio c U x mu n * (x n - c)) := by
    intro n
    have h := hvY n
    unfold margin at h ⊢
    rw [prior_succ]
    linear_combination (x n - c) * h
  have hU1 : 0 < U + 1 := by have := hY 0; simp [margin, prior] at this; linarith
  have hexp : ∀ N, margin c U x mu N ≤
      (U + 1) * Real.exp (-∑ i ∈ Finset.range N, ratio c U x mu i * (x i - c)) := by
    intro N
    induction N with
    | zero => simp [margin, prior]
    | succ N ih =>
        rw [hstep, Finset.sum_range_succ, neg_add, Real.exp_add, ← mul_assoc]
        have h1 : 1 - ratio c U x mu N * (x N - c) ≤
            Real.exp (-(ratio c U x mu N * (x N - c))) := by
          have := Real.add_one_le_exp (-(ratio c U x mu N * (x N - c)))
          linarith
        have h0 : 0 ≤ 1 - ratio c U x mu N * (x N - c) := by
          have := hstep N
          have hpos := hYpos (N + 1)
          rw [this] at hpos
          exact ((mul_pos_iff_of_pos_left (hYpos N)).mp hpos).le
        calc margin c U x mu N * (1 - ratio c U x mu N * (x N - c))
            ≤ ((U + 1) * Real.exp (-∑ i ∈ Finset.range N, ratio c U x mu i * (x i - c))) *
                (1 - ratio c U x mu N * (x N - c)) := mul_le_mul_of_nonneg_right ih h0
          _ ≤ _ := mul_le_mul_of_nonneg_left h1
              (mul_nonneg hU1.le (Real.exp_pos _).le)
  have hsum : Summable (ratio c U x mu) := by
    by_contra hns
    obtain ⟨N₀, hN₀⟩ := hfreq hns
    have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hv0).mp hns
    obtain ⟨N, hNbig, hNge⟩ := ((Filter.tendsto_atTop.mp htend (U / γ + 1)).and
      (Filter.eventually_ge_atTop N₀)).exists
    set S := ∑ i ∈ Finset.range N, ratio c U x mu i with hS
    have hfr := hN₀ N hNge
    have hsplit : ∑ i ∈ Finset.range N, ratio c U x mu i * (x i - c) =
        ∑ i ∈ Finset.range N, ratio c U x mu i * x i - c * S := by
      rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hge : γ * S ≤ ∑ i ∈ Finset.range N, ratio c U x mu i * (x i - c) := by
      rw [hsplit]; linarith
    have h1 : 1 ≤ (U + 1) * Real.exp (-(γ * S)) :=
      (hY N).trans ((hexp N).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hge)) hU1.le))
    have h2 := Real.add_one_le_exp (γ * S)
    have h3 : Real.exp (γ * S) * Real.exp (-(γ * S)) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : Real.exp (γ * S) ≤ U + 1 := by
      calc Real.exp (γ * S) = Real.exp (γ * S) * 1 := (mul_one _).symm
        _ ≤ Real.exp (γ * S) * ((U + 1) * Real.exp (-(γ * S))) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = (U + 1) * (Real.exp (γ * S) * Real.exp (-(γ * S))) := by ring
        _ = U + 1 := by rw [h3, mul_one]
    have h5 : γ * S ≤ U := by linarith
    have h6 : S ≤ U / γ := by rw [le_div_iff₀ hγ]; linarith
    linarith
  have hbound : ∀ n, margin c U x mu n ≤
      (U + 1) * Real.exp (c * ∑' i, ratio c U x mu i) := by
    intro n
    refine (hexp n).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hU1.le)
    have h1 : -∑ i ∈ Finset.range n, ratio c U x mu i * (x i - c) ≤
        c * ∑ i ∈ Finset.range n, ratio c U x mu i := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := mul_nonneg (hv0 i) (hx i).1
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_left
      (hsum.sum_le_tsum _ fun i _ => hv0 i) hc0.le)
  have hmusum : Summable mu := by
    refine Summable.of_nonneg_of_le hmu (fun n => ?_)
      (hsum.mul_right ((U + 1) * Real.exp (c * ∑' i, ratio c U x mu i)))
    rw [← hvY n]
    exact mul_le_mul_of_nonneg_left (hbound n) (hv0 n)
  refine ⟨hsum, ⟨_, hbound⟩, hmusum, fun S y hy => ?_⟩
  have h1 : -(c * ∑ i ∈ S, mu i) ≤ ∑ i ∈ S, mu i * (y i - c) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_nonneg (hmu i) (hy i)
    linarith
  have h2 : c * ∑ i ∈ S, mu i ≤ c * ∑' i, mu i :=
    mul_le_mul_of_nonneg_left (hmusum.sum_le_tsum _ fun i _ => hmu i) hc0.le
  linarith

end Bridge

/-! ## A7 — the instance: one fresh floor per day, settled the next -/

namespace DualCertifiedMarket

variable (M : DualCertifiedMarket)

/-- The realized truth value of the day-`n` sentence, as a payout. -/
def realized (b : ℕ → Bool) (n : ℕ) : ℝ := if b n then 1 else 0

/-- **The conditional bridge, instantiated** (A7).  One floor `c ≤ price (φ n)` per day;
by day `N` every live world agrees with the realized truth `b i` of `φ i` for `i < N`, and
on day `n` a world affirming `φ n` is still live.  If the realized normalized stakes
satisfy the frequency hypothesis, the account is bounded below, by `c ∑ mu`. -/
theorem accountBounded_of_frequency (φ : ℕ → Sentence) (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1)
    (hC : M.C = floors φ (fun _ => c)) (b : ℕ → Bool)
    (hsettle : ∀ N v, M.L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
    (hfresh : ∀ n, ∃ v, M.L.Live n v ∧ v.Holds (φ n))
    (γ : ℝ) (hγ : 0 < γ)
    (hfreq : Bridge.Frequency (c : ℝ) M.U γ (realized b) (fun n => M.mu n 0)) :
    M.AccountBounded ((c : ℝ) * ∑' n, M.mu n 0) := by
  have hc0' : (0 : ℝ) < c := by exact_mod_cast hc0
  have hc1' : (c : ℝ) < 1 := by exact_mod_cast hc1
  have hmu : ∀ n, 0 ≤ M.mu n 0 := fun n => M.mu_nonneg n 0 (by rw [hC]; exact Nat.one_pos)
  have hx : ∀ n, 0 ≤ realized b n ∧ realized b n ≤ 1 := fun n => by
    unfold realized; split_ifs <;> constructor <;> norm_num
  have hacc : ∀ N (v : PCWorld), M.C.account M.mu N v.payout =
      ∑ n ∈ Finset.range (N + 1), M.mu n 0 * (v.payout (φ n) - (c : ℝ)) := by
    intro N v; rw [hC, floors_account]
  have hceil : ∀ n, Bridge.prior (c : ℝ) (realized b) (fun n => M.mu n 0) n +
      M.mu n 0 * (1 - (c : ℝ)) ≤ M.U := by
    intro n
    obtain ⟨v, hv, hφ⟩ := hfresh n
    have h := M.account_le n v hv
    rw [hacc, Finset.sum_range_succ, payout_of_holds hφ] at h
    refine le_trans (le_of_eq ?_) h
    congr 1
    unfold Bridge.prior
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiff := hsettle n v hv i (Finset.mem_range.mp hi)
    unfold realized
    by_cases hb : b i = true
    · rw [if_pos hb, payout_of_holds (hiff.mpr hb)]
    · rw [if_neg hb, payout_of_not_holds (fun h => hb (hiff.mp h))]
  obtain ⟨_, _, _, hlow⟩ := Bridge.bridge hc0' hc1' hγ hx hmu hceil hfreq
  intro N v _
  rw [hacc]
  exact hlow (Finset.range (N + 1)) (fun n => v.payout (φ n)) fun n => (payout_cube v _).1

/-- The instance's conclusion: no efficiently computable trader exploits. -/
theorem no_exploit_of_frequency (φ : ℕ → Sentence) (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1)
    (hC : M.C = floors φ (fun _ => c)) (b : ℕ → Bool)
    (hsettle : ∀ N v, M.L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
    (hfresh : ∀ n, ∃ v, M.L.Live n v ∧ v.Holds (φ n))
    (γ : ℝ) (hγ : 0 < γ)
    (hfreq : Bridge.Frequency (c : ℝ) M.U γ (realized b) (fun n => M.mu n 0))
    (Tr : Trader) (hTr : EfficientlyComputable Tr) : ¬ M.L.Exploits Tr M.P :=
  M.no_efficient_trader_exploits
    (M.accountBounded_of_frequency φ c hc0 hc1 hC b hsettle hfresh γ hγ hfreq) Tr hTr

end DualCertifiedMarket

end Workspace.Normativity.Contrib.ExactConditions

#print axioms Workspace.Normativity.Contrib.ExactConditions.reserve_sum_bound
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.reserve_bound
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.accountBounded_of_reserve
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.account_ge_neg_odds
#print axioms Workspace.Normativity.Contrib.ExactConditions.Bridge.bridge
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.accountBounded_of_frequency
#print axioms Workspace.Normativity.Contrib.ExactConditions.DualCertifiedMarket.no_exploit_of_frequency
