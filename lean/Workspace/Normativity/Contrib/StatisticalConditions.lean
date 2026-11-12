/-
# Statistical conditions: the cost of losses, stakes, and slack floors

Round `projects/normativity/rounds/2026-11-12-statistical-conditions/`.

One floor `c ≤ price (φ n)` per day on a fresh sentence settled the next day, realized
values `x n`, stakes `mu n ≥ 0`, account `∑ mu n (x n - c)`, ceiling `U`.

* `Losses.headroom_le`, `Losses.account_ge`, `Losses.compound_prior`,
  `Losses.compound_ceiling` — the account after `R` lost instances is at least
  `-U ((1 - c)^-(R + 1) - 1)` with the open instance counted, and a staker that stakes its
  whole headroom on each lost instance attains it.
* `DualCertifiedMarket.account_ge_of_losses`, `accountBounded_of_finite_losses` — the
  market form; `finiteLosses_witness` inhabits it with a truth sequence that is not all one.
* `Stakes.abel_bound`, `Stakes.unit_bounded_staked_unbounded`,
  `Stakes.unit_unbounded_staked_bounded` — unit stakes against market stakes.
* `DualCertifiedMarket.stake_prices_le` — the multipliers are slack where the rows are:
  the staked value of the day's rows at the posted prices is at most the day's tolerance.
* `DualCertifiedMarket.account_ge_slack`, `accountBounded_of_eventually_slack` — a floor
  eventually cleared by a margin costs a bounded account.
* `Frequency.gain_bddAbove` — a weighting along which the frequency is at least `c + γ`
  gains a bounded amount by selling at `c`.
* `TableMixture.*` — a geometric mixture of finitely supported stakers under the summed
  ceiling whose account is unbounded exactly when the weight ratio is at least `1 - c`.
* `thresholdBuyer`, `thresholdBuyer_exploits`, `DualCertifiedMarket.bounded_or_buyer_exploits`
  — under frequency at least `c + γ` along the one weighting that reads whether the price
  is within `δ < γ` of the floor, either the account is bounded below or the buyer at
  those prices exploits.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ExactConditionsFloor
import Workspace.Normativity.Contrib.ExactConditionsReserve

namespace Workspace.Normativity.Contrib.StatisticalConditions

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.AssessmentFirm
open Workspace.Normativity.Contrib.ExactConditions

/-! ## 1. The cost of finitely many losses -/

namespace Losses

open Bridge

/-- The instances before `n` whose realized value is below the strength. -/
noncomputable def lost (c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => x i < c).card

lemma lost_succ_of_lt {c : ℝ} {x : ℕ → ℝ} {n : ℕ} (h : x n < c) :
    lost c x (n + 1) = lost c x n + 1 := by
  unfold lost
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h,
    Finset.card_insert_of_notMem (by simp)]

lemma lost_succ_of_not_lt {c : ℝ} {x : ℕ → ℝ} {n : ℕ} (h : ¬ x n < c) :
    lost c x (n + 1) = lost c x n := by
  unfold lost
  rw [Finset.range_add_one, Finset.filter_insert, if_neg h]

lemma lost_mono (c : ℝ) (x : ℕ → ℝ) : Monotone (lost c x) :=
  monotone_nat_of_le_succ fun n => by
    by_cases h : x n < c
    · rw [lost_succ_of_lt h]; exact Nat.le_succ _
    · rw [lost_succ_of_not_lt h]

variable {c U : ℝ} {x mu : ℕ → ℝ}

/-- **Headroom after losses.**  Under the per-day ceiling, the distance from the settled
account to the ceiling grows by a factor of at most `(1 - c)⁻¹` at each lost instance and
does not grow otherwise. -/
theorem headroom_le (hc0 : 0 ≤ c) (hc1 : c < 1) (hx : ∀ n, 0 ≤ x n) (hmu : ∀ n, 0 ≤ mu n)
    (hceil : ∀ n, prior c x mu n + mu n * (1 - c) ≤ U) (n : ℕ) :
    U - prior c x mu n ≤ U * ((1 - c)⁻¹) ^ lost c x n := by
  have h1c : 0 < 1 - c := by linarith
  have ha : 1 ≤ (1 - c)⁻¹ := (one_le_inv₀ h1c).mpr (by linarith)
  induction n with
  | zero => simp [prior, lost]
  | succ n ih =>
      rw [prior_succ]
      have hstake : mu n * (1 - c) ≤ U - prior c x mu n := by linarith [hceil n]
      by_cases hlt : x n < c
      · rw [lost_succ_of_lt hlt, pow_succ, ← mul_assoc]
        have h1 : U - (prior c x mu n + mu n * (x n - c)) ≤
            (U - prior c x mu n) + c * mu n := by nlinarith [mul_nonneg (hmu n) (hx n)]
        have h2 : (U - prior c x mu n) + c * mu n ≤ (U - prior c x mu n) * (1 - c)⁻¹ := by
          rw [le_mul_inv_iff₀ h1c]
          nlinarith
        exact (h1.trans h2).trans (mul_le_mul_of_nonneg_right ih (by positivity))
      · rw [lost_succ_of_not_lt hlt]
        have : 0 ≤ mu n * (x n - c) := mul_nonneg (hmu n) (by linarith [not_lt.mp hlt])
        linarith

/-- **The cost of losses**, the open instance included.  After the instances before `n`,
of which `lost c x n` were lost, and with instance `n` open at any nonnegative value `y`,
the account is at least `-U ((1 - c)^-(lost + 1) - 1)`. -/
theorem account_ge (hc0 : 0 ≤ c) (hc1 : c < 1) (hx : ∀ n, 0 ≤ x n) (hmu : ∀ n, 0 ≤ mu n)
    (hceil : ∀ n, prior c x mu n + mu n * (1 - c) ≤ U) (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    -(U * (((1 - c)⁻¹) ^ (lost c x n + 1) - 1)) ≤ prior c x mu n + mu n * (y - c) := by
  have h1c : 0 < 1 - c := by linarith
  have h := headroom_le hc0 hc1 hx hmu hceil n
  have hstake : mu n * (1 - c) ≤ U - prior c x mu n := by linarith [hceil n]
  have h2 : (U - prior c x mu n) + c * mu n ≤ (U - prior c x mu n) * (1 - c)⁻¹ := by
    rw [le_mul_inv_iff₀ h1c]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_right h (show (0 : ℝ) ≤ (1 - c)⁻¹ by positivity)
  rw [pow_succ]
  nlinarith [mul_nonneg (hmu n) hy, h2, h3]

/-- The settled account alone: at least `-U ((1 - c)^-lost - 1)`. -/
theorem prior_ge (hc0 : 0 ≤ c) (hc1 : c < 1) (hx : ∀ n, 0 ≤ x n) (hmu : ∀ n, 0 ≤ mu n)
    (hceil : ∀ n, prior c x mu n + mu n * (1 - c) ≤ U) (n : ℕ) :
    -(U * (((1 - c)⁻¹) ^ lost c x n - 1)) ≤ prior c x mu n := by
  have := headroom_le hc0 hc1 hx hmu hceil n
  linarith

/-- **The compounding staker**: nothing on an instance that will not be lost, the whole
headroom on one that will. -/
noncomputable def compound (c U : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if x n < c then U * ((1 - c)⁻¹) ^ (lost c x n + 1) else 0

lemma compound_nonneg (hc1 : c < 1) (hU : 0 ≤ U) (n : ℕ) : 0 ≤ compound c U x n := by
  have h1c : 0 < 1 - c := by linarith
  unfold compound
  split_ifs
  · positivity
  · exact le_rfl

/-- **Tightness.**  Where every lost instance settles at zero, the compounding staker's
settled account is exactly `-U ((1 - c)^-lost - 1)`. -/
theorem compound_prior (hc1 : c < 1) (hzero : ∀ n, x n < c → x n = 0) (n : ℕ) :
    prior c x (compound c U x) n = -(U * (((1 - c)⁻¹) ^ lost c x n - 1)) := by
  have h1c : (1 - c) ≠ 0 := by linarith
  induction n with
  | zero => simp [prior, lost]
  | succ n ih =>
      rw [prior_succ, ih]
      by_cases hlt : x n < c
      · rw [lost_succ_of_lt hlt, compound, if_pos hlt, hzero n hlt, pow_succ]
        field_simp
        ring
      · rw [lost_succ_of_not_lt hlt, compound, if_neg hlt]
        ring

/-- The compounding staker meets the per-day ceiling, with equality on each lost
instance. -/
theorem compound_ceiling (hc1 : c < 1) (hU : 0 ≤ U) (hzero : ∀ n, x n < c → x n = 0)
    (n : ℕ) : prior c x (compound c U x) n + compound c U x n * (1 - c) ≤ U := by
  have h1c : 0 < 1 - c := by linarith
  rw [compound_prior hc1 hzero]
  unfold compound
  split_ifs with hlt
  · rw [pow_succ]
    apply le_of_eq
    field_simp
    ring
  · have : 0 ≤ U * ((1 - c)⁻¹) ^ lost c x n := by positivity
    linarith

end Losses

/-! ## 1, market form -/

namespace DualCertifiedMarket

open ExactConditions.DualCertifiedMarket

variable (M : ExactConditions.DualCertifiedMarket)

/-- One floor per day at `c`, settled by the next day: the account at a world live at `N`
is the settled account plus the open instance. -/
lemma account_eq_prior (φ : ℕ → Sentence) (c : ℚ) (hC : M.C = floors φ (fun _ => c))
    (b : ℕ → Bool)
    (hsettle : ∀ N v, M.L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
    (N : ℕ) (v : PCWorld) (hv : M.L.Live N v) :
    M.C.account M.mu N v.payout =
      Bridge.prior (c : ℝ) (realized b) (fun n => M.mu n 0) N +
        M.mu N 0 * (v.payout (φ N) - (c : ℝ)) := by
  rw [hC, floors_account, Finset.sum_range_succ]
  congr 1
  unfold Bridge.prior
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiff := hsettle N v hv i (Finset.mem_range.mp hi)
  unfold realized
  by_cases hb : b i = true
  · rw [if_pos hb, payout_of_holds (hiff.mpr hb)]
  · rw [if_neg hb, payout_of_not_holds (fun h => hb (hiff.mp h))]

/-- The per-day ceiling on the realized sequence, from the account ceiling at a live
world affirming the day's sentence. -/
lemma ceiling_of_fresh (φ : ℕ → Sentence) (c : ℚ) (hC : M.C = floors φ (fun _ => c))
    (b : ℕ → Bool)
    (hsettle : ∀ N v, M.L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
    (hfresh : ∀ n, ∃ v, M.L.Live n v ∧ v.Holds (φ n)) (n : ℕ) :
    Bridge.prior (c : ℝ) (realized b) (fun n => M.mu n 0) n +
      M.mu n 0 * (1 - (c : ℝ)) ≤ M.U := by
  obtain ⟨v, hv, hφ⟩ := hfresh n
  have h := M.account_le n v hv
  rw [account_eq_prior M φ c hC b hsettle n v hv, payout_of_holds hφ] at h
  exact h

lemma realized_nonneg (b : ℕ → Bool) (n : ℕ) : 0 ≤ realized b n := by
  unfold realized; split_ifs <;> norm_num

/-- **The cost of losses, in a dual-certified market.**  One floor per day at `c`, settled
by the next day.  At a world live at `N` the account is at least
`-U ((1 - c)^-(R + 1) - 1)`, `R` the number of false instances before `N`. -/
theorem account_ge_of_losses (φ : ℕ → Sentence) (c : ℚ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hC : M.C = floors φ (fun _ => c)) (b : ℕ → Bool)
    (hsettle : ∀ N v, M.L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
    (hfresh : ∀ n, ∃ v, M.L.Live n v ∧ v.Holds (φ n))
    (N : ℕ) (v : PCWorld) (hv : M.L.Live N v) :
    -(M.U * (((1 - (c : ℝ))⁻¹) ^ (Losses.lost (c : ℝ) (realized b) N + 1) - 1)) ≤
      M.C.account M.mu N v.payout := by
  rw [account_eq_prior M φ c hC b hsettle N v hv]
  exact Losses.account_ge (by exact_mod_cast hc0) (by exact_mod_cast hc1) (realized_nonneg b)
    (fun n => M.mu_nonneg n 0 (by rw [hC]; exact Nat.one_pos))
    (ceiling_of_fresh M φ c hC b hsettle hfresh) N (payout_cube v _).1

/-- **A schema with at most `R` lost instances is affordable**, with an explicit bound. -/
theorem accountBounded_of_finite_losses (φ : ℕ → Sentence) (c : ℚ) (hc0 : 0 ≤ c)
    (hc1 : c < 1) (hC : M.C = floors φ (fun _ => c)) (b : ℕ → Bool)
    (hsettle : ∀ N v, M.L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
    (hfresh : ∀ n, ∃ v, M.L.Live n v ∧ v.Holds (φ n))
    (R : ℕ) (hR : ∀ N, Losses.lost (c : ℝ) (realized b) N ≤ R) :
    M.AccountBounded (M.U * (((1 - (c : ℝ))⁻¹) ^ (R + 1) - 1)) := by
  intro N v hv
  have hc1' : (c : ℝ) < 1 := by exact_mod_cast hc1
  have hc0' : (0 : ℝ) ≤ c := by exact_mod_cast hc0
  have ha : 1 ≤ (1 - (c : ℝ))⁻¹ := (one_le_inv₀ (by linarith)).mpr (by linarith)
  refine le_trans (neg_le_neg ?_) (account_ge_of_losses M φ c hc0 hc1 hC b hsettle hfresh N v hv)
  have hpow : ((1 - (c : ℝ))⁻¹) ^ (Losses.lost (c : ℝ) (realized b) N + 1) ≤
      ((1 - (c : ℝ))⁻¹) ^ (R + 1) := pow_le_pow_right₀ ha (Nat.succ_le_succ (hR N))
  nlinarith [M.U_pos]

end DualCertifiedMarket

/-! ### The witness: a truth sequence that is not all one -/

/-- The process settling atom `k` on day `k + 1` at the value `b k`. -/
def truthProcess (b : ℕ → Bool) : DeductiveProcess where
  D n := (Finset.range n).image fun k => if b k then (.atom k : Sentence) else ∼(.atom k)
  mono n := Finset.image_subset_image (Finset.range_subset_range.mpr (Nat.le_succ n))

/-- The world giving atom `k` the value `b k` below `N` and true from `N` on. -/
def truthWorld (b : ℕ → Bool) (N : ℕ) : PCWorld := boolPCWorld fun k => if k < N then b k else true

lemma truthWorld_holds_atom (b : ℕ → Bool) (N k : ℕ) :
    (truthWorld b N).Holds (.atom k) ↔ (if k < N then b k else true) = true := by
  rw [PCWorld.holds_atom]
  simp [truthWorld, boolPCWorld]

lemma truthWorld_live (b : ℕ → Bool) (N : ℕ) :
    (ofDeductiveProcess (truthProcess b)).Live N (truthWorld b N) := by
  intro φ hφ
  simp only [truthProcess, Finset.mem_image, Finset.mem_range] at hφ
  obtain ⟨k, hk, rfl⟩ := hφ
  by_cases hb : b k = true
  · rw [if_pos hb, truthWorld_holds_atom, if_pos hk]; exact hb
  · rw [if_neg hb, PCWorld.holds_neg, truthWorld_holds_atom, if_pos hk]; exact hb

lemma truthProcess_settle (b : ℕ → Bool) (N : ℕ) (v : PCWorld)
    (hv : (ofDeductiveProcess (truthProcess b)).Live N v) (i : ℕ) (hi : i < N) :
    v.Holds (.atom i) ↔ b i = true := by
  have hmem : (if b i then (.atom i : Sentence) else ∼(.atom i)) ∈ (truthProcess b).D N := by
    simp only [truthProcess, Finset.mem_image, Finset.mem_range]
    exact ⟨i, hi, rfl⟩
  have h := hv _ hmem
  by_cases hb : b i = true
  · rw [if_pos hb] at h; exact ⟨fun _ => hb, fun _ => h⟩
  · rw [if_neg hb, PCWorld.holds_neg] at h; exact ⟨fun h' => absurd h' h, fun h' => absurd h' hb⟩

lemma truthProcess_fresh (b : ℕ → Bool) (n : ℕ) :
    ∃ v, (ofDeductiveProcess (truthProcess b)).Live n v ∧ v.Holds (.atom n) :=
  ⟨truthWorld b n, truthWorld_live b n, by
    rw [truthWorld_holds_atom, if_neg (lt_irrefl n)]⟩

/-- False on day `0`, true after. -/
def oneLoss : ℕ → Bool := fun n => decide (n ≠ 0)

lemma lost_oneLoss (c : ℝ) (hc1 : c ≤ 1) (N : ℕ) :
    Losses.lost c (ExactConditions.DualCertifiedMarket.realized oneLoss) N ≤ 1 := by
  unfold Losses.lost
  have hsub : ((Finset.range N).filter fun i =>
      ExactConditions.DualCertifiedMarket.realized oneLoss i < c) ⊆ {0} := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_singleton]
    by_contra hne
    have : ExactConditions.DualCertifiedMarket.realized oneLoss i = 1 := by
      simp [ExactConditions.DualCertifiedMarket.realized, oneLoss, hne]
    linarith [hi.2]
  exact (Finset.card_le_card hsub).trans (by simp)

/-- **Matter 1, inhabited.**  Fresh atoms floored at a constant `c ∈ (0, 1)`, the first of
which settles false: the floors are not entailed, the day-`0` instance is lost, the
account is bounded below by `3 ((1 - c)^-2 - 1)`, and no efficiently computable trader
exploits the floor market. -/
theorem finiteLosses_witness (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) :
    oneLoss 0 = false ∧
      ((constantFresh c hc0.le hc1.le).market
        (ofDeductiveProcess (truthProcess oneLoss))).AccountBounded
          (3 * (((1 - (c : ℝ))⁻¹) ^ 2 - 1)) ∧
      ∀ Tr : Trader, EfficientlyComputable Tr →
        ¬ (ofDeductiveProcess (truthProcess oneLoss)).Exploits Tr
          ((constantFresh c hc0.le hc1.le).market
            (ofDeductiveProcess (truthProcess oneLoss))).P := by
  set M := (constantFresh c hc0.le hc1.le).market (ofDeductiveProcess (truthProcess oneLoss))
    with hM
  have hbound : M.AccountBounded (3 * (((1 - (c : ℝ))⁻¹) ^ 2 - 1)) := by
    have h := DualCertifiedMarket.accountBounded_of_finite_losses M (fun n => .atom n) c
      hc0.le hc1 rfl oneLoss (truthProcess_settle oneLoss) (truthProcess_fresh oneLoss) 1
      (lost_oneLoss (c : ℝ) (by exact_mod_cast hc1.le))
    rwa [hM, FloorSchedule.market_U] at h
  exact ⟨rfl, hbound, fun Tr hTr => M.no_efficient_trader_exploits hbound Tr hTr⟩

/-! ## 2. Unit stakes and market stakes -/

namespace Stakes

/-- Summation by parts, in the form used below. -/
lemma sum_mul_eq (mu d : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, mu i * d i =
      mu n * ∑ i ∈ Finset.range n, d i -
        ∑ i ∈ Finset.range n, (mu (i + 1) - mu i) * ∑ j ∈ Finset.range (i + 1), d j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun i =>
        (mu (i + 1) - mu i) * ∑ j ∈ Finset.range (i + 1), d j), Finset.sum_range_succ d]
      ring

/-- **Stakes of bounded variation preserve boundedness.**  If the partial sums of `d` are
bounded by `B`, the stakes by `Mb` and their total variation by `V`, the staked partial
sums are bounded by `B (Mb + V)`. -/
theorem abel_bound (mu d : ℕ → ℝ) (B Mb V : ℝ)
    (hd : ∀ n, |∑ i ∈ Finset.range n, d i| ≤ B) (hmu : ∀ n, |mu n| ≤ Mb)
    (hvar : ∀ n, ∑ i ∈ Finset.range n, |mu (i + 1) - mu i| ≤ V) (n : ℕ) :
    |∑ i ∈ Finset.range n, mu i * d i| ≤ B * (Mb + V) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hd 0)
  rw [sum_mul_eq]
  have h1 : |mu n * ∑ i ∈ Finset.range n, d i| ≤ Mb * B := by
    rw [abs_mul]
    exact mul_le_mul (hmu n) (hd n) (abs_nonneg _) ((abs_nonneg _).trans (hmu n))
  have h2 : |∑ i ∈ Finset.range n, (mu (i + 1) - mu i) * ∑ j ∈ Finset.range (i + 1), d j| ≤
      V * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i ∈ Finset.range n,
        |(mu (i + 1) - mu i) * ∑ j ∈ Finset.range (i + 1), d j| ≤ |mu (i + 1) - mu i| * B :=
      fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hd (i + 1)) (abs_nonneg _)
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hvar n) hB
  calc |mu n * ∑ i ∈ Finset.range n, d i -
        ∑ i ∈ Finset.range n, (mu (i + 1) - mu i) * ∑ j ∈ Finset.range (i + 1), d j|
      ≤ |mu n * ∑ i ∈ Finset.range n, d i| +
        |∑ i ∈ Finset.range n, (mu (i + 1) - mu i) * ∑ j ∈ Finset.range (i + 1), d j| :=
        abs_sub _ _
    _ ≤ Mb * B + V * B := add_le_add h1 h2
    _ = B * (Mb + V) := by ring

/-- True on even days, false on odd days. -/
def alt (n : ℕ) : ℝ := if n % 2 = 0 then 1 else 0

/-- One share on a day that settles true, two on a day that settles false. -/
def twoOnLoss (n : ℕ) : ℝ := if n % 2 = 0 then 1 else 2

lemma alt_unit_sum (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), (alt i - 1 / 2) = 0 ∧
      ∑ i ∈ Finset.range (2 * m + 1), (alt i - 1 / 2) = 1 / 2 := by
  induction m with
  | zero => exact ⟨by simp, by rw [Finset.sum_range_one]; norm_num [alt]⟩
  | succ m ih =>
      have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      have h1 : ∑ i ∈ Finset.range (2 * (m + 1)), (alt i - 1 / 2) = 0 := by
        rw [e1, Finset.sum_range_succ, ih.2]
        have : alt (2 * m + 1) = 0 := by simp [alt, Nat.add_mod]
        rw [this]; norm_num
      refine ⟨h1, ?_⟩
      rw [Finset.sum_range_succ, h1]
      have : alt (2 * (m + 1)) = 1 := by simp [alt]
      rw [this]; norm_num

lemma alt_staked_sum (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), twoOnLoss i * (alt i - 1 / 2) = -(m : ℝ) / 2 ∧
      ∑ i ∈ Finset.range (2 * m + 1), twoOnLoss i * (alt i - 1 / 2) = -(m : ℝ) / 2 + 1 / 2 := by
  induction m with
  | zero => exact ⟨by simp, by rw [Finset.sum_range_one]; norm_num [alt, twoOnLoss]⟩
  | succ m ih =>
      have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      have h1 : ∑ i ∈ Finset.range (2 * (m + 1)), twoOnLoss i * (alt i - 1 / 2) =
          -((m + 1 : ℕ) : ℝ) / 2 := by
        rw [e1, Finset.sum_range_succ, ih.2]
        have ha : alt (2 * m + 1) = 0 := by simp [alt, Nat.add_mod]
        have ht : twoOnLoss (2 * m + 1) = 2 := by simp [twoOnLoss, Nat.add_mod]
        rw [ha, ht]; push_cast; ring
      refine ⟨h1, ?_⟩
      rw [Finset.sum_range_succ, h1]
      have ha : alt (2 * (m + 1)) = 1 := by simp [alt]
      have ht : twoOnLoss (2 * (m + 1)) = 1 := by simp [twoOnLoss]
      rw [ha, ht]; push_cast; ring

/-- **Unit stakes bounded, market stakes not.**  At strength `1/2` on the alternating
sequence the unit-stake account takes the values `0` and `1/2`; the stakes `1` on true
days and `2` on false days meet the per-day ceiling `3/2` and their account after `2m`
days is `-m/2`. -/
theorem unit_bounded_staked_unbounded :
    (∀ n, |∑ i ∈ Finset.range n, (alt i - 1 / 2)| ≤ 1 / 2) ∧
      (∀ n, 0 ≤ twoOnLoss n) ∧
      (∀ n, Bridge.prior (1 / 2) alt twoOnLoss n + twoOnLoss n * (1 - 1 / 2) ≤ 3 / 2) ∧
      ∀ m : ℕ, Bridge.prior (1 / 2) alt twoOnLoss (2 * m) = -(m : ℝ) / 2 := by
  have hcases : ∀ n : ℕ, ∃ m, n = 2 * m ∨ n = 2 * m + 1 := fun n =>
    ⟨n / 2, by omega⟩
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, fun m => (alt_staked_sum m).1⟩
  · obtain ⟨m, rfl | rfl⟩ := hcases n
    · rw [(alt_unit_sum m).1]; norm_num
    · rw [(alt_unit_sum m).2]; norm_num
  · unfold twoOnLoss; split_ifs <;> norm_num
  · obtain ⟨m, rfl | rfl⟩ := hcases n
    · have ht : twoOnLoss (2 * m) = 1 := by simp [twoOnLoss]
      have := (alt_staked_sum m).1
      unfold Bridge.prior
      rw [this, ht]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · have ht : twoOnLoss (2 * m + 1) = 2 := by simp [twoOnLoss, Nat.add_mod]
      have := (alt_staked_sum m).2
      unfold Bridge.prior
      rw [this, ht]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith

/-- **Market stakes bounded, unit stakes not.**  At strength `1/2` on the sequence that
is always false, the unit-stake account after `n` days is `-n/2`; the stakes `2^-n` meet
the per-day ceiling `1/2` and their account stays above `-1`. -/
theorem unit_unbounded_staked_bounded :
    (∀ n : ℕ, ∑ _i ∈ Finset.range n, ((0 : ℝ) - 1 / 2) = -(n : ℝ) / 2) ∧
      (∀ n, Bridge.prior (1 / 2) (fun _ => 0) (fun i => (1 / 2 : ℝ) ^ i) n +
        (1 / 2 : ℝ) ^ n * (1 - 1 / 2) ≤ 1 / 2) ∧
      ∀ n, -1 ≤ Bridge.prior (1 / 2) (fun _ => 0) (fun i => (1 / 2 : ℝ) ^ i) n := by
  have hgeom : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i = 2 - 2 * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  have hprior : ∀ n : ℕ, Bridge.prior (1 / 2) (fun _ => 0) (fun i => (1 / 2 : ℝ) ^ i) n =
      -(1 - (1 / 2 : ℝ) ^ n) := by
    intro n
    unfold Bridge.prior
    have : ∀ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i * ((0 : ℝ) - 1 / 2) =
        -(1 / 2) * (1 / 2 : ℝ) ^ i := fun _ _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hgeom]
    ring
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  · rw [hprior]
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  · rw [hprior]
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    linarith

end Stakes

/-! ## 4. Slack floors -/

namespace DualCertifiedMarket

variable (M : ExactConditions.DualCertifiedMarket)

/-- A strategy is worth nothing when settled at the prices it was struck at. -/
lemma value_at_prices {n : ℕ} (T : Strategy n) (P : History) : T.value P (P n) = 0 := by
  unfold Strategy.value
  simp

/-- **The multipliers are slack where the rows are.**  The day's rows, staked by the
multipliers and evaluated at the posted prices, are worth at most the day's tolerance. -/
theorem stake_prices_le (n : ℕ) : M.C.stake M.mu n (M.P n) ≤ M.eps n := by
  have h := M.day_le n (M.P n) (M.P_range n)
  rw [value_at_prices] at h
  linarith

/-- One floor per day: the multiplier times the price's clearance of the floor is at most
the day's tolerance. -/
theorem mu_mul_clearance_le (φ : ℕ → Sentence) (c : ℚ) (hC : M.C = floors φ (fun _ => c))
    (n : ℕ) : M.mu n 0 * (M.P n (φ n) - (c : ℝ)) ≤ M.eps n := by
  have h := stake_prices_le M n
  rwa [hC, floors_stake] at h

/-- **The account charges only days near the floor.**  For every margin `δ > 0`, every
`N` and every cube valuation, the account is at least minus `c` times the tolerances over
`δ` plus the multipliers of the days through `N` whose price clears the floor by less
than `δ`. -/
theorem account_ge_slack (φ : ℕ → Sentence) (c : ℚ) (hc0 : 0 ≤ c)
    (hC : M.C = floors φ (fun _ => c)) (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (w : Sentence → ℝ)
    (hw : ∀ ψ, 0 ≤ w ψ) :
    -((c : ℝ) * (M.epsTotal / δ +
        ∑ n ∈ (Finset.range (N + 1)).filter (fun n => M.P n (φ n) < (c : ℝ) + δ), M.mu n 0)) ≤
      M.C.account M.mu N w := by
  classical
  have hc0' : (0 : ℝ) ≤ c := by exact_mod_cast hc0
  have hmu : ∀ n, 0 ≤ M.mu n 0 := fun n => M.mu_nonneg n 0 (by rw [hC]; exact Nat.one_pos)
  rw [hC, floors_account]
  have hterm : ∀ n ∈ Finset.range (N + 1),
      -((c : ℝ) * (M.eps n / δ + if M.P n (φ n) < (c : ℝ) + δ then M.mu n 0 else 0)) ≤
        M.mu n 0 * (w (φ n) - (c : ℝ)) := by
    intro n _
    have h1 : -((c : ℝ) * M.mu n 0) ≤ M.mu n 0 * (w (φ n) - (c : ℝ)) := by
      nlinarith [mul_nonneg (hmu n) (hw (φ n))]
    have heps : 0 ≤ M.eps n / δ := div_nonneg (M.eps_pos n).le hδ.le
    split_ifs with hlt
    · nlinarith
    · have hcl := mu_mul_clearance_le M φ c hC n
      have hle : M.mu n 0 ≤ M.eps n / δ := by
        rw [le_div_iff₀ hδ]
        nlinarith [hmu n, not_lt.mp hlt]
      nlinarith
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.sum_filter]
  have h : (∑ n ∈ Finset.range (N + 1), M.eps n) / δ ≤ M.epsTotal / δ :=
    div_le_div_of_nonneg_right (M.eps_sum_le N) hδ.le
  exact neg_le_neg (mul_le_mul_of_nonneg_left (by linarith) hc0')

/-- A bound on the multipliers of the days near the floor bounds the account. -/
theorem accountBounded_of_tight_sum (φ : ℕ → Sentence) (c : ℚ) (hc0 : 0 ≤ c)
    (hC : M.C = floors φ (fun _ => c)) (δ : ℝ) (hδ : 0 < δ) (T : ℝ)
    (hT : ∀ N, ∑ n ∈ (Finset.range (N + 1)).filter (fun n => M.P n (φ n) < (c : ℝ) + δ),
      M.mu n 0 ≤ T) :
    M.AccountBounded ((c : ℝ) * (M.epsTotal / δ + T)) := by
  intro N v _
  have hc0' : (0 : ℝ) ≤ c := by exact_mod_cast hc0
  refine le_trans (neg_le_neg ?_)
    (account_ge_slack M φ c hc0 hC δ hδ N v.payout fun ψ => (payout_cube v ψ).1)
  exact mul_le_mul_of_nonneg_left (by linarith [hT N]) hc0'

/-- **A floor eventually cleared by a margin costs a bounded account.**  If from day `N₀`
on the price of the day's sentence is at least `c + δ`, the account is bounded below by
`c (ε / δ + ∑_{n < N₀} mu n)`. -/
theorem accountBounded_of_eventually_slack (φ : ℕ → Sentence) (c : ℚ) (hc0 : 0 ≤ c)
    (hC : M.C = floors φ (fun _ => c)) (δ : ℝ) (hδ : 0 < δ) (N₀ : ℕ)
    (hslack : ∀ n, N₀ ≤ n → (c : ℝ) + δ ≤ M.P n (φ n)) :
    M.AccountBounded ((c : ℝ) * (M.epsTotal / δ + ∑ n ∈ Finset.range N₀, M.mu n 0)) := by
  have hmu : ∀ n, 0 ≤ M.mu n 0 := fun n => M.mu_nonneg n 0 (by rw [hC]; exact Nat.one_pos)
  refine accountBounded_of_tight_sum M φ c hc0 hC δ hδ _ fun N => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => hmu n
  rw [Finset.mem_filter] at hn
  rw [Finset.mem_range]
  by_contra hge
  exact absurd (hslack n (not_lt.mp hge)) (not_le.mpr hn.2)

end DualCertifiedMarket

/-! ## 4(a). One weighting -/

namespace Frequency

/-- **Frequency at least `c + γ` along a weighting**: if the weights are not summable,
their `x`-weighted partial sums eventually exceed the `c + γ` fraction of their partial
sums. -/
def Along (c γ : ℝ) (x w : ℕ → ℝ) : Prop :=
  ¬ Summable w → ∃ N₀, ∀ N, N₀ ≤ N →
    (c + γ) * ∑ i ∈ Finset.range N, w i ≤ ∑ i ∈ Finset.range N, w i * x i

/-- **Selling at the strength along a weighting of frequency at least it gains a bounded
amount.** -/
theorem gain_bddAbove {c γ : ℝ} {x w : ℕ → ℝ} (hc0 : 0 ≤ c) (hγ : 0 ≤ γ)
    (hw : ∀ n, 0 ≤ w n) (hx : ∀ n, 0 ≤ x n) (h : Along c γ x w) :
    ∃ B, ∀ N, ∑ i ∈ Finset.range N, w i * (c - x i) ≤ B := by
  have hsplit : ∀ N, ∑ i ∈ Finset.range N, w i * (c - x i) =
      c * ∑ i ∈ Finset.range N, w i - ∑ i ∈ Finset.range N, w i * x i := by
    intro N
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hle : ∀ N, ∑ i ∈ Finset.range N, w i * (c - x i) ≤ c * ∑ i ∈ Finset.range N, w i := by
    intro N
    rw [hsplit]
    have : 0 ≤ ∑ i ∈ Finset.range N, w i * x i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hx i)
    linarith
  by_cases hs : Summable w
  · exact ⟨c * ∑' i, w i, fun N => (hle N).trans
      (mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ fun i _ => hw i) hc0)⟩
  · obtain ⟨N₀, hN₀⟩ := h hs
    refine ⟨c * ∑ i ∈ Finset.range N₀, w i, fun N => ?_⟩
    have hB : 0 ≤ c * ∑ i ∈ Finset.range N₀, w i :=
      mul_nonneg hc0 (Finset.sum_nonneg fun i _ => hw i)
    rcases le_or_gt N₀ N with hge | hlt
    · have h1 := hN₀ N hge
      have h2 : 0 ≤ γ * ∑ i ∈ Finset.range N, w i :=
        mul_nonneg hγ (Finset.sum_nonneg fun i _ => hw i)
      rw [hsplit]
      nlinarith
    · exact (hle N).trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hlt.le) fun i _ _ => hw i) hc0)

end Frequency

/-- **The bridge's frequency hypothesis is summability of the normalized stakes.**  Under
the hypotheses of `Bridge.bridge`, `Bridge.Frequency` holds exactly when the normalized
stakes are summable: it is vacuous when they are, and the bridge makes them so. -/
theorem bridge_frequency_iff_summable {c U γ : ℝ} {x mu : ℕ → ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hγ : 0 < γ) (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1) (hmu : ∀ n, 0 ≤ mu n)
    (hceil : ∀ n, Bridge.prior c x mu n + mu n * (1 - c) ≤ U) :
    Bridge.Frequency c U γ x mu ↔ Summable (Bridge.ratio c U x mu) :=
  ⟨fun h => (Bridge.bridge hc0 hc1 hγ hx hmu hceil h).1, fun hs hns => absurd hs hns⟩

/-! ## 4(b). A mixture of tables -/

namespace TableMixture

open Bridge Losses

variable {c θ : ℝ} {x : ℕ → ℝ}

/-- **The table of `R` losses**, budget one: its whole wealth, at the floor's odds, on
each of the first `R` lost instances, and nothing after. -/
noncomputable def table (c : ℝ) (R : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if x n < c ∧ lost c x n < R then ((1 - c)⁻¹) ^ (lost c x n + 1) else 0

/-- **The mixture**: the table of `R` losses at weight `θ ^ R`, `R ≥ 1`, in closed form
(`stake_eq_tsum`). -/
noncomputable def stake (c θ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if x n < c then (θ / (1 - c)) ^ (lost c x n + 1) / (1 - θ) else 0

lemma stake_nonneg (hc1 : c < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (n : ℕ) : 0 ≤ stake c θ x n := by
  have h1c : 0 < 1 - c := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  unfold stake
  split_ifs
  · positivity
  · exact le_rfl

/-- The closed form is the weighted sum of the tables. -/
theorem stake_eq_tsum (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (n : ℕ) :
    stake c θ x n = ∑' R, θ ^ (R + 1) * table c (R + 1) x n := by
  by_cases hlt : x n < c
  · have hgeo := (hasSum_geometric_of_lt_one hθ0 hθ1).mul_left
      (θ ^ (lost c x n + 1) * ((1 - c)⁻¹) ^ (lost c x n + 1))
    have hshift : HasSum
        (fun R => θ ^ (R + lost c x n + 1) * table c (R + lost c x n + 1) x n)
        (θ ^ (lost c x n + 1) * ((1 - c)⁻¹) ^ (lost c x n + 1) * (1 - θ)⁻¹) := by
      have hfun : (fun R => θ ^ (R + lost c x n + 1) * table c (R + lost c x n + 1) x n) =
          fun R => θ ^ (lost c x n + 1) * ((1 - c)⁻¹) ^ (lost c x n + 1) * θ ^ R := by
        funext R
        rw [table, if_pos ⟨hlt, by omega⟩]
        ring
      rw [hfun]
      exact hgeo
    have hzero : ∑ i ∈ Finset.range (lost c x n), θ ^ (i + 1) * table c (i + 1) x n = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [table, if_neg (by
          intro h
          have := Finset.mem_range.mp hi
          omega)]
        ring
    have hsum : HasSum (fun R => θ ^ (R + 1) * table c (R + 1) x n)
        (θ ^ (lost c x n + 1) * ((1 - c)⁻¹) ^ (lost c x n + 1) * (1 - θ)⁻¹) := by
      refine (hasSum_nat_add_iff' (lost c x n)).mp ?_
      rw [hzero, sub_zero]
      exact hshift
    rw [hsum.tsum_eq, stake, if_pos hlt, div_pow, inv_pow]
    ring
  · have : ∀ R, θ ^ (R + 1) * table c (R + 1) x n = 0 := fun R => by
      rw [table, if_neg (fun h => hlt h.1)]; ring
    simp [stake, hlt, this]

/-- **Each table is bounded**: where every lost instance settles at zero, the settled
account of the table of `R` losses is `-((1 - c)^-min(lost, R) - 1)`. -/
theorem table_prior (hc1 : c < 1) (hzero : ∀ n, x n < c → x n = 0) (R n : ℕ) :
    prior c x (table c R x) n = -(((1 - c)⁻¹) ^ min (lost c x n) R - 1) := by
  have h1c : (1 - c) ≠ 0 := by linarith
  induction n with
  | zero => simp [prior, lost]
  | succ n ih =>
      rw [prior_succ, ih]
      by_cases hlt : x n < c
      · rw [lost_succ_of_lt hlt]
        by_cases hR : lost c x n < R
        · rw [table, if_pos ⟨hlt, hR⟩, hzero n hlt, min_eq_left hR.le,
            min_eq_left (Nat.succ_le_of_lt hR), pow_succ]
          field_simp
          ring
        · rw [table, if_neg (fun h => hR h.2), min_eq_right (not_lt.mp hR),
            min_eq_right ((not_lt.mp hR).trans (Nat.le_succ _))]
          ring
      · rw [lost_succ_of_not_lt hlt, table, if_neg (fun h => hlt h.1)]
        ring

/-- The mixture's settled account, where every lost instance settles at zero. -/
theorem prior_eq (hzero : ∀ n, x n < c → x n = 0) (n : ℕ) :
    prior c x (stake c θ x) n =
      -(c / (1 - θ)) * ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ (j + 1) := by
  induction n with
  | zero => simp [prior, lost]
  | succ n ih =>
      rw [prior_succ, ih]
      by_cases hlt : x n < c
      · rw [lost_succ_of_lt hlt, stake, if_pos hlt, hzero n hlt, Finset.sum_range_succ]
        ring
      · rw [lost_succ_of_not_lt hlt, stake, if_neg hlt]
        ring

lemma ceiling_aux (hc1 : c < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (k : ℕ) :
    θ * (θ / (1 - c)) ^ k - c * ∑ j ∈ Finset.range k, (θ / (1 - c)) ^ (j + 1) ≤ θ := by
  have h1c : 0 < 1 - c := by linarith
  have hr0 : 0 ≤ θ / (1 - c) := div_nonneg hθ0 h1c.le
  have hrc : θ / (1 - c) * (1 - c) = θ := div_mul_cancel₀ θ h1c.ne'
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hpow : 0 ≤ (θ / (1 - c)) ^ k := pow_nonneg hr0 k
      nlinarith [mul_nonneg hpow (mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ 1 - θ))]

/-- **The mixture meets the summed ceiling** `θ / (1 - θ)`, the tables' total weighted
budget. -/
theorem ceiling (hc0 : 0 ≤ c) (hc1 : c < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hzero : ∀ n, x n < c → x n = 0) (n : ℕ) :
    prior c x (stake c θ x) n + stake c θ x n * (1 - c) ≤ θ / (1 - θ) := by
  have h1c : 0 < 1 - c := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hr0 : 0 ≤ θ / (1 - c) := div_nonneg hθ0 h1c.le
  have hrc : θ / (1 - c) * (1 - c) = θ := div_mul_cancel₀ θ h1c.ne'
  rw [prior_eq hzero]
  have hG : 0 ≤ ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ (j + 1) :=
    Finset.sum_nonneg fun j _ => pow_nonneg hr0 _
  unfold stake
  split_ifs with hlt
  · have haux := ceiling_aux hc1 hθ0 hθ1 (lost c x n)
    rw [le_div_iff₀ h1θ]
    have e : (-(c / (1 - θ)) * ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ (j + 1) +
        (θ / (1 - c)) ^ (lost c x n + 1) / (1 - θ) * (1 - c)) * (1 - θ) =
        θ * (θ / (1 - c)) ^ lost c x n -
          c * ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ (j + 1) := by
      rw [pow_succ]
      field_simp
      ring
    rw [e]
    exact haux
  · have : 0 ≤ c / (1 - θ) * ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ (j + 1) :=
      mul_nonneg (div_nonneg hc0 h1θ.le) hG
    have : 0 ≤ θ / (1 - θ) := div_nonneg hθ0 h1θ.le
    linarith

/-- **Weight ratio at least `1 - c`: the mixture's account falls by at least
`c / (1 - θ)` at each loss**, so it is unbounded below on any sequence with infinitely
many losses, though each table's is bounded (`table_prior`). -/
theorem prior_le (hc0 : 0 ≤ c) (hc1 : c < 1) (hθ1 : θ < 1) (hθ : 1 - c ≤ θ)
    (hzero : ∀ n, x n < c → x n = 0) (n : ℕ) :
    prior c x (stake c θ x) n ≤ -(c / (1 - θ)) * lost c x n := by
  have h1c : 0 < 1 - c := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hr1 : 1 ≤ θ / (1 - c) := (one_le_div h1c).mpr hθ
  rw [prior_eq hzero]
  have hG : (lost c x n : ℝ) ≤ ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ (j + 1) := by
    have : ∑ _j ∈ Finset.range (lost c x n), (1 : ℝ) ≤
        ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ (j + 1) :=
      Finset.sum_le_sum fun j _ => one_le_pow₀ hr1
    simpa using this
  have hcθ : 0 ≤ c / (1 - θ) := div_nonneg hc0 h1θ.le
  nlinarith

/-- **Weight ratio below `1 - c`: the mixture's account is bounded below.** -/
theorem prior_ge (hc0 : 0 ≤ c) (hc1 : c < 1) (hθ0 : 0 ≤ θ) (hθ : θ < 1 - c)
    (hzero : ∀ n, x n < c → x n = 0) (n : ℕ) :
    -(c / (1 - θ) * (θ / (1 - c) * (1 - θ / (1 - c))⁻¹)) ≤ prior c x (stake c θ x) n := by
  have h1c : 0 < 1 - c := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hr0 : 0 ≤ θ / (1 - c) := div_nonneg hθ0 h1c.le
  have hr1 : θ / (1 - c) < 1 := (div_lt_one h1c).mpr hθ
  rw [prior_eq hzero]
  have hG : ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ (j + 1) ≤
      θ / (1 - c) * (1 - θ / (1 - c))⁻¹ := by
    have h1 : ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ (j + 1) =
        θ / (1 - c) * ∑ j ∈ Finset.range (lost c x n), (θ / (1 - c)) ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
    rw [h1, ← tsum_geometric_of_lt_one hr0 hr1]
    exact mul_le_mul_of_nonneg_left
      ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun j _ => pow_nonneg hr0 j) hr0
  have hcθ : 0 ≤ c / (1 - θ) := div_nonneg hc0 h1θ.le
  nlinarith

end TableMixture

/-! ## 4(c), 4(d). The buyer near the floor -/

/-- `min 1 (max 0 e)` as an expressible feature. -/
def clampEF (e : EF) : EF :=
  .mul (.const (-1)) (.max (.const (-1)) (.mul (.const (-1)) (.max (.const 0) e)))

lemma clampEF_denote (e : EF) (V : History) :
    (clampEF e).denote V = min 1 (max 0 (e.denote V)) := by
  simp only [clampEF, EF.denote, EF.denoteWith]
  push_cast
  rw [neg_one_mul, neg_one_mul, max_neg_neg, neg_neg]

lemma clampEF_rank (e : EF) : (clampEF e).rank = e.rank := by
  simp [clampEF, EF.rank]

/-- The day-`n` feature reading whether the price of `φ n` is within `δ` of `c`: one at
`c + δ/2` and below, zero at `c + δ` and above, linear between. -/
def thresholdFeature (φ : ℕ → Sentence) (c δ : ℚ) (n : ℕ) : EF :=
  clampEF (.mul (.const (2 / δ))
    (.add (.const (c + δ)) (.mul (.const (-1)) (.price (φ n) n))))

/-- The feature's value. -/
noncomputable def thresholdWeight (P : History) (φ : ℕ → Sentence) (c δ : ℚ) (n : ℕ) : ℝ :=
  min 1 (max 0 ((2 / (δ : ℝ)) * ((c : ℝ) + δ - P n (φ n))))

lemma thresholdFeature_denote (φ : ℕ → Sentence) (c δ : ℚ) (n : ℕ) (P : History) :
    (thresholdFeature φ c δ n).denote P = thresholdWeight P φ c δ n := by
  rw [thresholdFeature, clampEF_denote, thresholdWeight]
  simp only [EF.denote, EF.denoteWith]
  push_cast
  ring_nf

lemma thresholdFeature_rank (φ : ℕ → Sentence) (c δ : ℚ) (n : ℕ) :
    (thresholdFeature φ c δ n).rank ≤ n := by
  rw [thresholdFeature, clampEF_rank]
  simp [EF.rank]

lemma thresholdWeight_range (P : History) (φ : ℕ → Sentence) (c δ : ℚ) (n : ℕ) :
    0 ≤ thresholdWeight P φ c δ n ∧ thresholdWeight P φ c δ n ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

lemma lt_of_thresholdWeight_pos {P : History} {φ : ℕ → Sentence} {c δ : ℚ} (hδ : 0 < δ)
    {n : ℕ} (h : 0 < thresholdWeight P φ c δ n) : P n (φ n) < (c : ℝ) + δ := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  by_contra hge
  have hle : (2 / (δ : ℝ)) * ((c : ℝ) + δ - P n (φ n)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [not_lt.mp hge])
  have : thresholdWeight P φ c δ n ≤ 0 := by
    unfold thresholdWeight
    exact (min_le_right _ _).trans (max_le le_rfl hle)
  linarith

lemma clearance_of_thresholdWeight_lt_one {P : History} {φ : ℕ → Sentence} {c δ : ℚ}
    (hδ : 0 < δ) {n : ℕ} (h : thresholdWeight P φ c δ n < 1) :
    (c : ℝ) + (δ : ℝ) / 2 ≤ P n (φ n) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  by_contra hlt
  have hge : 1 ≤ (2 / (δ : ℝ)) * ((c : ℝ) + δ - P n (φ n)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ']
    linarith [not_le.mp hlt]
  have : 1 ≤ thresholdWeight P φ c δ n := by
    unfold thresholdWeight
    exact le_min le_rfl (le_max_of_le_right hge)
  linarith

/-- **The buyer near the floor**: on day `n` it buys `thresholdFeature` shares of `φ n`. -/
def thresholdBuyer (φ : ℕ → Sentence) (c δ : ℚ) : Trader where
  strat n :=
    { trades := [(thresholdFeature φ c δ n, φ n)]
      rank_le := by
        intro p hp
        rw [List.mem_singleton] at hp
        subst hp
        exact thresholdFeature_rank φ c δ n }

lemma thresholdBuyer_value (φ : ℕ → Sentence) (c δ : ℚ) (n : ℕ) (P : History)
    (w : Sentence → ℝ) :
    ((thresholdBuyer φ c δ).strat n).value P w =
      thresholdWeight P φ c δ n * (w (φ n) - P n (φ n)) := by
  simp [thresholdBuyer, Strategy.value, thresholdFeature_denote]

open ExactConditions.DualCertifiedMarket in
/-- **The buyer exploits a floor that stays tight on a sequence of high frequency.**  Any
history with prices at most one; sentences settled by the next day at the values `b`.  If
the threshold weights are not summable and the realized frequency along them is at least
`c + γ` with `δ < γ`, the buyer's value is bounded below and unbounded above over live
worlds. -/
theorem thresholdBuyer_exploits (L : Assessment) (P : History) (φ : ℕ → Sentence)
    (c δ : ℚ) (hc0 : 0 ≤ c) (hδ : 0 < δ) (hP1 : ∀ n, P n (φ n) ≤ 1) (b : ℕ → Bool)
    (hsettle : ∀ N v, L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
    (hlive : ∀ N, ∃ v, L.Live N v) (γ : ℝ) (hδγ : (δ : ℝ) < γ)
    (hfreq : Frequency.Along (c : ℝ) γ (realized b) (thresholdWeight P φ c δ))
    (hdiv : ¬ Summable (thresholdWeight P φ c δ)) :
    L.Exploits (thresholdBuyer φ c δ) P := by
  have hc0' : (0 : ℝ) ≤ c := by exact_mod_cast hc0
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  set W := thresholdWeight P φ c δ with hW
  have hW0 : ∀ n, 0 ≤ W n := fun n => (thresholdWeight_range P φ c δ n).1
  have hW1 : ∀ n, W n ≤ 1 := fun n => (thresholdWeight_range P φ c δ n).2
  obtain ⟨N₀, hN₀⟩ := hfreq hdiv
  -- the settled part of the buyer's value dominates the frequency surplus
  have hterm : ∀ n, W n * (realized b n - ((c : ℝ) + δ)) ≤ W n * (realized b n - P n (φ n)) := by
    intro n
    rcases (hW0 n).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · exact mul_le_mul_of_nonneg_left (by linarith [lt_of_thresholdWeight_pos hδ hpos]) (hW0 n)
  have hworth : ∀ N v, L.Live N v →
      ∑ n ∈ Finset.range N, W n * (realized b n - ((c : ℝ) + δ)) - 1 ≤
        (thresholdBuyer φ c δ).netWorth P v N := by
    intro N v hv
    unfold Trader.netWorth
    rw [Finset.sum_range_succ]
    have hopen : -1 ≤ ((thresholdBuyer φ c δ).strat N).value P v.payout := by
      rw [thresholdBuyer_value]
      have h1 : -1 ≤ v.payout (φ N) - P N (φ N) := by
        linarith [(payout_cube v (φ N)).1, hP1 N]
      nlinarith [hW0 N, hW1 N]
    have hsettled : ∑ n ∈ Finset.range N, W n * (realized b n - ((c : ℝ) + δ)) ≤
        ∑ n ∈ Finset.range N, ((thresholdBuyer φ c δ).strat n).value P v.payout := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [thresholdBuyer_value]
      have hiff := hsettle N v hv n (Finset.mem_range.mp hn)
      have hpay : v.payout (φ n) = realized b n := by
        unfold realized
        by_cases hb : b n = true
        · rw [if_pos hb, payout_of_holds (hiff.mpr hb)]
        · rw [if_neg hb, payout_of_not_holds (fun h => hb (hiff.mp h))]
      rw [hpay]
      exact hterm n
    linarith
  have hsurplus : ∀ N, ∑ n ∈ Finset.range N, W n * (realized b n - ((c : ℝ) + δ)) =
      ∑ n ∈ Finset.range N, W n * realized b n - ((c : ℝ) + δ) * ∑ n ∈ Finset.range N, W n := by
    intro N
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hsum0 : ∀ N, 0 ≤ ∑ n ∈ Finset.range N, W n := fun N =>
    Finset.sum_nonneg fun n _ => hW0 n
  refine ⟨⟨-(((c : ℝ) + δ) * ∑ n ∈ Finset.range N₀, W n + 1), ?_⟩, ?_⟩
  · rintro y ⟨N, v, hv, rfl⟩
    refine le_trans ?_ (hworth N v hv)
    rw [hsurplus]
    rcases le_or_gt N₀ N with hge | hlt
    · have h1 := hN₀ N hge
      have h2 : 0 ≤ (γ - δ) * ∑ n ∈ Finset.range N, W n :=
        mul_nonneg (by linarith) (hsum0 N)
      have h3 : 0 ≤ ((c : ℝ) + δ) * ∑ n ∈ Finset.range N₀, W n :=
        mul_nonneg (by linarith) (hsum0 N₀)
      nlinarith
    · have h1 : 0 ≤ ∑ n ∈ Finset.range N, W n * realized b n :=
        Finset.sum_nonneg fun n _ => mul_nonneg (hW0 n) (DualCertifiedMarket.realized_nonneg b n)
      have h2 : ∑ n ∈ Finset.range N, W n ≤ ∑ n ∈ Finset.range N₀, W n :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hlt.le) fun n _ _ => hW0 n
      have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ (c : ℝ) + δ)
      linarith
  · rintro ⟨B, hB⟩
    have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hW0).mp hdiv
    obtain ⟨N, hNbig, hNge⟩ := ((Filter.tendsto_atTop.mp htend ((B + 2) / (γ - δ))).and
      (Filter.eventually_ge_atTop N₀)).exists
    obtain ⟨v, hv⟩ := hlive N
    have h1 := hN₀ N hNge
    have h2 := hworth N v hv
    have h3 := hB ⟨N, v, hv, rfl⟩
    rw [hsurplus] at h2
    have h4 : B + 2 ≤ (γ - δ) * ∑ n ∈ Finset.range N, W n := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < γ - δ)] at hNbig
      linarith
    nlinarith

namespace DualCertifiedMarket

open ExactConditions.DualCertifiedMarket

variable (M : ExactConditions.DualCertifiedMarket)

/-- **Bounded account, or the buyer exploits.**  One floor per day at `c`, settled by the
next day; realized frequency at least `c + γ` along the one weighting that reads whether
the price is within `δ < γ` of the floor.  Either the account is bounded below over live
prefixes, or the buyer near the floor exploits the market. -/
theorem bounded_or_buyer_exploits (φ : ℕ → Sentence) (c δ : ℚ) (hc0 : 0 ≤ c) (hδ : 0 < δ)
    (hC : M.C = floors φ (fun _ => c)) (b : ℕ → Bool)
    (hsettle : ∀ N v, M.L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
    (hlive : ∀ N, ∃ v, M.L.Live N v) (γ : ℝ) (hδγ : (δ : ℝ) < γ)
    (hfreq : Frequency.Along (c : ℝ) γ (realized b) (thresholdWeight M.P φ c δ)) :
    (∃ B, M.AccountBounded B) ∨ M.L.Exploits (thresholdBuyer φ c δ) M.P := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  by_cases hs : Summable (thresholdWeight M.P φ c δ)
  · left
    have hev : ∀ᶠ n in Filter.atTop, thresholdWeight M.P φ c δ n < 1 :=
      hs.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one)
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
    exact ⟨_, accountBounded_of_eventually_slack M φ c hc0 hC ((δ : ℝ) / 2) (by positivity) N₀
      fun n hn => clearance_of_thresholdWeight_lt_one hδ (hN₀ n hn)⟩
  · right
    exact thresholdBuyer_exploits M.L M.P φ c δ hc0 hδ (fun n => (M.P_range n (φ n)).2) b
      hsettle hlive γ hδγ hfreq hs

/-- **The account is the criterion, under the threshold frequency.**  With the buyer near
the floor efficiently computable, the account is bounded below over live prefixes exactly
when no efficiently computable trader exploits the market. -/
theorem accountBounded_iff_unexploited (φ : ℕ → Sentence) (c δ : ℚ) (hc0 : 0 ≤ c)
    (hδ : 0 < δ) (hC : M.C = floors φ (fun _ => c)) (b : ℕ → Bool)
    (hsettle : ∀ N v, M.L.Live N v → ∀ i, i < N → (v.Holds (φ i) ↔ b i = true))
    (hlive : ∀ N, ∃ v, M.L.Live N v) (γ : ℝ) (hδγ : (δ : ℝ) < γ)
    (hfreq : Frequency.Along (c : ℝ) γ (realized b) (thresholdWeight M.P φ c δ))
    (heff : EfficientlyComputable (thresholdBuyer φ c δ)) :
    (∃ B, M.AccountBounded B) ↔
      ∀ Tr : Trader, EfficientlyComputable Tr → ¬ M.L.Exploits Tr M.P := by
  constructor
  · rintro ⟨B, hB⟩ Tr hTr
    exact M.no_efficient_trader_exploits hB Tr hTr
  · intro hno
    rcases bounded_or_buyer_exploits M φ c δ hc0 hδ hC b hsettle hlive γ hδγ hfreq with h | h
    · exact h
    · exact absurd h (hno _ heff)

end DualCertifiedMarket

/-! ### The witness for the threshold frequency: one loss -/

open ExactConditions.DualCertifiedMarket in
/-- With one lost instance the frequency along every weighting in `[0, 1]` is at least
`c + γ`, for every `c + γ < 1`. -/
lemma oneLoss_along (c γ : ℝ) (hcγ : c + γ < 1) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1) :
    Frequency.Along c γ (realized oneLoss) w := by
  intro hns
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n => (hw n).1).mp hns
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (Filter.tendsto_atTop.mp htend (1 / (1 - c - γ)))
  refine ⟨N₀, fun N hN => ?_⟩
  have hbig := hN₀ N hN
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - c - γ)] at hbig
  have hx : ∀ i, w i * realized oneLoss i = w i - if i = 0 then w 0 else 0 := by
    intro i
    by_cases hi : i = 0
    · subst hi; simp [realized, oneLoss]
    · simp [realized, oneLoss, hi]
  have hsum : ∑ i ∈ Finset.range N, (if i = 0 then w 0 else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq' (Finset.range N) 0 (fun _ => w 0)]
    split_ifs
    · exact (hw 0).2
    · exact zero_le_one
  rw [Finset.sum_congr rfl fun i _ => hx i, Finset.sum_sub_distrib]
  nlinarith

/-- **Matter 4, inhabited** with a truth sequence that is not all one.  Fresh atoms
floored at `c ∈ (0, 1)`, the first settling false, margin `δ = (1 - c)/4` and
`γ = (1 - c)/2`: the threshold frequency holds, and the account is bounded below. -/
theorem thresholdFrequency_witness (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) :
    oneLoss 0 = false ∧
      Frequency.Along (c : ℝ) ((1 - (c : ℝ)) / 2)
        (ExactConditions.DualCertifiedMarket.realized oneLoss)
        (thresholdWeight ((constantFresh c hc0.le hc1.le).market
          (ofDeductiveProcess (truthProcess oneLoss))).P (fun n => .atom n) c ((1 - c) / 4)) ∧
      ∃ B, ((constantFresh c hc0.le hc1.le).market
        (ofDeductiveProcess (truthProcess oneLoss))).AccountBounded B := by
  have hc1' : (c : ℝ) < 1 := by exact_mod_cast hc1
  exact ⟨rfl, oneLoss_along _ _ (by linarith) _ fun n => thresholdWeight_range _ _ _ _ n,
    ⟨_, (finiteLosses_witness c hc0 hc1).2.1⟩⟩

end Workspace.Normativity.Contrib.StatisticalConditions

#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Losses.headroom_le
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Losses.account_ge
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Losses.prior_ge
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Losses.compound_prior
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Losses.compound_ceiling
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.account_ge_of_losses
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_finite_losses
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.finiteLosses_witness
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Stakes.abel_bound
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Stakes.unit_bounded_staked_unbounded
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Stakes.unit_unbounded_staked_bounded
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.stake_prices_le
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.mu_mul_clearance_le
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.account_ge_slack
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_tight_sum
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_of_eventually_slack
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.Frequency.gain_bddAbove
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.TableMixture.stake_eq_tsum
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.TableMixture.table_prior
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.TableMixture.prior_eq
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.TableMixture.ceiling
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.TableMixture.prior_le
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.TableMixture.prior_ge
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.thresholdBuyer_exploits
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.bounded_or_buyer_exploits
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.DualCertifiedMarket.accountBounded_iff_unexploited
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.thresholdFrequency_witness
#print axioms Workspace.Normativity.Contrib.StatisticalConditions.bridge_frequency_iff_summable
