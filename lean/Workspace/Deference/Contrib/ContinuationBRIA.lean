/-
# Continuation BRIA: block accounting, the weighted wealth algebra, gate transparency

Round `projects/deference/rounds/2026-09-08-continuation-bria/`.

The small exact cores of the round.  Nothing here formalizes the BRIA criterion itself
(that is the source paper's, cited); what is proved is the algebra the round's theorems
rest on.

**Block accounting.**
* `sum_range_mul_eq`, `blockAverage_eq` — equal blocks of length `m`: the average of the
  `K` block averages is the primitive-time average over `m·K` steps.
* `sum_blocks_eq`, `sum_blocks_eq_weighted` — variable blocks `m k` with boundaries
  `S k = Σ_{j<k} m j`: the primitive-time total is `Σ_k m_k · G_k`, so the primitive-time
  average is the `m`-weighted mean of the block averages, not the macro-round mean.

**The weighted auction** (`Auction`): `n` hypotheses, round weights `w k > 0` (block
durations in the round's first model), allowance `A k i ≥ 0`, a winner `star k`, the
charged per-unit bid `b k` (the learner's estimate `α^e_k`) and the realized block
average `G k ≥ 0`.  The bid is wealth-bounded: `w k · b k ≤ W k (star k)`.
* `wealth_nonneg` — every wealth stays nonnegative.
* `wealth_sum_eq` — `Σ_i W_K i = 𝒜_K + Σ_{k<K} w_k (G_k − b_k)`; hence
  `overestimation_le_allowance`: the weighted cumulative overestimation is at most the
  total allowance distributed.
* `wealth_eq` — per hypothesis, wealth is its allowance plus its charged record.
* `record_le`, `record_lt_of_rejected` — the record with promises `e` (paid ≤ promised) is
  at most wealth minus allowance; at a round where `i` outpromises the winner and its
  wealth-bounded bid does not exceed the winning bid, `ℓ_K i < w_K · e_K i − A_K i ≤
  w_K − A_K i`.  Coverage's divergence clause therefore follows from `A_i(K) − w_K → ∞`
  along the rejection rounds, which is the round's capital-adequacy condition.
* `wealth_ge_of_no_win` — a hypothesis that stops winning keeps all later allowance, so
  under the same condition it eventually bids its full promise: coverage's test-set
  clause.

**Gate transparency** (`trajGated_eq_traj_of_admitted`): if every proposal of a
controller is admitted along its gated trajectory, the gated and ungated trajectories
coincide for the length of the lease.

**Regret decomposition** (`regret_decomposition`): the own-trajectory value gap
splits exactly into history-shift, promise slack and learning error.

**Dominance** (`dominant_block_lower_bound`): when the current block carries a fraction
`c` of all primitive time so far, one test on which the estimate exceeds the realized
value by `γ`, after the estimate has been within `ε` of the realized value, puts weighted
overestimation at least `(cγ − ε)·S − S_{k₀}` on the record.  The existence theorem's
obstruction uses `ε = 0`, `γ` the guaranteed floor.

Names are provisional (`AGENTS.md` standard 6).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

namespace Workspace.Deference.ContinuationBRIA

open Finset

/-! ## 1. Block accounting -/

theorem sum_range_mul_eq (r : ℕ → ℝ) (m K : ℕ) :
    ∑ t ∈ range (m * K), r t = ∑ k ∈ range K, ∑ j ∈ range m, r (m * k + j) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The macro-round mean of equal-block averages is the primitive-time average. -/
theorem blockAverage_eq (r : ℕ → ℝ) (m K : ℕ) :
    (∑ k ∈ range K, (∑ j ∈ range m, r (m * k + j)) / m) / K
      = (∑ t ∈ range (m * K), r t) / (m * K) := by
  rw [sum_range_mul_eq, ← Finset.sum_div, div_div]

/-- Block boundaries `S k = Σ_{j<k} m j`. -/
def boundary (m : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ range k, m j

theorem sum_blocks_eq (r : ℕ → ℝ) (m : ℕ → ℕ) (K : ℕ) :
    ∑ t ∈ range (boundary m K), r t
      = ∑ k ∈ range K, ∑ j ∈ range (m k), r (boundary m k + j) := by
  induction K with
  | zero => simp [boundary]
  | succ K ih =>
    rw [boundary, Finset.sum_range_succ, Finset.sum_range_add, ← boundary, ih,
      Finset.sum_range_succ]

/-- With `G k` the average over block `k`, the primitive-time total is `Σ m_k G_k`. -/
theorem sum_blocks_eq_weighted (r : ℕ → ℝ) (m : ℕ → ℕ) (hm : ∀ k, m k ≠ 0) (K : ℕ) :
    ∑ t ∈ range (boundary m K), r t
      = ∑ k ∈ range K, (m k : ℝ) * ((∑ j ∈ range (m k), r (boundary m k + j)) / m k) := by
  rw [sum_blocks_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (m k : ℝ) ≠ 0 := by exact_mod_cast hm k
  field_simp

/-! ## 2. The weighted auction -/

/-- The data of a weighted first-price auction over `n` hypotheses.  `w k` is the round
weight, `A k i` the allowance, `star k` the winner, `b k` the charged per-unit bid
(the learner's estimate) and `G k` the realized block average. -/
structure Auction (n : ℕ) where
  w : ℕ → ℝ
  A : ℕ → Fin n → ℝ
  star : ℕ → Fin n
  b : ℕ → ℝ
  G : ℕ → ℝ
  w_pos : ∀ k, 0 < w k
  A_nonneg : ∀ k i, 0 ≤ A k i
  G_nonneg : ∀ k, 0 ≤ G k

namespace Auction

variable {n : ℕ} (a : Auction n)

/-- Wealth entering round `k`: allowance is paid at the end of each round, the winner
receives `w k · G k` and pays `w k · b k`. -/
def W : ℕ → Fin n → ℝ
  | 0, _ => 0
  | k + 1, i => W k i + a.A k i + (if i = a.star k then a.w k * (a.G k - a.b k) else 0)

/-- The bid is wealth-bounded: the winner can pay what it bid. -/
def Feasible : Prop := ∀ k, a.w k * a.b k ≤ a.W k (a.star k)

theorem W_succ (k : ℕ) (i : Fin n) :
    a.W (k + 1) i = a.W k i + a.A k i + (if i = a.star k then a.w k * (a.G k - a.b k) else 0) :=
  rfl

theorem wealth_nonneg (hf : a.Feasible) : ∀ k i, 0 ≤ a.W k i := by
  intro k
  induction k with
  | zero => intro i; simp [W]
  | succ k ih =>
    intro i
    rw [W_succ]
    by_cases h : i = a.star k
    · subst h
      have := hf k
      have hG := a.G_nonneg k
      have hw := a.w_pos k
      have hA := a.A_nonneg k (a.star k)
      simp only [if_true]
      nlinarith [mul_nonneg hw.le hG]
    · simp only [h, if_false, add_zero]
      exact add_nonneg (ih i) (a.A_nonneg k i)

/-- Total allowance distributed in rounds `< K`. -/
def totalAllowance (K : ℕ) : ℝ := ∑ k ∈ range K, ∑ i, a.A k i

/-- The wealth identity: total wealth is total allowance plus what the winners earned
over what they paid. -/
theorem wealth_sum_eq (K : ℕ) :
    ∑ i, a.W K i = a.totalAllowance K + ∑ k ∈ range K, a.w k * (a.G k - a.b k) := by
  induction K with
  | zero => simp [W, totalAllowance]
  | succ K ih =>
    simp only [W_succ, Finset.sum_add_distrib, ih, totalAllowance, Finset.sum_range_succ,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

/-- Weighted cumulative overestimation is at most the allowance distributed. -/
theorem overestimation_le_allowance (hf : a.Feasible) (K : ℕ) :
    ∑ k ∈ range K, a.w k * (a.b k - a.G k) ≤ a.totalAllowance K := by
  have h := a.wealth_sum_eq K
  have hnn : 0 ≤ ∑ i, a.W K i :=
    Finset.sum_nonneg fun i _ => a.wealth_nonneg hf K i
  have : ∑ k ∈ range K, a.w k * (a.b k - a.G k)
      = -(∑ k ∈ range K, a.w k * (a.G k - a.b k)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linarith

/-- Cumulative allowance of one hypothesis. -/
def allowanceOf (i : Fin n) (K : ℕ) : ℝ := ∑ k ∈ range K, a.A k i

/-- The charged record of hypothesis `i`: what it earned over what it paid on its wins. -/
def chargedRecord (i : Fin n) (K : ℕ) : ℝ :=
  ∑ k ∈ range K, if i = a.star k then a.w k * (a.G k - a.b k) else 0

theorem wealth_eq (i : Fin n) (K : ℕ) :
    a.W K i = a.allowanceOf i K + a.chargedRecord i K := by
  induction K with
  | zero => simp [W, allowanceOf, chargedRecord]
  | succ K ih =>
    rw [W_succ, ih]
    simp only [allowanceOf, chargedRecord, Finset.sum_range_succ]
    ring

/-- The record against promises `e`: `Σ_{wins} w_k (G_k − e_k i)`. -/
def record (e : ℕ → Fin n → ℝ) (i : Fin n) (K : ℕ) : ℝ :=
  ∑ k ∈ range K, if i = a.star k then a.w k * (a.G k - e k i) else 0

/-- Paid at most what was promised ⇒ the record is at most wealth minus allowance. -/
theorem record_le (e : ℕ → Fin n → ℝ) (hpaid : ∀ k, a.b k ≤ e k (a.star k)) (i : Fin n)
    (K : ℕ) : a.record e i K ≤ a.W K i - a.allowanceOf i K := by
  rw [wealth_eq, add_sub_cancel_left, record, chargedRecord]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h : i = a.star k
  · subst h
    simp only [if_true]
    have := hpaid k
    have := a.w_pos k
    nlinarith
  · simp [h]

/-- At a round where `i` outpromises the winner (`b K < e K i`) while its wealth-bounded
bid does not exceed the winning bid, its record is below `w_K · e_K i − A_i(K)`. -/
theorem record_lt_of_rejected (e : ℕ → Fin n → ℝ) (hpaid : ∀ k, a.b k ≤ e k (a.star k))
    (i : Fin n) (K : ℕ) (hrej : a.b K < e K i)
    (hbid : min (e K i) (a.W K i / a.w K) ≤ a.b K) :
    a.record e i K < a.w K * e K i - a.allowanceOf i K := by
  have hw := a.w_pos K
  have hmin : a.W K i / a.w K ≤ a.b K := by
    rcases min_le_iff.mp hbid with h | h
    · exact absurd h (not_le.mpr hrej)
    · exact h
  have hW : a.W K i ≤ a.w K * a.b K := by
    rwa [div_le_iff₀ hw, mul_comm] at hmin
  have := a.record_le e hpaid i K
  have : a.w K * a.b K < a.w K * e K i := mul_lt_mul_of_pos_left hrej hw
  linarith

/-- With promises in `[0, 1]`, the bound is `w_K − A_i(K)`: coverage's divergence clause
follows once `A_i(K) − w_K → ∞` along the rejection rounds. -/
theorem record_lt_of_rejected' (e : ℕ → Fin n → ℝ) (hpaid : ∀ k, a.b k ≤ e k (a.star k))
    (he : ∀ k i, e k i ≤ 1) (i : Fin n) (K : ℕ) (hrej : a.b K < e K i)
    (hbid : min (e K i) (a.W K i / a.w K) ≤ a.b K) :
    a.record e i K < a.w K - a.allowanceOf i K := by
  have h := a.record_lt_of_rejected e hpaid i K hrej hbid
  have hw := a.w_pos K
  have : a.w K * e K i ≤ a.w K := by
    have := mul_le_mul_of_nonneg_left (he K i) hw.le
    simpa using this
  linarith

/-- A hypothesis that never wins from `K₀` on keeps every later allowance. -/
theorem wealth_ge_of_no_win (hf : a.Feasible) (i : Fin n) (K₀ : ℕ)
    (hno : ∀ k, K₀ ≤ k → a.star k ≠ i) :
    ∀ K, K₀ ≤ K → a.W K i ≥ ∑ k ∈ Ico K₀ K, a.A k i := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => simp [a.wealth_nonneg hf K₀ i]
  | succ K hK ih =>
    rw [W_succ, Finset.sum_Ico_succ_top hK]
    have : ¬ i = a.star K := fun h => hno K hK h.symm
    simp only [this, if_false, add_zero]
    linarith

end Auction

/-! ## 3. Gate transparency -/

section Gate

variable {S Act : Type*}

/-- The trajectory of a contingent controller `q` (seeing the state and the step index)
through a gate `gate : S → Act → Act` that returns the action actually executed. -/
def traj (gate : S → Act → Act) (step : S → Act → S) (q : S → ℕ → Act) (s₀ : S) : ℕ → S
  | 0 => s₀
  | j + 1 => step (traj gate step q s₀ j) (gate (traj gate step q s₀ j) (q (traj gate step q s₀ j) j))

/-- The ungated trajectory is the gate `fun _ a => a`. -/
abbrev trajPlain (step : S → Act → S) (q : S → ℕ → Act) (s₀ : S) : ℕ → S :=
  traj (fun _ a => a) step q s₀

/-- If every proposal is admitted along the gated trajectory for the lease, the gated
and ungated trajectories agree throughout the lease. -/
theorem trajGated_eq_traj_of_admitted (gate : S → Act → Act) (step : S → Act → S)
    (q : S → ℕ → Act) (s₀ : S) (m : ℕ)
    (hadm : ∀ j, j < m → gate (traj gate step q s₀ j) (q (traj gate step q s₀ j) j)
      = q (traj gate step q s₀ j) j) :
    ∀ j, j ≤ m → traj gate step q s₀ j = trajPlain step q s₀ j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hj' : j < m := by omega
    simp only [traj, trajPlain]
    rw [hadm j hj', ih (by omega)]

end Gate

/-! ## 4. The regret decomposition -/

/-- `Σ m (Gown − Gα) = Σ m (Gown − Gfrom) + Σ m (Gfrom − L) + Σ m (L − Gα)`: own-trajectory
value gap = history-shift + promise slack + learning error, exactly. -/
theorem regret_decomposition (m Gown Gfrom L Gα : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ range K, m k * (Gown k - Gα k)
      = ∑ k ∈ range K, m k * (Gown k - Gfrom k)
        + ∑ k ∈ range K, m k * (Gfrom k - L k)
        + ∑ k ∈ range K, m k * (L k - Gα k) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## 5. The dominance obstruction -/

/-- If the last block `K` carries a fraction `c` of `S = Σ_{k≤K} w_k`, the estimate has
been within `ε` of the realized value since `k₀` (and never more than `1` below it), and
block `K` is a test on which the estimate exceeds the realized value by at least `γ`, then
the weighted cumulative overestimation through `K` is at least `(cγ − ε) S − S_{k₀}`. -/
theorem dominant_block_lower_bound (w b G : ℕ → ℝ) (K k₀ : ℕ) (c γ ε : ℝ)
    (hw : ∀ k, 0 ≤ w k) (hk₀ : k₀ ≤ K)
    (hstable : ∀ k, k₀ ≤ k → k < K → b k - G k ≥ -ε)
    (hbounded : ∀ k, k < K → b k - G k ≥ -1)
    (hε : 0 ≤ ε) (hγ : 0 ≤ γ)
    (hdom : w K ≥ c * ∑ k ∈ range (K + 1), w k)
    (htest : b K - G K ≥ γ) :
    ∑ k ∈ range (K + 1), w k * (b k - G k)
      ≥ (c * γ - ε) * ∑ k ∈ range (K + 1), w k - ∑ k ∈ range k₀, w k := by
  have hsplit : ∑ k ∈ range (K + 1), w k * (b k - G k)
      = ∑ k ∈ range k₀, w k * (b k - G k) + ∑ k ∈ Ico k₀ K, w k * (b k - G k)
        + w K * (b K - G K) := by
    rw [Finset.sum_range_succ, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k₀) hk₀, ← Finset.range_eq_Ico]
  have h1 : ∑ k ∈ range k₀, w k * (b k - G k) ≥ -∑ k ∈ range k₀, w k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    have := hbounded k (by have := Finset.mem_range.mp hk; omega)
    nlinarith [hw k]
  have h2 : ∑ k ∈ Ico k₀ K, w k * (b k - G k) ≥ -ε * ∑ k ∈ Ico k₀ K, w k := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_Ico.mp hk
    have := hstable k hk'.1 hk'.2
    nlinarith [hw k]
  have h3 : w K * (b K - G K) ≥ γ * w K := by nlinarith [hw K]
  have hS : ∑ k ∈ Ico k₀ K, w k ≤ ∑ k ∈ range (K + 1), w k := by
    rw [Finset.sum_range_succ, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k₀) hk₀, ← Finset.range_eq_Ico]
    have := Finset.sum_nonneg fun k (_ : k ∈ range k₀) => hw k
    nlinarith [hw K]
  have h4 : γ * w K ≥ γ * (c * ∑ k ∈ range (K + 1), w k) :=
    mul_le_mul_of_nonneg_left hdom hγ
  have hSnn : 0 ≤ ∑ k ∈ range (K + 1), w k := Finset.sum_nonneg fun k _ => hw k
  have h5 : -ε * ∑ k ∈ Ico k₀ K, w k ≥ -ε * ∑ k ∈ range (K + 1), w k := by
    nlinarith
  rw [hsplit]
  nlinarith

end Workspace.Deference.ContinuationBRIA

#print axioms Workspace.Deference.ContinuationBRIA.sum_range_mul_eq
#print axioms Workspace.Deference.ContinuationBRIA.blockAverage_eq
#print axioms Workspace.Deference.ContinuationBRIA.sum_blocks_eq
#print axioms Workspace.Deference.ContinuationBRIA.sum_blocks_eq_weighted
#print axioms Workspace.Deference.ContinuationBRIA.Auction.wealth_nonneg
#print axioms Workspace.Deference.ContinuationBRIA.Auction.wealth_sum_eq
#print axioms Workspace.Deference.ContinuationBRIA.Auction.overestimation_le_allowance
#print axioms Workspace.Deference.ContinuationBRIA.Auction.wealth_eq
#print axioms Workspace.Deference.ContinuationBRIA.Auction.record_le
#print axioms Workspace.Deference.ContinuationBRIA.Auction.record_lt_of_rejected
#print axioms Workspace.Deference.ContinuationBRIA.Auction.record_lt_of_rejected'
#print axioms Workspace.Deference.ContinuationBRIA.Auction.wealth_ge_of_no_win
#print axioms Workspace.Deference.ContinuationBRIA.trajGated_eq_traj_of_admitted
#print axioms Workspace.Deference.ContinuationBRIA.regret_decomposition
#print axioms Workspace.Deference.ContinuationBRIA.dominant_block_lower_bound
