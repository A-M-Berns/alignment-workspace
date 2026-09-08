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

**The auction** (`Auction`): `n` hypotheses, round weights `w k > 0` (block durations in
the round's first model), allowance `A k i ≥ 0`, a winner `star k`, the charged per-unit
bid `b k` (the learner's estimate `α^e_k`) and the realized block average `G k ≥ 0`.  The
wealth recursion `W (k+1) = W k + A k + payoff` is shared by two timings:
* **source-paper timing** (`Feasible`): the bid at `k` is bounded by the carried wealth
  `W k`, and `A k` is credited after the round — `wealth_nonneg`, `overestimation_le_allowance`,
  `record_lt_of_rejected`: at a rejection `ℓ_K i < w_K · e_K i − A_K i` with `A_K i` the
  allowance *before* round `K`;
* **weighted-construction timing** (`FeasibleOpening`): the bid at `k` is bounded by the
  opening capital `B k = W k + A k` — `wealth_nonneg_opening`,
  `overestimation_le_allowance_opening`, `B_eq`, `record_lt_of_rejected_opening` (record
  over tests before `K`: `< w_K · e_K i − A_i(K)` with `A_i(K)` the allowance *through*
  round `K`), `record_succ_lt_of_rejected_opening` (the criterion's inclusive record:
  `< 2 w_K − A_i(K)`), and the attention bound `chargedRecord_ge_neg_allowance`.
  Coverage's divergence clause follows from `A_i(K) − 2 w_K → ∞`, the round's
  capital-adequacy condition under opening timing.
* `wealth_sum_eq` — `Σ_i W_K i = 𝒜_K + Σ_{k<K} w_k (G_k − b_k)`, timing-independent.
* `wealth_eq` — per hypothesis, wealth is its allowance plus its charged record.
* `record_le` — the record with promises `e` (paid ≤ promised) is at most wealth minus
  allowance.
* `wealth_ge_of_no_win` — a hypothesis that stops winning keeps all later allowance, so
  under the same condition it eventually bids its full promise: coverage's test-set
  clause.
* `record_ge_neg_overpromise` — the record is at least minus the tested overpromise, so
  finite total tested overpromise gives a record bounded below (the hypothesis of
  continuation-promise competence).

**Gate transparency** (`trajGated_eq_traj_of_admitted`): if every proposal of a
controller is admitted along its gated trajectory, the gated and ungated trajectories
coincide for the length of the lease.

**Regret decomposition** (`regret_decomposition`, `regret_le_of_bounds`): with the
learner's observed return, the external actual-history comparator return and the external
own-history comparator return typed separately, the own-trajectory value gap splits
exactly into history shift, promise slack and learning error, and bounds on the three
bound the gap.

**Uniform allowance constructor** (`sum_support_jump_le`): support-weighted jumps of the
running maximum sum to at most `2 B (√M_K − √M_0)` when the support is bounded by
`B / √M`; with `B = √S_K` this is the modulus-free subsidy bound of the pressure pass (the
fourth pass doubles the jump coefficient, so the bound is `4√(S_K M_K) + …`).

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
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

/-- Wealth carried into round `k`.  The recursion credits `A k` and the winner's payoff
`w k · G k − w k · b k` in the step to `k+1`; which capital the bid at `k` is bounded by is
the timing (`Feasible` vs `FeasibleOpening`). -/
def W : ℕ → Fin n → ℝ
  | 0, _ => 0
  | k + 1, i => W k i + a.A k i + (if i = a.star k then a.w k * (a.G k - a.b k) else 0)

/-- Source-paper timing: the winner can pay its bid from the wealth carried in. -/
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

/-- The record is bounded below by minus the tested overpromise:
`Σ_{wins} w (G − e) ≥ −Σ_{wins} w · max (e − G) 0`.  So finite total tested overpromise
gives a record bounded below, which is the theorem hypothesis of continuation-promise
competence. -/
theorem record_ge_neg_overpromise (e : ℕ → Fin n → ℝ) (i : Fin n) (K : ℕ) :
    a.record e i K ≥ -(∑ k ∈ range K, if i = a.star k then a.w k * max (e k i - a.G k) 0 else 0) := by
  unfold record
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h : i = a.star k
  · simp only [h, if_true]
    have hw := a.w_pos k
    have : e k (a.star k) - a.G k ≤ max (e k (a.star k) - a.G k) 0 := le_max_left _ _
    nlinarith
  · simp [h]

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


/-! ### 2a. Opening-subsidy timing — the weighted construction

The recursion `W (k+1) = W k + A k + payoff` is the same; what changes is the capital the
bid is bounded by.  Under the source paper's timing (`Feasible`) the bid at round `k` is
bounded by the wealth carried in, `W k`.  Under the weighted construction's timing
(`FeasibleOpening`) the round's allowance is credited at the *opening* of the round, so
the bid is bounded by `W k + A k` — the current block's subsidy finances the current
block.  Every identity below is the same algebra; the difference appears exactly where
the allowance index enters the rejection bound. -/

/-- Opening capital: carried wealth plus the round's allowance. -/
def B (k : ℕ) (i : Fin n) : ℝ := a.W k i + a.A k i

/-- The weighted construction's wealth bound: the winner can pay its bid from its
opening capital. -/
def FeasibleOpening : Prop := ∀ k, a.w k * a.b k ≤ a.B k (a.star k)

theorem wealth_nonneg_opening (hf : a.FeasibleOpening) : ∀ k i, 0 ≤ a.W k i := by
  intro k
  induction k with
  | zero => intro i; simp [W]
  | succ k ih =>
    intro i
    rw [W_succ]
    by_cases h : i = a.star k
    · subst h
      have := hf k
      simp only [B] at this
      have hG := a.G_nonneg k
      have hw := a.w_pos k
      simp only [if_true]
      nlinarith [mul_nonneg hw.le hG]
    · simp only [h, if_false, add_zero]
      exact add_nonneg (ih i) (a.A_nonneg k i)

/-- Weighted cumulative overestimation is at most the allowance distributed, under
opening timing as well: the identity `wealth_sum_eq` does not depend on timing. -/
theorem overestimation_le_allowance_opening (hf : a.FeasibleOpening) (K : ℕ) :
    ∑ k ∈ range K, a.w k * (a.b k - a.G k) ≤ a.totalAllowance K := by
  have h := a.wealth_sum_eq K
  have hnn : 0 ≤ ∑ i, a.W K i :=
    Finset.sum_nonneg fun i _ => a.wealth_nonneg_opening hf K i
  have : ∑ k ∈ range K, a.w k * (a.b k - a.G k)
      = -(∑ k ∈ range K, a.w k * (a.G k - a.b k)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linarith

/-- Opening capital is allowance through the round (inclusive) plus the charged record of
the rounds before it. -/
theorem B_eq (i : Fin n) (K : ℕ) :
    a.B K i = a.allowanceOf i (K + 1) + a.chargedRecord i K := by
  simp only [B, wealth_eq, allowanceOf, Finset.sum_range_succ]
  ring

/-- Rejection bound, opening timing, record over the tests *before* `K`: if `i` outpromises
the winner at `K` and its opening-capital-bounded bid does not exceed the winning bid,
its record is below `w_K · e_K i − A_i(K)` with `A_i(K)` the allowance through round `K`
inclusive. -/
theorem record_lt_of_rejected_opening (e : ℕ → Fin n → ℝ) (hpaid : ∀ k, a.b k ≤ e k (a.star k))
    (i : Fin n) (K : ℕ) (hrej : a.b K < e K i)
    (hbid : min (e K i) (a.B K i / a.w K) ≤ a.b K) :
    a.record e i K < a.w K * e K i - a.allowanceOf i (K + 1) := by
  have hw := a.w_pos K
  have hmin : a.B K i / a.w K ≤ a.b K := by
    rcases min_le_iff.mp hbid with h | h
    · exact absurd h (not_le.mpr hrej)
    · exact h
  have hB : a.B K i ≤ a.w K * a.b K := by
    rwa [div_le_iff₀ hw, mul_comm] at hmin
  have h1 : a.record e i K ≤ a.chargedRecord i K := by
    unfold record chargedRecord
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases h : i = a.star k
    · subst h; simp only [if_true]
      have := hpaid k; have := a.w_pos k; nlinarith
    · simp [h]
  have h2 := a.B_eq i K
  have : a.w K * a.b K < a.w K * e K i := mul_lt_mul_of_pos_left hrej hw
  linarith

/-- The same, for the criterion's *inclusive* record (Definition 5: tests `t ≤ T`), which
may include a wealth-constrained win at the rejection round itself: with promises and
returns in `[0, 1]`, the record through `K` is below `2 w_K − A_i(K)`.  Coverage's
divergence clause therefore follows from `A_i(K) − 2 w_K → ∞`. -/
theorem record_succ_lt_of_rejected_opening (e : ℕ → Fin n → ℝ)
    (hpaid : ∀ k, a.b k ≤ e k (a.star k)) (he : ∀ k i, e k i ≤ 1) (he0 : ∀ k i, 0 ≤ e k i)
    (hG1 : ∀ k, a.G k ≤ 1) (i : Fin n) (K : ℕ) (hrej : a.b K < e K i)
    (hbid : min (e K i) (a.B K i / a.w K) ≤ a.b K) :
    a.record e i (K + 1) < 2 * a.w K - a.allowanceOf i (K + 1) := by
  have h := a.record_lt_of_rejected_opening e hpaid i K hrej hbid
  have hw := a.w_pos K
  have hstep : a.record e i (K + 1) ≤ a.record e i K + a.w K := by
    unfold record
    rw [Finset.sum_range_succ]
    have : (if i = a.star K then a.w K * (a.G K - e K i) else 0) ≤ a.w K := by
      by_cases hi : i = a.star K
      · simp only [hi, if_true]
        have := hG1 K; have := he0 K (a.star K); nlinarith
      · simp [hi, hw.le]
    linarith
  have : a.w K * e K i ≤ a.w K := by
    have := mul_le_mul_of_nonneg_left (he K i) hw.le
    simpa using this
  linarith

/-- The attention bound: the weighted shortfall a hypothesis inflicts on its tests
through round `K` is at most the allowance it received through round `K`, the round's
own opening subsidy included. -/
theorem chargedRecord_ge_neg_allowance (hf : a.FeasibleOpening) (i : Fin n) (K : ℕ) :
    -(a.chargedRecord i K) ≤ a.allowanceOf i K := by
  have := a.wealth_eq i K
  have := a.wealth_nonneg_opening hf K i
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

/-! ## 4. The external regret decomposition

Three separately typed return sequences: `Gobs` is the learner's *observed* block
average (the only one the criterion and the auction see); `Gext` is an external
evaluator's value of the comparator `π` started from the learner's actual block-start
history; `Gown` is the same evaluator's value of `π` on `π`'s own trajectory.  `L` is the
promise `π`'s hypothesis makes.  The last two exist only under a declared rollout
semantics and are never consumed by the learner. -/

/-- Learning error: promises against the learner's observed returns. -/
def learnErr (m L Gobs : ℕ → ℝ) (K : ℕ) : ℝ := ∑ k ∈ range K, m k * (L k - Gobs k)

/-- Promise slack: the comparator's external actual-history value against its promise. -/
def slack (m Gext L : ℕ → ℝ) (K : ℕ) : ℝ := ∑ k ∈ range K, m k * (Gext k - L k)

/-- History shift: the comparator's own-trajectory value against its actual-history value. -/
def shift (m Gown Gext : ℕ → ℝ) (K : ℕ) : ℝ := ∑ k ∈ range K, m k * (Gown k - Gext k)

/-- At a block boundary, `Σ m (Gown − Gobs) = shift + slack + learnErr`, exactly. -/
theorem regret_decomposition (m Gobs Gext Gown L : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ range K, m k * (Gown k - Gobs k)
      = shift m Gown Gext K + slack m Gext L K + learnErr m L Gobs K := by
  unfold shift slack learnErr
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The three-bridge corollary: bounds on the three terms bound the regret. -/
theorem regret_le_of_bounds (m Gobs Gext Gown L : ℕ → ℝ) (K : ℕ) (a b c : ℝ)
    (hl : learnErr m L Gobs K ≤ a) (hs : slack m Gext L K ≤ b)
    (hh : shift m Gown Gext K ≤ c) :
    ∑ k ∈ range K, m k * (Gown k - Gobs k) ≤ a + b + c := by
  rw [regret_decomposition m Gobs Gext Gown L K]
  linarith

/-! ## 4a. The uniform allowance constructor

With `M` the running maximum of the schedule (nondecreasing, nonnegative) and a support
`s k` bounded by `B / √(M (k+1))`, the support-weighted jumps sum to at most
`2 B (√(M K) − √(M 0))`.  With `B = √S_K` and `s k = ⌊√(S_k / M_k)⌋ ≤ √(S_K / M_k)` this
is the `2√(S_K M_K)` part of the allowance bound, which needs no modulus of
convergence. -/

theorem jump_div_sqrt_le (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b) / Real.sqrt a ≤ 2 * (Real.sqrt a - Real.sqrt b) := by
  rcases eq_or_lt_of_le (hb.trans hab) with ha | ha
  · have hb0 : b = 0 := by linarith
    subst ha; subst hb0; simp
  · have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have hle : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hab
    rw [div_le_iff₀ hsa]
    have ea : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    have eb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb
    nlinarith [mul_nonneg hsb (sub_nonneg.mpr hle)]

theorem sum_jump_div_sqrt_le (M : ℕ → ℝ) (hM0 : 0 ≤ M 0) (hmono : ∀ k, M k ≤ M (k + 1))
    (K : ℕ) :
    ∑ k ∈ range K, (M (k + 1) - M k) / Real.sqrt (M (k + 1))
      ≤ 2 * (Real.sqrt (M K) - Real.sqrt (M 0)) := by
  have hnn : ∀ k, 0 ≤ M k := by
    intro k
    induction k with
    | zero => exact hM0
    | succ k ih => exact ih.trans (hmono k)
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have := jump_div_sqrt_le (M (K + 1)) (M K) (hnn K) (hmono K)
    linarith

/-- Support-weighted jumps: `s k · ΔM_k ≤ B · ΔM_k / √M_{k+1}` termwise, hence the sum
is at most `2 B (√M_K − √M_0)`. -/
theorem sum_support_jump_le (M s : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hM0 : 0 ≤ M 0)
    (hmono : ∀ k, M k ≤ M (k + 1))
    (hs : ∀ k, s k * Real.sqrt (M (k + 1)) ≤ B) (K : ℕ) :
    ∑ k ∈ range K, s k * (M (k + 1) - M k) ≤ 2 * B * (Real.sqrt (M K) - Real.sqrt (M 0)) := by
  have hnn : ∀ k, 0 ≤ M k := by
    intro k
    induction k with
    | zero => exact hM0
    | succ k ih => exact ih.trans (hmono k)
  have hterm : ∀ k, s k * (M (k + 1) - M k) ≤ B * ((M (k + 1) - M k) / Real.sqrt (M (k + 1))) := by
    intro k
    rcases eq_or_lt_of_le (hnn (k + 1)) with h0 | hpos
    · have : M k = 0 := le_antisymm (by rw [h0]; exact hmono k) (hnn k)
      rw [← h0, this]; simp
    · have hsq : 0 < Real.sqrt (M (k + 1)) := Real.sqrt_pos.mpr hpos
      have hd : 0 ≤ M (k + 1) - M k := sub_nonneg.mpr (hmono k)
      rw [mul_div_assoc', le_div_iff₀ hsq]
      have := hs k
      nlinarith
  calc ∑ k ∈ range K, s k * (M (k + 1) - M k)
      ≤ ∑ k ∈ range K, B * ((M (k + 1) - M k) / Real.sqrt (M (k + 1))) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = B * ∑ k ∈ range K, (M (k + 1) - M k) / Real.sqrt (M (k + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ B * (2 * (Real.sqrt (M K) - Real.sqrt (M 0))) :=
        mul_le_mul_of_nonneg_left (sum_jump_div_sqrt_le M hM0 hmono K) hB
    _ = 2 * B * (Real.sqrt (M K) - Real.sqrt (M 0)) := by ring

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
#print axioms Workspace.Deference.ContinuationBRIA.Auction.record_ge_neg_overpromise
#print axioms Workspace.Deference.ContinuationBRIA.Auction.wealth_nonneg_opening
#print axioms Workspace.Deference.ContinuationBRIA.Auction.overestimation_le_allowance_opening
#print axioms Workspace.Deference.ContinuationBRIA.Auction.B_eq
#print axioms Workspace.Deference.ContinuationBRIA.Auction.record_lt_of_rejected_opening
#print axioms Workspace.Deference.ContinuationBRIA.Auction.record_succ_lt_of_rejected_opening
#print axioms Workspace.Deference.ContinuationBRIA.Auction.chargedRecord_ge_neg_allowance
#print axioms Workspace.Deference.ContinuationBRIA.trajGated_eq_traj_of_admitted
#print axioms Workspace.Deference.ContinuationBRIA.regret_decomposition
#print axioms Workspace.Deference.ContinuationBRIA.regret_le_of_bounds
#print axioms Workspace.Deference.ContinuationBRIA.jump_div_sqrt_le
#print axioms Workspace.Deference.ContinuationBRIA.sum_jump_div_sqrt_le
#print axioms Workspace.Deference.ContinuationBRIA.sum_support_jump_le
#print axioms Workspace.Deference.ContinuationBRIA.dominant_block_lower_bound
