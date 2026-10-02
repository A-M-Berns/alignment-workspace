import Cleanroom.Lit.LitWeathersonFrames.CFrame
import Cleanroom.Trust.TtFiniteFrames.Geanakoplos
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Fin

/-!
# Frame Bentham (T9, T10): Value holds, Total Trust holds, the null-event artifact

Package `lit-weatherson-frames` (faf-cleanroom run, 2026-09-30). Weatherson's **Bentham**: a
coin is flipped until Tails; `F` the number of flips, `F = ∞` (probability `0`) if it never lands
Tails; the Experimenter at `F = x` learns `F ≤ x`. Carrier `ℕ`: world `0` is `F = ∞` with
`π 0 = 0`, world `m ≥ 1` is `F = m` with `π m = 2^{-m}`. Rows: `P 0 = π` (learns nothing),
`P n = π(· | 1 ≤ F ≤ n)` for `n ≥ 1`.

**Truncation** (the paper's proof, l. 200): `W_N = {F = 1, …, F = N+1}` as `Fin (N+1)` (world
`i ↦ F = i + 1`), prior `π_N i = 2^{-(i+1)} / (1 − 2^{-(N+1)})`, downward-ray correspondence
`i ↦ Iic i` (reflexive, transitive, nested), frame `Frame.ofCorr`. Its rows are Bentham's rows
restricted (`tr_E_eq`), so a recommended strategy restricts to a recommended strategy for the
finite sub-menu it uses (`tr_recommended`); `value_ofCorr_of_rtn` and `totalTrust_ofCorr_of_rtn`
(grade (a)) give the finite inequalities, and `N → ∞` gives Value (finite menus of integrable
options; uniformly bounded menus) and Total Trust — **Bentham is totally trusted** under the
positive-mass convention. The paper's Total Trust "failure" at `Y`, `t = 2/3` conditions on the
`π`-null event `{F = ∞}` (`Y_event_null`): the artifact of record, finding F-T10.
-/

namespace Cleanroom.Lit.LitWeathersonFrames

open Finset Filter Topology Cleanroom.Found.LitDdbFrames Cleanroom.Trust.TtFiniteFrames

noncomputable section

namespace Bentham

/-- Bentham's prior: `π 0 = 0` (`F = ∞`), `π m = 2^{-m}` for `m ≥ 1`.
Source: [[Deference and Infinite Frames]] §3 l. 196
Kind: D
Fidelity: exact (world `0` is `F = ∞`) -/
def π (m : ℕ) : ℝ := if m = 0 then 0 else (1/2) ^ m

/-- `π 0 = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π_zero : π 0 = 0 := by simp [π]

/-- `π (m + 1) = 2^{-(m+1)}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π_succ (m : ℕ) : π (m + 1) = (1/2) ^ (m + 1) := by simp [π]

/-- `π ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π_nonneg (m : ℕ) : 0 ≤ π m := by unfold π; split_ifs <;> positivity

/-- Partial geometric sums: `∑_{m < n} 2^{-(m+1)} = 1 − 2^{-n}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem geom_partial (n : ℕ) : ∑ m ∈ range n, (1/2 : ℝ) ^ (m + 1) = 1 - (1/2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- Partial geometric sums: `∑_{m < n} 4^{-(m+1)} = (1 − 4^{-n}) / 3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem geom4_partial (n : ℕ) : ∑ m ∈ range n, (1/4 : ℝ) ^ (m + 1) = (1 - (1/4) ^ n) / 3 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

/-- `π` sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π_hasSum : HasSum π 1 := by
  have h : HasSum (fun m => π (m + 1)) 1 := by
    refine (hasSum_geometric_two' 1).congr_fun fun m => ?_
    rw [π_succ, pow_succ, one_div_pow]; ring
  have h' : HasSum (fun n => π (n + 1)) (1 - ∑ i ∈ range 1, π i) := by simpa [π_zero] using h
  exact (hasSum_nat_add_iff' 1).mp h'

/-- `π` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem isDist : IsDist π := ⟨π_nonneg, π_hasSum⟩

/-- The mass `D n = π(1 ≤ F ≤ n) = 1 − 2^{-n}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def D (n : ℕ) : ℝ := 1 - (1/2) ^ n

/-- `D (n + 1) > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem D_pos (n : ℕ) : 0 < D (n + 1) := by
  unfold D
  have : (1/2 : ℝ) ^ (n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  linarith

/-- Bentham's rows: `P 0 = π`; `P n = π(· | 1 ≤ F ≤ n)` for `n ≥ 1`, in guarded product form.
Source: [[Deference and Infinite Frames]] §3 l. 196 (`P(F = x) = π(· | F ≤ x)`)
Kind: D
Fidelity: exact -/
def P (n m : ℕ) : ℝ :=
  if n = 0 then π m else if 1 ≤ m ∧ m ≤ n then (1/2) ^ m / D n else 0

/-- Row `0` is the prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P_zero : P 0 = π := by funext m; simp [P]

/-- Row `n + 1`, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P_succ (n m : ℕ) : P (n + 1) m = if 1 ≤ m ∧ m ≤ n + 1 then (1/2) ^ m / D (n + 1) else 0 := by
  simp [P]

/-- Rows are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P_nonneg (n m : ℕ) : 0 ≤ P n m := by
  rcases n with _ | n
  · rw [P_zero]; exact π_nonneg m
  · rw [P_succ]; split_ifs
    · exact div_nonneg (by positivity) (D_pos n).le
    · exact le_rfl

/-- The finite sum of row `n + 1` against `X`: `∑_{m < n+1} 2^{-(m+1)} X (m+1) / D (n+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_P_succ (n : ℕ) (X : ℕ → ℝ) :
    ∑ m ∈ range (n + 2), P (n + 1) m * X m =
      (∑ m ∈ range (n + 1), (1/2) ^ (m + 1) * X (m + 1)) / D (n + 1) := by
  rw [sum_range_succ', sum_div]
  have h0 : P (n + 1) 0 * X 0 = 0 := by simp [P_succ]
  rw [h0, add_zero]
  refine sum_congr rfl fun m hm => ?_
  have : 1 ≤ m + 1 ∧ m + 1 ≤ n + 1 := by have := mem_range.mp hm; omega
  rw [P_succ, if_pos this]; ring

/-- Row `n + 1` sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P_succ_hasSum (n : ℕ) : HasSum (P (n + 1)) 1 := by
  have h : HasSum (P (n + 1)) (∑ m ∈ range (n + 2), P (n + 1) m) :=
    hasSum_sum_of_ne_finset_zero fun m hm => by
      rw [P_succ, if_neg]; intro h; exact hm (mem_range.mpr (by omega))
  have e : ∑ m ∈ range (n + 2), P (n + 1) m = 1 := by
    have := sum_P_succ n (fun _ => 1)
    simp only [mul_one] at this
    rw [this, geom_partial]
    exact div_self (D_pos n).ne'
  rwa [e] at h

/-- **Frame Bentham.**
Source: [[Deference and Infinite Frames]] §3 l. 196
Kind: D
Fidelity: exact -/
def frame : CFrame ℕ where
  P := P
  P_nonneg := P_nonneg
  P_hasSum := fun n => by
    rcases n with _ | n
    · rw [P_zero]; exact π_hasSum
    · exact P_succ_hasSum n

/-- The Experimenter's estimate at `F = n + 1` is the finite conditional average.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_succ (n : ℕ) (X : ℕ → ℝ) :
    Eℕ (P (n + 1)) X = (∑ m ∈ range (n + 1), (1/2) ^ (m + 1) * X (m + 1)) / D (n + 1) := by
  unfold Eℕ
  rw [tsum_eq_sum (s := range (n + 2)) fun m hm => by
    rw [P_succ, if_neg, zero_mul]; intro h; exact hm (mem_range.mpr (by omega))]
  exact sum_P_succ n X

/-- The Experimenter's estimate at `F = ∞` is the prior expectation.
Source: [[Deference and Infinite Frames]] §3 l. 196 ("learns nothing")
Kind: L
Fidelity: n/a -/
theorem E_zero (X : ℕ → ℝ) : Eℕ (P 0) X = Eℕ π X := by rw [P_zero]

/-- Every row integrates a `π`-integrable variable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rowsIntegrable {X : ℕ → ℝ} (hX : IntegrableW π X) : RowsIntegrable frame X := by
  intro n
  rcases n with _ | n
  · show Summable (fun v => P 0 v * |X v|)
    rw [P_zero]; exact hX
  · show Summable (fun v => P (n + 1) v * |X v|)
    refine summable_of_ne_finset_zero (s := range (n + 2)) fun m hm => ?_
    rw [P_succ, if_neg, zero_mul]; intro h; exact hm (mem_range.mpr (by omega))

/-! ## The truncated frame on `Fin (N+1)` -/

/-- The truncated prior `π_N i = 2^{-(i+1)} / (1 − 2^{-(N+1)})` on `W_N = {F = 1, …, F = N+1}`.
Source: [[Deference and Infinite Frames]] §3 l. 200 (`W_n`, `P_n`)
Kind: D
Fidelity: exact -/
def trπ (N : ℕ) : Fin (N+1) → ℝ := fun i => (1/2) ^ (i.val + 1) / D (N + 1)

/-- The downward-ray correspondence `i ↦ Iic i` (`F ≤ x`).
Source: [[Deference and Infinite Frames]] §3 l. 196
Kind: D
Fidelity: exact -/
def trK (N : ℕ) : Corr (Fin (N+1)) := fun i => Finset.Iic i

/-- The downward-ray correspondence is reflexive, transitive and nested.
Source: [[Deference and Infinite Frames]] §3 l. 200 ("reflexive, transitive and nested")
Kind: L
Fidelity: n/a -/
theorem trK_rtn (N : ℕ) : (trK N).RTN := by
  refine ⟨fun i => by simp [trK], fun i j hj => ?_, fun i j => ?_⟩
  · intro k hk
    simp only [trK, Finset.mem_Iic] at hj hk ⊢
    exact le_trans hk hj
  · rcases le_total i j with h | h
    · right; left
      intro k hk
      simp only [trK, Finset.mem_Iic] at hk ⊢
      exact le_trans hk h
    · right; right
      intro k hk
      simp only [trK, Finset.mem_Iic] at hk ⊢
      exact le_trans hk h

/-- The truncated prior has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem trπ_pos (N : ℕ) : ∀ i, 0 < trπ N i :=
  fun i => div_pos (by positivity) (D_pos N)

/-- Sums over `Iic i` in `Fin (N+1)` are sums over `range (i+1)` in `ℕ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_Iic_fin {N : ℕ} (i : Fin (N+1)) (g : ℕ → ℝ) :
    ∑ v ∈ Finset.Iic i, g v.val = ∑ m ∈ range (i.val + 1), g m := by
  have h1 : Finset.Iic i = univ.filter (fun v => v ≤ i) := by ext v; simp
  rw [h1, sum_filter]
  have h2 : (fun v : Fin (N+1) => if v ≤ i then g v.val else 0) =
      fun v => (fun m => if m ≤ i.val then g m else 0) v.val := by
    funext v; rfl
  rw [h2, Fin.sum_univ_eq_sum_range (fun m => if m ≤ i.val then g m else 0) (N+1), ← sum_filter]
  congr 1
  ext m; simp [mem_range]; omega

/-- The truncated prior is a probability vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem trπ_mem (N : ℕ) : trπ N ∈ stdSimplex ℝ (Fin (N+1)) := by
  refine ⟨fun i => (trπ_pos N i).le, ?_⟩
  unfold trπ
  rw [Fin.sum_univ_eq_sum_range (fun m => (1/2 : ℝ) ^ (m + 1) / D (N + 1)) (N+1), ← sum_div,
    geom_partial]
  exact div_self (D_pos N).ne'

/-- **The truncated frame** `⟨W_N, P_N⟩`: the dependency's conditioning frame of `π_N` on the
downward rays.
Source: [[Deference and Infinite Frames]] §3 l. 200
Kind: D
Fidelity: exact -/
def trFrame (N : ℕ) : Frame (Fin (N+1)) :=
  Frame.ofCorr (trπ N) (fun i => (trπ_pos N i).le) (trK N)
    (Corr.mass_pos_of_reflexive (trπ_pos N) (trK_rtn N).1)

/-- Restriction of a variable to `W_N` (world `i ↦ F = i + 1`).
Source: [[Deference and Infinite Frames]] §3 l. 200 (`X_n`, `O_n`, `S_n`)
Kind: D
Fidelity: exact -/
def restrict (X : ℕ → ℝ) (N : ℕ) : Fin (N+1) → ℝ := fun i => X (i.val + 1)

/-- The mass of the truncated cell `Iic i` is `D (i+1) / D (N+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tr_mass (N : ℕ) (i : Fin (N+1)) : mass (trπ N) (trK N i) = D (i.val + 1) / D (N + 1) := by
  unfold mass trK trπ
  rw [sum_Iic_fin i (fun m => (1/2 : ℝ) ^ (m + 1) / D (N + 1)), ← sum_div, geom_partial]
  rfl

/-- The truncated cell sum against a restricted variable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tr_sum (N : ℕ) (i : Fin (N+1)) (X : ℕ → ℝ) :
    ∑ v ∈ trK N i, trπ N v * restrict X N v =
      (∑ m ∈ range (i.val + 1), (1/2) ^ (m + 1) * X (m + 1)) / D (N + 1) := by
  unfold trK trπ restrict
  rw [sum_Iic_fin i (fun m => (1/2 : ℝ) ^ (m + 1) / D (N + 1) * X (m + 1)), sum_div]
  exact sum_congr rfl fun m _ => by ring

/-- **The truncated frame's rows are Bentham's rows restricted**:
`E_{P_N, i}(X|_{W_N}) = E_{P (i+1)}(X)` — the sentence "if `S` is recommended on `⟨W, P⟩` then
`S_n` is recommended on `⟨W_n, P_n⟩`" (l. 200), at the level of estimates.
Source: [[Deference and Infinite Frames]] §3 l. 200; mandate T9 (the delicate step of item 033)
Kind: L
Fidelity: n/a -/
theorem tr_E_eq (N : ℕ) (i : Fin (N+1)) (X : ℕ → ℝ) :
    E ((trFrame N).P i) (restrict X N) = Eℕ (P (i.val + 1)) X := by
  unfold trFrame
  rw [Frame.ofCorr_E_eq, tr_sum, tr_mass, E_succ, div_div_div_cancel_right₀ (D_pos N).ne']

/-- The truncated prior's expectation of a restricted variable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tr_E_prior (N : ℕ) (X : ℕ → ℝ) :
    E (trπ N) (restrict X N) = (∑ m ∈ range (N + 1), (1/2) ^ (m + 1) * X (m + 1)) / D (N + 1) := by
  have h := tr_sum N (Fin.last N) X
  have hK : trK N (Fin.last N) = univ := by ext v; simp [trK, Fin.le_last]
  rw [hK] at h
  unfold E
  rw [h]
  rfl

/-- The return of a restricted strategy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tr_stratValue (N : ℕ) {ι : Type} (o : ι → ℕ → ℝ) (S : ℕ → ι) :
    stratValue (trπ N) (fun v => restrict (o (S (v.val + 1))) N) =
      (∑ m ∈ range (N + 1), (1/2) ^ (m + 1) * o (S (m + 1)) (m + 1)) / D (N + 1) := by
  unfold stratValue trπ restrict
  rw [Fin.sum_univ_eq_sum_range (fun m => (1/2 : ℝ) ^ (m + 1) / D (N + 1) * o (S (m + 1)) (m + 1))
    (N+1), sum_div]
  exact sum_congr rfl fun m _ => by ring

/-! ## Recommended strategies restrict (the delicate step of item 033) -/

/-- The restricted strategy `S_N : v ↦ o (S (v+1))|_{W_N}`.
Source: [[Deference and Infinite Frames]] §3 l. 200 (`S_n`)
Kind: D
Fidelity: exact -/
def trStrat {ι : Type} (o : ι → ℕ → ℝ) (S : ℕ → ι) (N : ℕ) : Fin (N+1) → (Fin (N+1) → ℝ) :=
  fun v => restrict (o (S (v.val + 1))) N

/-- The finite sub-menu used by the restricted strategy, plus the option under comparison
(`O_n` of l. 200, cut down to what `S_n` uses).
Source: [[Deference and Infinite Frames]] §3 l. 200 (`O_n`)
Kind: D
Fidelity: variant: the sub-menu the strategy uses, not the whole restricted menu (which may be
infinite); this is what makes the paper's step work for infinite menus too -/
def trMenu {ι : Type} (o : ι → ℕ → ℝ) (S : ℕ → ι) (N : ℕ) (j : ι) :
    DecisionProblem (Fin (N+1)) :=
  (univ.image (fun v : Fin (N+1) => restrict (o (S (v.val + 1))) N)) ∪ {restrict (o j) N}

/-- **"If `S` is recommended on `⟨W, P⟩` then `S_n` is recommended on `⟨W_n, P_n⟩`"** (l. 200),
for the finite sub-menu. Cell constraint through `Frame.ofCorr_P_inj` (distinct rows),
optimality through `tr_E_eq`.
Source: [[Deference and Infinite Frames]] §3 l. 200; inventory 033 step (i)
Kind: L
Fidelity: n/a -/
theorem tr_recommended {ι : Type} {o : ι → ℕ → ℝ} {S : ℕ → ι} (hS : RecommendedC frame o S)
    (N : ℕ) (j : ι) : (trFrame N).Recommended (trMenu o S N j) (trStrat o S N) := by
  refine ⟨⟨fun v => mem_union_left _ (mem_image_of_mem _ (mem_univ v)), fun v v' h => ?_⟩,
    fun v ô hô => ?_⟩
  · have hK := (Frame.ofCorr_P_inj (trπ N) (trπ_pos N) (trK N)
      (Corr.mass_pos_of_reflexive (trπ_pos N) (trK_rtn N).1) v v').mp h
    have h1 : v ∈ trK N v' := by rw [← hK]; simp [trK]
    have h2 : v' ∈ trK N v := by rw [hK]; simp [trK]
    simp only [trK, Finset.mem_Iic] at h1 h2
    rw [le_antisymm h1 h2]
  · obtain ⟨k, rfl⟩ : ∃ k, ô = restrict (o k) N := by
      rcases mem_union.mp hô with h | h
      · obtain ⟨v', -, rfl⟩ := mem_image.mp h
        exact ⟨S (v'.val + 1), rfl⟩
      · exact ⟨j, mem_singleton.mp h⟩
    show E _ (restrict (o k) N) ≤ E _ (restrict (o (S (v.val + 1))) N)
    rw [tr_E_eq, tr_E_eq]
    exact hS.2 (v.val + 1) k

/-- **The finite Value inequality on `W_N`** (from `value_ofCorr_of_rtn`, grade (a)), with the
common denominator `D (N+1)` cleared.
Source: [[Deference and Infinite Frames]] §3 l. 200 ("by the result of Geanakoplos");
`tt-finite-frames` `value_ofCorr_of_rtn`
Kind: C
Fidelity: n/a -/
theorem tr_value_ineq {ι : Type} {o : ι → ℕ → ℝ} {S : ℕ → ι} (hS : RecommendedC frame o S)
    (N : ℕ) (j : ι) :
    ∑ m ∈ range (N + 1), (1/2) ^ (m + 1) * o j (m + 1) ≤
      ∑ m ∈ range (N + 1), (1/2) ^ (m + 1) * o (S (m + 1)) (m + 1) := by
  have hne : (trMenu o S N j).Nonempty := ⟨_, mem_union_right _ (mem_singleton_self _)⟩
  have h := value_ofCorr_of_rtn (trπ_pos N) (trK_rtn N) (trMenu o S N j) hne (trStrat o S N)
    (tr_recommended hS N j) (restrict (o j) N) (mem_union_right _ (mem_singleton_self _))
  rw [tr_E_prior] at h
  rw [show stratValue (trπ N) (trStrat o S N) =
      (∑ m ∈ range (N + 1), (1/2) ^ (m + 1) * o (S (m + 1)) (m + 1)) / D (N + 1) from
    tr_stratValue N o S] at h
  exact (div_le_div_iff_of_pos_right (D_pos N)).mp h

/-- **The finite Total Trust inequality on `W_N`** (from `totalTrust_ofCorr_of_rtn`, grade (a)),
with the common denominator cleared and Bentham's estimates in the indicator.
Source: `tt-finite-frames` `totalTrust_ofCorr_of_rtn`; mandate T10 (a), direct route
Kind: C
Fidelity: n/a -/
theorem tr_tt_ineq (X : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ ∑ m ∈ range (N + 1),
      (1/2) ^ (m + 1) * (X (m + 1) - t) * (if t ≤ Eℕ (P (m + 1)) X then 1 else 0) := by
  have h : 0 ≤ ∑ v, trπ N v * (restrict X N v - t) *
      (if t ≤ E ((trFrame N).P v) (restrict X N) then 1 else 0) :=
    totalTrust_ofCorr_of_rtn (trπ_mem N) (trπ_pos N) (trK_rtn N) (restrict X N) t
  simp only [tr_E_eq] at h
  unfold trπ restrict at h
  rw [Fin.sum_univ_eq_sum_range (fun m => (1/2 : ℝ) ^ (m + 1) / D (N + 1) * (X (m + 1) - t) *
    (if t ≤ Eℕ (P (m + 1)) X then 1 else 0)) (N+1)] at h
  have e : ∑ m ∈ range (N + 1), (1/2 : ℝ) ^ (m + 1) / D (N + 1) * (X (m + 1) - t) *
      (if t ≤ Eℕ (P (m + 1)) X then 1 else 0) =
      (∑ m ∈ range (N + 1), (1/2) ^ (m + 1) * (X (m + 1) - t) *
        (if t ≤ Eℕ (P (m + 1)) X then 1 else 0)) / D (N + 1) := by
    rw [sum_div]; exact sum_congr rfl fun m _ => by ring
  rw [e] at h
  exact (div_nonneg_iff.mp h).elim (fun h => h.1) (fun h => by
    have := D_pos N; linarith [h.2])

/-! ## Limits -/

/-- A `π`-summable series is its shifted series (world `0` is null).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tsum_shift {X : ℕ → ℝ} (hX : Summable (fun m => π m * X m)) :
    ∑' m, (1/2 : ℝ) ^ (m + 1) * X (m + 1) = ∑' m, π m * X m := by
  rw [hX.tsum_eq_zero_add, π_zero, zero_mul, zero_add]
  exact tsum_congr fun m => by rw [π_succ]

/-- Partial sums over `W_N` converge to `E_π(X)` for `π`-summable `X`.
Source: [[Deference and Infinite Frames]] §3 l. 200 ("`Exp(X, π)` is the limit … of
`Exp(X_n, π)`")
Kind: L
Fidelity: n/a -/
theorem partial_tendsto {X : ℕ → ℝ} (hX : Summable (fun m => π m * X m)) :
    Tendsto (fun N => ∑ m ∈ range (N + 1), (1/2 : ℝ) ^ (m + 1) * X (m + 1)) atTop
      (𝓝 (∑' m, π m * X m)) := by
  have hs : Summable (fun m => (1/2 : ℝ) ^ (m + 1) * X (m + 1)) := by
    have := (summable_nat_add_iff 1).mpr hX
    exact this.congr fun m => by rw [π_succ]
  have h := hs.hasSum.tendsto_sum_nat
  rw [tsum_shift hX] at h
  exact h.comp (tendsto_add_atTop_nat 1)

/-- **T9 (load-bearing 5). Bentham is Valued on finite menus of integrable options.** Proof: the
paper's truncation — `value_ofCorr_of_rtn` on `⟨W_N, P_N⟩` for the finite sub-menu the strategy
uses, then `N → ∞` on both sides (world `0` is null, so the partial sums converge to the
`ℕ`-expectations). Recommendation at the null world `0` (`S 0` maximises `E_π`) is part of the
hypothesis `RecommendedC` but is not used.
Source: [[Deference and Infinite Frames]] §3 l. 200; inventory 033
Kind: C
Fidelity: exact (finite menus; integrable options)
Hyps: (a) only — the finite theorem is the dependency's `value_ofCorr_of_rtn` at grade (a),
never Geanakoplos at (b) -/
theorem valueFinInt : ValueFinInt π frame := by
  intro ι _ o ho _ S hS j
  have h1 := partial_tendsto ((ho j).summable_mul π_nonneg)
  have h2 := partial_tendsto (stratValue_summable_of_fintype isDist ho S)
  exact le_of_tendsto_of_tendsto' h1 h2 (fun N => tr_value_ineq hS N j)

/-- **T9, bounded form. Bentham is Valued on every uniformly bounded menu** (any index type):
the strategy uses at most `N+1` options on `W_N`, so the paper's step works for infinite menus.
Source: [[Deference and Infinite Frames]] §3 l. 200; inventory 033
Kind: C
Fidelity: stronger: any menu (the paper: finite `O`)
Hyps: (a) only -/
theorem valueBdd : ValueBdd π frame := by
  intro ι o ho S hS j
  have hoI : ∀ i, IntegrableW π (o i) := fun i => (ho.bdd i).integrableW isDist
  have h1 := partial_tendsto ((hoI j).summable_mul π_nonneg)
  have h2 := partial_tendsto (stratValue_summable_of_bddFam isDist ho S)
  exact le_of_tendsto_of_tendsto' h1 h2 (fun N => tr_value_ineq hS N j)

/-- **T10 (a), load-bearing 5. Bentham is totally trusted** (bounded variables), via
`value_imp_totalTrust` (T4) from `valueBdd`.
Source: [[Deference and Infinite Frames]] §3 l. 198 (the claim it refutes, under the
positive-mass convention); inventory 034
Kind: C
Fidelity: exact (product form, positive-mass convention)
Hyps: (a) only -/
theorem totalTrustC : TotalTrustC π frame := value_imp_totalTrust isDist valueBdd

/-- **T10 (a), integrable form**, via T4 from `valueFinInt`.
Source: [[Deference and Infinite Frames]] §3 l. 198; inventory 034
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem totalTrustInt : TotalTrustInt π frame := valueFinInt_imp_totalTrustInt isDist valueFinInt

/-- **T10 (a), direct route**: Total Trust on Bentham from `totalTrust_ofCorr_of_rtn` on the
truncations and the limit, not through T4 — so the row does not rest on T4 alone.
Source: mandate T10 (a) (second route)
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem totalTrustInt_direct : TotalTrustInt π frame := by
  intro X hX _ t
  show 0 ≤ ∑' m, π m * (X m - t) * (if t ≤ Eℕ (P m) X then 1 else 0)
  have hfs : Summable (fun m => π m * (X m - t) * (if t ≤ Eℕ (P m) X then 1 else 0)) :=
    totalTrust_summand_summable isDist hX t _
  have h := partial_tendsto (X := fun m => (X m - t) * (if t ≤ Eℕ (P m) X then 1 else 0))
    (hfs.congr fun m => by ring)
  refine ge_of_tendsto' (by simpa [mul_assoc] using h) fun N => ?_
  have := tr_tt_ineq X N t
  simpa [mul_assoc] using this

/-! ## T10 (b): the paper's witness `Y` and the null event -/

/-- The paper's variable: `Y (F = ∞) = 0`, `Y (F = n) = 1 − 2^{-n}`.
Source: [[Deference and Infinite Frames]] §3 l. 198
Kind: D
Fidelity: exact -/
def Y (m : ℕ) : ℝ := if m = 0 then 0 else 1 - (1/2) ^ m

/-- `Y` is bounded (by `1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Y_bdd : Bdd Y := by
  refine ⟨1, fun m => ?_⟩
  unfold Y
  split_ifs
  · simp
  · rw [abs_of_nonneg]
    · linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) m]
    · linarith [pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) (n := m)]

/-- `(1/2)^(m+1) · (1/2)^(m+1) = (1/4)^(m+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem half_sq (m : ℕ) : (1/2 : ℝ) ^ (m + 1) * (1/2) ^ (m + 1) = (1/4) ^ (m + 1) := by
  rw [← mul_pow]; norm_num

/-- **The Experimenter's estimate of `Y` at `F = n + 1`**: `2/3 − 2^{-(n+1)}/3`, hence `< 2/3`.
(Closed form: `∑_{m ≤ n+1} 2^{-m}(1 − 2^{-m}) = (1 − 2^{-(n+1)}) − (1 − 4^{-(n+1)})/3`, divided by
`1 − 2^{-(n+1)}`.)
Source: [[Deference and Infinite Frames]] §3 l. 198 ("the only world … is `F = ∞`"); mandate
T10 (b)
Kind: L
Fidelity: exact -/
theorem E_succ_Y (n : ℕ) : Eℕ (P (n + 1)) Y = 2/3 - (1/2) ^ (n + 1) / 3 := by
  rw [E_succ]
  have hnum : ∑ m ∈ range (n + 1), (1/2 : ℝ) ^ (m + 1) * Y (m + 1) =
      (1 - (1/2) ^ (n + 1)) - (1 - (1/4) ^ (n + 1)) / 3 := by
    have : ∀ m, (1/2 : ℝ) ^ (m + 1) * Y (m + 1) = (1/2) ^ (m + 1) - (1/4) ^ (m + 1) := by
      intro m; simp only [Y, Nat.succ_ne_zero, ↓reduceIte]; rw [mul_sub, mul_one, half_sq]
    simp only [this, sum_sub_distrib, geom_partial, geom4_partial]
  rw [hnum]
  unfold D
  have hx : (1/4 : ℝ) ^ (n + 1) = (1/2) ^ (n + 1) * (1/2) ^ (n + 1) := (half_sq n).symm
  rw [hx]
  have hD := D_pos n
  unfold D at hD
  field_simp
  ring

/-- At every finite world the estimate of `Y` is below `2/3`.
Source: [[Deference and Infinite Frames]] §3 l. 198
Kind: L
Fidelity: exact -/
theorem E_succ_Y_lt (n : ℕ) : Eℕ (P (n + 1)) Y < 2/3 := by
  rw [E_succ_Y]
  have : (0:ℝ) < (1/2) ^ (n + 1) := by positivity
  linarith

/-- At `F = ∞` the estimate of `Y` is `E_π(Y) = 2/3`.
Source: [[Deference and Infinite Frames]] §3 l. 198
Kind: L
Fidelity: exact -/
theorem E_zero_Y : Eℕ (P 0) Y = 2/3 := by
  rw [E_zero]
  unfold Eℕ
  have h : HasSum (fun m => π (m + 1) * Y (m + 1)) (1 - 1/3) := by
    have h2 : HasSum (fun m => (1/2 : ℝ) ^ (m + 1)) 1 :=
      (hasSum_geometric_two' 1).congr_fun fun m => by rw [pow_succ, one_div_pow]; ring
    have h4 : HasSum (fun m => (1/4 : ℝ) ^ (m + 1)) (1/3) := by
      have := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).mul_right (1/4)
      norm_num at this
      refine this.congr_fun fun m => ?_
      norm_num [pow_succ]
    refine (h2.sub h4).congr_fun fun m => ?_
    rw [π_succ]
    simp only [Y, Nat.succ_ne_zero, ↓reduceIte]
    rw [mul_sub, mul_one, half_sq]
  have h'' : HasSum (fun n => π (n + 1) * Y (n + 1)) (1 - 1/3 - ∑ i ∈ range 1, π i * Y i) := by
    simpa [π_zero] using h
  have h' : HasSum (fun m => π m * Y m) (1 - 1/3) := (hasSum_nat_add_iff' 1).mp h''
  rw [h'.tsum_eq]; norm_num

/-- **The threshold event `[E(Y) ≥ 2/3]` is exactly `{F = ∞}`.**
Source: [[Deference and Infinite Frames]] §3 l. 198 ("The only world `w` where … is `F = ∞`")
Kind: L
Fidelity: exact -/
theorem Y_event (w : ℕ) : (2/3 ≤ Eℕ (P w) Y ↔ w = 0) := by
  rcases w with _ | n
  · simp [E_zero_Y]
  · simp only [Nat.succ_ne_zero, iff_false, not_le]
    exact E_succ_Y_lt n

/-- **T10 (b). The null-event artifact.** The paper's witness `(Y, 2/3)`: the threshold event is
the single world `F = ∞`, which is `π`-null; the product-form Total Trust sum there is `0`
(`π 0 · (Y 0 − 2/3) = 0`), so under the positive-mass convention of record (DDB Lemma 7.1;
`lit-ddb-frames` `totalTrust_iff_cond`) the inequality holds — as `totalTrustC` says it must.
The paper's "`E(Y | {…}, π) = 0 < 2/3`" evaluates the `0/0` conditional expectation on the null
event pointwise as `Y(∞) = 0`; under *that* reading (variant: every world of the event, null
included, evaluated pointwise) the frame fails at the one null world, which is what
root-deference-012 paraphrases as "fails only at a null world".
Source: [[Deference and Infinite Frames]] §3 l. 198; abstract l. 29; inventory 034;
root-deference-012
Kind: N+
Fidelity: variant: the pointwise-null-world reading is compiled beside the record reading
Hyps: none -/
theorem Y_event_null :
    (∀ w, 2/3 ≤ Eℕ (P w) Y ↔ w = 0) ∧ π 0 = 0 ∧ Y 0 < 2/3 ∧ 2/3 ≤ Eℕ (P 0) Y ∧
      ∑' w, π w * (Y w - 2/3) * (if 2/3 ≤ Eℕ (P w) Y then 1 else 0) = 0 := by
  refine ⟨Y_event, π_zero, by simp [Y], by rw [E_zero_Y], ?_⟩
  have : ∀ w, π w * (Y w - 2/3) * (if 2/3 ≤ Eℕ (P w) Y then (1:ℝ) else 0) = 0 := by
    intro w
    rcases w with _ | n
    · rw [π_zero]; ring
    · rw [if_neg (not_le.mpr (E_succ_Y_lt n))]; ring
  simp only [this, tsum_zero]

/-- **The Bentham finding (T9–T10, composite).** Bentham is Valued (finite menus of integrable
options; uniformly bounded menus) *and* totally trusted (bounded and integrable variables), and
the paper's counterexample to Total Trust is the null-event artifact `Y_event_null`.
Source: [[Deference and Infinite Frames]] §3 ll. 196–200; abstract l. 29; inventory 033–034
Kind: C
Fidelity: exact (positive-mass convention)
Hyps: (a) only -/
theorem status :
    ValueFinInt π frame ∧ ValueBdd π frame ∧ TotalTrustC π frame ∧ TotalTrustInt π frame ∧
      ((∀ w, 2/3 ≤ Eℕ (P w) Y ↔ w = 0) ∧ π 0 = 0 ∧ Y 0 < 2/3 ∧ 2/3 ≤ Eℕ (P 0) Y ∧
        ∑' w, π w * (Y w - 2/3) * (if 2/3 ≤ Eℕ (P w) Y then 1 else 0) = 0) :=
  ⟨valueFinInt, valueBdd, totalTrustC, totalTrustInt_direct, Y_event_null⟩

end Bentham

end

end Cleanroom.Lit.LitWeathersonFrames
