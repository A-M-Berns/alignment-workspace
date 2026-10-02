import Cleanroom.Lit.LitWeathersonFrames.PoolingCountable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Fintype.BigOperators

/-!
# Zhang does not extend to countably many values (E1): the chain on `ℤ × Bool`

Package `lit-weatherson-frames` (faf-cleanroom run, 2026-09-30). The package's new result,
answering inventory item 024 negatively: **Weatherson's finiteness constraint 5 cannot be weakened
to countability.** A model on `W = ℤ × Bool` (`(k, b)`: chain position `k`, truth of `p` is `b`)
satisfies constraints 1–4 of Zhang's theorem (deference to both experts, strict betweenness on
every cell) with `A ≠ B` at *every* world and a countably infinite range of expert values
accumulating at `0` and `1`.

Values `v k = 2^k/3` (`k ≤ 0`), `1 − 2^{1−k}/3` (`k ≥ 0`), strictly increasing; at position `k`
even `(A, B) = (v k, v (k+1))`, at `k` odd `(A, B) = (v (k+1), v k)`, so each value `v j` is taken
exactly at positions `j − 1` and `j`. Position masses `q k = 4^{k−1}` (`k ≤ 0`), `2 · 4^{−k}`
(`k ≥ 1`), summing to `1/3 + 2/3 = 1`; posteriors `c k = (10/27) 2^k` (`k ≤ 0`),
`1 − (10/27) 2^{−k}` (`k ≥ 1`), strictly inside `(v k, v (k+1))`;
`C (k, true) = q k · c k`, `C (k, false) = q k · (1 − c k)`. Deference at the value `v j` is the
identity `q (j−1)(c (j−1) − v j) + q j (c j − v j) = 0` (`identity`), checked in three cases
(`j ≤ 0`, `j = 1`, `j ≥ 2`) from the closed forms — not by `norm_num` at finitely many `j`.
This is exactly where `zhang_finite_upper`'s proof used finiteness: no value is a maximum on
the support.
-/

namespace Cleanroom.Lit.LitWeathersonFrames

open Finset

noncomputable section

namespace Chain

/-! ## The numbers -/

/-- The values `v k = 2^k / 3` for `k ≤ 0`, `1 − (2/3) 2^{-k}` for `k > 0` (both `1/3` at `0`).
Source: mandate E1
Kind: D
Fidelity: n/a -/
def v (k : ℤ) : ℝ := if k ≤ 0 then (2:ℝ) ^ k / 3 else 1 - 2/3 / (2:ℝ) ^ k

/-- Position masses `q k = 4^{k−1}` for `k ≤ 0`, `2 · 4^{−k}` for `k > 0`.
Source: mandate E1
Kind: D
Fidelity: n/a -/
def q (k : ℤ) : ℝ := if k ≤ 0 then ((2:ℝ) ^ k) ^ 2 / 4 else 2 / ((2:ℝ) ^ k) ^ 2

/-- Posteriors `c k = (10/27) 2^k` for `k ≤ 0`, `1 − (10/27) 2^{-k}` for `k > 0`.
Source: mandate E1
Kind: D
Fidelity: n/a -/
def c (k : ℤ) : ℝ := if k ≤ 0 then 10/27 * (2:ℝ) ^ k else 1 - 10/27 / (2:ℝ) ^ k

/-- `2^k > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem two_zpow_pos (k : ℤ) : 0 < (2:ℝ) ^ k := zpow_pos (by norm_num) k

/-- `2^(k+1) = 2^k · 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem two_zpow_succ (k : ℤ) : (2:ℝ) ^ (k + 1) = 2 ^ k * 2 := zpow_add_one₀ two_ne_zero k

/-- `2^(k−1) = 2^k / 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem two_zpow_pred (k : ℤ) : (2:ℝ) ^ (k - 1) = 2 ^ k / 2 := by
  rw [zpow_sub_one₀ two_ne_zero k, div_eq_mul_inv]

/-- `2^k ≥ 1` for `k ≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem two_zpow_ge_one {k : ℤ} (hk : 0 < k) : 1 ≤ (2:ℝ) ^ k :=
  one_le_zpow₀ (by norm_num) hk.le

/-- `2^k ≤ 1` for `k ≤ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem two_zpow_le_one {k : ℤ} (hk : k ≤ 0) : (2:ℝ) ^ k ≤ 1 :=
  zpow_le_one_of_nonpos₀ (by norm_num) hk

/-- The values increase strictly along the chain.
Source: mandate E1 ("strictly increasing")
Kind: L
Fidelity: n/a -/
theorem v_lt_succ (k : ℤ) : v k < v (k + 1) := by
  have hy := two_zpow_pos k
  by_cases h1 : k + 1 ≤ 0
  · have h0 : k ≤ 0 := by omega
    simp only [v, h0, h1, if_true, two_zpow_succ]
    linarith
  · by_cases h0 : k ≤ 0
    · have hk : k = 0 := by omega
      subst hk
      simp only [v, le_refl, if_true, zpow_zero]
      norm_num
    · simp only [v, h0, h1, if_false, two_zpow_succ]
      have : 2/3 / ((2:ℝ) ^ k * 2) < 2/3 / (2:ℝ) ^ k :=
        div_lt_div_of_pos_left (by norm_num) hy (by linarith)
      linarith

/-- `v` is strictly monotone, hence injective.
Source: mandate E1
Kind: L
Fidelity: n/a -/
theorem v_strictMono : StrictMono v := strictMono_int_of_lt_succ v_lt_succ

/-- `v` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem v_injective : Function.Injective v := v_strictMono.injective

/-- The values are credences: `0 < v k < 1`.
Source: mandate E1 ("all in `(0, 1)`")
Kind: L
Fidelity: n/a -/
theorem v_mem (k : ℤ) : 0 < v k ∧ v k < 1 := by
  have hy := two_zpow_pos k
  by_cases h0 : k ≤ 0
  · simp only [v, h0, if_true]
    have := two_zpow_le_one h0
    constructor <;> linarith
  · simp only [v, h0, if_false]
    have h1 := two_zpow_ge_one (by omega : 0 < k)
    have : 2/3 / (2:ℝ) ^ k ≤ 2/3 := by
      rw [div_le_iff₀ hy]; linarith
    constructor <;> linarith [div_pos (by norm_num : (0:ℝ) < 2/3) hy]

/-- The posterior at position `k` lies strictly between `v k` and `v (k+1)`.
Source: mandate E1 (claim (2))
Kind: L
Fidelity: n/a -/
theorem c_between (k : ℤ) : v k < c k ∧ c k < v (k + 1) := by
  have hy := two_zpow_pos k
  by_cases h1 : k + 1 ≤ 0
  · have h0 : k ≤ 0 := by omega
    simp only [v, c, h0, h1, if_true, two_zpow_succ]
    constructor <;> linarith
  · by_cases h0 : k ≤ 0
    · have hk : k = 0 := by omega
      subst hk
      simp only [v, c, le_refl, if_true, zpow_zero]
      norm_num
    · simp only [v, c, h0, h1, if_false, two_zpow_succ]
      have e : 2/3 / ((2:ℝ) ^ k * 2) = 1/3 / (2:ℝ) ^ k := by field_simp
      rw [e]
      constructor
      · have : 10/27 / (2:ℝ) ^ k < 2/3 / (2:ℝ) ^ k := div_lt_div_of_pos_right (by norm_num) hy
        linarith
      · have : 1/3 / (2:ℝ) ^ k < 10/27 / (2:ℝ) ^ k := div_lt_div_of_pos_right (by norm_num) hy
        linarith

/-- Position masses are positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem q_pos (k : ℤ) : 0 < q k := by
  have hy := two_zpow_pos k
  unfold q; split_ifs <;> positivity

/-- Posteriors are credences: `0 < c k < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem c_mem (k : ℤ) : 0 < c k ∧ c k < 1 := by
  have hy := two_zpow_pos k
  by_cases h0 : k ≤ 0
  · simp only [c, h0, if_true]
    have := two_zpow_le_one h0
    constructor <;> linarith
  · simp only [c, h0, if_false]
    have h1 := two_zpow_ge_one (by omega : 0 < k)
    have : 10/27 / (2:ℝ) ^ k ≤ 10/27 := by
      rw [div_le_iff₀ hy]; linarith
    constructor <;> linarith [div_pos (by norm_num : (0:ℝ) < 10/27) hy]

/-- **The deference identity** at every value: `q (j−1)(c (j−1) − v j) + q j (c j − v j) = 0`.
Three cases from the closed forms: `j ≤ 0` (both positions on the lower branch), `j = 1`, and
`j ≥ 2` (both on the upper branch).
Source: mandate E1 (claim (3))
Kind: L
Fidelity: n/a -/
theorem identity (j : ℤ) : q (j - 1) * (c (j - 1) - v j) + q j * (c j - v j) = 0 := by
  have hy := two_zpow_pos j
  have hy' : (2:ℝ) ^ j ≠ 0 := hy.ne'
  by_cases h0 : j ≤ 0
  · have h1 : j - 1 ≤ 0 := by omega
    simp only [q, c, v, h0, h1, if_true, two_zpow_pred]
    field_simp
    ring
  · by_cases h1 : j - 1 ≤ 0
    · have hj : j = 1 := by omega
      subst hj
      simp only [q, c, v, le_refl, if_true, sub_self, zpow_zero, zpow_one]
      all_goals norm_num
    · simp only [q, c, v, h0, h1, if_false, two_zpow_pred]
      field_simp
      ring

/-! ## The model on `ℤ × Bool` -/

/-- Expert `A`: `v k` at even positions, `v (k+1)` at odd ones.
Source: mandate E1
Kind: D
Fidelity: n/a -/
def A (w : ℤ × Bool) : ℝ := if w.1 % 2 = 0 then v w.1 else v (w.1 + 1)

/-- Expert `B`: `v (k+1)` at even positions, `v k` at odd ones.
Source: mandate E1
Kind: D
Fidelity: n/a -/
def B (w : ℤ × Bool) : ℝ := if w.1 % 2 = 0 then v (w.1 + 1) else v w.1

/-- The novice's weights: `q k · c k` at `(k, true)`, `q k · (1 − c k)` at `(k, false)`.
Source: mandate E1
Kind: D
Fidelity: n/a -/
def C (w : ℤ × Bool) : ℝ := q w.1 * (if w.2 then c w.1 else 1 - c w.1)

/-- The target: the indicator of `p`, true at `(k, true)`.
Source: mandate E1
Kind: D
Fidelity: n/a -/
def Y (w : ℤ × Bool) : ℝ := if w.2 then 1 else 0

/-- `C > 0` everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem C_pos (w : ℤ × Bool) : 0 < C w := by
  unfold C
  have := c_mem w.1
  refine mul_pos (q_pos _) ?_
  split_ifs <;> linarith

/-- `C ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem C_nonneg (w : ℤ × Bool) : 0 ≤ C w := (C_pos w).le

/-- `Y` is an indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Y_indicator (w : ℤ × Bool) : Y w = 0 ∨ Y w = 1 := by
  unfold Y; split_ifs <;> simp

/-- `Y` is bounded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Y_bdd : Bdd Y := ⟨1, fun w => by unfold Y; split_ifs <;> simp⟩

/-- The experts disagree at every world.
Source: mandate E1 ("`A ≠ B` everywhere")
Kind: L
Fidelity: n/a -/
theorem A_ne_B (w : ℤ × Bool) : A w ≠ B w := by
  unfold A B
  split_ifs
  · exact (v_lt_succ _).ne
  · exact (v_lt_succ _).ne'

/-- `max (A w) (B w) = v (w.1 + 1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem max_AB (w : ℤ × Bool) : max (A w) (B w) = v (w.1 + 1) := by
  unfold A B
  split_ifs
  · exact max_eq_right (v_lt_succ _).le
  · exact max_eq_left (v_lt_succ _).le

/-- `min (A w) (B w) = v w.1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem min_AB (w : ℤ × Bool) : min (A w) (B w) = v w.1 := by
  unfold A B
  split_ifs
  · exact min_eq_left (v_lt_succ _).le
  · exact min_eq_right (v_lt_succ _).le

/-- The level set of `A` at an even value `v j` is the pair of positions `j`, `j − 1`.
Source: mandate E1 ("each value `v k` is taken … at exactly the positions `k − 1` and `k`")
Kind: L
Fidelity: n/a -/
theorem level_A {j : ℤ} (hj : j % 2 = 0) (w : ℤ × Bool) :
    A w = v j ↔ w.1 = j ∨ w.1 = j - 1 := by
  unfold A
  constructor
  · intro h
    split_ifs at h with hw
    · left; exact v_injective h
    · right; have := v_injective h; omega
  · rintro (h | h)
    · rw [if_pos (by omega), h]
    · rw [if_neg (by omega), h]; congr 1; omega

/-- The level set of `B` at an odd value `v j` is the pair of positions `j`, `j − 1`.
Source: mandate E1
Kind: L
Fidelity: n/a -/
theorem level_B {j : ℤ} (hj : j % 2 ≠ 0) (w : ℤ × Bool) :
    B w = v j ↔ w.1 = j ∨ w.1 = j - 1 := by
  unfold B
  constructor
  · intro h
    split_ifs at h with hw
    · right; have := v_injective h; omega
    · left; exact v_injective h
  · rintro (h | h)
    · rw [if_neg (by omega), h]
    · rw [if_pos (by omega), h]; congr 1; omega

/-- Every value of `A` is an even `v j`; every value of `B` is an odd `v j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem A_val (w : ℤ × Bool) : ∃ j, j % 2 = 0 ∧ A w = v j := by
  unfold A; split_ifs with h
  · exact ⟨w.1, h, rfl⟩
  · exact ⟨w.1 + 1, by omega, rfl⟩

/-- Every value of `B` is an odd `v j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem B_val (w : ℤ × Bool) : ∃ j, j % 2 ≠ 0 ∧ B w = v j := by
  unfold B; split_ifs with h
  · exact ⟨w.1 + 1, by omega, rfl⟩
  · exact ⟨w.1, h, rfl⟩

/-- The deference sum over a two-position level set, evaluated.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tsum_level (j : ℤ) (a : ℝ) (X : ℤ × Bool → ℝ)
    (hlev : ∀ w, X w = a ↔ w.1 = j ∨ w.1 = j - 1) :
    ∑' w, C w * (Y w - a) * (if X w = a then 1 else 0) =
      q (j - 1) * (c (j - 1) - a) + q j * (c j - a) := by
  rw [tsum_eq_sum (s := ({j, j - 1} : Finset ℤ) ×ˢ (univ : Finset Bool))]
  · rw [Finset.sum_product, Finset.sum_pair (by omega : j ≠ j - 1)]
    simp only [Fintype.sum_bool]
    have h1 : X (j, true) = a := (hlev _).mpr (Or.inl rfl)
    have h2 : X (j, false) = a := (hlev _).mpr (Or.inl rfl)
    have h3 : X (j - 1, true) = a := (hlev _).mpr (Or.inr rfl)
    have h4 : X (j - 1, false) = a := (hlev _).mpr (Or.inr rfl)
    simp [h1, h2, h3, h4, C, Y]
    ring
  · intro w hw
    have : ¬ (w.1 = j ∨ w.1 = j - 1) := by
      intro h
      apply hw
      simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
        and_true]
      exact h
    rw [if_neg (fun h => this ((hlev w).mp h)), mul_zero]

/-- **Constraint 1: `C` defers to `A`.**
Source: mandate E1 (claim (3)); [[Deference and Infinite Frames]] §1 l. 56
Kind: L
Fidelity: n/a -/
theorem defersA : DefersC C Y A := by
  intro a
  by_cases h : ∃ w, A w = a
  · obtain ⟨w₀, hw₀⟩ := h
    obtain ⟨j, hj, hv⟩ := A_val w₀
    rw [← hw₀, hv, tsum_level j (v j) A (level_A hj), identity]
  · push Not at h
    simp [h]

/-- **Constraint 2: `C` defers to `B`.**
Source: mandate E1 (claim (3)); [[Deference and Infinite Frames]] §1 l. 57
Kind: L
Fidelity: n/a -/
theorem defersB : DefersC C Y B := by
  intro b
  by_cases h : ∃ w, B w = b
  · obtain ⟨w₀, hw₀⟩ := h
    obtain ⟨j, hj, hv⟩ := B_val w₀
    rw [← hw₀, hv, tsum_level j (v j) B (level_B hj), identity]
  · push Not at h
    simp [h]

/-- The joint cell of a position: `A w = A (k, ·) ∧ B w = B (k, ·) ↔ w.1 = k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cell (k : ℤ) (w : ℤ × Bool) :
    (A w = A (k, true) ∧ B w = B (k, true)) ↔ w.1 = k := by
  constructor
  · rintro ⟨hA, hB⟩
    have h := max_AB w
    rw [hA, hB, max_AB] at h
    have := v_injective h
    simp only at this
    omega
  · intro h
    have hA : A w = A (w.1, true) := rfl
    have hB : B w = B (w.1, true) := rfl
    rw [hA, hB, h]; exact ⟨rfl, rfl⟩

/-- **Constraint 4 (strict, closed reading): `C` pools strictly between the experts at every
positive-mass cell**, with posterior `c k` at position `k`.
Source: mandate E1 (claim (2)); [[Deference and Infinite Frames]] §1 l. 59
Kind: L
Fidelity: n/a -/
theorem between4 : Between4C C Y A B := by
  intro a b
  by_cases h : ∃ w, A w = a ∧ B w = b
  · obtain ⟨w₀, ha, hb⟩ := h
    set k := w₀.1 with hk
    have hA0 : A w₀ = A (k, true) := rfl
    have hB0 : B w₀ = B (k, true) := rfl
    refine ⟨c k, ?_, ?_, ?_, fun _ => ?_⟩
    · rw [← ha, ← hb, hA0, hB0]
      rw [tsum_eq_sum (s := ({k} : Finset ℤ) ×ˢ (univ : Finset Bool))]
      · rw [Finset.sum_product, Finset.sum_singleton]
        simp only [Fintype.sum_bool]
        have h2 : A (k, false) = A (k, true) := rfl
        have h2' : B (k, false) = B (k, true) := rfl
        simp [h2, h2', C, Y]
        ring
      · intro w hw
        have : w.1 ≠ k := by
          intro h; apply hw
          simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true]
          exact h
        rw [if_neg (fun h => this ((cell k w).mp h)), mul_zero]
    · rw [← ha, ← hb, min_AB]; exact (c_between k).1.le
    · rw [← ha, ← hb, max_AB]; exact (c_between k).2.le
    · rw [← ha, ← hb, min_AB, max_AB]; exact c_between k
  · push Not at h
    refine ⟨(a + b) / 2, ?_, ?_, ?_, fun hab => ?_⟩
    · have : ∀ w, ¬ (A w = a ∧ B w = b) := fun w hw => h w hw.1 hw.2
      simp [this]
    · rcases le_total a b with hab | hab
      · rw [min_eq_left hab]; linarith
      · rw [min_eq_right hab]; linarith
    · rcases le_total a b with hab | hab
      · rw [max_eq_right hab]; linarith
      · rw [max_eq_left hab]; linarith
    · rcases lt_or_gt_of_ne hab with hab | hab
      · rw [min_eq_left hab.le, max_eq_right hab.le]; constructor <;> linarith
      · rw [min_eq_right hab.le, max_eq_left hab.le]; constructor <;> linarith

/-- The weights sum to one along the chain: `∑_k q k = 1` (`11/12` on `ℕ`, `1/12` on the
negative half).
Source: mandate E1 (claim (1))
Kind: L
Fidelity: n/a -/
theorem q_hasSum : HasSum q 1 := by
  have e4 : ∀ n : ℕ, ((2:ℝ) ^ n) ^ 2 = 4 ^ n := fun n => by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hnat : HasSum (fun n : ℕ => q n) (11/12) := by
    have h : HasSum (fun n : ℕ => q ((n + 1 : ℕ) : ℤ)) (2/3) := by
      have := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).mul_left (1/2)
      norm_num at this
      refine this.congr_fun fun n => ?_
      have hpos : ¬ (((n + 1 : ℕ) : ℤ) ≤ 0) := by omega
      simp only [q, hpos, if_false, zpow_natCast]
      rw [e4 (n + 1), pow_succ, one_div_pow]
      field_simp
      ring
    have h' : HasSum (fun n : ℕ => q ((n + 1 : ℕ) : ℤ)) (11/12 - ∑ i ∈ range 1, q (i : ℤ)) := by
      have q0 : q 0 = 1/4 := by norm_num [q]
      have : (11/12 : ℝ) - ∑ i ∈ range 1, q (i : ℤ) = 2/3 := by simp [q0]; norm_num
      rw [this]; exact h
    exact (hasSum_nat_add_iff' 1).mp h'
  have hneg : HasSum (fun n : ℕ => q (-((n : ℤ) + 1))) (1/12) := by
    have := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).mul_left (1/16)
    norm_num at this
    refine this.congr_fun fun n => ?_
    have hle : (-((n : ℤ) + 1)) ≤ 0 := by omega
    simp only [q, hle, if_true]
    have e : (2:ℝ) ^ (-((n : ℤ) + 1)) = ((2:ℝ) ^ (n + 1))⁻¹ := by
      rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    rw [e, inv_pow, e4 (n + 1), pow_succ, one_div_pow]
    field_simp
    ring
  have := HasSum.of_nat_of_neg_add_one hnat hneg
  norm_num at this
  exact this

/-- The fibers of `C` over a position sum to `q k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem C_fiber (k : ℤ) : HasSum (fun b : Bool => C (k, b)) (q k) := by
  have := hasSum_fintype (fun b : Bool => C (k, b))
  rw [Fintype.sum_bool] at this
  have e : C (k, true) + C (k, false) = q k := by simp [C]; ring
  rwa [e] at this

/-- **`C` is a probability distribution on `ℤ × Bool`.**
Source: mandate E1 (claim (1))
Kind: L
Fidelity: n/a -/
theorem C_hasSum : HasSum C 1 := by
  have hnn : (0 : ℤ × Bool → ℝ) ≤ C := fun w => C_nonneg w
  have hs : Summable C := by
    rw [summable_prod_of_nonneg hnn]
    refine ⟨fun k => (C_fiber k).summable, ?_⟩
    have : (fun k => ∑' b, C (k, b)) = q := funext fun k => (C_fiber k).tsum_eq
    rw [this]; exact q_hasSum.summable
  have h := hs.hasSum
  rw [hs.tsum_prod' (fun k => (C_fiber k).summable)] at h
  have : (fun k => ∑' b, C (k, b)) = q := funext fun k => (C_fiber k).tsum_eq
  simp only [this, q_hasSum.tsum_eq] at h
  exact h

/-- The experts disagree on a positive-mass world (`C(A = B) = 0 < 1`).
Source: mandate E1 (claim (4))
Kind: L
Fidelity: n/a -/
theorem not_agreeAE : ¬ AgreeAEC C A B :=
  fun h => A_ne_B (0, true) (h (0, true) (C_pos _))

/-- **Constraint 5 fails**: no finite set of values covers the support (the even values
`v (2n)`, `n : ℕ`, are infinitely many, all attained by `A` at positive-mass worlds).
Source: mandate E1 (claim (5))
Kind: L
Fidelity: n/a -/
theorem not_finiteRange : ¬ ∃ S : Finset ℝ, FiniteRangeOn C A B S := by
  rintro ⟨S, hS⟩
  have hsub : Set.range (fun n : ℕ => v (2 * (n : ℤ))) ⊆ (S : Set ℝ) := by
    rintro _ ⟨n, rfl⟩
    have := (hS (2 * (n : ℤ), true) (C_pos _)).1
    have hA : A (2 * (n : ℤ), true) = v (2 * (n : ℤ)) := by
      simp only [A]; rw [if_pos (by omega)]
    rwa [hA] at this
  have hinj : Function.Injective (fun n : ℕ => v (2 * (n : ℤ))) := by
    intro a b h
    have := v_injective h
    omega
  exact Set.infinite_range_of_injective hinj (S.finite_toSet.subset hsub)

/-- The range of the experts is countable.
Source: mandate E1
Kind: L
Fidelity: n/a -/
theorem range_countable : Set.Countable (Set.range A ∪ Set.range B) :=
  (Set.countable_range A).union (Set.countable_range B)

/-- **E1 (the package's new result). Zhang's theorem does not extend to countably many expert
values**: on `ℤ × Bool` there is a probability `C` (full support), an event `Y = 𝟙_p`, and experts
`A`, `B` with `C` deferring to both, strict closed-reading betweenness on every cell, `A ≠ B` at
every world (so `C(A = B) = 0 < 1`), a countably infinite range, and **no** finite set of values
covering the support — every hypothesis of `zhang_countable_finiteRange` except constraint 5,
and its conclusion false. Weatherson's finiteness constraint 5 cannot be weakened to
countability; inventory item 024 is answered negatively.
Source: [[Deference and Infinite Frames]] §1 last paragraph, §4 (the open question); inventory
024; mandate E1
Kind: N+
Fidelity: n/a (a counterexample)
Hyps: none -/
theorem zhang_countable_fails :
    (∀ w, 0 < C w) ∧ HasSum C 1 ∧ (∀ w, Y w = 0 ∨ Y w = 1) ∧ DefersC C Y A ∧ DefersC C Y B ∧
      Between4C C Y A B ∧ (∀ w, A w ≠ B w) ∧ ¬ AgreeAEC C A B ∧
      Set.Countable (Set.range A ∪ Set.range B) ∧ ¬ ∃ S : Finset ℝ, FiniteRangeOn C A B S :=
  ⟨C_pos, C_hasSum, Y_indicator, defersA, defersB, between4, A_ne_B, not_agreeAE,
    range_countable, not_finiteRange⟩

end Chain

end

end Cleanroom.Lit.LitWeathersonFrames
