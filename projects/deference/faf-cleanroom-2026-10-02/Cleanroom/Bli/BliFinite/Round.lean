import Cleanroom.Bli.BliFinite.Index
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Ring

/-!
# `bli-finite` · Round: coordinatewise rounding and its error (T2)

Appendix B's discretization `D_n` rounds a price list to one of finitely many lists
(bli-paper-033). The **coordinatewise** reading is formalized here: each price is clamped to
`[0,1]` and rounded to the nearest grid value, **ties down** (`⌈x·d − 1/2⌉ / d`). This rounding
does *not* preserve propositional coherence (`roundTo_not_coherent`, in `RoundCoherence.lean`);
the surviving reading of "`D_n` … maintaining propositional consistency" is world rounding
(T4, `WorldRound.lean`).

Sources: bli-paper-033, bli-slides-008; [[bli-program]] §2.2.
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction

/-- Clamp a rational to `[0,1]`: `max 0 (min 1 x)`. Every rounding below clamps first, so a junk
price (outside the cube) is rounded to a grid value in a stated way.
Source: mandate design decision 2
Kind: D
Fidelity: n/a -/
def clamp01 (x : ℚ) : ℚ := max 0 (min 1 x)

/-- `clamp01` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clamp01_nonneg (x : ℚ) : 0 ≤ clamp01 x := le_max_left _ _

/-- `clamp01` is at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clamp01_le_one (x : ℚ) : clamp01 x ≤ 1 := by
  unfold clamp01
  exact max_le zero_le_one (min_le_left _ _)

/-- `clamp01` fixes `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clamp01_eq_self {x : ℚ} (hx : 0 ≤ x ∧ x ≤ 1) : clamp01 x = x := by
  unfold clamp01
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Scalar rounding to the grid `gridVals d`: nearest value, **ties down**.
Source: bli-paper-033 (`D_n`, coordinatewise reading)
Kind: D
Fidelity: exact (one fixed tie rule; the paper fixes none) -/
def roundVal (d : ℕ) (x : ℚ) : ℚ := ((⌈clamp01 x * d - 1 / 2⌉ : ℤ) : ℚ) / d

/-- **Coordinatewise rounding** of a table: `roundVal` in every coordinate.
Source: bli-paper-033 (`D_n`, coordinatewise reading); bli-slides-008
Kind: D
Fidelity: exact (coordinatewise reading; ties down) -/
def roundTo {𝒮 : SmallIndex} {m : ℕ} (d : ℕ) (t : Table 𝒮 m) : Table 𝒮 m :=
  fun φ => roundVal d (t φ)

/-! ## Scalar lemmas -/

/-- The rounded value is a grid value, for every `d` (at `d = 0` both sides are `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundVal_mem_gridVals (d : ℕ) (x : ℚ) : roundVal d x ∈ gridVals d := by
  unfold roundVal
  have h0 := clamp01_nonneg x
  have h1 := clamp01_le_one x
  set y := clamp01 x with hy
  have hdq : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
  have hc0 : (0 : ℤ) ≤ ⌈y * d - 1 / 2⌉ := by
    have : (-1 : ℤ) < ⌈y * d - 1 / 2⌉ := by
      rw [Int.lt_ceil]; push_cast; nlinarith
    omega
  have hcd : ⌈y * d - 1 / 2⌉ ≤ (d : ℤ) := by
    rw [Int.ceil_le]; push_cast; nlinarith
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hc0
  rw [hk] at hcd
  refine mem_gridVals_iff.mpr ⟨k, by exact_mod_cast hcd, ?_⟩
  rw [hk, Int.cast_natCast]

/-- Rounding error of a value in `[0,1]`: at most half a grid step.
Source: bli-paper-033 (`‖D_n(Q) − Q‖_∞ ≤ ε_n`, bli-slides-008)
Kind: P
Fidelity: exact
Hyps: (a) `0 < d`; (a) `x ∈ [0,1]` -/
lemma roundVal_err {d : ℕ} (hd : 0 < d) {x : ℚ} (hx : 0 ≤ x ∧ x ≤ 1) :
    |roundVal d x - x| ≤ 1 / (2 * d) := by
  unfold roundVal
  rw [clamp01_eq_self hx]
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  set c : ℤ := ⌈x * d - 1 / 2⌉ with hc
  have h1 : x * d - 1 / 2 ≤ c := Int.le_ceil _
  have h2 : (c : ℚ) < x * d - 1 / 2 + 1 := Int.ceil_lt_add_one _
  have e : (c : ℚ) / d - x = (c - x * d) / d := by field_simp
  have e2 : (1 : ℚ) / (2 * d) * d = 1 / 2 := by field_simp
  rw [e, abs_div, abs_of_pos hdq, div_le_iff₀ hdq, e2]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A grid value rounds to itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundVal_eq_self {d : ℕ} (hd : 0 < d) {x : ℚ} (hx : x ∈ gridVals d) : roundVal d x = x := by
  obtain ⟨k, hk, rfl⟩ := mem_gridVals_iff.mp hx
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hk' : (k : ℚ) ≤ d := by exact_mod_cast hk
  unfold roundVal
  rw [clamp01_eq_self ⟨by positivity, by rw [div_le_one hdq]; exact hk'⟩]
  have : ⌈(k : ℚ) / d * d - 1 / 2⌉ = (k : ℤ) := by
    rw [Int.ceil_eq_iff, div_mul_cancel₀ _ hdq.ne']
    push_cast
    constructor <;> linarith
  rw [this, Int.cast_natCast]

/-- `0` is a fixed point of rounding (for every `d`).
Source: none: infrastructure (the reason exact 0 prices survive rounding, bli-superbelief E5/E6)
Kind: L
Fidelity: n/a -/
lemma roundVal_zero (d : ℕ) : roundVal d 0 = 0 := by
  unfold roundVal
  rw [clamp01_eq_self ⟨le_rfl, zero_le_one⟩, zero_mul, zero_sub]
  have : ⌈(-(1 / 2) : ℚ)⌉ = 0 := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> norm_num
  rw [this]; simp

/-- `1` is a fixed point of rounding when `0 < d`.
Source: none: infrastructure (the reason exact 1 prices survive rounding, bli-superbelief E5/E6)
Kind: L
Fidelity: n/a -/
lemma roundVal_one {d : ℕ} (hd : 0 < d) : roundVal d 1 = 1 :=
  roundVal_eq_self hd (one_mem_gridVals hd)

/-! ## Table lemmas -/

variable {𝒮 : SmallIndex} {m : ℕ}

/-- A rounded table is a grid table (unconditionally, thanks to the clamp).
Source: bli-paper-033
Kind: L
Fidelity: exact -/
lemma roundTo_mem_grid {d : ℕ → ℕ} (t : Table 𝒮 m) : roundTo (d m) t ∈ grid 𝒮 d m :=
  mem_grid_iff.mpr fun φ => roundVal_mem_gridVals _ _

/-- Rounding error of a table in the unit cube: at most `1 / (2 d)` in every coordinate.
Source: bli-paper-033; bli-slides-008
Kind: P
Fidelity: exact
Hyps: (a) `0 < d`; (a) `t.InUnit` -/
lemma roundTo_err {d : ℕ} (hd : 0 < d) {t : Table 𝒮 m} (ht : t.InUnit) (φ : ↥(𝒮.S m)) :
    |roundTo d t φ - t φ| ≤ 1 / (2 * d) :=
  roundVal_err hd (ht φ)

/-- A grid table rounds to itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundTo_eq_self_of_mem_grid {d : ℕ → ℕ} (hd : 0 < d m) {t : Table 𝒮 m}
    (ht : t ∈ grid 𝒮 d m) : roundTo (d m) t = t :=
  funext fun φ => roundVal_eq_self hd (mem_grid_iff.mp ht φ)

/-- A coordinate priced exactly `0` stays `0` under rounding.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundTo_zero {d : ℕ} {t : Table 𝒮 m} {φ : ↥(𝒮.S m)} (h : t φ = 0) : roundTo d t φ = 0 := by
  unfold roundTo; rw [h]; exact roundVal_zero d

/-- A coordinate priced exactly `1` stays `1` under rounding (`0 < d`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundTo_one {d : ℕ} (hd : 0 < d) {t : Table 𝒮 m} {φ : ↥(𝒮.S m)} (h : t φ = 1) :
    roundTo d t φ = 1 := by
  unfold roundTo; rw [h]; exact roundVal_one hd

end Cleanroom.Bli.BliFinite
