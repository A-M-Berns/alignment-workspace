import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Constructions

/-!
# Gap 2: a continuous, order-faithful encoding of "assessed by eval"

The reaudit's Gap 2 ([[oracle-side-gaps-reaudit]] Q2): the reset predicate reads infinitely many oracle
coordinates and the natural threshold reading is discontinuous, but the map
`G(q) := ∑_k 2^{-(k+1)} q_k` on `[0,1]`-valued profiles `q : ℕ → [0,1]` (product topology) is continuous, and on
threshold profiles (`q_k = 1` if `p_k < x`, `0` if `p_k > x`, free at `p_k = x`, for an enumeration `p` of the dyadics)
it is order-faithful: `x < y ⟹ G(q_x) < G(q_y)` whenever some `p_k` lies strictly between `x` and `y`. So Gap 2
collapses into Gap 1 (prose in the report). Model-free real analysis.

Source: [[oracle-side-gaps-reaudit]] Q2; [[uea-inventory]] 008.
-/

namespace Cleanroom.Uea.UeaColeShadow.Encoding

/-- Profiles: one coordinate in `[0,1]` per dyadic index. -/
abbrev Profile := ℕ → Set.Icc (0:ℝ) 1

/-- `G(q) := ∑_k 2^{-(k+1)} q_k`.
Source: [[oracle-side-gaps-reaudit]] Q2 (`G_x(q) = ∑_k 2^{-k} q(M_x, 1, p_k)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def G (q : Profile) : ℝ := ∑' k, (1 / 2 : ℝ) ^ (k + 1) * (q k : ℝ)

theorem term_nonneg (q : Profile) (k : ℕ) : 0 ≤ (1 / 2 : ℝ) ^ (k + 1) * (q k : ℝ) :=
  mul_nonneg (by positivity) (q k).2.1

theorem term_le (q : Profile) (k : ℕ) : (1 / 2 : ℝ) ^ (k + 1) * (q k : ℝ) ≤ (1 / 2 : ℝ) ^ k := by
  have h1 : (q k : ℝ) ≤ 1 := (q k).2.2
  have h2 : (0:ℝ) ≤ (1 / 2) ^ (k + 1) := by positivity
  calc (1 / 2 : ℝ) ^ (k + 1) * (q k : ℝ) ≤ (1 / 2 : ℝ) ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = (1 / 2 : ℝ) ^ (k + 1) := mul_one _
    _ ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)

theorem summable_term (q : Profile) : Summable (fun k => (1 / 2 : ℝ) ^ (k + 1) * (q k : ℝ)) :=
  Summable.of_nonneg_of_le (term_nonneg q) (term_le q) summable_geometric_two

/-- **`G` is continuous** in the product topology (uniform geometric domination).
Source: [[oracle-side-gaps-reaudit]] Q2
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem continuous_G : Continuous G := by
  refine continuous_tsum (fun k => ?_) summable_geometric_two (fun k q => ?_)
  · exact continuous_const.mul (continuous_subtype_val.comp (continuous_apply k))
  · rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg q k)]
    exact term_le q k

/-- A threshold profile at `x` for the enumeration `p`: `q_k = 1` below `x`, `0` above, free at `p_k = x`.
Source: [[oracle-side-gaps-reaudit]] Q2 (reading T)
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsThreshold (p : ℕ → ℝ) (x : ℝ) (q : Profile) : Prop :=
  ∀ k, (p k < x → (q k : ℝ) = 1) ∧ (x < p k → (q k : ℝ) = 0)

/-- **`G` is order-faithful on threshold profiles**: if `x < y` and some `p_k` lies strictly between them (as for an
enumeration of the dyadics), then `G(q_x) < G(q_y)`.
Source: [[oracle-side-gaps-reaudit]] Q2
Kind: P
Fidelity: exact (the density of the enumeration between `x` and `y` is the hypothesis `hdense`)
Hyps: (a) -/
theorem G_lt_G {p : ℕ → ℝ} {x y : ℝ} (hxy : x < y) (hdense : ∃ k, x < p k ∧ p k < y) {q q' : Profile}
    (hq : IsThreshold p x q) (hq' : IsThreshold p y q') : G q < G q' := by
  obtain ⟨k₀, hk₀x, hk₀y⟩ := hdense
  have hle : ∀ k, (1 / 2 : ℝ) ^ (k + 1) * (q k : ℝ) ≤ (1 / 2 : ℝ) ^ (k + 1) * (q' k : ℝ) := by
    intro k
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rcases lt_trichotomy (p k) x with h | h | h
    · rw [(hq k).1 h, (hq' k).1 (lt_trans h hxy)]
    · rw [(hq' k).1 (h ▸ hxy)]; exact (q k).2.2
    · rw [(hq k).2 h]; exact (q' k).2.1
  have hlt : (1 / 2 : ℝ) ^ (k₀ + 1) * (q k₀ : ℝ) < (1 / 2 : ℝ) ^ (k₀ + 1) * (q' k₀ : ℝ) := by
    rw [(hq k₀).2 hk₀x, (hq' k₀).1 hk₀y, mul_zero, mul_one]
    positivity
  exact Summable.tsum_lt_tsum_of_nonneg (term_nonneg q) hle hlt (summable_term q')

end Cleanroom.Uea.UeaColeShadow.Encoding
