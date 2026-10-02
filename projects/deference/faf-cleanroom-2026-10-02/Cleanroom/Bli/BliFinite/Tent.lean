import Cleanroom.Bli.BliFinite.Kernel
import Cleanroom.Bli.BliFinite.Round
import Mathlib.Algebra.BigOperators.Intervals

/-!
# `bli-finite` · Tent: the tent kernel (T7, load-bearing; the N+ inhabitant of the package)

**This run's construction** ([[bli-program]] §2.4/§3.4; not in the corpus — not Eisenstat's,
Roman's or Soto's): the explicit, rational, division-free one-step kernel with full support on
the product face. One coordinate at price `x ∈ [0,1]` (clamped first) is the law

`tent1 d x = max(0, 1 − 2x) · δ₀ + (1 − |2x − 1|) · U_d + max(0, 2x − 1) · δ₁`,

with `U_d` the uniform law on `gridVals d` (mean `1/2` because the grid is symmetric). Its mean
is `x`; it has full support on the grid iff `0 < x < 1`, and is the point mass at `x` when
`x ∈ {0, 1}`. The kernel is the product over the day-`m` sentences, with new day-`(m+1)`
sentences entering uniformly. Headlines: `tentKernel_isProb`, `tentKernel_balanced`,
`tentLaw_pos_iff` (support = product face exactly), `tentKernel_nonDegenerate`, and the
corollary `faceProd_eq_faceGen` (the product-grid case of `bli-superbelief`'s E1, landed here
because its witness lives here).
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction Finset

/-! ## One coordinate -/

/-- The uniform law on `gridVals d` (zero off the grid).
Source: [[bli-program]] §2.4 (`V := U_d`)
Kind: D
Fidelity: exact -/
def uniform1 (d : ℕ) (v : ℚ) : ℚ := if v ∈ gridVals d then 1 / (d + 1) else 0

/-- **The one-coordinate tent law** at price `x` (clamped to `[0,1]`), as a function of the grid
value `v`.
Source: [[bli-program]] §2.4 (this run's construction)
Kind: D
Fidelity: exact -/
def tent1 (d : ℕ) (x : ℚ) (v : ℚ) : ℚ :=
  max 0 (1 - 2 * clamp01 x) * (if v = 0 then 1 else 0)
    + (1 - |2 * clamp01 x - 1|) * uniform1 d v
    + max 0 (2 * clamp01 x - 1) * (if v = 1 then 1 else 0)

/-- The uniform law is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uniform1_nonneg (d : ℕ) (v : ℚ) : 0 ≤ uniform1 d v := by
  unfold uniform1; split_ifs <;> positivity

/-- The uniform law vanishes off the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uniform1_eq_zero_of_not_mem {d : ℕ} {v : ℚ} (h : v ∉ gridVals d) : uniform1 d v = 0 := by
  unfold uniform1; rw [if_neg h]

/-- The uniform law is positive exactly on the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uniform1_pos_iff {d : ℕ} {v : ℚ} : 0 < uniform1 d v ↔ v ∈ gridVals d := by
  unfold uniform1
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => by positivity⟩
  · exact ⟨fun h' => absurd h' (lt_irrefl _), fun h' => absurd h' h⟩

/-- The uniform law sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uniform1_sum_one {d : ℕ} (hd : 0 < d) : ∑ v ∈ gridVals d, uniform1 d v = 1 := by
  rw [Finset.sum_congr rfl (fun v hv => by unfold uniform1; rw [if_pos hv]), Finset.sum_const,
    card_gridVals hd, nsmul_eq_mul]
  have : ((d : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The sum of the grid values is `(d + 1) / 2` (the grid is symmetric about `1/2`).
Source: mandate T7 (`∑_{k ≤ d} k/d = (d+1)/2`)
Kind: L
Fidelity: n/a -/
lemma sum_gridVals {d : ℕ} (hd : 0 < d) : ∑ v ∈ gridVals d, v = ((d : ℚ) + 1) / 2 := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold gridVals
  rw [Finset.sum_image (fun a _ b _ hab => by exact_mod_cast (div_left_inj' hdq).mp hab)]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  have h := Finset.sum_range_id_mul_two (d + 1)
  simp only [Nat.add_sub_cancel] at h
  have h' : ((∑ i ∈ Finset.range (d + 1), i : ℕ) : ℚ) * 2 = ((d : ℚ) + 1) * d := by
    exact_mod_cast h
  field_simp
  linarith

/-- The uniform law has mean `1/2`.
Source: [[bli-program]] §2.4 ("mean `1/2` because the grid is symmetric")
Kind: L
Fidelity: n/a -/
lemma uniform1_mean {d : ℕ} (hd : 0 < d) : ∑ v ∈ gridVals d, uniform1 d v * v = 1 / 2 := by
  rw [Finset.sum_congr rfl (fun v hv => by unfold uniform1; rw [if_pos hv]), ← Finset.mul_sum,
    sum_gridVals hd]
  have : ((d : ℚ) + 1) ≠ 0 := by positivity
  field_simp

/-- A weighted point-mass term sums against the grid to its weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_gridVals_indicator {d : ℕ} (c a : ℚ) (ha : a ∈ gridVals d) :
    ∑ v ∈ gridVals d, c * (if v = a then 1 else 0) = c := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro v _ hv; simp [hv]
  · intro h; exact absurd ha h

/-- A weighted point-mass term integrates a function against the grid to its value at the point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_gridVals_indicator_mul {d : ℕ} (c a : ℚ) (ha : a ∈ gridVals d) (f : ℚ → ℚ) :
    ∑ v ∈ gridVals d, c * ((if v = a then 1 else 0) * f v) = c * f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro v _ hv; simp [hv]
  · intro h; exact absurd ha h

/-- `|2·clamp01 x − 1| ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abs_two_mul_clamp_sub_one_le (x : ℚ) : |2 * clamp01 x - 1| ≤ 1 := by
  have h0 := clamp01_nonneg x
  have h1 := clamp01_le_one x
  rw [abs_le]; constructor <;> linarith

/-- The tent law is nonnegative.
Source: [[bli-program]] §3.4
Kind: L
Fidelity: exact -/
lemma tent1_nonneg (d : ℕ) (x v : ℚ) : 0 ≤ tent1 d x v := by
  unfold tent1
  have := abs_two_mul_clamp_sub_one_le x
  have := uniform1_nonneg d v
  have h2 : 0 ≤ 1 - |2 * clamp01 x - 1| := by linarith
  refine add_nonneg (add_nonneg (mul_nonneg (le_max_left _ _) ?_) (mul_nonneg h2 ‹_›))
    (mul_nonneg (le_max_left _ _) ?_) <;> split_ifs <;> norm_num

/-- The tent law vanishes off the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tent1_eq_zero_of_not_mem {d : ℕ} (hd : 0 < d) (x : ℚ) {v : ℚ} (hv : v ∉ gridVals d) :
    tent1 d x v = 0 := by
  have h0 : v ≠ 0 := fun h => hv (h ▸ zero_mem_gridVals d)
  have h1 : v ≠ 1 := fun h => hv (h ▸ one_mem_gridVals hd)
  unfold tent1
  rw [if_neg h0, if_neg h1, uniform1_eq_zero_of_not_mem hv]
  ring

/-- The three tent weights sum to one.
Source: [[bli-program]] §3.4
Kind: L
Fidelity: n/a -/
lemma tent_weights_sum (y : ℚ) : max 0 (1 - 2 * y) + (1 - |2 * y - 1|) + max 0 (2 * y - 1) = 1 := by
  rcases le_or_gt (2 * y) 1 with h | h
  · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [abs_of_pos (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; ring

/-- **The tent law is a probability on the grid.**
Source: [[bli-program]] §3.4
Kind: P
Fidelity: exact
Hyps: (a) `0 < d` -/
lemma tent1_sum_one {d : ℕ} (hd : 0 < d) (x : ℚ) : ∑ v ∈ gridVals d, tent1 d x v = 1 := by
  unfold tent1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sum_gridVals_indicator (d := d) _ 0 (zero_mem_gridVals d),
    sum_gridVals_indicator (d := d) _ 1 (one_mem_gridVals hd), ← Finset.mul_sum,
    uniform1_sum_one hd, mul_one]
  exact tent_weights_sum _

/-- **The tent law has mean `x`** for `x ∈ [0,1]`.
Source: [[bli-program]] §3.4 ("mean `t`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < d`; (a) `x ∈ [0,1]` -/
lemma tent1_mean {d : ℕ} (hd : 0 < d) {x : ℚ} (hx : 0 ≤ x ∧ x ≤ 1) :
    ∑ v ∈ gridVals d, tent1 d x v * v = x := by
  unfold tent1
  rw [clamp01_eq_self hx]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [sum_gridVals_indicator_mul (d := d) _ 0 (zero_mem_gridVals d),
    sum_gridVals_indicator_mul (d := d) _ 1 (one_mem_gridVals hd),
    ← Finset.mul_sum, uniform1_mean hd]
  simp only [mul_zero, zero_add, mul_one]
  rcases le_or_gt (2 * x) 1 with h | h
  · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
  · rw [abs_of_pos (by linarith), max_eq_right (by linarith)]; ring

/-- **Support of the tent law**: for `x ∈ [0,1]` and `0 < d`, `tent1 d x v > 0` iff `v` is a grid
value and `0 < x < 1`, or `x ∈ {0, 1}` and `v = x` (the point mass at the boundary).
Source: [[bli-program]] §3.4 ("full support on the grid iff `t ∈ (0,1)`; point mass at the
boundary")
Kind: P
Fidelity: exact
Hyps: (a) `0 < d`; (a) `x ∈ [0,1]` -/
lemma tent1_pos_iff {d : ℕ} (hd : 0 < d) {x : ℚ} (hx : 0 ≤ x ∧ x ≤ 1) (v : ℚ) :
    0 < tent1 d x v ↔ (v ∈ gridVals d ∧ 0 < x ∧ x < 1) ∨ (v = x ∧ (x = 0 ∨ x = 1)) := by
  have hcl := clamp01_eq_self hx
  by_cases hv : v ∈ gridVals d
  · -- on the grid: `tent1 ≥ (1 − |2x−1|)/(d+1)`, positive iff `0 < x < 1` or a point mass hits
    rcases hx.1.eq_or_lt with h0 | h0
    · -- x = 0: tent1 = [v = 0]
      subst h0
      have : tent1 d 0 v = if v = 0 then 1 else 0 := by
        unfold tent1
        rw [hcl, max_eq_right (by norm_num : (0 : ℚ) ≤ 1 - 2 * 0),
          max_eq_left (by norm_num : 2 * (0 : ℚ) - 1 ≤ 0)]
        norm_num
      rw [this]
      constructor
      · intro h; right; refine ⟨?_, Or.inl rfl⟩
        by_contra hne; rw [if_neg hne] at h; exact lt_irrefl _ h
      · rintro (⟨_, h, _⟩ | ⟨rfl, _⟩)
        · exact absurd h (lt_irrefl _)
        · simp
    rcases hx.2.eq_or_lt with h1 | h1
    · -- x = 1: tent1 = [v = 1]
      subst h1
      have : tent1 d 1 v = if v = 1 then 1 else 0 := by
        unfold tent1
        rw [hcl, max_eq_left (by norm_num : (1 : ℚ) - 2 * 1 ≤ 0),
          max_eq_right (by norm_num : (0 : ℚ) ≤ 2 * 1 - 1)]
        norm_num
      rw [this]
      constructor
      · intro h; right; refine ⟨?_, Or.inr rfl⟩
        by_contra hne; rw [if_neg hne] at h; exact lt_irrefl _ h
      · rintro (⟨_, _, h⟩ | ⟨rfl, _⟩)
        · exact absurd h (lt_irrefl _)
        · simp
    · -- 0 < x < 1: the uniform term is positive
      have hmid : 0 < (1 - |2 * clamp01 x - 1|) * uniform1 d v := by
        rw [hcl]
        apply mul_pos
        · rw [sub_pos, abs_lt]; constructor <;> linarith
        · exact uniform1_pos_iff.mpr hv
      constructor
      · intro _; exact Or.inl ⟨hv, h0, h1⟩
      · intro _
        unfold tent1
        have ha : 0 ≤ max 0 (1 - 2 * clamp01 x) * (if v = 0 then (1 : ℚ) else 0) := by
          apply mul_nonneg (le_max_left _ _); split_ifs <;> norm_num
        have hb : 0 ≤ max 0 (2 * clamp01 x - 1) * (if v = 1 then (1 : ℚ) else 0) := by
          apply mul_nonneg (le_max_left _ _); split_ifs <;> norm_num
        linarith
  · -- off the grid: zero, and neither disjunct holds
    rw [tent1_eq_zero_of_not_mem hd x hv]
    constructor
    · intro h; exact absurd h (lt_irrefl _)
    · rintro (⟨h, _⟩ | ⟨rfl, h⟩)
      · exact absurd h hv
      · rcases h with rfl | rfl
        · exact absurd (zero_mem_gridVals d) hv
        · exact absurd (one_mem_gridVals hd) hv

/-! ## The product kernel -/

variable {𝒮 : SmallIndex} (𝓜 : Mesh) (m : ℕ)

/-- The one-coordinate law of the tent kernel at a day-`(m+1)` sentence: the tent law at the
day-`m` price if the sentence was already small, the uniform law if it is new.
Source: [[bli-program]] §2.4 (`⨂_{φ∈S_m} ν^tent(t_φ) ⊗ ⨂_{φ ∈ S_{m+1}∖S_m} V`)
Kind: D
Fidelity: exact -/
def tentCoord (t : Table 𝒮 m) (φ : ↥(𝒮.S (m + 1))) (v : ℚ) : ℚ :=
  if h : φ.1 ∈ 𝒮.S m then tent1 (𝓜.d (m + 1)) (t ⟨φ.1, h⟩) v else uniform1 (𝓜.d (m + 1)) v

/-- **The tent kernel's law**: the product of the one-coordinate laws.
Source: [[bli-program]] §2.4
Kind: D
Fidelity: exact -/
def tentLaw (t : Table 𝒮 m) : Superbelief 𝒮 (m + 1) :=
  fun Q => ∏ φ, tentCoord 𝓜 m t φ (Q φ)

variable {𝓜 m}

/-- One-coordinate laws are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentCoord_nonneg (t : Table 𝒮 m) (φ : ↥(𝒮.S (m + 1))) (v : ℚ) :
    0 ≤ tentCoord 𝓜 m t φ v := by
  unfold tentCoord; split_ifs
  · exact tent1_nonneg _ _ _
  · exact uniform1_nonneg _ _

/-- One-coordinate laws sum to one over the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentCoord_sum_one (t : Table 𝒮 m) (φ : ↥(𝒮.S (m + 1))) :
    ∑ v ∈ gridVals (𝓜.d (m + 1)), tentCoord 𝓜 m t φ v = 1 := by
  unfold tentCoord; split_ifs
  · exact tent1_sum_one (𝓜.d_pos _) _
  · exact uniform1_sum_one (𝓜.d_pos _)

/-- One-coordinate laws vanish off the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentCoord_eq_zero_of_not_mem (t : Table 𝒮 m) (φ : ↥(𝒮.S (m + 1))) {v : ℚ}
    (hv : v ∉ gridVals (𝓜.d (m + 1))) : tentCoord 𝓜 m t φ v = 0 := by
  unfold tentCoord; split_ifs
  · exact tent1_eq_zero_of_not_mem (𝓜.d_pos _) _ hv
  · exact uniform1_eq_zero_of_not_mem hv

/-- The tent law is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentLaw_nonneg (t : Table 𝒮 m) (Q : Table 𝒮 (m + 1)) : 0 ≤ tentLaw 𝓜 m t Q :=
  Finset.prod_nonneg fun φ _ => tentCoord_nonneg t φ _

/-- The tent law vanishes off the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentLaw_eq_zero_of_not_mem (t : Table 𝒮 m) {Q : Table 𝒮 (m + 1)}
    (hQ : Q ∉ grid 𝒮 𝓜.d (m + 1)) : tentLaw 𝓜 m t Q = 0 := by
  rw [mem_grid_iff] at hQ
  simp only [not_forall] at hQ
  obtain ⟨φ, hφ⟩ := hQ
  exact Finset.prod_eq_zero (Finset.mem_univ φ) (tentCoord_eq_zero_of_not_mem t φ hφ)

/-- The tent law sums to one over the grid (product of one-coordinate sums).
Source: [[bli-program]] §3.4
Kind: P
Fidelity: exact
Hyps: (a) none (the mesh carries `0 < d`) -/
lemma tentLaw_sum_one (t : Table 𝒮 m) : ∑ Q ∈ grid 𝒮 𝓜.d (m + 1), tentLaw 𝓜 m t Q = 1 := by
  unfold tentLaw grid
  rw [Finset.sum_prod_piFinset]
  exact Finset.prod_eq_one fun φ _ => tentCoord_sum_one t φ

/-- **`tentKernel_isProb`.**
Source: [[bli-program]] §3.4
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tentLaw_isProb (t : Table 𝒮 m) : IsProb 𝓜.d (tentLaw 𝓜 m t) :=
  ⟨tentLaw_nonneg t, fun _ hQ => tentLaw_eq_zero_of_not_mem t hQ, tentLaw_sum_one t⟩

/-- **`tentKernel_balanced`**: the restricted mean of the tent law at a unit-cube table is that
table (marginalize the product coordinate by coordinate).
Source: [[bli-program]] §3.4 ("the product over coordinates is … `Balanced`")
Kind: P
Fidelity: exact
Hyps: (a) `t.InUnit` -/
theorem tentLaw_balanced {t : Table 𝒮 m} (ht : t.InUnit) : Balanced 𝓜.d (tentLaw 𝓜 m t) t := by
  intro ψ
  set ψ' : ↥(𝒮.S (m + 1)) := ⟨ψ.1, 𝒮.mono m ψ.2⟩ with hψ'
  show meanOn (grid 𝒮 𝓜.d (m + 1)) (tentLaw 𝓜 m t) ψ' = t ψ
  unfold meanOn tentLaw grid
  -- fold `Q ψ'` into the product as an extra factor at coordinate `ψ'`
  set g' : ↥(𝒮.S (m + 1)) → ℚ → ℚ :=
    fun φ v => tentCoord 𝓜 m t φ v * (if φ = ψ' then v else 1) with hg'
  have hfold : ∀ Q : Table 𝒮 (m + 1),
      (∏ φ, tentCoord 𝓜 m t φ (Q φ)) * Q ψ' = ∏ φ, g' φ (Q φ) := by
    intro Q
    simp only [hg']
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (fun Q _ => hfold Q), Finset.sum_prod_piFinset _ g']
  have hcoord : ∀ φ : ↥(𝒮.S (m + 1)),
      ∑ v ∈ gridVals (𝓜.d (m + 1)), g' φ v = if φ = ψ' then t ψ else 1 := by
    intro φ
    simp only [hg']
    by_cases hφ : φ = ψ'
    · subst hφ
      simp only [if_true]
      unfold tentCoord
      simp only [dif_pos (show ψ'.1 ∈ 𝒮.S m from ψ.2)]
      exact tent1_mean (𝓜.d_pos _) (ht ψ)
    · simp only [hφ, if_false, mul_one]
      exact tentCoord_sum_one t φ
  rw [Finset.prod_congr rfl (fun φ _ => hcoord φ), Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]

/-- **The tent kernel** of record on day `m`.
Source: [[bli-program]] §2.4 (this run's construction; not in the corpus)
Kind: D
Fidelity: exact -/
def tentKernel (𝓜 : Mesh) (m : ℕ) : Kernel 𝒮 𝓜.d m where
  law := tentLaw 𝓜 m
  prob := tentLaw_isProb
  balanced := fun _ ht => tentLaw_balanced ht

/-- The tent skeleton: the tent kernel on every day.
Source: [[bli-program]] §2.4
Kind: D
Fidelity: exact -/
def tentSkeleton (𝒮 : SmallIndex) (𝓜 : Mesh) : Skeleton 𝒮 𝓜.d := ⟨fun m => tentKernel 𝓜 m⟩

/-- Unfolding lemma for the tent kernel.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tentKernel_law (𝓜 : Mesh) (m : ℕ) (t : Table 𝒮 m) :
    (tentKernel (𝒮 := 𝒮) 𝓜 m).law t = tentLaw 𝓜 m t := rfl

/-- Positivity of a product of nonnegative factors is positivity of every factor.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prod_pos_iff_of_nonneg {ι : Type} [Fintype ι] {f : ι → ℚ} (hf : ∀ i, 0 ≤ f i) :
    0 < ∏ i, f i ↔ ∀ i, 0 < f i := by
  constructor
  · intro h i
    rcases (hf i).eq_or_lt with h0 | h0
    · rw [Finset.prod_eq_zero (Finset.mem_univ i) h0.symm] at h
      exact absurd h (lt_irrefl _)
    · exact h0
  · intro h
    exact Finset.prod_pos fun i _ => h i

/-- **Support of the tent kernel = the product face**: at a unit-cube table `t`, the tent law is
positive at `Q` iff `Q` is a grid table agreeing with `t` wherever `t` is 0 or 1.
Source: [[bli-program]] §3.4 (`NonDegenerate` on the product face); mandate T7
Kind: P
Fidelity: exact
Hyps: (a) `t.InUnit` -/
theorem tentLaw_pos_iff {t : Table 𝒮 m} (ht : t.InUnit) (Q : Table 𝒮 (m + 1)) :
    0 < tentLaw 𝓜 m t Q ↔ Q ∈ faceProd 𝒮 𝓜.d m t := by
  have hd := 𝓜.d_pos (m + 1)
  rw [mem_faceProd_iff, mem_grid_iff]
  unfold tentLaw
  rw [prod_pos_iff_of_nonneg (fun φ => tentCoord_nonneg t φ _)]
  constructor
  · intro h
    refine ⟨fun φ => ?_, fun ψ hψ => ?_⟩
    · have hφ := h φ
      unfold tentCoord at hφ
      split_ifs at hφ with hmem
      · rcases (tent1_pos_iff hd (ht ⟨φ.1, hmem⟩) _).mp hφ with ⟨hg, -⟩ | ⟨hv, h01⟩
        · exact hg
        · rw [hv]
          rcases h01 with h0 | h0 <;> rw [h0]
          · exact zero_mem_gridVals _
          · exact one_mem_gridVals hd
      · exact uniform1_pos_iff.mp hφ
    · have hφ := h ⟨ψ.1, 𝒮.mono m ψ.2⟩
      unfold tentCoord at hφ
      rw [dif_pos ψ.2] at hφ
      rcases (tent1_pos_iff hd (ht ψ) _).mp hφ with ⟨-, h0, h1⟩ | ⟨hv, -⟩
      · exfalso
        rcases hψ with h | h <;> rw [h] at h0 h1 <;> linarith
      · exact hv
  · rintro ⟨hgrid, hface⟩ φ
    unfold tentCoord
    split_ifs with hmem
    · rw [tent1_pos_iff hd (ht ⟨φ.1, hmem⟩)]
      by_cases hint : 0 < t ⟨φ.1, hmem⟩ ∧ t ⟨φ.1, hmem⟩ < 1
      · exact Or.inl ⟨hgrid φ, hint⟩
      · right
        have h01 : t ⟨φ.1, hmem⟩ = 0 ∨ t ⟨φ.1, hmem⟩ = 1 := by
          have := ht ⟨φ.1, hmem⟩
          rcases this.1.eq_or_lt with h0 | h0
          · exact Or.inl h0.symm
          · rcases this.2.eq_or_lt with h1 | h1
            · exact Or.inr h1
            · exact absurd ⟨h0, h1⟩ hint
        refine ⟨?_, h01⟩
        have := hface ⟨φ.1, hmem⟩ h01
        rw [Table.restrict_apply] at this
        exact this
    · exact uniform1_pos_iff.mpr (hgrid φ)

/-- **`tentKernel_nonDegenerate`**: positive mass on every point of the product face.
Source: [[bli-program]] §3.4; bli-slides-018 (the surviving form of full support)
Kind: P
Fidelity: exact
Hyps: (a) `t.InUnit` -/
theorem tentLaw_nonDegenerate {t : Table 𝒮 m} (ht : t.InUnit) :
    NonDegenerate 𝓜.d (tentLaw 𝓜 m t) t :=
  fun Q hQ => (tentLaw_pos_iff ht Q).mpr hQ

/-- **The face theorem on the product grid (E1, product case)**: the product face *is* the
generated face — every product-face point carries positive mass in some balance solution (the
tent kernel), and no balance solution charges anything outside the product face
(`faceGen_subset_faceProd`). Landed here because its witness lives here; `bli-superbelief`
takes the general-grid case.
Source: [[bli-program]] §3.4 (face theorem, product case `C:E1`)
Kind: C
Fidelity: exact
Hyps: (a) `t.InUnit` -/
theorem faceProd_eq_faceGen {t : Table 𝒮 m} (ht : t.InUnit) :
    faceProd 𝒮 𝓜.d m t = faceGen (grid 𝒮 𝓜.d (m + 1)) t := by
  apply Finset.Subset.antisymm
  · intro Q hQ
    exact mem_faceGen_of_pos (tentLaw_isProb t)
      (balanced_iff_restrict_meanOn_eq.mp (tentLaw_balanced ht)) ((tentLaw_pos_iff ht Q).mpr hQ)
  · exact faceGen_subset_faceProd _ _

end Cleanroom.Bli.BliFinite
