import Cleanroom.Bli.BliFinite.Witness
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.MinMax

/-!
# `bli-superbelief` · Modulus: the `ℓ¹`-modulus of the tent kernel (E2(a)), with the program's
constant corrected

**The claim of record is false as stated.** [[bli-program]] §2.4/§3.4 (and the mandate) assert
`‖κ(t) − κ(t')‖₁ ≤ 2|S|·‖t − t'‖∞`, "because each one-coordinate law is 2-Lipschitz in `ℓ¹`".
The one-coordinate tent law is *not* 2-Lipschitz in `ℓ¹`: at `d = 2`, `tent1 2 0 = δ₀` and
`tent1 2 (1/2) = U₂`, whose `ℓ¹` distance is `|1 − 1/3| + 1/3 + 1/3 = 4/3 > 2·(1/2) = 1`
(`tentLaw_l1_two_witness`, on the worked witness with `|S 0| = 1`). What is true: the three tent
*weights* are jointly 4-Lipschitz — `|Δw₀| + |Δw_U| + |Δw₁| ≤ 4|Δx|` (`tent_weights_lipschitz`,
equality on either side of `1/2`) — so each one-coordinate law is **4-Lipschitz** in `ℓ¹`
(`tent1_l1_le`, in the clamped price; `clamp01` is 1-Lipschitz), and the product law telescopes
to `‖κ(t) − κ(t')‖₁ ≤ 4·|S m|·‖t − t'‖∞` (`tentLaw_l1_le`), stated with `ε` for the sup norm and
**no unit-cube hypothesis** (the clamp absorbs it). The general product lemma is
`prod_l1_le`: the `ℓ¹` distance of two product probabilities is at most the sum of the
coordinate `ℓ¹` distances (hybrid argument, by induction on the coordinate set).

The corrected constant matters downstream: `bli-trajectory`'s `C:C3` modulus `2|S|/(2d)` becomes
`4|S|/(2d) = 2|S|/d`. Filed in `bli-superbelief-findings`.

Sources: [[bli-program]] §2.4 ("Lipschitz constant 2 in each weight" — true per weight, false for
the law), §3.4 (the claimed `2|S|`); mandate E2(a).
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction Finset Cleanroom.Bli.BliFinite

/-! ## One coordinate -/

/-- **The tent weights are jointly 4-Lipschitz**: `|Δw₀| + |Δw_U| + |Δw₁| ≤ 4|y − y'|`, with
equality when `y`, `y'` are on the same side of `1/2`.
Source: [[bli-program]] §2.4 (corrected: the weights are 2-Lipschitz each, jointly 4)
Kind: P
Fidelity: stronger: the joint constant (the per-weight `2` gives only `6`)
Hyps: (a) none -/
lemma tent_weights_lipschitz (y y' : ℚ) :
    |max 0 (1 - 2 * y) - max 0 (1 - 2 * y')| + |(1 - |2 * y - 1|) - (1 - |2 * y' - 1|)| +
      |max 0 (2 * y - 1) - max 0 (2 * y' - 1)| ≤ 4 * |y - y'| := by
  -- `w₀ − w₁ = 1 − 2y` and `w_U = 1 − w₀ − w₁`
  have key : ∀ a : ℚ, max 0 (1 - 2 * a) - max 0 (2 * a - 1) = 1 - 2 * a := by
    intro a
    rcases le_total (2 * a) 1 with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have keyU : ∀ a : ℚ, 1 - |2 * a - 1| = 1 - max 0 (1 - 2 * a) - max 0 (2 * a - 1) := by
    intro a
    rcases le_total (2 * a) 1 with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [keyU y, keyU y']
  have hky := key y
  have hky' := key y'
  set w0 := max 0 (1 - 2 * y) with hw0
  set w0' := max 0 (1 - 2 * y') with hw0'
  set w1 := max 0 (2 * y - 1) with hw1
  set w1' := max 0 (2 * y' - 1) with hw1'
  -- `|Δw_U| ≤ |Δw₀| + |Δw₁|`
  have hU : |(1 - w0 - w1) - (1 - w0' - w1')| ≤ |w0 - w0'| + |w1 - w1'| := by
    have : (1 - w0 - w1) - (1 - w0' - w1') = -((w0 - w0') + (w1 - w1')) := by ring
    rw [this, abs_neg]
    exact abs_add_le _ _
  -- `|Δw₀| + |Δw₁| = 2|Δy|` by monotonicity
  have h01 : |w0 - w0'| + |w1 - w1'| = 2 * |y - y'| := by
    rcases le_total y y' with hy | hy
    · have hw0le : w0' ≤ w0 := max_le_max le_rfl (by linarith)
      have hw1le : w1 ≤ w1' := max_le_max le_rfl (by linarith)
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have hw0le : w0 ≤ w0' := max_le_max le_rfl (by linarith)
      have hw1le : w1' ≤ w1 := max_le_max le_rfl (by linarith)
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  linarith

/-- `clamp01` is 1-Lipschitz.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clamp01_lipschitz (a b : ℚ) : |clamp01 a - clamp01 b| ≤ |a - b| := by
  unfold clamp01
  calc |max 0 (min 1 a) - max 0 (min 1 b)| = |max (min 1 a) 0 - max (min 1 b) 0| := by
        rw [max_comm 0, max_comm 0]
    _ ≤ |min 1 a - min 1 b| := abs_max_sub_max_le_abs _ _ _
    _ = |max (-a) (-1) - max (-b) (-1)| := by
        rw [min_comm, min_comm 1 b, ← neg_neg (min a 1), ← neg_neg (min b 1), ← max_neg_neg,
          ← max_neg_neg, neg_sub_neg, abs_sub_comm]
    _ ≤ |-a - -b| := abs_max_sub_max_le_abs _ _ _
    _ = |a - b| := by rw [neg_sub_neg, abs_sub_comm]

/-- **The one-coordinate tent law is 4-Lipschitz in `ℓ¹`** (in the clamped price): the `ℓ¹`
distance of `tent1 d x` and `tent1 d x'` over the grid is at most `4·|clamp01 x − clamp01 x'|`.
Source: [[bli-program]] §3.4 (corrected from "2-Lipschitz")
Kind: P
Fidelity: variant: constant `4`, the true one (the program's `2` is refuted by
`tentLaw_l1_two_witness`)
Hyps: (a) `0 < d` -/
lemma tent1_l1_le {d : ℕ} (hd : 0 < d) (x x' : ℚ) :
    ∑ v ∈ gridVals d, |tent1 d x v - tent1 d x' v| ≤ 4 * |clamp01 x - clamp01 x'| := by
  set y := clamp01 x with hy
  set y' := clamp01 x' with hy'
  calc ∑ v ∈ gridVals d, |tent1 d x v - tent1 d x' v|
      ≤ ∑ v ∈ gridVals d, (|max 0 (1 - 2 * y) - max 0 (1 - 2 * y')| * (if v = 0 then 1 else 0) +
          |(1 - |2 * y - 1|) - (1 - |2 * y' - 1|)| * uniform1 d v +
          |max 0 (2 * y - 1) - max 0 (2 * y' - 1)| * (if v = 1 then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro v _
        have hexp : tent1 d x v - tent1 d x' v =
            (max 0 (1 - 2 * y) - max 0 (1 - 2 * y')) * (if v = 0 then 1 else 0) +
            ((1 - |2 * y - 1|) - (1 - |2 * y' - 1|)) * uniform1 d v +
            (max 0 (2 * y - 1) - max 0 (2 * y' - 1)) * (if v = 1 then 1 else 0) := by
          unfold tent1
          rw [← hy, ← hy']
          ring
        rw [hexp]
        refine (abs_add_le _ _).trans ?_
        refine add_le_add (abs_add_le _ _) le_rfl |>.trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by split_ifs <;> norm_num : (0 : ℚ) ≤ if v = 0 then 1 else 0),
          abs_of_nonneg (uniform1_nonneg d v),
          abs_of_nonneg (by split_ifs <;> norm_num : (0 : ℚ) ≤ if v = 1 then 1 else 0)]
    _ = |max 0 (1 - 2 * y) - max 0 (1 - 2 * y')| + |(1 - |2 * y - 1|) - (1 - |2 * y' - 1|)| +
          |max 0 (2 * y - 1) - max 0 (2 * y' - 1)| := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          sum_gridVals_indicator (d := d) _ 0 (zero_mem_gridVals d),
          sum_gridVals_indicator (d := d) _ 1 (one_mem_gridVals hd), ← Finset.mul_sum,
          uniform1_sum_one hd, mul_one]
    _ ≤ 4 * |y - y'| := tent_weights_lipschitz y y'

/-! ## Products of probability vectors -/

section ProdL1

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [DecidableEq κ]

/-- The hybrid inequality, over a coordinate set `s`: the `ℓ¹` distance of the partial products
over `s`, weighted by the `f`-product over the other coordinates, is at most the sum of the
coordinate `ℓ¹` distances over `s`.
Source: none: infrastructure (the telescoping of [[bli-program]] §3.4, made a lemma)
Kind: P
Fidelity: n/a
Hyps: (a) nonnegative coordinate laws of mass one -/
lemma prod_l1_aux (K : Finset κ) (f g : ι → κ → ℚ) (hf0 : ∀ i k, 0 ≤ f i k) (hg0 : ∀ i k, 0 ≤ g i k)
    (hf1 : ∀ i, ∑ k ∈ K, f i k = 1) (hg1 : ∀ i, ∑ k ∈ K, g i k = 1) (s : Finset ι) :
    ∑ x ∈ Fintype.piFinset (fun _ : ι => K),
        (∏ i ∈ Finset.univ \ s, f i (x i)) * |∏ i ∈ s, f i (x i) - ∏ i ∈ s, g i (x i)| ≤
      ∑ i ∈ s, ∑ k ∈ K, |f i k - g i k| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      -- the pointwise bound
      have hpt : ∀ x : ι → κ,
          (∏ i ∈ Finset.univ \ insert a s, f i (x i)) *
              |∏ i ∈ insert a s, f i (x i) - ∏ i ∈ insert a s, g i (x i)| ≤
            (∏ i ∈ Finset.univ \ s, f i (x i)) * |∏ i ∈ s, f i (x i) - ∏ i ∈ s, g i (x i)| +
            (∏ i ∈ Finset.univ \ insert a s, f i (x i)) * (|f a (x a) - g a (x a)| * ∏ i ∈ s, g i (x i)) := by
        intro x
        have hR : 0 ≤ ∏ i ∈ Finset.univ \ insert a s, f i (x i) :=
          Finset.prod_nonneg fun i _ => hf0 i (x i)
        have hsplit : ∏ i ∈ Finset.univ \ s, f i (x i) =
            f a (x a) * ∏ i ∈ Finset.univ \ insert a s, f i (x i) := by
          rw [Finset.sdiff_insert, ← Finset.mul_prod_erase (Finset.univ \ s) (fun i => f i (x i))
            (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩)]
        rw [Finset.prod_insert ha, Finset.prod_insert ha, hsplit]
        have htri : |f a (x a) * ∏ i ∈ s, f i (x i) - g a (x a) * ∏ i ∈ s, g i (x i)| ≤
            f a (x a) * |∏ i ∈ s, f i (x i) - ∏ i ∈ s, g i (x i)| +
            |f a (x a) - g a (x a)| * ∏ i ∈ s, g i (x i) := by
          have heq : f a (x a) * ∏ i ∈ s, f i (x i) - g a (x a) * ∏ i ∈ s, g i (x i) =
              f a (x a) * (∏ i ∈ s, f i (x i) - ∏ i ∈ s, g i (x i)) +
              (f a (x a) - g a (x a)) * ∏ i ∈ s, g i (x i) := by ring
          rw [heq]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (hf0 a (x a)),
            abs_of_nonneg (Finset.prod_nonneg fun i _ => hg0 i (x i))]
        calc (∏ i ∈ Finset.univ \ insert a s, f i (x i)) *
              |f a (x a) * ∏ i ∈ s, f i (x i) - g a (x a) * ∏ i ∈ s, g i (x i)|
            ≤ (∏ i ∈ Finset.univ \ insert a s, f i (x i)) *
              (f a (x a) * |∏ i ∈ s, f i (x i) - ∏ i ∈ s, g i (x i)| +
                |f a (x a) - g a (x a)| * ∏ i ∈ s, g i (x i)) := mul_le_mul_of_nonneg_left htri hR
          _ = _ := by ring
      -- the new term is a product of coordinate sums
      have hnew : ∑ x ∈ Fintype.piFinset (fun _ : ι => K),
          (∏ i ∈ Finset.univ \ insert a s, f i (x i)) *
            (|f a (x a) - g a (x a)| * ∏ i ∈ s, g i (x i)) = ∑ k ∈ K, |f a k - g a k| := by
        let h : ι → κ → ℚ := fun i k =>
          if i ∈ s then g i k else if i = a then |f i k - g i k| else f i k
        have hprod : ∀ x : ι → κ, (∏ i ∈ Finset.univ \ insert a s, f i (x i)) *
            (|f a (x a) - g a (x a)| * ∏ i ∈ s, g i (x i)) = ∏ i, h i (x i) := by
          intro x
          rw [← Finset.prod_sdiff (Finset.subset_univ (insert a s)), Finset.prod_insert ha]
          have h1 : ∏ i ∈ Finset.univ \ insert a s, h i (x i) =
              ∏ i ∈ Finset.univ \ insert a s, f i (x i) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hi' := Finset.mem_sdiff.mp hi
            simp only [Finset.mem_insert, not_or] at hi'
            simp only [h, if_neg hi'.2.2, if_neg hi'.2.1]
          have h2 : h a (x a) = |f a (x a) - g a (x a)| := by
            simp [h, ha]
          have h3 : ∏ i ∈ s, h i (x i) = ∏ i ∈ s, g i (x i) := by
            apply Finset.prod_congr rfl
            intro i hi
            simp only [h, if_pos hi]
          rw [h1, h2, h3]
        rw [Finset.sum_congr rfl (fun x _ => hprod x), ← Finset.prod_univ_sum]
        rw [← Finset.prod_sdiff (Finset.subset_univ (insert a s)), Finset.prod_insert ha]
        have h1 : ∏ i ∈ Finset.univ \ insert a s, ∑ k ∈ K, h i k = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          have hi' := Finset.mem_sdiff.mp hi
          simp only [Finset.mem_insert, not_or] at hi'
          simp only [h, if_neg hi'.2.2, if_neg hi'.2.1]
          exact hf1 i
        have h2 : ∑ k ∈ K, h a k = ∑ k ∈ K, |f a k - g a k| := by
          apply Finset.sum_congr rfl
          intro k _
          simp [h, ha]
        have h3 : ∏ i ∈ s, ∑ k ∈ K, h i k = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          simp only [h, if_pos hi]
          exact hg1 i
        rw [h1, h2, h3, one_mul, mul_one]
      calc ∑ x ∈ Fintype.piFinset (fun _ : ι => K),
            (∏ i ∈ Finset.univ \ insert a s, f i (x i)) *
              |∏ i ∈ insert a s, f i (x i) - ∏ i ∈ insert a s, g i (x i)|
          ≤ ∑ x ∈ Fintype.piFinset (fun _ : ι => K),
              ((∏ i ∈ Finset.univ \ s, f i (x i)) * |∏ i ∈ s, f i (x i) - ∏ i ∈ s, g i (x i)| +
              (∏ i ∈ Finset.univ \ insert a s, f i (x i)) *
                (|f a (x a) - g a (x a)| * ∏ i ∈ s, g i (x i))) :=
            Finset.sum_le_sum fun x _ => hpt x
        _ = (∑ x ∈ Fintype.piFinset (fun _ : ι => K),
              (∏ i ∈ Finset.univ \ s, f i (x i)) * |∏ i ∈ s, f i (x i) - ∏ i ∈ s, g i (x i)|) +
            ∑ k ∈ K, |f a k - g a k| := by rw [Finset.sum_add_distrib, hnew]
        _ ≤ (∑ i ∈ s, ∑ k ∈ K, |f i k - g i k|) + ∑ k ∈ K, |f a k - g a k| := by linarith [ih]
        _ = ∑ i ∈ insert a s, ∑ k ∈ K, |f i k - g i k| := by
            rw [Finset.sum_insert ha]; exact add_comm _ _

/-- **The `ℓ¹` distance of two product probabilities is at most the sum of the coordinate `ℓ¹`
distances.**
Source: [[bli-program]] §3.4 ("telescoping the product"), made a lemma
Kind: P
Fidelity: exact
Hyps: (a) nonnegative coordinate laws of mass one on `K` -/
theorem prod_l1_le (K : Finset κ) (f g : ι → κ → ℚ) (hf0 : ∀ i k, 0 ≤ f i k) (hg0 : ∀ i k, 0 ≤ g i k)
    (hf1 : ∀ i, ∑ k ∈ K, f i k = 1) (hg1 : ∀ i, ∑ k ∈ K, g i k = 1) :
    ∑ x ∈ Fintype.piFinset (fun _ : ι => K), |∏ i, f i (x i) - ∏ i, g i (x i)| ≤
      ∑ i, ∑ k ∈ K, |f i k - g i k| := by
  refine (le_of_eq ?_).trans (prod_l1_aux K f g hf0 hg0 hf1 hg1 Finset.univ)
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sdiff_self, Finset.prod_empty, one_mul]

end ProdL1

/-! ## The tent kernel -/

variable {𝒮 : SmallIndex} {𝓜 : Mesh} {m : ℕ}

/-- The coordinate `ℓ¹` distance of the tent kernel: `≤ 4ε` at an old sentence when the tables are
`ε`-close there, `0` at a new one.
Source: [[bli-program]] §3.4
Kind: L
Fidelity: exact -/
lemma tentCoord_l1_le (t t' : Table 𝒮 m) {ε : ℚ} (hε : ∀ φ, |t φ - t' φ| ≤ ε)
    (φ : ↥(𝒮.S (m + 1))) :
    ∑ v ∈ gridVals (𝓜.d (m + 1)), |tentCoord 𝓜 m t φ v - tentCoord 𝓜 m t' φ v| ≤
      if φ.1 ∈ 𝒮.S m then 4 * ε else 0 := by
  unfold tentCoord
  split_ifs with hφ
  · calc ∑ v ∈ gridVals (𝓜.d (m + 1)),
          |tent1 (𝓜.d (m + 1)) (t ⟨φ.1, hφ⟩) v - tent1 (𝓜.d (m + 1)) (t' ⟨φ.1, hφ⟩) v|
        ≤ 4 * |clamp01 (t ⟨φ.1, hφ⟩) - clamp01 (t' ⟨φ.1, hφ⟩)| := tent1_l1_le (𝓜.d_pos _) _ _
      _ ≤ 4 * ε := by
          have := (clamp01_lipschitz (t ⟨φ.1, hφ⟩) (t' ⟨φ.1, hφ⟩)).trans (hε ⟨φ.1, hφ⟩)
          linarith
  · simp

/-- The day-`(m+1)` sentences already small on day `m` number `|S m|`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma card_filter_old (𝒮 : SmallIndex) (m : ℕ) :
    ((Finset.univ : Finset ↥(𝒮.S (m + 1))).filter (fun φ => φ.1 ∈ 𝒮.S m)).card = (𝒮.S m).card := by
  rw [← Fintype.card_coe (𝒮.S m), ← Finset.card_univ]
  refine Finset.card_bij (fun φ hφ => ⟨φ.1, (Finset.mem_filter.mp hφ).2⟩) ?_ ?_ ?_
  · intro φ _; exact Finset.mem_univ _
  · intro φ _ ψ _ h
    exact Subtype.ext (Subtype.mk.inj h)
  · intro φ' _
    exact ⟨⟨φ'.1, 𝒮.mono m φ'.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, φ'.2⟩, rfl⟩

/-- **E2(a), the `ℓ¹`-modulus of the tent kernel, with the correct constant.** If the day-`m`
tables `t`, `t'` are `ε`-close in every coordinate, the tent laws at `t` and `t'` are
`4·|S m|·ε`-close in `ℓ¹` over the day-`(m+1)` grid. No unit-cube hypothesis (the clamp is
inside `tent1`). The program's `2|S|` is false (`tentLaw_l1_two_witness`).
Source: [[bli-program]] §2.4, §3.4 (`‖κ(t)−κ(t')‖₁ ≤ 2|S|‖t−t'‖∞`, corrected to `4|S|`)
Kind: P
Fidelity: variant: constant `4` in place of the program's false `2`
Hyps: (a) `hε : ∀ φ, |t φ − t' φ| ≤ ε` (the sup-norm bound, spelled out) -/
theorem tentLaw_l1_le (t t' : Table 𝒮 m) {ε : ℚ} (hε : ∀ φ, |t φ - t' φ| ≤ ε) :
    ∑ Q ∈ grid 𝒮 𝓜.d (m + 1), |tentLaw 𝓜 m t Q - tentLaw 𝓜 m t' Q| ≤
      4 * (𝒮.S m).card * ε := by
  classical
  have hprod := prod_l1_le (ι := ↥(𝒮.S (m + 1))) (gridVals (𝓜.d (m + 1)))
    (fun φ v => tentCoord 𝓜 m t φ v) (fun φ v => tentCoord 𝓜 m t' φ v)
    (fun φ v => tentCoord_nonneg t φ v) (fun φ v => tentCoord_nonneg t' φ v)
    (fun φ => tentCoord_sum_one t φ) (fun φ => tentCoord_sum_one t' φ)
  calc ∑ Q ∈ grid 𝒮 𝓜.d (m + 1), |tentLaw 𝓜 m t Q - tentLaw 𝓜 m t' Q|
      = ∑ Q ∈ Fintype.piFinset (fun _ : ↥(𝒮.S (m + 1)) => gridVals (𝓜.d (m + 1))),
          |∏ φ, tentCoord 𝓜 m t φ (Q φ) - ∏ φ, tentCoord 𝓜 m t' φ (Q φ)| := rfl
    _ ≤ ∑ φ, ∑ v ∈ gridVals (𝓜.d (m + 1)), |tentCoord 𝓜 m t φ v - tentCoord 𝓜 m t' φ v| := hprod
    _ ≤ ∑ φ : ↥(𝒮.S (m + 1)), (if φ.1 ∈ 𝒮.S m then 4 * ε else 0) :=
        Finset.sum_le_sum fun φ _ => tentCoord_l1_le t t' hε φ
    _ = 4 * (𝒮.S m).card * ε := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_filter_old]
        ring

/-! ## The refutation of the program's constant -/

/-- **The program's `2|S|` is false.** On the worked witness (`|S 0| = 1`, `d = 2`), the tent laws
at `t₀' = (p ↦ 0)` and `t₀ = (p ↦ 1/2)` — sup-distance exactly `1/2` — are at `ℓ¹` distance `4/3`
(three face points at `|1/3 − 1/9| = 2/9`, six others at `1/9`), while `2·|S 0|·(1/2) = 1 < 4/3`.
The corrected bound `4·1·(1/2) = 2` holds.
Source: [[bli-program]] §2.4/§3.4 (refuted: "each one-coordinate law is 2-Lipschitz in `ℓ¹`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem tentLaw_l1_two_witness :
    (∀ φ, |t₀' φ - t₀ φ| ≤ 1 / 2) ∧
    ∑ Q ∈ grid witIndex witMesh.d 1, |tentLaw witMesh 0 t₀' Q - tentLaw witMesh 0 t₀ Q| = 4 / 3 ∧
    ¬ (∑ Q ∈ grid witIndex witMesh.d 1, |tentLaw witMesh 0 t₀' Q - tentLaw witMesh 0 t₀ Q| ≤
        2 * (witIndex.S 0).card * (1 / 2)) := by
  classical
  have hsum : ∑ Q ∈ grid witIndex witMesh.d 1, |tentLaw witMesh 0 t₀' Q - tentLaw witMesh 0 t₀ Q|
      = 4 / 3 := by
    rw [← Finset.sum_sdiff (faceProd_subset_grid witMesh.d t₀')]
    have hface : ∀ Q ∈ faceProd witIndex witMesh.d 0 t₀',
        |tentLaw witMesh 0 t₀' Q - tentLaw witMesh 0 t₀ Q| = 2 / 9 := by
      intro Q hQ
      obtain ⟨hg, hp⟩ := (mem_faceProd_t₀'_iff Q).mp hQ
      rw [tentLaw_t₀' hg, if_pos hp, tentLaw_t₀ hg]
      norm_num
    have hoff : ∀ Q ∈ grid witIndex witMesh.d 1 \ faceProd witIndex witMesh.d 0 t₀',
        |tentLaw witMesh 0 t₀' Q - tentLaw witMesh 0 t₀ Q| = 1 / 9 := by
      intro Q hQ
      obtain ⟨hg, hnf⟩ := Finset.mem_sdiff.mp hQ
      have hp : Q ⟨pW, pW_mem_S1⟩ ≠ 0 := fun h => hnf ((mem_faceProd_t₀'_iff Q).mpr ⟨hg, h⟩)
      rw [tentLaw_t₀' hg, if_neg hp, tentLaw_t₀ hg]
      norm_num
    rw [Finset.sum_congr rfl hface, Finset.sum_congr rfl hoff, Finset.sum_const, Finset.sum_const,
      Finset.card_sdiff_of_subset (faceProd_subset_grid witMesh.d t₀'), card_grid_witness,
      card_faceProd_t₀', nsmul_eq_mul, nsmul_eq_mul]
    norm_num
  refine ⟨fun φ => by unfold t₀' t₀; norm_num, hsum, ?_⟩
  rw [hsum, witIndex_S_zero, Finset.card_singleton]
  norm_num

end Cleanroom.Bli.BliSuperbelief
