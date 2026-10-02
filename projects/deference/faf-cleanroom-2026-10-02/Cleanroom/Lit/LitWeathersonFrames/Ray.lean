import Cleanroom.Lit.LitWeathersonFrames.CFrame
import Cleanroom.Trust.TtFiniteFrames.Geanakoplos
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin

/-!
# Ray frames on `ℕ`: the lumping bridge and the ray lemma (T5, T8)

Package `lit-weatherson-frames` (faf-cleanroom run, 2026-09-30). A **ray frame** is the
countable frame on `ℕ` whose expert at world `n` has learned `F ≥ n` and nothing else: row `n` is
`π(· | Ici n)`, for any full-support prior `π` (`IsRayPrior`). Weatherson's **Coin** is the
geometric instance (`Coin.lean`).

The engine is the **lumping bridge** (T5): for each `N`, collapse the tail `{m ≥ N}` to one world
and get a finite frame on `Fin (N+1)`, built by the dependency's `Frame.ofCorr` from the
upward-ray correspondence `i ↦ Ici i`, which is reflexive, transitive and nested. Its rows
reproduce the ray frame's estimates exactly (`lump_E_eq`), its prior reproduces `Eℕ π`
(`lump_E_prior`), and a recommended strategy on the ray frame restricts to a recommended strategy
on the lumped frame for a *finite* sub-menu (`lump_recommended`). `tt-finite-frames`'
`value_ofCorr_of_rtn` / `totalTrust_ofCorr_of_rtn` (grade (a)) then give the finite inequalities,
and `N → ∞` gives the ray lemma (T8): Total Trust for every integrable variable, Value for every
finite menu of integrable options and for every uniformly bounded menu. The paper's cutoff
argument (l. 190–192) is not needed.
-/

namespace Cleanroom.Lit.LitWeathersonFrames

open Finset Filter Topology Cleanroom.Found.LitDdbFrames Cleanroom.Trust.TtFiniteFrames

noncomputable section

/-! ## Tail sums and the ray frame -/

/-- A **ray prior**: a full-support distribution on `ℕ`.
Source: [[Deference and Infinite Frames]] §3 l. 188 (Coin's `π`), generalized (inventory 036)
Kind: D
Fidelity: exact -/
def IsRayPrior (π : ℕ → ℝ) : Prop := (∀ n, 0 < π n) ∧ HasSum π 1

/-- The tail mass `π(F ≥ n) = ∑' m, π (m + n)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tail (π : ℕ → ℝ) (n : ℕ) : ℝ := ∑' m, π (m + n)

/-- The tail sum `∑' m, π (m + n) * X (m + n)` of a variable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tailE (π X : ℕ → ℝ) (n : ℕ) : ℝ := ∑' m, π (m + n) * X (m + n)

/-- Row `n` of the ray frame: `π(· | Ici n)`, guarded product form `𝟙[n ≤ m] π m / tail π n`.
Source: [[Deference and Infinite Frames]] §3 l. 188 (`P(F = x) = π(· | F ≥ x)`)
Kind: D
Fidelity: exact -/
def rayP (π : ℕ → ℝ) (n m : ℕ) : ℝ := if n ≤ m then π m / tail π n else 0

/-- A ray prior is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsRayPrior.isDist {π : ℕ → ℝ} (hπ : IsRayPrior π) : IsDist π :=
  ⟨fun n => (hπ.1 n).le, hπ.2⟩

/-- Shifted summability.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsRayPrior.summable_shift {π : ℕ → ℝ} (hπ : IsRayPrior π) (n : ℕ) :
    Summable (fun m => π (m + n)) :=
  (summable_nat_add_iff n).mpr hπ.2.summable

/-- The tail has positive mass under a ray prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsRayPrior.tail_pos {π : ℕ → ℝ} (hπ : IsRayPrior π) (n : ℕ) : 0 < tail π n :=
  (hπ.summable_shift n).tsum_pos (fun m => (hπ.1 (m + n)).le) 0 (hπ.1 (0 + n))

/-- Partial mass plus tail is one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsRayPrior.sum_add_tail {π : ℕ → ℝ} (hπ : IsRayPrior π) (n : ℕ) :
    ∑ m ∈ range n, π m + tail π n = 1 := by
  rw [tail, hπ.2.summable.sum_add_tsum_nat_add n, hπ.2.tsum_eq]

/-- The tail tends to zero.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tail_tendsto_zero (π : ℕ → ℝ) : Tendsto (tail π) atTop (𝓝 0) :=
  tendsto_sum_nat_add π

/-- The tail sum of an integrable variable tends to zero in absolute value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tailE_abs_tendsto_zero (π X : ℕ → ℝ) : Tendsto (tailE π (fun m => |X m|)) atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun m => π m * |X m|)

/-- `|tailE π X n| ≤ tailE π |X| n` for a ray prior and an integrable `X`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem abs_tailE_le {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X) (n : ℕ) :
    |tailE π X n| ≤ tailE π (fun m => |X m|) n := by
  unfold tailE
  have h1 : Summable (fun m => π (m + n) * X (m + n)) :=
    (summable_nat_add_iff n).mpr (hX.summable_mul hπ.isDist.1)
  have h2 : Summable (fun m => π (m + n) * |X (m + n)|) := (summable_nat_add_iff n).mpr hX
  have h2' : Summable (fun m => ‖π (m + n) * X (m + n)‖) :=
    h2.congr fun m => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ.1 _).le]
  calc |∑' m, π (m + n) * X (m + n)| = ‖∑' m, π (m + n) * X (m + n)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' m, ‖π (m + n) * X (m + n)‖ := norm_tsum_le_tsum_norm h2'
    _ = ∑' m, π (m + n) * |X (m + n)| :=
        tsum_congr fun m => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ.1 _).le]

/-- **The ray frame**: rows `π(· | Ici n)`.
Source: [[Deference and Infinite Frames]] §3 l. 188; inventory 036
Kind: D
Fidelity: exact -/
def rayFrame (π : ℕ → ℝ) (hπ : IsRayPrior π) : CFrame ℕ where
  P := rayP π
  P_nonneg := fun n m => by
    unfold rayP
    split_ifs
    · exact div_nonneg (hπ.1 m).le (hπ.tail_pos n).le
    · exact le_rfl
  P_hasSum := fun n => by
    have h : HasSum (fun m => rayP π n (m + n)) (tail π n / tail π n) := by
      have := ((hπ.summable_shift n).hasSum).div_const (tail π n)
      refine this.congr_fun fun m => ?_
      simp [rayP]
    rw [div_self (hπ.tail_pos n).ne'] at h
    have h' := (hasSum_nat_add_iff n).mp h
    have hz : ∑ i ∈ range n, rayP π n i = 0 :=
      sum_eq_zero fun i hi => by simp [rayP, not_le.mpr (mem_range.mp hi)]
    rwa [hz, add_zero] at h'

/-- The rows of the ray frame, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rayFrame_P (π : ℕ → ℝ) (hπ : IsRayPrior π) : (rayFrame π hπ).P = rayP π := rfl

/-- The summand `𝟙[n ≤ m] π m X m` is summable for integrable `X`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem summable_ind_mul {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X) (n : ℕ) :
    Summable (fun m => if n ≤ m then π m * X m else 0) := by
  refine Summable.of_norm_bounded hX fun m => ?_
  rw [Real.norm_eq_abs]
  split_ifs
  · rw [abs_mul, abs_of_nonneg (hπ.1 m).le]
  · simp [mul_nonneg (hπ.1 m).le (abs_nonneg _)]

/-- The tail sum from `n` of `𝟙[n ≤ ·] π X` is `tailE π X n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tsum_ind_mul_eq_tailE {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X)
    (n : ℕ) : ∑' m, (if n ≤ m then π m * X m else 0) = tailE π X n := by
  have h := (summable_ind_mul hπ hX n).sum_add_tsum_nat_add n
  have hz : ∑ i ∈ range n, (if n ≤ i then π i * X i else 0) = 0 :=
    sum_eq_zero fun i hi => by simp [not_le.mpr (mem_range.mp hi)]
  rw [hz, zero_add] at h
  rw [← h, tailE]
  exact tsum_congr fun m => by simp

/-- **The ray frame's estimate**: `E_{P_n}(X) = tailE π X n / tail π n` for integrable `X`.
Source: [[Deference and Infinite Frames]] §3 l. 190 (`Exp(X | F ≥ k, π)`)
Kind: L
Fidelity: n/a -/
theorem rayE {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X) (n : ℕ) :
    Eℕ (rayP π n) X = tailE π X n / tail π n := by
  unfold Eℕ
  rw [← tsum_ind_mul_eq_tailE hπ hX n, ← tsum_div_const]
  refine tsum_congr fun m => ?_
  unfold rayP
  split_ifs <;> simp [div_mul_eq_mul_div]

/-- `tail π n · E_{P_n}(X) = tailE π X n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tail_mul_rayE {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X) (n : ℕ) :
    tail π n * Eℕ (rayP π n) X = tailE π X n := by
  rw [rayE hπ hX, mul_div_cancel₀ _ (hπ.tail_pos n).ne']

/-- Every row of the ray frame integrates a `π`-integrable variable (the row's density w.r.t.
`π` is at most `1 / tail π n`): the integrability transfer of T5.
Source: mandate T5
Kind: L
Fidelity: n/a -/
theorem IntegrableW.rowsIntegrable_ray {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X) :
    RowsIntegrable (rayFrame π hπ) X := by
  intro n
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg ((rayFrame π hπ).P_nonneg n m) (abs_nonneg _))
    (fun m => ?_) (hX.div_const (tail π n))
  show rayP π n m * |X m| ≤ π m * |X m| / tail π n
  unfold rayP
  split_ifs
  · rw [div_mul_eq_mul_div]
  · rw [zero_mul]; exact div_nonneg (mul_nonneg (hπ.1 m).le (abs_nonneg _)) (hπ.tail_pos n).le

/-- Rows of the ray frame are pairwise distinct: the cell constraint is vacuous on ray frames
(every strategy `S : ℕ → ι` is a strategy).
Source: none: infrastructure (T6 needs it for Coin's strategies)
Kind: L
Fidelity: n/a -/
theorem rayP_inj {π : ℕ → ℝ} (hπ : IsRayPrior π) {n n' : ℕ} (h : rayP π n = rayP π n') :
    n = n' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := congrFun h n
    simp [rayP, not_le.mpr hlt, (hπ.1 n).ne', (hπ.tail_pos n).ne'] at this
  · have := congrFun h n'
    simp [rayP, not_le.mpr hlt] at this
    exact absurd this.symm (div_pos (hπ.1 n') (hπ.tail_pos n')).ne'

/-- Every `S : ℕ → ι` is a strategy on a ray frame.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rayFrame_isStrategy {π : ℕ → ℝ} (hπ : IsRayPrior π) {ι : Type} (S : ℕ → ι) :
    (rayFrame π hπ).IsStrategyC S :=
  fun n n' h => by rw [rayP_inj hπ h]

/-- Tail sum of a step variable `𝟙[k ≤ ·] c` from `n ≤ k`: `c · tail π k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tailE_step_of_le {π : ℕ → ℝ} (hπ : IsRayPrior π) {n k : ℕ} (hnk : n ≤ k) (c : ℝ) :
    tailE π (fun m => if k ≤ m then c else 0) n = c * tail π k := by
  unfold tailE tail
  have hf : Summable (fun m => π (m + n) * (if k ≤ m + n then c else 0)) := by
    refine Summable.of_norm_bounded ((hπ.summable_shift n).mul_right |c|) fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ.1 _).le]
    split_ifs <;> simp [mul_nonneg (hπ.1 _).le (abs_nonneg c)]
  have h := hf.sum_add_tsum_nat_add (k - n)
  have hz : ∑ i ∈ range (k - n), π (i + n) * (if k ≤ i + n then c else 0) = 0 :=
    sum_eq_zero fun i hi => by
      have : ¬ k ≤ i + n := by have := mem_range.mp hi; omega
      simp [this]
  rw [hz, zero_add] at h
  rw [← h, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have h1 : k ≤ m + (k - n) + n := by omega
  have h2 : m + (k - n) + n = m + k := by omega
  simp [h2, mul_comm]

/-- Tail sum of a step variable `𝟙[k ≤ ·] c` from `n ≥ k`: `c · tail π n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tailE_step_of_ge {π : ℕ → ℝ} {n k : ℕ} (hkn : k ≤ n) (c : ℝ) :
    tailE π (fun m => if k ≤ m then c else 0) n = c * tail π n := by
  unfold tailE tail
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have : k ≤ m + n := by omega
  simp [this, mul_comm]

/-- Estimates of a step variable `𝟙[k ≤ ·] c` on the ray frame, case `n ≤ k`:
`E_{P_n} = c · tail π k / tail π n`.
Source: [[Deference and Infinite Frames]] §3 l. 188 (the `O_i` estimates)
Kind: L
Fidelity: n/a -/
theorem rayE_step_of_le {π : ℕ → ℝ} (hπ : IsRayPrior π) {n k : ℕ} (hnk : n ≤ k) (c : ℝ) :
    Eℕ (rayP π n) (fun m => if k ≤ m then c else 0) = c * tail π k / tail π n := by
  rw [rayE hπ (Bdd.integrableW ⟨|c|, fun m => by split_ifs <;> simp⟩ hπ.isDist),
    tailE_step_of_le hπ hnk]

/-- Estimates of a step variable `𝟙[k ≤ ·] c` on the ray frame, case `k ≤ n`: `E_{P_n} = c`.
Source: [[Deference and Infinite Frames]] §3 l. 188 (the `O_i` estimates)
Kind: L
Fidelity: n/a -/
theorem rayE_step_of_ge {π : ℕ → ℝ} (hπ : IsRayPrior π) {n k : ℕ} (hkn : k ≤ n) (c : ℝ) :
    Eℕ (rayP π n) (fun m => if k ≤ m then c else 0) = c := by
  rw [rayE hπ (Bdd.integrableW ⟨|c|, fun m => by split_ifs <;> simp⟩ hπ.isDist),
    tailE_step_of_ge hkn, mul_div_cancel_right₀ _ (hπ.tail_pos n).ne']

/-! ## The lumped finite frame on `Fin (N+1)` (T5) -/

/-- The lumped prior on `ℕ` (worlds `< N` keep their mass; world `N` carries the tail).
Source: mandate T5
Kind: D
Fidelity: n/a -/
def lumpPrior (π : ℕ → ℝ) (N : ℕ) (m : ℕ) : ℝ := if m < N then π m else tail π N

/-- The lumped variable on `ℕ` (worlds `< N` keep their value; world `N` carries the tail
average `E_{P_N}(X)`).
Source: mandate T5
Kind: D
Fidelity: n/a -/
def lumpVar (π X : ℕ → ℝ) (N : ℕ) (m : ℕ) : ℝ := if m < N then X m else Eℕ (rayP π N) X

/-- The lumped prior as a vector on `Fin (N+1)`.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def lumpπ (π : ℕ → ℝ) (N : ℕ) : Fin (N+1) → ℝ := fun i => lumpPrior π N i.val

/-- The lumped variable as a vector on `Fin (N+1)`.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def lumpX (π X : ℕ → ℝ) (N : ℕ) : Fin (N+1) → ℝ := fun i => lumpVar π X N i.val

/-- The upward-ray correspondence `i ↦ Ici i` on `Fin (N+1)`.
Source: mandate T5; [[Deference and Infinite Frames]] §3 l. 188 (`F ≥ x`)
Kind: D
Fidelity: exact -/
def lumpK (N : ℕ) : Corr (Fin (N+1)) := fun i => Finset.Ici i

/-- The upward-ray correspondence is reflexive, transitive and nested.
Source: mandate T5
Kind: L
Fidelity: n/a -/
theorem lumpK_rtn (N : ℕ) : (lumpK N).RTN := by
  refine ⟨fun i => by simp [lumpK], fun i j hj => ?_, fun i j => ?_⟩
  · intro k hk
    simp only [lumpK, Finset.mem_Ici] at hj hk ⊢
    exact le_trans hj hk
  · rcases le_total i j with h | h
    · right; right
      intro k hk
      simp only [lumpK, Finset.mem_Ici] at hk ⊢
      exact le_trans h hk
    · right; left
      intro k hk
      simp only [lumpK, Finset.mem_Ici] at hk ⊢
      exact le_trans h hk

/-- The lumped prior has full support.
Source: mandate T5
Kind: L
Fidelity: n/a -/
theorem lumpπ_pos {π : ℕ → ℝ} (hπ : IsRayPrior π) (N : ℕ) : ∀ i, 0 < lumpπ π N i := by
  intro i
  unfold lumpπ lumpPrior
  split_ifs
  · exact hπ.1 _
  · exact hπ.tail_pos N

/-- **The lumped frame**: the dependency's conditioning frame of the lumped prior on the
upward-ray correspondence.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def lumpFrame (π : ℕ → ℝ) (hπ : IsRayPrior π) (N : ℕ) : Frame (Fin (N+1)) :=
  Frame.ofCorr (lumpπ π N) (fun i => (lumpπ_pos hπ N i).le) (lumpK N)
    (Corr.mass_pos_of_reflexive (lumpπ_pos hπ N) (lumpK_rtn N).1)

/-- Sums over `Ici i` in `Fin (N+1)` are sums over `Ico i (N+1)` in `ℕ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_Ici_fin {N : ℕ} (i : Fin (N+1)) (g : ℕ → ℝ) :
    ∑ v ∈ Finset.Ici i, g v.val = ∑ m ∈ Ico i.val (N+1), g m := by
  have h1 : Finset.Ici i = univ.filter (fun v => i ≤ v) := by ext v; simp
  rw [h1, sum_filter]
  have h2 : (fun v : Fin (N+1) => if i ≤ v then g v.val else 0) =
      fun v => (fun m => if i.val ≤ m then g m else 0) v.val := by
    funext v; rfl
  rw [h2, Fin.sum_univ_eq_sum_range (fun m => if i.val ≤ m then g m else 0) (N+1), ← sum_filter]
  congr 1
  ext m; simp [mem_Ico]; omega

/-- Partial sum from `i` to `N` plus the tail from `N` is the tail from `i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_Ico_add_tsum {f : ℕ → ℝ} (hf : Summable f) {i N : ℕ} (hiN : i ≤ N) :
    ∑ m ∈ Ico i N, f m + ∑' m, f (m + N) = ∑' m, f (m + i) := by
  have h := ((summable_nat_add_iff i).mpr hf).sum_add_tsum_nat_add (N - i)
  rw [sum_Ico_eq_sum_range]
  have e1 : ∑ k ∈ range (N - i), f (i + k) = ∑ k ∈ range (N - i), f (k + i) :=
    sum_congr rfl fun k _ => by rw [add_comm]
  have e2 : ∑' m, f (m + N) = ∑' m, f (m + (N - i) + i) :=
    tsum_congr fun m => by congr 1; omega
  rw [e1, e2]; exact h

/-- The lumped prior is a probability vector.
Source: mandate T5
Kind: L
Fidelity: n/a -/
theorem lumpπ_mem {π : ℕ → ℝ} (hπ : IsRayPrior π) (N : ℕ) : lumpπ π N ∈ stdSimplex ℝ (Fin (N+1)) := by
  refine ⟨fun i => (lumpπ_pos hπ N i).le, ?_⟩
  unfold lumpπ
  rw [Fin.sum_univ_eq_sum_range (lumpPrior π N) (N+1), sum_range_succ]
  have : ∑ m ∈ range N, lumpPrior π N m = ∑ m ∈ range N, π m :=
    sum_congr rfl fun m hm => by simp [lumpPrior, mem_range.mp hm]
  rw [this]
  simp only [lumpPrior, lt_irrefl, ↓reduceIte]
  exact hπ.sum_add_tail N

/-- The mass of the lumped cell `Ici i` is the tail from `i`.
Source: mandate T5
Kind: L
Fidelity: n/a -/
theorem lump_mass_Ici {π : ℕ → ℝ} (hπ : IsRayPrior π) (N : ℕ) (i : Fin (N+1)) :
    mass (lumpπ π N) (lumpK N i) = tail π i.val := by
  unfold mass lumpK lumpπ
  rw [sum_Ici_fin i (lumpPrior π N), sum_Ico_succ_top (Nat.lt_succ_iff.mp i.isLt)]
  have : ∑ m ∈ Ico i.val N, lumpPrior π N m = ∑ m ∈ Ico i.val N, π m :=
    sum_congr rfl fun m hm => by simp [lumpPrior, (mem_Ico.mp hm).2]
  rw [this]
  simp only [lumpPrior, lt_irrefl, ↓reduceIte]
  exact sum_Ico_add_tsum hπ.2.summable (Nat.lt_succ_iff.mp i.isLt)

/-- The lumped cell sum `∑_{v ∈ Ici i} π̂ v X̂ v` is the tail sum from `i`.
Source: mandate T5
Kind: L
Fidelity: n/a -/
theorem lump_sum_Ici {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X) (N : ℕ)
    (i : Fin (N+1)) :
    ∑ v ∈ lumpK N i, lumpπ π N v * lumpX π X N v = tailE π X i.val := by
  unfold lumpK lumpπ lumpX
  rw [sum_Ici_fin i (fun m => lumpPrior π N m * lumpVar π X N m),
    sum_Ico_succ_top (Nat.lt_succ_iff.mp i.isLt)]
  have : ∑ m ∈ Ico i.val N, lumpPrior π N m * lumpVar π X N m = ∑ m ∈ Ico i.val N, π m * X m :=
    sum_congr rfl fun m hm => by simp [lumpPrior, lumpVar, (mem_Ico.mp hm).2]
  rw [this]
  simp only [lumpPrior, lumpVar, lt_irrefl, ↓reduceIte]
  rw [tail_mul_rayE hπ hX N]
  exact sum_Ico_add_tsum (hX.summable_mul hπ.isDist.1) (Nat.lt_succ_iff.mp i.isLt)

/-- **T5 (i). The lumped frame reproduces the ray frame's estimates**:
`E_{F̂.P i}(X̂) = E_{P_i}(X)` for every `i : Fin (N+1)` and integrable `X`.
Source: mandate T5 (i)
Kind: L
Fidelity: n/a -/
theorem lump_E_eq {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X) (N : ℕ)
    (i : Fin (N+1)) :
    E ((lumpFrame π hπ N).P i) (lumpX π X N) = Eℕ (rayP π i.val) X := by
  unfold lumpFrame
  rw [Frame.ofCorr_E_eq, lump_sum_Ici hπ hX N i, lump_mass_Ici hπ N i, rayE hπ hX]

/-- **T5 (ii). The lumped prior reproduces `E_π`**: `E_{π̂}(X̂) = E_π(X)` for integrable `X`.
Source: mandate T5 (ii)
Kind: L
Fidelity: n/a -/
theorem lump_E_prior {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X) (N : ℕ) :
    E (lumpπ π N) (lumpX π X N) = Eℕ π X := by
  have h := lump_sum_Ici hπ hX N 0
  have h0 : lumpK N 0 = univ := by ext v; simp [lumpK]
  rw [h0] at h
  unfold E
  rw [h, tailE, Eℕ]
  simp

/-- **T5 (iv). The return of a lumped strategy**: for `Ŝ v := X̂_{o (S v)}`,
`stratValue π̂ Ŝ = ∑_{m < N} π m · o (S m) m + tailE π (o (S N)) N`.
Source: mandate T5 (iv)
Kind: L
Fidelity: n/a -/
theorem lump_stratValue {π : ℕ → ℝ} (hπ : IsRayPrior π) {ι : Type} {o : ι → ℕ → ℝ}
    (ho : ∀ i, IntegrableW π (o i)) (S : ℕ → ι) (N : ℕ) :
    stratValue (lumpπ π N) (fun v => lumpX π (o (S v.val)) N) =
      ∑ m ∈ range N, π m * o (S m) m + tailE π (o (S N)) N := by
  unfold stratValue lumpπ lumpX
  rw [Fin.sum_univ_eq_sum_range (fun m => lumpPrior π N m * lumpVar π (o (S m)) N m) (N+1),
    sum_range_succ]
  have : ∑ m ∈ range N, lumpPrior π N m * lumpVar π (o (S m)) N m =
      ∑ m ∈ range N, π m * o (S m) m :=
    sum_congr rfl fun m hm => by simp [lumpPrior, lumpVar, mem_range.mp hm]
  rw [this]
  simp only [lumpPrior, lumpVar, lt_irrefl, ↓reduceIte]
  rw [tail_mul_rayE hπ (ho _) N]

/-! ## T5 (iii): recommended strategies transfer to the lumped frame -/

/-- The lumped strategy `v ↦ X̂_{o (S v)}`.
Source: mandate T5 (iii)
Kind: D
Fidelity: n/a -/
def lumpStrat (π : ℕ → ℝ) {ι : Type} (o : ι → ℕ → ℝ) (S : ℕ → ι) (N : ℕ) :
    Fin (N+1) → (Fin (N+1) → ℝ) :=
  fun v => lumpX π (o (S v.val)) N

/-- The finite sub-menu used by the lumped strategy, plus the option `o j` under comparison.
Source: mandate T5 (iii)
Kind: D
Fidelity: n/a -/
def lumpMenu (π : ℕ → ℝ) {ι : Type} (o : ι → ℕ → ℝ) (S : ℕ → ι) (N : ℕ) (j : ι) :
    DecisionProblem (Fin (N+1)) :=
  (univ.image (fun v : Fin (N+1) => lumpX π (o (S v.val)) N)) ∪ {lumpX π (o j) N}

/-- **T5 (iii).** A recommended strategy on the ray frame lumps to a recommended strategy on the
lumped frame for the finite sub-menu `lumpMenu`. The cell constraint holds because the lumped
frame's rows are pairwise distinct (`Frame.ofCorr_P_inj`), and optimality transfers through
`lump_E_eq`.
Source: mandate T5 (iii)
Kind: L
Fidelity: n/a -/
theorem lump_recommended {π : ℕ → ℝ} (hπ : IsRayPrior π) {ι : Type} {o : ι → ℕ → ℝ}
    (ho : ∀ i, IntegrableW π (o i)) {S : ℕ → ι} (hS : RecommendedC (rayFrame π hπ) o S)
    (N : ℕ) (j : ι) :
    (lumpFrame π hπ N).Recommended (lumpMenu π o S N j) (lumpStrat π o S N) := by
  refine ⟨⟨fun v => mem_union_left _ (mem_image_of_mem _ (mem_univ v)), fun v v' h => ?_⟩,
    fun v ô hô => ?_⟩
  · have hK := (Frame.ofCorr_P_inj (lumpπ π N) (lumpπ_pos hπ N) (lumpK N)
      (Corr.mass_pos_of_reflexive (lumpπ_pos hπ N) (lumpK_rtn N).1) v v').mp h
    have h1 : v' ∈ lumpK N v := by rw [hK]; simp [lumpK]
    have h2 : v ∈ lumpK N v' := by rw [← hK]; simp [lumpK]
    simp only [lumpK, Finset.mem_Ici] at h1 h2
    rw [le_antisymm h1 h2]
  · obtain ⟨k, rfl⟩ : ∃ k, ô = lumpX π (o k) N := by
      rcases mem_union.mp hô with h | h
      · obtain ⟨v', -, rfl⟩ := mem_image.mp h
        exact ⟨S v'.val, rfl⟩
      · exact ⟨j, mem_singleton.mp h⟩
    show E _ (lumpX π (o k) N) ≤ E _ (lumpX π (o (S v.val)) N)
    rw [lump_E_eq hπ (ho k), lump_E_eq hπ (ho _)]
    exact hS.2 v.val k

/-- **The finite Value inequality on the lumped frame** (from `value_ofCorr_of_rtn`, grade (a)):
`E_π(o j) ≤ ∑_{m < N} π m · o (S m) m + tailE π (o (S N)) N`.
Source: mandate T8 (b); `tt-finite-frames` `value_ofCorr_of_rtn`
Kind: C
Fidelity: n/a -/
theorem lump_value_ineq {π : ℕ → ℝ} (hπ : IsRayPrior π) {ι : Type} {o : ι → ℕ → ℝ}
    (ho : ∀ i, IntegrableW π (o i)) {S : ℕ → ι} (hS : RecommendedC (rayFrame π hπ) o S)
    (N : ℕ) (j : ι) :
    Eℕ π (o j) ≤ ∑ m ∈ range N, π m * o (S m) m + tailE π (o (S N)) N := by
  have hne : (lumpMenu π o S N j).Nonempty := ⟨_, mem_union_right _ (mem_singleton_self _)⟩
  have h := value_ofCorr_of_rtn (lumpπ_pos hπ N) (lumpK_rtn N) (lumpMenu π o S N j) hne
    (lumpStrat π o S N) (lump_recommended hπ ho hS N j) (lumpX π (o j) N)
    (mem_union_right _ (mem_singleton_self _))
  rw [lump_E_prior hπ (ho j)] at h
  rw [← lump_stratValue hπ ho S N]
  exact h

/-- **The finite Total Trust inequality on the lumped frame** (from `totalTrust_ofCorr_of_rtn`,
grade (a)), written with the ray frame's estimates.
Source: mandate T8 (a); `tt-finite-frames` `totalTrust_ofCorr_of_rtn`
Kind: C
Fidelity: n/a -/
theorem lump_tt_ineq {π : ℕ → ℝ} (hπ : IsRayPrior π) {X : ℕ → ℝ} (hX : IntegrableW π X)
    (N : ℕ) (t : ℝ) :
    0 ≤ ∑ m ∈ range N, π m * (X m - t) * (if t ≤ Eℕ (rayP π m) X then 1 else 0) +
      tail π N * (Eℕ (rayP π N) X - t) * (if t ≤ Eℕ (rayP π N) X then 1 else 0) := by
  have h : 0 ≤ ∑ v, lumpπ π N v * (lumpX π X N v - t) *
      (if t ≤ E ((lumpFrame π hπ N).P v) (lumpX π X N) then 1 else 0) :=
    totalTrust_ofCorr_of_rtn (lumpπ_mem hπ N) (lumpπ_pos hπ N) (lumpK_rtn N) (lumpX π X N) t
  simp only [lump_E_eq hπ hX N] at h
  unfold lumpπ lumpX at h
  rw [Fin.sum_univ_eq_sum_range (fun m => lumpPrior π N m * (lumpVar π X N m - t) *
    (if t ≤ Eℕ (rayP π m) X then 1 else 0)) (N+1), sum_range_succ] at h
  have h1 : ∑ m ∈ range N, lumpPrior π N m * (lumpVar π X N m - t) *
      (if t ≤ Eℕ (rayP π m) X then 1 else 0) =
      ∑ m ∈ range N, π m * (X m - t) * (if t ≤ Eℕ (rayP π m) X then 1 else 0) :=
    sum_congr rfl fun m hm => by simp [lumpPrior, lumpVar, mem_range.mp hm]
  rw [h1] at h
  simpa only [lumpPrior, lumpVar, lt_irrefl, ↓reduceIte] using h

/-! ## T8. The ray lemma -/

/-- `tailE π |X| n ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tailE_abs_nonneg {π : ℕ → ℝ} (hπ : IsRayPrior π) (X : ℕ → ℝ) (n : ℕ) :
    0 ≤ tailE π (fun m => |X m|) n :=
  tsum_nonneg fun _ => mul_nonneg (hπ.1 _).le (abs_nonneg _)

/-- The lump term of the Total Trust inequality tends to zero.
Source: mandate T8 (a)
Kind: L
Fidelity: n/a -/
theorem lump_tt_term_tendsto {π X : ℕ → ℝ} (hπ : IsRayPrior π) (hX : IntegrableW π X) (t : ℝ) :
    Tendsto (fun N => tail π N * (Eℕ (rayP π N) X - t) * (if t ≤ Eℕ (rayP π N) X then 1 else 0))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun N => tailE π (fun m => |X m|) N + |t| * tail π N)
    (fun N => ?_) ?_
  · rw [Real.norm_eq_abs]
    have hind : |(if t ≤ Eℕ (rayP π N) X then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc |tail π N * (Eℕ (rayP π N) X - t) * (if t ≤ Eℕ (rayP π N) X then 1 else 0)|
        = |tail π N * (Eℕ (rayP π N) X - t)| * |(if t ≤ Eℕ (rayP π N) X then (1:ℝ) else 0)| :=
          abs_mul _ _
      _ ≤ |tail π N * (Eℕ (rayP π N) X - t)| * 1 :=
          mul_le_mul_of_nonneg_left hind (abs_nonneg _)
      _ = |tailE π X N - tail π N * t| := by rw [mul_one, mul_sub, tail_mul_rayE hπ hX N]
      _ ≤ |tailE π X N| + |tail π N * t| := abs_sub _ _
      _ ≤ tailE π (fun m => |X m|) N + |t| * tail π N := by
          rw [abs_mul, abs_of_nonneg (hπ.tail_pos N).le, mul_comm]
          exact add_le_add (abs_tailE_le hπ hX N) le_rfl
  · have := (tailE_abs_tendsto_zero π X).add ((tail_tendsto_zero π).const_mul |t|)
    simpa using this

/-- **T8 (a), load-bearing 3. Ray frames are totally trusted** (integrable variables): for every
full-support prior `π` on `ℕ`, the frame whose expert at `n` has learned `F ≥ n` satisfies
product-form Total Trust for every `π`-integrable `X` (every row integrates such an `X`
automatically, `IntegrableW.rowsIntegrable_ray`). Proof: the lumped `Fin (N+1)` frame is
`Frame.ofCorr` of an RTN correspondence, `totalTrust_ofCorr_of_rtn` gives
`0 ≤ ∑_{m<N} π m (X m − t) 𝟙[…] + tail π N (E_{P_N}X − t) 𝟙[…]`, and `N → ∞`. The geometric
weights of Coin are not used; the paper's cutoff argument is not needed.
Source: [[Deference and Infinite Frames]] §3 ll. 190–192 (Coin's Total Trust); inventory 031,
036 (the ray lemma, generalized)
Kind: C
Fidelity: stronger: any full-support prior, integrable `X` (the paper: geometric prior, "any
random variable")
Hyps: (a) `hπ : IsRayPrior π`; the finite theorem `totalTrust_ofCorr_of_rtn` is the
dependency's, at grade (a) -/
theorem ray_totalTrustInt {π : ℕ → ℝ} (hπ : IsRayPrior π) : TotalTrustInt π (rayFrame π hπ) := by
  intro X hX _ t
  show 0 ≤ ∑' m, π m * (X m - t) * (if t ≤ Eℕ (rayP π m) X then 1 else 0)
  have hfs : Summable (fun m => π m * (X m - t) * (if t ≤ Eℕ (rayP π m) X then 1 else 0)) :=
    totalTrust_summand_summable hπ.isDist hX t _
  have h1 := hfs.hasSum.tendsto_sum_nat
  have h3 := h1.add (lump_tt_term_tendsto hπ hX t)
  rw [add_zero] at h3
  exact ge_of_tendsto' h3 (fun N => lump_tt_ineq hπ hX N t)

/-- **T8 (a), bounded form.** Ray frames satisfy `TotalTrustC`.
Source: [[Deference and Infinite Frames]] §3 ll. 190–192; inventory 036
Kind: C
Fidelity: exact
Hyps: (a) `hπ` -/
theorem ray_totalTrustC {π : ℕ → ℝ} (hπ : IsRayPrior π) : TotalTrustC π (rayFrame π hπ) :=
  (ray_totalTrustInt hπ).totalTrustC hπ.isDist

/-- **T8 (b), load-bearing 3. Ray frames are Valued on finite menus of integrable options.**
Proof: `value_ofCorr_of_rtn` on the lumped frame with the finite sub-menu of T5 (iii) gives
`E_π(o j) ≤ ∑_{m<N} π m · o (S m) m + tailE π (o (S N)) N`; the partial sums converge to the
strategy's return, and the lump term is bounded by `∑_i tailE π |o i| N → 0` because the menu is
finite.
Source: [[Deference and Infinite Frames]] §3 l. 194 (the "`O` finite" objection); inventory
031/032 (`Value` for finite menus on Coin), 036
Kind: C
Fidelity: exact (finite menus; integrable options)
Hyps: (a) `hπ`; the finite theorem is the dependency's at grade (a) -/
theorem ray_valueFinInt {π : ℕ → ℝ} (hπ : IsRayPrior π) : ValueFinInt π (rayFrame π hπ) := by
  intro ι _ o ho _ S hS j
  have hret : Summable (fun m => π m * o (S m) m) :=
    stratValue_summable_of_fintype hπ.isDist ho S
  have h1 : Tendsto (fun N => ∑ m ∈ range N, π m * o (S m) m) atTop (𝓝 (stratValueC π o S)) :=
    hret.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun N => tailE π (o (S N)) N) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun N => ∑ i, tailE π (fun m => |o i m|) N) (fun N => ?_) ?_
    · rw [Real.norm_eq_abs]
      refine le_trans (abs_tailE_le hπ (ho _) N) ?_
      exact Finset.single_le_sum (f := fun i => tailE π (fun m => |o i m|) N)
        (fun i _ => tailE_abs_nonneg hπ (o i) N) (mem_univ (S N))
    · have := tendsto_finsetSum (univ : Finset ι) (fun i _ => tailE_abs_tendsto_zero π (o i))
      simpa using this
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact ge_of_tendsto' h3 (fun N => lump_value_ineq hπ ho hS N j)

/-- **T8 (c). Ray frames are Valued on every uniformly bounded menu** (any index type): the lump
term is bounded by `M · tail π N → 0`.
Source: [[Deference and Infinite Frames]] §3 l. 194 (the "unbounded" objection); inventory 036
Kind: C
Fidelity: exact (uniformly bounded options; per-option boundedness is *not* enough — Coin)
Hyps: (a) `hπ`; the finite theorem is the dependency's at grade (a) -/
theorem ray_valueBdd {π : ℕ → ℝ} (hπ : IsRayPrior π) : ValueBdd π (rayFrame π hπ) := by
  intro ι o ho S hS j
  obtain ⟨M, hM⟩ := ho
  have hoI : ∀ i, IntegrableW π (o i) := fun i => Bdd.integrableW ⟨M, hM i⟩ hπ.isDist
  have hret : Summable (fun m => π m * o (S m) m) :=
    stratValue_summable_of_bddFam hπ.isDist ⟨M, hM⟩ S
  have h1 : Tendsto (fun N => ∑ m ∈ range N, π m * o (S m) m) atTop (𝓝 (stratValueC π o S)) :=
    hret.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun N => tailE π (o (S N)) N) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun N => M * tail π N) (fun N => ?_) ?_
    · rw [Real.norm_eq_abs]
      refine le_trans (abs_tailE_le hπ (hoI _) N) ?_
      unfold tailE tail
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun _ => ?_) ((summable_nat_add_iff N).mpr (hoI _))
        ((hπ.summable_shift N).mul_left M)
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM _ _) (hπ.1 _).le
    · simpa using (tail_tendsto_zero π).const_mul M
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact ge_of_tendsto' h3 (fun N => lump_value_ineq hπ hoI hS N j)

end

end Cleanroom.Lit.LitWeathersonFrames
