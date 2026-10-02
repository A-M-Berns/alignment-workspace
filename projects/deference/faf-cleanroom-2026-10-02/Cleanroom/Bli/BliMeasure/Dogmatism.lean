import Cleanroom.Bli.BliMeasure.Constraints
import Mathlib.Analysis.Convex.Combination

/-!
# `bli-measure` · Dogmatism: when is the realized next state charged? (target 4)

* `mem_faceGen_cgrid_iff` — **the face of a grid table on the grid of record is a support
  condition**: `Q ∈ faceGen (cgrid (m+1)) t` iff `Q ∈ cgrid (m+1)` and `Q`'s restriction vanishes
  wherever `t`'s vector does. (⇒) is pinning at `0`; (⇐) is `bli-superbelief`'s hull
  characterization `faceGen_eq_hullFace` with the explicit perturbation `t + ε(t − Q.restrict)`,
  `ε` the least positive weight of `t`, written as a convex combination of the restrictions of
  point masses (which are grid tables). This is the B3 form of the mandate's "relative interior
  of the hull": on the world-vector grid the relative interior is a support condition.
* `candidate_charged_of_support` / `realized_charged` — **the sufficient condition**: when the
  mesh is fine enough that rounding kills no support world at day `n` (`MeshFine n`:
  `1/d n ≤` every positive weight — automatic on the denominator mesh, `meshFine_denomMesh`)
  and the base has full support on the stage's consistent worlds, every day-`(n+1)` candidate
  supported on `DP.D n`-consistent worlds is charged — in particular the realized one, since the
  base's day-`(n+1)` measure is `DP.D (n+1)`-supported and stages grow. So the Bayesian-update
  headline is **not vacuous** on such days (`0 < 𝐏_n(σ_{n+1})`), with the per-day mesh proviso
  stated explicitly (the mandate's "if that proviso cannot be made uniform in `n`").
* `support_lost_of_coarse` — **N−**: on a mesh with `d n = 1` and a base with two support
  worlds, rounding zeroes a support world (the rounded measure is a point mass). Which world is
  zeroed is `remainderRound`'s classical choice, so the null-conditioning instance
  (`𝐏_n(σ) = 0`, `TB` with both sides `0`) cannot be pinned to the rounding; it is exhibited in
  `NullConditioning.lean` (repair round 2) through a base whose next measure leaves the previous
  support (`dogBase`, `dog_null_conditioning`, `dog_TB_degenerate`).
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliSuperbelief

variable {DP : DeductiveProcess} (base : CoherentBase DP) (𝓜 : Mesh)

/-! ## The face of a grid table is a support condition -/

/-- The point table of a world: the marginal table of the point mass at `u₀`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pointTable {B : ℕ → ℕ} (m : ℕ) (u₀ : FiniteWorld (B m)) : Table (wIndex B) m :=
  fun φ => wMarginal (fun u => if u = u₀ then (1 : ℚ) else 0) φ.1

/-- The value of a coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma wcAt_val {B : ℕ → ℕ} {k m : ℕ} (hk : k ≤ m) (u : FiniteWorld (B k)) :
    (wcAt (B := B) hk u).1 = worldConj u := rfl

/-- The point table pays a sentence as its world does.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pointTable_apply {B : ℕ → ℕ} (m : ℕ) (u₀ : FiniteWorld (B m)) (φ : ↥((wIndex B).S m)) :
    pointTable m u₀ φ = u₀.payoutRat φ.1 := by
  unfold pointTable wMarginal
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' univ u₀, if_pos (mem_univ _)]

/-- The restriction of the day-`(m+1)` point table at an extension is the day-`m` point table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_pointTable_extFW (𝔅 : AtomBounds) (m : ℕ) (u : FiniteWorld (𝔅.B m)) :
    (pointTable (m + 1) (extFW (𝔅.B_mono m) u)).restrict = pointTable m u := by
  funext φ
  rw [Table.restrict_apply, pointTable_apply, pointTable_apply, payoutRat_extFW]

/-- The sum over `FiniteWorld (B m)` of a grid table's day-`m` coordinates is one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_apply_wcAt_succ {m : ℕ} {Q : Table (wIndex base.𝔅.B) (m + 1)} (hQ : Q ∈ cgrid base.𝔅 𝓜 (m + 1)) :
    ∑ u : FiniteWorld (base.𝔅.B m), Q (wcAt (Nat.le_succ m) u) = 1 := by
  simp only [cgrid_apply_wcAt base.𝔅 𝓜 hQ (Nat.le_succ m)]
  rw [Finset.sum_fiberwise (univ : Finset (FiniteWorld (base.𝔅.B (m + 1)))) (restrFW (base.𝔅.B_mono m))]
  exact vecOf_sum base.𝔅 𝓜 hQ

/-- Summing a longer world's payouts of the day-`m` conjunctions over the fiber of a day-`k`
world gives its payout of the day-`k` conjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_payoutRat_worldConj_fiber {k m : ℕ} (hk : k ≤ m) (u' : FiniteWorld (base.𝔅.B (m + 1)))
    (u₀ : FiniteWorld (base.𝔅.B k)) :
    ∑ u ∈ univ.filter (fun u : FiniteWorld (base.𝔅.B m) => restrFW (base.𝔅.B_le hk) u = u₀),
        u'.payoutRat (worldConj u) =
      u'.payoutRat (worldConj u₀) := by
  simp only [payoutRat_worldConj (base.𝔅.B_mono m)]
  rw [Finset.sum_ite_eq, payoutRat_worldConj (base.𝔅.B_le (hk.trans (Nat.le_succ m)))]
  have : restrFW (base.𝔅.B_mono m) u' ∈
      univ.filter (fun u : FiniteWorld (base.𝔅.B m) => restrFW (base.𝔅.B_le hk) u = u₀) ↔
      restrFW (base.𝔅.B_le (hk.trans (Nat.le_succ m))) u' = u₀ := by
    rw [Finset.mem_filter, restrFW_restrFW]
    simp
  by_cases h : restrFW (base.𝔅.B_le (hk.trans (Nat.le_succ m))) u' = u₀
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]

/-- A grid table's day-`k` coordinate is the sum of its day-`m` coordinates over the fiber
(`k ≤ m`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma apply_wcAt_eq_sum_fiber {m : ℕ} {Q : Table (wIndex base.𝔅.B) (m + 1)}
    (hQ : Q ∈ cgrid base.𝔅 𝓜 (m + 1)) {k : ℕ} (hk : k ≤ m) (u₀ : FiniteWorld (base.𝔅.B k)) :
    Q (wcAt (hk.trans (Nat.le_succ m)) u₀) =
      ∑ u ∈ univ.filter (fun u : FiniteWorld (base.𝔅.B m) => restrFW (base.𝔅.B_le hk) u = u₀),
        Q (wcAt (Nat.le_succ m) u) := by
  rw [cgrid_apply_eq_wMarginal base.𝔅 𝓜 hQ]
  simp only [cgrid_apply_eq_wMarginal base.𝔅 𝓜 hQ, wcAt_val]
  unfold wMarginal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u' _
  rw [← Finset.mul_sum, sum_payoutRat_worldConj_fiber base hk u' u₀]

/-- **(⇒) Pinning**: a face member vanishes (after restriction) wherever `t` does.
Source: bli-slides-021 (pinning); mandate target 4
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem restrict_eq_zero_of_mem_faceGen {m : ℕ} {t : Table (wIndex base.𝔅.B) m}
    {Q : Table (wIndex base.𝔅.B) (m + 1)} (hQ : Q ∈ faceGen (cgrid base.𝔅 𝓜 (m + 1)) t)
    (u : FiniteWorld (base.𝔅.B m)) (hu : vecOf t u = 0) : Q (wcAt (Nat.le_succ m) u) = 0 := by
  obtain ⟨-, F, hF, hb, hpos⟩ := mem_faceGen_iff.mp hQ
  have hmean : meanOn (cgrid base.𝔅 𝓜 (m + 1)) F (wcAt (Nat.le_succ m) u) = 0 := by
    have := congrFun hb (wcSelf m u)
    rw [Table.restrict_apply] at this
    rw [← hu]
    exact this
  exact IsProbOn.coord_eq_zero_of_meanOn_eq_zero hF (cgrid_inUnit base.𝔅 𝓜 (m + 1)) hmean hpos

/-- The least positive weight of a grid table's vector.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def minPos {m : ℕ} (t : Table (wIndex base.𝔅.B) m) : ℚ :=
  if h : (univ.filter fun u : FiniteWorld (base.𝔅.B m) => vecOf t u ≠ 0).Nonempty
  then (univ.filter fun u : FiniteWorld (base.𝔅.B m) => vecOf t u ≠ 0).inf' h (vecOf t)
  else 1

/-- The least positive weight is positive and below every positive weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma minPos_spec {m : ℕ} {t : Table (wIndex base.𝔅.B) m} (ht : t ∈ cgrid base.𝔅 𝓜 m) :
    0 < minPos base t ∧ ∀ u, vecOf t u ≠ 0 → minPos base t ≤ vecOf t u := by
  have hne : (univ.filter fun u : FiniteWorld (base.𝔅.B m) => vecOf t u ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    have hsum := vecOf_sum base.𝔅 𝓜 ht
    rw [Finset.sum_eq_zero (fun u _ => not_not.mp (h (mem_univ u)))] at hsum
    exact zero_ne_one hsum
  unfold minPos
  rw [dif_pos hne]
  constructor
  · obtain ⟨u, hu, hmin⟩ := Finset.exists_mem_eq_inf' hne (vecOf t)
    rw [hmin]
    rw [Finset.mem_filter] at hu
    exact lt_of_le_of_ne (vecOf_nonneg base.𝔅 𝓜 ht u) (Ne.symm hu.2)
  · intro u hu
    exact Finset.inf'_le (vecOf t) (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩)

/-- **The face of a grid table on the grid of record is a support condition.**
`Q ∈ faceGen (cgrid (m+1)) t` iff `Q` is a grid table whose restriction vanishes wherever `t`'s
vector does — on the world-vector grid, "relative interior of the hull" is "same support".
Source: [[bli-measure-mandate]] target 4 (`faceGen_eq_hullFace`, "the face is the whole
`D n`-consistent subgrid"); [[bli-program]] §3.4
Kind: P
Fidelity: exact
Hyps: (a) `ht` -/
theorem mem_faceGen_cgrid_iff {m : ℕ} {t : Table (wIndex base.𝔅.B) m} (ht : t ∈ cgrid base.𝔅 𝓜 m)
    (Q : Table (wIndex base.𝔅.B) (m + 1)) :
    Q ∈ faceGen (cgrid base.𝔅 𝓜 (m + 1)) t ↔
      Q ∈ cgrid base.𝔅 𝓜 (m + 1) ∧
        ∀ u : FiniteWorld (base.𝔅.B m), vecOf t u = 0 → Q (wcAt (Nat.le_succ m) u) = 0 := by
  constructor
  · intro hQ
    exact ⟨faceGen_subset _ _ hQ, fun u hu => restrict_eq_zero_of_mem_faceGen base 𝓜 hQ u hu⟩
  · rintro ⟨hQ, hsupp⟩
    rw [faceGen_eq_hullFace]
    obtain ⟨hε, hεle⟩ := minPos_spec base 𝓜 ht
    refine ⟨hQ, minPos base t, hε, ?_⟩
    -- the perturbed point as a probability vector
    set p : FiniteWorld (base.𝔅.B m) → ℚ :=
      fun u => vecOf t u + minPos base t * (vecOf t u - Q (wcAt (Nat.le_succ m) u)) with hp
    have hp0 : ∀ u, 0 ≤ p u := by
      intro u
      simp only [hp]
      by_cases hu : vecOf t u = 0
      · rw [hu, hsupp u hu]; simp
      · have h1 := hεle u hu
        have h2 : Q (wcAt (Nat.le_succ m) u) ≤ 1 := (cgrid_inUnit base.𝔅 𝓜 (m + 1) Q hQ _).2
        have h3 : 0 ≤ Q (wcAt (Nat.le_succ m) u) := (cgrid_inUnit base.𝔅 𝓜 (m + 1) Q hQ _).1
        nlinarith [vecOf_nonneg base.𝔅 𝓜 ht u]
    have hp1 : ∑ u, p u = 1 := by
      simp only [hp]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, vecOf_sum base.𝔅 𝓜 ht,
        sum_apply_wcAt_succ base 𝓜 hQ]
      ring
    -- the perturbed point is the convex combination of point tables weighted by `p`
    refine mem_convexHull_of_exists_fintype p
      (fun u => (pointTable (m + 1) (extFW (base.𝔅.B_mono m) u)).restrict) hp0 hp1 ?_ ?_
    · intro u
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨pointTable (m + 1) (extFW (base.𝔅.B_mono m) u),
        Cleanroom.Bli.BliMeasure.pointTable_mem_cgrid base.𝔅 𝓜 (m + 1) _, rfl⟩
    · funext φ
      obtain ⟨k, hk, u₀, hu₀⟩ := mem_wIndex.mp φ.2
      have hφ : φ = wcAt hk u₀ := wcAt_eq hk u₀ φ hu₀.symm
      subst hφ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply,
        restrict_pointTable_extFW, pointTable_apply, wcAt_val]
      have ht' : t (wcAt hk u₀) =
          ∑ u ∈ univ.filter (fun u : FiniteWorld (base.𝔅.B m) => restrFW (base.𝔅.B_le hk) u = u₀),
            vecOf t u := cgrid_apply_wcAt base.𝔅 𝓜 ht hk u₀
      have hQ' : Q.restrict (wcAt hk u₀) =
          ∑ u ∈ univ.filter (fun u : FiniteWorld (base.𝔅.B m) => restrFW (base.𝔅.B_le hk) u = u₀),
            Q (wcAt (Nat.le_succ m) u) := by
        rw [Table.restrict_apply]
        exact apply_wcAt_eq_sum_fiber base 𝓜 hQ hk u₀
      have hR : ∑ u : FiniteWorld (base.𝔅.B m), p u * u.payoutRat (worldConj u₀) =
          ∑ u ∈ univ.filter (fun u : FiniteWorld (base.𝔅.B m) => restrFW (base.𝔅.B_le hk) u = u₀),
            p u := by
        rw [← Finset.sum_filter_add_sum_filter_not univ
          (fun u : FiniteWorld (base.𝔅.B m) => restrFW (base.𝔅.B_le hk) u = u₀)]
        have hz : ∑ u ∈ univ.filter (fun u : FiniteWorld (base.𝔅.B m) =>
            ¬ restrFW (base.𝔅.B_le hk) u = u₀), p u * u.payoutRat (worldConj u₀) = 0 := by
          apply Finset.sum_eq_zero
          intro u hu
          rw [Finset.mem_filter] at hu
          rw [payoutRat_worldConj (base.𝔅.B_le hk), if_neg hu.2, mul_zero]
        rw [hz, add_zero]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.mem_filter] at hu
        rw [payoutRat_worldConj (base.𝔅.B_le hk), if_pos hu.2, mul_one]
      rw [hR, ht', hQ', ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]

/-! ## The sufficient condition -/

/-- **`MeshFine n`**: the day-`n` mesh resolves every positive weight of the exposed measure
(`1/d n ≤ w n u` whenever `w n u ≠ 0`), so rounding kills no support world.
Source: [[bli-measure-mandate]] target 4 (the mesh proviso)
Kind: D
Fidelity: exact -/
def MeshFine (n : ℕ) : Prop := ∀ u, base.w n u ≠ 0 → 1 / (𝓜.d n : ℚ) ≤ base.w n u

/-- Under `MeshFine n`, rounding preserves the support exactly.
Source: [[bli-measure-mandate]] target 4 ("rounding kills no support world: prove the lemma")
Kind: P
Fidelity: exact
Hyps: (a) `hf` -/
theorem measureRound_ne_zero_iff_of_meshFine {n : ℕ} (hf : MeshFine base 𝓜 n)
    (u : FiniteWorld (base.𝔅.B n)) : measureRound base 𝓜 n u ≠ 0 ↔ base.w n u ≠ 0 := by
  constructor
  · exact w_ne_zero_of_measureRound_ne_zero base 𝓜 n
  · intro hw h0
    have hlt := remainderRound_abs_sub_lt (𝓜.d_pos n) (base.w n) (base.w_nonneg n) (base.w_sum n) u
    change |measureRound base 𝓜 n u - base.w n u| < 1 / 𝓜.d n at hlt
    rw [h0, zero_sub, abs_neg, abs_of_nonneg (base.w_nonneg n u)] at hlt
    exact absurd (hf u hw) (not_le.mpr hlt)

/-- The denominator mesh is fine on every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem meshFine_denomMesh (n : ℕ) : MeshFine base (denomMesh base) n := by
  intro u hu
  obtain ⟨k, hk⟩ := w_grid_denomMesh base n u
  have hd : (0 : ℚ) < (denomMesh base).d n := by exact_mod_cast (denomMesh base).d_pos n
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    rw [this] at hk
    simp at hk
    exact hu hk
  rw [hk, div_le_div_iff_of_pos_right hd]
  exact_mod_cast hk1

/-- **Every candidate supported on the stage's consistent worlds is charged** (mesh fine at day
`n`, full support of the base on the day-`n` consistent worlds): a day-`(n+1)` grid table whose
restriction charges only `DP.D n`-consistent worlds lies in the face of the rounded table.
Source: [[bli-measure-mandate]] target 4 (sufficient condition)
Kind: C
Fidelity: exact
Hyps: (a) `hfull` (full support on the consistent worlds — `pcCoreWeights_fullSupport` over the
recursion), `hf` (`MeshFine n`) -/
theorem candidate_charged_of_support {n : ℕ}
    (hfull : ∀ u : FiniteWorld (base.𝔅.B n), (worldOf u).ConsistentWith (DP.D n) → base.w n u ≠ 0)
    (hf : MeshFine base 𝓜 n) {Q : Table (wIndex base.𝔅.B) (n + 1)} (hQ : Q ∈ cgrid base.𝔅 𝓜 (n + 1))
    (hsupp : ∀ u' : FiniteWorld (base.𝔅.B (n + 1)), vecOf Q u' ≠ 0 →
      (worldOf (restrFW (base.𝔅.B_mono n) u')).ConsistentWith (DP.D n)) :
    Q ∈ faceGen (cgrid base.𝔅 𝓜 (n + 1)) (roundedTable base 𝓜 n) := by
  rw [mem_faceGen_cgrid_iff base 𝓜 (roundedTable_mem_cgrid base 𝓜 n)]
  refine ⟨hQ, fun u hu => ?_⟩
  rw [vecOf_roundedTable] at hu
  rw [cgrid_apply_wcAt base.𝔅 𝓜 hQ (Nat.le_succ n)]
  apply Finset.sum_eq_zero
  intro u' hu'
  rw [Finset.mem_filter] at hu'
  by_contra hne
  have hcons := hsupp u' hne
  rw [hu'.2] at hcons
  have := (measureRound_ne_zero_iff_of_meshFine base 𝓜 hf u).mpr (hfull u hcons)
  exact this hu

/-- **The realized next state is charged** (mesh fine at day `n`, full support of the base on the
day-`n` consistent worlds): `0 < 𝐏_n(⌜𝑸_{n+1} = actual (n+1)⌝)`. The base's day-`(n+1)` measure is
`DP.D (n+1)`-supported and the stage grows, so its rounding's restriction charges only
`DP.D n`-consistent worlds. The Bayesian-update headline is not vacuous on such days.
Source: [[bli-measure-mandate]] target 4; `bli-superbelief` E6 (`dogmatism`), the B3 form
Kind: C
Fidelity: exact
Hyps: (a) `hfull`, `hf` (per-day mesh proviso, stated explicitly) -/
theorem realized_charged {n : ℕ}
    (hfull : ∀ u : FiniteWorld (base.𝔅.B n), (worldOf u).ConsistentWith (DP.D n) → base.w n u ≠ 0)
    (hf : MeshFine base 𝓜 n) :
    0 < superbelief (b3History base 𝓜) n (b3Actual base 𝓜 (n + 1)) := by
  rw [b3_FS base 𝓜 n (b3Actual_mem base 𝓜 (n + 1)), wdecode_b3Actual]
  apply candidate_charged_of_support base 𝓜 hfull hf (roundedTable_mem_cgrid base 𝓜 (n + 1))
  intro u' hu'
  rw [vecOf_roundedTable] at hu'
  have hw := w_ne_zero_of_measureRound_ne_zero base 𝓜 (n + 1) hu'
  have hcons := base.w_supp (n + 1) u' hw
  intro φ hφ
  have hB := base.B_stage n φ hφ
  exact (holds_worldOf_restrFW (base.𝔅.B_mono n) u' hB).mpr (hcons φ (DP.mono n hφ))

/-! ## N−: a coarse mesh loses support -/

/-- **N− (support loss by rounding)**: on a mesh with `d n = 1`, a base with two support worlds on
day `n` has a support world zeroed by rounding (the rounded measure is a point mass).
Source: [[bli-measure-mandate]] target 4 (N−)
Kind: N−
Fidelity: exact
Hyps: (a) `hd`, two support worlds -/
theorem support_lost_of_coarse {n : ℕ} (hd : 𝓜.d n = 1) {u₁ u₂ : FiniteWorld (base.𝔅.B n)}
    (hne : u₁ ≠ u₂) (h₁ : base.w n u₁ ≠ 0) (h₂ : base.w n u₂ ≠ 0) :
    ∃ u, base.w n u ≠ 0 ∧ measureRound base 𝓜 n u = 0 := by
  by_contra hcon
  have hcon' : ∀ u, base.w n u ≠ 0 → measureRound base 𝓜 n u ≠ 0 :=
    fun u hu h0 => hcon ⟨u, hu, h0⟩
  have hr : ∀ u, base.w n u ≠ 0 → 1 ≤ measureRound base 𝓜 n u := by
    intro u hu
    obtain ⟨k, hk⟩ := measureRound_grid base 𝓜 n u
    rw [hd, Nat.cast_one, div_one] at hk
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0] at hk; exact hcon' u hu (by rw [hk]; rfl)
    rw [hk]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hsum := measureRound_sum base 𝓜 n
  have hpair : measureRound base 𝓜 n u₁ + measureRound base 𝓜 n u₂ ≤ 1 := by
    rw [← hsum, ← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun u _ _ => measureRound_nonneg base 𝓜 n u)
  linarith [hr u₁ h₁, hr u₂ h₂]

end Cleanroom.Bli.BliMeasure
