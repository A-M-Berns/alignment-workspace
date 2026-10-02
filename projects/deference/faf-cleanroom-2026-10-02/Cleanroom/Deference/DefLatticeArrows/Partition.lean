import Cleanroom.Deference.DefLatticeArrows.TowerToTrust
import Cleanroom.Deference.DefLatticeArrows.GapBets

/-!
# T4c — The partition argument: band Reflection ⟹ Total Trust, and the four-face square

Package `def-lattice-arrows`, file 9. [[reflection-in-li]] §It joins the circle over
`def-lattice`'s objects: the above-ramp `Ind_δ(q > v)` is a telescoping sum of band weights
along a grid `v = t_0 < t_1 < ⋯ < t_K`, each band's lower face (at `t_k ≥ v`) is a band
value-form instance, and summing the faces (T0 for the two identities `W = ∑ W_k`,
`XW = ∑ XW_k`) gives soft Total Trust above at `(v, δ)`.

**What the partition proves, and what needs no proof (finding F12; audit r1 fidelity B1):**
def-lattice's `BandReflection` quantifies over every band half-width `ε > 0`. A band of
half-width `ε ≥ (1 + δ − v)/2` centred at `v + ε` *is* the up-ramp at `v` on `[0,1]`, so over
the unbounded predicate every soft Total-Trust face is a single wide-band face and the arrow
`BandReflection ⟹ TotalTrust` needs no grid, no band quotes and no partition
(`WideBand.lean`, `totalTrust_of_bandReflection`). The partition's content is therefore
stated for **narrow** bands: the per-instance theorems take the `K` band faces at half-width
`ek ≥ δ` as hypotheses (`softAbove_instance_of_bandFaces`, `softBelow_instance_of_bandFaces`),
and the predicate-level arrows are from `BandReflectionWithin P DP E c` — bands of half-width
`≤ c·δ`, `c ≥ 1` — on the canonical grids (bands of half-width exactly `δ`), where no single
band is the ramp at any `v < 1 − 2cδ` (`bandWt_ne_rampAbove_of_narrow`, `WideBand.lean`).

**The identity, pinned (finding):** for `t' ≥ t + δ`,
`ctsInd δ q t − ctsInd δ q t' = ctsInd δ q t · ctsInd δ (t' + δ) q` for every `q`
(`ctsInd_sub_ctsInd_eq_band`). The wiki's remark that spacing `≥ δ` "is not needed" is
**false** for the product-band form def-lattice fixed (`bandWt`): at `t' = t` the left side is
`0` while the product is positive on `(t, t + δ)`. The grid is therefore quantified with
spacing `≥ δ`; `sk`/`ek` are the band centre and half-width that realise the bracket
`[t_k, t_{k+1} + δ]` as a `bandWt`.

The grid is finite and fixed independently of `n` (LUVs are `[0,1]`-valued, so `t_K ≥ 1`
kills the last ramp). Both halves are proved; with `bandReflection_of_towerValued` (T4b) and
`towerValued_of_softTotalTrust_gapBets` (T5) this closes the square
`BandReflectionWithin ⟺ TotalTrust` (`bandReflectionWithin_iff_totalTrust_onQuotes`), every
existence clause visible. The square over the unbounded predicate
(`bandReflection_iff_totalTrust_onQuotes`, `WideBand.lean`) has `→` free.
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-! ### Ramp arithmetic: the band identity -/

/-- **The band identity**: for `t + δ ≤ t'`, the difference of two up-ramps at `t < t'` is the
product band `ctsInd δ q t · ctsInd δ (t' + δ) q` (an up-ramp at `t` times a down-ramp at
`t' + δ`). Spacing `≥ δ` is necessary: at `t' = t` the left side vanishes while the product is
positive on `(t, t + δ)`.
Source: [[reflection-in-li]] §It joins the circle (the telescoping decomposition), with the
spacing condition the product form needs; mandate T4 (the finding)
Kind: L
Fidelity: exact (the corrected identity)
Hyps: (a) none -/
theorem ctsInd_sub_ctsInd_eq_band {δ : ℚ} (hδ : 0 < δ) {t t' : ℝ} (hgap : t + δ ≤ t')
    (x : ℝ) : ctsInd δ x t - ctsInd δ x t' = ctsInd δ x t * ctsInd δ (t' + δ) x := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  rcases le_or_gt x t with h1 | h1
  · rw [(ctsInd_eq_zero_iff hδ x t).mpr h1, (ctsInd_eq_zero_iff hδ x t').mpr (by linarith)]
    ring
  rcases le_or_gt x (t + δ) with h2 | h2
  · rw [(ctsInd_eq_zero_iff hδ x t').mpr (by linarith),
      (ctsInd_eq_one_iff hδ (t' + δ) x).mpr (by linarith)]
    ring
  rcases le_or_gt x t' with h3 | h3
  · rw [(ctsInd_eq_one_iff hδ x t).mpr (by linarith), (ctsInd_eq_zero_iff hδ x t').mpr h3,
      (ctsInd_eq_one_iff hδ (t' + δ) x).mpr (by linarith)]
    ring
  rcases le_or_gt x (t' + δ) with h4 | h4
  · rw [(ctsInd_eq_one_iff hδ x t).mpr (by linarith), ctsInd_eq_div hδ h3.le h4,
      ctsInd_eq_div hδ (by linarith : x ≤ t' + δ) (by linarith : t' + δ ≤ x + δ)]
    field_simp
    ring
  · rw [(ctsInd_eq_one_iff hδ x t).mpr (by linarith), (ctsInd_eq_one_iff hδ x t').mpr (by linarith),
      (ctsInd_eq_zero_iff hδ (t' + δ) x).mpr h4.le]
    ring

/-- The centre of band `k` of a grid `t` at width `δ`: `(t_k + t_{k+1} + δ)/2`.
Source: mandate T4 (the partition argument)
Kind: D
Fidelity: n/a -/
def sk (t : ℕ → ℚ) (δ : ℚ) (k : ℕ) : ℚ := (t k + t (k + 1) + δ) / 2

/-- The half-width of band `k`: `(t_{k+1} + δ − t_k)/2`.
Source: mandate T4 (the partition argument)
Kind: D
Fidelity: n/a -/
def ek (t : ℕ → ℚ) (δ : ℚ) (k : ℕ) : ℚ := (t (k + 1) + δ - t k) / 2

/-- The band's lower endpoint is `t_k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sk_sub_ek (t : ℕ → ℚ) (δ : ℚ) (k : ℕ) : sk t δ k - ek t δ k = t k := by
  simp [sk, ek]; ring

/-- The band's half-width is positive on a grid with spacing `≥ δ > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ek_pos {t : ℕ → ℚ} {δ : ℚ} (hδ : 0 < δ) (hgap : ∀ k, t k + δ ≤ t (k + 1)) (k : ℕ) :
    0 < ek t δ k := by
  simp only [ek]
  linarith [hgap k]

/-- **Band `k` of the grid is the bracket** `ctsInd δ x t_k − ctsInd δ x t_{k+1}`.
Source: [[reflection-in-li]] §It joins the circle
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bandWt_grid {t : ℕ → ℚ} {δ : ℚ} (hδ : 0 < δ) (hgap : ∀ k, t k + δ ≤ t (k + 1)) (k : ℕ)
    (x : ℝ) : bandWt δ (sk t δ k) (ek t δ k) x = ctsInd δ x (t k) - ctsInd δ x (t (k + 1)) := by
  have h1 : ((sk t δ k : ℚ) : ℝ) - ((ek t δ k : ℚ) : ℝ) = (t k : ℝ) := by
    rw [← Rat.cast_sub, sk_sub_ek]
  have h2 : ((sk t δ k : ℚ) : ℝ) + ((ek t δ k : ℚ) : ℝ) = (t (k + 1) : ℝ) + δ := by
    simp only [sk, ek]; push_cast; ring
  have hgap' : (t k : ℝ) + δ ≤ t (k + 1) := by exact_mod_cast hgap k
  simp only [bandWt]
  rw [h1, h2, ctsInd_sub_ctsInd_eq_band hδ hgap' x]

/-- The grid dominates its origin: `t_0 ≤ t_k` (spacing `≥ δ > 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem grid_ge {t : ℕ → ℚ} {δ : ℚ} (hδ : 0 < δ) (hgap : ∀ k, t k + δ ≤ t (k + 1)) :
    ∀ k, t 0 ≤ t k := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih => linarith [hgap k]

/-- **The telescoping decomposition of the up-ramp**: on `[0, 1]` and a grid with `t_0 = v`,
spacing `≥ δ`, `t_K ≥ 1`, `∑_{k<K} bandWt δ (sk k) (ek k) x = rampAbove δ v x`.
Source: [[reflection-in-li]] §It joins the circle
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sum_bandWt_grid {t : ℕ → ℚ} {δ v : ℚ} (hδ : 0 < δ) (ht0 : t 0 = v)
    (hgap : ∀ k, t k + δ ≤ t (k + 1)) (K : ℕ) (htK : 1 ≤ t K) {x : ℝ} (hx : x ≤ 1) :
    ∑ k ∈ Finset.range K, bandWt δ (sk t δ k) (ek t δ k) x = rampAbove δ v x := by
  simp_rw [bandWt_grid hδ hgap]
  rw [Finset.sum_range_sub' (fun k => ctsInd δ x (t k)) K]
  have hK : ctsInd δ x (t K) = 0 := by
    rw [ctsInd_eq_zero_iff hδ]
    have : (1 : ℝ) ≤ t K := by exact_mod_cast htK
    linarith
  simp [hK, ht0, rampAbove]

/-! ### Sums -/

/-- A `Finset.range` sum as a list sum (for `listComb`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem list_sum_map_range (f : ℕ → ℝ) (K : ℕ) :
    ((List.range K).map f).sum = ∑ k ∈ Finset.range K, f k := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

/-- A `Finset.range` sum of sequences each `≳ₙ 0` is `≳ₙ 0`.
Source: none: infrastructure (FAF `AsympLE.add`)
Kind: L
Fidelity: n/a -/
theorem asympGE_zero_finset_range_sum (f : ℕ → ℕ → ℝ) (K : ℕ)
    (h : ∀ k < K, f k ≳ₙ (fun _ => (0 : ℝ))) :
    (fun n => ∑ k ∈ Finset.range K, f k n) ≳ₙ (fun _ => (0 : ℝ)) := by
  induction K with
  | zero => simpa using AsympEq.asympGE (AsympEq.refl (fun _ => (0 : ℝ)))
  | succ K ih =>
    have := AsympLE.add (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))) (h K (Nat.lt_succ_self K))
    simp only [Finset.sum_range_succ]
    intro ε hε
    filter_upwards [this ε hε] with n hn
    simpa using hn

/-- The novice's expectations are nonnegative.
Source: none: infrastructure (FAF `LUV.expect_mem_Icc`, `IsLogicalInductor.price_mem_Icc`)
Kind: L
Fidelity: n/a -/
theorem expect_nonneg [IsLogicalInductor P DP] (X : LUV) (n : ℕ) : 0 ≤ X.expect P n :=
  (LUV.expect_mem_Icc P n X (fun s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s)).1

/-! ### The two identities `W = ∑ W_k`, `XW = ∑ XW_k` through `E^H_n` -/

/-- **The weight quote is the sum of the band weight quotes**, through `E^H_n`:
`E^H_n(W_n) ≈ₙ ∑_k E^H_n(W_{k,n})` (the combination `W − ∑_k W_k` is valued `0` in every
consistent world, by `sum_bandWt_grid` at the expert's estimate).
Source: [[reflection-in-li]] §It joins the circle ("summing the finitely many bands with the
novice's `loe`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expect_weight_eq_sum_bands [IsLogicalInductor P DP] {E : Expert DP} {X W XW : ℕ → LUV}
    {t : ℕ → ℚ} {δ v : ℚ} (hδ : 0 < δ) (ht0 : t 0 = v) (hgap : ∀ k, t k + δ ≤ t (k + 1))
    (K : ℕ) (htK : 1 ≤ t K) (q : WeightQuote DP E X (rampAbove δ v) W XW)
    (Wk XWk : ℕ → ℕ → LUV)
    (qk : ∀ k, WeightQuote DP E X (bandWt δ (sk t δ k) (ek t δ k)) (Wk k) (XWk k))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (W n).expect P n) ≈ₙ (fun n => ∑ k ∈ Finset.range K, (Wk k n).expect P n) := by
  have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp)
    (ts := (1, W) :: (List.range K).map (fun k => ((-1 : ℚ), Wk k)))
    (fun p hp => by
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
      rcases hp with rfl | ⟨k, -, rfl⟩
      · exact q.weight_codes
      · exact (qk k).weight_codes)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
      rcases hp with rfl | ⟨k, -, rfl⟩
      · exact fun n v hv => ⟨_, q.weight_reflected n v hv⟩
      · exact fun n v hv => ⟨_, (qk k).weight_reflected n v hv⟩))
    (0 : ℝ) (slack := fun _ => 0) tendsto_const_nhds
    (fun n w hw ν hν => by
      have hW := listComb_valuesAt_mem hν (p := (1, W)) (by simp)
      have hWk : ∀ k ∈ Finset.range K, ν (Wk k n) = bandWt δ (sk t δ k) (ek t δ k)
          (E.estimate X n) := by
        intro k hk
        have := listComb_valuesAt_mem hν (p := ((-1 : ℚ), Wk k))
          (by simp only [List.mem_cons, List.mem_map, List.mem_range]
              exact Or.inr ⟨k, Finset.mem_range.mp hk, rfl⟩)
        exact this.eq ((qk k).weight_reflected n w hw)
      rw [listComb_value]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      rw [list_sum_map_range, hW.eq (q.weight_reflected n w hw)]
      rw [Finset.sum_congr rfl (fun k hk => by rw [hWk k hk])]
      have hsum := sum_bandWt_grid hδ ht0 hgap K htK (E.estimate_mem_Icc X n).2
      simp only [Rat.cast_neg, Rat.cast_one, neg_one_mul, Finset.sum_neg_distrib, hsum]
      simp)
    hworld
  have h' : (fun n => (W n).expect P n - ∑ k ∈ Finset.range K, (Wk k n).expect P n) ≈ₙ
      (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [listComb_expect, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      list_sum_map_range]
    simp [Finset.sum_neg_distrib, sub_eq_add_neg]
  exact asympEq_sub_zero_iff.mp h'

/-- **The product quote is the sum of the band product quotes**, through `E^H_n`:
`E^H_n(XW_n) ≈ₙ ∑_k E^H_n(XW_{k,n})` (the combination `XW − ∑_k XW_k` is valued within the
summed slacks of `0`).
Source: [[reflection-in-li]] §It joins the circle
Kind: C
Fidelity: exact (within FAF's slacks)
Hyps: (a) -/
theorem expect_product_eq_sum_bands [IsLogicalInductor P DP] {E : Expert DP}
    {X W XW : ℕ → LUV} {t : ℕ → ℚ} {δ v : ℚ} (hδ : 0 < δ) (ht0 : t 0 = v)
    (hgap : ∀ k, t k + δ ≤ t (k + 1)) (K : ℕ) (htK : 1 ≤ t K)
    (q : WeightQuote DP E X (rampAbove δ v) W XW) (Wk XWk : ℕ → ℕ → LUV)
    (qk : ∀ k, WeightQuote DP E X (bandWt δ (sk t δ k) (ek t δ k)) (Wk k) (XWk k))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n) ≈ₙ (fun n => ∑ k ∈ Finset.range K, (XWk k n).expect P n) := by
  have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp)
    (ts := (1, XW) :: (List.range K).map (fun k => ((-1 : ℚ), XWk k)))
    (fun p hp => by
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
      rcases hp with rfl | ⟨k, -, rfl⟩
      · exact q.product_codes
      · exact (qk k).product_codes)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
      rcases hp with rfl | ⟨k, -, rfl⟩
      · exact (weightQuote_product_valued q)
      · exact (weightQuote_product_valued (qk k))))
    (0 : ℝ) (slack := fun n => q.slack n + ∑ k ∈ Finset.range K, (qk k).slack n)
    (by
      have := q.slack_tendsto.add (tendsto_finsetSum (Finset.range K)
        (fun k _ => (qk k).slack_tendsto))
      simpa using this)
    (fun n w hw ν hν => by
      obtain ⟨x, hx⟩ := q.source_valued n w hw
      obtain ⟨z, hz, hzx⟩ := q.product_reflected n w hw x hx
      have hXW := listComb_valuesAt_mem hν (p := (1, XW)) (by simp)
      have hk : ∀ k ∈ Finset.range K, |ν (XWk k n) -
          x * bandWt δ (sk t δ k) (ek t δ k) (E.estimate X n)| ≤ (qk k).slack n := by
        intro k hk
        obtain ⟨zk, hzk, hzkx⟩ := (qk k).product_reflected n w hw x hx
        have := listComb_valuesAt_mem hν (p := ((-1 : ℚ), XWk k))
          (by simp only [List.mem_cons, List.mem_map, List.mem_range]
              exact Or.inr ⟨k, Finset.mem_range.mp hk, rfl⟩)
        rw [this.eq hzk]
        exact hzkx
      rw [listComb_value]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      rw [list_sum_map_range, hXW.eq hz]
      have hsum := sum_bandWt_grid hδ ht0 hgap K htK (E.estimate_mem_Icc X n).2
      have hlow := Finset.sum_le_sum (fun k hmem => (abs_le.mp (hk k hmem)).1)
      have hup := Finset.sum_le_sum (fun k hmem => (abs_le.mp (hk k hmem)).2)
      rw [Finset.sum_neg_distrib] at hlow
      have hS : ∑ k ∈ Finset.range K, (ν (XWk k n) -
          x * bandWt δ (sk t δ k) (ek t δ k) (E.estimate X n)) =
          ∑ k ∈ Finset.range K, ν (XWk k n) -
            x * ∑ k ∈ Finset.range K, bandWt δ (sk t δ k) (ek t δ k) (E.estimate X n) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hsum] at hS
      rw [abs_le] at hzx ⊢
      simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_zero, neg_one_mul, Finset.sum_neg_distrib,
        one_mul, zero_add, sub_zero]
      constructor <;> linarith [hzx.1, hzx.2, hlow, hup, hS])
    hworld
  have h' : (fun n => (XW n).expect P n - ∑ k ∈ Finset.range K, (XWk k n).expect P n) ≈ₙ
      (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [listComb_expect, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      list_sum_map_range]
    simp [Finset.sum_neg_distrib, sub_eq_add_neg]
  exact asympEq_sub_zero_iff.mp h'

/-! ### The partition argument -/

/-- **Band faces ⟹ soft Total Trust above, per instance (the partition argument)**: on a
grid `v = t_0 < ⋯ < t_K` with spacing `≥ δ` and `t_K ≥ 1`, with the ramp package `(W, XW)` at
`rampAbove δ v` and band packages `(W_k, XW_k)` at every band of the grid, the `K` band faces
`E^H_n(XW_{k,n}) − t_k·E^H_n(W_{k,n}) ≳ₙ 0` (the bands' lower faces, at `t_k = sk − ek`) sum to
`E^H_n(XW_n) − v·E^H_n(W_n) ≈ₙ ∑_k [E^H_n(XW_{k,n}) − t_k E^H_n(W_{k,n})]
+ ∑_k (t_k − v) E^H_n(W_{k,n}) ≳ₙ 0`, the second sum being pointwise nonnegative. The faces
are the instance facts (mandate design decision 1), not the predicate `BandReflection`: over
def-lattice's unbounded-width predicate the conclusion is itself one wide-band face
(`WideBand.lean`, F12; audit r1 fidelity B1), so a statement from the predicate would have a
trivial proof and certify nothing about the telescoping. The bands here have half-width
`ek ≥ δ`; on the canonical grid exactly `δ`.
Source: [[reflection-in-li]] §It joins the circle; vq-wiki-006
Kind: C
Fidelity: exact (grid with spacing `≥ δ`, the corrected identity; faces as hypotheses)
Hyps: (a) the packages `q`, `qk` (data) and the `K` band faces `hfaces` (band value-form
instances at half-width `ek`); `hworld` -/
theorem softAbove_instance_of_bandFaces [IsLogicalInductor P DP] {E : Expert DP}
    {X W XW : ℕ → LUV}
    {t : ℕ → ℚ} {δ v : ℚ} (hδ : 0 < δ) (ht0 : t 0 = v) (hgap : ∀ k, t k + δ ≤ t (k + 1))
    (K : ℕ) (htK : 1 ≤ t K) (q : WeightQuote DP E X (rampAbove δ v) W XW)
    (Wk XWk : ℕ → ℕ → LUV)
    (qk : ∀ k, WeightQuote DP E X (bandWt δ (sk t δ k) (ek t δ k)) (Wk k) (XWk k))
    (hfaces : ∀ k < K, (fun n => (XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n) ≳ₙ
      (fun _ => (0 : ℝ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n - (v : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  have hsumFaces := asympGE_zero_finset_range_sum
    (fun k n => (XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n) K hfaces
  have hW := expect_weight_eq_sum_bands (P := P) hδ ht0 hgap K htK q Wk XWk qk hworld
  have hXW := expect_product_eq_sum_bands (P := P) hδ ht0 hgap K htK q Wk XWk qk hworld
  -- the residual sum is pointwise nonnegative
  have hres : ∀ n, 0 ≤ ∑ k ∈ Finset.range K, ((t k : ℝ) - v) * (Wk k n).expect P n := by
    intro n
    refine Finset.sum_nonneg (fun k _ => mul_nonneg ?_ (expect_nonneg (DP := DP) (Wk k n) n))
    have := grid_ge hδ hgap k
    rw [ht0] at this
    have : (v : ℝ) ≤ t k := by exact_mod_cast this
    linarith
  -- assemble
  have hEq : (fun n => (XW n).expect P n - (v : ℝ) * (W n).expect P n) ≈ₙ
      (fun n => (∑ k ∈ Finset.range K, ((XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n)) +
        ∑ k ∈ Finset.range K, ((t k : ℝ) - v) * (Wk k n).expect P n) := by
    have h1 := hXW.sub (hW.const_mul (v : ℝ))
    have h2 : (fun n => (∑ k ∈ Finset.range K, (XWk k n).expect P n) -
        (v : ℝ) * ∑ k ∈ Finset.range K, (Wk k n).expect P n) =
        (fun n => (∑ k ∈ Finset.range K, ((XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n)) +
          ∑ k ∈ Finset.range K, ((t k : ℝ) - v) * (Wk k n).expect P n) := by
      funext n
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [h2] at h1
    exact h1
  have hge : (fun _ => (0 : ℝ)) ≲ₙ
      (fun n => (∑ k ∈ Finset.range K, ((XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n)) +
        ∑ k ∈ Finset.range K, ((t k : ℝ) - v) * (Wk k n).expect P n) := by
    intro ε hε
    filter_upwards [hsumFaces ε hε] with n hn
    linarith [hres n]
  exact hge.trans_asympEq hEq.symm

/-! ### The below half: the mirrored grid -/

/-- The ramp is invariant under negating both arguments (it depends on their difference).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ctsInd_neg_neg (δ : ℚ) (a b : ℝ) : ctsInd δ (-a) (-b) = ctsInd δ b a := by
  unfold ctsInd
  congr 2
  ring

/-- **The band identity, downward**: for `t' + δ ≤ t`, the difference of two down-ramps at
`t > t'` is the product band `ctsInd δ t x · ctsInd δ x (t' − δ)`.
Source: [[reflection-in-li]] §It joins the circle ("The low side is symmetric")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_down_sub_eq_band {δ : ℚ} (hδ : 0 < δ) {t t' : ℝ} (hgap : t' + δ ≤ t) (x : ℝ) :
    ctsInd δ t x - ctsInd δ t' x = ctsInd δ t x * ctsInd δ x (t' - δ) := by
  have h := ctsInd_sub_ctsInd_eq_band hδ (t := -t) (t' := -t') (by linarith) (-x)
  rw [ctsInd_neg_neg, ctsInd_neg_neg] at h
  rw [h]
  congr 1
  rw [show -t' + (δ : ℝ) = -(t' - δ) by ring, ctsInd_neg_neg]

/-- The centre of the downward band `k`: `(t_k + t_{k+1} − δ)/2`.
Source: mandate T4 (the partition argument, low side)
Kind: D
Fidelity: n/a -/
def skD (t : ℕ → ℚ) (δ : ℚ) (k : ℕ) : ℚ := (t k + t (k + 1) - δ) / 2

/-- The half-width of the downward band `k`: `(t_k − t_{k+1} + δ)/2`.
Source: mandate T4 (the partition argument, low side)
Kind: D
Fidelity: n/a -/
def ekD (t : ℕ → ℚ) (δ : ℚ) (k : ℕ) : ℚ := (t k - t (k + 1) + δ) / 2

/-- The downward band's upper endpoint is `t_k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem skD_add_ekD (t : ℕ → ℚ) (δ : ℚ) (k : ℕ) : skD t δ k + ekD t δ k = t k := by
  simp [skD, ekD]; ring

/-- The downward band's half-width is positive on a grid descending by `≥ δ > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ekD_pos {t : ℕ → ℚ} {δ : ℚ} (hδ : 0 < δ) (hgap : ∀ k, t (k + 1) + δ ≤ t k) (k : ℕ) :
    0 < ekD t δ k := by
  simp only [ekD]
  linarith [hgap k]

/-- Downward band `k` is the bracket `ctsInd δ t_k x − ctsInd δ t_{k+1} x` of down-ramps.
Source: [[reflection-in-li]] §It joins the circle
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bandWt_grid_down {t : ℕ → ℚ} {δ : ℚ} (hδ : 0 < δ) (hgap : ∀ k, t (k + 1) + δ ≤ t k)
    (k : ℕ) (x : ℝ) :
    bandWt δ (skD t δ k) (ekD t δ k) x = ctsInd δ (t k) x - ctsInd δ (t (k + 1)) x := by
  have h1 : ((skD t δ k : ℚ) : ℝ) - ((ekD t δ k : ℚ) : ℝ) = (t (k + 1) : ℝ) - δ := by
    simp only [skD, ekD]; push_cast; ring
  have h2 : ((skD t δ k : ℚ) : ℝ) + ((ekD t δ k : ℚ) : ℝ) = (t k : ℝ) := by
    rw [← Rat.cast_add, skD_add_ekD]
  have hgap' : (t (k + 1) : ℝ) + δ ≤ t k := by exact_mod_cast hgap k
  simp only [bandWt]
  rw [h1, h2, ctsInd_down_sub_eq_band hδ hgap' x, mul_comm]

/-- The descending grid is dominated by its origin: `t_k ≤ t_0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem grid_le {t : ℕ → ℚ} {δ : ℚ} (hδ : 0 < δ) (hgap : ∀ k, t (k + 1) + δ ≤ t k) :
    ∀ k, t k ≤ t 0 := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih => linarith [hgap k]

/-- **The telescoping decomposition of the down-ramp**: on `[0, 1]` and a grid with `t_0 = v`,
descending by `≥ δ`, `t_K ≤ 0`, `∑_{k<K} bandWt δ (skD k) (ekD k) x = rampBelow δ v x`.
Source: [[reflection-in-li]] §It joins the circle
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem sum_bandWt_grid_down {t : ℕ → ℚ} {δ v : ℚ} (hδ : 0 < δ) (ht0 : t 0 = v)
    (hgap : ∀ k, t (k + 1) + δ ≤ t k) (K : ℕ) (htK : t K ≤ 0) {x : ℝ} (hx : 0 ≤ x) :
    ∑ k ∈ Finset.range K, bandWt δ (skD t δ k) (ekD t δ k) x = rampBelow δ v x := by
  simp_rw [bandWt_grid_down hδ hgap]
  rw [Finset.sum_range_sub' (fun k => ctsInd δ (t k) x) K]
  have hK : ctsInd δ (t K) x = 0 := by
    rw [ctsInd_eq_zero_iff hδ]
    have : (t K : ℝ) ≤ 0 := by exact_mod_cast htK
    linarith
  simp [hK, ht0, rampBelow]

/-! ### The two identities, for any weight that the bands partition -/

/-- **A weight quote is the sum of band weight quotes that partition its weight**, through
`E^H_n` (generic in the weight: the hypothesis `hsum` is the pointwise partition on `[0,1]`).
Source: [[reflection-in-li]] §It joins the circle
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expect_weight_eq_sum_bands_of_partition [IsLogicalInductor P DP] {E : Expert DP}
    {X W XW : ℕ → LUV} {wt : ℝ → ℝ} {δ : ℚ} (s e : ℕ → ℚ) (K : ℕ)
    (hsum : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∑ k ∈ Finset.range K, bandWt δ (s k) (e k) x = wt x)
    (q : WeightQuote DP E X wt W XW) (Wk XWk : ℕ → ℕ → LUV)
    (qk : ∀ k, WeightQuote DP E X (bandWt δ (s k) (e k)) (Wk k) (XWk k))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (W n).expect P n) ≈ₙ (fun n => ∑ k ∈ Finset.range K, (Wk k n).expect P n) := by
  have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp)
    (ts := (1, W) :: (List.range K).map (fun k => ((-1 : ℚ), Wk k)))
    (fun p hp => by
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
      rcases hp with rfl | ⟨k, -, rfl⟩
      · exact q.weight_codes
      · exact (qk k).weight_codes)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
      rcases hp with rfl | ⟨k, -, rfl⟩
      · exact fun n v hv => ⟨_, q.weight_reflected n v hv⟩
      · exact fun n v hv => ⟨_, (qk k).weight_reflected n v hv⟩))
    (0 : ℝ) (slack := fun _ => 0) tendsto_const_nhds
    (fun n w hw ν hν => by
      have hW := listComb_valuesAt_mem hν (p := (1, W)) (by simp)
      have hWk : ∀ k ∈ Finset.range K, ν (Wk k n) = bandWt δ (s k) (e k) (E.estimate X n) := by
        intro k hk
        have := listComb_valuesAt_mem hν (p := ((-1 : ℚ), Wk k))
          (by simp only [List.mem_cons, List.mem_map, List.mem_range]
              exact Or.inr ⟨k, Finset.mem_range.mp hk, rfl⟩)
        exact this.eq ((qk k).weight_reflected n w hw)
      rw [listComb_value]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      rw [list_sum_map_range, hW.eq (q.weight_reflected n w hw)]
      rw [Finset.sum_congr rfl (fun k hk => by rw [hWk k hk])]
      have hs := hsum (E.estimate X n) (E.estimate_mem_Icc X n).1 (E.estimate_mem_Icc X n).2
      simp only [Rat.cast_neg, Rat.cast_one, neg_one_mul, Finset.sum_neg_distrib, hs]
      simp)
    hworld
  have h' : (fun n => (W n).expect P n - ∑ k ∈ Finset.range K, (Wk k n).expect P n) ≈ₙ
      (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [listComb_expect, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      list_sum_map_range]
    simp [Finset.sum_neg_distrib, sub_eq_add_neg]
  exact asympEq_sub_zero_iff.mp h'

/-- **A product quote is the sum of band product quotes that partition its weight**, through
`E^H_n` (generic in the weight).
Source: [[reflection-in-li]] §It joins the circle
Kind: C
Fidelity: exact (within FAF's slacks)
Hyps: (a) -/
theorem expect_product_eq_sum_bands_of_partition [IsLogicalInductor P DP] {E : Expert DP}
    {X W XW : ℕ → LUV} {wt : ℝ → ℝ} {δ : ℚ} (s e : ℕ → ℚ) (K : ℕ)
    (hsum : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∑ k ∈ Finset.range K, bandWt δ (s k) (e k) x = wt x)
    (q : WeightQuote DP E X wt W XW) (Wk XWk : ℕ → ℕ → LUV)
    (qk : ∀ k, WeightQuote DP E X (bandWt δ (s k) (e k)) (Wk k) (XWk k))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n) ≈ₙ (fun n => ∑ k ∈ Finset.range K, (XWk k n).expect P n) := by
  have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp)
    (ts := (1, XW) :: (List.range K).map (fun k => ((-1 : ℚ), XWk k)))
    (fun p hp => by
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
      rcases hp with rfl | ⟨k, -, rfl⟩
      · exact q.product_codes
      · exact (qk k).product_codes)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
      rcases hp with rfl | ⟨k, -, rfl⟩
      · exact (weightQuote_product_valued q)
      · exact (weightQuote_product_valued (qk k))))
    (0 : ℝ) (slack := fun n => q.slack n + ∑ k ∈ Finset.range K, (qk k).slack n)
    (by
      have := q.slack_tendsto.add (tendsto_finsetSum (Finset.range K)
        (fun k _ => (qk k).slack_tendsto))
      simpa using this)
    (fun n w hw ν hν => by
      obtain ⟨x, hx⟩ := q.source_valued n w hw
      obtain ⟨z, hz, hzx⟩ := q.product_reflected n w hw x hx
      have hXW := listComb_valuesAt_mem hν (p := (1, XW)) (by simp)
      have hk : ∀ k ∈ Finset.range K, |ν (XWk k n) -
          x * bandWt δ (s k) (e k) (E.estimate X n)| ≤ (qk k).slack n := by
        intro k hk
        obtain ⟨zk, hzk, hzkx⟩ := (qk k).product_reflected n w hw x hx
        have := listComb_valuesAt_mem hν (p := ((-1 : ℚ), XWk k))
          (by simp only [List.mem_cons, List.mem_map, List.mem_range]
              exact Or.inr ⟨k, Finset.mem_range.mp hk, rfl⟩)
        rw [this.eq hzk]
        exact hzkx
      rw [listComb_value]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
      rw [list_sum_map_range, hXW.eq hz]
      have hs := hsum (E.estimate X n) (E.estimate_mem_Icc X n).1 (E.estimate_mem_Icc X n).2
      have hlow := Finset.sum_le_sum (fun k hmem => (abs_le.mp (hk k hmem)).1)
      have hup := Finset.sum_le_sum (fun k hmem => (abs_le.mp (hk k hmem)).2)
      rw [Finset.sum_neg_distrib] at hlow
      have hS : ∑ k ∈ Finset.range K, (ν (XWk k n) - x * bandWt δ (s k) (e k) (E.estimate X n)) =
          ∑ k ∈ Finset.range K, ν (XWk k n) -
            x * ∑ k ∈ Finset.range K, bandWt δ (s k) (e k) (E.estimate X n) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hs] at hS
      rw [abs_le] at hzx ⊢
      simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_zero, neg_one_mul, Finset.sum_neg_distrib,
        one_mul, zero_add, sub_zero]
      constructor <;> linarith [hzx.1, hzx.2, hlow, hup, hS])
    hworld
  have h' : (fun n => (XW n).expect P n - ∑ k ∈ Finset.range K, (XWk k n).expect P n) ≈ₙ
      (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [listComb_expect, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      list_sum_map_range]
    simp [Finset.sum_neg_distrib, sub_eq_add_neg]
  exact asympEq_sub_zero_iff.mp h'

/-- A `Finset.range` sum of sequences each `≲ₙ 0` is `≲ₙ 0`.
Source: none: infrastructure (FAF `AsympLE.add`)
Kind: L
Fidelity: n/a -/
theorem asympLE_zero_finset_range_sum (f : ℕ → ℕ → ℝ) (K : ℕ)
    (h : ∀ k < K, f k ≲ₙ (fun _ => (0 : ℝ))) :
    (fun n => ∑ k ∈ Finset.range K, f k n) ≲ₙ (fun _ => (0 : ℝ)) := by
  induction K with
  | zero => simpa using AsympEq.asympLE (AsympEq.refl (fun _ => (0 : ℝ)))
  | succ K ih =>
    have := AsympLE.add (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))) (h K (Nat.lt_succ_self K))
    simp only [Finset.sum_range_succ]
    intro ε hε
    filter_upwards [this ε hε] with n hn
    simpa using hn

/-- **Band faces ⟹ soft Total Trust below, per instance (the partition argument, low
side)**: on a grid `v = t_0 > ⋯ > t_K` descending by `≥ δ` with `t_K ≤ 0`, the `K` band
packages' upper faces (at `t_k = skD + ekD ≤ v`), taken as hypotheses, sum to
`E^H_n(XW_n) − v·E^H_n(W_n) ≲ₙ 0`. Faces, not the predicate: see
`softAbove_instance_of_bandFaces`.
Source: [[reflection-in-li]] §It joins the circle ("The low side is symmetric"); vq-wiki-006
Kind: C
Fidelity: exact (faces as hypotheses)
Hyps: (a) the packages (data) and the `K` band faces `hfaces`; `hworld` -/
theorem softBelow_instance_of_bandFaces [IsLogicalInductor P DP] {E : Expert DP}
    {X W XW : ℕ → LUV}
    {t : ℕ → ℚ} {δ v : ℚ} (hδ : 0 < δ) (ht0 : t 0 = v) (hgap : ∀ k, t (k + 1) + δ ≤ t k)
    (K : ℕ) (htK : t K ≤ 0) (q : WeightQuote DP E X (rampBelow δ v) W XW)
    (Wk XWk : ℕ → ℕ → LUV)
    (qk : ∀ k, WeightQuote DP E X (bandWt δ (skD t δ k) (ekD t δ k)) (Wk k) (XWk k))
    (hfaces : ∀ k < K, (fun n => (XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n) ≲ₙ
      (fun _ => (0 : ℝ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n - (v : ℝ) * (W n).expect P n) ≲ₙ (fun _ => (0 : ℝ)) := by
  have hsumFaces := asympLE_zero_finset_range_sum
    (fun k n => (XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n) K hfaces
  have hpart : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ∑ k ∈ Finset.range K, bandWt δ (skD t δ k) (ekD t δ k) x = rampBelow δ v x :=
    fun x hx _ => sum_bandWt_grid_down hδ ht0 hgap K htK hx
  have hW := expect_weight_eq_sum_bands_of_partition (P := P) _ _ K hpart q Wk XWk qk hworld
  have hXW := expect_product_eq_sum_bands_of_partition (P := P) _ _ K hpart q Wk XWk qk hworld
  have hres : ∀ n, ∑ k ∈ Finset.range K, ((t k : ℝ) - v) * (Wk k n).expect P n ≤ 0 := by
    intro n
    refine Finset.sum_nonpos (fun k _ => mul_nonpos_of_nonpos_of_nonneg ?_
      (expect_nonneg (DP := DP) (Wk k n) n))
    have := grid_le hδ hgap k
    rw [ht0] at this
    have : (t k : ℝ) ≤ v := by exact_mod_cast this
    linarith
  have hEq : (fun n => (XW n).expect P n - (v : ℝ) * (W n).expect P n) ≈ₙ
      (fun n => (∑ k ∈ Finset.range K, ((XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n)) +
        ∑ k ∈ Finset.range K, ((t k : ℝ) - v) * (Wk k n).expect P n) := by
    have h1 := hXW.sub (hW.const_mul (v : ℝ))
    have h2 : (fun n => (∑ k ∈ Finset.range K, (XWk k n).expect P n) -
        (v : ℝ) * ∑ k ∈ Finset.range K, (Wk k n).expect P n) =
        (fun n => (∑ k ∈ Finset.range K, ((XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n)) +
          ∑ k ∈ Finset.range K, ((t k : ℝ) - v) * (Wk k n).expect P n) := by
      funext n
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [h2] at h1
    exact h1
  have hle : (fun n => (∑ k ∈ Finset.range K, ((XWk k n).expect P n - (t k : ℝ) * (Wk k n).expect P n)) +
        ∑ k ∈ Finset.range K, ((t k : ℝ) - v) * (Wk k n).expect P n) ≲ₙ (fun _ => (0 : ℝ)) := by
    intro ε hε
    filter_upwards [hsumFaces ε hε] with n hn
    linarith [hres n]
  exact hEq.trans_asympLE hle

/-! ### Predicate level: the canonical grids and the square -/

/-- **Band quotes available** for every source at every band (positive width and half-width):
the existence clause of the partition argument. `(c)` for a general expert
(`li-quote-lane`); the self-expert's band quotes are `Construction/Quotation` work not done
here (def-lattice audit N2: only the above-ramp package is shown inhabited).
Source: [[reflection-in-li]] §It joins the circle; mandate T4
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def BandQuotesAvailable (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ X : ℕ → LUV, LUV.MachineThresholdCodeSeq X → ∀ s ε δ : ℚ, 0 < ε → 0 < δ →
    ∃ W XW : ℕ → LUV, Nonempty (WeightQuote DP E X (bandWt δ s ε) W XW)

/-- The upward canonical grid `t_k = v + kδ` reaches `1` after `⌈(1 − v)/δ⌉` steps.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem canonical_grid_up {v δ : ℚ} (hδ : 0 < δ) :
    1 ≤ v + (Nat.ceil ((1 - v) / δ) : ℚ) * δ := by
  have h := Nat.le_ceil ((1 - v) / δ)
  rw [div_le_iff₀ hδ] at h
  linarith

/-- The downward canonical grid `t_k = v − kδ` reaches `0` after `⌈v/δ⌉` steps.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem canonical_grid_down {v δ : ℚ} (hδ : 0 < δ) :
    v - (Nat.ceil (v / δ) : ℚ) * δ ≤ 0 := by
  have h := Nat.le_ceil (v / δ)
  rw [div_le_iff₀ hδ] at h
  linarith

/-- **Band Reflection within a width ratio**: def-lattice's `BandReflection` restricted to
bands whose half-width is at most `c` times the ramp width (`ε ≤ c·δ`). def-lattice's
predicate quantifies over every half-width, and a band of half-width `ε ≥ (1 + δ − v)/2`
centred at `v + ε` *is* the up-ramp at `v` on `[0,1]`, so the unbounded predicate contains
every soft Total-Trust face as a wide-band instance (`WideBand.lean`, F12). Under `ε ≤ c·δ` no
band is the ramp at any `v < 1 − 2cδ` (`bandWt_ne_rampAbove_of_narrow`), and the partition
argument is what carries the narrow faces to the ramp. `c ≥ 1` is what the canonical grids
need (bands of half-width exactly `δ`); the wiki's `ε > δ` for the normalized reading is any
`c > 1`. `BandReflection` implies it for every `c` (`bandReflectionWithin_of_bandReflection`).
Source: [[reflection-in-li]] §It joins the circle (narrow bands); audit r1 fidelity B1
Kind: D
Fidelity: variant: def-lattice's `BandReflection` with the half-width bounded by `c·δ` -/
def BandReflectionWithin (P : History) (DP : DeductiveProcess) (E : Expert DP) (c : ℚ) :
    Prop :=
  ∀ s ε δ : ℚ, 0 < ε → ε ≤ c * δ → 0 < δ →
    ThresholdIneqAbove P DP E (bandWt δ s ε) (s - ε) ∧
      ThresholdIneqBelow P DP E (bandWt δ s ε) (s + ε)

/-- The unbounded predicate implies the narrow one at every ratio.
Source: none: infrastructure
Kind: L
Fidelity: exact -/
theorem bandReflectionWithin_of_bandReflection {E : Expert DP} (hB : BandReflection P DP E)
    (c : ℚ) : BandReflectionWithin P DP E c :=
  fun s ε δ hε _ hδ => hB s ε δ hε hδ

/-- On the canonical upward grid `t_k = v + kδ` every band has half-width exactly `δ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ek_canonical (v δ : ℚ) (k : ℕ) : ek (fun k => v + k * δ) δ k = δ := by
  simp only [ek]; push_cast; ring

/-- On the canonical downward grid `t_k = v − kδ` every band has half-width exactly `δ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ekD_canonical (v δ : ℚ) (k : ℕ) : ekD (fun k => v - k * δ) δ k = δ := by
  simp only [ekD]; push_cast; ring

/-- **Narrow band Reflection ⟹ soft Total Trust, above half** (predicate level): with band
quotes available, on the canonical grid `t_k = v + kδ` (bands of half-width `δ ≤ c·δ`), the
partition argument from the faces `BandReflectionWithin` supplies.
Source: [[reflection-in-li]] §It joins the circle; vq-wiki-006
Kind: L
Fidelity: exact (narrow bands, `c ≥ 1`)
Hyps: (c) `BandQuotesAvailable` (existence); `BandReflectionWithin c` is the deference
hypothesis; `hworld` -/
theorem softTotalTrustAbove_of_bandReflectionWithin [IsLogicalInductor P DP] {E : Expert DP}
    {c : ℚ} (hc : 1 ≤ c) (hB : BandReflectionWithin P DP E c) (hq : BandQuotesAvailable DP E)
    {v δ : ℚ} (hδ : 0 < δ) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    SoftTotalTrustAbove P DP E v δ := by
  intro X W XW hX q
  let t : ℕ → ℚ := fun k => v + k * δ
  have hgap : ∀ k, t k + δ ≤ t (k + 1) := fun k => by simp only [t]; push_cast; linarith
  have hchoice : ∀ k, ∃ W XW : ℕ → LUV,
      Nonempty (WeightQuote DP E X (bandWt δ (sk t δ k) (ek t δ k)) W XW) :=
    fun k => hq X hX (sk t δ k) (ek t δ k) δ (ek_pos hδ hgap k) hδ
  choose Wk XWk hqk using hchoice
  refine softAbove_instance_of_bandFaces hδ (by simp [t]) hgap (Nat.ceil ((1 - v) / δ))
    (canonical_grid_up hδ) q Wk XWk (fun k => Classical.choice (hqk k)) (fun k _ => ?_) hworld
  have hek : ek t δ k ≤ c * δ := by
    rw [show ek t δ k = δ from ek_canonical v δ k]
    exact le_mul_of_one_le_left hδ.le hc
  have := (hB (sk t δ k) (ek t δ k) δ (ek_pos hδ hgap k) hek hδ).1 X (Wk k) (XWk k) hX
    (Classical.choice (hqk k))
  rwa [sk_sub_ek] at this

/-- **Narrow band Reflection ⟹ soft Total Trust, below half** (predicate level): on the
canonical descending grid `t_k = v − kδ`.
Source: [[reflection-in-li]] §It joins the circle
Kind: L
Fidelity: exact (narrow bands, `c ≥ 1`)
Hyps: as `softTotalTrustAbove_of_bandReflectionWithin` -/
theorem softTotalTrustBelow_of_bandReflectionWithin [IsLogicalInductor P DP] {E : Expert DP}
    {c : ℚ} (hc : 1 ≤ c) (hB : BandReflectionWithin P DP E c) (hq : BandQuotesAvailable DP E)
    {v δ : ℚ} (hδ : 0 < δ) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    SoftTotalTrustBelow P DP E v δ := by
  intro X W XW hX q
  let t : ℕ → ℚ := fun k => v - k * δ
  have hgap : ∀ k, t (k + 1) + δ ≤ t k := fun k => by simp only [t]; push_cast; linarith
  have hchoice : ∀ k, ∃ W XW : ℕ → LUV,
      Nonempty (WeightQuote DP E X (bandWt δ (skD t δ k) (ekD t δ k)) W XW) :=
    fun k => hq X hX (skD t δ k) (ekD t δ k) δ (ekD_pos hδ hgap k) hδ
  choose Wk XWk hqk using hchoice
  refine softBelow_instance_of_bandFaces hδ (by simp [t]) hgap (Nat.ceil (v / δ))
    (canonical_grid_down hδ) q Wk XWk (fun k => Classical.choice (hqk k)) (fun k _ => ?_) hworld
  have hek : ekD t δ k ≤ c * δ := by
    rw [show ekD t δ k = δ from ekD_canonical v δ k]
    exact le_mul_of_one_le_left hδ.le hc
  have := (hB (skD t δ k) (ekD t δ k) δ (ekD_pos hδ hgap k) hek hδ).2 X (Wk k) (XWk k) hX
    (Classical.choice (hqk k))
  rwa [skD_add_ekD] at this

/-- **Narrow band Reflection ⟹ Total Trust** (predicate level): both halves at every
threshold and width, from bands of half-width `≤ c·δ` only. This is the content of
[[reflection-in-li]]'s partition argument; over def-lattice's unbounded predicate the arrow
is free (`totalTrust_of_bandReflection`, `WideBand.lean`, F12).
Source: [[reflection-in-li]] §It joins the circle ("Hence soft value-Reflection ⟺ TT")
Kind: L
Fidelity: exact (narrow bands, `c ≥ 1`)
Hyps: (c) `BandQuotesAvailable`; `BandReflectionWithin c`; `hworld` -/
theorem totalTrust_of_bandReflectionWithin [IsLogicalInductor P DP] {E : Expert DP}
    {c : ℚ} (hc : 1 ≤ c) (hB : BandReflectionWithin P DP E c) (hq : BandQuotesAvailable DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TotalTrust P DP E :=
  fun _ _ hδ => ⟨softTotalTrustAbove_of_bandReflectionWithin hc hB hq hδ hworld,
    softTotalTrustBelow_of_bandReflectionWithin hc hB hq hδ hworld⟩

/-- **The square `BandReflectionWithin ⟺ TotalTrust`, on the quotes**: `→` is the partition
argument (band quotes available; bands of half-width `≤ c·δ`, `c ≥ 1`); `←` runs the loop —
Total Trust ⟹ Tower on valued sources by gap-bets (T5: gap packages and the expert's gap
pins) ⟹ band Reflection at every band (T4b: product quotes and folds at every band) ⟹ its
narrow restriction. Every existence clause is visible in the hypotheses; none is discharged
for a general expert. The square over the unbounded predicate is
`bandReflection_iff_totalTrust_onQuotes` (`WideBand.lean`), whose `→` needs no clause.
Source: [[reflection-in-li]] §It joins the circle (the four-face square); mandate T4
Kind: L
Fidelity: exact (modulo the disclosed clauses; narrow bands)
Hyps: (c) `BandQuotesAvailable`, `GapPackagesAvailable`, band `ProductQuotesAvailable`
(existence); `ExpertPinsGaps`, band `ExpertFoldsAt` ((b) self / (c) general); `hworld` -/
theorem bandReflectionWithin_iff_totalTrust_onQuotes [IsLogicalInductor P DP] {E : Expert DP}
    {c : ℚ} (hc : 1 ≤ c)
    (hbands : BandQuotesAvailable DP E) (hg : GapPackagesAvailable DP E)
    (hp : ExpertPinsGaps DP E)
    (hq : ∀ s ε δ : ℚ, 0 < ε → 0 < δ → ProductQuotesAvailable DP E (bandWt δ s ε))
    (hf : ∀ s ε δ : ℚ, 0 < ε → 0 < δ → ExpertFoldsAt DP E (bandWt δ s ε))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    BandReflectionWithin P DP E c ↔ TotalTrust P DP E :=
  ⟨fun hB => totalTrust_of_bandReflectionWithin hc hB hbands hworld,
    fun hT => bandReflectionWithin_of_bandReflection
      (bandReflection_of_towerValued (towerValued_of_softTotalTrust_gapBets hT hg hp hworld)
        hq hf hworld) c⟩

end

end Cleanroom.Deference.DefLatticeArrows
