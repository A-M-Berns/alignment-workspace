import Cleanroom.Bli.BliWitnessLia.Prior

/-!
# `bli-witness-lia` · Horizon2: U15 at horizon two over the segment (T9, `extension`)

`sistSkel (segmentSkeleton H K hK) n 1 (linkedTable n) coin₂ c V r₀ Qh` — the SIST mugging whose
states are day-`(n+2)` tables, two steps after the base's realized day-`n` table. The branch
masses are now genuine two-step `trajLaw` sums (`stateMass_sistSkel_h1`, proved here for every
skeleton: `μ(T) = ∑_{Q₁} κ_n(t)(Q₁) · κ_{n+1}(Q₁)(T)`): the day-`(n+1)` step is the two-point law
on the two slice marginals (`segmentSkeleton_law_linked`), and the day-`(n+2)` step at each slice
marginal is the **tent** (`segmentSkeleton_law_tent`: the segment kernel is the tent at every
table other than the linked one, and a slice marginal is never the linked table,
`Uncharged.linkedTable_succ_ne_sliceT/F`). So

`μ(T) = ½ · tentLaw (sliceT n) T + ½ · tentLaw (sliceF n) T` (`stateMass₂_eq`).

**What the tent does at the coin.** The slice marginals are *certain* about the coin (`1` and
`0`), and the one-coordinate tent at a price exactly `1` (resp. `0`) is the point mass at `1`
(resp. `0`) — `tent1_one`, `tent1_zero`, read off `tent1`'s definition (its three weights are
`max 0 (1 − 2x)`, `1 − |2x − 1|`, `max 0 (2x − 1)`). By the product-grid coordinate lemma
(`sum_piFinset_coord`, no counting of tables), the Ask class (coin `1`) collects exactly the
`sliceT` branch and the Rec class (coin `0`) exactly the `sliceF` branch: `μ(Ask) = μ(Rec) = 1/2`,
`μ(Other) = 0` (`classMass_ask₂`, `classMass_rec₂`, `classMass_other₂`), and the verdict is
unchanged, `(V − c)/2` (`verdict₂`). This is the first `h ≥ 1` instance of U15 in the run: the
recursion of `trajLaw` does work (the state masses are sums over the intermediate day-`(n+1)`
table), the classes do not move, because the coin, once decided by the kernel, stays decided
under the tent.

The observed table of record is `askTable₂`: the true-slice marginal `sliceT n` read on the
day-`(n+2)` sentences with the new sentences at `1` — an Ask table (`askC_askTable₂`) **of
positive mass** (`stateMass₂_askTable₂_pos`, through `tentLaw_pos_iff`: it lies on the product
face over `sliceT n`), so the updateful rule's refusal is stated at a charged table, as at horizon
one. The verdict at *any* Ask table is `verdict₂` (its `askC Qh` hypothesis is the honest
"at an Ask table" of `verdict_sistSkel`); the table of record instantiates it.

The infinite base of the plan entry for this target ("if `bli-exact-base` lands M4") does not
apply: M4 is OPEN there (`worldMarket_exists`, `bundleMarket_LI_exists`, `weakening_exists`);
nothing here is built on it.

Sources: mandate T9; [[bli-program]] §3.9 U15; `bli-finite`'s `Tent`; udt-bli-sist T8
(`stateMass_sistSkel`, `sum_piFinset_coord`).
-/

namespace Cleanroom.Bli.BliWitnessLia

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Skel
open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist

noncomputable section

/-! ## The two-step state mass, for every skeleton -/

/-- **At horizon two the branch masses are two-step `trajLaw` sums**:
`stateMass T = ∑_{Q₁ ∈ grid (n+1)} κ_n(t)(Q₁) · κ_{n+1}(Q₁)(T)` — the recursion of `trajLaw`
doing work (udt-bli-sist's `stateMass_sistSkel_h0` is the horizon-one case).
Source: mandate T9 ("the masses are now sums of two-step `trajLaw` products"); udt-bli-sist T8
Kind: L
Fidelity: exact -/
theorem stateMass_sistSkel_h1 {𝒮 : SmallIndex} {d : ℕ → ℕ} (sk : Skeleton 𝒮 d) (n : ℕ)
    (t : Table 𝒮 n) (coin : ↥(𝒮.S (n + 1 + 1))) (c V : ℚ) (r₀ : Bool → ℚ)
    (Qh : ↥(grid 𝒮 d (n + 1 + 1))) (T : ↥(grid 𝒮 d (n + 1 + 1))) :
    (sistSkel sk n 1 t coin c V r₀ Qh).stateMass T =
      ∑ Q₁ ∈ grid 𝒮 d (n + 1), (sk.κ n).law t Q₁ * (sk.κ (n + 1)).law Q₁ T.1 := by
  rw [stateMass_sistSkel, sum_trajGrid_succ, sum_trajGrid_succ, sum_trajGrid_zero]
  refine Finset.sum_congr rfl fun Q₁ _ => ?_
  simp only [lastOf, trajLaw_succ, trajLaw_zero, Traj.last_zero, one_mul, Nat.add_zero]
  rw [Finset.sum_ite_eq' (grid 𝒮 d (n + 1 + 1)) T.1, if_pos T.2]
  rfl

/-! ## The tent at a certain coordinate is a point mass -/

/-- The one-coordinate tent at price `0` is the point mass at `0`.
Source: `bli-finite`'s `tent1` (its weights at `x = 0` are `1, 0, 0`)
Kind: L
Fidelity: n/a -/
lemma tent1_zero (d : ℕ) (v : ℚ) : tent1 d 0 v = if v = 0 then 1 else 0 := by
  unfold tent1
  rw [clamp01_eq_self ⟨le_rfl, by norm_num⟩, max_eq_right (by norm_num : (0 : ℚ) ≤ 1 - 2 * 0),
    max_eq_left (by norm_num : 2 * (0 : ℚ) - 1 ≤ 0)]
  norm_num

/-- The one-coordinate tent at price `1` is the point mass at `1`.
Source: `bli-finite`'s `tent1` (its weights at `x = 1` are `0, 0, 1`)
Kind: L
Fidelity: n/a -/
lemma tent1_one (d : ℕ) (v : ℚ) : tent1 d 1 v = if v = 1 then 1 else 0 := by
  unfold tent1
  rw [clamp01_eq_self ⟨by norm_num, le_rfl⟩, max_eq_left (by norm_num : 1 - 2 * (1 : ℚ) ≤ 0),
    max_eq_right (by norm_num : (0 : ℚ) ≤ 2 * 1 - 1)]
  norm_num

/-! ## The segment skeleton off the linked table -/

/-- **The segment kernel is the tent at every table other than the linked one** (on every day:
`segKernel` on segment days, `tentKernel` after).
Source: `bli-exact-base`'s `Skel.segKernel`/`segmentSkeleton` (definitions); mandate T9
Kind: L
Fidelity: n/a -/
lemma segmentSkeleton_law_tent {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {m : ℕ}
    {Q : Table smallIndex m} (hne : Q ≠ linkedTable m) :
    ((segmentSkeleton H K hK).κ m).law Q = tentLaw (Bli.segmentMesh K) m Q := by
  show ((if hm : m < H then _ else _ : BliFinite.Kernel smallIndex _ m)).law Q = _
  by_cases hm : m < H
  · rw [dif_pos hm]
    show (if Q = linkedTable m then _ else _) = _
    rw [if_neg hne]
  · rw [dif_neg hm]
    rfl

/-! ## The horizon-two prior -/

/-- **The coin at horizon two**: `freshCoord` as a day-`(n+2)` small sentence.
Source: mandate T9 (`coin₂`)
Kind: D
Fidelity: exact -/
def coinAt₂ (n : ℕ) (h1 : 1 ≤ n) : ↥(smallIndex.S (n + 1 + 1)) :=
  ⟨freshCoord, show freshCoord ∈ smallIndex.S (n + 1 + 1) from
    freshCoord_mem_smallSet (by omega)⟩

/-- The coin's sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma coinAt₂_val (n : ℕ) (h1 : 1 ≤ n) : (coinAt₂ n h1).1 = freshCoord := rfl

/-- **The SIST mugging prior over the linked splice at horizon two**: `sistSkel` at
`segmentSkeleton`, base table the base's realized day-`n` table, coin `freshCoord`, states the
day-`(n+2)` grid tables, observed table `Qh` (the table of record is `askTable₂`).
Source: [[bli-program]] §3.9 U15; mandate T9
Kind: D
Fidelity: exact -/
abbrev segmentSist₂ (H K : ℕ) (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) (n : ℕ) (h2 : 2 ≤ n)
    (c V : ℚ) (r₀ : Bool → ℚ) (Qh : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1))) :
    FiniteBLIPrior smallIndex (n + 1 + 1) (grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1)) Bool :=
  sistSkel (segmentSkeleton H K hK) n 1 (linkedTable n) (coinAt₂ n (by omega)) c V r₀ Qh

section H2

/-- **The horizon-two branch masses over the segment**: step one the two-point law at the linked
table, step two the tent at each slice marginal —
`μ(T) = ½ · tentLaw (sliceT n) T + ½ · tentLaw (sliceF n) T`. Derived from the kernel, never
typed.
Source: mandate T9; [[bli-program]] §3.9 U15 ("`μ` is `trajLaw`")
Kind: C (`stateMass_sistSkel_h1` + `segmentSkeleton_law_linked` + `segmentSkeleton_law_tent`)
Fidelity: exact
Hyps: (a) -/
theorem stateMass₂_eq {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
    (c V : ℚ) (r₀ : Bool → ℚ) (Qh : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1)))
    (T : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1))) :
    (segmentSist₂ H K hK n h2 c V r₀ Qh).stateMass T =
      1 / 2 * tentLaw (Bli.segmentMesh K) (n + 1) (sliceT n) T.1 +
      1 / 2 * tentLaw (Bli.segmentMesh K) (n + 1) (sliceF n) T.1 := by
  have hT := sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 1 0 1 True
  have hF := sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 0 0 1 False
  rw [stateMass_sistSkel_h1, segmentSkeleton_law_linked hK hn]
  unfold twoPointLaw
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', if_pos hT,
    if_pos hF]
  rw [segmentSkeleton_law_tent hK (Uncharged.linkedTable_succ_ne_sliceT (n := n) (by omega)).symm,
    segmentSkeleton_law_tent hK (Uncharged.linkedTable_succ_ne_sliceF (n := n) (by omega)).symm]

/-- The tent at the true-slice marginal is the point mass at `1` on the coin coordinate.
Source: mandate T9 ("what is the tent's law at a coordinate priced exactly `1`? … a point mass")
Kind: L
Fidelity: n/a -/
lemma tentCoord_sliceT_coin {K n : ℕ} (h2 : 2 ≤ n) (v : ℚ) :
    tentCoord (Bli.segmentMesh K) (n + 1) (sliceT n) (coinAt₂ n (by omega)) v =
      if v = 1 then 1 else 0 := by
  have hf : freshCoord ∈ smallIndex.S (n + 1) := freshCoord_mem_smallSet (by omega)
  show (if h : freshCoord ∈ smallIndex.S (n + 1) then
      tent1 ((Bli.segmentMesh K).d (n + 1 + 1)) (sliceT n ⟨freshCoord, h⟩) v
    else uniform1 ((Bli.segmentMesh K).d (n + 1 + 1)) v) = _
  rw [dif_pos hf, show sliceT n ⟨freshCoord, hf⟩ = 1 from
    (sliceTable_fresh n 1 0 1 True hf).trans (by simp)]
  exact tent1_one _ _

/-- The tent at the false-slice marginal is the point mass at `0` on the coin coordinate.
Source: mandate T9
Kind: L
Fidelity: n/a -/
lemma tentCoord_sliceF_coin {K n : ℕ} (h2 : 2 ≤ n) (v : ℚ) :
    tentCoord (Bli.segmentMesh K) (n + 1) (sliceF n) (coinAt₂ n (by omega)) v =
      if v = 0 then 1 else 0 := by
  have hf : freshCoord ∈ smallIndex.S (n + 1) := freshCoord_mem_smallSet (by omega)
  show (if h : freshCoord ∈ smallIndex.S (n + 1) then
      tent1 ((Bli.segmentMesh K).d (n + 1 + 1)) (sliceF n ⟨freshCoord, h⟩) v
    else uniform1 ((Bli.segmentMesh K).d (n + 1 + 1)) v) = _
  rw [dif_pos hf, show sliceF n ⟨freshCoord, hf⟩ = 0 from
    (sliceTable_fresh n 0 0 1 False hf).trans (by simp)]
  exact tent1_zero _ _

/-- **The coin-class mass of a tent branch** is the tent's one-coordinate law at the coin —
by the product-grid coordinate lemma, not by counting.
Source: udt-bli-sist T8 (`sum_grid_coin_tentLaw`, the template); mandate T9
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem sum_grid_coin_tentLaw₂ {K n : ℕ} (h2 : 2 ≤ n) (t : Table smallIndex (n + 1)) (v : ℚ)
    (hv : v ∈ gridVals ((Bli.segmentMesh K).d (n + 1 + 1))) :
    (∑ Q ∈ grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1),
      if Q (coinAt₂ n (by omega)) = v then tentLaw (Bli.segmentMesh K) (n + 1) t Q else 0) =
    tentCoord (Bli.segmentMesh K) (n + 1) t (coinAt₂ n (by omega)) v := by
  change (∑ Q ∈ Fintype.piFinset
      (fun _ : ↥(smallIndex.S (n + 1 + 1)) => gridVals ((Bli.segmentMesh K).d (n + 1 + 1))),
    if Q (coinAt₂ n (by omega)) = v then
      ∏ φ, tentCoord (Bli.segmentMesh K) (n + 1) t φ (Q φ) else 0) = _
  rw [sum_piFinset_coord (gridVals ((Bli.segmentMesh K).d (n + 1 + 1)))
    (fun φ u => tentCoord (Bli.segmentMesh K) (n + 1) t φ u) (coinAt₂ n (by omega)) v hv]
  have hone : ∏ i ∈ univ.erase (coinAt₂ n (by omega)),
      ∑ u ∈ gridVals ((Bli.segmentMesh K).d (n + 1 + 1)),
        tentCoord (Bli.segmentMesh K) (n + 1) t i u = 1 :=
    Finset.prod_eq_one (fun φ _ => tentCoord_sum_one (𝓜 := Bli.segmentMesh K) t φ)
  rw [hone, mul_one]

/-- Splitting a half-half mixture under an indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_ite_half {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] (f g : α → ℚ) :
    (∑ x ∈ s, if p x then 1 / 2 * f x + 1 / 2 * g x else 0) =
      1 / 2 * (∑ x ∈ s, if p x then f x else 0) + 1 / 2 * (∑ x ∈ s, if p x then g x else 0) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- **The mass of a coin class at horizon two**: `½·[v = 1] + ½·[v = 0]` — the `sliceT` branch
puts all its mass on coin `1`, the `sliceF` branch on coin `0`.
Source: mandate T9; udt-bli-sist T8 (`classMass_coin`, the template)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem classMass_coin₂ {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
    (c V : ℚ) (r₀ : Bool → ℚ) (Qh : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1))) (v : ℚ) (hv : v ∈ gridVals ((Bli.segmentMesh K).d (n + 1 + 1))) :
    classMass (segmentSist₂ H K hK n h2 c V r₀ Qh)
      (univ.filter (fun T : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1)) =>
        T.1 (coinAt₂ n (by omega)) = v)) =
      1 / 2 * (if v = 1 then 1 else 0) + 1 / 2 * (if v = 0 then 1 else 0) := by
  unfold classMass
  simp only [stateMass₂_eq hK hn h2 c V r₀ Qh]
  rw [Finset.sum_filter, Finset.sum_coe_sort (grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1))
    (fun Q => if Q (coinAt₂ n (by omega)) = v then
      1 / 2 * tentLaw (Bli.segmentMesh K) (n + 1) (sliceT n) Q +
      1 / 2 * tentLaw (Bli.segmentMesh K) (n + 1) (sliceF n) Q else 0)]
  rw [sum_ite_half, sum_grid_coin_tentLaw₂ h2 _ v hv, sum_grid_coin_tentLaw₂ h2 _ v hv,
    tentCoord_sliceT_coin h2, tentCoord_sliceF_coin h2]

/-- **`μ(Ask) = 1/2` at horizon two.**
Source: mandate T9
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem classMass_ask₂ {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
    (c V : ℚ) (r₀ : Bool → ℚ) (Qh : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1))) :
    classMass (segmentSist₂ H K hK n h2 c V r₀ Qh) (univ.filter (askC n 1 (coinAt₂ n (by omega)))) =
      1 / 2 := by
  have h := classMass_coin₂ hK hn h2 c V r₀ Qh 1 (one_mem_gridVals ((Bli.segmentMesh K).d_pos _))
  norm_num at h
  exact h

/-- **`μ(Rec ∖ Ask) = 1/2` at horizon two.**
Source: mandate T9
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem classMass_rec₂ {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
    (c V : ℚ) (r₀ : Bool → ℚ) (Qh : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1))) :
    classMass (segmentSist₂ H K hK n h2 c V r₀ Qh)
      (univ.filter (fun T => ¬ askC n 1 (coinAt₂ n (by omega)) T ∧
        recC n 1 (coinAt₂ n (by omega)) T)) = 1 / 2 := by
  have e : (univ.filter (fun T : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1)) =>
      ¬ askC n 1 (coinAt₂ n (by omega)) T ∧ recC n 1 (coinAt₂ n (by omega)) T)) =
      univ.filter (fun T => T.1 (coinAt₂ n (by omega)) = 0) := by
    apply Finset.filter_congr
    intro T _
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      refine ⟨?_, h⟩
      unfold askC
      rw [h]; norm_num
  rw [e]
  have h := classMass_coin₂ hK hn h2 c V r₀ Qh 0 (zero_mem_gridVals _)
  norm_num at h
  exact h

/-- **`μ(Other) = 0` at horizon two**: by `E5` (`sum_stateMass`) minus the two classes — the
coin, once decided by the kernel, stays decided under the tent, so the residual class is still
empty of mass.
Source: mandate T9, § 3.3
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem classMass_other₂ {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
    (c V : ℚ) (r₀ : Bool → ℚ) (Qh : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1))) :
    classMass (segmentSist₂ H K hK n h2 c V r₀ Qh)
      (univ.filter (fun T => ¬ askC n 1 (coinAt₂ n (by omega)) T ∧
        ¬ recC n 1 (coinAt₂ n (by omega)) T)) = 0 := by
  have h1 := Finset.sum_filter_add_sum_filter_not univ (askC n 1 (coinAt₂ n (by omega)))
    (segmentSist₂ H K hK n h2 c V r₀ Qh).stateMass
  have h2' := Finset.sum_filter_add_sum_filter_not
    (univ.filter (fun T => ¬ askC n 1 (coinAt₂ n (by omega)) T))
    (recC n 1 (coinAt₂ n (by omega))) (segmentSist₂ H K hK n h2 c V r₀ Qh).stateMass
  rw [Finset.filter_filter, Finset.filter_filter] at h2'
  rw [(segmentSist₂ H K hK n h2 c V r₀ Qh).sum_stateMass] at h1
  have ha := classMass_ask₂ hK hn h2 c V r₀ Qh
  have hr := classMass_rec₂ hK hn h2 c V r₀ Qh
  unfold classMass at ha hr ⊢
  linarith

/-- **The verdict at horizon two, at any Ask table**: `EU Qh give − EU Qh refuse = (V − c)/2` —
unchanged from horizon one, the classes having kept their masses under the tent step.
Source: [[bli-program]] §3.9 U15 (horizon `h ≥ 1`); mandate T9 ("`verdict_sistSkel` applies unchanged")
Kind: C (instance of `verdict_sistSkel`; the content is `classMass_*₂`)
Fidelity: exact
Hyps: (a) `askC Qh` (the "at an Ask table" of the verdict; instantiated at `askTable₂`) -/
theorem verdict₂ {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
    (c V : ℚ) (r₀ : Bool → ℚ) (Qh : ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1)))
    (hQ : askC n 1 (coinAt₂ n (by omega)) Qh) :
    (segmentSist₂ H K hK n h2 c V r₀ Qh).EU Qh true -
      (segmentSist₂ H K hK n h2 c V r₀ Qh).EU Qh false = (V - c) / 2 := by
  rw [verdict_sistSkel _ _ _ _ _ _ _ _ _ hQ, classMass_rec₂ hK hn h2 c V r₀ Qh,
    classMass_ask₂ hK hn h2 c V r₀ Qh, classMass_other₂ hK hn h2 c V r₀ Qh]
  ring

end H2

/-! ## The observed table of record at horizon two: a charged Ask table -/

/-- **The true-slice marginal read on day-`(n+2)` sentences**, new sentences at `1`.
Source: mandate T9 (`Qh` a day-`(n+2)` grid table)
Kind: D
Fidelity: exact -/
def extT (n : ℕ) : Table smallIndex (n + 1 + 1) :=
  fun φ => if h : φ.1 ∈ smallIndex.S (n + 1) then sliceT n ⟨φ.1, h⟩ else 1

section AskTable2

/-- `extT n` is a grid table of `segmentMesh K` on day `n+2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extT_mem_grid {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) :
    extT n ∈ grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1) := by
  rw [mem_grid_iff]
  intro φ
  unfold extT
  split_ifs with h
  · refine gridVals_mono ?_ ((Bli.segmentMesh K).d_pos _) (sliceTable_mem_gridVals n 1 0 1 True ⟨φ.1, h⟩)
    show 2 ^ Segment.k₀ n ∣ 2 ^ (n + 1 + 1 + K)
    exact pow_dvd_pow 2 (by have := hK n hn; omega)
  · exact one_mem_gridVals ((Bli.segmentMesh K).d_pos _)

/-- **The observed table of record at horizon two.**
Source: mandate T9
Kind: D
Fidelity: exact -/
def askTable₂ {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) :
    ↥(grid smallIndex (Bli.segmentMesh K).d (n + 1 + 1)) :=
  ⟨extT n, extT_mem_grid hK hn⟩

/-- `askTable₂` is an Ask table (its coin is `sliceT n`'s, `1`) — proved, not hypothesized.
Source: mandate T9
Kind: L
Fidelity: exact -/
lemma askC_askTable₂ {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n) : askC n 1 (coinAt₂ n (by omega)) (askTable₂ hK hn) := by
  have hf : freshCoord ∈ smallIndex.S (n + 1) := freshCoord_mem_smallSet (by omega)
  show (if h : freshCoord ∈ smallIndex.S (n + 1) then sliceT n ⟨freshCoord, h⟩ else (1 : ℚ)) = 1
  rw [dif_pos hf]
  exact (sliceTable_fresh n 1 0 1 True hf).trans (by simp)

/-- `extT n` restricts to `sliceT n`, so it lies on the product face over `sliceT n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extT_mem_faceProd {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) :
    extT n ∈ faceProd smallIndex (Bli.segmentMesh K).d (n + 1) (sliceT n) := by
  rw [mem_faceProd_iff]
  refine ⟨extT_mem_grid hK hn, fun φ _ => ?_⟩
  show (if h : φ.1 ∈ smallIndex.S (n + 1) then sliceT n ⟨φ.1, h⟩ else (1 : ℚ)) = sliceT n φ
  rw [dif_pos φ.2]

/-- **`askTable₂` has positive mass** at horizon two: the tent at `sliceT n` charges every table
on its product face (`tentLaw_pos_iff`), and `extT n` is one.
Source: mandate T9 (the positivity `homeEU_sistSkel` needs, derived)
Kind: L
Fidelity: exact -/
theorem stateMass₂_askTable₂_pos {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
    (c V : ℚ) (r₀ : Bool → ℚ) :
    0 < (segmentSist₂ H K hK n h2 c V r₀ (askTable₂ hK hn)).stateMass (askTable₂ hK hn) := by
  rw [stateMass₂_eq hK hn h2]
  have hT := sliceTable_mem_grid ((Bli.segmentMesh K).d_pos _) (kAt_dvd_segmentMesh hK hn) 1 0 1 True
  have hpos : 0 < tentLaw (Bli.segmentMesh K) (n + 1) (sliceT n) (extT n) :=
    (tentLaw_pos_iff (inUnit_of_mem_grid hT) _).2 (extT_mem_faceProd hK hn)
  have hnn : 0 ≤ tentLaw (Bli.segmentMesh K) (n + 1) (sliceF n) (extT n) := tentLaw_nonneg _ _
  show 0 < 1 / 2 * tentLaw (Bli.segmentMesh K) (n + 1) (sliceT n) (extT n) +
    1 / 2 * tentLaw (Bli.segmentMesh K) (n + 1) (sliceF n) (extT n)
  linarith

/-- **U15 at horizon two, the two rules at the table of record**: with `c < V` one-step UDT gives
(strictly) and with `0 < c` the updateful rule refuses, at the charged Ask table `askTable₂`;
the verdict is `(V − c)/2`.
Source: [[bli-program]] §3.9 U15 (`h ≥ 1`); mandate T9
Kind: C (instances of `verdict₂` and `homeEU_sistSkel`)
Fidelity: exact
Hyps: (a) `c < V` for the first clause, `0 < c` for the second -/
theorem rules₂ {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n) (c V : ℚ) (r₀ : Bool → ℚ) :
    (segmentSist₂ H K hK n h2 c V r₀ (askTable₂ hK hn)).EU (askTable₂ hK hn) true -
      (segmentSist₂ H K hK n h2 c V r₀ (askTable₂ hK hn)).EU (askTable₂ hK hn) false =
        (V - c) / 2 ∧
    (c < V → (segmentSist₂ H K hK n h2 c V r₀ (askTable₂ hK hn)).IsOneStepChoice
      (askTable₂ hK hn) true) ∧
    (0 < c → (segmentSist₂ H K hK n h2 c V r₀ (askTable₂ hK hn)).IsUpdatefulChoice
      (askTable₂ hK hn) false) := by
  have hd := verdict₂ hK hn h2 c V r₀ (askTable₂ hK hn) (askC_askTable₂ hK hn h2)
  refine ⟨hd, fun hcV b => ?_, fun hc b => ?_⟩
  · cases b
    · linarith
    · exact le_rfl
  · have h := homeEU_sistSkel (segmentSkeleton H K hK) n 1 (linkedTable n) (coinAt₂ n (by omega))
      c V r₀ (askTable₂ hK hn) (askC_askTable₂ hK hn h2) (stateMass₂_askTable₂_pos hK hn h2 c V r₀)
    rw [h, h]
    cases b <;> simp <;> linarith

end AskTable2

end

end Cleanroom.Bli.BliWitnessLia
