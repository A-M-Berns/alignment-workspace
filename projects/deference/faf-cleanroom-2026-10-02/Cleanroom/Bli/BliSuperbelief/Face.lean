import Cleanroom.Bli.BliFinite.Superbelief
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.BigOperators.Field

/-!
# `bli-superbelief` · Face: the face theorem on a general finite grid (E1)

The finite existence question of the BLI program, on an **arbitrary finite carrier** `G` of
day-`(m+1)` tables (not only the product grid): given a day-`m` table `t`,

* **(i) existence with full face support** (`exists_fullSupport_faceGen`): if *some* balance
  solution on `G` exists (`faceGen G t` nonempty), there is a rational probability on `G` with
  restricted mean `t` whose support is *exactly* the generated face `faceGen G t` — average
  finitely many rational witnesses, one per face point;
* **(ii) characterization** (`faceGen_eq_hullFace`): `Q ∈ faceGen G t` iff `Q ∈ G` and `t` can be
  backed away from `π Q := Q.restrict` inside the hull: `t + ε • (t − π Q) ∈ conv π(G)` for some
  rational `ε > 0` — i.e. `Q` lies on the minimal face of `conv π(G)` containing `t`. The
  "minimal face" is *characterized*, never defined (mandate design decision 2);
* **(iii) full support iff back-away everywhere** (`faceGen_eq_iff_backaway`) and its product-grid
  corollary `faceProd_eq_grid_iff` (the face is the whole grid iff `t` has no `0/1` coordinate);
* **face constancy** (`faceConst`, `faceConst_prod`): a coordinate constant on the face is the
  base price, and on the product grid it is a `0/1` price (the `udt-bli-sist` U12 input).

The containment "every balance solution is supported inside `faceGen`" is *definitional* with
`bli-finite`'s `faceGen` (`mem_faceGen_of_pos`, kind `T`) and is cited, never re-proved. The
product-grid case of (i) is `bli-finite`'s `faceProd_eq_faceGen` (via the tent kernel), cited.
Everything here is rational: the solution of (i) is an average of rational witnesses, and the
convex hull is `convexHull ℚ` over the *restricted* image (the mean is compared on day `m`).

Sources: [[bli-program]] §3.4 (face theorem, general grids); bli-slides-020 (the iff the slide
needs), bli-slides-024 (ii), bli-paper-044 (the "support ≥ 2" existence question).
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction Finset Cleanroom.Bli.BliFinite

variable {𝒮 : SmallIndex} {m : ℕ}

/-! ## Restriction as a linear map; the mean is in the hull -/

/-- Restriction of a day-`(m+1)` table to day `m`, as a `ℚ`-linear map (so that Mathlib's
`LinearMap.image_convexHull` moves the hull through it).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def restrictₗ (𝒮 : SmallIndex) (m : ℕ) : Table 𝒮 (m + 1) →ₗ[ℚ] Table 𝒮 m where
  toFun := Table.restrict
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- Unfolding lemma for `restrictₗ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma restrictₗ_apply (Q : Table 𝒮 (m + 1)) : restrictₗ 𝒮 m Q = Q.restrict := rfl

/-- The mean is the weighted sum of the carrier's tables (as vectors).
Source: bli-slides-019 (the convolution as a vector identity)
Kind: L
Fidelity: n/a -/
lemma meanOn_eq_sum_smul (G : Finset (Table 𝒮 m)) (F : Superbelief 𝒮 m) :
    meanOn G F = ∑ Q ∈ G, F Q • Q := by
  funext φ
  simp [meanOn, Finset.sum_apply]

/-- The mean of a probability on `G` lies in the convex hull of `G`.
Source: bli-slides-020 (hull of the grid)
Kind: L
Fidelity: exact -/
lemma meanOn_mem_convexHull {G : Finset (Table 𝒮 m)} {F : Superbelief 𝒮 m} (hF : IsProbOn G F) :
    meanOn G F ∈ convexHull ℚ (↑G : Set (Table 𝒮 m)) := by
  rw [Finset.mem_convexHull']
  exact ⟨F, fun Q _ => hF.1 Q, hF.2.2, (meanOn_eq_sum_smul G F).symm⟩

/-- The hull of the restricted carrier is the restriction of the hull of the carrier.
Source: none: infrastructure (`LinearMap.image_convexHull`)
Kind: L
Fidelity: n/a -/
lemma convexHull_image_restrict (G : Finset (Table 𝒮 (m + 1))) :
    convexHull ℚ (↑(G.image Table.restrict) : Set (Table 𝒮 m)) =
      restrictₗ 𝒮 m '' convexHull ℚ (↑G : Set (Table 𝒮 (m + 1))) := by
  rw [LinearMap.image_convexHull, Finset.coe_image]
  rfl

/-- The restricted mean of a probability on `G` lies in the hull of the restricted carrier.
Source: bli-slides-020
Kind: L
Fidelity: exact -/
lemma restrict_meanOn_mem_convexHull {G : Finset (Table 𝒮 (m + 1))} {F : Superbelief 𝒮 (m + 1)}
    (hF : IsProbOn G F) :
    (meanOn G F).restrict ∈ convexHull ℚ (↑(G.image Table.restrict) : Set (Table 𝒮 m)) := by
  rw [convexHull_image_restrict]
  exact ⟨meanOn G F, meanOn_mem_convexHull hF, rfl⟩

/-! ## Vacuity guards for `faceGen` -/

/-- The point mass at a carrier table whose restriction is `t` is a balance solution, so
`faceGen G t` is nonempty: the hypothesis `hne` of `exists_fullSupport_faceGen` is inhabited
whenever `t` is the restriction of a carrier point.
Source: bli-slides-005 (the degenerate solution); mandate E1 (vacuity check)
Kind: L
Fidelity: exact -/
lemma mem_faceGen_of_restrict_eq {G : Finset (Table 𝒮 (m + 1))} {t : Table 𝒮 m}
    {Q : Table 𝒮 (m + 1)} (hQ : Q ∈ G) (h : Q.restrict = t) : Q ∈ faceGen G t := by
  classical
  refine mem_faceGen_of_pos (F := fun R => if R = Q then 1 else 0) ⟨?_, ?_, ?_⟩ ?_ (by simp)
  · intro R; dsimp only; split_ifs <;> norm_num
  · intro R hR; dsimp only; rw [if_neg]; rintro rfl; exact hR hQ
  · simp [hQ]
  · rw [← h]
    funext φ
    rw [Table.restrict_apply, Table.restrict_apply]
    unfold meanOn
    simp [hQ]

/-- If `t` is outside the hull of the restricted carrier, no balance solution exists:
`faceGen G t = ∅`, and `exists_fullSupport_faceGen` is vacuous there (its hypothesis `hne`
fails). This is the honest scope of E1(i).
Source: mandate E1 (vacuity check)
Kind: L
Fidelity: exact -/
lemma faceGen_eq_empty_of_not_mem_hull {G : Finset (Table 𝒮 (m + 1))} {t : Table 𝒮 m}
    (h : t ∉ convexHull ℚ (↑(G.image Table.restrict) : Set (Table 𝒮 m))) :
    faceGen G t = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro Q hQ
  obtain ⟨-, F, hF, hb, -⟩ := mem_faceGen_iff.mp hQ
  exact h (hb ▸ restrict_meanOn_mem_convexHull hF)

/-- **Scope of E1(i), both directions.** `faceGen G t` is nonempty iff `t` lies in the hull of
the restricted carrier: the hypothesis `hne` of `exists_fullSupport_faceGen` is exactly the
program's "`p ∈ conv X`" (forward: the restricted mean of a solution is in the hull; backward: a
hull representation of `t` is a balance solution, and some carrier point carries positive weight).
Source: [[bli-program]] §3.4 (E1, "for `p ∈ conv X`"); mandate E1 (vacuity check); audit r1
(fidelity §3.1)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem faceGen_nonempty_iff_mem_hull (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m) :
    (faceGen G t).Nonempty ↔ t ∈ convexHull ℚ (↑(G.image Table.restrict) : Set (Table 𝒮 m)) := by
  classical
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨-, F, hF, hb, -⟩ := mem_faceGen_iff.mp hQ
    exact hb ▸ restrict_meanOn_mem_convexHull hF
  · intro hmem
    rw [convexHull_image_restrict] at hmem
    obtain ⟨P, hP, hPt⟩ := hmem
    rw [restrictₗ_apply] at hPt
    obtain ⟨w, hw0, hw1, hwP⟩ := Finset.mem_convexHull'.mp hP
    let F : Superbelief 𝒮 (m + 1) := fun R => if R ∈ G then w R else 0
    have hPφ : ∀ ψ : ↥(𝒮.S (m + 1)), P ψ = ∑ R ∈ G, w R * R ψ := by
      intro ψ
      rw [← hwP, Finset.sum_apply]
      rfl
    have hF : IsProbOn G F := by
      refine ⟨fun R => ?_, fun R hR => ?_, ?_⟩
      · dsimp only [F]; split_ifs with hR
        · exact hw0 R hR
        · exact le_rfl
      · simp [F, hR]
      · rw [Finset.sum_congr rfl fun R hR => show F R = w R from if_pos hR]
        exact hw1
    have hmean : meanOn G F = P := by
      funext ψ
      unfold meanOn
      rw [hPφ ψ]
      exact Finset.sum_congr rfl fun R hR => by simp [F, hR]
    have hb : (meanOn G F).restrict = t := by rw [hmean]; exact hPt
    obtain ⟨Q, hQG, hQ⟩ : ∃ Q ∈ G, F Q ≠ 0 := by
      by_contra h
      push Not at h
      have : ∑ R ∈ G, F R = 0 := Finset.sum_eq_zero h
      rw [hF.2.2] at this
      exact one_ne_zero this
    exact ⟨Q, mem_faceGen_of_pos hF hb (lt_of_le_of_ne (hF.1 Q) (Ne.symm hQ))⟩

/-! ## (i) Existence with full face support -/

section Existence
open Classical

/-- One chosen balance solution charging the face point `Q` (zero for a non-face point).
Source: mandate E1 (route: choose a witness per face point)
Kind: D
Fidelity: n/a -/
noncomputable def faceWitness (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m)
    (Q : Table 𝒮 (m + 1)) : Superbelief 𝒮 (m + 1) :=
  if h : Q ∈ faceGen G t then Classical.choose (mem_faceGen_iff.mp h).2 else 0

/-- The chosen witness is a balance solution on `G` charging `Q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceWitness_spec {G : Finset (Table 𝒮 (m + 1))} {t : Table 𝒮 m} {Q : Table 𝒮 (m + 1)}
    (hQ : Q ∈ faceGen G t) :
    IsProbOn G (faceWitness G t Q) ∧ (meanOn G (faceWitness G t Q)).restrict = t ∧
      0 < faceWitness G t Q Q := by
  unfold faceWitness
  rw [dif_pos hQ]
  exact Classical.choose_spec (mem_faceGen_iff.mp hQ).2

/-- The uniform average of the chosen witnesses over the face — the full-support solution.
Source: mandate E1 (route: average with weight `1/card`)
Kind: D
Fidelity: n/a -/
noncomputable def faceAverage (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m) :
    Superbelief 𝒮 (m + 1) :=
  fun R => (∑ Q ∈ faceGen G t, faceWitness G t Q R) / (faceGen G t).card

/-- **E1(i), existence with full face support.** On an arbitrary finite carrier `G` of day-`(m+1)`
tables, if some balance solution over `t` exists (`faceGen G t` nonempty), there is a rational
probability `F` on `G` with restricted mean `t` whose support is *exactly* `faceGen G t`:
`0 < F Q ↔ Q ∈ faceGen G t`. The solution is the uniform average of one rational witness per
face point (rational throughout; no real numbers, no choice of a real). The hypothesis `hne` is
inhabited by the point mass when `t` is the restriction of a carrier point
(`mem_faceGen_of_restrict_eq`) and fails when `t` is outside the hull
(`faceGen_eq_empty_of_not_mem_hull`), where the statement is vacuous; it holds exactly when
`t ∈ conv π(G)` (`faceGen_nonempty_iff_mem_hull`), the program's scope for E1.
Source: [[bli-program]] §3.4 (face theorem, general grids); bli-paper-044 (existence with
support ≥ 2); bli-slides-020
Kind: P
Fidelity: exact
Hyps: (a) `hne : (faceGen G t).Nonempty` (some balance solution exists; see the vacuity guards) -/
theorem exists_fullSupport_faceGen (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m)
    (hne : (faceGen G t).Nonempty) :
    ∃ F : Superbelief 𝒮 (m + 1), IsProbOn G F ∧ (meanOn G F).restrict = t ∧
      ∀ Q, 0 < F Q ↔ Q ∈ faceGen G t := by
  have hcard : (0 : ℚ) < (faceGen G t).card := by exact_mod_cast hne.card_pos
  refine ⟨faceAverage G t, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- nonnegative
    intro R
    unfold faceAverage
    exact div_nonneg (Finset.sum_nonneg fun Q hQ => (faceWitness_spec hQ).1.1 R) hcard.le
  · -- zero off `G`
    intro R hR
    unfold faceAverage
    rw [Finset.sum_eq_zero (fun Q hQ => (faceWitness_spec hQ).1.2.1 R hR), zero_div]
  · -- mass one
    unfold faceAverage
    rw [← Finset.sum_div, Finset.sum_comm,
      Finset.sum_congr rfl (fun Q hQ => (faceWitness_spec hQ).1.2.2), Finset.sum_const,
      nsmul_eq_mul, mul_one, div_self hcard.ne']
  · -- restricted mean is `t`
    funext φ
    rw [Table.restrict_apply]
    have hφ : ∀ Q ∈ faceGen G t, meanOn G (faceWitness G t Q) ⟨φ.1, 𝒮.mono m φ.2⟩ = t φ := by
      intro Q hQ
      have := congrFun (faceWitness_spec hQ).2.1 φ
      rwa [Table.restrict_apply] at this
    unfold meanOn faceAverage
    simp only [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ Q ∈ faceGen G t,
        ∑ R ∈ G, faceWitness G t Q R * R ⟨φ.1, 𝒮.mono m φ.2⟩ = t φ := fun Q hQ => hφ Q hQ
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    field_simp
  · -- support is exactly the face
    intro R
    constructor
    · intro hpos
      by_contra hR
      have hle : ∀ Q ∈ faceGen G t, faceWitness G t Q R ≤ 0 := fun Q hQ =>
        not_lt.mp fun h => hR (mem_faceGen_of_pos (faceWitness_spec hQ).1 (faceWitness_spec hQ).2.1 h)
      have : faceAverage G t R ≤ 0 := by
        unfold faceAverage
        exact div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos hle) hcard.le
      linarith
    · intro hR
      unfold faceAverage
      apply div_pos _ hcard
      calc (0 : ℚ) < faceWitness G t R R := (faceWitness_spec hR).2.2
        _ ≤ ∑ Q ∈ faceGen G t, faceWitness G t Q R :=
          Finset.single_le_sum (fun Q hQ => (faceWitness_spec hQ).1.1 R) hR

end Existence

/-! ## (ii) The hull characterization -/

/-- A probability's mass at a point is at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isProbOn_le_one {α : Type} {G : Finset α} {F : α → ℚ} (h : IsProbOn G F) {Q : α}
    (hQ : Q ∈ G) : F Q ≤ 1 := by
  rw [← h.2.2]
  exact Finset.single_le_sum (fun R _ => h.1 R) hQ

/-- If a probability on `G` puts mass one at `Q`, it is the point mass: every other carrier
point has mass zero.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isProbOn_eq_zero_of_ne_of_eq_one {α : Type} [DecidableEq α] {G : Finset α} {F : α → ℚ}
    (h : IsProbOn G F) {Q : α} (hQ : Q ∈ G) (h1 : F Q = 1) {R : α} (hR : R ∈ G) (hRQ : R ≠ Q) :
    F R = 0 := by
  have hsum := h.2.2
  rw [← Finset.add_sum_erase G F hQ, h1] at hsum
  have hzero : ∑ x ∈ G.erase Q, F x = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => h.1 x)).mp hzero R (Finset.mem_erase.mpr ⟨hRQ, hR⟩)

/-- **E1(ii), the hull characterization of the generated face.** `Q ∈ faceGen G t` iff `Q ∈ G`
and `t` can be backed away from `π Q := Q.restrict` inside the hull of the restricted carrier:
there is a rational `ε > 0` with `t + ε • (t − π Q) ∈ conv π(G)` (`convexHull ℚ` over the
*restricted* image `G.image Table.restrict`). Equivalently, `Q` lies on the minimal face of
`conv π(G)` containing `t` — characterized, not defined. Forward: from a solution with
`F Q = c > 0`, condition off `Q` (if `c < 1`; if `c = 1` then `t = π Q` and `ε = 1` works with the
hull point `t` itself). Backward: a hull representation of `t + ε (t − π Q)` pulled back to `G`
through `restrictₗ`, mixed with the point mass at `Q` in proportion `1 : ε`.
Source: [[bli-program]] §3.4 (`D:P3`, minimal face); bli-slides-020 (the iff the slide needs —
this survey's reading, ATTRIBUTION-UNVETTED as the author's intent); bli-slides-024 (ii)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem faceGen_eq_hullFace (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m) (Q : Table 𝒮 (m + 1)) :
    Q ∈ faceGen G t ↔ Q ∈ G ∧ ∃ ε : ℚ, 0 < ε ∧
      t + ε • (t - Q.restrict) ∈ convexHull ℚ (↑(G.image Table.restrict) : Set (Table 𝒮 m)) := by
  classical
  constructor
  · intro h
    obtain ⟨hQG, F, hF, hb, hpos⟩ := mem_faceGen_iff.mp h
    refine ⟨hQG, ?_⟩
    rcases (isProbOn_le_one hF hQG).lt_or_eq with hlt | heq
    · -- `c < 1`: condition off `Q`
      set c := F Q with hc
      have h1c : 0 < 1 - c := by linarith
      refine ⟨c / (1 - c), div_pos hpos h1c, ?_⟩
      let F' : Superbelief 𝒮 (m + 1) := fun R => (F R - if R = Q then c else 0) / (1 - c)
      have hF' : IsProbOn G F' := by
        refine ⟨?_, ?_, ?_⟩
        · intro R
          apply div_nonneg _ h1c.le
          split_ifs with hRQ
          · rw [hRQ]; linarith
          · linarith [hF.1 R]
        · intro R hR
          have hRQ : R ≠ Q := fun e => hR (e ▸ hQG)
          simp only [F', if_neg hRQ, sub_zero, hF.2.1 R hR, zero_div]
        · show (∑ R ∈ G, (F R - if R = Q then c else 0) / (1 - c)) = 1
          rw [← Finset.sum_div, Finset.sum_sub_distrib, hF.2.2,
            Finset.sum_ite_eq' G Q (fun _ => c), if_pos hQG, div_self h1c.ne']
      have hmean : (meanOn G F').restrict = t + (c / (1 - c)) • (t - Q.restrict) := by
        funext φ
        have ht : meanOn G F ⟨φ.1, 𝒮.mono m φ.2⟩ = t φ := by
          have := congrFun hb φ
          rwa [Table.restrict_apply] at this
        rw [Table.restrict_apply]
        show meanOn G F' ⟨φ.1, 𝒮.mono m φ.2⟩ = t φ + c / (1 - c) * (t φ - Q ⟨φ.1, 𝒮.mono m φ.2⟩)
        unfold meanOn at ht ⊢
        simp only [F', div_mul_eq_mul_div, ← Finset.sum_div, sub_mul, Finset.sum_sub_distrib, ht,
          ite_mul, zero_mul, Finset.sum_ite_eq' G Q, if_pos hQG]
        field_simp
        ring
      rw [← hmean]
      exact restrict_meanOn_mem_convexHull hF'
    · -- `c = 1`: `t = π Q`
      refine ⟨1, one_pos, ?_⟩
      have ht : t = Q.restrict := by
        rw [← hb]
        funext φ
        rw [Table.restrict_apply, Table.restrict_apply]
        unfold meanOn
        rw [Finset.sum_eq_single Q]
        · rw [heq, one_mul]
        · intro R hR hRQ
          rw [isProbOn_eq_zero_of_ne_of_eq_one hF hQG heq hR hRQ, zero_mul]
        · intro hQ; exact absurd hQG hQ
      rw [ht, sub_self, smul_zero, add_zero]
      exact subset_convexHull ℚ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hQG))
  · rintro ⟨hQG, ε, hε, hmem⟩
    rw [convexHull_image_restrict] at hmem
    obtain ⟨P, hP, hPt⟩ := hmem
    rw [restrictₗ_apply] at hPt
    obtain ⟨w, hw0, hw1, hwP⟩ := Finset.mem_convexHull'.mp hP
    have h1ε : 0 < 1 + ε := by linarith
    let F : Superbelief 𝒮 (m + 1) :=
      fun R => (if R ∈ G then w R else 0) / (1 + ε) + if R = Q then ε / (1 + ε) else 0
    have hPφ : ∀ ψ : ↥(𝒮.S (m + 1)), P ψ = ∑ R ∈ G, w R * R ψ := by
      intro ψ
      rw [← hwP, Finset.sum_apply]
      rfl
    refine mem_faceGen_iff.mpr ⟨hQG, F, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro R
      apply add_nonneg
      · apply div_nonneg _ h1ε.le
        split_ifs with hR
        · exact hw0 R hR
        · exact le_rfl
      · split_ifs
        · exact div_nonneg hε.le h1ε.le
        · exact le_rfl
    · intro R hR
      have hRQ : R ≠ Q := fun e => hR (e ▸ hQG)
      simp only [F, if_neg hR, if_neg hRQ, zero_div, add_zero]
    · simp only [F, Finset.sum_add_distrib, Finset.sum_ite_eq' G Q, if_pos hQG]
      rw [← Finset.sum_div, Finset.sum_congr rfl (fun R hR => if_pos hR), hw1]
      field_simp
    · funext φ
      rw [Table.restrict_apply]
      have hPt' := congrFun hPt φ
      rw [Table.restrict_apply] at hPt'
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Table.restrict_apply] at hPt'
      show meanOn G F ⟨φ.1, 𝒮.mono m φ.2⟩ = t φ
      unfold meanOn
      simp only [F, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div, ← Finset.sum_div,
        ite_mul, zero_mul, Finset.sum_ite_eq' G Q, if_pos hQG]
      rw [Finset.sum_congr rfl (fun R hR => by rw [if_pos hR]), ← hPφ, hPt']
      field_simp
      ring
    · show 0 < (if Q ∈ G then w Q else 0) / (1 + ε) + if Q = Q then ε / (1 + ε) else 0
      rw [if_pos hQG, if_pos rfl]
      have : 0 ≤ w Q / (1 + ε) := div_nonneg (hw0 Q hQG) h1ε.le
      have : 0 < ε / (1 + ε) := div_pos hε h1ε
      linarith

/-! ## (iii) Full support iff back-away everywhere; the product-grid corollary -/

/-- **E1(iii), general form.** The generated face is the whole carrier iff every carrier point
can be backed away from inside the hull of the restricted carrier — the relative-interior
condition, stated as the back-away criterion (Mathlib's `intrinsicInterior` identification is
not attempted; see the report).
Source: [[bli-program]] §3.4 ("support is all of `X` iff `p` is in the relative interior");
bli-slides-020
Kind: C
Fidelity: variant: relative interior rendered as the back-away criterion of E1(ii)
Hyps: (a) none -/
theorem faceGen_eq_iff_backaway (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m) :
    faceGen G t = G ↔ ∀ Q ∈ G, ∃ ε : ℚ, 0 < ε ∧
      t + ε • (t - Q.restrict) ∈ convexHull ℚ (↑(G.image Table.restrict) : Set (Table 𝒮 m)) := by
  constructor
  · intro h Q hQ
    exact ((faceGen_eq_hullFace G t Q).mp (h.symm ▸ hQ)).2
  · intro h
    apply Finset.Subset.antisymm (faceGen_subset G t)
    intro Q hQ
    exact (faceGen_eq_hullFace G t Q).mpr ⟨hQ, h Q hQ⟩

/-- **E1(iii), product-grid corollary.** On the product grid (`0 < d (m+1)`) the product face is
the whole grid iff `t` has no `0/1` coordinate on `S m`. Combined with `faceProd_eq_faceGen`
(`bli-finite`, for unit-cube `t`) this is "full support iff `t` is interior". Nearly definitional:
`faceProd` is the grid filtered by agreement at the `0/1` coordinates, so the filter is vacuous iff
there are none (the constant-`0`/`1` grid tables witness the converse).
Source: [[bli-program]] §3.4 (product grid: coordinatewise); bli-slides-020 (interior of the cube)
Kind: C
Fidelity: exact
Hyps: (a) `0 < d (m+1)` -/
theorem faceProd_eq_grid_iff {d : ℕ → ℕ} (hd : 0 < d (m + 1)) (t : Table 𝒮 m) :
    faceProd 𝒮 d m t = grid 𝒮 d (m + 1) ↔ ∀ φ : ↥(𝒮.S m), t φ ≠ 0 ∧ t φ ≠ 1 := by
  constructor
  · intro h φ
    constructor
    · intro h0
      have hone : (fun _ => (1 : ℚ) : Table 𝒮 (m + 1)) ∈ grid 𝒮 d (m + 1) :=
        mem_grid_iff.mpr fun _ => one_mem_gridVals hd
      rw [← h, mem_faceProd_iff] at hone
      have := hone.2 φ (Or.inl h0)
      rw [Table.restrict_apply, h0] at this
      norm_num at this
    · intro h1
      have hzero : (fun _ => (0 : ℚ) : Table 𝒮 (m + 1)) ∈ grid 𝒮 d (m + 1) :=
        mem_grid_iff.mpr fun _ => zero_mem_gridVals _
      rw [← h, mem_faceProd_iff] at hzero
      have := hzero.2 φ (Or.inr h1)
      rw [Table.restrict_apply, h1] at this
      norm_num at this
  · intro h
    apply Finset.Subset.antisymm (faceProd_subset_grid d t)
    intro Q hQ
    refine mem_faceProd_iff.mpr ⟨hQ, fun φ hφ => ?_⟩
    rcases hφ with h0 | h1
    · exact absurd h0 (h φ).1
    · exact absurd h1 (h φ).2

/-! ## Face constancy (the `udt-bli-sist` U12 input) -/

/-- **Face constancy.** If a day-`m` coordinate `φ` takes the same value `c` on every point of the
generated face, the base price is `c`: `t φ = c`. Proof: the full-support solution of E1(i) has
its mass exactly on the face, so its restricted mean at `φ` is `c`.
Source: [[bli-program]] §3.4; mandate E1 (U12 corollary)
Kind: C
Fidelity: exact
Hyps: (a) `hne : (faceGen G t).Nonempty` -/
theorem faceConst (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m) (hne : (faceGen G t).Nonempty)
    (φ : ↥(𝒮.S m)) (c : ℚ) (hc : ∀ Q ∈ faceGen G t, Q.restrict φ = c) : t φ = c := by
  obtain ⟨F, hF, hb, hsupp⟩ := exists_fullSupport_faceGen G t hne
  have ht := congrFun hb φ
  rw [Table.restrict_apply] at ht
  rw [← ht]
  show ∑ Q ∈ G, F Q * Q ⟨φ.1, 𝒮.mono m φ.2⟩ = c
  calc ∑ Q ∈ G, F Q * Q ⟨φ.1, 𝒮.mono m φ.2⟩ = ∑ Q ∈ G, F Q * c := by
        apply Finset.sum_congr rfl
        intro Q hQ
        by_cases hQf : Q ∈ faceGen G t
        · rw [← hc Q hQf, Table.restrict_apply]
        · have : F Q = 0 := le_antisymm (not_lt.mp fun h => hQf ((hsupp Q).mp h)) (hF.1 Q)
          rw [this, zero_mul, zero_mul]
    _ = c := by rw [← Finset.sum_mul, hF.2.2, one_mul]

/-- The base face point of the product grid: `t`'s value at the pinned coordinates, `0` elsewhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def basePoint (𝒮 : SmallIndex) (m : ℕ) (t : Table 𝒮 m) : Table 𝒮 (m + 1) :=
  fun ψ => if h : ψ.1 ∈ 𝒮.S m then
    (if t ⟨ψ.1, h⟩ = 0 ∨ t ⟨ψ.1, h⟩ = 1 then t ⟨ψ.1, h⟩ else 0) else 0

/-- The base point with coordinate `φ` overwritten by `v`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def basePointUpd (𝒮 : SmallIndex) (m : ℕ) (t : Table 𝒮 m) (φ : ↥(𝒮.S m)) (v : ℚ) :
    Table 𝒮 (m + 1) :=
  fun ψ => if ψ.1 = φ.1 then v else basePoint 𝒮 m t ψ

/-- The base point with coordinate `φ` overwritten by a grid value `v ∈ {0, 1}` is on the product
face whenever `t φ` is not a `0/1` price (`0 < d (m+1)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma basePointUpd_mem_faceProd {d : ℕ → ℕ} (hd : 0 < d (m + 1)) (t : Table 𝒮 m) (φ : ↥(𝒮.S m))
    (hφ : ¬ (t φ = 0 ∨ t φ = 1)) {v : ℚ} (hv : v = 0 ∨ v = 1) :
    basePointUpd 𝒮 m t φ v ∈ faceProd 𝒮 d m t := by
  refine mem_faceProd_iff.mpr ⟨mem_grid_iff.mpr fun ψ => ?_, fun ψ hψ => ?_⟩
  · unfold basePointUpd basePoint
    split_ifs with h1 h2 h3
    · rcases hv with rfl | rfl
      · exact zero_mem_gridVals _
      · exact one_mem_gridVals hd
    · rcases h3 with h3 | h3 <;> rw [h3]
      · exact zero_mem_gridVals _
      · exact one_mem_gridVals hd
    · exact zero_mem_gridVals _
    · exact zero_mem_gridVals _
  · rw [Table.restrict_apply]
    unfold basePointUpd basePoint
    have hne : ψ.1 ≠ φ.1 := by
      intro e
      apply hφ
      have : ψ = φ := Subtype.ext e
      rwa [← this]
    rw [if_neg hne, dif_pos ψ.2, if_pos hψ]

/-- **Face constancy on the product grid.** If a day-`m` coordinate `φ` takes the same value `c`
on every point of the product face (`0 < d (m+1)`), then `c` is the base price *and* a `0/1`
price: `t φ = c ∧ (c = 0 ∨ c = 1)` — "on the product face a constant coordinate is at a `0/1`
price". Proof: if `t φ ∉ {0, 1}` the face contains points with `φ`-value `0` and `1`.
Source: [[bli-program]] §3.4; mandate E1 (U12 corollary, product form)
Kind: C
Fidelity: exact
Hyps: (a) `0 < d (m+1)` -/
theorem faceConst_prod {d : ℕ → ℕ} (hd : 0 < d (m + 1)) (t : Table 𝒮 m) (φ : ↥(𝒮.S m)) (c : ℚ)
    (hc : ∀ Q ∈ faceProd 𝒮 d m t, Q.restrict φ = c) : t φ = c ∧ (c = 0 ∨ c = 1) := by
  have hpin : t φ = 0 ∨ t φ = 1 := by
    by_contra hn
    have h0 := hc _ (basePointUpd_mem_faceProd hd t φ hn (Or.inl rfl))
    have h1 := hc _ (basePointUpd_mem_faceProd hd t φ hn (Or.inr rfl))
    rw [Table.restrict_apply] at h0 h1
    unfold basePointUpd at h0 h1
    rw [if_pos rfl] at h0 h1
    rw [← h0] at h1
    norm_num at h1
  -- the base point itself is on the face and reads `t φ` at `φ`
  have hbase : basePoint 𝒮 m t ∈ faceProd 𝒮 d m t := by
    refine mem_faceProd_iff.mpr ⟨mem_grid_iff.mpr fun ψ => ?_, fun ψ hψ => ?_⟩
    · unfold basePoint
      split_ifs with h1 h2
      · rcases h2 with h2 | h2 <;> rw [h2]
        · exact zero_mem_gridVals _
        · exact one_mem_gridVals hd
      · exact zero_mem_gridVals _
      · exact zero_mem_gridVals _
    · rw [Table.restrict_apply]
      unfold basePoint
      rw [dif_pos ψ.2, if_pos hψ]
  have := hc _ hbase
  rw [Table.restrict_apply] at this
  unfold basePoint at this
  rw [dif_pos φ.2, if_pos hpin] at this
  exact ⟨this, this ▸ hpin⟩

end Cleanroom.Bli.BliSuperbelief
