/-
# Coverage: every point lies in some face's cell

`PolyhedralProjection` builds, for each *face* of a rational polytope, a rational affine
**candidate** map and the closed **cell** on which that candidate is certified to be the
nearest point.  What is missing there is that the finitely many cells actually **cover**:
every point of the ambient space lies in the cell of some face assembled from the
polytope's own vertices.  This file closes that gap and reads off the consequence the
compiler needs — each coordinate of the projection is piecewise affine, with rational
components indexed by a finite list of faces, and hence (Ovchinnikov) a max of mins of
those components.

**The geometry.**  Write `q = K.proj p` as a convex combination of vertices and call a
vertex *active* when its weight is strictly positive.  Shifting weight between two active
vertices stays inside the region in both directions, so the variational inequality bites
twice and gives `⟪p − q, y − z⟫ = 0` for active `y, z` — that is `inner_eq_zero_of_active`,
proved upstream.  Fixing one active vertex as `base`, the displacement `q − base` is a real
combination of the directions `v − base` over active `v`, because the weights sum to one.
So `q` is a point of the affine span of the active vertices whose displacement from `p` is
orthogonal to that span, which is exactly the system `Face.candidate_unique` solves —
*provided* the spanning directions are independent.

**Thinning.**  They need not be, and making them so is the only real work here.  If the
directions are dependent, one of them is a real combination of the others; delete it and
absorb its coefficient into theirs.  The list gets shorter and the point it represents does
not move, so an induction on length terminates at an independent — that is, `Regular` —
face.

*Coefficients are indexed by the vertex, not by a position in the list.*  That is what
keeps the induction short: deleting an entry leaves the coefficient function literally
unchanged, so the erased list's hypothesis is the old one with two sums rearranged, and no
re-indexing lemma is ever needed.  Positions appear exactly twice — once to read a linear
dependence off `Fintype.not_linearIndependent_iff`, once to feed `Face.candidate_unique` —
and `sum_toFinset_eq_sum_fin` is the bridge both times.

**What is *not* claimed.**  Nothing here says the cells are the normal-cone decomposition,
that they meet only along boundaries, or that the enumerated face list is minimal: it holds
`|verts| · 2 ^ |verts|` faces, most of them degenerate.  Degenerate faces need no treatment
because a face's cell is defined by its candidate passing the polytope's own certificate,
so a junk candidate simply has an empty cell.  Coverage is all the downstream compiler
asks for.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.PolyhedralProjection
import Workspace.Normativity.Contrib.MaxMinRepresentation

namespace Workspace.Normativity.Contrib.PolyhedralCoverage

open scoped RealInnerProductSpace
open Workspace.Normativity.Contrib.RationalPolytope
open Workspace.Normativity.Contrib.PolyhedralProjection
open Workspace.Normativity.Contrib.MaxMinRepresentation

variable {d : ℕ}

/-! ## Two bridges

A sum over a duplicate-free list's `toFinset` is a sum over its positions.  This is what
lets the argument be phrased with vertex-indexed coefficients while the two mathlib
interfaces it must meet — linear independence and the face's Gram system — are both
position-indexed. -/

/-- A `Nodup` list's `toFinset` sum, read off positions. -/
theorem sum_toFinset_eq_sum_fin {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (L : List α) (hnd : L.Nodup) (f : α → M) :
    ∑ v ∈ L.toFinset, f v = ∑ j : Fin L.length, f (L.get j) := by
  rw [List.sum_toFinset _ hnd, ← List.ofFn_getElem_eq_map L f, List.sum_ofFn]
  rfl

/-- A rational point's coordinates are the casts of its rational coordinates. -/
theorem toPt_apply (v : Fin d → ℚ) (i : Fin d) : (toPt v) i = (v i : ℝ) := rfl

/-- `toPt` is injective, so a face's rational data is recoverable from its points. -/
theorem toPt_injective : Function.Injective (toPt : (Fin d → ℚ) → Pt d) := by
  intro a b hab
  funext i
  have hcast : ((a i : ℚ) : ℝ) = ((b i : ℚ) : ℝ) := congrArg (fun x : Pt d => x i) hab
  exact_mod_cast hcast

/-- The difference of two rational points is the rational point of the difference. -/
theorem toPt_sub (v b : Fin d → ℚ) : toPt v - toPt b = toPt (fun i => v i - b i) := by
  ext i
  simp only [PiLp.sub_apply, toPt, WithLp.ofLp_toLp, Rat.cast_sub]

/-! ## The spanning directions, indexed by position

`Face.dir` is indexed by `Fin F.dim`, which is only *definitionally* `Fin F.rest.length`.
Naming the same family over `Fin L.length` costs one lemma and buys back every later
rewrite. -/

/-- The directions from `base` to the entries of `L`. -/
def dirs (base : Fin d → ℚ) (L : List (Fin d → ℚ)) (j : Fin L.length) : Pt d :=
  toPt (L.get j) - toPt base

theorem face_dir_eq_dirs (base : Fin d → ℚ) (L : List (Fin d → ℚ)) :
    (Face.mk base L).dir = dirs base L := by
  funext j
  rw [dirs, toPt_sub]
  rfl

theorem dirs_apply (base : Fin d → ℚ) (L : List (Fin d → ℚ)) (j : Fin L.length) (i : Fin d) :
    (dirs base L j) i = (L.get j i : ℝ) - (base i : ℝ) := by
  simp only [dirs, PiLp.sub_apply, toPt_apply]

/-- A face's spanning direction, as a difference of points. -/
theorem face_dir_apply (base : Fin d → ℚ) (L : List (Fin d → ℚ))
    (j : Fin (Face.mk base L).dim) :
    (Face.mk base L).dir j = toPt (L.get ⟨j.1, j.2⟩) - toPt base := by
  rw [toPt_sub]
  rfl

/-! ## Reading a dependence off a face

`Fintype.not_linearIndependent_iff` hands back a coefficient function indexed by positions.
Transporting it to a vertex-indexed one is a single `Finset.sum_eq_single` step, done once
here so that the induction below never sees a position again. -/

/-- A dependent face has a nontrivial **vertex-indexed** relation among its directions. -/
theorem exists_vertex_dependence (base : Fin d → ℚ) (L : List (Fin d → ℚ))
    (hnd : L.Nodup) (h : ¬ LinearIndependent ℝ (Face.mk base L).dir) :
    ∃ (G : (Fin d → ℚ) → ℝ) (u : Fin d → ℚ), u ∈ L ∧ G u ≠ 0 ∧
      ∀ i, ∑ v ∈ L.toFinset, G v * ((v i : ℝ) - (base i : ℝ)) = 0 := by
  classical
  have h' : ¬ LinearIndependent ℝ (dirs base L) := fun hli =>
    h (by rw [face_dir_eq_dirs]; exact hli)
  obtain ⟨g, hg0, k, hgk⟩ := Fintype.not_linearIndependent_iff.mp h'
  have hinj : Function.Injective L.get := List.nodup_iff_injective_get.mp hnd
  set G : (Fin d → ℚ) → ℝ :=
    fun v => ∑ j : Fin L.length, if L.get j = v then g j else 0 with hG
  have hGget : ∀ j₀ : Fin L.length, G (L.get j₀) = g j₀ := by
    intro j₀
    simp only [hG]
    rw [Finset.sum_eq_single j₀]
    · rw [if_pos rfl]
    · intro j _ hj; exact if_neg fun he => hj (hinj he)
    · intro hj; exact absurd (Finset.mem_univ j₀) hj
  refine ⟨G, L.get k, List.get_mem _ _, by rw [hGget]; exact hgk, fun i => ?_⟩
  have hcoord : ∑ j : Fin L.length, g j * ((L.get j i : ℝ) - (base i : ℝ)) = 0 := by
    have hz := congrArg (fun x : Pt d => x i) hg0
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, dirs_apply] at hz
    simpa using hz
  rw [sum_toFinset_eq_sum_fin L hnd, ← hcoord]
  exact Finset.sum_congr rfl fun j₀ _ => by rw [hGget j₀]

/-! ## The regular case

When the directions are already independent, the candidate is `q` by uniqueness.  This is
the induction's base and also its exit at every step. -/

/-- An independent face whose span carries `q` and is orthogonal to `p − q` has `q` as its
candidate. -/
theorem regular_and_candidate_of_linearIndependent (p q : Pt d) (base : Fin d → ℚ)
    (L : List (Fin d → ℚ)) (hnd : L.Nodup)
    (hLI : LinearIndependent ℝ (Face.mk base L).dir)
    (horth : ∀ v ∈ L, ⟪toPt v - toPt base, p - q⟫ = 0)
    (c : (Fin d → ℚ) → ℝ)
    (hc : ∀ i, q i = (base i : ℝ) + ∑ v ∈ L.toFinset, ((v i : ℝ) - (base i : ℝ)) * c v) :
    (Face.mk base L).Regular ∧ q = (Face.mk base L).candidate p := by
  classical
  have hreg : (Face.mk base L).Regular :=
    (Face.mk base L).regular_of_linearIndependent hLI
  refine ⟨hreg, ?_⟩
  have hx : ∀ i, q i = (base i : ℝ) + ∑ j : Fin (Face.mk base L).dim,
      ((Face.mk base L).dirQ j i : ℝ) * c (L.get ⟨j.1, j.2⟩) := by
    intro i
    have hbridge : ∑ v ∈ L.toFinset, ((v i : ℝ) - (base i : ℝ)) * c v
        = ∑ j : Fin (Face.mk base L).dim,
            ((Face.mk base L).dirQ j i : ℝ) * c (L.get ⟨j.1, j.2⟩) := by
      rw [sum_toFinset_eq_sum_fin L hnd]
      exact Finset.sum_congr rfl fun j _ => by simp only [Face.dirQ, Rat.cast_sub]
    rw [hc i, hbridge]
  have horth' : ∀ l : Fin (Face.mk base L).dim, ⟪(Face.mk base L).dir l, p - q⟫ = 0 := by
    intro l
    rw [face_dir_apply]
    exact horth _ (List.get_mem _ _)
  exact (Face.mk base L).candidate_unique hreg p q _ hx horth'

/-! ## Thinning to a regular face

The induction.  Its hypotheses: the list is duplicate-free, `p − q` is orthogonal to every
direction from `base`, and `q` is a real combination of those directions.  Its conclusion: a
*regular sublist* face with the same base whose candidate at `p` is `q`.

The step deletes one vertex `u` carrying a nonzero coefficient `G u` in a linear dependence
and replaces `c` by `c − (c u / G u) · G`.  The deleted term is exactly what the correction
adds back. -/

/-- **Thinning.**  Bounded by `n` so the recursion runs on a natural number. -/
theorem exists_regular_face_aux (p q : Pt d) (base : Fin d → ℚ) (n : ℕ) :
    ∀ L : List (Fin d → ℚ), L.length ≤ n → L.Nodup →
      (∀ v ∈ L, ⟪toPt v - toPt base, p - q⟫ = 0) →
      (∃ c : (Fin d → ℚ) → ℝ, ∀ i, q i = (base i : ℝ)
          + ∑ v ∈ L.toFinset, ((v i : ℝ) - (base i : ℝ)) * c v) →
      ∃ F : Face d, F.base = base ∧ F.rest.Sublist L ∧ F.Regular ∧ q = F.candidate p := by
  classical
  induction n with
  | zero =>
      rintro L hlen hnd horth ⟨c, hc⟩
      have hL : L = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hL
      have hLI : LinearIndependent ℝ (Face.mk base ([] : List (Fin d → ℚ))).dir := by
        haveI : IsEmpty (Fin (Face.mk base ([] : List (Fin d → ℚ))).dim) :=
          show IsEmpty (Fin 0) from inferInstance
        exact linearIndependent_empty_type
      obtain ⟨hreg, hcand⟩ :=
        regular_and_candidate_of_linearIndependent p q base [] hnd hLI horth c hc
      exact ⟨Face.mk base [], rfl, List.Sublist.refl _, hreg, hcand⟩
  | succ n ih =>
      rintro L hlen hnd horth ⟨c, hc⟩
      by_cases hLI : LinearIndependent ℝ (Face.mk base L).dir
      · obtain ⟨hreg, hcand⟩ :=
          regular_and_candidate_of_linearIndependent p q base L hnd hLI horth c hc
        exact ⟨Face.mk base L, rfl, List.Sublist.refl _, hreg, hcand⟩
      · obtain ⟨G, u, huL, hGu, hrel⟩ := exists_vertex_dependence base L hnd hLI
        have hperm : L.Perm (u :: L.erase u) := List.perm_cons_erase huL
        have hnd' : (u :: L.erase u).Nodup := hperm.nodup_iff.mp hnd
        have hnotmem : u ∉ L.erase u := (List.nodup_cons.mp hnd').1
        have hnde : (L.erase u).Nodup := (List.nodup_cons.mp hnd').2
        have hsplit : ∀ f : (Fin d → ℚ) → ℝ,
            ∑ v ∈ L.toFinset, f v = f u + ∑ v ∈ (L.erase u).toFinset, f v := by
          intro f
          rw [List.toFinset_eq_of_perm _ _ hperm, List.toFinset_cons,
            Finset.sum_insert (by simpa using hnotmem)]
        have hlen' : (L.erase u).length ≤ n := by
          have := List.length_erase_of_mem huL
          omega
        have hstep : ∀ i : Fin d, q i = (base i : ℝ)
            + ∑ v ∈ (L.erase u).toFinset,
                ((v i : ℝ) - (base i : ℝ)) * (c v - (c u / G u) * G v) := by
          intro i
          have hrel' := hrel i
          rw [hsplit (fun v => G v * ((v i : ℝ) - (base i : ℝ)))] at hrel'
          have hE : ∑ v ∈ (L.erase u).toFinset, G v * ((v i : ℝ) - (base i : ℝ))
              = -(G u * ((u i : ℝ) - (base i : ℝ))) := by linarith
          have hL1 : ∑ v ∈ (L.erase u).toFinset,
              ((v i : ℝ) - (base i : ℝ)) * (c v - (c u / G u) * G v)
              = (∑ v ∈ (L.erase u).toFinset, ((v i : ℝ) - (base i : ℝ)) * c v)
                - (c u / G u) * ∑ v ∈ (L.erase u).toFinset,
                    G v * ((v i : ℝ) - (base i : ℝ)) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun v _ => by ring
          have hcancel : (c u / G u) * (G u * ((u i : ℝ) - (base i : ℝ)))
              = ((u i : ℝ) - (base i : ℝ)) * c u := by
            field_simp
          rw [hL1, hE, hc i, hsplit (fun v => ((v i : ℝ) - (base i : ℝ)) * c v)]
          linarith [hcancel]
        exact (ih (L.erase u) hlen' hnde (fun v hv => horth v (List.mem_of_mem_erase hv))
          ⟨_, hstep⟩).imp fun F hF =>
            ⟨hF.1, hF.2.1.trans (List.erase_sublist), hF.2.2⟩

/-! ## Coverage

The active vertices of one convex representation of `K.proj p` supply the list to thin.
Everything before the call to `exists_regular_face_aux` is bookkeeping: turning the centre
of mass into a plain weighted sum, cutting the vertex set down to its active part, and
moving from points of `Pt d` back to the rational tuples a `Face` is built from. -/

/-- **Coverage, with the sublist witness.**  Every point lies in the cell of a face whose
base is a vertex and whose rest is a sublist of the vertex list. -/
theorem exists_face_sublist_mem_cell (K : RationalPolytope d) (p : Pt d) :
    ∃ F : Face d, F.base ∈ K.verts ∧ F.rest.Sublist K.verts ∧ p ∈ cell K F := by
  classical
  set q : Pt d := K.proj p with hqdef
  set VF : Finset (Pt d) := K.vertexSet_finite.toFinset with hVF
  have hqmem : q ∈ convexHull ℝ K.vertexSet := K.proj_mem p
  rw [K.vertexSet_finite.convexHull_eq] at hqmem
  obtain ⟨w, hw, hwsum, hcm⟩ := hqmem
  have hqsum : ∑ v ∈ VF, w v • v = q := by
    rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hwsum]
    rfl
  -- some vertex is active
  obtain ⟨y₀, hy₀mem, hy₀⟩ : ∃ y ∈ VF, 0 < w y := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hle : ∑ v ∈ VF, w v ≤ 0 := Finset.sum_nonpos fun v hv => hcon v hv
    rw [hwsum] at hle
    linarith
  obtain ⟨base, hbase, hbaseq⟩ : ∃ b ∈ K.verts, toPt b = y₀ := by
    have hy : y₀ ∈ K.vertexSet := by simpa [hVF] using hy₀mem
    obtain ⟨b, hb, hbq⟩ := hy
    exact ⟨b, hb, hbq⟩
  -- the active vertices, as rational tuples
  set L : List (Fin d → ℚ) := K.verts.dedup.filter (fun v => 0 < w (toPt v)) with hL
  have hmemL : ∀ v, v ∈ L ↔ (v ∈ K.verts ∧ 0 < w (toPt v)) := by
    intro v
    rw [hL, List.mem_filter, List.mem_dedup]
    simp
  have hnd : L.Nodup := (K.verts.nodup_dedup).filter _
  have hsub : L.Sublist K.verts :=
    List.filter_sublist.trans (List.dedup_sublist K.verts)
  have hvert : ∀ v ∈ L, toPt v ∈ VF := by
    intro v hv
    have : toPt v ∈ K.vertexSet := ⟨v, ((hmemL v).mp hv).1, rfl⟩
    simpa [hVF] using this
  have hbaseL : base ∈ L := (hmemL base).mpr ⟨hbase, by rw [hbaseq]; exact hy₀⟩
  -- orthogonality on the active set
  have horth : ∀ v ∈ L, ⟪toPt v - toPt base, p - q⟫ = 0 := by
    intro v hv
    rw [real_inner_comm]
    exact inner_eq_zero_of_active K p hw hwsum hqsum (hvert v hv) (hvert base hbaseL)
      ((hmemL v).mp hv).2 ((hmemL base).mp hbaseL).2
  -- the projection as a combination of the active directions
  have hspan : ∀ i : Fin d, q i = (base i : ℝ)
      + ∑ v ∈ L.toFinset, ((v i : ℝ) - (base i : ℝ)) * w (toPt v) := by
    intro i
    have hcoord : q i = ∑ v ∈ VF, w v * (v i) := by
      rw [← hqsum]
      simp [WithLp.ofLp_sum, Finset.sum_apply]
    have hbcoord : ∑ v ∈ VF, w v * (base i : ℝ) = (base i : ℝ) := by
      rw [← Finset.sum_mul, hwsum, one_mul]
    have hkey : q i - (base i : ℝ) = ∑ v ∈ VF, w v * (v i - (base i : ℝ)) := by
      have hexp : ∑ v ∈ VF, w v * (v i - (base i : ℝ))
          = (∑ v ∈ VF, w v * (v i)) - ∑ v ∈ VF, w v * (base i : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [hexp, hbcoord, ← hcoord]
    have himg : VF.filter (fun y => 0 < w y) = L.toFinset.image toPt := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image, List.mem_toFinset]
      constructor
      · rintro ⟨hyV, hyw⟩
        have hy : y ∈ K.vertexSet := by simpa [hVF] using hyV
        obtain ⟨v, hv, rfl⟩ := hy
        exact ⟨v, (hmemL v).mpr ⟨hv, hyw⟩, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨hvert v hv, ((hmemL v).mp hv).2⟩
    have hfilter : ∑ v ∈ VF, w v * (v i - (base i : ℝ))
        = ∑ v ∈ VF.filter (fun y => 0 < w y), w v * (v i - (base i : ℝ)) := by
      refine (Finset.sum_filter_of_ne fun v hv hne => ?_).symm
      have hv0 : 0 ≤ w v := hw v (by simpa [hVF] using hv)
      rcases lt_or_eq_of_le hv0 with h | h
      · exact h
      · exact absurd (by rw [← h]; ring) hne
    rw [himg, Finset.sum_image (fun a _ b _ hab => toPt_injective hab)] at hfilter
    have hfinal : q i - (base i : ℝ)
        = ∑ v ∈ L.toFinset, ((v i : ℝ) - (base i : ℝ)) * w (toPt v) := by
      rw [hkey, hfilter]
      exact Finset.sum_congr rfl fun v _ => by rw [toPt_apply]; ring
    linarith [hfinal]
  obtain ⟨F, hFb, hFr, _hFreg, hFq⟩ :=
    exists_regular_face_aux p q base L.length L le_rfl hnd horth ⟨_, hspan⟩
  refine ⟨F, hFb ▸ hbase, hFr.trans hsub, ?_, ?_⟩
  · rw [← hFq, hqdef]; exact K.proj_mem p
  · intro v hv
    rw [← hFq, hqdef]
    exact K.proj_variational p (K.vertexSet_subset_carrier hv)

/-- **Coverage.**  Every point lies in the cell of a face built from the polytope's own
vertices.  The finitely many rational affine candidates therefore leave nothing uncovered,
which is the last gap in reading the projection as a piecewise affine map. -/
theorem exists_face_mem_cell (K : RationalPolytope d) (p : Pt d) :
    ∃ F : Face d, F.base ∈ K.verts ∧ (∀ v ∈ F.rest, v ∈ K.verts) ∧ p ∈ cell K F := by
  obtain ⟨F, hb, hr, hc⟩ := exists_face_sublist_mem_cell K p
  exact ⟨F, hb, fun v hv => hr.subset hv, hc⟩

/-! ## The affine components

`AffineForm` is finite rational data; here it becomes an honest `AffineMap`, which is the
shape the max–min development consumes. -/

/-- A rational affine form, as an affine map. -/
def _root_.Workspace.Normativity.Contrib.PolyhedralProjection.AffineForm.toAffineMap
    (a : AffineForm d) : Pt d →ᵃ[ℝ] ℝ where
  toFun := a.eval
  linear :=
    { toFun := fun x => ∑ i, (a.coeff i : ℝ) * x i
      map_add' := fun x y => by
        simp only [PiLp.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      map_smul' := fun t x => by
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  map_vadd' := fun x v => by
    have hpt : ∀ i : Fin d, (a.coeff i : ℝ) * ((v + x) i)
        = (a.coeff i : ℝ) * v i + (a.coeff i : ℝ) * x i := fun i => by
      simp only [PiLp.add_apply]; ring
    simp only [vadd_eq_add, AffineForm.eval, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hpt i, Finset.sum_add_distrib]
    ring

theorem AffineForm.toAffineMap_apply (a : AffineForm d) (p : Pt d) :
    a.toAffineMap p = a.eval p := rfl

/-! ## The face enumeration

A finite list of faces: base a vertex, rest a sublist of the vertex list.  Coverage says
this list is enough. -/

/-- Every face with a vertex base and a sublist rest, enumerated. -/
def faceList (K : RationalPolytope d) : List (Face d) :=
  (K.verts.map fun b => K.verts.sublists.map fun r => Face.mk b r).flatten

theorem mem_faceList {K : RationalPolytope d} {F : Face d}
    (hb : F.base ∈ K.verts) (hr : F.rest.Sublist K.verts) : F ∈ faceList K := by
  rw [faceList, List.mem_flatten]
  refine ⟨K.verts.sublists.map fun r => Face.mk F.base r, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨F.base, hb, rfl⟩
  · exact List.mem_map.mpr ⟨F.rest, List.mem_sublists.mpr hr, rfl⟩

/-! ## The payoff -/

/-- **Each coordinate of the projection is piecewise affine**, with the enumerated faces'
rational pieces as its components and their cells as the closed pieces. -/
theorem isPiecewiseAffineOn_proj (K : RationalPolytope d) (i : Fin d) :
    IsPiecewiseAffineOn (Set.univ : Set (Pt d)) (fun p => K.proj p i)
      (fun l : Fin (faceList K).length => (((faceList K).get l).piece i).toAffineMap) := by
  refine isPiecewiseAffineOn_of_finite
    (fun l : Fin (faceList K).length => cell K ((faceList K).get l)) id
    (fun l => isClosed_cell K _) (fun p _ => ?_) (fun l x hx => ?_)
  · obtain ⟨F, hb, hr, hcell⟩ := exists_face_sublist_mem_cell K p
    obtain ⟨l, hl⟩ := List.mem_iff_get.mp (mem_faceList hb hr)
    exact Set.mem_iUnion.mpr ⟨l, by rw [hl]; exact hcell⟩
  · rw [← candidate_eq_proj_of_mem_cell K _ hx.1]
    rfl

/-- **The max–min representation of the projection.**  Ovchinnikov's theorem applied to the
piecewise-affine reading: each coordinate is a maximum of minima of rational affine forms
attached to the enumerated faces. -/
theorem exists_maxMin_proj (K : RationalPolytope d) (i : Fin d) :
    ∃ (m : ℕ) (S : Fin (m + 1) → Finset (Fin (faceList K).length))
      (hS : ∀ j, (S j).Nonempty),
      ∀ p : Pt d, K.proj p i = Finset.univ.sup' Finset.univ_nonempty
        fun j => (S j).inf' (hS j) fun l => (((faceList K).get l).piece i).eval p := by
  obtain ⟨m, S, hS, hrep⟩ :=
    exists_maxMin_representation (convex_univ (𝕜 := ℝ) (E := Pt d))
      ⟨0, Set.mem_univ 0⟩ (isPiecewiseAffineOn_proj K i)
  exact ⟨m, S, hS, fun p => hrep p (Set.mem_univ p)⟩

/-! ## Nonvacuity

`AGENTS.md` standard 3: the statements above ship with a term inhabiting their hypothesis
package.  `RationalPolytope` carries a real hypothesis — a nonempty vertex list — so the
witness is a concrete polytope, here the unit segment in one dimension, at a point outside
it. -/

/-- The unit segment, as a rational polytope. -/
def unitSegment : RationalPolytope 1 where
  verts := [fun _ => 0, fun _ => 1]
  verts_ne := List.cons_ne_nil _ _

/-- Coverage is about something: a two-vertex polytope and a point outside it. -/
theorem coverage_nonvacuous :
    ∃ F : Face 1, F.base ∈ unitSegment.verts ∧ (∀ v ∈ F.rest, v ∈ unitSegment.verts) ∧
      (toPt (fun _ => 2) : Pt 1) ∈ cell unitSegment F :=
  exists_face_mem_cell unitSegment (toPt fun _ => 2)

/-- The piecewise-affine reading is about something too: the segment has faces to be
piecewise affine over. -/
theorem faceList_unitSegment_ne_nil : faceList unitSegment ≠ [] := by
  intro h
  have hm : Face.mk (fun _ => 0) [] ∈ faceList unitSegment :=
    mem_faceList (by simp [unitSegment]) (List.nil_sublist _)
  rw [h] at hm
  simp at hm

end Workspace.Normativity.Contrib.PolyhedralCoverage

#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.sum_toFinset_eq_sum_fin
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.toPt_apply
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.toPt_injective
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.toPt_sub
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.dirs_apply
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.face_dir_apply
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.face_dir_eq_dirs
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.exists_vertex_dependence
#print axioms
  Workspace.Normativity.Contrib.PolyhedralCoverage.regular_and_candidate_of_linearIndependent
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.exists_regular_face_aux
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.exists_face_sublist_mem_cell
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.exists_face_mem_cell
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.AffineForm.toAffineMap_apply
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.mem_faceList
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.isPiecewiseAffineOn_proj
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.exists_maxMin_proj
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.coverage_nonvacuous
#print axioms Workspace.Normativity.Contrib.PolyhedralCoverage.faceList_unitSegment_ne_nil
