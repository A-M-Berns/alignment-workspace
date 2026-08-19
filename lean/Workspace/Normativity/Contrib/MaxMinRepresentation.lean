/-
# Max–min representation of piecewise affine functions

Ovchinnikov's theorem (*Max–Min Representation of Piecewise Linear Functions*,
Beiträge zur Algebra und Geometrie **43** (2002) 297–302; preprint
`arXiv:math/0009026`), Theorem 4.1(a): a piecewise affine function on a convex
domain is the maximum, over a finite family of subsets of its components, of the
minimum of that subset.

**What is proved here.**  `exists_maxMin_representation`: for `f` piecewise affine
on a convex `Γ` with components `g : ι → E →ᵃ[ℝ] ℝ`, there are finitely many
nonempty `S j ⊆ ι` with `f x = ⨆ j ⨅ i ∈ S j, g i x` on `Γ`.  Nothing is assumed
beyond convexity and nonemptiness of `Γ`: no full-dimensionality, no continuity of
`f` (which the closed pieces force), no finite dimension, and no norm.  The
converse, `isPiecewiseAffineOn_maxMin` (the source's Theorem 4.1(b)), and the
continuity the source asserts in passing, `continuousOn_of_isPiecewiseAffineOn`,
are proved as well.  The converse's proof was produced by Harmonic's Aristotle from
a statement and outline written here, then reviewed and rebuilt; the round's
`PROVENANCE.md` records that.

**Deviation from the source's proof.**  The paper argues through the hyperplane
arrangement `{gᵢ = gⱼ}`, its regions, and a tope-graph metric, and proves its key
lemma by induction along a chain of pairwise adjacent regions.  That chain needs a
genericity argument the paper states without proof ("we can always choose `p` and
`q` in such a way that different hyperplanes in `S(P,Q)` intersect `[p,q]` in
different points"), and it needs `∪T` dense in `Γ`, which fails when `Γ` has empty
interior.  The proof here restricts to the segment `[x,y]` instead and inducts on
the finitely many parameters at which two components cross on that segment
(`exists_le_of_le_of_forall_selects`).  On a line the ordering of the crossing
parameters replaces the tope graph, the base case needs only agreement at a single
crossing parameter rather than on a common facet, and the "positive on one open
halfspace, negative on the other" step becomes the monotonicity of an affine
function of one variable (`affine_le_of_lt_of_le`).  No arrangement, no
adjacency, no density, and no full-dimensionality hypothesis is needed.

**Definition.**  `IsPiecewiseAffineOn Γ f g` says: finitely many closed sets cover
`Γ`, and on each of them (intersected with `Γ`) `f` agrees with one of the `g i`.
The source's Definition 2.1 instead calls the affine function agreeing with `f` on
a piece *the* component of `f` there, which presumes it is unique; uniqueness fails
for a piece contained in a hyperplane, and the source never says a piece is
full-dimensional.  Taking the components as given data sidesteps that.

Names are provisional (`AGENTS.md` standard 6).
-/

import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic.LinearCombination

namespace Workspace.Normativity.Contrib.MaxMin

open Set

/-! ## Affine functions of one real variable

Two facts, both immediate from the normal form `δ t = (δ 1 - δ 0) * t + δ 0`: an
affine function of one variable is determined by its values at two points, and one
that is positive somewhere and nonpositive later stays nonpositive. -/

theorem affine_apply_eq_slope (δ : ℝ →ᵃ[ℝ] ℝ) (t : ℝ) : δ t = (δ 1 - δ 0) * t + δ 0 := by
  have h : δ t = (1 - t) * δ 0 + t * δ 1 := by
    simpa [AffineMap.lineMap_apply_ring] using δ.apply_lineMap (0 : ℝ) 1 t
  rw [h]; ring

/-- An affine function of one real variable is determined by its values at two
distinct points. -/
theorem affine_eq_of_ne {δ ε : ℝ →ᵃ[ℝ] ℝ} {p q : ℝ} (hpq : p ≠ q) (hp : δ p = ε p)
    (hq : δ q = ε q) (t : ℝ) : δ t = ε t := by
  have h1 := hp
  have h2 := hq
  rw [affine_apply_eq_slope δ p, affine_apply_eq_slope ε p] at h1
  rw [affine_apply_eq_slope δ q, affine_apply_eq_slope ε q] at h2
  have key : ((δ 1 - δ 0) - (ε 1 - ε 0)) * (p - q) = 0 := by linear_combination h1 - h2
  have hslope : δ 1 - δ 0 = ε 1 - ε 0 := by
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · exact absurd h (sub_ne_zero.mpr hpq)
  rw [hslope] at h1
  rw [affine_apply_eq_slope δ t, affine_apply_eq_slope ε t, hslope]
  linarith

/-- If `δ` exceeds `ε` at `a` but not at a later point `t`, it does not exceed it
anywhere from `t` on. -/
theorem affine_le_of_lt_of_le {δ ε : ℝ →ᵃ[ℝ] ℝ} {a t b : ℝ} (hat : a < t) (htb : t ≤ b)
    (ha : ε a < δ a) (ht : δ t ≤ ε t) : δ b ≤ ε b := by
  rw [affine_apply_eq_slope δ a, affine_apply_eq_slope ε a] at ha
  rw [affine_apply_eq_slope δ t, affine_apply_eq_slope ε t] at ht
  rw [affine_apply_eq_slope δ b, affine_apply_eq_slope ε b]
  nlinarith [ha, ht, hat, htb]

/-! ## Selecting one component on a connected set

If finitely many closed sets cover a preconnected `J`, `φ` agrees on each with one
member of a family of affine functions, and no two members of the family cross
inside `J` without being equal, then a single member agrees with `φ` on all of
`J`. -/

theorem exists_forall_eq_of_isPreconnected {ι : Type*} [Finite ι] {J : Set ℝ}
    (hJ : IsPreconnected J) (hJne : J.Nonempty) {D : ι → Set ℝ}
    (hDc : ∀ i, IsClosed (D i)) (hcov : J ⊆ ⋃ i, D i) {φ : ℝ → ℝ} {h : ι → ℝ →ᵃ[ℝ] ℝ}
    (hag : ∀ i, ∀ t ∈ D i ∩ J, φ t = h i t)
    (hcross : ∀ i j, ∀ t ∈ J, h i t = h j t → ∀ s, h i s = h j s) :
    ∃ i, ∀ t ∈ J, φ t = h i t := by
  classical
  obtain ⟨t₀, ht₀⟩ := hJne
  obtain ⟨i₀, hi₀⟩ : ∃ i, t₀ ∈ D i := mem_iUnion.mp (hcov ht₀)
  set U : Set ℝ := ⋃ j ∈ {j | ∀ s, h i₀ s = h j s}, D j
  set V : Set ℝ := ⋃ j ∈ {j | ¬ ∀ s, h i₀ s = h j s}, D j
  have hUc : IsClosed U := (toFinite _).isClosed_biUnion fun j _ => hDc j
  have hVc : IsClosed V := (toFinite _).isClosed_biUnion fun j _ => hDc j
  have hcovUV : J ⊆ U ∪ V := by
    intro t ht
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov ht)
    by_cases hP : ∀ s, h i₀ s = h j s
    · exact Or.inl (mem_biUnion hP hj)
    · exact Or.inr (mem_biUnion hP hj)
  have hUJ : (J ∩ U).Nonempty := ⟨t₀, ht₀, mem_biUnion (fun _ => rfl) hi₀⟩
  have hVJ : ¬ (J ∩ V).Nonempty := by
    intro hne
    obtain ⟨t, htJ, htU, htV⟩ := isPreconnected_closed_iff.mp hJ U V hUc hVc hcovUV hUJ hne
    obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp htU
    obtain ⟨k, hk, htk⟩ := mem_iUnion₂.mp htV
    have e1 : φ t = h j t := hag j t ⟨htj, htJ⟩
    have e2 : φ t = h k t := hag k t ⟨htk, htJ⟩
    exact hk fun s => (hj s).trans (hcross j k t htJ (e1.symm.trans e2) s)
  refine ⟨i₀, fun t ht => ?_⟩
  have htU : t ∈ U := by
    rcases hcovUV ht with h' | h'
    · exact h'
    · exact absurd ⟨t, ht, h'⟩ hVJ
  obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp htU
  rw [hag j t ⟨htj, ht⟩, hj t]

/-! ## The chain lemma

The one-dimensional heart of the proof.  `φ` selects, on every subinterval of
`[c, b]` free of breakpoints, one member of an affine family `h`; then some member
lies below `φ` at the left end and above `φ` at the right end.  Induction is on the
number of breakpoints strictly inside `[a, b]`. -/

theorem exists_le_of_le_of_forall_selects {ι : Type*} (h : ι → ℝ →ᵃ[ℝ] ℝ) (φ : ℝ → ℝ)
    (B : Finset ℝ) (c b : ℝ)
    (hsel : ∀ u v : ℝ, c ≤ u → u ≤ v → v ≤ b → (∀ t ∈ B, t ∉ Ioo u v) →
      ∃ i, ∀ t ∈ Icc u v, φ t = h i t) :
    ∀ (n : ℕ) (a : ℝ), c ≤ a → a ≤ b →
      (B.filter (fun t => t ∈ Ioo a b)).card ≤ n → ∃ i, h i a ≤ φ a ∧ φ b ≤ h i b := by
  classical
  have base : ∀ a : ℝ, c ≤ a → a ≤ b → (∀ t ∈ B, t ∉ Ioo a b) →
      ∃ i, h i a ≤ φ a ∧ φ b ≤ h i b := by
    intro a hca hab hno
    obtain ⟨i, hi⟩ := hsel a b hca hab le_rfl hno
    exact ⟨i, le_of_eq (hi a (left_mem_Icc.mpr hab)).symm,
      le_of_eq (hi b (right_mem_Icc.mpr hab))⟩
  intro n
  induction n with
  | zero =>
    intro a hca hab hcard
    refine base a hca hab fun t htB htio => ?_
    have : t ∈ B.filter (fun t => t ∈ Ioo a b) := Finset.mem_filter.mpr ⟨htB, htio⟩
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at this
    simp at this
  | succ n ih =>
    intro a hca hab hcard
    by_cases hfil : (B.filter (fun t => t ∈ Ioo a b)).Nonempty
    · set t₁ := (B.filter (fun t => t ∈ Ioo a b)).min' hfil with ht₁def
      have ht₁mem : t₁ ∈ B.filter (fun t => t ∈ Ioo a b) := Finset.min'_mem _ _
      have ht₁io : t₁ ∈ Ioo a b := (Finset.mem_filter.mp ht₁mem).2
      have hno : ∀ t ∈ B, t ∉ Ioo a t₁ := by
        intro t htB htio
        have hmem : t ∈ B.filter (fun t => t ∈ Ioo a b) :=
          Finset.mem_filter.mpr ⟨htB, ⟨htio.1, htio.2.trans ht₁io.2⟩⟩
        exact absurd (Finset.min'_le _ _ hmem) (not_le.mpr htio.2)
      obtain ⟨k₀, hk₀⟩ := hsel a t₁ hca (le_of_lt ht₁io.1) (le_of_lt ht₁io.2) hno
      have hsub : B.filter (fun t => t ∈ Ioo t₁ b) ⊂ B.filter (fun t => t ∈ Ioo a b) := by
        constructor
        · intro t ht
          obtain ⟨htB, htio⟩ := Finset.mem_filter.mp ht
          exact Finset.mem_filter.mpr ⟨htB, ⟨ht₁io.1.trans htio.1, htio.2⟩⟩
        · intro hcon
          have := hcon ht₁mem
          exact absurd (Finset.mem_filter.mp this).2.1 (lt_irrefl t₁)
      have hcard' : (B.filter (fun t => t ∈ Ioo t₁ b)).card ≤ n := by
        have := Finset.card_lt_card hsub
        omega
      obtain ⟨r, hr1, hr2⟩ := ih t₁ (hca.trans (le_of_lt ht₁io.1)) (le_of_lt ht₁io.2) hcard'
      have hφa : φ a = h k₀ a := hk₀ a (left_mem_Icc.mpr (le_of_lt ht₁io.1))
      have hφt₁ : φ t₁ = h k₀ t₁ := hk₀ t₁ (right_mem_Icc.mpr (le_of_lt ht₁io.1))
      by_cases hcase : h r a ≤ φ a
      · exact ⟨r, hcase, hr2⟩
      · refine ⟨k₀, le_of_eq hφa.symm, ?_⟩
        have hlt : h k₀ a < h r a := by rw [← hφa]; exact not_le.mp hcase
        have hle : h r t₁ ≤ h k₀ t₁ := by rw [← hφt₁]; exact hr1
        exact hr2.trans
          (affine_le_of_lt_of_le ht₁io.1 (le_of_lt ht₁io.2) hlt hle)
    · refine base a hca hab fun t htB htio => ?_
      exact hfil ⟨t, Finset.mem_filter.mpr ⟨htB, htio⟩⟩

/-! ## Piecewise affine functions -/

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- `f` is piecewise affine on `Γ` with components `g`: finitely many closed sets
cover `Γ`, and on each of them `f` agrees with one component. -/
def IsPiecewiseAffineOn (Γ : Set E) (f : E → ℝ) (g : ι → E →ᵃ[ℝ] ℝ) : Prop :=
  ∃ (m : ℕ) (Q : Fin m → Set E) (c : Fin m → ι),
    (∀ l, IsClosed (Q l)) ∧ Γ ⊆ ⋃ l, Q l ∧ ∀ l, ∀ x ∈ Q l ∩ Γ, f x = g (c l) x

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The pieces may be indexed by any finite type. -/
theorem isPiecewiseAffineOn_of_finite {κ : Type*} [Finite κ] {Γ : Set E} {f : E → ℝ}
    {g : ι → E →ᵃ[ℝ] ℝ} (Q : κ → Set E) (c : κ → ι) (hQc : ∀ l, IsClosed (Q l))
    (hcov : Γ ⊆ ⋃ l, Q l) (hQf : ∀ l, ∀ x ∈ Q l ∩ Γ, f x = g (c l) x) :
    IsPiecewiseAffineOn Γ f g := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  refine ⟨n, fun l => Q (e.symm l), fun l => c (e.symm l), fun l => hQc _, fun x hx => ?_,
    fun l => hQf _⟩
  obtain ⟨l, hl⟩ := mem_iUnion.mp (hcov hx)
  exact mem_iUnion.mpr ⟨e l, by simpa using hl⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- A piecewise affine function on a closed domain is continuous there.  The source
asserts this without proof ("Clearly, any piecewise linear function on `Γ` is
continuous"); it is the pasting lemma for a finite closed cover.  Continuity of the
components is automatic in finite dimension
(`AffineMap.continuous_of_finiteDimensional`). -/
theorem continuousOn_of_isPiecewiseAffineOn [Finite ι] {Γ : Set E} {f : E → ℝ}
    {g : ι → E →ᵃ[ℝ] ℝ} (hΓ : IsClosed Γ) (hg : ∀ i, Continuous (g i))
    (hf : IsPiecewiseAffineOn Γ f g) : ContinuousOn f Γ := by
  obtain ⟨m, Q, c, hQc, hcov, hQf⟩ := hf
  have hunion : ⋃ l, (Q l ∩ Γ) = Γ := by
    refine Subset.antisymm (iUnion_subset fun l => inter_subset_right) fun x hx => ?_
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨l, hl, hx⟩
  rw [← hunion]
  refine (locallyFinite_of_finite _).continuousOn_iUnion
    (fun l => (hQc l).inter hΓ) fun l => ?_
  exact ContinuousOn.congr (hg (c l)).continuousOn fun x hx => hQf l x hx

/-- **Lemma 4.1.**  For any two points of a convex domain there is a component
below `f` at the first and above `f` at the second. -/
theorem exists_le_and_le [Finite ι] {Γ : Set E} {f : E → ℝ} {g : ι → E →ᵃ[ℝ] ℝ}
    (hΓ : Convex ℝ Γ) (hf : IsPiecewiseAffineOn Γ f g) {x y : E} (hx : x ∈ Γ)
    (hy : y ∈ Γ) : ∃ i, g i x ≤ f x ∧ f y ≤ g i y := by
  classical
  obtain ⟨m, Q, c, hQc, hcov, hQf⟩ := hf
  set L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y with hL
  have hLcont : Continuous L := AffineMap.lineMap_continuous
  have hLmem : ∀ t ∈ Icc (0 : ℝ) 1, L t ∈ Γ := fun t ht => hΓ.lineMap_mem hx hy ht
  set h : ι → ℝ →ᵃ[ℝ] ℝ := fun i => (g i).comp L with hh
  set φ : ℝ → ℝ := fun t => f (L t) with hφ
  set D : ι → Set ℝ := fun i => ⋃ l ∈ {l | c l = i}, L ⁻¹' Q l
  have hDc : ∀ i, IsClosed (D i) :=
    fun i => (toFinite _).isClosed_biUnion fun l _ => (hQc l).preimage hLcont
  have hDcov : Icc (0 : ℝ) 1 ⊆ ⋃ i, D i := by
    intro t ht
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hcov (hLmem t ht))
    exact mem_iUnion.mpr ⟨c l, mem_biUnion rfl hl⟩
  have hag : ∀ i, ∀ t ∈ D i ∩ Icc (0 : ℝ) 1, φ t = h i t := by
    rintro i t ⟨htD, htI⟩
    obtain ⟨l, hl, htl⟩ := mem_iUnion₂.mp htD
    have hl' : c l = i := hl
    have := hQf l (L t) ⟨htl, hLmem t htI⟩
    simpa [hφ, hh, hl'] using this
  -- the finitely many parameters at which two distinct restricted components cross
  set S : Set ℝ := {t | ∃ i j, (¬ ∀ s, h i s = h j s) ∧ h i t = h j t} with hS
  have hSfin : S.Finite := by
    have hsub : S ⊆ ⋃ p : ι × ι, {t | h p.1 t = h p.2 t ∧ ¬ ∀ s, h p.1 s = h p.2 s} := by
      rintro t ⟨i, j, hne, heq⟩
      exact mem_iUnion.mpr ⟨(i, j), heq, hne⟩
    refine Set.Finite.subset (Set.finite_iUnion fun p => ?_) hsub
    apply Set.Subsingleton.finite
    rintro t₁ ⟨e1, hne⟩ t₂ ⟨e2, -⟩
    by_contra hne2
    exact hne fun s => affine_eq_of_ne hne2 e1 e2 s
  have hsel : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 →
      (∀ t ∈ hSfin.toFinset, t ∉ Ioo u v) → ∃ i, ∀ t ∈ Icc u v, φ t = h i t := by
    intro u v hu huv hv hno
    have hIcc : Icc u v ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hu hv
    have hcross : ∀ i j, ∀ t ∈ Ioo u v, h i t = h j t → ∀ s, h i s = h j s := by
      intro i j t ht heq
      by_contra hc
      exact hno t (hSfin.mem_toFinset.mpr ⟨i, j, hc, heq⟩) ht
    rcases eq_or_lt_of_le huv with rfl | hlt
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hDcov (hIcc (left_mem_Icc.mpr huv)))
      refine ⟨i, fun t ht => ?_⟩
      rw [Icc_self, mem_singleton_iff] at ht
      subst ht
      exact hag i t ⟨hi, hIcc (left_mem_Icc.mpr le_rfl)⟩
    · have hIoo : Ioo u v ⊆ Icc (0 : ℝ) 1 := (Ioo_subset_Icc_self).trans hIcc
      obtain ⟨i₀, hi₀⟩ := exists_forall_eq_of_isPreconnected isPreconnected_Ioo
        (nonempty_Ioo.mpr hlt) hDc (hIoo.trans hDcov)
        (fun i t ht => hag i t ⟨ht.1, hIoo ht.2⟩) hcross
      refine ⟨i₀, fun t ht => ?_⟩
      -- every point of the closed interval is in the closure of one piece meeting `Ioo u v`
      have hclos : Icc u v ⊆ ⋃ i, closure (D i ∩ Ioo u v) := by
        rw [← closure_Ioo (ne_of_lt hlt)]
        refine closure_minimal ?_ (isClosed_iUnion_of_finite fun i => isClosed_closure)
        intro s hs
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hDcov (hIoo hs))
        exact mem_iUnion.mpr ⟨i, subset_closure ⟨hi, hs⟩⟩
      obtain ⟨i₁, hi₁⟩ := mem_iUnion.mp (hclos ht)
      have htD : t ∈ D i₁ := (hDc i₁).closure_subset
        (closure_mono (inter_subset_left) hi₁)
      obtain ⟨s₀, hs₀⟩ : (D i₁ ∩ Ioo u v).Nonempty := by
        rcases Set.eq_empty_or_nonempty (D i₁ ∩ Ioo u v) with hemp | hne'
        · rw [hemp, closure_empty] at hi₁; simp at hi₁
        · exact hne'
      have hcs : h i₁ s₀ = h i₀ s₀ := by
        rw [← hag i₁ s₀ ⟨hs₀.1, hIoo hs₀.2⟩, hi₀ s₀ hs₀.2]
      rw [hag i₁ t ⟨htD, hIcc ht⟩, hcross i₁ i₀ s₀ hs₀.2 hcs t]
  obtain ⟨i, h0, h1⟩ := exists_le_of_le_of_forall_selects h φ hSfin.toFinset 0 1 hsel
    (hSfin.toFinset.filter (fun t => t ∈ Ioo (0 : ℝ) 1)).card 0 le_rfl zero_le_one le_rfl
  refine ⟨i, ?_, ?_⟩
  · simpa [hφ, hh, hL] using h0
  · simpa [hφ, hh, hL] using h1

/-! ## The representation -/

/-- **Theorem 4.1(a).**  A piecewise affine function on a nonempty convex domain is
a maximum of minima of its components. -/
theorem exists_maxMin_representation [Finite ι] {Γ : Set E} {f : E → ℝ}
    {g : ι → E →ᵃ[ℝ] ℝ} (hΓ : Convex ℝ Γ) (hne : Γ.Nonempty)
    (hf : IsPiecewiseAffineOn Γ f g) :
    ∃ (m : ℕ) (S : Fin (m + 1) → Finset ι) (hS : ∀ j, (S j).Nonempty),
      ∀ x ∈ Γ, f x = Finset.univ.sup' Finset.univ_nonempty
        fun j => (S j).inf' (hS j) fun i => g i x := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨m₀, Q, c, hQc, hcov, hQf⟩ := hf
  have hfa : IsPiecewiseAffineOn Γ f g := ⟨m₀, Q, c, hQc, hcov, hQf⟩
  -- the components at least as large as `f` at a point
  set up : E → Finset ι := fun y => Finset.univ.filter (fun i => f y ≤ g i y) with hup
  have hmem_up : ∀ y i, i ∈ up y ↔ f y ≤ g i y := by
    intro y i; simp [hup]
  have hattain : ∀ y ∈ Γ, ∃ i, f y = g i y := by
    intro y hy
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hcov hy)
    exact ⟨c l, hQf l y ⟨hl, hy⟩⟩
  have hup_ne : ∀ y ∈ Γ, (up y).Nonempty := by
    intro y hy
    obtain ⟨i, hi⟩ := hattain y hy
    exact ⟨i, (hmem_up y i).mpr (le_of_eq hi)⟩
  -- enumerate the finitely many sets that occur
  obtain ⟨y₀, hy₀⟩ := hne
  set A : Finset (Finset ι) := Finset.univ.filter (fun T => ∃ y ∈ Γ, up y = T) with hA
  have hmem_A : ∀ T, T ∈ A ↔ ∃ y ∈ Γ, up y = T := by intro T; simp [hA]
  have hAne : A.Nonempty := ⟨up y₀, (hmem_A _).mpr ⟨y₀, hy₀, rfl⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, A.card = m + 1 := ⟨A.card - 1, by
    have := Finset.card_pos.mpr hAne; omega⟩
  have hcardA : Fintype.card {T // T ∈ A} = m + 1 := by rw [Fintype.card_coe, hm]
  set e := Fintype.equivFinOfCardEq hcardA with he
  set S : Fin (m + 1) → Finset ι := fun j => (e.symm j).1 with hSdef
  have hSA : ∀ j, S j ∈ A := fun j => (e.symm j).2
  have hSwit : ∀ j, ∃ y ∈ Γ, up y = S j := fun j => (hmem_A _).mp (hSA j)
  have hS : ∀ j, (S j).Nonempty := by
    intro j
    obtain ⟨y, hy, hyj⟩ := hSwit j
    exact hyj ▸ hup_ne y hy
  refine ⟨m, S, hS, fun x hx => ?_⟩
  refine le_antisymm ?_ ?_
  · have hxA : up x ∈ A := (hmem_A _).mpr ⟨x, hx, rfl⟩
    have hj : S (e ⟨up x, hxA⟩) = up x := by simp [hSdef]
    refine le_trans ?_ (Finset.le_sup'
      (fun j => (S j).inf' (hS j) fun i => g i x) (Finset.mem_univ (e ⟨up x, hxA⟩)))
    refine Finset.le_inf' _ _ fun i hi => ?_
    rw [hj] at hi
    exact (hmem_up x i).mp hi
  · refine Finset.sup'_le _ _ fun j _ => ?_
    obtain ⟨y, hy, hyj⟩ := hSwit j
    obtain ⟨i, hix, hiy⟩ := exists_le_and_le hΓ hfa hx hy
    have hiS : i ∈ S j := hyj ▸ (hmem_up y i).mpr hiy
    exact (Finset.inf'_le _ hiS).trans hix


/-! ## The converse

Theorem 4.1(b).  Proved by Aristotle (Harmonic) from the statement and outline in
this round's report; reviewed and rebuilt here. -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Theorem 4.1(b).**  A max of mins of affine functions is piecewise affine, on
any domain. -/
theorem isPiecewiseAffineOn_maxMin [Finite ι] {Γ : Set E} {g : ι → E →ᵃ[ℝ] ℝ}
    (hg : ∀ i, Continuous (g i)) {m : ℕ} (S : Fin (m + 1) → Finset ι)
    (hS : ∀ j, (S j).Nonempty) :
    IsPiecewiseAffineOn Γ
      (fun x => Finset.univ.sup' Finset.univ_nonempty fun j => (S j).inf' (hS j) fun i => g i x)
      g := by
  classical
  refine isPiecewiseAffineOn_of_finite (κ := Fin (m + 1) × ι × (Fin (m + 1) → ι))
    (fun p => if p.2.1 ∈ S p.1 ∧ ∀ j', p.2.2 j' ∈ S j' then
        {x | (∀ i' ∈ S p.1, g p.2.1 x ≤ g i' x) ∧ ∀ j', g (p.2.2 j') x ≤ g p.2.1 x}
      else ∅)
    (fun p => p.2.1) ?_ ?_ ?_
  · rintro ⟨j, i, k⟩
    dsimp only
    by_cases hgood : i ∈ S j ∧ ∀ j', k j' ∈ S j'
    · rw [if_pos hgood]
      have hset : {x | (∀ i' ∈ S j, g i x ≤ g i' x) ∧ ∀ j', g (k j') x ≤ g i x} =
          (⋂ i' ∈ (S j : Set ι), {x | g i x ≤ g i' x}) ∩ ⋂ j', {x | g (k j') x ≤ g i x} := by
        ext x; simp [Set.mem_iInter]
      rw [hset]
      exact (isClosed_biInter fun i' _ => isClosed_le (hg i) (hg i')).inter
        (isClosed_iInter fun j' => isClosed_le (hg _) (hg i))
    · rw [if_neg hgood]
      exact isClosed_empty
  · intro x _
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (m + 1)))
      fun j => (S j).inf' (hS j) fun i => g i x
    obtain ⟨i, hiS, hi⟩ := Finset.exists_mem_eq_inf' (hS j) fun i => g i x
    have hk : ∀ j' : Fin (m + 1), ∃ i' ∈ S j', (S j').inf' (hS j') (fun i => g i x) = g i' x :=
      fun j' => Finset.exists_mem_eq_inf' (hS j') fun i => g i x
    choose k hkS hkeq using hk
    refine Set.mem_iUnion.mpr ⟨⟨j, i, k⟩, ?_⟩
    dsimp only
    have hgood : i ∈ S j ∧ ∀ j', k j' ∈ S j' := ⟨hiS, hkS⟩
    rw [if_pos hgood]
    constructor
    · intro i' hi'
      rw [← hi]
      exact Finset.inf'_le _ hi'
    · intro j'
      rw [← hkeq j', ← hi, ← hj]
      exact Finset.le_sup' (fun j => (S j).inf' (hS j) fun i => g i x) (Finset.mem_univ j')
  · rintro ⟨j, i, k⟩ x ⟨hxQ, -⟩
    dsimp only at hxQ ⊢
    by_cases hgood : i ∈ S j ∧ ∀ j', k j' ∈ S j'
    · rw [if_pos hgood] at hxQ
      obtain ⟨h1, h2⟩ := hxQ
      refine le_antisymm (Finset.sup'_le _ _ fun j' _ => ?_) ?_
      · exact le_trans (Finset.inf'_le _ (hgood.2 j')) (h2 j')
      · refine le_trans ?_ (Finset.le_sup' (α := ℝ) _ (Finset.mem_univ j))
        exact Finset.le_inf' _ _ fun i' hi' => h1 i' hi'
    · rw [if_neg hgood] at hxQ
      exact absurd hxQ (Set.notMem_empty x)

/-! ## The source's arrangement can be empty

Section 2 of the source asserts that the arrangement `H` — the hyperplanes
`{gᵢ = gⱼ}` meeting `interior Γ` — is nonempty as soon as `f` has two distinct
components, and the proof of Theorem 4.1(a) ends by density of the union of the
regions of `H` in `Γ`.  On a closed convex domain with empty interior no hyperplane
meets `interior Γ`, so `H` is empty, the family of regions is empty, and its union
is not dense.  Here is such a domain carrying a piecewise affine function with two
distinct components; `exists_maxMin_representation` applies to it unchanged. -/

/-- The segment `[0,1] × {0}` in the plane. -/
def segmentDomain : Set (ℝ × ℝ) := Icc 0 1 ×ˢ {0}

/-- Two distinct affine functions on the plane, `x₁ - 1/2` and `1/2 - x₁`. -/
noncomputable def segmentComponent : Fin 2 → ((ℝ × ℝ) →ᵃ[ℝ] ℝ) := fun l =>
  if l = 0 then (LinearMap.fst ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ (ℝ × ℝ) (1 / 2)
  else AffineMap.const ℝ (ℝ × ℝ) (1 / 2) - (LinearMap.fst ℝ ℝ ℝ).toAffineMap

theorem segmentComponent_zero (p : ℝ × ℝ) : segmentComponent 0 p = p.1 - 1 / 2 := by
  simp [segmentComponent]

theorem segmentComponent_one (p : ℝ × ℝ) : segmentComponent 1 p = 1 / 2 - p.1 := by
  simp [segmentComponent]

theorem segment_hypotheses :
    Convex ℝ segmentDomain ∧ IsClosed segmentDomain ∧ segmentDomain.Nonempty ∧
      interior segmentDomain = ∅ ∧ segmentComponent 0 ≠ segmentComponent 1 ∧
      IsPiecewiseAffineOn segmentDomain (fun p => |p.1 - 1 / 2|) segmentComponent := by
  refine ⟨(convex_Icc 0 1).prod (convex_singleton 0), isClosed_Icc.prod isClosed_singleton,
    ⟨(0, 0), by norm_num [segmentDomain]⟩, ?_, ?_, ?_⟩
  · simp [segmentDomain, interior_prod_eq]
  · intro hcon
    have hval := congrArg (fun a => a ((1 : ℝ), (0 : ℝ))) hcon
    rw [segmentComponent_zero, segmentComponent_one] at hval
    norm_num at hval
  · refine ⟨2, fun l => if l = 0 then Ici (1 / 2) ×ˢ univ else Iic (1 / 2) ×ˢ univ, id,
      fun l => ?_, fun p hp => ?_, fun l p hp => ?_⟩
    · by_cases h : l = 0 <;>
        simp [h, isClosed_Ici.prod isClosed_univ, isClosed_Iic.prod isClosed_univ]
    · rcases le_total (1 / 2 : ℝ) p.1 with h | h
      · exact mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact mem_iUnion.mpr ⟨1, by simpa using h⟩
    · by_cases h : l = 0
      · subst h
        have hp1 : (1 / 2 : ℝ) ≤ p.1 := by simpa using hp.1
        show |p.1 - 1 / 2| = segmentComponent 0 p
        rw [segmentComponent_zero, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1 - 1 / 2)]
      · have hl : l = 1 := by omega
        subst hl
        have hp1 : p.1 ≤ (1 / 2 : ℝ) := by simpa using hp.1
        show |p.1 - 1 / 2| = segmentComponent 1 p
        rw [segmentComponent_one, abs_of_nonpos (by linarith : p.1 - 1 / 2 ≤ (0 : ℝ))]
        ring

/-! ## A nonvacuity witness

A term inhabiting the full hypothesis package of `exists_maxMin_representation`:
the absolute value on `ℝ`, with components `x` and `-x` and pieces `Ici 0` and
`Iic 0`. -/

/-- `x ↦ -x`, as an affine map. -/
def negLine : ℝ →ᵃ[ℝ] ℝ where
  toFun x := -x
  linear := -LinearMap.id
  map_vadd' p v := by simp; ring

/-- The two components of `|·|`. -/
def absComponent : Fin 2 → (ℝ →ᵃ[ℝ] ℝ) := fun l => if l = 0 then AffineMap.id ℝ ℝ else negLine

/-- The two pieces of `|·|`. -/
def absPiece : Fin 2 → Set ℝ := fun l => if l = 0 then Ici 0 else Iic 0

theorem abs_isPiecewiseAffineOn :
    IsPiecewiseAffineOn (univ : Set ℝ) (fun x => |x|) absComponent := by
  refine ⟨2, absPiece, id, fun l => ?_, fun x _ => ?_, fun l x hx => ?_⟩
  · by_cases h : l = 0 <;> simp [absPiece, h, isClosed_Ici, isClosed_Iic]
  · rcases le_total 0 x with h | h
    · exact mem_iUnion.mpr ⟨0, by simp [absPiece, h]⟩
    · exact mem_iUnion.mpr ⟨1, by simp [absPiece, h]⟩
  · by_cases h : l = 0
    · have hx0 : (0 : ℝ) ≤ x := by simpa [absPiece, h] using hx.1
      simp [absComponent, h, abs_of_nonneg hx0]
    · have hx0 : x ≤ (0 : ℝ) := by simpa [absPiece, h] using hx.1
      simp [absComponent, h, negLine, abs_of_nonpos hx0]

/-- The hypotheses of `exists_maxMin_representation` are satisfiable. -/
theorem maxMin_hypotheses_nonvacuous :
    Convex ℝ (univ : Set ℝ) ∧ (univ : Set ℝ).Nonempty ∧
      IsPiecewiseAffineOn (univ : Set ℝ) (fun x => |x|) absComponent :=
  ⟨convex_univ, univ_nonempty, abs_isPiecewiseAffineOn⟩

end Workspace.Normativity.Contrib.MaxMin

#print axioms Workspace.Normativity.Contrib.MaxMin.affine_apply_eq_slope
#print axioms Workspace.Normativity.Contrib.MaxMin.affine_eq_of_ne
#print axioms Workspace.Normativity.Contrib.MaxMin.affine_le_of_lt_of_le
#print axioms Workspace.Normativity.Contrib.MaxMin.exists_forall_eq_of_isPreconnected
#print axioms Workspace.Normativity.Contrib.MaxMin.exists_le_of_le_of_forall_selects
#print axioms Workspace.Normativity.Contrib.MaxMin.isPiecewiseAffineOn_of_finite
#print axioms Workspace.Normativity.Contrib.MaxMin.continuousOn_of_isPiecewiseAffineOn
#print axioms Workspace.Normativity.Contrib.MaxMin.exists_le_and_le
#print axioms Workspace.Normativity.Contrib.MaxMin.exists_maxMin_representation
#print axioms Workspace.Normativity.Contrib.MaxMin.isPiecewiseAffineOn_maxMin
#print axioms Workspace.Normativity.Contrib.MaxMin.abs_isPiecewiseAffineOn
#print axioms Workspace.Normativity.Contrib.MaxMin.maxMin_hypotheses_nonvacuous
#print axioms Workspace.Normativity.Contrib.MaxMin.segmentComponent_zero
#print axioms Workspace.Normativity.Contrib.MaxMin.segmentComponent_one
#print axioms Workspace.Normativity.Contrib.MaxMin.segment_hypotheses
