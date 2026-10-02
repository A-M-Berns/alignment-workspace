import Cleanroom.Bli.BliFinite.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# `bli-finite` · Superbelief: `IsProb`, `mean`, `Balanced`, faces, `NonDegenerate` (T5)

Roman's *superbelief* (bli-slides-019) is a vector over the grid of possible next-day tables;
constraint 5 is normalization (`IsProb`), constraint 4 is "the mean table is the current
table" (`Balanced`). Design decisions of record (mandate 4–6):

* a superbelief is a **total** function `Table 𝒮 m → ℚ`; `IsProb` carries an explicit
  **off-grid support clause** (without it, off-grid mass makes `mean` wrong while the grid sum
  still reads 1);
* `Balanced` compares the day-`(m+1)` mean, restricted, to the day-`m` table — on day `m`'s
  sentences only ("mean over the wrong small set" is the program's named risk);
* two faces: `faceProd` (the grid tables agreeing with `t` wherever `t` is 0 or 1) and
  `faceGen` (the grid points carrying positive mass in *some* balance solution). With this
  `faceGen`, "every balance solution is supported inside `faceGen`" is **definitional** (kind
  `T`); the content of the face theorem is `faceProd = faceGen` (T7, `Tent.lean`).

Note on `Superbelief`: the mandate spells it `Superbelief 𝒮 d m`, but the type does not
depend on `d` (a phantom parameter cannot be inferred from a function type), so it is
`Superbelief 𝒮 m` here and `d` is an explicit argument of `IsProb`/`mean`/`Balanced`.

Sources: bli-slides-017 (constraints 4–5), 018 (`NonDegenerate`, in its surviving face form),
019 (vector, "norm", convolution, linearity); [[bli-program]] §2.4.
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction Finset

variable {𝒮 : SmallIndex} {m : ℕ}

/-- **Superbelief**: a rational weight on every day-`m` table (Roman's `F⃗`, bli-slides-019).
Support in the grid is the separate predicate `IsProb`.
Source: bli-slides-019; [[bli-program]] §2.4
Kind: D
Fidelity: variant: total function with a support clause, in place of a function on the grid -/
abbrev Superbelief (𝒮 : SmallIndex) (m : ℕ) : Type := Table 𝒮 m → ℚ

/-! ## Probability on a finite carrier (general form, reused for trajectory laws) -/

/-- `F` is a probability supported on the finite set `G`: nonnegative, **zero off `G`**, total
mass one on `G`.
Source: bli-slides-017 constraint 5 (+ the support clause, mandate design decision 4)
Kind: D
Fidelity: exact -/
def IsProbOn {α : Type} (G : Finset α) (F : α → ℚ) : Prop :=
  (∀ x, 0 ≤ F x) ∧ (∀ x, x ∉ G → F x = 0) ∧ ∑ x ∈ G, F x = 1

/-- Total mass on `G` (Roman's `|F⃗| = ∑ F^i`, bli-slides-019 — a *linear functional*, not a
norm, on signed vectors).
Source: bli-slides-019
Kind: D
Fidelity: exact -/
def massOn {α : Type} (G : Finset α) (F : α → ℚ) : ℚ := ∑ x ∈ G, F x

/-- The mean table of `F` over the carrier `G` (Roman's convolution `C[F⃗](φ) = ∑ F^i 𝒬_i(φ)`).
Source: bli-slides-019
Kind: D
Fidelity: exact -/
def meanOn (G : Finset (Table 𝒮 m)) (F : Superbelief 𝒮 m) : Table 𝒮 m :=
  fun φ => ∑ Q ∈ G, F Q * Q φ

/-! ## The grid instances -/

/-- `F` is a probability on the day-`m` product grid.
Source: bli-slides-017 constraint 5; mandate design decision 4
Kind: D
Fidelity: exact -/
def IsProb (d : ℕ → ℕ) (F : Superbelief 𝒮 m) : Prop := IsProbOn (grid 𝒮 d m) F

/-- Total mass on the grid.
Source: bli-slides-019
Kind: D
Fidelity: exact -/
def mass (d : ℕ → ℕ) (F : Superbelief 𝒮 m) : ℚ := massOn (grid 𝒮 d m) F

/-- The mean table over the grid.
Source: bli-slides-019; bli-paper-037 (the right-hand side of constraint 4)
Kind: D
Fidelity: exact -/
def mean (d : ℕ → ℕ) (F : Superbelief 𝒮 m) : Table 𝒮 m := meanOn (grid 𝒮 d m) F

/-- **Balance (constraint 4)**: the mean of a day-`(m+1)` superbelief, restricted to the
day-`m` sentences, is the day-`m` table. Kernels go `m → m+1`; the mean lives on day `m+1` and
is compared on day `m`'s sentences only.
Source: bli-paper-037 (`𝐏_{n-1}(φ) = ∑_Q 𝐏_{n-1}(𝐐_n = Q) Q[φ]`); bli-slides-017 constraint 4
Kind: D
Fidelity: exact -/
def Balanced (d : ℕ → ℕ) (F : Superbelief 𝒮 (m + 1)) (t : Table 𝒮 m) : Prop :=
  ∀ φ : ↥(𝒮.S m), (mean d F).restrict φ = t φ

/-- **Product face** of the day-`(m+1)` grid over the day-`m` table `t`: the grid tables agreeing
with `t` on every day-`m` sentence that `t` prices exactly 0 or 1. Computed on day `(m+1)`'s
grid, pinned by day `m`'s table.
Source: bli-slides-021 (the surviving weakening of full support); [[bli-program]] §2.4
Kind: D
Fidelity: exact -/
def faceProd (𝒮 : SmallIndex) (d : ℕ → ℕ) (m : ℕ) (t : Table 𝒮 m) : Finset (Table 𝒮 (m + 1)) :=
  (grid 𝒮 d (m + 1)).filter
    (fun Q => ∀ φ : ↥(𝒮.S m), (t φ = 0 ∨ t φ = 1) → Q.restrict φ = t φ)

/-- **Non-degeneracy** (the surviving form of "full support", bli-slides-018): positive mass on
every point of the product face.
Source: bli-slides-018 (desideratum), 021 (why not the whole grid); [[bli-program]] §2.4
Kind: D
Fidelity: variant: face form in place of full support on `D^S` (disclosed) -/
def NonDegenerate (d : ℕ → ℕ) (F : Superbelief 𝒮 (m + 1)) (t : Table 𝒮 m) : Prop :=
  ∀ Q ∈ faceProd 𝒮 d m t, 0 < F Q

section FaceGen
open Classical

/-- **Generated face** of a finite carrier `G` over `t`: the points of `G` carrying positive mass
in *some* probability on `G` whose restricted mean is `t` (the minimal face of `conv G`
containing `t`, without convex-geometry API). **With this definition, "every balance solution is
supported inside the face" is definitional**; the content downstream (`bli-superbelief` E1) is
the existence of a solution supported on all of it, and `faceProd = faceGen` on the product
grid (T7).
Source: [[bli-program]] §3.4 (face theorem, general grids); mandate design decision 6
Kind: D
Fidelity: exact -/
noncomputable def faceGen (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m) :
    Finset (Table 𝒮 (m + 1)) :=
  G.filter (fun Q => ∃ F : Superbelief 𝒮 (m + 1), IsProbOn G F ∧ (meanOn G F).restrict = t ∧ 0 < F Q)

/-! ## Linearity (bli-slides-019) -/

/-- The mean is additive in the superbelief.
Source: bli-slides-019 (linearity of `C`)
Kind: L
Fidelity: exact -/
lemma meanOn_add (G : Finset (Table 𝒮 m)) (F₁ F₂ : Superbelief 𝒮 m) :
    meanOn G (F₁ + F₂) = meanOn G F₁ + meanOn G F₂ := by
  funext φ; simp [meanOn, add_mul, Finset.sum_add_distrib]

/-- The mean is homogeneous in the superbelief.
Source: bli-slides-019
Kind: L
Fidelity: exact -/
lemma meanOn_smul (G : Finset (Table 𝒮 m)) (c : ℚ) (F : Superbelief 𝒮 m) :
    meanOn G (c • F) = c • meanOn G F := by
  funext φ; simp [meanOn, Finset.mul_sum, mul_assoc]

/-- The mass is additive (Roman's `|αF₁ + βF₂| = α|F₁| + β|F₂|`; `|·|` is a linear functional,
not a norm).
Source: bli-slides-019
Kind: L
Fidelity: exact -/
lemma massOn_add {α : Type} (G : Finset α) (F₁ F₂ : α → ℚ) :
    massOn G (F₁ + F₂) = massOn G F₁ + massOn G F₂ := by
  simp [massOn, Finset.sum_add_distrib]

/-- The mass is homogeneous.
Source: bli-slides-019
Kind: L
Fidelity: exact -/
lemma massOn_smul {α : Type} (G : Finset α) (c : ℚ) (F : α → ℚ) :
    massOn G (c • F) = c * massOn G F := by
  simp [massOn, Finset.mul_sum]

/-- Grid form of `meanOn_add`.
Source: bli-slides-019
Kind: L
Fidelity: exact -/
lemma mean_add (d : ℕ → ℕ) (F₁ F₂ : Superbelief 𝒮 m) :
    mean d (F₁ + F₂) = mean d F₁ + mean d F₂ := meanOn_add _ _ _

/-- Grid form of `meanOn_smul`.
Source: bli-slides-019
Kind: L
Fidelity: exact -/
lemma mean_smul (d : ℕ → ℕ) (c : ℚ) (F : Superbelief 𝒮 m) :
    mean d (c • F) = c • mean d F := meanOn_smul _ _ _

/-- Grid form of `massOn_add`.
Source: bli-slides-019
Kind: L
Fidelity: exact -/
lemma mass_add (d : ℕ → ℕ) (F₁ F₂ : Superbelief 𝒮 m) :
    mass d (F₁ + F₂) = mass d F₁ + mass d F₂ := massOn_add _ _ _

/-- Grid form of `massOn_smul`.
Source: bli-slides-019
Kind: L
Fidelity: exact -/
lemma mass_smul (d : ℕ → ℕ) (c : ℚ) (F : Superbelief 𝒮 m) :
    mass d (c • F) = c * mass d F := massOn_smul _ _ _

/-! ## Basic consequences -/

/-- A probability on `G` has mass one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma IsProbOn.massOn_eq_one {α : Type} {G : Finset α} {F : α → ℚ} (h : IsProbOn G F) :
    massOn G F = 1 := h.2.2

/-- Positive mass only on the carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma IsProbOn.mem_of_pos {α : Type} {G : Finset α} {F : α → ℚ} (h : IsProbOn G F) {x : α}
    (hx : 0 < F x) : x ∈ G := by
  by_contra hn
  have := h.2.1 x hn
  linarith

/-- The mean of a probability whose carrier lies in the unit cube lies in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma IsProbOn.meanOn_mem_Icc {G : Finset (Table 𝒮 m)} {F : Superbelief 𝒮 m}
    (h : IsProbOn G F) (hG : ∀ Q ∈ G, Q.InUnit) (φ : ↥(𝒮.S m)) :
    0 ≤ meanOn G F φ ∧ meanOn G F φ ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun Q hQ => mul_nonneg (h.1 Q) (hG Q hQ φ).1
  · calc meanOn G F φ = ∑ Q ∈ G, F Q * Q φ := rfl
      _ ≤ ∑ Q ∈ G, F Q :=
        Finset.sum_le_sum fun Q hQ => mul_le_of_le_one_right (h.1 Q) (hG Q hQ φ).2
      _ = 1 := h.2.2

/-- The mean of a grid probability lies in `[0,1]`.
Source: bli-slides-020 (the hull of the grid is the cube)
Kind: L
Fidelity: exact -/
lemma IsProb.mean_mem_Icc {d : ℕ → ℕ} {F : Superbelief 𝒮 m} (h : IsProb d F) (φ : ↥(𝒮.S m)) :
    0 ≤ mean d F φ ∧ mean d F φ ≤ 1 :=
  h.meanOn_mem_Icc (fun _ hQ => inUnit_of_mem_grid hQ) φ

/-- A balanced superbelief's restricted mean *is* the table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Balanced.restrict_mean_eq {d : ℕ → ℕ} {F : Superbelief 𝒮 (m + 1)} {t : Table 𝒮 m}
    (h : Balanced d F t) : (mean d F).restrict = t :=
  funext h

/-- Balance in the `faceGen` spelling.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma balanced_iff_restrict_meanOn_eq {d : ℕ → ℕ} {F : Superbelief 𝒮 (m + 1)} {t : Table 𝒮 m} :
    Balanced d F t ↔ (meanOn (grid 𝒮 d (m + 1)) F).restrict = t :=
  ⟨fun h => funext h, fun h φ => congrFun h φ⟩

/-! ## Faces -/

/-- Membership in the product face.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_faceProd_iff {d : ℕ → ℕ} {t : Table 𝒮 m} {Q : Table 𝒮 (m + 1)} :
    Q ∈ faceProd 𝒮 d m t ↔
      Q ∈ grid 𝒮 d (m + 1) ∧ ∀ φ : ↥(𝒮.S m), (t φ = 0 ∨ t φ = 1) → Q.restrict φ = t φ := by
  unfold faceProd; exact Finset.mem_filter

/-- Membership in the generated face.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_faceGen_iff {G : Finset (Table 𝒮 (m + 1))} {t : Table 𝒮 m} {Q : Table 𝒮 (m + 1)} :
    Q ∈ faceGen G t ↔
      Q ∈ G ∧ ∃ F : Superbelief 𝒮 (m + 1), IsProbOn G F ∧ (meanOn G F).restrict = t ∧ 0 < F Q := by
  unfold faceGen; exact Finset.mem_filter

/-- The product face is a subset of the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceProd_subset_grid (d : ℕ → ℕ) (t : Table 𝒮 m) : faceProd 𝒮 d m t ⊆ grid 𝒮 d (m + 1) :=
  Finset.filter_subset _ _

/-- The generated face is a subset of its carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceGen_subset (G : Finset (Table 𝒮 (m + 1))) (t : Table 𝒮 m) : faceGen G t ⊆ G :=
  Finset.filter_subset _ _

/-- **Every balance solution is supported inside `faceGen`** — definitional with this `faceGen`
(kind `T`; recorded so that auditors see it is not a theorem).
Source: mandate design decision 6
Kind: T
Fidelity: n/a -/
lemma mem_faceGen_of_pos {G : Finset (Table 𝒮 (m + 1))} {t : Table 𝒮 m} {F : Superbelief 𝒮 (m + 1)}
    (hF : IsProbOn G F) (hb : (meanOn G F).restrict = t) {Q : Table 𝒮 (m + 1)} (hQ : 0 < F Q) :
    Q ∈ faceGen G t :=
  mem_faceGen_iff.mpr ⟨hF.mem_of_pos hQ, F, hF, hb, hQ⟩

/-! ## The mechanism behind bli-slides-021 / E5 -/

/-- **Pinning at 1.** If a probability on a carrier of `[0,1]`-valued coordinates has mean exactly
`1` at coordinate `φ`, every point carrying positive mass has `Q φ = 1`.
Source: bli-slides-021 (the two-line derivation, made a lemma)
Kind: P
Fidelity: exact
Hyps: (a) all -/
lemma IsProbOn.coord_eq_one_of_meanOn_eq_one {G : Finset (Table 𝒮 m)} {F : Superbelief 𝒮 m}
    (h : IsProbOn G F) (hG : ∀ Q ∈ G, Q.InUnit) {φ : ↥(𝒮.S m)} (h1 : meanOn G F φ = 1)
    {Q : Table 𝒮 m} (hQ : 0 < F Q) : Q φ = 1 := by
  have hQG : Q ∈ G := h.mem_of_pos hQ
  have hle : ∀ Q ∈ G, F Q * Q φ ≤ F Q :=
    fun Q hQ => mul_le_of_le_one_right (h.1 Q) (hG Q hQ φ).2
  have hsum : ∑ Q ∈ G, F Q * Q φ = ∑ Q ∈ G, F Q := by
    change meanOn G F φ = _ at h1 ⊢
    rw [h1, h.2.2]
  have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum Q hQG
  exact (mul_right_eq_self₀.mp this).resolve_right hQ.ne'

/-- **Pinning at 0.** If a probability on a carrier of `[0,1]`-valued coordinates has mean exactly
`0` at coordinate `φ`, every point carrying positive mass has `Q φ = 0`.
Source: bli-slides-021 (dual case)
Kind: P
Fidelity: exact
Hyps: (a) all -/
lemma IsProbOn.coord_eq_zero_of_meanOn_eq_zero {G : Finset (Table 𝒮 m)} {F : Superbelief 𝒮 m}
    (h : IsProbOn G F) (hG : ∀ Q ∈ G, Q.InUnit) {φ : ↥(𝒮.S m)} (h0 : meanOn G F φ = 0)
    {Q : Table 𝒮 m} (hQ : 0 < F Q) : Q φ = 0 := by
  have hQG : Q ∈ G := h.mem_of_pos hQ
  have hnn : ∀ Q ∈ G, 0 ≤ F Q * Q φ := fun Q hQ => mul_nonneg (h.1 Q) (hG Q hQ φ).1
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 Q hQG
  exact (mul_eq_zero.mp this).resolve_left hQ.ne'

/-- **The generated face lies in the product face** (on the product grid): a balance solution
puts no mass on a table disagreeing with `t` where `t` is 0 or 1. This is the mechanism behind
bli-slides-021 and E5, proved as a lemma; the finding itself is `bli-superbelief`'s.
Source: bli-slides-021; [[bli-program]] §3.4
Kind: P
Fidelity: exact
Hyps: (a) all -/
lemma faceGen_subset_faceProd (d : ℕ → ℕ) (t : Table 𝒮 m) :
    faceGen (grid 𝒮 d (m + 1)) t ⊆ faceProd 𝒮 d m t := by
  intro Q hQ
  obtain ⟨hQG, F, hF, hb, hpos⟩ := mem_faceGen_iff.mp hQ
  refine mem_faceProd_iff.mpr ⟨hQG, fun φ hφ => ?_⟩
  have hG : ∀ Q ∈ grid 𝒮 d (m + 1), Q.InUnit := fun _ hQ => inUnit_of_mem_grid hQ
  have hmean : meanOn (grid 𝒮 d (m + 1)) F ⟨φ.1, 𝒮.mono m φ.2⟩ = t φ := by
    have := congrFun hb φ
    simpa [Table.restrict_apply] using this
  rcases hφ with h0 | h1
  · rw [Table.restrict_apply, h0]
    exact hF.coord_eq_zero_of_meanOn_eq_zero hG (by rw [hmean, h0]) hpos
  · rw [Table.restrict_apply, h1]
    exact hF.coord_eq_one_of_meanOn_eq_one hG (by rw [hmean, h1]) hpos

/-- Under `IsProb ∧ Balanced`, non-degeneracy says exactly that the support **is** the product
face.
Source: bli-slides-018 (support = face, `FS`); [[bli-program]] §2.4
Kind: C
Fidelity: exact
Hyps: (a) all -/
lemma nonDegenerate_iff_support_eq_faceProd {d : ℕ → ℕ} {F : Superbelief 𝒮 (m + 1)}
    {t : Table 𝒮 m} (hF : IsProb d F) (hb : Balanced d F t) :
    NonDegenerate d F t ↔ ∀ Q, 0 < F Q ↔ Q ∈ faceProd 𝒮 d m t := by
  constructor
  · intro hnd Q
    refine ⟨fun hpos => ?_, fun hQ => hnd Q hQ⟩
    exact faceGen_subset_faceProd d t
      (mem_faceGen_of_pos hF (balanced_iff_restrict_meanOn_eq.mp hb) hpos)
  · intro h Q hQ
    exact (h Q).mpr hQ

end FaceGen

end Cleanroom.Bli.BliFinite
