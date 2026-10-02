import LogicalInduction.Framework.Foundations
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# `bli-finite` · Index: small-sentence index, tables, mesh, grid (T1)

The finite object every BLI package is stated over, with **no inductor, criterion or
construction in sight**. Design decisions of record (mandate §"Design decisions" 1–3):

* the index of small sentences is a *parameter* `SmallIndex` (a nested family of finite
  sentence sets), not `bli-found`'s `smallSet` — dependents instantiate it;
* tables are `ℚ`-valued functions on the day's small sentences; "meant in `[0,1]`" is the
  predicate `Table.InUnit`, never a subtype;
* the mesh carries `0 < d m` and `d m ∣ d (m+1)` as fields; `gridVals d = {0, 1/d, …, 1}`
  **with 0 and 1** (Roman's dot grid `{1/d, …, 1}` omits 0; bli-slides-017's flag), and
  `grid 𝒮 d m` is the product grid on the day-`m` tables.

Sources: bli-slides-017 (grid), bli-paper-033 (`𝒟_n`), [[bli-program]] §2.2.
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction

/-! ## The index of small sentences -/

/-- **Small-sentence index**: a nested family `S 0 ⊆ S 1 ⊆ ⋯` of finite sentence sets, the
sentences "small" on each day. The BLI area's `smallSet` (`bli-found`, F1) is one instance;
this package leaves the index abstract so that it depends on nothing.
Monotonicity is a field because `Balanced` restricts a day-`(m+1)` mean to the day-`m`
sentences.
Source: [[bli-program]] §2.1–2.2; mandate design decision 1
Kind: D
Fidelity: variant: parameter in place of the program's `smallSet` -/
structure SmallIndex where
  /-- The sentences small on day `m`. -/
  S : ℕ → Finset Sentence
  /-- Small sentences stay small. -/
  mono : ∀ m, S m ⊆ S (m + 1)

namespace SmallIndex

/-- Nestedness at arbitrary distance: `S m ⊆ S n` whenever `m ≤ n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mono_le (𝒮 : SmallIndex) {m n : ℕ} (h : m ≤ n) : 𝒮.S m ⊆ 𝒮.S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (𝒮.mono _)

end SmallIndex

/-! ## Tables -/

/-- **Table**: a rational price for every sentence small on day `m` (the paper's written-out
price list `Q`, bli-paper-032). Values are meant in `[0,1]`; see `Table.InUnit`.
Source: bli-paper-032; [[bli-program]] §2.2
Kind: D
Fidelity: exact -/
abbrev Table (𝒮 : SmallIndex) (m : ℕ) : Type := ↥(𝒮.S m) → ℚ

namespace Table

variable {𝒮 : SmallIndex} {m : ℕ}

/-- A table lies in the unit cube: every price is in `[0,1]`. A table outside the cube is
junk input, and every definition of the package is total on it in a stated way.
Source: bli-paper-030 flag ("prices lie in `[0,1]`"); mandate design decision 2
Kind: D
Fidelity: exact -/
def InUnit (t : Table 𝒮 m) : Prop := ∀ φ, 0 ≤ t φ ∧ t φ ≤ 1

/-- Restrict a day-`(m+1)` table to the day-`m` sentences (which are small on day `m+1` by
`SmallIndex.mono`).
Source: none: infrastructure (mandate design decision 1)
Kind: D
Fidelity: n/a -/
def restrict (t : Table 𝒮 (m + 1)) : Table 𝒮 m :=
  fun φ => t ⟨φ.1, 𝒮.mono m φ.2⟩

/-- Unfolding lemma for `restrict`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma restrict_apply (t : Table 𝒮 (m + 1)) (φ : ↥(𝒮.S m)) :
    t.restrict φ = t ⟨φ.1, 𝒮.mono m φ.2⟩ := rfl

/-- Restriction preserves the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma InUnit.restrict {t : Table 𝒮 (m + 1)} (h : t.InUnit) : t.restrict.InUnit :=
  fun _ => h _

/-- Transport a table along an equality of days (used only by the trajectory API, where
`n + h + k` and `n + (h + k)` must be identified). Cast-free: it re-indexes through the
membership proof.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def castDay {m m' : ℕ} (h : m = m') (t : Table 𝒮 m) : Table 𝒮 m' :=
  fun φ => t ⟨φ.1, h ▸ φ.2⟩

/-- Transport along `rfl` is the identity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma castDay_rfl (t : Table 𝒮 m) : t.castDay rfl = t := rfl

/-- Unfolding lemma for `castDay`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma castDay_apply {m m' : ℕ} (h : m = m') (t : Table 𝒮 m) (φ : ↥(𝒮.S m')) :
    t.castDay h φ = t ⟨φ.1, h ▸ φ.2⟩ := rfl

end Table

/-! ## Mesh and grid -/

/-- **Mesh**: the day-indexed denominators of the price grid, positive and nested (`d m` divides
`d (m+1)`, so every day-`m` grid value is a day-`(m+1)` grid value).
Source: bli-paper-033 (`D_n` must refine); [[bli-program]] §2.2; mandate design decision 3
Kind: D
Fidelity: exact -/
structure Mesh where
  /-- Denominator on day `m`. -/
  d : ℕ → ℕ
  /-- No day has a zero denominator (`k / 0 = 0` would collapse the grid to `{0}`). -/
  d_pos : ∀ m, 0 < d m
  /-- Grids refine. -/
  d_dvd : ∀ m, d m ∣ d (m + 1)

/-- The grid values `{0, 1/d, 2/d, …, 1}` — **with 0 and 1**. Roman's `D = {1/d, …, 1}`
(bli-slides-017) omits 0; the program adds it because exact agreement on a sentence priced
below `1/d` is otherwise impossible (bli-superbelief E5). At `d = 0` Lean's `k / 0 = 0` gives
`{0}`; `Mesh.d_pos` excludes that, and every lemma below assumes `0 < d`.
Source: bli-slides-017; [[bli-program]] §2.2
Kind: D
Fidelity: variant: 0 added to Roman's grid (disclosed) -/
def gridVals (d : ℕ) : Finset ℚ :=
  (Finset.range (d + 1)).image (fun k : ℕ => (k : ℚ) / d)

/-- The product grid on day-`m` tables: every coordinate in `gridVals (d m)`.
Source: bli-slides-017 (`D^S`); [[bli-program]] §2.2
Kind: D
Fidelity: exact (with 0 added to `D`) -/
def grid (𝒮 : SmallIndex) (d : ℕ → ℕ) (m : ℕ) : Finset (Table 𝒮 m) :=
  Fintype.piFinset (fun _ => gridVals (d m))

/-! ### Grid-value lemmas -/

/-- Membership in the grid: `q = k / d` for some `k ≤ d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_gridVals_iff {d : ℕ} {q : ℚ} :
    q ∈ gridVals d ↔ ∃ k : ℕ, k ≤ d ∧ q = (k : ℚ) / d := by
  unfold gridVals
  simp only [Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

/-- Grid values lie in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridVals_subset_Icc {d : ℕ} {q : ℚ} (hq : q ∈ gridVals d) : 0 ≤ q ∧ q ≤ 1 := by
  obtain ⟨k, hk, rfl⟩ := mem_gridVals_iff.mp hq
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · have hd' : (0 : ℚ) < d := by exact_mod_cast hd
    constructor
    · positivity
    · rw [div_le_one hd']; exact_mod_cast hk

/-- `0` is a grid value (for every `d`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zero_mem_gridVals (d : ℕ) : (0 : ℚ) ∈ gridVals d :=
  mem_gridVals_iff.mpr ⟨0, Nat.zero_le _, by simp⟩

/-- `1` is a grid value when `0 < d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_mem_gridVals {d : ℕ} (hd : 0 < d) : (1 : ℚ) ∈ gridVals d :=
  mem_gridVals_iff.mpr ⟨d, le_rfl, by
    have : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp⟩

/-- The grid has `d + 1` values when `0 < d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma card_gridVals {d : ℕ} (hd : 0 < d) : (gridVals d).card = d + 1 := by
  unfold gridVals
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (a : ℚ) = b := (div_left_inj' hd').mp hab
  exact_mod_cast this

/-- Nesting: a coarser grid's values are values of every (positive) grid it divides into.
Source: bli-paper-033 (`D_n` refines); mandate design decision 3
Kind: L
Fidelity: n/a -/
lemma gridVals_mono {d d' : ℕ} (h : d ∣ d') (hd' : 0 < d') : gridVals d ⊆ gridVals d' := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := mem_gridVals_iff.mp hq
  obtain ⟨c, rfl⟩ := h
  have hd : 0 < d := Nat.pos_of_ne_zero (fun h => by subst h; simp at hd')
  have hc : 0 < c := Nat.pos_of_ne_zero (fun h => by subst h; simp at hd')
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  refine mem_gridVals_iff.mpr ⟨k * c, Nat.mul_le_mul_right c hk, ?_⟩
  push_cast
  field_simp

/-! ### Grid lemmas -/

variable {𝒮 : SmallIndex} {d : ℕ → ℕ} {m : ℕ}

/-- Membership in the product grid is coordinatewise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_grid_iff {Q : Table 𝒮 m} : Q ∈ grid 𝒮 d m ↔ ∀ φ, Q φ ∈ gridVals (d m) := by
  unfold grid; exact Fintype.mem_piFinset

/-- The grid is nonempty (the zero table is in it).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma grid_nonempty : (grid 𝒮 d m).Nonempty :=
  ⟨fun _ => 0, mem_grid_iff.mpr fun _ => zero_mem_gridVals _⟩

/-- Every grid table lies in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inUnit_of_mem_grid {Q : Table 𝒮 m} (hQ : Q ∈ grid 𝒮 d m) : Q.InUnit :=
  fun φ => gridVals_subset_Icc (mem_grid_iff.mp hQ φ)

/-- The grid has `(d m + 1) ^ |S m|` tables when `0 < d m`.
Source: bli-slides-019 (`q = d^{|S|}`, with the added 0 giving `d + 1`)
Kind: L
Fidelity: n/a -/
lemma card_grid (hd : 0 < d m) : (grid 𝒮 d m).card = (d m + 1) ^ (𝒮.S m).card := by
  unfold grid
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    card_gridVals hd]

/-- **Nesting, the true consequence of `gridVals_mono`.** A day-`(m+1)` table whose restriction is
a day-`m` grid table, and whose *new* coordinates are day-`(m+1)` grid values, is a day-`(m+1)`
grid table: coarse grid tables extend to fine grid tables (this is what a point-mass kernel at
the current table needs). The mandate's `restrict_mem_grid` ("the restriction of a fine grid
table is a coarse grid table") is **false** when `d m < d (m+1)` (`Q φ = 1/4` is fine for
`d (m+1) = 4` and not coarse for `d m = 2`); see `bli-finite-findings` F-9.
Source: bli-paper-033 (`D_n` refines); mandate design decision 3 (corrected)
Kind: L
Fidelity: n/a -/
lemma mem_grid_of_restrict_mem_grid (𝓜 : Mesh) {Q : Table 𝒮 (m + 1)}
    (h₁ : Q.restrict ∈ grid 𝒮 𝓜.d m)
    (h₂ : ∀ φ : ↥(𝒮.S (m + 1)), φ.1 ∉ 𝒮.S m → Q φ ∈ gridVals (𝓜.d (m + 1))) :
    Q ∈ grid 𝒮 𝓜.d (m + 1) := by
  rw [mem_grid_iff] at h₁ ⊢
  intro φ
  by_cases hφ : φ.1 ∈ 𝒮.S m
  · have := h₁ ⟨φ.1, hφ⟩
    rw [Table.restrict_apply] at this
    exact gridVals_mono (𝓜.d_dvd m) (𝓜.d_pos (m + 1)) this
  · exact h₂ φ hφ

/-- The mandate's `restrict_mem_grid` holds when consecutive denominators agree.
Source: mandate design decision 3 (the special case that is true)
Kind: L
Fidelity: weaker: needs `d (m+1) = d m` -/
lemma restrict_mem_grid_of_eq {Q : Table 𝒮 (m + 1)} (hd : d (m + 1) = d m)
    (hQ : Q ∈ grid 𝒮 d (m + 1)) : Q.restrict ∈ grid 𝒮 d m := by
  rw [mem_grid_iff] at hQ ⊢
  intro φ
  rw [Table.restrict_apply, ← hd]
  exact hQ _

end Cleanroom.Bli.BliFinite
