import Cleanroom.Found.LitDdbFrames.Basic
import Cleanroom.Found.LitDdbFrames.Blackwell
import Mathlib.Algebra.BigOperators.Field

/-!
# Possibility correspondences and the conditioning frame (definitions of record)

Package `tt-finite-frames` (faf-cleanroom run, 2026-09-29), Target G1. A *possibility
correspondence* `K : W → Finset W` (Weatherson's "experiment" `E`: at `w` the agent learns
`E(w)`; written `K` in Lean because `E` is the dependency's expectation) and the frame it induces
by conditioning a prior on it: `Frame.ofCorr π K` has row `w ↦ π(· | K w)`. Partitions are the
special case `Corr.ofMap f` (the fibres of a map). Every frame this package builds is `ofCorr` or
its partition case `ofPartition`; the trust predicates are the dependency's (`TotalTrust`, `Value`,
…), never redefined.

Conventions (binding, from the mandate): `Corr.Transitive` is the **corrected** direction
`v ∈ K w → K v ⊆ K w` (Weatherson prints the inclusion reversed; the printed form is
`Corr.TransitivePrinted`, kept only for the finding G6). Priors carry `hπ : ∀ w, 0 ≤ π w`; full
support `∀ w, 0 < π w` is stated explicitly where a result needs it.

No FAF object models any of this (grep of FAF for `Blackwell|garbl|Geanakoplos`, 2026-09-29: no
hits), so nothing here is a modelling substitution.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Correspondences -/

/-- A possibility correspondence: at each world the set of worlds the agent considers possible
(Weatherson's experiment `E : W → 𝒫(W)`; Geanakoplos's information structure).
Source: [[Deference and Infinite Frames]] §2 l. 108
Kind: D
Fidelity: exact -/
abbrev Corr (W : Type) := W → Finset W

namespace Corr

/-- Reflexive: `w ∈ E w`.
Source: [[Deference and Infinite Frames]] §2 l. 134
Kind: D
Fidelity: exact -/
def Reflexive (K : Corr W) : Prop := ∀ w, w ∈ K w

/-- Transitive, in the **corrected** direction: `v ∈ E w → E v ⊆ E w` (positive introspection;
transcriber's note 1 of the source).
Source: [[Deference and Infinite Frames]] §2 l. 136 as corrected by note 1 (l. 11)
Kind: D
Fidelity: variant: the source prints the inclusion reversed; see `TransitivePrinted` -/
def Transitive (K : Corr W) : Prop := ∀ w v, v ∈ K w → K v ⊆ K w

/-- Transitive **as printed** in the source: `v ∈ E w → E w ⊆ E v`. Defined only for the finding
G6 (`Weatherson.lean`): the source's own example fails it.
Source: [[Deference and Infinite Frames]] §2 l. 136 (printed form)
Kind: D
Fidelity: exact (of the printed text; the intended condition is `Transitive`) -/
def TransitivePrinted (K : Corr W) : Prop := ∀ w v, v ∈ K w → K w ⊆ K v

/-- Nested: any two cells are disjoint or comparable.
Source: [[Deference and Infinite Frames]] §2 l. 138
Kind: D
Fidelity: exact -/
def Nested (K : Corr W) : Prop := ∀ w v, Disjoint (K w) (K v) ∨ K w ⊆ K v ∨ K v ⊆ K w

/-- Partitional: reflexive, and `v ∈ E w → E w = E v`.
Source: [[Deference and Infinite Frames]] §2 l. 130
Kind: D
Fidelity: exact -/
def Partitional (K : Corr W) : Prop := Reflexive K ∧ ∀ w v, v ∈ K w → K w = K v

/-- Reflexive, transitive (corrected direction) and nested: Geanakoplos's hypothesis.
Source: [[Deference and Infinite Frames]] §2 l. 132–140
Kind: D
Fidelity: exact (with the corrected transitivity) -/
def RTN (K : Corr W) : Prop := Reflexive K ∧ Transitive K ∧ Nested K

/-- `E₁` refines `E₂` (is more informative): `E₁ w ⊆ E₂ w` at every world. Distinct from the
dependency's `Blackwell.Refines` on maps; `refines_ofMap_iff` is the bridge.
Source: [[Deference and Infinite Frames]] §2 l. 114
Kind: D
Fidelity: exact -/
def Refines (K₁ K₂ : Corr W) : Prop := ∀ w, K₁ w ⊆ K₂ w

/-- The partition correspondence of a map: `ofMap f w = {v | f v = f w}`, the fibre through `w`.
Source: none: infrastructure (partitions as correspondences)
Kind: D
Fidelity: exact -/
def ofMap {ι : Type} [DecidableEq ι] (f : W → ι) : Corr W :=
  fun w => univ.filter (fun v => f v = f w)

/-- Membership in a fibre.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem mem_ofMap {ι : Type} [DecidableEq ι] {f : W → ι} {w v : W} :
    v ∈ ofMap f w ↔ f v = f w := by simp [ofMap]

/-- The fibres of a map form a partitional correspondence.
Source: none: infrastructure (G1)
Kind: L
Fidelity: n/a -/
theorem ofMap_partitional {ι : Type} [DecidableEq ι] (f : W → ι) : Partitional (ofMap f) := by
  refine ⟨fun w => by simp, fun w v hv => ?_⟩
  rw [mem_ofMap] at hv
  ext u
  simp [hv]

/-- In a partitional correspondence, `v ∈ E w ↔ E v = E w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Partitional.mem_iff_eq {K : Corr W} (hK : Partitional K) {w v : W} :
    v ∈ K w ↔ K v = K w := by
  constructor
  · intro h; exact (hK.2 w v h).symm
  · intro h; rw [← h]; exact hK.1 v

/-- A partitional correspondence is transitive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Partitional.transitive {K : Corr W} (hK : Partitional K) : Transitive K :=
  fun w v hv => by rw [hK.2 w v hv]

/-- A partitional correspondence is nested.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Partitional.nested {K : Corr W} (hK : Partitional K) : Nested K := by
  intro w v
  by_cases h : Disjoint (K w) (K v)
  · exact Or.inl h
  · right; left
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨u, hu, hu'⟩ := h
    rw [hK.2 w u hu, hK.2 v u hu']

/-- Partitional implies reflexive-transitive-nested.
Source: none: infrastructure (G1: "`Corr.ofMap f` is RTN")
Kind: L
Fidelity: n/a -/
theorem Partitional.rtn {K : Corr W} (hK : Partitional K) : RTN K :=
  ⟨hK.1, hK.transitive, hK.nested⟩

/-- The fibres of a map are reflexive, transitive and nested.
Source: none: infrastructure (G1)
Kind: L
Fidelity: n/a -/
theorem ofMap_rtn {ι : Type} [DecidableEq ι] (f : W → ι) : RTN (ofMap f) :=
  (ofMap_partitional f).rtn

/-- A correspondence is partitional iff it is the fibre correspondence of its own cell map
`E : W → Finset W`.
Source: none: infrastructure (G1, `Corr.partitional_iff_ofMap`)
Kind: L
Fidelity: n/a -/
theorem partitional_iff_ofMap {K : Corr W} : Partitional K ↔ K = ofMap K := by
  constructor
  · intro hK
    funext w
    ext v
    rw [mem_ofMap]
    exact hK.mem_iff_eq
  · intro h
    rw [h]
    exact ofMap_partitional K

/-- Refinement of fibre correspondences is refinement of maps: `ofMap f₁` refines `ofMap f₂`
iff `f₂` factors through `f₁`. (`[Nonempty κ]` is needed: on an empty `W` with `κ` empty and `ι`
inhabited the left side is vacuous and the right side has no map.)
Source: none: infrastructure (G1, the bridge to the dependency's `Blackwell.Refines`)
Kind: L
Fidelity: n/a -/
theorem refines_ofMap_iff {ι κ : Type} [DecidableEq ι] [DecidableEq κ] [Nonempty κ]
    (f₁ : W → ι) (f₂ : W → κ) : Refines (ofMap f₁) (ofMap f₂) ↔ Blackwell.Refines f₁ f₂ := by
  constructor
  · intro h
    classical
    refine ⟨fun s => if hs : ∃ w, f₁ w = s then f₂ hs.choose else Classical.arbitrary κ, ?_⟩
    funext w
    have hs : ∃ v, f₁ v = f₁ w := ⟨w, rfl⟩
    simp only [Function.comp, dif_pos hs]
    have hmem : hs.choose ∈ ofMap f₁ w := by rw [mem_ofMap]; exact hs.choose_spec
    have := h w hmem
    rw [mem_ofMap] at this
    exact this.symm
  · rintro ⟨g, rfl⟩ w v hv
    rw [mem_ofMap] at hv ⊢
    simp [Function.comp, hv]

/-- Summing over the worlds is summing over the cells of a partitional correspondence.
Source: none: infrastructure (the cellwise regrouping every partition argument uses)
Kind: L
Fidelity: n/a -/
theorem Partitional.sum_cells {K : Corr W} (hK : Partitional K) (g : W → ℝ) :
    ∑ w, g w = ∑ C ∈ univ.image K, ∑ w ∈ C, g w := by
  rw [← sum_fiberwise_of_maps_to (g := K) (t := univ.image K)
    (fun w _ => mem_image_of_mem K (mem_univ w))]
  apply sum_congr rfl
  intro C hC
  obtain ⟨v, _, rfl⟩ := mem_image.1 hC
  apply sum_congr _ (fun _ _ => rfl)
  ext w
  simp only [mem_filter, mem_univ, true_and]
  exact hK.mem_iff_eq.symm

/-- Under a full-support prior every cell of a reflexive correspondence has positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_pos_of_reflexive {π : W → ℝ} (hpos : ∀ w, 0 < π w) {K : Corr W}
    (hK : Reflexive K) (w : W) : 0 < mass π (K w) :=
  mass_pos_of_mem (fun v => (hpos v).le) (hK w) (hpos w)

end Corr

/-! ## The conditioning frame -/

/-- **The conditioning frame** of a prior on a correspondence: row `w` is `π(· | E w)`, i.e.
`v ↦ 𝟙[v ∈ E w] π v / π(E w)`. The division is guarded by `h : ∀ w, 0 < π(E w)` inside the
construction; no predicate divides. This is the package's one construction of record: the lab's
`condExpert π c` is `ofPartition π c`, Weatherson's "update by conditionalising on `E(w)`" is this
row.
Source: [[Deference and Infinite Frames]] §2 l. 108 ("update by conditionalising on `E_i(w)`");
trust-lab-063 `condExpert`
Kind: D
Fidelity: exact -/
def Frame.ofCorr (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (K : Corr W) (h : ∀ w, 0 < mass π (K w)) :
    Frame W where
  P := fun w v => (if v ∈ K w then π v else 0) / mass π (K w)
  P_mem := fun w => by
    refine ⟨fun v => div_nonneg ?_ (h w).le, ?_⟩
    · split_ifs
      · exact hπ v
      · exact le_rfl
    · rw [← Finset.sum_div, div_eq_one_iff_eq (h w).ne']
      simp [mass, sum_ite_mem]

/-- The rows of the conditioning frame, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofCorr_P_apply (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (K : Corr W)
    (h : ∀ w, 0 < mass π (K w)) (w v : W) :
    (Frame.ofCorr π hπ K h).P w v = (if v ∈ K w then π v else 0) / mass π (K w) := rfl

/-- The expert's estimate at `w` is the conditional expectation `E_π(X | E w)` (ratio form; the
division is the construction's guarded one).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofCorr_E_eq (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (K : Corr W)
    (h : ∀ w, 0 < mass π (K w)) (w : W) (X : W → ℝ) :
    E ((Frame.ofCorr π hπ K h).P w) X = (∑ v ∈ K w, π v * X v) / mass π (K w) := by
  unfold E
  simp only [Frame.ofCorr_P_apply]
  rw [Finset.sum_div]
  rw [← sum_subset (subset_univ (K w))]
  · apply sum_congr rfl
    intro v hv
    rw [if_pos hv]
    ring
  · intro v _ hv
    simp [hv]

/-- **The consumer identity** for the conditioning frame, product form:
`E_{P_w}(X) · π(E w) = ∑_{v ∈ E w} π v X v`.
Source: none: infrastructure (G1, `ofCorr_E`)
Kind: L
Fidelity: n/a -/
theorem Frame.ofCorr_E (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (K : Corr W)
    (h : ∀ w, 0 < mass π (K w)) (w : W) (X : W → ℝ) :
    E ((Frame.ofCorr π hπ K h).P w) X * mass π (K w) = ∑ v ∈ K w, π v * X v := by
  rw [Frame.ofCorr_E_eq, div_mul_cancel₀ _ (h w).ne']

/-- Equal cells give equal rows (no positivity needed).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofCorr_P_eq_of_eq (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (K : Corr W)
    (h : ∀ w, 0 < mass π (K w)) {w v : W} (e : K w = K v) :
    (Frame.ofCorr π hπ K h).P w = (Frame.ofCorr π hπ K h).P v := by
  funext u
  simp only [Frame.ofCorr_P_apply, e]

/-- **Rows determine cells under full support**: `P_w = P_v ↔ E w = E v`. This is why DDB's cell
constraint on strategies (phrased through `P`) and Weatherson's (phrased through `E`) agree
under `hpos`; on null worlds they differ.
Source: none: infrastructure (G1, `ofCorr_P_inj`)
Kind: L
Fidelity: n/a -/
theorem Frame.ofCorr_P_inj (π : W → ℝ) (hpos : ∀ w, 0 < π w) (K : Corr W)
    (h : ∀ w, 0 < mass π (K w)) (w v : W) :
    (Frame.ofCorr π (fun w => (hpos w).le) K h).P w =
      (Frame.ofCorr π (fun w => (hpos w).le) K h).P v ↔ K w = K v := by
  constructor
  · intro hP
    ext u
    have hu := congrFun hP u
    simp only [Frame.ofCorr_P_apply] at hu
    constructor
    · intro huw
      by_contra huv
      rw [if_pos huw, if_neg huv, zero_div] at hu
      have := div_pos (hpos u) (h w)
      linarith
    · intro huv
      by_contra huw
      rw [if_neg huw, if_pos huv, zero_div] at hu
      have := div_pos (hpos u) (h v)
      linarith
  · exact Frame.ofCorr_P_eq_of_eq π _ K h

/-- Under full support, the DDB cell `[P = P_w]` of the conditioning frame is the set of worlds
with the same `E`-cell as `w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofCorr_cell (π : W → ℝ) (hpos : ∀ w, 0 < π w) (K : Corr W)
    (h : ∀ w, 0 < mass π (K w)) (w : W) :
    (Frame.ofCorr π (fun w => (hpos w).le) K h).cell
        ((Frame.ofCorr π (fun w => (hpos w).le) K h).P w) =
      univ.filter (fun v => K v = K w) := by
  ext v
  simp only [Frame.mem_cell, mem_filter, mem_univ, true_and]
  exact Frame.ofCorr_P_inj π hpos K h v w

/-- For a partitional correspondence under full support, the DDB cell of `w` is `E w` itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofCorr_cell_of_partitional (π : W → ℝ) (hpos : ∀ w, 0 < π w) {K : Corr W}
    (hK : K.Partitional) (h : ∀ w, 0 < mass π (K w)) (w : W) :
    (Frame.ofCorr π (fun w => (hpos w).le) K h).cell
        ((Frame.ofCorr π (fun w => (hpos w).le) K h).P w) =
      K w := by
  rw [Frame.ofCorr_cell π hpos K h]
  ext v
  simp only [mem_filter, mem_univ, true_and]
  exact hK.mem_iff_eq.symm

/-- **The partition expert** of a full-support prior and a map `f`: the conditioning frame of the
fibres of `f`. This is the lab's `condExpert π f` (trust-lab-063) and the object of every
partition-expert trust statement in the package.
Source: trust-lab-063 `condExpert`; [[route-transitivity]] §5.1 Link 1
Kind: D
Fidelity: exact -/
def Frame.ofPartition {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w) (f : W → ι) :
    Frame W :=
  Frame.ofCorr π (fun w => (hpos w).le) (Corr.ofMap f)
    (Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional f).1)

/-- The partition expert is the conditioning frame of the fibre correspondence (by definition).
Source: none: infrastructure (G1, `ofPartition_eq_ofCorr`)
Kind: L
Fidelity: n/a -/
theorem Frame.ofPartition_eq_ofCorr {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w)
    (f : W → ι) :
    Frame.ofPartition π hpos f = Frame.ofCorr π (fun w => (hpos w).le) (Corr.ofMap f)
      (Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional f).1) := rfl

/-- Rows of the partition expert: `P_w v = 𝟙[f v = f w] π v / π(f = f w)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofPartition_P_apply {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w)
    (f : W → ι) (w v : W) :
    (Frame.ofPartition π hpos f).P w v =
      (if f v = f w then π v else 0) / mass π (Corr.ofMap f w) := by
  simp [Frame.ofPartition, Frame.ofCorr_P_apply]

/-- The partition expert's estimate at `w`, product form:
`E_{P_w}(X) · π(f = f w) = ∑_{f v = f w} π v X v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofPartition_E {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w)
    (f : W → ι) (w : W) (X : W → ℝ) :
    E ((Frame.ofPartition π hpos f).P w) X * mass π (Corr.ofMap f w) =
      ∑ v ∈ Corr.ofMap f w, π v * X v :=
  Frame.ofCorr_E π (fun w => (hpos w).le) (Corr.ofMap f)
    (Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional f).1) w X

/-- The partition expert's estimate at `w`, ratio form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofPartition_E_eq {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w)
    (f : W → ι) (w : W) (X : W → ℝ) :
    E ((Frame.ofPartition π hpos f).P w) X =
      (∑ v ∈ Corr.ofMap f w, π v * X v) / mass π (Corr.ofMap f w) :=
  Frame.ofCorr_E_eq π (fun w => (hpos w).le) (Corr.ofMap f)
    (Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional f).1) w X

/-- Rows of the partition expert coincide exactly on the fibres of `f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofPartition_P_inj {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w)
    (f : W → ι) (w v : W) :
    (Frame.ofPartition π hpos f).P w = (Frame.ofPartition π hpos f).P v ↔ f w = f v := by
  rw [Frame.ofPartition_eq_ofCorr, Frame.ofCorr_P_inj π hpos]
  constructor
  · intro h
    have := (Corr.ofMap_partitional f).1 w
    rw [h, Corr.mem_ofMap] at this
    exact this
  · intro h
    ext u
    simp [Corr.mem_ofMap, h]

/-- The DDB cell of the partition expert at `w` is the fibre of `w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofPartition_cell {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w)
    (f : W → ι) (w : W) :
    (Frame.ofPartition π hpos f).cell ((Frame.ofPartition π hpos f).P w) = Corr.ofMap f w :=
  Frame.ofCorr_cell_of_partitional π hpos (Corr.ofMap_partitional f)
    (Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional f).1) w

end

end Cleanroom.Trust.TtFiniteFrames
