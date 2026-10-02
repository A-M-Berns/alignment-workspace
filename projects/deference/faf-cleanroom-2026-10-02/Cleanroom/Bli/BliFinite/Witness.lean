import Cleanroom.Bli.BliFinite.Tent

/-!
# `bli-finite` · Witness: the worked instance exercising T1–T7 together (T9, N+)

`S 0 = {p}`, `S 1 = S 2 = ⋯ = {p, q}`, mesh `d = 2` everywhere, `t₀ = (p ↦ 1/2)`:

* the day-1 grid has `9` tables (`card_grid_witness`);
* the tent kernel at `t₀` is the uniform `1/9` on all of them (`tentLaw_t₀`), so the product
  face is the whole grid (`faceProd_t₀`), every point has positive mass, the mass sums to `1`
  by the explicit `9 · (1/9)` computation (`sum_tentLaw_t₀`), balance holds (by the theorem
  `tentLaw_balanced`, instantiated), and the horizon-2 trajectory law satisfies the martingale
  identity at day `2` by the theorem `trajLaw_martingale` (81 trajectories, none listed);
* the pinned case `t₀' = (p ↦ 0)`: the face is `{Q : Q p = 0}` with exactly `3` points, each of
  mass `1/3`, and the grid point `(p ↦ 1/2, q ↦ 0)` has mass `0` — the face is a proper subset
  of the grid when a price is `0`.

So the witness has `d ≥ 2`, `|S| ≥ 2`, a face with `≥ 2` points and positive mass on all of
them, and shows the face is proper when a price is 0 ([[bli-program]] §7 item 11's checklist).
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction LO.Propositional Finset

/-- The atom `p` of the witness.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev pW : Sentence := Formula.atom 0
/-- The atom `q` of the witness.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev qW : Sentence := Formula.atom 1

/-- `p ≠ q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pW_ne_qW : pW ≠ qW := fun h => absurd (Formula.atom.inj h) (by norm_num)

/-- The witness index: `S 0 = {p}`, `S m = {p, q}` for `m ≥ 1`.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def witIndex : SmallIndex where
  S := fun m => if m = 0 then {pW} else {pW, qW}
  mono := by
    intro m
    by_cases h : m = 0
    · subst h
      simp only [if_true, Nat.zero_add, one_ne_zero, if_false]
      intro x hx; simp only [Finset.mem_singleton] at hx; simp [hx]
    · simp only [h, if_false, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      exact Finset.Subset.refl _

/-- The witness mesh: `d = 2` on every day.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def witMesh : Mesh := ⟨fun _ => 2, fun _ => by norm_num, fun _ => dvd_refl 2⟩

/-- Day 0 of the witness index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma witIndex_S_zero : witIndex.S 0 = {pW} := rfl

/-- Later days of the witness index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma witIndex_S_succ (m : ℕ) : witIndex.S (m + 1) = {pW, qW} := by
  simp [witIndex]

/-- `p` is small on day 0.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pW_mem_S0 : pW ∈ witIndex.S 0 := by simp [witIndex]
/-- `p` is small on day 1.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pW_mem_S1 : pW ∈ witIndex.S 1 := by simp [witIndex]
/-- `q` is small on day 1.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma qW_mem_S1 : qW ∈ witIndex.S 1 := by simp [witIndex]
/-- `q` is not small on day 0.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma qW_not_mem_S0 : qW ∉ witIndex.S 0 := by
  simp [witIndex, pW_ne_qW.symm]

/-- The day-0 table `p ↦ 1/2`.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def t₀ : Table witIndex 0 := fun _ => 1 / 2

/-- The pinned day-0 table `p ↦ 0`.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def t₀' : Table witIndex 0 := fun _ => 0

/-- `t₀` is in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma t₀_inUnit : t₀.InUnit := fun _ => by unfold t₀; norm_num

/-- `t₀'` is in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma t₀'_inUnit : t₀'.InUnit := fun _ => by unfold t₀'; norm_num

/-! ## The day-1 grid -/

/-- The day-1 grid has `3^2 = 9` tables.
Source: mandate T9
Kind: L
Fidelity: n/a -/
lemma card_grid_witness : (grid witIndex witMesh.d 1).card = 9 := by
  rw [card_grid (witMesh.d_pos 1)]
  have : (witIndex.S 1).card = 2 := by
    rw [witIndex_S_succ, Finset.card_pair pW_ne_qW]
  rw [this]; rfl

/-- The universe of day-1 small sentences, as the pair `{p, q}` in the subtype.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma univ_S1 : (Finset.univ : Finset ↥(witIndex.S 1)) = {⟨pW, pW_mem_S1⟩, ⟨qW, qW_mem_S1⟩} := by
  ext ⟨x, hx⟩
  have hx' := hx
  rw [witIndex_S_succ, Finset.mem_insert, Finset.mem_singleton] at hx'
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
  exact hx'

/-- The two day-1 small sentences are distinct as subtype elements.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma subtype_p_ne_q : (⟨pW, pW_mem_S1⟩ : ↥(witIndex.S 1)) ≠ ⟨qW, qW_mem_S1⟩ :=
  fun h => pW_ne_qW (Subtype.mk.inj h)

/-- The tent law on the witness is the product of the `p`-factor and the `q`-factor.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tentLaw_witness_eq (t : Table witIndex 0) (Q : Table witIndex 1) :
    tentLaw witMesh 0 t Q =
      tent1 2 (t ⟨pW, pW_mem_S0⟩) (Q ⟨pW, pW_mem_S1⟩) * uniform1 2 (Q ⟨qW, qW_mem_S1⟩) := by
  unfold tentLaw
  rw [univ_S1, Finset.prod_pair subtype_p_ne_q]
  unfold tentCoord
  rw [dif_pos pW_mem_S0, dif_neg qW_not_mem_S0]
  rfl

/-- `tent1 2 (1/2)` is the uniform law: each grid value has weight `1/3`.
Source: mandate T9 (`tent1 2 (1/2) = uniform`)
Kind: L
Fidelity: n/a -/
lemma tent1_two_half {v : ℚ} (hv : v ∈ gridVals 2) : tent1 2 (1 / 2) v = 1 / 3 := by
  unfold tent1 uniform1
  rw [clamp01_eq_self (by norm_num), if_pos hv]
  norm_num

/-- `tent1 d 0` is the point mass at `0`.
Source: mandate T9 (the pinned case)
Kind: L
Fidelity: n/a -/
lemma tent1_zero_eq (d : ℕ) (v : ℚ) : tent1 d 0 v = if v = 0 then 1 else 0 := by
  unfold tent1
  rw [clamp01_eq_self (by norm_num), max_eq_right (by norm_num : (0 : ℚ) ≤ 1 - 2 * 0),
    max_eq_left (by norm_num : 2 * (0 : ℚ) - 1 ≤ 0)]
  norm_num

/-- The uniform law at `d = 2` is `1/3` on the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uniform1_two {v : ℚ} (hv : v ∈ gridVals 2) : uniform1 2 v = 1 / 3 := by
  unfold uniform1; rw [if_pos hv]; norm_num

/-! ## The interior table `t₀ = (p ↦ 1/2)` -/

/-- **The tent kernel at `t₀` is uniform `1/9` on the 9 grid tables.**
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma tentLaw_t₀ {Q : Table witIndex 1} (hQ : Q ∈ grid witIndex witMesh.d 1) :
    tentLaw witMesh 0 t₀ Q = 1 / 9 := by
  rw [tentLaw_witness_eq]
  have hp := mem_grid_iff.mp hQ ⟨pW, pW_mem_S1⟩
  have hq := mem_grid_iff.mp hQ ⟨qW, qW_mem_S1⟩
  show tent1 2 (1 / 2) _ * uniform1 2 _ = 1 / 9
  rw [tent1_two_half hp, uniform1_two hq]; norm_num

/-- Positive mass on every grid table.
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma tentLaw_t₀_pos {Q : Table witIndex 1} (hQ : Q ∈ grid witIndex witMesh.d 1) :
    0 < tentLaw witMesh 0 t₀ Q := by
  rw [tentLaw_t₀ hQ]; norm_num

/-- The product face over `t₀` is the whole grid (no coordinate of `t₀` is 0 or 1).
Source: mandate T9
Kind: L
Fidelity: n/a -/
lemma faceProd_t₀ : faceProd witIndex witMesh.d 0 t₀ = grid witIndex witMesh.d 1 := by
  unfold faceProd
  apply Finset.filter_true_of_mem
  intro Q _ φ hφ
  exfalso
  rcases hφ with h | h <;> unfold t₀ at h <;> norm_num at h

/-- **The explicit mass check**: `9 · (1/9) = 1` over the 9 grid tables (the numeric form of
`tentLaw_sum_one` on the witness).
Source: mandate T9 ("`norm_num` on the 9-term sum")
Kind: N+
Fidelity: exact -/
lemma sum_tentLaw_t₀ : ∑ Q ∈ grid witIndex witMesh.d 1, tentLaw witMesh 0 t₀ Q = 1 := by
  rw [Finset.sum_congr rfl (fun Q hQ => tentLaw_t₀ hQ), Finset.sum_const, card_grid_witness,
    nsmul_eq_mul]
  norm_num

/-- Balance at `t₀` (the theorem `tentLaw_balanced`, instantiated).
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma balanced_t₀ : Balanced witMesh.d (tentLaw witMesh 0 t₀) t₀ := tentLaw_balanced t₀_inUnit

/-- Non-degeneracy at `t₀` (the theorem, instantiated; here the face is the whole grid).
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma nonDegenerate_t₀ : NonDegenerate witMesh.d (tentLaw witMesh 0 t₀) t₀ :=
  tentLaw_nonDegenerate t₀_inUnit

/-- **The martingale identity on the witness at horizon 2, day 2** (by the theorem, not by
enumerating the 81 trajectories): the expected day-2 price of `p` under the tent skeleton
started at `t₀` is `1/2`.
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma trajLaw_martingale_witness :
    ∑ τ ∈ trajGrid witIndex witMesh.d 0 2,
      trajLaw (tentSkeleton witIndex witMesh) 0 2 t₀ τ *
        τ.day 2 (by norm_num) (by norm_num) ⟨pW, witIndex.mono_le (by norm_num) pW_mem_S0⟩ =
      1 / 2 :=
  trajLaw_martingale (tentSkeleton witIndex witMesh) t₀_inUnit ⟨pW, pW_mem_S0⟩ 2
    (by norm_num) (by norm_num)

/-! ## The pinned table `t₀' = (p ↦ 0)` -/

/-- The grid table `(p ↦ 1/2, q ↦ 0)`: in the grid, off the face.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def Q₁ : Table witIndex 1 := fun φ => if φ.1 = pW then 1 / 2 else 0

/-- The grid table `(p ↦ 0, q ↦ 1/2)`: on the face.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def Q₂ : Table witIndex 1 := fun φ => if φ.1 = pW then 0 else 1 / 2

/-- `1/2` is a grid value at `d = 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma half_mem_gridVals_two : (1 / 2 : ℚ) ∈ gridVals 2 :=
  mem_gridVals_iff.mpr ⟨1, by norm_num, by norm_num⟩

/-- `Q₁` is a grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Q₁_mem_grid : Q₁ ∈ grid witIndex witMesh.d 1 := by
  rw [mem_grid_iff]; intro φ; unfold Q₁; split_ifs
  · exact half_mem_gridVals_two
  · exact zero_mem_gridVals _

/-- `Q₂` is a grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Q₂_mem_grid : Q₂ ∈ grid witIndex witMesh.d 1 := by
  rw [mem_grid_iff]; intro φ; unfold Q₂; split_ifs
  · exact zero_mem_gridVals _
  · exact half_mem_gridVals_two

/-- The face over the pinned table is `{Q ∈ grid : Q p = 0}`.
Source: mandate T9
Kind: L
Fidelity: n/a -/
lemma mem_faceProd_t₀'_iff (Q : Table witIndex 1) :
    Q ∈ faceProd witIndex witMesh.d 0 t₀' ↔ Q ∈ grid witIndex witMesh.d 1 ∧ Q ⟨pW, pW_mem_S1⟩ = 0 := by
  rw [mem_faceProd_iff]
  constructor
  · rintro ⟨hg, hf⟩
    exact ⟨hg, hf ⟨pW, pW_mem_S0⟩ (Or.inl rfl)⟩
  · rintro ⟨hg, hp⟩
    refine ⟨hg, fun φ _ => ?_⟩
    have : φ = ⟨pW, pW_mem_S0⟩ := by
      ext
      have h : φ.1 ∈ ({pW} : Finset Sentence) := φ.2
      exact Finset.mem_singleton.mp h
    subst this
    exact hp

/-- `(p ↦ 1/2, q ↦ 0)` is off the pinned face.
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma Q₁_not_mem_faceProd : Q₁ ∉ faceProd witIndex witMesh.d 0 t₀' := by
  rw [mem_faceProd_t₀'_iff]
  rintro ⟨-, h⟩
  unfold Q₁ at h; simp at h

/-- `(p ↦ 0, q ↦ 1/2)` is on the pinned face.
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma Q₂_mem_faceProd : Q₂ ∈ faceProd witIndex witMesh.d 0 t₀' := by
  rw [mem_faceProd_t₀'_iff]
  exact ⟨Q₂_mem_grid, by unfold Q₂; simp⟩

/-- **The tent kernel at the pinned table**: mass `1/3` on every face point, `0` off the face.
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma tentLaw_t₀' {Q : Table witIndex 1} (hQ : Q ∈ grid witIndex witMesh.d 1) :
    tentLaw witMesh 0 t₀' Q = if Q ⟨pW, pW_mem_S1⟩ = 0 then 1 / 3 else 0 := by
  rw [tentLaw_witness_eq]
  have hq := mem_grid_iff.mp hQ ⟨qW, qW_mem_S1⟩
  show tent1 2 0 _ * uniform1 2 _ = _
  rw [tent1_zero_eq, uniform1_two hq]
  split_ifs <;> norm_num

/-- The off-face point `(p ↦ 1/2, q ↦ 0)` has mass `0`.
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma tentLaw_t₀'_Q₁ : tentLaw witMesh 0 t₀' Q₁ = 0 := by
  rw [tentLaw_t₀' Q₁_mem_grid]; unfold Q₁; simp

/-- The face point `(p ↦ 0, q ↦ 1/2)` has mass `1/3`.
Source: mandate T9
Kind: N+
Fidelity: exact -/
lemma tentLaw_t₀'_Q₂ : tentLaw witMesh 0 t₀' Q₂ = 1 / 3 := by
  rw [tentLaw_t₀' Q₂_mem_grid]; unfold Q₂; simp

/-- **The pinned face has exactly 3 points.**
Source: mandate T9 ("three tables of mass 1/3")
Kind: N+
Fidelity: exact -/
lemma card_faceProd_t₀' : (faceProd witIndex witMesh.d 0 t₀').card = 3 := by
  have heq : faceProd witIndex witMesh.d 0 t₀' =
      Fintype.piFinset (fun φ : ↥(witIndex.S 1) => if φ.1 = pW then ({0} : Finset ℚ) else gridVals 2) := by
    ext Q
    rw [mem_faceProd_t₀'_iff, mem_grid_iff, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hg, hp⟩ φ
      by_cases hφ : φ.1 = pW
      · rw [if_pos hφ, Finset.mem_singleton]
        have : φ = ⟨pW, pW_mem_S1⟩ := Subtype.ext hφ
        rw [this]; exact hp
      · rw [if_neg hφ]; exact hg φ
    · intro h
      refine ⟨fun φ => ?_, ?_⟩
      · have := h φ
        split_ifs at this with hφ
        · rw [Finset.mem_singleton] at this; rw [this]; exact zero_mem_gridVals _
        · exact this
      · have := h ⟨pW, pW_mem_S1⟩
        rw [if_pos rfl, Finset.mem_singleton] at this
        exact this
  rw [heq, Fintype.card_piFinset, univ_S1, Finset.prod_pair subtype_p_ne_q]
  simp only [if_true, Finset.card_singleton]
  rw [if_neg pW_ne_qW.symm, card_gridVals (by norm_num)]
  norm_num

/-- **The face is a proper subset of the grid when a price is 0.**
Source: mandate T9; [[bli-program]] §7 item 11
Kind: N+
Fidelity: exact -/
lemma faceProd_t₀'_ssubset : faceProd witIndex witMesh.d 0 t₀' ⊂ grid witIndex witMesh.d 1 :=
  Finset.ssubset_iff_subset_ne.mpr ⟨faceProd_subset_grid _ _,
    fun h => Q₁_not_mem_faceProd (h ▸ Q₁_mem_grid)⟩

/-- **The worked witness, assembled** (T9): `d = 2 ≥ 2`, `|S 1| = 2 ≥ 2`; at the interior table
the face is the whole 9-point grid with mass `1/9` everywhere and total mass 1; at the pinned
table the face has 3 points of mass `1/3`, is a proper subset of the grid, and the off-face
point `(p ↦ 1/2, q ↦ 0)` has mass 0.
Source: mandate T9; [[bli-program]] §7 item 11 (checklist)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem worked_witness :
    witMesh.d 1 = 2 ∧ (witIndex.S 1).card = 2 ∧
    (grid witIndex witMesh.d 1).card = 9 ∧
    faceProd witIndex witMesh.d 0 t₀ = grid witIndex witMesh.d 1 ∧
    (∀ Q ∈ grid witIndex witMesh.d 1, tentLaw witMesh 0 t₀ Q = 1 / 9) ∧
    ∑ Q ∈ grid witIndex witMesh.d 1, tentLaw witMesh 0 t₀ Q = 1 ∧
    Balanced witMesh.d (tentLaw witMesh 0 t₀) t₀ ∧
    (faceProd witIndex witMesh.d 0 t₀').card = 3 ∧
    (∀ Q ∈ faceProd witIndex witMesh.d 0 t₀', tentLaw witMesh 0 t₀' Q = 1 / 3) ∧
    faceProd witIndex witMesh.d 0 t₀' ⊂ grid witIndex witMesh.d 1 ∧
    Q₁ ∈ grid witIndex witMesh.d 1 ∧ tentLaw witMesh 0 t₀' Q₁ = 0 := by
  refine ⟨rfl, by rw [witIndex_S_succ, Finset.card_pair pW_ne_qW], card_grid_witness, faceProd_t₀,
    fun Q hQ => tentLaw_t₀ hQ, sum_tentLaw_t₀, balanced_t₀, card_faceProd_t₀', ?_,
    faceProd_t₀'_ssubset, Q₁_mem_grid, tentLaw_t₀'_Q₁⟩
  intro Q hQ
  obtain ⟨hg, hp⟩ := (mem_faceProd_t₀'_iff Q).mp hQ
  rw [tentLaw_t₀' hg, if_pos hp]

end Cleanroom.Bli.BliFinite
