import Cleanroom.Bli.BliFinite.Tent

/-!
# `bli-superbelief` · Boundary: the grid without 0, full support on the whole grid, and the
surviving `FS` (E5)

The refutation package of the boundary (one refuted formulation per row, each beside its
surviving weakening; [[plan]] §0.4 rule 3):

* **(a)** Roman's grid **as printed**, `D = {1/d, …, 1}` without `0` (`posGridVals`/`posGrid`,
  refuted objects, *not* definitions of record): every balance solution over it has mean `≥ 1/d`
  in every coordinate, so exact agreement with a table pricing some small sentence below `1/d`
  (a contradiction priced `0`, say) has **no** balance solution (`posGrid_no_balance_below`).
  Surviving neighbour: `bli-finite`'s `gridVals` with `0` (`zero_mem_gridVals`).
* **(b)** full support over **all** of `D^S` (bli-slides-018's desideratum (6)) is inconsistent
  with exact agreement at a `0/1` price (`fullSupport_grid_contra_zeroOne`): the grid table
  disagreeing with `t` at the pinned coordinate must carry mass `0` by the pinning lemma.
* **(c)** the surviving weakening, non-degeneracy on the product face, is satisfiable at every
  unit-cube table by the tent kernel (`nonDegenerate_face_satisfiable`, cited from `bli-finite`),
  and is *strictly* weaker than full support exactly when `t` has a `0/1` coordinate
  (`faceProd_eq_grid_iff` in `Face.lean`; the instance `faceProd_t₀'_ssubset` in `bli-finite`).
  This is the artifact check ([[STANDARDS]] §3): (b) is about the source's formulation, not the
  encoding.

Sources: bli-slides-017 (the printed `D`), 018 (the desideratum), 021 (the two-line derivation),
025 (d) ("[0;1] boundaries" as a missing detail); [[bli-program]] §3.4 Boundary, §3.10 row E5,
§7 item 6. "Roman meant `0 ∉ D`" is ATTRIBUTION-UNVETTED (see the findings).
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction Finset Cleanroom.Bli.BliFinite

variable {𝒮 : SmallIndex} {m : ℕ}

/-! ## (a) The grid without 0 — the refuted object -/

/-- **Refuted object, not of record**: Roman's dot grid as printed, `{1/d, 2/d, …, 1}`, without
`0` (bli-slides-017). Defined here only to state `posGrid_no_balance_below` against it.
Source: bli-slides-017 (`D = {1/d, …, 1}`)
Kind: D
Fidelity: exact (the printed grid; refuted by `posGrid_no_balance_below`) -/
def posGridVals (d : ℕ) : Finset ℚ :=
  (Finset.range d).image (fun k : ℕ => ((k : ℚ) + 1) / d)

/-- **Refuted object, not of record**: the product of the printed grids on day-`m` tables.
Source: bli-slides-017 (`D^S`)
Kind: D
Fidelity: exact (refuted by `posGrid_no_balance_below`) -/
def posGrid (𝒮 : SmallIndex) (d : ℕ → ℕ) (m : ℕ) : Finset (Table 𝒮 m) :=
  Fintype.piFinset (fun _ => posGridVals (d m))

/-- Membership in the printed grid values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_posGridVals_iff {d : ℕ} {q : ℚ} :
    q ∈ posGridVals d ↔ ∃ k : ℕ, k < d ∧ q = ((k : ℚ) + 1) / d := by
  unfold posGridVals
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

/-- Every printed grid value is at least `1/d` (`0 < d`).
Source: bli-slides-017 flag ("every grid point has `𝒬(φ) ≥ 1/d`")
Kind: L
Fidelity: exact -/
lemma one_div_le_of_mem_posGridVals {d : ℕ} (hd : 0 < d) {q : ℚ} (hq : q ∈ posGridVals d) :
    1 / (d : ℚ) ≤ q := by
  obtain ⟨k, -, rfl⟩ := mem_posGridVals_iff.mp hq
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [div_le_div_iff_of_pos_right hdq]
  have : (0 : ℚ) ≤ k := by exact_mod_cast Nat.zero_le k
  linarith

/-- Membership in the printed product grid is coordinatewise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_posGrid_iff {d : ℕ → ℕ} {Q : Table 𝒮 m} :
    Q ∈ posGrid 𝒮 d m ↔ ∀ φ, Q φ ∈ posGridVals (d m) := by
  unfold posGrid; exact Fintype.mem_piFinset

/-- **The mean over the printed grid is at least `1/d` in every coordinate**: bli-slides-017's
constraint 4 with `0 ∉ D` forces `𝐏_n(φ) ≥ 1/d` for every small `φ`.
Source: bli-slides-017 (flag); [[bli-program]] §3.4 Boundary
Kind: P
Fidelity: exact
Hyps: (a) `0 < d (m+1)` -/
theorem posGrid_mean_ge {d : ℕ → ℕ} (hd : 0 < d (m + 1)) {F : Superbelief 𝒮 (m + 1)}
    (hF : IsProbOn (posGrid 𝒮 d (m + 1)) F) (φ : ↥(𝒮.S (m + 1))) :
    1 / (d (m + 1) : ℚ) ≤ meanOn (posGrid 𝒮 d (m + 1)) F φ := by
  calc 1 / (d (m + 1) : ℚ) = ∑ Q ∈ posGrid 𝒮 d (m + 1), F Q * (1 / (d (m + 1) : ℚ)) := by
        rw [← Finset.sum_mul, hF.2.2, one_mul]
    _ ≤ ∑ Q ∈ posGrid 𝒮 d (m + 1), F Q * Q φ :=
        Finset.sum_le_sum fun Q hQ =>
          mul_le_mul_of_nonneg_left (one_div_le_of_mem_posGridVals hd (mem_posGrid_iff.mp hQ φ)) (hF.1 Q)

/-- **E5(a), refutation.** Over the printed grid `D = {1/d, …, 1}` (no `0`), a day-`m` table with a
coordinate priced **below `1/d`** admits **no** balance solution: constraints 4–5 with exact
constraint 1 are jointly unsatisfiable there. Refuted: bli-slides-017's constraint set as printed,
on any day whose small set contains a sentence priced below `1/d` (a contradiction priced `0`,
say). Surviving neighbour: the grid with `0` (`bli-finite`'s `gridVals`, `zero_mem_gridVals`).
Two steps over `posGrid_mean_ge` (the inequality, Kind `P`).
Source: bli-slides-017 (flag), bli-slides-025 (d); [[bli-program]] §3.4 Boundary, §3.10 row E5
Kind: C
Fidelity: exact
Hyps: (a) `0 < d (m+1)`; (a) `t φ < 1 / d (m+1)` -/
theorem posGrid_no_balance_below {d : ℕ → ℕ} (hd : 0 < d (m + 1)) (t : Table 𝒮 m) (φ : ↥(𝒮.S m))
    (ht : t φ < 1 / (d (m + 1) : ℚ)) :
    ¬ ∃ F : Superbelief 𝒮 (m + 1),
      IsProbOn (posGrid 𝒮 d (m + 1)) F ∧ (meanOn (posGrid 𝒮 d (m + 1)) F).restrict = t := by
  rintro ⟨F, hF, hb⟩
  have h1 := posGrid_mean_ge hd hF ⟨φ.1, 𝒮.mono m φ.2⟩
  have h2 := congrFun hb φ
  rw [Table.restrict_apply] at h2
  linarith

/-! ## (b) Full support on the whole grid — refuted at a 0/1 price -/

/-- **E5(b), refutation.** On the grid with `0` and `1` (`0 < d (m+1)`), a probability with **full
support on the whole grid** cannot be balanced at a table with a `0/1` coordinate: the grid table
disagreeing with `t` at that coordinate carries positive mass, yet the pinning lemma
(`faceGen_subset_faceProd`) forces mass `0` there. Refuted: bli-slides-018's desideratum (6)
("`𝐏_n(𝐐_{n+1} = 𝒬) ≠ 0` for all `𝒬 ∈ D^S`") jointly with exact constraint 1 at a `0/1` price.
Surviving neighbour: `nonDegenerate_face_satisfiable`. Two lines over `bli-finite`'s pinning
lemmas (Kind `C`). Stated on the program's grid (with `0`): the price-`1` case uses the all-zeros
table, and on the deck's printed grid `{1/d, …, 1}` the same refutation goes through with the
table `φ ↦ 1/d`; the price-`0` case is not representable there at all (findings F-1).
Source: bli-slides-018 (desideratum), bli-slides-021 (the derivation); [[bli-program]] §3.4
Kind: C
Fidelity: exact
Hyps: (a) `0 < d (m+1)`; (a) the four clauses are the refuted package -/
theorem fullSupport_grid_contra_zeroOne {d : ℕ → ℕ} (hd : 0 < d (m + 1)) {F : Superbelief 𝒮 (m + 1)}
    {t : Table 𝒮 m} (hF : IsProb d F) (hb : Balanced d F t)
    (hfull : ∀ Q ∈ grid 𝒮 d (m + 1), 0 < F Q) (hφ : ∃ φ : ↥(𝒮.S m), t φ = 0 ∨ t φ = 1) : False := by
  obtain ⟨φ, hφ⟩ := hφ
  have key : ∀ Q ∈ grid 𝒮 d (m + 1), Q.restrict φ = t φ := fun Q hQ =>
    (mem_faceProd_iff.mp (faceGen_subset_faceProd d t
      (mem_faceGen_of_pos hF (balanced_iff_restrict_meanOn_eq.mp hb) (hfull Q hQ)))).2 φ hφ
  rcases hφ with h0 | h1
  · have := key (fun _ => 1) (mem_grid_iff.mpr fun _ => one_mem_gridVals hd)
    rw [Table.restrict_apply, h0] at this
    norm_num at this
  · have := key (fun _ => 0) (mem_grid_iff.mpr fun _ => zero_mem_gridVals _)
    rw [Table.restrict_apply, h1] at this
    norm_num at this

/-- The same refutation in the `NonDegenerate`-free spelling used by the desiderata: no `F` is
simultaneously a balanced grid probability at a table with a `0/1` coordinate and fully supported.
Source: bli-slides-018/021
Kind: C
Fidelity: exact
Hyps: (a) `0 < d (m+1)` -/
theorem not_fullSupport_of_zeroOne {d : ℕ → ℕ} (hd : 0 < d (m + 1)) {t : Table 𝒮 m}
    (hφ : ∃ φ : ↥(𝒮.S m), t φ = 0 ∨ t φ = 1) :
    ¬ ∃ F : Superbelief 𝒮 (m + 1), IsProb d F ∧ Balanced d F t ∧ ∀ Q ∈ grid 𝒮 d (m + 1), 0 < F Q :=
  fun ⟨_, hF, hb, hfull⟩ => fullSupport_grid_contra_zeroOne hd hF hb hfull hφ

/-! ## (c) The surviving weakening: non-degeneracy on the product face is satisfiable -/

/-- **E5(c), the surviving `FS`.** Non-degeneracy on the product face — positive mass on every grid
table agreeing with `t` at its `0/1` coordinates — is satisfiable at **every** unit-cube table,
by the tent kernel (`bli-finite`'s `tentLaw_isProb`, `tentLaw_balanced`, `tentLaw_nonDegenerate`,
cited). It is strictly weaker than full support exactly when `t` has a `0/1` coordinate
(`faceProd_eq_grid_iff`). This is the artifact check for (b).
Source: bli-slides-018 (surviving form), 021; [[bli-program]] §3.4 ("artifact check")
Kind: C
Fidelity: exact
Hyps: (a) `t.InUnit` -/
theorem nonDegenerate_face_satisfiable (𝓜 : Mesh) (t : Table 𝒮 m) (ht : t.InUnit) :
    ∃ F : Superbelief 𝒮 (m + 1), IsProb 𝓜.d F ∧ Balanced 𝓜.d F t ∧ NonDegenerate 𝓜.d F t :=
  ⟨tentLaw 𝓜 m t, tentLaw_isProb t, tentLaw_balanced ht, tentLaw_nonDegenerate ht⟩

/-- Non-degeneracy on the face never conflicts with a `0/1` price — while full support always does
(the two rows side by side): at a unit-cube `t` with a `0/1` coordinate, a non-degenerate balanced
solution exists and no fully supported one does.
Source: [[bli-program]] §3.4 Boundary; §7 item 6 (impossibility beside its weakening)
Kind: C
Fidelity: exact
Hyps: (a) `t.InUnit`; (a) a `0/1` coordinate exists -/
theorem nonDegenerate_yes_fullSupport_no (𝓜 : Mesh) (t : Table 𝒮 m) (ht : t.InUnit)
    (hφ : ∃ φ : ↥(𝒮.S m), t φ = 0 ∨ t φ = 1) :
    (∃ F : Superbelief 𝒮 (m + 1), IsProb 𝓜.d F ∧ Balanced 𝓜.d F t ∧ NonDegenerate 𝓜.d F t) ∧
    ¬ ∃ F : Superbelief 𝒮 (m + 1), IsProb 𝓜.d F ∧ Balanced 𝓜.d F t ∧
        ∀ Q ∈ grid 𝒮 𝓜.d (m + 1), 0 < F Q :=
  ⟨nonDegenerate_face_satisfiable 𝓜 t ht, not_fullSupport_of_zeroOne (𝓜.d_pos _) hφ⟩

end Cleanroom.Bli.BliSuperbelief
