import Cleanroom.Corrigibility.CorrReflectFrames.Collapse
import Cleanroom.Udt.UdtSupercondition.Anticipation

/-!
# corr-reflect-frames — T3(a) and T0's bridge to `udt-supercondition`

**Theorem A in SC vocabulary** (`calibrated_iff_reflective_and_introspective`): for any
anticipation structure on a same-ontology prior, SC-internal calibration is reflection together
with **introspection** (`Introspective`: every positive atom's kernel gives that atom probability
one — the one new predicate on anticipation structures this package adds). Proved directly in
`ℝ≥0∞`; `calibrated_implies_reflective` is SC's Prop 3.8 (⇒).

**The bridge**: a finite frame `(π, F)` becomes the anticipation structure with atoms the rows of
`F`, quotient `w ↦ F.P w`, kernel `ρ ↦ ρ` (`toAnticipation`, over `pmfOfSimplex π`), and
`Reflects ↔ Calibrated`, `EstimateMatching ↔ Reflective`, `CandsIntrospective ↔ Introspective`.
So T1's `reflects_iff_estimateMatching_and_int` and this file's Theorem A are one theorem; both
are proved directly (T1 over frames in `ℝ`, T3(a) over anticipation structures in `ℝ≥0∞`) and
`reflects_iff_estimateMatching_and_int_transported` re-derives the frame form through the
bridge as the consistency check.

`pmfOfSimplex` generalizes `udt-supercondition`'s `pmfOfReal` (on `Fin n`) to any `Fintype`
carrier, as the mandate asks, rather than importing that package's witness file.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames
open Cleanroom.Udt.UdtSupercondition (AnticipationStructure)
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Introspection for anticipation structures; Theorem A over SC's objects -/

section General

variable {Ω : Type} {P : PMF Ω}

/-- **Introspection** of an anticipation structure (same ontology): every atom `ā` of positive
prior mass has a kernel `κ_ā` giving the atom itself probability one — the future belief knows
which belief it is. Radical's INT / Armstrong's "introspection of `ρ_j`" in SC vocabulary.
Source: [[radical]] S1 (INT) l. 17; [[armstrong]] S16; mandate T0
Kind: D
Fidelity: exact (restricted to positive atoms, as INT is restricted to the range on the support)
Scope: same ontology `Q = Ω` -/
def Introspective (as : AnticipationStructure P Ω) : Prop :=
  ∀ ā, 0 < (P.map as.a) ā →
    Cleanroom.Udt.UdtSupercondition.mass (as.κ ā) (as.a ⁻¹' {ā}) = 1

/-- Under introspection the kernel of a positive atom vanishes off the atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Introspective.zero_of_ne {as : AnticipationStructure P Ω} (h : Introspective as) {ā : as.A}
    (hā : 0 < (P.map as.a) ā) {x : Ω} (hx : as.a x ≠ ā) : as.κ ā x = 0 := by
  have := (Cleanroom.Udt.UdtSupercondition.mass_eq_one_iff _ _).1 (h ā hā)
  by_contra hne
  exact hx (this x hne)

/-- **Theorem A in SC vocabulary (T3(a)).** For an anticipation structure on a same-ontology
prior, SC-internal calibration (`P(· | ā) = κ_ā` on positive atoms) holds iff the structure is
reflective (`Q₀ = P`, the martingale condition) **and** introspective. (⇒) is SC Prop 3.8 plus
Theorem A(c) (`P(ā ∩ {x}) = κ_ā(x) · P(ā)` with `x ∉ ā` forces `κ_ā(x) = 0`); (⇐) is Theorem
A(a): at `x ∈ ā`, reflection's sum `∑_b P(b) κ_b(x)` collapses to the `b = ā` term by
introspection. The converse of Prop 3.8 fails without introspection:
`reflective_not_calibrated_witness` (`as38`) in `udt-supercondition`, and the twist family here.
Source: [[radical]] Theorem I3.3(b) l. 108 (the survivor reading), Theorem I4.1;
[[armstrong]] Theorem A l. 103–109
Kind: P
Fidelity: exact (point-set over any type `Ω`; SC-internal calibration)
Hyps: (a) none
Scope: same ontology; `Introspective` is the scope predicate, in the statement -/
theorem calibrated_iff_reflective_and_introspective (as : AnticipationStructure P Ω) :
    as.Calibrated ↔ as.Reflective ∧ Introspective as := by
  constructor
  · intro h
    refine ⟨Cleanroom.Udt.UdtSupercondition.calibrated_implies_reflective h, ?_⟩
    intro ā hā
    rw [Cleanroom.Udt.UdtSupercondition.mass_eq_one_iff]
    intro x hx
    by_contra hnot
    have hc := h ā x
    have h0 : Cleanroom.Udt.UdtSupercondition.mass P (as.a ⁻¹' {ā} ∩ {x}) = 0 := by
      rw [Cleanroom.Udt.UdtSupercondition.mass_inter_singleton, Set.indicator_of_notMem hnot]
    rw [h0] at hc
    rcases mul_eq_zero.1 hc.symm with h1 | h1
    · exact hx h1
    · exact hā.ne' h1
  · rintro ⟨hR, hI⟩ ā x
    rw [Cleanroom.Udt.UdtSupercondition.mass_inter_singleton]
    by_cases hā : 0 < (P.map as.a) ā
    · by_cases hx : x ∈ as.a ⁻¹' {ā}
      · rw [Set.indicator_of_mem hx]
        have hxa : as.a x = ā := hx
        have hRx : as.priorPredictive x = P x := by rw [hR]
        rw [AnticipationStructure.priorPredictive_apply, tsum_eq_single ā] at hRx
        · rw [← hRx]; ring
        · intro b hb
          by_cases hb0 : (P.map as.a) b = 0
          · rw [hb0, zero_mul]
          · have hbpos : 0 < (P.map as.a) b := pos_iff_ne_zero.2 hb0
            rw [hI.zero_of_ne hbpos (by rw [hxa]; exact hb.symm), mul_zero]
      · rw [Set.indicator_of_notMem hx, hI.zero_of_ne hā hx, zero_mul]
    · have h0 : (P.map as.a) ā = 0 := le_antisymm (not_lt.1 hā) zero_le
      rw [h0, mul_zero]
      by_cases hx : x ∈ as.a ⁻¹' {ā}
      · rw [Set.indicator_of_mem hx]
        have := Cleanroom.Udt.UdtSupercondition.apply_le_mass P hx
        rw [← as.map_a_apply, h0] at this
        exact le_antisymm this zero_le
      · rw [Set.indicator_of_notMem hx]

end General

/-! ## The bridge: a frame as an anticipation structure -/

section Frames

variable {W : Type} [Fintype W] [DecidableEq W]

/-- A `PMF` on a finite carrier from a point of the standard simplex (`pmfOfReal` generalized
from `Fin n` to any `Fintype`).
Source: none: infrastructure (bridge; mandate T0)
Kind: D
Fidelity: n/a -/
def pmfOfSimplex (ρ : W → ℝ) (hρ : ρ ∈ stdSimplex ℝ W) : PMF W :=
  PMF.ofFintype (fun w => ENNReal.ofReal (ρ w))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hρ.1 i), hρ.2, ENNReal.ofReal_one])

/-- The mass function of `pmfOfSimplex`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem pmfOfSimplex_apply (ρ : W → ℝ) (hρ : ρ ∈ stdSimplex ℝ W) (w : W) :
    pmfOfSimplex ρ hρ w = ENNReal.ofReal (ρ w) := rfl

/-- SC's mass of a finite event under `pmfOfSimplex` is `ofReal` of the frame mass.
Source: none: infrastructure (the `ℝ ↔ ℝ≥0∞` conversion)
Kind: L
Fidelity: n/a -/
theorem scmass_pmfOfSimplex (ρ : W → ℝ) (hρ : ρ ∈ stdSimplex ℝ W) (A : Finset W) :
    Cleanroom.Udt.UdtSupercondition.mass (pmfOfSimplex ρ hρ) (↑A : Set W) =
      ENNReal.ofReal (mass ρ A) := by
  rw [Cleanroom.Udt.UdtSupercondition.mass, PMF.toOuterMeasure_apply_finset]
  simp only [pmfOfSimplex_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hρ.1 i)]
  rfl

/-- Every row of a frame is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_stdSimplex_of_mem_rows {F : Frame W} {ρ : W → ℝ} (h : ρ ∈ univ.image F.P) :
    ρ ∈ stdSimplex ℝ W := by
  obtain ⟨w, _, rfl⟩ := mem_image.1 h; exact F.P_mem w

/-- Candidates are rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cands_subset_rows (F : Frame W) (π : W → ℝ) {ρ : W → ℝ} (h : ρ ∈ F.cands π) :
    ρ ∈ univ.image F.P :=
  image_subset_image (subset_univ _) h

/-- **A frame as an anticipation structure**: atoms are the rows of `F` (a finite subtype, hence
countable), the quotient sends a world to its row, and the kernel of a row is the row itself.
The prior is a parameter, normally `pmfOfSimplex π hπ`.
Source: [[radical]] Def I3.2 l. 104 (the meta-belief event `E_ρ = {P_{t+1} = ρ}`), [[mm]]
Prop I3.1 l. 125; mandate T0
Kind: D
Fidelity: exact -/
def toAnticipation (F : Frame W) (P : PMF W) : AnticipationStructure P W where
  A := {ρ : W → ℝ // ρ ∈ univ.image F.P}
  countable := @Finite.to_countable _ (@Finite.of_fintype _ (Finset.Subtype.fintype (univ.image F.P)))
  a := fun w => ⟨F.P w, mem_image_of_mem _ (mem_univ w)⟩
  κ := fun ρ => pmfOfSimplex ρ.1 (mem_stdSimplex_of_mem_rows ρ.2)

/-- The atoms of a frame's anticipation structure form a finite type.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance instFintypeAtoms (F : Frame W) (P : PMF W) : Fintype (toAnticipation F P).A :=
  Finset.Subtype.fintype (univ.image F.P)

/-- The atom of a row is its cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toAnticipation_preimage (F : Frame W) (P : PMF W) (ā : (toAnticipation F P).A) :
    (toAnticipation F P).a ⁻¹' {ā} = (↑(F.cell ā.1) : Set W) := by
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff, mem_coe, Frame.mem_cell, toAnticipation]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The atom mass of a row is `ofReal` of its cell mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toAnticipation_map_apply {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W)
    (ā : (toAnticipation F (pmfOfSimplex π hπ)).A) :
    (pmfOfSimplex π hπ).map (toAnticipation F (pmfOfSimplex π hπ)).a ā =
      ENNReal.ofReal (mass π (F.cell ā.1)) := by
  rw [AnticipationStructure.map_a_apply, toAnticipation_preimage, scmass_pmfOfSimplex]

/-- The kernel of a row at a world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toAnticipation_κ_apply (F : Frame W) (P : PMF W) (ā : (toAnticipation F P).A) (x : W) :
    (toAnticipation F P).κ ā x = ENNReal.ofReal (ā.1 x) := rfl

/-- **Bridge (i): Reflection is SC-internal calibration** of the frame's anticipation
structure (over all rows; at a null row both sides vanish).
Source: [[mm]] Prop I3.1 l. 125 ("Reflection is superconditioning on 'I will believe this'");
mandate T0
Kind: L
Fidelity: exact
Hyps: (a) `hπ` only -/
theorem reflects_iff_calibrated {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    Reflects π F ↔ (toAnticipation F (pmfOfSimplex π hπ)).Calibrated := by
  have key : ∀ (ā : (toAnticipation F (pmfOfSimplex π hπ)).A) (x : W),
      (Cleanroom.Udt.UdtSupercondition.mass (pmfOfSimplex π hπ)
          ((toAnticipation F (pmfOfSimplex π hπ)).a ⁻¹' {ā} ∩ {x}) =
        (toAnticipation F (pmfOfSimplex π hπ)).κ ā x *
          (pmfOfSimplex π hπ).map (toAnticipation F (pmfOfSimplex π hπ)).a ā) ↔
      (π x * ind (F.cell ā.1) x = mass π (F.cell ā.1) * ā.1 x) := by
    intro ā x
    rw [toAnticipation_map_apply, toAnticipation_preimage, toAnticipation_κ_apply,
      ← coe_singleton, ← coe_inter, scmass_pmfOfSimplex,
      ← ENNReal.ofReal_mul ((mem_stdSimplex_of_mem_rows ā.2).1 x),
      ENNReal.ofReal_eq_ofReal_iff (mass_nonneg hπ.1 _)
        (mul_nonneg ((mem_stdSimplex_of_mem_rows ā.2).1 x) (mass_nonneg hπ.1 _))]
    have hm : mass π (F.cell ā.1 ∩ {x}) = π x * ind (F.cell ā.1) x := by
      by_cases hx : x ∈ F.cell ā.1
      · rw [inter_eq_right.2 (singleton_subset_iff.2 hx), mass_singleton]; simp [ind, hx]
      · have : F.cell ā.1 ∩ {x} = ∅ := by
          ext y; simp only [mem_inter, mem_singleton, notMem_empty, iff_false, not_and]
          rintro hy rfl; exact hx hy
        rw [this]; simp [mass, ind, hx]
    rw [hm, mul_comm (ā.1 x)]
  constructor
  · intro h ā x
    rw [key]
    by_cases hc : ā.1 ∈ F.cands π
    · exact h ā.1 hc x
    · have hm := mass_cell_eq_zero_of_not_mem_cands hπ.1 F hc
      rw [hm, zero_mul]
      by_cases hx : x ∈ F.cell ā.1
      · rw [eq_zero_of_mass_eq_zero hπ.1 hm hx, zero_mul]
      · simp [ind, hx]
  · intro h ρ hρ x
    have := h ⟨ρ, cands_subset_rows F π hρ⟩ x
    rw [key] at this
    exact this

/-- The prior-predictive of the frame's anticipation structure is `ofReal` of `πP`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toAnticipation_priorPredictive {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W)
    (x : W) : (toAnticipation F (pmfOfSimplex π hπ)).priorPredictive x =
      ENNReal.ofReal (∑ w, π w * F.P w x) := by
  letI : Fintype (toAnticipation F (pmfOfSimplex π hπ)).A :=
    inferInstanceAs (Fintype {ρ : W → ℝ // ρ ∈ univ.image F.P})
  rw [AnticipationStructure.priorPredictive_apply, tsum_fintype]
  have e : ∀ ā : (toAnticipation F (pmfOfSimplex π hπ)).A,
      (pmfOfSimplex π hπ).map (toAnticipation F (pmfOfSimplex π hπ)).a ā *
        (toAnticipation F (pmfOfSimplex π hπ)).κ ā x =
      ENNReal.ofReal (mass π (F.cell ā.1) * ā.1 x) := by
    intro ā
    rw [toAnticipation_map_apply, toAnticipation_κ_apply, ENNReal.ofReal_mul (mass_nonneg hπ.1 _)]
  rw [sum_congr rfl (fun ā _ => e ā),
    ← ENNReal.ofReal_sum_of_nonneg (fun ā _ =>
      mul_nonneg (mass_nonneg hπ.1 _) ((mem_stdSimplex_of_mem_rows ā.2).1 x))]
  congr 1
  show ∑ ā : {ρ : W → ℝ // ρ ∈ univ.image F.P}, mass π (F.cell ā.1) * ā.1 x = _
  rw [sum_coe_sort (univ.image F.P) (fun ρ => mass π (F.cell ρ) * ρ x),
    sum_rowClosed F (fun _ _ _ _ => mem_univ _) (fun w => π w * F.P w x)]
  apply sum_congr rfl
  intro ρ _
  unfold mass
  rw [sum_mul]
  apply sum_congr rfl
  intro w hw
  rw [Frame.mem_cell.1 hw]

/-- **Bridge (ii): estimate matching is SC's reflection** (prior-predictive equals prior) of the
frame's anticipation structure.
Source: [[radical]] Theorem I3.3(b) l. 108 (`∑ q_i ρ_i = P_t`); mandate T0
Kind: L
Fidelity: exact
Hyps: (a) `hπ` only -/
theorem estimateMatching_iff_reflective {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    EstimateMatching π F ↔ (toAnticipation F (pmfOfSimplex π hπ)).Reflective := by
  rw [estimateMatching_iff_stationary]
  unfold AnticipationStructure.Reflective
  constructor
  · intro h
    apply PMF.ext; intro x
    rw [toAnticipation_priorPredictive, h x]; rfl
  · intro h x
    have := DFunLike.congr_fun h x
    rw [toAnticipation_priorPredictive, pmfOfSimplex_apply,
      ENNReal.ofReal_eq_ofReal_iff (sum_nonneg (fun w _ => mul_nonneg (hπ.1 w) (F.P_nonneg w x)))
        (hπ.1 x)] at this
    exact this

/-- **Bridge (iii): introspection at candidates is introspection** of the frame's anticipation
structure.
Source: [[radical]] S1 (INT); mandate T0
Kind: L
Fidelity: exact
Hyps: (a) `hπ` only -/
theorem candsIntrospective_iff_introspective {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (F : Frame W) :
    CandsIntrospective π F ↔ Introspective (toAnticipation F (pmfOfSimplex π hπ)) := by
  have hmap : ∀ ā : (toAnticipation F (pmfOfSimplex π hπ)).A,
      (0 < (pmfOfSimplex π hπ).map (toAnticipation F (pmfOfSimplex π hπ)).a ā ↔
        ā.1 ∈ F.cands π) := by
    intro ā
    rw [toAnticipation_map_apply, ENNReal.ofReal_pos]
    exact (F.mem_cands_iff_mass_cell_pos hπ.1).symm
  have hκ : ∀ ā : (toAnticipation F (pmfOfSimplex π hπ)).A,
      (Cleanroom.Udt.UdtSupercondition.mass ((toAnticipation F (pmfOfSimplex π hπ)).κ ā)
          ((toAnticipation F (pmfOfSimplex π hπ)).a ⁻¹' {ā}) = 1 ↔ F.selfMass ā.1 = 1) := by
    intro ā
    rw [toAnticipation_preimage]
    show Cleanroom.Udt.UdtSupercondition.mass (pmfOfSimplex ā.1 (mem_stdSimplex_of_mem_rows ā.2))
      (↑(F.cell ā.1) : Set W) = 1 ↔ _
    rw [scmass_pmfOfSimplex, ENNReal.ofReal_eq_one]
    rfl
  constructor
  · intro h ā hā
    rw [hκ]; exact h ā.1 ((hmap ā).1 hā)
  · intro h ρ hρ
    have := h ⟨ρ, cands_subset_rows F π hρ⟩ ((hmap _).2 hρ)
    rwa [hκ] at this

/-- **Theorem A transported.** T1's INT-free collapse `Reflects ↔ EstimateMatching ∧ INT` re-derived
from the SC-vocabulary Theorem A through the bridge — the consistency check that T1 and T3(a) are
one theorem.
Source: [[armstrong]] Theorem A l. 108; mandate T3(a) ("prove one and transport the other")
Kind: C
Fidelity: exact
Hyps: (a) `hπ` only -/
theorem reflects_iff_estimateMatching_and_int_transported {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (F : Frame W) : Reflects π F ↔ EstimateMatching π F ∧ CandsIntrospective π F := by
  rw [reflects_iff_calibrated hπ, estimateMatching_iff_reflective hπ,
    candsIntrospective_iff_introspective hπ]
  exact calibrated_iff_reflective_and_introspective _

end Frames

end

end Cleanroom.Corrigibility.CorrReflectFrames
