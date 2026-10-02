import Cleanroom.Decision.DpFirstpersonSc.Grades

/-!
# SC's refinement measure does not track expressibility (AN-15) — T10(a) of
[[dp-firstperson-sc-mandate]]

On the lifted prior `μ = runPMF C B` with the *observation* anticipation algebra
`Ā_obs = σ{λ⁻¹O_e : e ∈ queried B}` (`obsAtom`), the density of Proposition 2's state
`P' = μ(· | occ(d))` w.r.t. `μ` is `1_{occ(d)}/μ(occ(d))`. It is constant on the atoms of `Ā_obs`
— i.e. `P'` is SC §4.6's Jeffrey posterior on `Ā_obs`, `JeffreyOnA μ obsAtom P'`, equivalently
SC open question 1's measure (the conditional entropy of `dP'/dμ` given `Ā_obs`) vanishes — **iff
`occ(d)` is a.s. a union of observation atoms** (`OccUnionOfObsAtoms`):
`density_const_iff_occ_union`, through `udt-supercondition`'s `jeffreyOnA_iff_density_const`.

For the *strict-OC* state the density is constant on the observation atoms on **every** tree
(`density_const_obs`: `λ⁻¹O_d` is a union of them when `d` is queried), so the measure's verdict
on the OC/SSC pair is `density_const_iff_occ_union`'s condition alone — both halves of F7 are
Lean facts (repair round 1, audit r1 fidelity N6).

Consequences (the finding against SC open question 1): on `mug1` and TN-V2 (`occ(d) = ⊤`,
`occ_univ_occUnion`) the density is constant for the per-run state and the strict-OC state alike
— the measure sees no OC/SSC difference on the flagship examples; on the radical-label tree
(evented chance `A/B`, `O_d = ⊤`, `occ(d) = λ⁻¹{side = A}`: *expressible*) it is non-constant
(`WitnessesLicense.lean`). The measure tracks `𝓔`-expressibility in **exactly one direction**
(repair round 2, audit r2 adversarial B2): an a.s. union of observation atoms is automatically
occurrence-expressible (`occUnion_occExpressible` — the atoms are pulled back from `Ω`-events, so
leaves with equal worlds have equal atoms), hence **the measure fires on every non-expressible
`occ(d)`** (`not_occExpressible_measure_fires`: AN-15(b)'s surviving half as a theorem); the
converse fails (the radical-label tree: expressible, fires), and the measure is silent on
`B₁`/TN-V2 where OC and SSC differ. So it is neither a test of expressibility nor a test of the
OC/SSC difference. AN-15(b) is dead (`anticipation.md` Dead 6) in its "exactly when" form; this is
the surviving (b′) plus (b)'s positive direction. The entropy form (T10(b)) is stretch and not
built.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Decision.DpCalibration
open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Finset

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (obs : ι → Finset Ω) (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ)

/-- **The observation anticipation algebra on the run space**: a leaf's atom is the profile
`e ↦ [λ(ℓ) ∈ O_e]` over the queried points.
Source: `anticipation.md` AN-15 (`Ā_obs`)
Kind: D -/
def obsAtom : B.Leaves → (↥(queried B) → Bool) := fun ℓ e => decide (world B ℓ ∈ obs e.1)

/-- **`occ(d)` is a.s. a union of observation atoms**: two positive-mass leaves in one
observation atom are both in `occ(d)` or both outside.
Source: `anticipation.md` AN-15(b′) ("`occ(d) ∉ Ā_obs` mod `μ`-null")
Kind: D -/
def OccUnionOfObsAtoms (d : ι) : Prop :=
  ∀ ℓ ℓ', 0 < leafLaw C B ℓ → 0 < leafLaw C B ℓ' → obsAtom obs B ℓ = obsAtom obs B ℓ' →
    (ℓ ∈ occ d B ↔ ℓ' ∈ occ d B)

/-- A leaf is `μ`-null iff its law is zero. Source: none: infrastructure. Kind: L -/
theorem runPMF_eq_zero_iff (ℓ : B.Leaves) : runPMF C B ℓ = 0 ↔ ¬ 0 < leafLaw C B ℓ := by
  rw [runPMF, toPMF_eq_zero_iff]
  show leafLaw C B ℓ = 0 ↔ _
  constructor
  · intro h; rw [h]; exact lt_irrefl 0
  · intro h; exact le_antisymm (not_lt.mp h) (leafLaw_nonneg C B ℓ)

/-- **AN-15(b′): the density of `μ(· | occ(d))` is constant on the observation atoms iff
`occ(d)` is a.s. a union of them.** Left side: SC's Jeffrey-on-`Ā_obs` predicate (density
constant on atoms, `jeffreyOnA_iff_density_const`); right side: the null-set statement.
Source: `anticipation.md` AN-15(b′) ("`H(dP'/dP | Ā_obs) > 0` iff `occ(d) ∉ Ā_obs` mod `μ`-null")
Kind: P
Fidelity: exact (constancy in SC's multiplicative form; the entropy form is not built)
Hyps: (a) `0 < μ(occ(d))` -/
theorem density_const_iff_occ_union (d : ι) (h : 0 < Tree.mass C B (occ d B)) :
    JeffreyOnA (runPMF C B) (obsAtom obs B)
        (condOn (runPMF C B) (↑(occ d B) : Set B.Leaves) ((mass_runPMF_pos_iff C B _).mpr h)) ↔
      OccUnionOfObsAtoms obs C B d := by
  rw [jeffreyOnA_iff_density_const]
  have hM : 0 < mass (runPMF C B) (↑(occ d B) : Set B.Leaves) :=
    (mass_runPMF_pos_iff C B (occ d B)).mpr h
  have hM0 : (mass (runPMF C B) (↑(occ d B) : Set B.Leaves))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.2 (mass_ne_top _ _)
  have hc : ∀ ℓ, condOn (runPMF C B) (↑(occ d B) : Set B.Leaves) hM ℓ =
      (if ℓ ∈ occ d B then runPMF C B ℓ else 0) *
        (mass (runPMF C B) (↑(occ d B) : Set B.Leaves))⁻¹ := by
    intro ℓ
    rw [condOn_apply]
    congr 1
    by_cases hℓ : ℓ ∈ occ d B
    · rw [Set.indicator_of_mem (Finset.mem_coe.mpr hℓ), if_pos hℓ]
    · rw [Set.indicator_of_notMem (fun h' => hℓ (Finset.mem_coe.mp h')), if_neg hℓ]
  constructor
  · rintro ⟨-, hconst⟩ ℓ ℓ' hℓ hℓ' hatom
    have := hconst ℓ ℓ' hatom
    rw [hc, hc] at this
    have hP : runPMF C B ℓ ≠ 0 := fun h0 => (runPMF_eq_zero_iff C B ℓ).mp h0 hℓ
    have hP' : runPMF C B ℓ' ≠ 0 := fun h0 => (runPMF_eq_zero_iff C B ℓ').mp h0 hℓ'
    by_cases h1 : ℓ ∈ occ d B <;> by_cases h2 : ℓ' ∈ occ d B
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · exfalso
      rw [if_pos h1, if_neg h2, zero_mul, zero_mul] at this
      exact (mul_ne_zero (mul_ne_zero hP hM0) hP') this
    · exfalso
      rw [if_neg h1, if_pos h2, zero_mul, zero_mul] at this
      exact (mul_ne_zero (mul_ne_zero hP' hM0) hP) this.symm
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  · intro hu
    refine ⟨fun ℓ h0 => ?_, fun ℓ ℓ' hatom => ?_⟩
    · rw [hc, h0]
      simp
    · rw [hc, hc]
      by_cases hℓ : 0 < leafLaw C B ℓ
      · by_cases hℓ' : 0 < leafLaw C B ℓ'
        · have hiff := hu ℓ ℓ' hℓ hℓ' hatom
          by_cases h1 : ℓ ∈ occ d B
          · rw [if_pos h1, if_pos (hiff.mp h1)]; ring
          · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.mpr h2))]; simp
        · have h0 : runPMF C B ℓ' = 0 := (runPMF_eq_zero_iff C B ℓ').mpr hℓ'
          rw [h0]
          simp
      · have h0 : runPMF C B ℓ = 0 := (runPMF_eq_zero_iff C B ℓ).mpr hℓ
        rw [h0]
        simp

/-- When `occ(d)` is every run the condition holds trivially — `mug1`, TN-V2 at both points: the
refinement measure is `0` for the per-run state, as for the strict-OC state; it cannot see the
OC/SSC difference there.
Source: `anticipation.md` AN-15(a) ("`B₁` and TN-V2 (`occ = λ⁻¹⊤`) … SC open question 1's measure
is `0` for both")
Kind: L -/
theorem occ_univ_occUnion (d : ι) (h : occ d B = Finset.univ) : OccUnionOfObsAtoms obs C B d := by
  intro ℓ ℓ' _ _ _
  simp [h]

/-- **The OC half of F7: the strict-OC state's density is constant on the observation atoms, on
every tree.** `ν(· | O_d)` lifted to the run space is `μ(· | λ⁻¹O_d)`, whose density
`1_{λ⁻¹O_d}/ν(O_d)` is constant on each atom of `Ā_obs` because `λ⁻¹O_d` is a union of them
(`d` queried). So SC's refinement measure is `0` for the strict-OC state everywhere, and with
`density_const_iff_occ_union` it sees the OC/SSC difference iff `occ(d)` is not a.s. a union of
observation atoms.
Source: `anticipation.md` AN-15(a) ("for the strict-OC state the density is constant on `Ā_obs`");
findings F7; audit r1 fidelity N6
Kind: L (`λ⁻¹O_d` is a union of observation atoms because the atom carries the `d`-coordinate;
audit r2 adversarial N4)
Fidelity: exact
Hyps: (a) `d ∈ queried B`, (a) `0 < ν(O_d)` -/
theorem density_const_obs (d : ι) (hd : d ∈ queried B) (hO : 0 < nu C B (obs d)) :
    JeffreyOnA (runPMF C B) (obsAtom obs B)
      (condOn (runPMF C B) (↑(worldEv B (obs d)) : Set B.Leaves)
        ((mass_runPMF_pos_iff C B (worldEv B (obs d))).mpr hO)) := by
  rw [jeffreyOnA_iff_density_const]
  have hM : 0 < mass (runPMF C B) (↑(worldEv B (obs d)) : Set B.Leaves) :=
    (mass_runPMF_pos_iff C B _).mpr hO
  have hc : ∀ ℓ, condOn (runPMF C B) (↑(worldEv B (obs d)) : Set B.Leaves) hM ℓ =
      (if ℓ ∈ worldEv B (obs d) then runPMF C B ℓ else 0) *
        (mass (runPMF C B) (↑(worldEv B (obs d)) : Set B.Leaves))⁻¹ := by
    intro ℓ
    rw [condOn_apply]
    congr 1
    by_cases hℓ : ℓ ∈ worldEv B (obs d)
    · rw [Set.indicator_of_mem (Finset.mem_coe.mpr hℓ), if_pos hℓ]
    · rw [Set.indicator_of_notMem (fun h' => hℓ (Finset.mem_coe.mp h')), if_neg hℓ]
  refine ⟨fun ℓ h0 => ?_, fun ℓ ℓ' hatom => ?_⟩
  · rw [hc, h0]; simp
  · have hiff : ℓ ∈ worldEv B (obs d) ↔ ℓ' ∈ worldEv B (obs d) := by
      have := congrFun hatom ⟨d, hd⟩
      simp only [obsAtom, decide_eq_decide] at this
      simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
      exact this
    rw [hc, hc]
    by_cases h1 : ℓ ∈ worldEv B (obs d)
    · rw [if_pos h1, if_pos (hiff.mp h1)]; ring
    · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.mpr h2))]; simp

/-- **An a.s. union of observation atoms is occurrence-expressible**, with the event
`X := {λ(ℓ) : ℓ ∈ occ(d), μ(ℓ) > 0}`: `obsAtom` depends on a leaf only through its world, so two
positive leaves with the same world have the same atom and (`OccUnionOfObsAtoms`) agree on
membership in `occ(d)` — `occ(d)` is a.s. a union of world fibres. This is the direction of
AN-15(b) that survives Dead 6; its converse fails (the radical-label tree).
Source: `anticipation.md` AN-15(b) ("positive when `occ(d) ∉ λ⁻¹(𝓔)`"), Dead 6; audit r2
adversarial B2 (the probe's proof adopted)
Kind: P
Fidelity: exact
Hyps: (a) `OccUnionOfObsAtoms` -/
theorem occUnion_occExpressible (d : ι) (h : OccUnionOfObsAtoms obs C B d) :
    OccExpressible C B d := by
  refine ⟨Finset.univ.filter fun ω => ∃ ℓ ∈ occ d B, 0 < leafLaw C B ℓ ∧ world B ℓ = ω, ?_, ?_⟩
  · rw [mass_eq_zero_iff]
    intro ℓ hℓ
    rw [Finset.mem_sdiff] at hℓ
    by_contra hne
    have hpos : 0 < leafLaw C B ℓ := lt_of_le_of_ne (leafLaw_nonneg C B ℓ) (Ne.symm hne)
    apply hℓ.2
    simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ℓ, hℓ.1, hpos, rfl⟩
  · rw [mass_eq_zero_iff]
    intro ℓ hℓ
    rw [Finset.mem_sdiff] at hℓ
    by_contra hne
    have hpos : 0 < leafLaw C B ℓ := lt_of_le_of_ne (leafLaw_nonneg C B ℓ) (Ne.symm hne)
    have hX := hℓ.1
    simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨ℓ', hℓ'occ, hℓ'pos, hw⟩ := hX
    have hatom : obsAtom obs B ℓ = obsAtom obs B ℓ' := by
      funext e; simp only [obsAtom, hw]
    exact hℓ.2 ((h ℓ ℓ' hpos hℓ'pos hatom).mpr hℓ'occ)

/-- **The measure fires on every non-expressible `occ(d)`**: if `occ(d)` is not
occurrence-expressible, the density of `μ(· | occ(d))` is not constant on the observation atoms —
SC open question 1's measure is positive there (AN-15(b)'s surviving direction). Together with
`radicalLabel_occExpressible` + `radicalLabel_not_occUnion` (expressible, fires) and
`occ_univ_occUnion` (`B₁`/TN-V2: silent), the measure tracks expressibility in this direction
only.
Source: `anticipation.md` AN-15(b) ("positive when `occ(d) ∉ λ⁻¹(𝓔)`"); audit r2 adversarial B2
Kind: L (contrapositive of `occUnion_occExpressible` through `density_const_iff_occ_union`)
Fidelity: exact
Hyps: (a) `0 < μ(occ(d))`, (a) `¬ OccExpressible` -/
theorem not_occExpressible_measure_fires (d : ι) (h : 0 < Tree.mass C B (occ d B))
    (hne : ¬ OccExpressible C B d) :
    ¬ JeffreyOnA (runPMF C B) (obsAtom obs B)
        (condOn (runPMF C B) (↑(occ d B) : Set B.Leaves) ((mass_runPMF_pos_iff C B _).mpr h)) :=
  fun hJ => hne (occUnion_occExpressible obs C B d
    ((density_const_iff_occ_union obs C B d h).mp hJ))

end Cleanroom.Decision.DpFirstpersonSc
