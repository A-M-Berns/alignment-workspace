import Cleanroom.Corrigibility.CorrReflectFrames.Bridge
import Cleanroom.Udt.UdtSupercondition.DZ
import Cleanroom.Udt.UdtSupercondition.Witnesses

/-!
# corr-reflect-frames — T3(b)–(e): the meta-belief representation

**Existence form** (Armstrong I3.2 = radical I3.3(b) read correctly): for candidate future
beliefs `q : I → PMF Ω` with weights `w : PMF I`, a joint on `Ω × I` with `Ω`-marginal `P`,
`I`-marginal `w` and conditional `q i` given `{snd = i}` (general reflection) exists iff
`∑ᵢ wᵢ qᵢ = P`; the joint is `metaJoint q w`, `(ω, i) ↦ w i · q i ω`, and it is forced.

**Refuted reading** (radical I3.3(b) as printed, fixed joint): with the anticipation structure
fixed, "endorses its own output iff `∑ q_i ρ_i = P`" fails in the ⇐ direction —
`udt-supercondition`'s `as38` is reflective and not calibrated; the twist family is the same
phenomenon on frames. The survivor is Theorem A (`Bridge.lean`, with introspection) and the
existence form here (a *new* joint, which is what the printed ⇐ proof constructs).

**D–Z**: `sameOntology_condModel_iff_of_fintype` is I3.1 finite (`udt-supercondition`, cited,
not re-proved); I3.3(a) is total probability (`sum_condOn_mass`).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Cleanroom.Udt.UdtSupercondition (AnticipationStructure condOn)
open scoped ENNReal
open Set

noncomputable section

set_option linter.unusedSectionVars false

section Existence

variable {Ω I : Type} [Fintype I] [DecidableEq I]

/-- **The meta-belief joint** `J(ω, i) = w i · q i ω` on `Ω × I`: the superconditioning space
whose event `{snd = i}` ("I will believe `q i`") has conditional `q i`.
Source: [[armstrong]] I3.2 l. 111 (`J(ω, k) = w_k q_k(ω)`); [[radical]] Theorem I3.3(b) ⇐
proof l. 108 (`K(i | ω) := q_i ρ_i(ω) / P_t(ω)`)
Kind: D
Fidelity: exact -/
def metaJoint (q : I → PMF Ω) (w : PMF I) : PMF (Ω × I) :=
  w.bind (fun i => (q i).map (fun ω => (ω, i)))

/-- The meta-belief joint pointwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem metaJoint_apply (q : I → PMF Ω) (w : PMF I) (ω : Ω) (i : I) :
    metaJoint q w (ω, i) = w i * q i ω := by
  rw [metaJoint, PMF.bind_apply, tsum_fintype, Finset.sum_eq_single i]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single ω]
    · simp
    · intro ω' hω'
      simp [Prod.ext_iff, hω'.symm]
  · intro j _ hj
    rw [PMF.map_apply]
    simp [Prod.ext_iff, hj.symm]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The `I`-marginal of the meta-belief joint is `w`.
Source: [[armstrong]] I3.2 l. 111
Kind: L
Fidelity: n/a -/
theorem metaJoint_map_snd (q : I → PMF Ω) (w : PMF I) : (metaJoint q w).map Prod.snd = w := by
  rw [metaJoint, PMF.map_bind]
  have : ∀ i, ((q i).map (fun ω => (ω, i))).map Prod.snd = pure i := by
    intro i
    rw [PMF.map_comp]
    exact PMF.map_const (q i) i
  exact (congrArg w.bind (funext this)).trans (PMF.bind_pure w)

/-- The `Ω`-marginal of the meta-belief joint is the mixture `∑ᵢ wᵢ qᵢ = w.bind q`.
Source: [[armstrong]] I3.2 l. 111 ("with `ω`-marginal `ρ_i` … iff `∑_k w_k q_k = ρ_i`")
Kind: L
Fidelity: n/a -/
theorem metaJoint_map_fst (q : I → PMF Ω) (w : PMF I) : (metaJoint q w).map Prod.fst = w.bind q := by
  rw [metaJoint, PMF.map_bind]
  congr 1
  funext i
  rw [PMF.map_comp]
  exact PMF.map_id (q i)

/-- The mass of the meta-belief event `{snd = i}` under any joint with `I`-marginal `w` is `w i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_snd_eq {J : PMF (Ω × I)} {w : PMF I} (hJ : J.map Prod.snd = w) (i : I) :
    Cleanroom.Udt.UdtSupercondition.mass J {x | x.2 = i} = w i := by
  have : ({x | x.2 = i} : Set (Ω × I)) = Prod.snd ⁻¹' {i} := rfl
  rw [this, ← Cleanroom.Udt.UdtSupercondition.mass_map, hJ,
    Cleanroom.Udt.UdtSupercondition.mass_singleton]

/-- **The meta-belief joint endorses its output**: conditional on `{snd = i}` (positive), the
joint is `q i` on the `Ω`-coordinate — superconditioning `P → q i` on "I will believe `q i`".
Source: [[armstrong]] I3.2 l. 111 ("`J(· | k) = q_k` by construction"); [[radical]] Theorem
I3.3(b) l. 108
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem metaJoint_condOn (q : I → PMF Ω) (w : PMF I) {i : I}
    (h : 0 < Cleanroom.Udt.UdtSupercondition.mass (metaJoint q w) {x | x.2 = i}) :
    condOn (metaJoint q w) {x | x.2 = i} h = (q i).map (fun ω => (ω, i)) := by
  have hw : Cleanroom.Udt.UdtSupercondition.mass (metaJoint q w) {x | x.2 = i} = w i :=
    mass_snd_eq (metaJoint_map_snd q w) i
  have hwpos : w i ≠ 0 := by rw [← hw]; exact h.ne'
  apply PMF.ext
  rintro ⟨ω, j⟩
  rw [Cleanroom.Udt.UdtSupercondition.condOn_apply, hw, PMF.map_apply]
  by_cases hj : j = i
  · subst hj
    rw [Set.indicator_of_mem (by simp), metaJoint_apply, tsum_eq_single ω]
    · rw [if_pos rfl, mul_comm (w j), mul_assoc, ENNReal.mul_inv_cancel hwpos (PMF.apply_ne_top w j),
        mul_one]
    · intro ω' hω'
      simp [Prod.ext_iff, hω'.symm]
  · rw [Set.indicator_of_notMem (by simpa using hj)]
    simp [Prod.ext_iff, hj]

/-- **Uniqueness**: any joint with `I`-marginal `w` whose conditionals on the positive
meta-belief events are the announced `q i` is the meta-belief joint.
Source: [[armstrong]] I3.2 l. 111 ("then `J(ω, k) = w_k q_k(ω)` is one"; forced)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem eq_metaJoint {q : I → PMF Ω} {w : PMF I} {J : PMF (Ω × I)} (hJ : J.map Prod.snd = w)
    (hc : ∀ i (h : 0 < Cleanroom.Udt.UdtSupercondition.mass J {x | x.2 = i}),
      condOn J {x | x.2 = i} h = (q i).map (fun ω => (ω, i))) :
    J = metaJoint q w := by
  apply PMF.ext
  rintro ⟨ω, i⟩
  rw [metaJoint_apply]
  have hw := mass_snd_eq hJ i
  by_cases hi : 0 < w i
  · have hpos : 0 < Cleanroom.Udt.UdtSupercondition.mass J {x | x.2 = i} := by rw [hw]; exact hi
    have := DFunLike.congr_fun (hc i hpos) (ω, i)
    rw [Cleanroom.Udt.UdtSupercondition.condOn_apply, hw, Set.indicator_of_mem (by simp),
      PMF.map_apply, tsum_eq_single ω] at this
    · rw [if_pos rfl] at this
      rw [← this, mul_comm (w i), mul_assoc, ENNReal.inv_mul_cancel hi.ne' (PMF.apply_ne_top w i),
        mul_one]
    · intro ω' hω'
      simp [Prod.ext_iff, hω'.symm]
  · have h0 : w i = 0 := le_antisymm (not_lt.1 hi) zero_le
    rw [h0, zero_mul]
    have := Cleanroom.Udt.UdtSupercondition.apply_le_mass J (s := {x | x.2 = i}) (x := (ω, i))
      (by simp)
    rw [hw, h0] at this
    exact le_antisymm this zero_le

/-- **The existence form of the meta-belief representation (Armstrong I3.2 = radical I3.3(b)
read correctly).** A joint on `Ω × I` with `Ω`-marginal `P`, `I`-marginal `w`, and the
announced `q i` as its conditional on each positive meta-belief event `{snd = i}` exists iff
`∑ᵢ wᵢ qᵢ = P` (`w.bind q = P`). Read `J` as the same-ontology conditioning models of all
targets at once: each `q i` is a superconditioning of `P` by "I will believe `q i`", and one
joint serves every target iff the anticipation is a martingale.
Source: [[armstrong]] I3.2 l. 111; [[radical]] Theorem I3.3(b) l. 108 (existence reading —
ATTRIBUTION-UNVETTED that this is what the author meant; the printed ⇐ proof constructs this
joint)
Kind: P
Fidelity: exact (finite `I`, any `Ω`; conditionals as `condOn`, guarded)
Hyps: (a) none -/
theorem exists_metaJoint_iff (q : I → PMF Ω) (w : PMF I) (P : PMF Ω) :
    (∃ J : PMF (Ω × I), J.map Prod.fst = P ∧ J.map Prod.snd = w ∧
        ∀ i (h : 0 < Cleanroom.Udt.UdtSupercondition.mass J {x | x.2 = i}),
          condOn J {x | x.2 = i} h = (q i).map (fun ω => (ω, i))) ↔
      w.bind q = P := by
  constructor
  · rintro ⟨J, hfst, hsnd, hc⟩
    rw [eq_metaJoint hsnd hc, metaJoint_map_fst] at hfst
    exact hfst
  · intro h
    refine ⟨metaJoint q w, ?_, metaJoint_map_snd q w, fun i hi => metaJoint_condOn q w hi⟩
    rw [metaJoint_map_fst, h]

/-- **I3.3(a): total probability over the meta-belief events.** For any joint with
`Ω`-marginal `P` and any event `A ⊆ Ω`, `∑ᵢ J({snd = i} ∩ fst⁻¹ A) = P(A)` (the weighted sum of
the conditionals `J(A | snd = i)` over positive `i` is `P(A)`).
Source: [[radical]] Theorem I3.3(a) l. 107
Kind: L
Fidelity: exact (product form over the meta-belief partition)
Hyps: (a) none -/
theorem sum_mass_snd_inter_eq {J : PMF (Ω × I)} {P : PMF Ω} (hJ : J.map Prod.fst = P)
    (A : Set Ω) :
    ∑ i, Cleanroom.Udt.UdtSupercondition.mass J ({x | x.2 = i} ∩ Prod.fst ⁻¹' A) =
      Cleanroom.Udt.UdtSupercondition.mass P A := by
  rw [← hJ, Cleanroom.Udt.UdtSupercondition.mass_map,
    Cleanroom.Udt.UdtSupercondition.mass_eq_tsum_fiber J (Prod.fst ⁻¹' A) Prod.snd, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext x
  simp [and_comm]

end Existence

/-! ## The refuted fixed-joint reading of I3.3(b) -/

open Cleanroom.Udt.UdtSupercondition in
/-- **Refuted row (radical Theorem I3.3(b), fixed-joint reading).** As printed: "The
representation endorses its own output — `P_t(· | E_{ρ_i}) = ρ_i` for all `i` — iff
`∑ᵢ qᵢ ρᵢ = P_t`", for the fixed joint `P_t(ω, P_{t+1} = ρ) = P_t(ω) K(ρ | ω)`. Reading
formalized: an anticipation structure `as` (the joint fixed), endorsement = `as.Calibrated`,
the martingale condition = `as.Reflective`; the ⇐ direction claims `Reflective → Calibrated`.
It is false: `udt-supercondition`'s `as38` (uniform prior on `Fin 4`, two atoms with
`κ = (1/2, 0, 1/4, 1/4)` and `(0, 1/2, 1/4, 1/4)`) is reflective and not calibrated. The
survivor is Theorem A with introspection (`calibrated_iff_reflective_and_introspective`) and the
existence form `exists_metaJoint_iff` (which the printed ⇐ proof actually constructs).
ATTRIBUTION-UNVETTED which reading the author intended.
Source: [[radical]] Theorem I3.3(b) l. 108; plan §0.4 rule 3
Kind: N+
Fidelity: n/a (refutation of a reading)
Hyps: (a) none -/
theorem i33b_fixed_joint_refuted :
    ¬ ∀ (Ω : Type) (P : PMF Ω) (as : AnticipationStructure P Ω), as.Reflective → as.Calibrated :=
  fun h => reflective_not_calibrated_witness.2
    (h (Fin 4) unif4 as38 reflective_not_calibrated_witness.1)

open Cleanroom.Udt.UdtSupercondition in
/-- **I3.1 finite (cited).** Diaconis–Zabell on a finite carrier: a same-ontology conditioning
model for `P → P'` exists iff `P' ≪ P`. Re-exported from `udt-supercondition` for
corr-wf13-032 and corr-core-005 (the "support caveat" is D–Z necessity, a theorem; the
"bounded density in the infinite case" recollection is `sameOntology_condModel_iff`, correct).
Source: [[radical]] Theorem I3.1 l. 100; [[mm]] D–Z l. 124; `udt-supercondition`
`sameOntology_condModel_iff_of_fintype`
Kind: L
Fidelity: exact (re-export; no new D–Z proof)
Hyps: (a) none -/
theorem dz_finite {Ω : Type} [Fintype Ω] (P P' : PMF Ω) :
    Nonempty (SameOntologyModel P P') ↔ ∀ x, P x = 0 → P' x = 0 :=
  sameOntology_condModel_iff_of_fintype P P'

end

end Cleanroom.Corrigibility.CorrReflectFrames
