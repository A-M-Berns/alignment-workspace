import Cleanroom.Udt.UdtSupercondition.Defs

/-!
# Anticipation structures, calibration, reflection, bridge-calibration

SC §3–§5's anticipation-side objects, point-set: a sub-algebra `Ā ⊆ P̄` is a quotient map
`a : Ω → A` onto a countable type of anticipation atoms; SC's atoms of `(Ā, P|_Ā)` are the
`ā : A` with `0 < (P.map a) ā`, and every definition quantifies over positive atoms exactly as
the source does, by being stated in **multiplicative form** (vacuous at null atoms).

**Vocabulary (dp-cf-2-064):** `Calibrated` is *SC-internal* calibration (Def 3.5): the intended
kernel equals the prior's own conditional. It is not the decision-problems' *external*
calibration (run statistics). Nothing here is called `TotalTrust`, `Coherent` or `Fair`.

* `AnticipationStructure P Q` (Def 3.1), `priorPredictive` (§3.3, literally `(P.map a).bind κ`);
* `Calibrated` (Def 3.5), `Reflective` (Def 3.7), `calibrated_implies_reflective` (Prop 3.8, ⇒);
  the non-converse witness is in `Witnesses.lean`;
* `condKernel`/`condAnticipation`: the prior's own conditionals as a kernel, always calibrated;
* `JointCalibrated` / `CMCalibrated` (Def 4.1): calibration of a conditioning model, which depends
  only on its joint law, hence is preserved by thinning (Remark 4.6);
* `cmCalibrated_of_sameOntology` (Prop 4.2 / Cor 4.3);
* `BridgeCalibrated` (Def 5.1).

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

/-! ### Anticipation structures -/

/-- An **anticipation structure** on `P` targeting `Q` (SC Def 3.1): the anticipation
sub-algebra as a quotient map `a : Ω → A` onto the anticipation atoms, and the intended kernel
`κ : A → PMF Q`. The parameter `P` is phantom in the data; it fixes which prior the
calibration predicates refer to.
Source: [[superconditioning-mismatched-ontologies]] §3.2 Def 3.1 | udt-rep-057
Kind: D
Fidelity: exact: point-set over countable types (SC §0.2, Remark 3.2: atoms are the bearers)
Hyps: n/a -/
structure AnticipationStructure {Ω : Type} (P : PMF Ω) (Q : Type) where
  /-- The anticipation atoms. -/
  A : Type
  /-- Countability (SC §0.10). -/
  [countable : Countable A]
  /-- The quotient map onto the anticipation atoms (the sub-algebra `Ā ⊆ P̄`). -/
  a : Ω → A
  /-- The intended kernel: the future belief each atom is meant to represent. -/
  κ : A → PMF Q

attribute [instance] AnticipationStructure.countable

variable {Ω Ω' : Type} {P : PMF Ω}

/-- The **prior-predictive** measure `Q₀(q̄) = ∑_ā κ_ā(q̄) · P(ā)` (SC §3.3), literally
`(P.map a).bind κ`.
Source: [[superconditioning-mismatched-ontologies]] §3.3
Kind: D
Fidelity: exact (`PMF.bind_apply` is the displayed sum)
Hyps: n/a -/
noncomputable def AnticipationStructure.priorPredictive (as : AnticipationStructure P Ω') :
    PMF Ω' :=
  (P.map as.a).bind as.κ

/-- The prior-predictive as SC displays it.
Source: [[superconditioning-mismatched-ontologies]] §3.3
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem AnticipationStructure.priorPredictive_apply (as : AnticipationStructure P Ω') (q : Ω') :
    as.priorPredictive q = ∑' ā, (P.map as.a) ā * as.κ ā q :=
  PMF.bind_apply _ _ _

/-- The prior-predictive as `P.bind (κ ∘ a)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem AnticipationStructure.priorPredictive_eq_bind (as : AnticipationStructure P Ω') :
    as.priorPredictive = P.bind (as.κ ∘ as.a) :=
  PMF.bind_map _ _ _

/-- The atom mass `(P.map a) ā` is the mass of the atom as an event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem AnticipationStructure.map_a_apply (as : AnticipationStructure P Ω') (ā : as.A) :
    (P.map as.a) ā = mass P (as.a ⁻¹' {ā}) :=
  map_apply_eq_mass _ _ _

/-! ### Same-ontology calibration and reflection -/

/-- **SC-internal calibration** (Def 3.5, same ontology): on every atom of positive mass, the
prior's own conditional `P(· | ā)` equals the intended kernel `κ_ā`; in multiplicative form
`P(ā ∩ {x}) = κ_ā(x) · P(ā)`, which is vacuous at null atoms exactly as SC's "for atoms with
`P(ā) > 0`". This is *not* the decision-problems' external calibration (dp-cf-2-064).
Source: [[superconditioning-mismatched-ontologies]] §3.4 Def 3.5 | udt-rep-057
Kind: D
Fidelity: exact (multiplicative form; the division form is `Calibrated.condOn_eq`)
Scope: same ontology `Q = Ω`; SC-internal calibration
Hyps: n/a -/
def AnticipationStructure.Calibrated (as : AnticipationStructure P Ω) : Prop :=
  ∀ ā x, mass P (as.a ⁻¹' {ā} ∩ {x}) = as.κ ā x * (P.map as.a) ā

/-- The division form of calibration: on a positive atom, `P(· | ā) = κ_ā`.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Def 3.5 (Cal)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem AnticipationStructure.Calibrated.condOn_eq {as : AnticipationStructure P Ω}
    (h : as.Calibrated) (ā : as.A) (hā : 0 < mass P (as.a ⁻¹' {ā})) :
    condOn P (as.a ⁻¹' {ā}) hā = as.κ ā :=
  PMF.ext fun x => by
    rw [condOn_apply, ← mass_inter_singleton, h ā x, as.map_a_apply, mul_assoc,
      ENNReal.mul_inv_cancel hā.ne' (mass_ne_top _ _), mul_one]

/-- **Reflection** (Def 3.7, same ontology): the prior-predictive equals the prior.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Def 3.7 | udt-rep-057
Kind: D
Fidelity: exact ("equivalently `Q₀ = P`")
Scope: same ontology `Q = Ω`
Hyps: n/a -/
def AnticipationStructure.Reflective (as : AnticipationStructure P Ω) : Prop :=
  as.priorPredictive = P

/-- **Calibration implies reflection** (SC Prop 3.8, first half): total probability with `κ_ā`
substituted for `P(· | ā)`. The converse fails: `reflective_not_calibrated_witness`.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Prop 3.8 | udt-rep-057
Kind: P
Fidelity: exact: point-set over countable types (SC §0.2)
Scope: same ontology; `Calibrated` is SC-internal calibration (Def 3.5), not the
decision-problems' external one
Hyps: (a) all -/
theorem calibrated_implies_reflective {as : AnticipationStructure P Ω} (h : as.Calibrated) :
    as.Reflective :=
  PMF.ext fun x => by
    rw [AnticipationStructure.priorPredictive_apply]
    have e : ∀ ā, (P.map as.a) ā * as.κ ā x = (as.a ⁻¹' {ā}).indicator P x := fun ā => by
      rw [mul_comm, ← h ā x, mass_inter_singleton]
    rw [tsum_congr e, tsum_eq_single (as.a x)]
    · exact indicator_of_mem (show x ∈ as.a ⁻¹' {as.a x} from rfl) P
    · intro ā hā
      exact indicator_of_notMem (s := as.a ⁻¹' {ā}) (a := x)
        (fun hm => hā (mem_singleton_iff.1 hm).symm) P

/-! ### The prior's own conditionals as a kernel -/

/-- The kernel of the prior's own conditionals on the atoms of `a`: `P(· | ā)` on positive atoms
and `P` itself on null atoms (a choice, irrelevant to every multiplicative-form predicate).
Source: [[superconditioning-mismatched-ontologies]] §3.4 (the calibrated kernel), §12.1
Kind: D
Fidelity: exact on positive atoms
Hyps: n/a -/
noncomputable def condKernel (P : PMF Ω) {A : Type} (a : Ω → A) (ā : A) : PMF Ω :=
  if h : 0 < mass P (a ⁻¹' {ā}) then condOn P (a ⁻¹' {ā}) h else P

/-- The anticipation structure whose kernel is the prior's own conditionals.
Source: [[superconditioning-mismatched-ontologies]] §12.1 (calibration "by construction")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def condAnticipation (P : PMF Ω) {A : Type} [Countable A] (a : Ω → A) :
    AnticipationStructure P Ω :=
  { A := A, a := a, κ := condKernel P a }

/-- The conditional kernel on a positive atom is the conditional.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condKernel_of_pos (P : PMF Ω) {A : Type} (a : Ω → A) (ā : A)
    (h : 0 < mass P (a ⁻¹' {ā})) : condKernel P a ā = condOn P (a ⁻¹' {ā}) h := by
  rw [condKernel, dif_pos h]

/-- The conditional kernel's mass function, in the junk-free indicator form (both branches).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condKernel_apply_mul (P : PMF Ω) {A : Type} (a : Ω → A) (ā : A) (x : Ω) :
    condKernel P a ā x * mass P (a ⁻¹' {ā}) = (a ⁻¹' {ā}).indicator P x := by
  rw [condKernel]
  split_ifs with h
  · rw [condOn_apply, mul_assoc, ENNReal.inv_mul_cancel h.ne' (mass_ne_top _ _), mul_one]
  · have h0 : mass P (a ⁻¹' {ā}) = 0 := le_antisymm (not_lt.1 h) zero_le
    rw [h0, mul_zero]
    by_cases hx : x ∈ a ⁻¹' {ā}
    · rw [indicator_of_mem hx]
      exact (le_antisymm ((apply_le_mass P hx).trans h0.le) zero_le).symm
    · rw [indicator_of_notMem hx]

/-- The prior's own conditionals are a calibrated anticipation structure.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Def 3.5 (the paradigm instance), §12.1
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem calibrated_condAnticipation (P : PMF Ω) {A : Type} [Countable A] (a : Ω → A) :
    (condAnticipation P a).Calibrated := fun ā x => by
  show mass P (a ⁻¹' {ā} ∩ {x}) = condKernel P a ā x * (P.map a) ā
  rw [map_apply_eq_mass, condKernel_apply_mul, mass_inter_singleton]
  rfl

/-- The prior's own conditionals are reflective.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Obs 3.4 (total probability)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem reflective_condAnticipation (P : PMF Ω) {A : Type} [Countable A] (a : Ω → A) :
    (condAnticipation P a).Reflective :=
  calibrated_implies_reflective (calibrated_condAnticipation P a)

/-! ### Calibrated conditioning models -/

/-- Calibration of a joint law `J` on `Ω × Ω′` w.r.t. an anticipation structure: on each atom
`ā`, the conditional `Ω′`-marginal is `κ_ā` (multiplicative form:
`J(ā × {q}) = κ_ā(q) · J(ā × Ω′)`).
Source: [[superconditioning-mismatched-ontologies]] §4.2 Def 4.1 (the joint of `(p(Ā), q(Q̄))`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def JointCalibrated (J : PMF (Ω × Ω')) (as : AnticipationStructure P Ω') : Prop :=
  ∀ ā q, mass J (Prod.fst ⁻¹' (as.a ⁻¹' {ā}) ∩ Prod.snd ⁻¹' {q}) =
    as.κ ā q * mass J (Prod.fst ⁻¹' (as.a ⁻¹' {ā}))

/-- **Calibrated conditioning model** (SC Def 4.1, (CM-Cal)): in the enlarged space, conditional
on `p⁻¹ ā`, the distribution of `p′` is `κ_ā`; multiplicative form
`μ(p⁻¹ ā ∩ p′⁻¹ q) = κ_ā(q) · μ(p⁻¹ ā)`, vacuous on null atoms exactly as the source.
Source: [[superconditioning-mismatched-ontologies]] §4.2 Def 4.1 | udt-rep-058
Kind: D
Fidelity: exact (multiplicative form)
Scope: SC-internal calibration
Hyps: n/a -/
def CMCalibrated {Q : PMF Ω'} (m : CondModel P Q) (as : AnticipationStructure P Ω') : Prop :=
  ∀ ā q, mass m.μ (m.p ⁻¹' (as.a ⁻¹' {ā}) ∩ m.p' ⁻¹' {q}) =
    as.κ ā q * mass m.μ (m.p ⁻¹' (as.a ⁻¹' {ā}))

/-- Calibration of a model depends only on its joint law.
Source: [[superconditioning-mismatched-ontologies]] §4.4 Remark 4.4
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem cmCalibrated_iff_jointCalibrated {Q : PMF Ω'} (m : CondModel P Q)
    (as : AnticipationStructure P Ω') : CMCalibrated m as ↔ JointCalibrated m.jointLaw as := by
  simp only [CMCalibrated, JointCalibrated, CondModel.mass_jointLaw_prod, CondModel.mass_jointLaw_fst]

/-- The joint law of `P` with the kernel `κ ∘ a` is calibrated.
Source: [[superconditioning-mismatched-ontologies]] §4.4 (proof of Thm 4.5, "Calibration")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem jointCalibrated_couple (as : AnticipationStructure P Ω') :
    JointCalibrated (couple P (as.κ ∘ as.a)) as := fun ā q => by
  rw [mass_couple_prod, ← mass_singleton, ← mass_map, couple_map_fst, mass_singleton,
    mass_eq_tsum, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ as.a ⁻¹' {ā}
  · rw [indicator_of_mem hx, indicator_of_mem hx, mass_singleton, Function.comp_apply,
      mem_singleton_iff.1 hx, mul_comm]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- A calibrated joint law with first marginal `P` has second marginal the prior-predictive.
Source: [[superconditioning-mismatched-ontologies]] §4.4 Remark 4.6 (implicit: the unconditional
`Q̄`-marginal of a calibrated joint is `Q₀`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem JointCalibrated.map_snd {J : PMF (Ω × Ω')} {as : AnticipationStructure P Ω'}
    (hJ : JointCalibrated J as) (hfst : J.map Prod.fst = P) :
    J.map Prod.snd = as.priorPredictive :=
  PMF.ext fun q => by
    rw [map_apply_eq_mass, AnticipationStructure.priorPredictive_apply,
      mass_eq_tsum_fiber J _ (as.a ∘ Prod.fst)]
    refine tsum_congr fun ā => ?_
    rw [preimage_comp, inter_comm, hJ ā q, ← mass_map, hfst, map_apply_eq_mass, mul_comm]

/-- A calibrated conditioning model's unconditional `Ω′`-marginal is the prior-predictive.
Source: [[superconditioning-mismatched-ontologies]] §4.4 Remark 4.6
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem CMCalibrated.map_p' {Q : PMF Ω'} {m : CondModel P Q} {as : AnticipationStructure P Ω'}
    (h : CMCalibrated m as) : m.μ.map m.p' = as.priorPredictive := by
  have := ((cmCalibrated_iff_jointCalibrated m as).1 h).map_snd m.jointLaw_map_fst
  rwa [CondModel.jointLaw, PMF.map_comp] at this

/-- **Calibration is thinning-closed** (SC Remark 4.6, the mechanism of Thm 4.5): thinning
preserves the joint law, hence calibration.
Source: [[superconditioning-mismatched-ontologies]] §4.4 Remark 4.6 | mandate T20
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem CMCalibrated.thin {Q : PMF Ω'} {m : CondModel P Q} {as : AnticipationStructure P Ω'}
    (h : CMCalibrated m as) (w : m.L → ℝ≥0∞) (hw : ∀ l, w l ≤ 1)
    (hpos : 0 < ∑' l, m.ev.indicator (fun l => w l * m.μ l) l) (P'' : PMF Ω')
    (hP'' : ∀ x', P'' x' = thinPostFun m.μ w m.ev m.p' x') :
    CMCalibrated (m.thin w hw hpos P'' hP'') as := by
  rw [cmCalibrated_iff_jointCalibrated, CondModel.jointLaw_thin]
  exact (cmCalibrated_iff_jointCalibrated m as).1 h

/-- **Same-ontology calibration is automatic** (SC Prop 4.2 / Cor 4.3): if `p′ = p` and the
anticipation is calibrated, every conditioning model is calibrated. Three lines (the mandate's
pre-label `L`; the round-0 docstring said `P`).
Source: [[superconditioning-mismatched-ontologies]] §4.3 Prop 4.2, Cor 4.3 | udt-rep-058
Kind: L
Fidelity: exact
Scope: same ontology; SC-internal calibration
Hyps: (a) all -/
theorem cmCalibrated_of_sameOntology {Q : PMF Ω} (m : CondModel P Q) (hpp : m.p' = m.p)
    (as : AnticipationStructure P Ω) (h : as.Calibrated) : CMCalibrated m as := fun ā x => by
  have e1 : mass m.μ (m.p ⁻¹' (as.a ⁻¹' {ā}) ∩ m.p' ⁻¹' {x}) = mass P (as.a ⁻¹' {ā} ∩ {x}) := by
    rw [hpp, ← preimage_inter, ← mass_map, m.hp]
  have e2 : mass m.μ (m.p ⁻¹' (as.a ⁻¹' {ā})) = mass P (as.a ⁻¹' {ā}) := by
    rw [← mass_map, m.hp]
  rw [e1, e2, h ā x, as.map_a_apply]

/-- Prop 4.2 for same-ontology models.
Source: [[superconditioning-mismatched-ontologies]] §4.3 Cor 4.3
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem SameOntologyModel.cmCalibrated_toCondModel {Q : PMF Ω} (m : SameOntologyModel P Q)
    (as : AnticipationStructure P Ω) (h : as.Calibrated) : CMCalibrated m.toCondModel as :=
  cmCalibrated_of_sameOntology m.toCondModel rfl as h

/-! ### Bridge-calibration -/

/-- **`Ĉ`-calibration** (SC Def 5.1): for each atom `ā` and shared proposition `y`, the
bridge-conditional `P(c⁻¹ y | ā)` equals the kernel's opinion `κ_ā(c′⁻¹ y)`; multiplicative form
`P(ā ∩ c⁻¹ y) = κ_ā(c′⁻¹ y) · P(ā)`.
Source: [[superconditioning-mismatched-ontologies]] §5.2 Def 5.1 | udt-rep-061
Kind: D
Fidelity: exact (multiplicative form)
Scope: SC-internal calibration on the shared language
Hyps: n/a -/
def BridgeCalibrated (as : AnticipationStructure P Ω') (ci : CommonInfo Ω Ω') : Prop :=
  ∀ ā y, mass P (as.a ⁻¹' {ā} ∩ ci.c ⁻¹' {y}) = mass (as.κ ā) (ci.c' ⁻¹' {y}) * (P.map as.a) ā

/-- The division form: on a positive atom the bridge-conditional `ν_ā` is `κ^C_ā`.
Source: [[superconditioning-mismatched-ontologies]] §5.2 Def 5.1
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem BridgeCalibrated.condOn_eq {as : AnticipationStructure P Ω'} {ci : CommonInfo Ω Ω'}
    (h : BridgeCalibrated as ci) (ā : as.A) (hā : 0 < mass P (as.a ⁻¹' {ā})) (y : ci.C) :
    mass (condOn P (as.a ⁻¹' {ā}) hā) (ci.c ⁻¹' {y}) = mass (as.κ ā) (ci.c' ⁻¹' {y}) := by
  rw [mass_condOn, inter_comm, h ā y, as.map_a_apply, mul_assoc,
    ENNReal.mul_inv_cancel hā.ne' (mass_ne_top _ _), mul_one]

end Cleanroom.Udt.UdtSupercondition
