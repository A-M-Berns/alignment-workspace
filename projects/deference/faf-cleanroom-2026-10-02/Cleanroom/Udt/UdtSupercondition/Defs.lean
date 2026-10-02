import Cleanroom.Udt.UdtSupercondition.Thinning

/-!
# Conditioning models, common information and compatibility: the definitions of record

The objects of SC Part I (Defs 1.1, 2.1, 2.3 and Remark 2.5's same-ontology case), point-set
over countable types (SC §0.2, §0.10). Dependents (`corr-reflect-frames`, `dp-firstperson-sc`,
`udt-endorse-policy`) import these definitions; the names are stable from the first commit.

* `CondModel P P′` (SC Def 1.1): a carrier `L`, `μ : PMF L`, projections `p : L → Ω`,
  `p′ : L → Ω′`, evidence `ev` of positive mass, with `μ.map p = P` and
  `(condOn μ ev _).map p′ = P′`. `HasCondModel P P′ := Nonempty (CondModel P P′)`.
  **Vocabulary (dp-cf-2-064):** SC's "prior" is the *earlier belief* `P` of a conditioning
  model, not v2's one `s°` per problem.
* `CommonInfo Ω Ω′` (SC Def 2.1): a shared type `C` with translations `c : Ω → C`,
  `c′ : Ω′ → C`; `ci.C₁ P = P.map c`, `ci.C₂ P′ = P′.map c′` (SC's `C`, `C′`). The translations
  need not be surjective: a σ-algebra homomorphism may send a nonempty event to `⊥`
  (SC §0.2), which is what the quotient obstruction `thm24_sufficiency_refuted` exploits.
* `Compatible m ci` (SC Def 2.3): `c ∘ p = c′ ∘ p′` as functions on `L` — SC's exact reading
  ("as random variables `L̂ → Ĉ`", i.e. equal σ-algebra homomorphisms, i.e. equal point
  functions). `CompatibleAE` is the μ-a.e. variant, a remark.
* `SameOntologyModel P P′` (SC Remark 2.5): one projection; `sameOntology_iff_compatible_id`
  identifies it with the `Compatible` case of `idCI`.
* `CondModel.jointLaw m`: the joint pushforward `μ.map (p, p′)`; calibration of a model
  (`Calibration.lean`) depends only on it, which is why thinning preserves calibration
  (SC Remark 4.6).
* `CondModel.thin`, `SameOntologyModel.thin`: the thinned model (mandate T20); `productModel`
  (SC Thm 1.2's model) and `SameOntologyModel.trivial`.

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

/-! ### Conditioning models -/

/-- A **conditioning model** for the belief change `P ⟶ P′` (SC Def 1.1): an enlarged countable
space `(L, μ)` projecting onto `Ω` (probability-preservingly) and onto `Ω′` after conditioning on
the evidence event `ev`. "Prior" here is SC's earlier belief `P`, not v2's `s°` (dp-cf-2-064).
Source: [[superconditioning-mismatched-ontologies]] §1.2 Def 1.1 | udt-rep-054 | bli-soto-b-054
Kind: D
Fidelity: exact: point-set over countable types (SC §0.2); `L : Type` (universe 0)
Scope: countable discrete (SC §0.10)
Hyps: n/a -/
structure CondModel {Ω Ω' : Type} (P : PMF Ω) (P' : PMF Ω') where
  /-- The enlarged carrier. -/
  L : Type
  /-- Countability (SC §0.10). No proof in the package uses it. -/
  [countable : Countable L]
  /-- The measure on the enlarged carrier. -/
  μ : PMF L
  /-- The projection to the earlier ontology. -/
  p : L → Ω
  /-- The projection to the later ontology. -/
  p' : L → Ω'
  /-- The evidence event. -/
  ev : Set L
  /-- `p` is probability-preserving: `p_* μ = P`. -/
  hp : μ.map p = P
  /-- The evidence has positive mass. -/
  hev : 0 < mass μ ev
  /-- `p′` is probability-preserving from `μ(· | ev)` to `P′`. -/
  hp' : (condOn μ ev hev).map p' = P'

attribute [instance] CondModel.countable

/-- A conditioning model exists for the pair `(P, P′)`.
Source: [[superconditioning-mismatched-ontologies]] §1.3 Thm 1.2 (the predicate)
Kind: D
Fidelity: exact
Hyps: n/a -/
def HasCondModel {Ω Ω' : Type} (P : PMF Ω) (P' : PMF Ω') : Prop := Nonempty (CondModel P P')

variable {Ω Ω' : Type} {P : PMF Ω} {P' : PMF Ω'}

/-- The posterior measure `L′ = μ(· | ev)` of a conditioning model (SC Def 1.1).
Source: [[superconditioning-mismatched-ontologies]] §1.2 Def 1.1 (`L′`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def CondModel.post (m : CondModel P P') : PMF m.L := condOn m.μ m.ev m.hev

/-- The joint pushforward `μ.map (p, p′)` of a conditioning model on `Ω × Ω′`.
Source: none: infrastructure (SC Remark 4.4's "joint of `(p(Ā), q(Q̄))` in `L̄`")
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def CondModel.jointLaw (m : CondModel P P') : PMF (Ω × Ω') :=
  m.μ.map fun l => (m.p l, m.p' l)

/-- The joint law's first marginal is `P`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem CondModel.jointLaw_map_fst (m : CondModel P P') : m.jointLaw.map Prod.fst = P := by
  rw [CondModel.jointLaw, PMF.map_comp]; exact m.hp

/-- Rectangle masses under the joint law are joint preimage masses under `μ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem CondModel.mass_jointLaw_prod (m : CondModel P P') (U : Set Ω) (V : Set Ω') :
    mass m.jointLaw (Prod.fst ⁻¹' U ∩ Prod.snd ⁻¹' V) = mass m.μ (m.p ⁻¹' U ∩ m.p' ⁻¹' V) := by
  rw [CondModel.jointLaw, mass_map]; rfl

/-- Fibre masses of `p` under `μ` are masses under the joint law.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem CondModel.mass_jointLaw_fst (m : CondModel P P') (U : Set Ω) :
    mass m.jointLaw (Prod.fst ⁻¹' U) = mass m.μ (m.p ⁻¹' U) := by
  rw [CondModel.jointLaw, mass_map]; rfl

/-! ### Common information and compatibility -/

/-- A **common-information structure** (SC Def 2.1): the shared language `C` with its
interpretations `c` in `Ω` and `c′` in `Ω′`. Neither translation need be surjective (SC §0.2).
Source: [[superconditioning-mismatched-ontologies]] §2.2 Def 2.1 | udt-rep-055
Kind: D
Fidelity: exact: point-set over countable types (SC §0.2)
Hyps: n/a -/
structure CommonInfo (Ω Ω' : Type) where
  /-- The shared language. -/
  C : Type
  /-- Countability (SC §0.10). -/
  [countable : Countable C]
  /-- Interpretation of `C`-events in the earlier ontology. -/
  c : Ω → C
  /-- Interpretation of `C`-events in the later ontology. -/
  c' : Ω' → C

attribute [instance] CommonInfo.countable

/-- SC's `C = c_* P`, the earlier belief on the shared language.
Source: [[superconditioning-mismatched-ontologies]] §2.2 Def 2.1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def CommonInfo.C₁ (ci : CommonInfo Ω Ω') (P : PMF Ω) : PMF ci.C := P.map ci.c

/-- SC's `C′ = c′_* P′`, the later belief on the shared language.
Source: [[superconditioning-mismatched-ontologies]] §2.2 Def 2.1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def CommonInfo.C₂ (ci : CommonInfo Ω Ω') (P' : PMF Ω') : PMF ci.C := P'.map ci.c'

/-- `C₁ y` is the mass of the `c`-fibre over `y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem CommonInfo.C₁_apply (ci : CommonInfo Ω Ω') (P : PMF Ω) (y : ci.C) :
    ci.C₁ P y = mass P (ci.c ⁻¹' {y}) := map_apply_eq_mass _ _ _

/-- `C₂ y` is the mass of the `c′`-fibre over `y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem CommonInfo.C₂_apply (ci : CommonInfo Ω Ω') (P' : PMF Ω') (y : ci.C) :
    ci.C₂ P' y = mass P' (ci.c' ⁻¹' {y}) := map_apply_eq_mass _ _ _

/-- **`Ĉ`-compatibility** (SC Def 2.3, (Compat)): `c ∘ p = c′ ∘ p′` as functions on `L` — SC's
exact reading (equality as random variables `L̂ → Ĉ`, i.e. as σ-algebra homomorphisms, i.e. as
point functions in the countable discrete case). The μ-a.e. variant is `CompatibleAE`.
Source: [[superconditioning-mismatched-ontologies]] §2.3 Def 2.3 | udt-rep-055
Kind: D
Fidelity: exact (function equality; the source says "as random variables")
Hyps: n/a -/
def Compatible (m : CondModel P P') (ci : CommonInfo Ω Ω') : Prop :=
  ci.c ∘ m.p = ci.c' ∘ m.p'

/-- Almost-everywhere compatibility: the two paths to `C` agree on every point of positive
`μ`-mass. A remark in SC's terms (SC §0.3 "equality almost everywhere").
Source: [[superconditioning-mismatched-ontologies]] §0.3, §2.3 (a.e. reading)
Kind: D
Fidelity: variant: a.e. in place of exact equality
Hyps: n/a -/
def CompatibleAE (m : CondModel P P') (ci : CommonInfo Ω Ω') : Prop :=
  ∀ l, m.μ l ≠ 0 → ci.c (m.p l) = ci.c' (m.p' l)

/-- Exact compatibility implies a.e. compatibility.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Compatible.compatibleAE {m : CondModel P P'} {ci : CommonInfo Ω Ω'} (h : Compatible m ci) :
    CompatibleAE m ci := fun l _ => congrFun h l

/-- The common random variable `c_L = c ∘ p = c′ ∘ p′` of a compatible model (SC §2.3).
Source: [[superconditioning-mismatched-ontologies]] §2.3
Kind: D
Fidelity: exact
Hyps: n/a -/
def CondModel.cL (m : CondModel P P') (ci : CommonInfo Ω Ω') : m.L → ci.C := ci.c ∘ m.p

/-- The identity common-information structure `C = Ω`, `c = c′ = id` (SC Remark 2.2, 2.5).
Source: [[superconditioning-mismatched-ontologies]] §2.2 Remark 2.2, §2.6 Remark 2.5
Kind: D
Fidelity: exact
Hyps: n/a -/
def idCI (Ω : Type) [Countable Ω] : CommonInfo Ω Ω := { C := Ω, c := id, c' := id }

/-- The trivial common-information structure `C = Unit` (SC Remark 2.2, 2.6).
Source: [[superconditioning-mismatched-ontologies]] §2.2 Remark 2.2, §2.6 Remark 2.6
Kind: D
Fidelity: exact (`{⊥, ⊤}` is the σ-algebra of the one-point type)
Hyps: n/a -/
def trivialCI (Ω Ω' : Type) : CommonInfo Ω Ω' := { C := Unit, c := fun _ => (), c' := fun _ => () }

/-- Compatibility with `idCI` is `p = p′`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem compatible_idCI_iff [Countable Ω] {P P' : PMF Ω} (m : CondModel P P') :
    Compatible m (idCI Ω) ↔ m.p = m.p' := by
  simp only [Compatible, idCI, Function.id_comp]

/-- Every model is compatible with the trivial common information.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.6
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem compatible_trivialCI (m : CondModel P P') : Compatible m (trivialCI Ω Ω') := rfl

/-! ### Same-ontology models -/

/-- A **same-ontology conditioning model** (SC Remark 2.5): one projection `p`, so that
`p_* μ = P` and `p_* μ(· | ev) = P′` on the same `Ω`. It is the `Compatible` case of `idCI`
(`sameOntology_iff_compatible_id`).
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5 | udt-rep-056 |
corr-wf13-032 (I3.1)
Kind: D
Fidelity: exact
Hyps: n/a -/
structure SameOntologyModel {Ω : Type} (P P' : PMF Ω) where
  /-- The enlarged carrier. -/
  L : Type
  /-- Countability (SC §0.10). -/
  [countable : Countable L]
  /-- The measure on the enlarged carrier. -/
  μ : PMF L
  /-- The one projection. -/
  p : L → Ω
  /-- The evidence event. -/
  ev : Set L
  /-- `p_* μ = P`. -/
  hp : μ.map p = P
  /-- The evidence has positive mass. -/
  hev : 0 < mass μ ev
  /-- `p_* μ(· | ev) = P′`. -/
  hp' : (condOn μ ev hev).map p = P'

attribute [instance] SameOntologyModel.countable

variable {Q : PMF Ω}

/-- A same-ontology model as a conditioning model with `p′ = p`.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5
Kind: D
Fidelity: exact
Hyps: n/a -/
def SameOntologyModel.toCondModel (m : SameOntologyModel P Q) : CondModel P Q :=
  { L := m.L, μ := m.μ, p := m.p, p' := m.p, ev := m.ev, hp := m.hp, hev := m.hev, hp' := m.hp' }

/-- `toCondModel` is compatible with `idCI`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem SameOntologyModel.toCondModel_compatible [Countable Ω] (m : SameOntologyModel P Q) :
    Compatible m.toCondModel (idCI Ω) := rfl

/-- A conditioning model compatible with `idCI` (so `p = p′`) is a same-ontology model.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5
Kind: D
Fidelity: exact
Hyps: n/a -/
def SameOntologyModel.ofCompatible [Countable Ω] (m : CondModel P Q) (h : Compatible m (idCI Ω)) :
    SameOntologyModel P Q :=
  { L := m.L, μ := m.μ, p := m.p, ev := m.ev, hp := m.hp, hev := m.hev,
    hp' := by rw [(compatible_idCI_iff m).1 h]; exact m.hp' }

/-- A same-ontology model exists iff a conditioning model compatible with `idCI` exists
(SC Remark 2.5, "with `P′ = P`, `c = c′ = id`").
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5 | udt-rep-056
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem sameOntology_iff_compatible_id [Countable Ω] :
    Nonempty (SameOntologyModel P Q) ↔ ∃ m : CondModel P Q, Compatible m (idCI Ω) :=
  ⟨fun ⟨m⟩ => ⟨m.toCondModel, m.toCondModel_compatible⟩,
    fun ⟨m, h⟩ => ⟨SameOntologyModel.ofCompatible m h⟩⟩

/-- The posterior of a same-ontology model.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def SameOntologyModel.post (m : SameOntologyModel P Q) : PMF m.L :=
  condOn m.μ m.ev m.hev

/-! ### The models every existence proof starts from -/

/-- SC Thm 1.2's model: the product coupling `P ⊗ P′` on `Ω × Ω′` with evidence `⊤`.
Source: [[superconditioning-mismatched-ontologies]] §1.3 Thm 1.2 (proof)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def productModel [Countable Ω] [Countable Ω'] (P : PMF Ω) (P' : PMF Ω') :
    CondModel P P' where
  L := Ω × Ω'
  μ := couple P fun _ => P'
  p := Prod.fst
  p' := Prod.snd
  ev := univ
  hp := couple_map_fst _ _
  hev := by rw [mass_univ]; exact zero_lt_one
  hp' := by rw [condOn_univ, couple_map_snd, PMF.bind_const]

/-- The trivial same-ontology model: `L = Ω`, `μ = P`, `p = id`, `ev = ⊤`; its posterior is `P`.
Source: [[superconditioning-mismatched-ontologies]] §1.3 (the degenerate bridge), mandate T20
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def SameOntologyModel.trivial [Countable Ω] (P : PMF Ω) : SameOntologyModel P P where
  L := Ω
  μ := P
  p := id
  ev := univ
  hp := PMF.map_id P
  hev := by rw [mass_univ]; exact zero_lt_one
  hp' := by rw [condOn_univ, PMF.map_id]

/-! ### Thinned models -/

/-- The evidence of a thinned model: the old evidence, on the `true` layer.
Source: mandate T20 ("`ev × {true}`")
Kind: D
Fidelity: n/a
Hyps: n/a -/
def thinEv {L : Type} (ev : Set L) : Set (L × Bool) := Prod.fst ⁻¹' ev ∩ evTrue L

/-- The evidence layer of the thinned model, as a preimage-intersection (set identity).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem preimage_inter_thinEv {L : Type} {Z : Type} (q : L → Z) (ev : Set L) (S : Set Z) :
    (q ∘ Prod.fst) ⁻¹' S ∩ thinEv ev = Prod.fst ⁻¹' (q ⁻¹' S ∩ ev) ∩ evTrue L := by
  ext l
  simp only [thinEv, mem_inter_iff, mem_preimage, Function.comp, evTrue, mem_setOf_eq]
  tauto

/-- The posterior mass function of a thinning of `m` by `w` (the formula the thinned model's
posterior satisfies): `x ↦ ∑_{p⁻¹ x ∩ ev} w · μ / ∑_{ev} w · μ`.
Source: mandate T20
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def thinPostFun {L : Type} (μ : PMF L) (w : L → ℝ≥0∞) (ev : Set L) {Z : Type}
    (q : L → Z) (x : Z) : ℝ≥0∞ :=
  (∑' l, (q ⁻¹' {x} ∩ ev).indicator (fun l => w l * μ l) l) *
    (∑' l, ev.indicator (fun l => w l * μ l) l)⁻¹

/-- **The thinned conditioning model.** Thin `m.μ` by `w`, keep both projections through `fst`,
and take the old evidence on the `true` layer. Its posterior is any `P″` satisfying the
`thinPostFun` formula (supplied as a proof, so no transport along an equality is ever needed).
Source: [[superconditioning-mismatched-ontologies]] §4.4 Remark 4.6 (the mechanism), mandate T20
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def CondModel.thin (m : CondModel P P') (w : m.L → ℝ≥0∞) (hw : ∀ l, w l ≤ 1)
    (hpos : 0 < ∑' l, m.ev.indicator (fun l => w l * m.μ l) l) (P'' : PMF Ω')
    (hP'' : ∀ x', P'' x' = thinPostFun m.μ w m.ev m.p' x') : CondModel P P'' where
  L := m.L × Bool
  μ := Cleanroom.Udt.UdtSupercondition.thin m.μ w hw
  p := m.p ∘ Prod.fst
  p' := m.p' ∘ Prod.fst
  ev := thinEv m.ev
  hp := by rw [← PMF.map_comp, thin_map_fst, m.hp]
  hev := by rw [thinEv, mass_thin_inter_evTrue]; exact hpos
  hp' := PMF.ext fun x' => by
    rw [hP'', map_apply_eq_mass, mass_condOn, preimage_inter_thinEv, thinEv,
      mass_thin_inter_evTrue, mass_thin_inter_evTrue, thinPostFun]

/-- The thinned model has the same joint law as the original (SC Remark 4.6: thinning changes
the evidence, not the unconditional joint of `(p, p′)`).
Source: [[superconditioning-mismatched-ontologies]] §4.4 Remark 4.6
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem CondModel.jointLaw_thin (m : CondModel P P') (w : m.L → ℝ≥0∞) (hw : ∀ l, w l ≤ 1)
    (hpos : 0 < ∑' l, m.ev.indicator (fun l => w l * m.μ l) l) (P'' : PMF Ω')
    (hP'' : ∀ x', P'' x' = thinPostFun m.μ w m.ev m.p' x') :
    (m.thin w hw hpos P'' hP'').jointLaw = m.jointLaw := by
  show (Cleanroom.Udt.UdtSupercondition.thin m.μ w hw).map
    ((fun l => (m.p l, m.p' l)) ∘ Prod.fst) = _
  rw [← PMF.map_comp, thin_map_fst]; rfl

/-- **The thinned same-ontology model.**
Source: mandate T20
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def SameOntologyModel.thin (m : SameOntologyModel P Q) (w : m.L → ℝ≥0∞)
    (hw : ∀ l, w l ≤ 1) (hpos : 0 < ∑' l, m.ev.indicator (fun l => w l * m.μ l) l) (Q' : PMF Ω)
    (hQ' : ∀ x, Q' x = thinPostFun m.μ w m.ev m.p x) : SameOntologyModel P Q' where
  L := m.L × Bool
  μ := Cleanroom.Udt.UdtSupercondition.thin m.μ w hw
  p := m.p ∘ Prod.fst
  ev := thinEv m.ev
  hp := by rw [← PMF.map_comp, thin_map_fst, m.hp]
  hev := by rw [thinEv, mass_thin_inter_evTrue]; exact hpos
  hp' := PMF.ext fun x => by
    rw [hQ', map_apply_eq_mass, mass_condOn, preimage_inter_thinEv, thinEv,
      mass_thin_inter_evTrue, mass_thin_inter_evTrue, thinPostFun]

/-- The thinning of the trivial model by the steering weight towards `Q` has posterior `Q`:
the formula `thinPostFun` evaluates to `Q x` (SC Remark 2.5's construction, in thinning form).
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem thinPostFun_trivial_steer [Countable Ω] (P Q : PMF Ω) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : BoundedDensity Q P B) (x : Ω) :
    Q x = thinPostFun (SameOntologyModel.trivial P).μ (steerWeight P id Q B)
      (SameOntologyModel.trivial P).ev (SameOntologyModel.trivial P).p x := by
  have hB' : BoundedDensity Q (P.map id) B := by rw [PMF.map_id]; exact h
  have e1 := steerWeight_fiber_sum P id Q B hB hB' x
  have e2 := steerWeight_total P id Q B hB hB'
  show Q x = (∑' l, (id ⁻¹' {x} ∩ univ).indicator (fun l => steerWeight P id Q B l * P l) l) *
    (∑' l, (univ : Set Ω).indicator (fun l => steerWeight P id Q B l * P l) l)⁻¹
  simp only [inter_univ, indicator_univ]
  rw [e1, e2, inv_inv, mul_assoc, ENNReal.inv_mul_cancel h.ne_zero hB, mul_one]

/-- The steering weight is at most one for the trivial model (its `map id` is `P`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerWeight_id_le_one (P Q : PMF Ω) (B : ℝ≥0∞) (h : BoundedDensity Q P B) (x : Ω) :
    steerWeight P id Q B x ≤ 1 :=
  steerWeight_le_one P id Q B (by rw [PMF.map_id]; exact h) x

/-- The total steering weight for the trivial model is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem steerWeight_id_total_pos [Countable Ω] (P Q : PMF Ω) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : BoundedDensity Q P B) :
    0 < ∑' l, (SameOntologyModel.trivial P).ev.indicator
      (fun l => steerWeight P id Q B l * (SameOntologyModel.trivial P).μ l) l := by
  show 0 < ∑' l, (univ : Set Ω).indicator (fun l => steerWeight P id Q B l * P l) l
  simp only [indicator_univ]
  exact steerWeight_total_pos P id Q B hB (by rw [PMF.map_id]; exact h)

/-- **The Diaconis–Zabell model** for `P ⟶ Q` with bounded density: the trivial model thinned by
the steering weight. Its posterior is `Q`.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5 (Diaconis–Zabell 1982)
Kind: D
Fidelity: exact (construction differs from SC's: thinning instead of the residual measure)
Hyps: n/a -/
noncomputable def SameOntologyModel.dz [Countable Ω] (P Q : PMF Ω) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : BoundedDensity Q P B) : SameOntologyModel P Q :=
  (SameOntologyModel.trivial P).thin (steerWeight P id Q B) (steerWeight_id_le_one P Q B h)
    (steerWeight_id_total_pos P Q B hB h) Q (thinPostFun_trivial_steer P Q B hB h)

end Cleanroom.Udt.UdtSupercondition
