import Cleanroom.Udt.UdtSupercondition.Anticipation
import Cleanroom.Udt.UdtSupercondition.DZ

/-!
# Canonical `L̄` and calibrated refinement (SC §6.1, §6.3): T13, T14

* T13 (SC Prop 6.1, Candidate A): the **canonical** same-ontology models are those on
  `L = A × Ω` with `μ(ā, x) = P(ā) · κ_ā(x)`, `p = snd` and arbitrary evidence; their posteriors
  are `canonicalPosteriors as`. SC says "measure determined by calibration"; we formalize under
  `Reflective` (which is what `p_* μ = P` needs, and which calibration implies), fidelity
  `variant`. Proved: `jeffreyMixtures_subset_canonical` and `canonical_subset_dz`; the two
  strictness witnesses are in `Witnesses.lean` (`canonical_not_jeffreyMixture_witness`,
  `dz_not_canonical_witness`).
* T14 (SC Def 6.2, Props 6.3, 6.4, Candidate C): `CalibratedRefinement`;
  `refinement_kernel_averages` (Prop 6.3, which needs coarse calibration as a hypothesis — SC's
  Def 6.2 does not state it, its proof uses it); `refinement_top_eq_condOn` (Prop 6.4): the
  posteriors of calibrated refinement models are exactly the Bayesian conditionings of `P` on
  positive events — for *every* refinement, not only `Ā⁺ = P̄` — so "recovers unconstrained
  same-ontology superconditioning" is false under the Diaconis–Zabell reading
  (`Witnesses.lean`, `condOn_not_dz_witness`).

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

variable {Ω : Type} {P : PMF Ω}

/-! ### T13: canonical `L̄` -/

section Canonical

variable (as : AnticipationStructure P Ω)

/-- The canonical joint `μ(ā, x) = P(ā) · κ_ā(x)` on `A × Ω` (SC §6.1).
Source: [[superconditioning-mismatched-ontologies]] §6.1 ("`L(ā, p̄) = P(ā) · κ_ā(p̄)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def canonicalJoint : PMF (as.A × Ω) := couple (P.map as.a) as.κ

/-- The unnormalized canonical posterior weight at `x`: `∑_{ā ∈ S x} P(ā) · κ_ā(x)` (SC §6.1:
"each atom `p̄` selects a subset `l̄_{p̄}` of anticipation atoms").
Source: [[superconditioning-mismatched-ontologies]] §6.1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def canonicalWeight (S : Ω → Set as.A) (x : Ω) : ℝ≥0∞ :=
  ∑' ā, (S x).indicator (fun ā => (P.map as.a) ā * as.κ ā x) ā

/-- The total unnormalized canonical weight.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def canonicalTotal (S : Ω → Set as.A) : ℝ≥0∞ := ∑' x, canonicalWeight as S x

/-- **Canonical-`L̄` posteriors** (SC §6.1): `P′ ∝ x ↦ ∑_{ā ∈ S x} P(ā) · κ_ā(x)` for some
selection `S : Ω → Set A` of positive total weight.
Source: [[superconditioning-mismatched-ontologies]] §6.1 Prop 6.1 | udt-rep-062
Kind: D
Fidelity: exact
Hyps: n/a -/
def canonicalPosteriors : Set (PMF Ω) :=
  { P' | ∃ S : Ω → Set as.A, 0 < canonicalTotal as S ∧
      ∀ x, P' x = canonicalWeight as S x * (canonicalTotal as S)⁻¹ }

/-- **`κ`-mixtures — SC's "Jeffrey posteriors"** (§4.6, "a restricted mixture of the `κ_ā`"):
`P′ ∝ ∑_{ā ∈ T} P(ā) κ_ā` for a set `T` of anticipation atoms containing a positive one. These
are Jeffrey updates of `P` on `Ā` (`JeffreyOnA`) only *under calibration* (then `κ_ā = P(·|ā)`,
`JeffreyOnA.eq_tsum_kappa`), with weights `∝ P(ā)` on `T`. **The reading is load-bearing** for
Prop 6.1: under the general reading `JeffreyOnA` (arbitrary weights on positive atoms) the first
inclusion of Prop 6.1 is *false* — a reflective `as` with weights not proportional to `P(ā)` is
not canonical, since canonical weights at `x` take at most `2^{|A|}` values. The mandate's reading
(this definition) is defensible from §6's opening sentence; the first strictness witness is
robust across both readings (`post13_not_jeffreyOnA`).
Source: [[superconditioning-mismatched-ontologies]] §4.6, §6.1 ("the Jeffrey posteriors") |
audit r1 (fidelity §3.7, adversarial §3.5)
Kind: D
Fidelity: exact (under the restricted-mixture reading; see above)
Hyps: n/a -/
def JeffreyMixtures : Set (PMF Ω) :=
  { P' | ∃ T : Set as.A, (∃ ā ∈ T, 0 < (P.map as.a) ā) ∧
      ∀ x, P' x = (∑' ā, T.indicator (fun ā => (P.map as.a) ā * as.κ ā x) ā) *
        (mass (P.map as.a) T)⁻¹ }

/-- **The Diaconis–Zabell set**: the posteriors with bounded density w.r.t. `P` — by
`sameOntology_condModel_iff`, exactly the unconstrained same-ontology posteriors.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5, §6.1 ("unconstrained
posteriors")
Kind: D
Fidelity: exact
Hyps: n/a -/
def dzPosteriors (P : PMF Ω) : Set (PMF Ω) := { P' | ∃ B, B ≠ ⊤ ∧ BoundedDensity P' P B }

/-- The evidence of a canonical model determined by a selection `S`.
Source: [[superconditioning-mismatched-ontologies]] §6.1
Kind: D
Fidelity: exact
Hyps: n/a -/
def canonicalEv (S : Ω → Set as.A) : Set (as.A × Ω) := {z | z.1 ∈ S z.2}

/-- The canonical joint's mass on `{x} × S x`-type slices is the canonical weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_canonicalJoint_snd_inter (S : Ω → Set as.A) (x : Ω) :
    mass (canonicalJoint as) (Prod.snd ⁻¹' {x} ∩ canonicalEv as S) = canonicalWeight as S x := by
  rw [mass_eq_tsum, ENNReal.tsum_prod', canonicalWeight]
  refine tsum_congr fun ā => ?_
  rw [tsum_eq_single x]
  · by_cases hā : ā ∈ S x
    · rw [indicator_of_mem (show (ā, x) ∈ Prod.snd ⁻¹' {x} ∩ canonicalEv as S from ⟨rfl, hā⟩),
        indicator_of_mem hā, canonicalJoint, couple_apply]
    · rw [indicator_of_notMem (fun h => hā h.2), indicator_of_notMem hā]
  · intro y hy
    exact indicator_of_notMem (fun h => hy (mem_singleton_iff.1 h.1)) _

/-- The canonical joint's mass on the evidence is the canonical total.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_canonicalJoint_ev (S : Ω → Set as.A) :
    mass (canonicalJoint as) (canonicalEv as S) = canonicalTotal as S := by
  rw [mass_eq_tsum_fiber (canonicalJoint as) _ Prod.snd, canonicalTotal]
  exact tsum_congr fun x => by rw [inter_comm, mass_canonicalJoint_snd_inter]

/-- **The canonical model** (SC §6.1, Candidate A): `L = A × Ω`, `μ = canonicalJoint`,
`p = snd`, evidence `canonicalEv S`; under reflection its posterior is the canonical posterior of
`S`. SC says "measure determined by calibration"; `p_* μ = P` needs exactly reflection.
Source: [[superconditioning-mismatched-ontologies]] §6.1 | udt-rep-062
Kind: D
Fidelity: variant: `Reflective` in place of SC's "determined by calibration" (reflection is what
`p_* μ = P` requires; calibration implies it, Prop 3.8)
Hyps: n/a -/
noncomputable def canonicalModel [Countable Ω] (hR : as.Reflective) (S : Ω → Set as.A)
    (hS : 0 < canonicalTotal as S) (P' : PMF Ω)
    (hP' : ∀ x, P' x = canonicalWeight as S x * (canonicalTotal as S)⁻¹) :
    SameOntologyModel P P' where
  L := as.A × Ω
  μ := canonicalJoint as
  p := Prod.snd
  ev := canonicalEv as S
  hp := by rw [canonicalJoint, couple_map_snd]; exact hR
  hev := by rw [mass_canonicalJoint_ev]; exact hS
  hp' := PMF.ext fun x => by
    rw [hP', map_apply_eq_mass, mass_condOn, mass_canonicalJoint_snd_inter, mass_canonicalJoint_ev]

/-- **Identification (SC §6.1):** the canonical posteriors are exactly the posteriors of the
canonical joint conditioned on an arbitrary evidence event of `A × Ω` and pushed to `Ω`.
Source: [[superconditioning-mismatched-ontologies]] §6.1 | udt-rep-062
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem mem_canonicalPosteriors_iff (P' : PMF Ω) :
    P' ∈ canonicalPosteriors as ↔
      ∃ (ev : Set (as.A × Ω)) (hev : 0 < mass (canonicalJoint as) ev),
        (condOn (canonicalJoint as) ev hev).map Prod.snd = P' := by
  constructor
  · rintro ⟨S, hS, hP'⟩
    refine ⟨canonicalEv as S, by rw [mass_canonicalJoint_ev]; exact hS, PMF.ext fun x => ?_⟩
    rw [hP', map_apply_eq_mass, mass_condOn, mass_canonicalJoint_snd_inter, mass_canonicalJoint_ev]
  · rintro ⟨ev, hev, hP'⟩
    have hS : canonicalEv as (fun x => {ā | (ā, x) ∈ ev}) = ev := by
      ext ⟨ā, x⟩; rfl
    refine ⟨fun x => {ā | (ā, x) ∈ ev}, by rw [← mass_canonicalJoint_ev, hS]; exact hev, fun x => ?_⟩
    rw [← hP', map_apply_eq_mass, mass_condOn, ← mass_canonicalJoint_snd_inter as _ x,
      ← mass_canonicalJoint_ev, hS]

/-- **Jeffrey mixtures are canonical posteriors** (SC Prop 6.1, first inclusion): take the
selection constant, `S x = T`.
Source: [[superconditioning-mismatched-ontologies]] §6.1 Prop 6.1 | udt-rep-062
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem jeffreyMixtures_subset_canonical : JeffreyMixtures as ⊆ canonicalPosteriors as := by
  rintro P' ⟨T, ⟨ā₀, hā₀, hpos⟩, hP'⟩
  have htotal : canonicalTotal as (fun _ => T) = mass (P.map as.a) T := by
    rw [canonicalTotal, mass_eq_tsum]
    simp only [canonicalWeight]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ā => ?_
    by_cases hā : ā ∈ T
    · simp only [indicator_of_mem hā]
      rw [ENNReal.tsum_mul_left, (as.κ ā).tsum_coe, mul_one]
    · simp only [indicator_of_notMem hā, tsum_zero]
  refine ⟨fun _ => T, ?_, fun x => ?_⟩
  · rw [htotal]
    exact lt_of_lt_of_le hpos (apply_le_mass _ hā₀)
  · rw [hP' x, htotal]; rfl

/-- **Canonical posteriors have bounded density** (SC Prop 6.1, second inclusion, under
reflection): `P′ x ≤ P x / total`.
Source: [[superconditioning-mismatched-ontologies]] §6.1 Prop 6.1 | udt-rep-062
Kind: P
Fidelity: variant: under `Reflective`
Hyps: (a) all -/
theorem canonical_subset_dz (hR : as.Reflective) : canonicalPosteriors as ⊆ dzPosteriors P := by
  rintro P' ⟨S, hS, hP'⟩
  refine ⟨(canonicalTotal as S)⁻¹, ENNReal.inv_ne_top.2 hS.ne', fun x => ?_⟩
  rw [hP' x, mul_comm]
  refine mul_le_mul' le_rfl ?_
  calc canonicalWeight as S x ≤ ∑' ā, (P.map as.a) ā * as.κ ā x :=
        ENNReal.tsum_le_tsum fun ā => indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le)
    _ = as.priorPredictive x := (as.priorPredictive_apply x).symm
    _ = P x := by rw [hR]

end Canonical

/-! ### T14: calibrated refinement -/

/-- **A calibrated refinement model** (SC Def 6.2): a finer anticipation `a⁺` (with
`a = g ∘ a⁺`), a kernel `κ⁺` calibrated on the finer atoms, and an evidence event `ev` of the
finer algebra with `P′ = P(· | a⁺⁻¹ ev)`. SC's Def 6.2 does not require the *coarse* kernel to
be calibrated; Prop 6.3 needs it (`refinement_kernel_averages`).
Source: [[superconditioning-mismatched-ontologies]] §6.3 Def 6.2 | udt-rep-063
Kind: D
Fidelity: exact
Hyps: n/a -/
structure CalibratedRefinement (P : PMF Ω) (P' : PMF Ω) (as : AnticipationStructure P Ω) where
  /-- The finer anticipation atoms. -/
  Aplus : Type
  /-- Countability (SC §0.10). -/
  [countable : Countable Aplus]
  /-- The finer quotient map. -/
  aplus : Ω → Aplus
  /-- The coarsening `A⁺ → A`. -/
  g : Aplus → as.A
  /-- `Ā ⊆ Ā⁺`: `a` factors through `a⁺`. -/
  hg : as.a = g ∘ aplus
  /-- The refined kernel. -/
  κplus : Aplus → PMF Ω
  /-- The refined kernel is calibrated. -/
  hcal : AnticipationStructure.Calibrated (P := P) { A := Aplus, a := aplus, κ := κplus }
  /-- The evidence, an event of the finer algebra. -/
  ev : Set Aplus
  /-- The evidence has positive mass. -/
  hpos : 0 < mass P (aplus ⁻¹' ev)
  /-- `P′ = P(· | ā₀)`. -/
  hpost : P' = condOn P (aplus ⁻¹' ev) hpos

attribute [instance] CalibratedRefinement.countable

variable {P' : PMF Ω} {as : AnticipationStructure P Ω}

/-- **Prop 6.3, multiplicative form:** `κ_ā(x) · P(ā) = ∑_{b ⊆ ā} κ⁺_{b}(x) · P(b)`, for a
refinement whose coarse kernel is calibrated.
Source: [[superconditioning-mismatched-ontologies]] §6.3 Prop 6.3 | udt-rep-063
Kind: P
Fidelity: variant: adds the hypothesis `as.Calibrated` (coarse calibration), which SC's Def 6.2
does not state and Prop 6.3's proof uses ("calibration at both levels")
Hyps: (a) all -/
theorem refinement_kernel_averages_mul (r : CalibratedRefinement P P' as) (hc : as.Calibrated)
    (ā : as.A) (x : Ω) :
    as.κ ā x * (P.map as.a) ā =
      ∑' b, (r.g ⁻¹' {ā}).indicator (fun b => r.κplus b x * (P.map r.aplus) b) b := by
  rw [← hc ā x, r.hg, preimage_comp, inter_comm,
    mass_inter_preimage_eq_tsum P {x} r.aplus (r.g ⁻¹' {ā})]
  refine tsum_congr fun b => ?_
  by_cases h : b ∈ r.g ⁻¹' {ā}
  · rw [indicator_of_mem h, indicator_of_mem h, inter_comm]
    exact r.hcal b x
  · rw [indicator_of_notMem h, indicator_of_notMem h]

/-- **SC Prop 6.3 (coherence of a calibrated refinement):** on a positive coarse atom the
refined kernel averages back to the coarse one,
`κ_ā = ∑_{b ⊆ ā} (P(b)/P(ā)) · κ⁺_{b}`, provided the coarse kernel is calibrated.
Source: [[superconditioning-mismatched-ontologies]] §6.3 Prop 6.3 | udt-rep-063
Kind: P
Fidelity: variant: adds the hypothesis `as.Calibrated`, which SC's Def 6.2 does not state and
Prop 6.3's proof uses (finding: imprecision)
Scope: same ontology; SC-internal calibration
Hyps: (a) all -/
theorem refinement_kernel_averages (r : CalibratedRefinement P P' as) (hc : as.Calibrated)
    (ā : as.A) (hā : 0 < (P.map as.a) ā) (x : Ω) :
    as.κ ā x = ∑' b, (r.g ⁻¹' {ā}).indicator
      (fun b => (P.map r.aplus) b * ((P.map as.a) ā)⁻¹ * r.κplus b x) b := by
  have e := refinement_kernel_averages_mul r hc ā x
  calc as.κ ā x = as.κ ā x * (P.map as.a) ā * ((P.map as.a) ā)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hā.ne' (PMF.apply_ne_top _ _), mul_one]
    _ = (∑' b, (r.g ⁻¹' {ā}).indicator (fun b => r.κplus b x * (P.map r.aplus) b) b) *
        ((P.map as.a) ā)⁻¹ := by rw [e]
    _ = _ := by
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun b => ?_
        rw [← indicator_mul_const]
        by_cases h : b ∈ r.g ⁻¹' {ā}
        · rw [indicator_of_mem h, indicator_of_mem h]; ring
        · rw [indicator_of_notMem h, indicator_of_notMem h]

/-- **Prop 6.4's refinement:** `Ā⁺ = P̄` (`a⁺ = id`), `κ⁺ = δ`, evidence any event `S` of positive
mass; `δ` is calibrated.
Source: [[superconditioning-mismatched-ontologies]] §6.3 Prop 6.4 | udt-rep-063
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def topRefinement [Countable Ω] (as : AnticipationStructure P Ω) (S : Set Ω)
    (h : 0 < mass P S) : CalibratedRefinement P (condOn P S h) as where
  Aplus := Ω
  aplus := id
  g := as.a
  hg := rfl
  κplus := PMF.pure
  hcal := fun x' x => by
    show mass P (id ⁻¹' {x'} ∩ {x}) = PMF.pure x' x * (P.map id) x'
    rw [PMF.pure_apply, PMF.map_id, preimage_id]
    by_cases hx : x = x'
    · subst hx; rw [inter_self, mass_singleton, if_pos rfl, one_mul]
    · rw [if_neg hx, zero_mul, mass_eq_zero_iff]
      rintro y ⟨hy1, hy2⟩
      exact absurd ((mem_singleton_iff.1 hy2).symm.trans (mem_singleton_iff.1 hy1)) hx
  ev := S
  hpos := by rw [preimage_id]; exact h
  hpost := by
    have key : ∀ (T : Set Ω) (hT : 0 < mass P T), T = S → condOn P T hT = condOn P S h := by
      intro T hT e; subst e; rfl
    exact (key _ _ (preimage_id)).symm

/-- **SC Prop 6.4, both readings resolved:** the posteriors of calibrated refinement models are
exactly the Bayesian conditionings of `P` on positive events — and this holds for *every*
refinement, not only `Ā⁺ = P̄`. Under the reading "conditioning on any event of `P̄`" Prop 6.4 is
true; under the Diaconis–Zabell reading ("unconstrained same-ontology superconditioning",
`dzPosteriors`) it is false (`condOn_not_dz_witness`): refinement inside `P̄` never enriches.
Plumbing, not a theorem with content: SC Def 6.2 *defines* `P′ = P(· | ā₀)` (the `hpost` field),
so (⇒) is that field read off and (⇐) is `topRefinement`; the D–Z reading of Prop 6.4 is false by
Def 6.2 itself, and `condOn_not_dz_witness` only exhibits the gap between event conditioning and
D–Z.
Source: [[superconditioning-mismatched-ontologies]] §6.3 Prop 6.4, §8.4 ("interpolates") |
udt-rep-063 | audit r1 (fidelity §3.5)
Kind: L
Fidelity: variant: the statement is the event-conditioning reading; the D–Z reading is refuted
Scope: same ontology
Hyps: (a) all -/
theorem refinement_posteriors_eq_condOn [Countable Ω] (as : AnticipationStructure P Ω)
    (P' : PMF Ω) :
    Nonempty (CalibratedRefinement P P' as) ↔ ∃ (S : Set Ω) (h : 0 < mass P S), P' = condOn P S h :=
  ⟨fun ⟨r⟩ => ⟨r.aplus ⁻¹' r.ev, r.hpos, r.hpost⟩,
    fun ⟨S, h, hP'⟩ => ⟨hP' ▸ topRefinement as S h⟩⟩

/-- Round-0 name of `refinement_posteriors_eq_condOn`, kept so the round-0 ledger and report
resolve; the new name says the statement is for every refinement, not only `Ā⁺ = P̄` ("top").
Source: none: infrastructure (alias)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem refinement_top_eq_condOn [Countable Ω] (as : AnticipationStructure P Ω) (P' : PMF Ω) :
    Nonempty (CalibratedRefinement P P' as) ↔ ∃ (S : Set Ω) (h : 0 < mass P S), P' = condOn P S h :=
  refinement_posteriors_eq_condOn as P'

end Cleanroom.Udt.UdtSupercondition
