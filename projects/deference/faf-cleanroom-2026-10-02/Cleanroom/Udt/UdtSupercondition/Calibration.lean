import Cleanroom.Udt.UdtSupercondition.Anticipation
import Cleanroom.Udt.UdtSupercondition.DZ

/-!
# Calibrated conditioning models (SC §4–§5, §12.2): T9, T10, T11

* T9 `calibrated_condModel_exists` (SC Thm 4.5, **calibration does not restrict posteriors**):
  for any anticipation structure and any `Q` with bounded density w.r.t. the prior-predictive
  `Q₀`, a calibrated conditioning model with posterior exactly `Q` exists. No hypothesis on the
  anticipation structure (SC assumes none either). Construction: the steered thinning of the
  coupling `(x, q) ↦ P x · κ_{a x}(q)`.
* T10 (SC Prop 4.7, **corrected**): `compatible_calibrated_iff_bridgeCalibrated` — a compatible
  *and* calibrated model exists iff the anticipation is `Ĉ`-calibrated (Def 5.1) and `P′` has
  bounded density w.r.t. `Q₀`. Necessity of `Ĉ`-calibration is
  `BridgeCalibrated.of_compatible_cmCalibrated`; under it `Q₀.map c′ = C` (so the range
  condition of T4 is automatic) and the common-information D–Z condition is *implied* by the
  calibration one (`BridgeCalibrated.boundedDensity_C`): "the tighter of the two" is always the
  calibration condition. Prop 4.7 as stated is refuted by `prop47_refuted` (in `Witnesses.lean`).
* T11 `CrossCoherent` (SC Def 12.2) with `crossCoherent_iff_ineq`: clause (1)'s existence and
  inequality readings coincide in the presence of clause (2), because `Ĉ`-calibration forces the
  range condition.

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

variable {Ω Ω' : Type} {P : PMF Ω}

/-! ### A fibre-regrouping lemma with an indicator -/

/-- A sum of `S.indicator (u (g x) · P x)` regroups by the fibres of `g`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem tsum_indicator_comp_mul_eq_tsum_fiber {X Y : Type*} (P : PMF X) (g : X → Y)
    (u : Y → ℝ≥0∞) (S : Set X) :
    ∑' x, S.indicator (fun x => u (g x) * P x) x = ∑' y, u y * mass P (S ∩ g ⁻¹' {y}) := by
  rw [tsum_fiber g]
  refine tsum_congr fun y => ?_
  rw [mass_eq_tsum, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [indicator_indicator]
  by_cases hx : x ∈ g ⁻¹' {y} ∩ S
  · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ S ∩ g ⁻¹' {y} from ⟨hx.2, hx.1⟩)]
    have : g x = y := hx.1
    rw [this]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ⟨h.2, h.1⟩), mul_zero]

/-! ### T9: calibration does not restrict posteriors -/

section T9

variable (as : AnticipationStructure P Ω') (Q : PMF Ω')

/-- The bounded-density hypothesis of Thm 4.5, transported to the coupling's second marginal.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem boundedDensity_couple_snd {B : ℝ≥0∞} (hBD : BoundedDensity Q as.priorPredictive B) :
    BoundedDensity Q ((couple P (as.κ ∘ as.a)).map Prod.snd) B := by
  rw [couple_map_snd, ← as.priorPredictive_eq_bind]; exact hBD

/-- **SC Thm 4.5's model:** the steered thinning of `(x, q) ↦ P x · κ_{a x}(q)` towards `Q`
along the `Q`-coordinate, on `(Ω × Ω′) × Bool`, evidence the `true` layer, `μ(ev) = 1/B`.
Source: [[superconditioning-mismatched-ontologies]] §4.4 Thm 4.5 (proof)
Kind: D
Fidelity: exact (SC's `L` with the weight `(1/B)·Q/Q₀`; the `0/0` convention made explicit)
Hyps: n/a -/
noncomputable def calModel [Countable Ω] [Countable Ω'] {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hBD : BoundedDensity Q as.priorPredictive B) : CondModel P Q where
  L := (Ω × Ω') × Bool
  μ := steerThin (couple P (as.κ ∘ as.a)) Prod.snd Q B (boundedDensity_couple_snd as Q hBD)
  p := fun l => l.1.1
  p' := fun l => l.1.2
  ev := evTrue (Ω × Ω')
  hp := by
    show (steerThin _ _ _ _ _).map (Prod.fst ∘ Prod.fst) = P
    rw [← PMF.map_comp, steerThin_map_fst, couple_map_fst]
  hev := steerThin_evTrue_pos _ _ _ _ hB (boundedDensity_couple_snd as Q hBD)
  hp' := steerThin_condOn_map _ _ _ _ hB (boundedDensity_couple_snd as Q hBD)

/-- The joint law of Thm 4.5's model is the coupling `(x, q) ↦ P x · κ_{a x}(q)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem calModel_jointLaw [Countable Ω] [Countable Ω'] {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hBD : BoundedDensity Q as.priorPredictive B) :
    (calModel as Q hB hBD).jointLaw = couple P (as.κ ∘ as.a) := by
  show (steerThin (couple P (as.κ ∘ as.a)) Prod.snd Q B
    (boundedDensity_couple_snd as Q hBD)).map Prod.fst = _
  exact steerThin_map_fst _ _ _ _ _

/-- Thm 4.5's model is calibrated.
Source: [[superconditioning-mismatched-ontologies]] §4.4 Thm 4.5 ("Calibration")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem calModel_cmCalibrated [Countable Ω] [Countable Ω'] {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hBD : BoundedDensity Q as.priorPredictive B) :
    CMCalibrated (calModel as Q hB hBD) as := by
  rw [cmCalibrated_iff_jointCalibrated, calModel_jointLaw]
  exact jointCalibrated_couple as

/-- Thm 4.5's model has evidence mass `1/B`.
Source: [[superconditioning-mismatched-ontologies]] §4.4 Thm 4.5 ("`L(l̄) = 1/B`")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem calModel_mass_ev [Countable Ω] [Countable Ω'] {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hBD : BoundedDensity Q as.priorPredictive B) :
    mass (calModel as Q hB hBD).μ (calModel as Q hB hBD).ev = B⁻¹ :=
  steerThin_mass_evTrue _ _ _ _ hB (boundedDensity_couple_snd as Q hBD)

/-- **SC Thm 4.5 — calibration does not restrict posteriors.** For any anticipation structure
`(a, κ)` on `P` targeting `Ω′` with prior-predictive `Q₀`, and any `Q` with
`BoundedDensity Q Q₀ B`, `B ≠ ⊤`, there is a **calibrated** conditioning model for `(P, Q)` — the
posterior *is* `Q`, by the `CondModel` field — with evidence mass `1/B`. No hypothesis on
`(a, κ)`: calibration of the anticipation structure itself is not assumed (SC does not assume it
either; the same-ontology reading through Prop 4.2 might suggest otherwise).
Source: [[superconditioning-mismatched-ontologies]] §4.4 Thm 4.5 | udt-rep-059
Kind: P
Fidelity: exact: point-set over countable types (SC §0.2); the `0/0` convention of the weight
made explicit; construction is SC's own (`L̄ = P̄ ⊗ Q̄ ⊗ D̄`)
Scope: countable discrete (SC §0.10); `CMCalibrated` is SC-internal calibration (Def 4.1), not
the decision-problems' external one
Hyps: (a) all -/
theorem calibrated_condModel_exists [Countable Ω] [Countable Ω'] {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hBD : BoundedDensity Q as.priorPredictive B) :
    ∃ m : CondModel P Q, CMCalibrated m as ∧ mass m.μ m.ev = B⁻¹ :=
  ⟨calModel as Q hB hBD, calModel_cmCalibrated as Q hB hBD, calModel_mass_ev as Q hB hBD⟩

/-- The posterior of any conditioning model has bounded density `1/μ(ev)` w.r.t. the model's
unconditional `Ω′`-marginal.
Source: [[superconditioning-mismatched-ontologies]] §2.5 (the necessity argument, applied to
`p′` itself)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem CondModel.post_boundedDensity {Q : PMF Ω'} (m : CondModel P Q) :
    BoundedDensity Q (m.μ.map m.p') (mass m.μ m.ev)⁻¹ := fun x' => by
  have e : Q x' = ((condOn m.μ m.ev m.hev).map m.p') x' := by rw [m.hp']
  rw [e, map_apply_eq_mass, mass_condOn, map_apply_eq_mass, mul_comm]
  exact mul_le_mul' le_rfl (mass_mono _ inter_subset_left)

/-- **The converse of Thm 4.5:** a calibrated conditioning model forces the calibration D–Z
condition `Q ≪ Q₀` with bounded density (bound `1/μ(ev)`). So Thm 4.5 is an iff.
Source: [[superconditioning-mismatched-ontologies]] §4.5 ("the D-Z condition relative to `Q₀`
is necessary")
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem CMCalibrated.boundedDensity {Q : PMF Ω'} {m : CondModel P Q}
    {as : AnticipationStructure P Ω'} (h : CMCalibrated m as) :
    BoundedDensity Q as.priorPredictive (mass m.μ m.ev)⁻¹ := by
  have := m.post_boundedDensity
  rwa [h.map_p'] at this

/-- **Thm 4.5 as an iff:** a calibrated conditioning model for `(P, Q)` exists iff `Q` has
bounded density w.r.t. the prior-predictive.
Source: [[superconditioning-mismatched-ontologies]] §4.4 Thm 4.5, §4.5 (necessity)
Kind: C
Fidelity: stronger: SC states only (⇐)
Hyps: (a) all -/
theorem calibrated_condModel_iff [Countable Ω] [Countable Ω'] :
    (∃ m : CondModel P Q, CMCalibrated m as) ↔ ∃ B, B ≠ ⊤ ∧ BoundedDensity Q as.priorPredictive B :=
  ⟨fun ⟨m, hm⟩ => ⟨_, m.inv_mass_ev_ne_top, hm.boundedDensity⟩,
    fun ⟨_, hB, hBD⟩ => ⟨calModel as Q hB hBD, calModel_cmCalibrated as Q hB hBD⟩⟩

end T9

/-! ### T10: Prop 4.7 corrected -/

section T10

variable {P' : PMF Ω'} (as : AnticipationStructure P Ω') (ci : CommonInfo Ω Ω')

/-- Under compatibility, pulling back a `C`-event through `c′ ∘ p′` is pulling it back through
`c ∘ p`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Compatible.preimage_c' {P' : PMF Ω'} {m : CondModel P P'} {ci : CommonInfo Ω Ω'}
    (hm : Compatible m ci) (T : Set ci.C) :
    m.p' ⁻¹' (ci.c' ⁻¹' T) = m.p ⁻¹' (ci.c ⁻¹' T) := by
  ext l
  have := congrFun hm l
  simp only [Function.comp_apply] at this
  simp only [mem_preimage, this]

/-- **Necessity of `Ĉ`-calibration** (T10 (i)): a `Ĉ`-compatible *and* calibrated conditioning
model forces the anticipation to be `Ĉ`-calibrated. This is the hypothesis SC Prop 4.7 omits.
Source: [[superconditioning-mismatched-ontologies]] §4.5 Prop 4.7 (corrected) | udt-rep-060
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem BridgeCalibrated.of_compatible_cmCalibrated {m : CondModel P P'} (hm : Compatible m ci)
    (hc : CMCalibrated m as) : BridgeCalibrated as ci := fun ā y => by
  have e1 : mass P (as.a ⁻¹' {ā} ∩ ci.c ⁻¹' {y}) =
      mass m.μ (m.p ⁻¹' (as.a ⁻¹' {ā}) ∩ m.p' ⁻¹' (ci.c' ⁻¹' {y})) := by
    rw [hm.preimage_c', ← preimage_inter, ← mass_map, m.hp]
  have e2 : mass m.μ (m.p ⁻¹' (as.a ⁻¹' {ā})) = (P.map as.a) ā := by
    rw [← mass_map, m.hp, as.map_a_apply]
  rw [e1, mass_inter_preimage_eq_tsum m.μ (m.p ⁻¹' (as.a ⁻¹' {ā})) m.p' (ci.c' ⁻¹' {y}), ← e2,
    mass_eq_tsum, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ ci.c' ⁻¹' {y}
  · rw [indicator_of_mem hq, indicator_of_mem hq, hc ā q]
  · rw [indicator_of_notMem hq, indicator_of_notMem hq, zero_mul]

/-- Masses of two events that agree on every point of positive mass coincide.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_congr_ae {X : Type} (μ : PMF X) {s t : Set X}
    (h : ∀ l, μ l ≠ 0 → (l ∈ s ↔ l ∈ t)) : mass μ s = mass μ t := by
  rw [mass_eq_tsum, mass_eq_tsum]
  refine tsum_congr fun l => ?_
  by_cases hl : μ l = 0
  · have e1 : s.indicator μ l = 0 := by
      by_cases hs : l ∈ s
      · rw [indicator_of_mem hs, hl]
      · exact indicator_of_notMem hs _
    have e2 : t.indicator μ l = 0 := by
      by_cases ht : l ∈ t
      · rw [indicator_of_mem ht, hl]
      · exact indicator_of_notMem ht _
    rw [e1, e2]
  · by_cases hs : l ∈ s
    · rw [indicator_of_mem hs, indicator_of_mem ((h l hl).1 hs)]
    · rw [indicator_of_notMem hs, indicator_of_notMem (fun ht => hs ((h l hl).2 ht))]

/-- **Necessity of `Ĉ`-calibration under a.e. compatibility** — the encoding check for T10 (i),
the counterpart of `compatibleAE_range_subset` for T3: exact compatibility is not what does the
work; `μ`-a.e. agreement of `c ∘ p` and `c′ ∘ p′` already forces `Ĉ`-calibration of a calibrated
model.
Source: [[superconditioning-mismatched-ontologies]] §4.5 Prop 4.7 (corrected), §0.3 (a.e.
reading) | audit r1 (fidelity §3.6)
Kind: P
Fidelity: variant: a.e. compatibility in place of exact
Hyps: (a) all -/
theorem BridgeCalibrated.of_compatibleAE_cmCalibrated {m : CondModel P P'} (hm : CompatibleAE m ci)
    (hc : CMCalibrated m as) : BridgeCalibrated as ci := fun ā y => by
  have e0 : mass P (as.a ⁻¹' {ā} ∩ ci.c ⁻¹' {y}) =
      mass m.μ (m.p ⁻¹' (as.a ⁻¹' {ā}) ∩ m.p ⁻¹' (ci.c ⁻¹' {y})) := by
    rw [← preimage_inter, ← mass_map, m.hp]
  have e1 : mass P (as.a ⁻¹' {ā} ∩ ci.c ⁻¹' {y}) =
      mass m.μ (m.p ⁻¹' (as.a ⁻¹' {ā}) ∩ m.p' ⁻¹' (ci.c' ⁻¹' {y})) := by
    rw [e0]
    refine mass_congr_ae m.μ fun l hl => ?_
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hm l hl]
  have e2 : mass m.μ (m.p ⁻¹' (as.a ⁻¹' {ā})) = (P.map as.a) ā := by
    rw [← mass_map, m.hp, as.map_a_apply]
  rw [e1, mass_inter_preimage_eq_tsum m.μ (m.p ⁻¹' (as.a ⁻¹' {ā})) m.p' (ci.c' ⁻¹' {y}), ← e2,
    mass_eq_tsum, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ ci.c' ⁻¹' {y}
  · rw [indicator_of_mem hq, indicator_of_mem hq, hc ā q]
  · rw [indicator_of_notMem hq, indicator_of_notMem hq, zero_mul]

/-- **Trivial common information makes every anticipation structure `Ĉ`-calibrated:** with
`C = Unit` the shared language carries no information and Def 5.1 reads `P(ā) = 1 · P(ā)`. So
a `C = Unit` instance cannot witness "`Ĉ`-calibrated but not calibrated" non-degenerately
(`bridgeCalibrated_not_calibrated` uses `C = Bool`, `c = parity4`).
Source: [[superconditioning-mismatched-ontologies]] §5.1 Def 5.1, §2.6 Remark 2.6 | audit r1
(adversarial B1)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem bridgeCalibrated_trivialCI : BridgeCalibrated as (trivialCI Ω Ω') := by
  intro ā y
  have h1 : (trivialCI Ω Ω').c ⁻¹' {y} = univ :=
    eq_univ_of_forall fun _ => mem_singleton_iff.2 (@Subsingleton.elim Unit _ () y)
  have h2 : (trivialCI Ω Ω').c' ⁻¹' {y} = univ :=
    eq_univ_of_forall fun _ => mem_singleton_iff.2 (@Subsingleton.elim Unit _ () y)
  rw [h1, h2, inter_univ, mass_univ, one_mul, as.map_a_apply]

/-- **T10 (ii):** under `Ĉ`-calibration the prior-predictive pushes forward to `C`:
`Q₀.map c′ = C₁`.
Source: [[superconditioning-mismatched-ontologies]] §4.5 (corrected), §5.2
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem BridgeCalibrated.priorPredictive_map_c' (h : BridgeCalibrated as ci) :
    as.priorPredictive.map ci.c' = ci.C₁ P :=
  PMF.ext fun y => by
    rw [map_apply_eq_mass, AnticipationStructure.priorPredictive, mass_bind, ci.C₁_apply,
      mass_eq_tsum_fiber P _ as.a]
    refine tsum_congr fun ā => ?_
    rw [inter_comm, h ā y, mul_comm]

/-- **T10 (ii′):** under `Ĉ`-calibration every `C`-positive shared proposition is in the range of
`c′` — the range condition of the repaired Thm 2.4 is automatic.
Source: [[superconditioning-mismatched-ontologies]] §4.5 (corrected)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem BridgeCalibrated.range (h : BridgeCalibrated as ci) (y : ci.C) (hy : 0 < ci.C₁ P y) :
    y ∈ Set.range ci.c' := by
  rw [← h.priorPredictive_map_c', map_apply_eq_mass, mass_pos_iff] at hy
  obtain ⟨x', hx', -⟩ := hy
  exact ⟨x', hx'⟩

/-- **T10 (iv):** under `Ĉ`-calibration the common-information D–Z condition is *implied* by the
calibration D–Z condition, with the same bound: "the tighter of the two" (SC Prop 4.7) is always
the calibration condition.
Source: [[superconditioning-mismatched-ontologies]] §4.5 Prop 4.7 ("the tighter of the two"),
corrected
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem BridgeCalibrated.boundedDensity_C (h : BridgeCalibrated as ci) {B : ℝ≥0∞}
    (hBD : BoundedDensity P' as.priorPredictive B) :
    BoundedDensity (ci.C₂ P') (ci.C₁ P) B := by
  rw [← h.priorPredictive_map_c']; exact hBD.map ci.c'

/-- The kernel of Prop 4.7's construction: `κ_{a x}` conditioned on the `c′`-fibre over `c x`
(on `P`-positive `x` that fibre has positive `κ_{a x}`-mass under `Ĉ`-calibration); `κ_{a x}`
itself where the fibre is `κ`-null (never used).
Source: [[superconditioning-mismatched-ontologies]] §4.5 Prop 4.7 (sketch: "the
anticipation-calibrated conditionals on the diagonal")
Kind: D
Fidelity: exact on `P`-positive points
Hyps: n/a -/
noncomputable def bridgeKernel (x : Ω) : PMF Ω' :=
  if h : 0 < mass (as.κ (as.a x)) (ci.c' ⁻¹' {ci.c x}) then condOn (as.κ (as.a x)) _ h
  else as.κ (as.a x)

/-- Under `Ĉ`-calibration, at a `P`-positive point the kernel gives the fibre positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem BridgeCalibrated.fibre_pos (h : BridgeCalibrated as ci) {x : Ω} (hx : P x ≠ 0) :
    0 < mass (as.κ (as.a x)) (ci.c' ⁻¹' {ci.c x}) := by
  have h1 : 0 < mass P (as.a ⁻¹' {as.a x} ∩ ci.c ⁻¹' {ci.c x}) :=
    lt_of_lt_of_le (pos_iff_ne_zero.2 hx) (apply_le_mass P ⟨rfl, rfl⟩)
  rw [h (as.a x) (ci.c x)] at h1
  exact (ENNReal.mul_pos_iff.1 h1).1

/-- The bridge kernel's mass function times `P x`, in a form depending on `x` only through
`(a x, c x)`: `P x · G (a x) (c x)` with `G ā y q = 𝟙[c′ q = y] κ_ā(q) / κ_ā(c′⁻¹ y)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem BridgeCalibrated.mul_bridgeKernel (h : BridgeCalibrated as ci) (x : Ω) (q : Ω') :
    P x * bridgeKernel as ci x q =
      P x * ((ci.c' ⁻¹' {ci.c x}).indicator (as.κ (as.a x)) q *
        (mass (as.κ (as.a x)) (ci.c' ⁻¹' {ci.c x}))⁻¹) := by
  by_cases hx : P x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [bridgeKernel, dif_pos (h.fibre_pos as ci hx), condOn_apply]

/-- Under `Ĉ`-calibration the bridge coupling vanishes off the diagonal.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem BridgeCalibrated.bridgeCouple_vanish (h : BridgeCalibrated as ci) :
    ∀ z, z ∉ diagSet ci → couple P (bridgeKernel as ci) z = 0 := by
  rintro ⟨x, x'⟩ hz
  rw [couple_apply, h.mul_bridgeKernel as ci x x',
    indicator_of_notMem (show x' ∉ ci.c' ⁻¹' {ci.c x} from fun e => hz e.symm), zero_mul, mul_zero]

/-- For `q` in the `c′`-fibre over `y`, `𝟙 · κ_ā(q) / κ_ā(fibre) · κ_ā(fibre) = κ_ā(q)`, also when the
fibre is `κ_ā`-null (then `κ_ā(q) = 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem indicator_div_mass_mul (κ : PMF Ω') (T : Set Ω') (q : Ω') :
    T.indicator κ q * (mass κ T)⁻¹ * mass κ T = T.indicator κ q := by
  by_cases hT : mass κ T = 0
  · rw [hT, mul_zero]
    by_cases hq : q ∈ T
    · rw [indicator_of_mem hq]
      exact (le_antisymm ((apply_le_mass κ hq).trans hT.le) zero_le).symm
    · rw [indicator_of_notMem hq]
  · rw [mul_assoc, ENNReal.inv_mul_cancel hT (mass_ne_top _ _), mul_one]

/-- **The bridge coupling is calibrated** under `Ĉ`-calibration: the sum over the atom `ā` of
`P x · bridgeKernel x q` regroups by `c`-fibres, where `Ĉ`-calibration turns
`P(ā ∩ c⁻¹ y)` into `κ_ā(c′⁻¹ y) · P(ā)` and the conditioning denominator cancels.
Source: [[superconditioning-mismatched-ontologies]] §4.5 Prop 4.7 (sketch), verified
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem BridgeCalibrated.jointCalibrated_bridgeCouple (h : BridgeCalibrated as ci) :
    JointCalibrated (couple P (bridgeKernel as ci)) as := fun ā q => by
  rw [mass_couple_prod, ← mass_singleton, ← mass_map, couple_map_fst, mass_singleton,
    ← as.map_a_apply]
  have e1 : ∀ x, (as.a ⁻¹' {ā}).indicator (fun x => P x * mass (bridgeKernel as ci x) {q}) x =
      (as.a ⁻¹' {ā}).indicator (fun x => ((ci.c' ⁻¹' {ci.c x}).indicator (as.κ ā) q *
        (mass (as.κ ā) (ci.c' ⁻¹' {ci.c x}))⁻¹) * P x) x := fun x => by
    by_cases hx : x ∈ as.a ⁻¹' {ā}
    · rw [indicator_of_mem hx, indicator_of_mem hx, mass_singleton, h.mul_bridgeKernel as ci x q,
        mul_comm]
      have : as.a x = ā := hx
      rw [this]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  rw [tsum_congr e1, tsum_indicator_comp_mul_eq_tsum_fiber P ci.c
    (fun y => (ci.c' ⁻¹' {y}).indicator (as.κ ā) q * (mass (as.κ ā) (ci.c' ⁻¹' {y}))⁻¹)]
  have e2 : ∀ y, (ci.c' ⁻¹' {y}).indicator (as.κ ā) q * (mass (as.κ ā) (ci.c' ⁻¹' {y}))⁻¹ *
      mass P (as.a ⁻¹' {ā} ∩ ci.c ⁻¹' {y}) = (ci.c' ⁻¹' {y}).indicator (as.κ ā) q * (P.map as.a) ā :=
    fun y => by rw [h ā y, ← mul_assoc, indicator_div_mass_mul]
  rw [tsum_congr e2, ENNReal.tsum_mul_right, tsum_eq_single (ci.c' q)]
  · rw [indicator_of_mem (show q ∈ ci.c' ⁻¹' {ci.c' q} from rfl)]
  · intro y hy
    exact indicator_of_notMem (s := ci.c' ⁻¹' {y}) (a := q) (fun e => hy (mem_singleton_iff.1 e).symm)
      (as.κ ā)

/-- The bridge coupling restricted to the diagonal.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def bridgePMF (h : BridgeCalibrated as ci) : PMF (diagSet ci) :=
  toSubtype (couple P (bridgeKernel as ci)) (diagSet ci) (h.bridgeCouple_vanish as ci)

/-- The bridge PMF pushes forward to `P` along the first coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bridgePMF_map_fst (h : BridgeCalibrated as ci) :
    (bridgePMF as ci h).map (fun z => z.val.1) = P := by
  show (bridgePMF as ci h).map (Prod.fst ∘ Subtype.val) = P
  rw [← PMF.map_comp, bridgePMF, toSubtype_map_val, couple_map_fst]

/-- The bridge PMF pushes forward to the prior-predictive along the second coordinate.
Source: [[superconditioning-mismatched-ontologies]] §4.5 (the diagonal joint has
`Q̄`-marginal `Q₀`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem bridgePMF_map_snd (h : BridgeCalibrated as ci) :
    (bridgePMF as ci h).map (fun z => z.val.2) = as.priorPredictive := by
  show (bridgePMF as ci h).map (Prod.snd ∘ Subtype.val) = _
  rw [← PMF.map_comp, bridgePMF, toSubtype_map_val]
  exact (h.jointCalibrated_bridgeCouple as ci).map_snd (couple_map_fst _ _)

/-- The bounded-density hypothesis of Prop 4.7, transported to the bridge PMF.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem boundedDensity_bridgePMF (h : BridgeCalibrated as ci) {B : ℝ≥0∞}
    (hBD : BoundedDensity P' as.priorPredictive B) :
    BoundedDensity P' ((bridgePMF as ci h).map (fun z => z.val.2)) B := by
  rw [bridgePMF_map_snd]; exact hBD

/-- **Prop 4.7's model, corrected:** the steered thinning of the diagonal bridge coupling
towards `P′` along the `Ω′`-coordinate, on `diagSet ci × Bool`.
Source: [[superconditioning-mismatched-ontologies]] §4.5 Prop 4.7 (sketch), corrected
Kind: D
Fidelity: variant: needs `Ĉ`-calibration (absent from SC's statement); thinning in place of
SC's `D̄`-layer weights
Hyps: n/a -/
noncomputable def bridgeModel [Countable Ω] [Countable Ω'] (h : BridgeCalibrated as ci) {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hBD : BoundedDensity P' as.priorPredictive B) : CondModel P P' where
  L := diagSet ci × Bool
  μ := steerThin (bridgePMF as ci h) (fun z => z.val.2) P' B (boundedDensity_bridgePMF as ci h hBD)
  p := fun l => l.1.val.1
  p' := fun l => l.1.val.2
  ev := evTrue (diagSet ci)
  hp := by
    show (steerThin _ _ _ _ _).map ((fun z : diagSet ci => z.val.1) ∘ Prod.fst) = P
    rw [← PMF.map_comp, steerThin_map_fst, bridgePMF_map_fst]
  hev := steerThin_evTrue_pos _ _ _ _ hB (boundedDensity_bridgePMF as ci h hBD)
  hp' := steerThin_condOn_map _ _ _ _ hB (boundedDensity_bridgePMF as ci h hBD)

/-- The corrected model is `Ĉ`-compatible (by the carrier).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bridgeModel_compatible [Countable Ω] [Countable Ω'] (h : BridgeCalibrated as ci)
    {B : ℝ≥0∞} (hB : B ≠ ⊤) (hBD : BoundedDensity P' as.priorPredictive B) :
    Compatible (bridgeModel as ci h hB hBD) ci :=
  funext fun l => l.1.property

/-- The corrected model is calibrated (its joint law is the bridge coupling).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bridgeModel_cmCalibrated [Countable Ω] [Countable Ω'] (h : BridgeCalibrated as ci)
    {B : ℝ≥0∞} (hB : B ≠ ⊤) (hBD : BoundedDensity P' as.priorPredictive B) :
    CMCalibrated (bridgeModel as ci h hB hBD) as := by
  rw [cmCalibrated_iff_jointCalibrated]
  have e : (bridgeModel as ci h hB hBD).jointLaw = couple P (bridgeKernel as ci) := by
    show (steerThin (bridgePMF as ci h) (fun z => z.val.2) P' B
      (boundedDensity_bridgePMF as ci h hBD)).map (Subtype.val ∘ Prod.fst) = _
    rw [← PMF.map_comp, steerThin_map_fst, bridgePMF, toSubtype_map_val]
  rw [e]
  exact h.jointCalibrated_bridgeCouple as ci

/-- **SC Prop 4.7, corrected (T10):** a `Ĉ`-compatible *and* calibrated conditioning model for
`(P, P′)` exists iff the anticipation structure is `Ĉ`-calibrated (Def 5.1) and `P′` has bounded
density w.r.t. the prior-predictive `Q₀`. SC's statement lacks `Ĉ`-calibration (which is
necessary, `BridgeCalibrated.of_compatible_cmCalibrated`) and lists the common-information D–Z
condition as a separate constraint, which is implied (`BridgeCalibrated.boundedDensity_C`).
Source: [[superconditioning-mismatched-ontologies]] §4.5 Prop 4.7 (corrected) | udt-rep-060/061
Kind: P
Fidelity: variant: adds the hypothesis `BridgeCalibrated as ci`, absent from SC's statement and
necessary (see `prop47_refuted`); the C-side D–Z condition is a consequence, not a hypothesis
Scope: countable discrete (SC §0.10); `Compatible` exact; `CMCalibrated`/`BridgeCalibrated` are
SC-internal calibration
Hyps: (a) all -/
theorem compatible_calibrated_iff_bridgeCalibrated [Countable Ω] [Countable Ω'] :
    (∃ m : CondModel P P', Compatible m ci ∧ CMCalibrated m as) ↔
      BridgeCalibrated as ci ∧ ∃ B, B ≠ ⊤ ∧ BoundedDensity P' as.priorPredictive B := by
  constructor
  · rintro ⟨m, hm, hc⟩
    exact ⟨BridgeCalibrated.of_compatible_cmCalibrated as ci hm hc,
      _, m.inv_mass_ev_ne_top, hc.boundedDensity⟩
  · rintro ⟨h, B, hB, hBD⟩
    exact ⟨bridgeModel as ci h hB hBD, bridgeModel_compatible as ci h hB hBD,
      bridgeModel_cmCalibrated as ci h hB hBD⟩

/-- The corrected model's evidence has mass `1/B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bridgeModel_mass_ev [Countable Ω] [Countable Ω'] (h : BridgeCalibrated as ci) {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hBD : BoundedDensity P' as.priorPredictive B) :
    mass (bridgeModel as ci h hB hBD).μ (bridgeModel as ci h hB hBD).ev = B⁻¹ :=
  steerThin_mass_evTrue _ _ _ _ hB (boundedDensity_bridgePMF as ci h hBD)

/-- **Prop 4.7 as stated is refuted whenever `Ĉ`-calibration fails:** if the anticipation is not
`Ĉ`-calibrated, then no `Ĉ`-compatible calibrated model exists, *whatever* the two D–Z conditions
say. The `Fin` instance with both D–Z conditions satisfied is `prop47_refuted`.
Source: [[superconditioning-mismatched-ontologies]] §4.5 Prop 4.7 (as stated) | udt-rep-060
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem not_compatible_calibrated_of_not_bridgeCalibrated (h : ¬ BridgeCalibrated as ci) :
    ¬ ∃ m : CondModel P P', Compatible m ci ∧ CMCalibrated m as := by
  rintro ⟨m, hm, hc⟩
  exact h (BridgeCalibrated.of_compatible_cmCalibrated as ci hm hc)

/-! #### Def 5.1's "weaker than full calibration": the same-ontology comparison -/

/-- Same ontology, `c′ = c`: SC-internal calibration implies `Ĉ`-calibration (the only sense in
which Def 5.1 is "weaker than full calibration"; cross-ontology "full calibration" is undefined,
SC Remark 3.6). The converse fails for non-injective `c`: `bridgeCalibrated_not_calibrated`
(in `Witnesses.lean`).
Source: [[superconditioning-mismatched-ontologies]] §5.2 (Def 5.1's comparison claim) |
udt-rep-061
Kind: L
Fidelity: variant: SC's comparison is made precise as the same-ontology, `c′ = c` case
Hyps: (a) -/
theorem AnticipationStructure.Calibrated.bridgeCalibrated {as : AnticipationStructure P Ω}
    (h : as.Calibrated) (ci : CommonInfo Ω Ω) (hcc : ci.c' = ci.c) :
    BridgeCalibrated as ci := fun ā y => by
  rw [hcc]
  have e1 := mass_inter_preimage_eq_tsum P (as.a ⁻¹' {ā}) id (ci.c ⁻¹' {y})
  simp only [preimage_id] at e1
  have e2 := mass_eq_tsum (as.κ ā) (ci.c ⁻¹' {y})
  have e3 : (∑' x, (ci.c ⁻¹' {y}).indicator (as.κ ā) x) * (P.map as.a) ā =
      ∑' x, (ci.c ⁻¹' {y}).indicator (as.κ ā) x * (P.map as.a) ā :=
    ENNReal.tsum_mul_right.symm
  rw [e1, e2, e3]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ ci.c ⁻¹' {y}
  · rw [indicator_of_mem hx, indicator_of_mem hx, h ā x]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]

end T10

/-! ### T11: cross-ontology epistemic coherence (SC Def 12.2) -/

section T11

variable {Ωi Ωj : Type} (ci : CommonInfo Ωi Ωj) (Xi : PMF Ωi) (Xj : PMF Ωj)

/-- **Cross-ontology epistemic coherence** (SC Def 12.2), *existence reading* of clause (1): a
`Ĉ`-compatible conditioning model for `(Xᵢ, Xⱼ)` exists, and some anticipation structure on
`Xᵢ` targeting `Ωⱼ` is `Ĉ`-calibrated. SC's clause (1) says "the compatible model exists:
`Cⱼ ≪ Cᵢ` bounded"; the two readings differ by the range condition of `commonInfo_condModel_iff`
in general, but coincide here (`crossCoherent_iff_ineq`). **Collapse (finding F14):** the
existential clause (2) is *equivalent* to that range condition (`bridgeCalibrated_exists_of_range`
with `BridgeCalibrated.range`), so `CrossCoherent ci Xi Xj ↔ ∃ m, Compatible m ci`
(`crossCoherent_iff_compatible`) — Def 12.2 has no anticipation content unless `(Ā, κ)` is fixed
in advance (`CrossCoherentVia`), exactly as Def 12.1 collapses to `Downstream`. This is SC's
coherence (an epistemic relation between decision-points), not v2's Def 22 (dp-cf-2-064).
Source: [[superconditioning-mismatched-ontologies]] §12.2 Def 12.2 | udt-rep-076
Kind: D
Fidelity: exact (existence reading of clause (1))
Hyps: n/a -/
def CrossCoherent : Prop :=
  (∃ m : CondModel Xi Xj, Compatible m ci) ∧
    ∃ as : AnticipationStructure Xi Ωj, BridgeCalibrated as ci

/-- SC Def 12.2 with the *inequality reading* of clause (1).
Source: [[superconditioning-mismatched-ontologies]] §12.2 Def 12.2 ("`Cⱼ ≪ Cᵢ` with bounded
density")
Kind: D
Fidelity: exact (inequality reading of clause (1))
Hyps: n/a -/
def CrossCoherentIneq : Prop :=
  (∃ B, B ≠ ⊤ ∧ BoundedDensity (ci.C₂ Xj) (ci.C₁ Xi) B) ∧
    ∃ as : AnticipationStructure Xi Ωj, BridgeCalibrated as ci

/-- **The two readings of Def 12.2 coincide:** clause (2) (`Ĉ`-calibration) forces the range
condition that separates the existence and inequality readings of clause (1).
Source: [[superconditioning-mismatched-ontologies]] §12.2 Def 12.2 | udt-rep-076
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem crossCoherent_iff_ineq [Countable Ωi] [Countable Ωj] :
    CrossCoherent ci Xi Xj ↔ CrossCoherentIneq ci Xi Xj := by
  constructor
  · rintro ⟨hm, as, has⟩
    exact ⟨((commonInfo_condModel_iff ci Xi Xj).1 hm).1, as, has⟩
  · rintro ⟨hB, as, has⟩
    exact ⟨(commonInfo_condModel_iff ci Xi Xj).2 ⟨hB, fun y hy => has.range as ci y hy⟩, as, has⟩

include Xj in
/-- **Clause (2) of Def 12.2 is implied by the range condition of the repaired Thm 2.4:** whenever
every `C₁`-positive `y` is in `range c′`, the one-atom anticipation structure whose kernel is
`C₁.bind fibreDist` (any kernel pushing forward to `C₁` along `c′` would do) is `Ĉ`-calibrated.
With `BridgeCalibrated.range` the existential clause (2) is therefore *equivalent* to the range
condition — it adds nothing beyond clause (1) (finding F14).
Source: [[superconditioning-mismatched-ontologies]] §12.2 Def 12.2 clause (2) | audit r1
(fidelity §3.3, adversarial §3.1)
Kind: P
Fidelity: n/a (a fact about the definition)
Hyps: (a) all -/
theorem bridgeCalibrated_exists_of_range (hr : ∀ y, 0 < ci.C₁ Xi y → y ∈ Set.range ci.c') :
    ∃ as : AnticipationStructure Xi Ωj, BridgeCalibrated as ci := by
  refine ⟨{ A := Unit, a := fun _ => (), κ := fun _ => (ci.C₁ Xi).bind (fibreDist ci Xj) }, ?_⟩
  intro ā y
  cases ā
  have hU : (fun _ : Ωi => ()) ⁻¹' {()} = univ := eq_univ_of_forall fun _ => rfl
  change mass Xi ((fun _ : Ωi => ()) ⁻¹' {()} ∩ ci.c ⁻¹' {y}) =
    mass ((ci.C₁ Xi).bind (fibreDist ci Xj)) (ci.c' ⁻¹' {y}) * (Xi.map fun _ => ()) ()
  rw [hU, univ_inter, map_apply_eq_mass, hU, mass_univ, mul_one, ← ci.C₁_apply, mass_bind,
    tsum_eq_single y]
  · by_cases hy : ci.C₁ Xi y = 0
    · rw [hy, zero_mul]
    · have hmem := hr y (pos_iff_ne_zero.2 hy)
      have h1 : mass (fibreDist ci Xj y) (ci.c' ⁻¹' {y}) = 1 := by
        rw [mass_eq_one_iff]
        intro x' hx'
        by_contra hc
        exact hx' (fibreDist_apply_of_ne ci Xj hmem x' hc)
      rw [h1, mul_one]
  · intro y' hy'
    by_cases hy0 : ci.C₁ Xi y' = 0
    · rw [hy0, zero_mul]
    · have hmem := hr y' (pos_iff_ne_zero.2 hy0)
      have h0 : mass (fibreDist ci Xj y') (ci.c' ⁻¹' {y}) = 0 := by
        rw [mass_eq_zero_iff]
        intro x' hx'
        have hx'' : ci.c' x' = y := hx'
        exact fibreDist_apply_of_ne ci Xj hmem x' fun e => hy' (e.symm.trans hx'')
      rw [h0, mul_zero]

/-- **Def 12.2 collapses to the repaired Thm 2.4** (finding F14): `CrossCoherent ci Xi Xj` iff a
`Ĉ`-compatible conditioning model exists. The anticipation clause is idle under existential
quantification — the cross-ontology counterpart of `epistemicallyCoherent_iff_condOn` (F7).
Source: [[superconditioning-mismatched-ontologies]] §12.2 Def 12.2 | udt-rep-076 | audit r1
Kind: C
Fidelity: exact (finding: the definition is degenerate as stated)
Hyps: (a) all -/
theorem crossCoherent_iff_compatible [Countable Ωi] [Countable Ωj] :
    CrossCoherent ci Xi Xj ↔ ∃ m : CondModel Xi Xj, Compatible m ci :=
  ⟨fun h => h.1, fun h => ⟨h, bridgeCalibrated_exists_of_range ci Xi Xj
    fun y hy => ((commonInfo_condModel_iff ci Xi Xj).1 h).2 y hy⟩⟩

/-- The inequality reading likewise: Def 12.2 is "bounded density and the range condition".
Source: [[superconditioning-mismatched-ontologies]] §12.2 Def 12.2 | audit r1
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem crossCoherentIneq_iff :
    CrossCoherentIneq ci Xi Xj ↔
      (∃ B, B ≠ ⊤ ∧ BoundedDensity (ci.C₂ Xj) (ci.C₁ Xi) B) ∧
        ∀ y, 0 < ci.C₁ Xi y → y ∈ Set.range ci.c' :=
  ⟨fun ⟨hB, as, has⟩ => ⟨hB, fun y hy => has.range as ci y hy⟩,
    fun ⟨hB, hr⟩ => ⟨hB, bridgeCalibrated_exists_of_range ci Xi Xj hr⟩⟩

/-- **Cross-ontology coherence via a fixed anticipation structure** (Def 12.2 read with `(Ā, κ)`
given in advance): a `Ĉ`-compatible conditioning model for `(Xᵢ, Xⱼ)` exists and *this* `as` is
`Ĉ`-calibrated. The cross-ontology counterpart of `CoherentVia`, and the version with content
(`crossCoherent_iff_compatible` shows the existential Def 12.2 has none): `BridgeCalibrated as ci`
fails for `as10`/`ci10` (`prop47_refuted`). A compatible model *calibrated w.r.t. `as`* is the
stronger `∃ m, Compatible m ci ∧ CMCalibrated m as` of `compatible_calibrated_iff_bridgeCalibrated`,
which adds the calibration D–Z bound `P′ ≪ Q₀`.
Source: [[superconditioning-mismatched-ontologies]] §12.2 Def 12.2 (read with `(Ā, κ)` fixed) |
udt-rep-076 | audit r1 (fidelity §3.3, adversarial §3.1)
Kind: D
Fidelity: variant: the anticipation structure is a parameter, not existentially quantified
Hyps: n/a -/
def CrossCoherentVia (as : AnticipationStructure Xi Ωj) : Prop :=
  (∃ m : CondModel Xi Xj, Compatible m ci) ∧ BridgeCalibrated as ci

/-- Coherence via a fixed structure implies Def 12.2's existential coherence.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem CrossCoherentVia.crossCoherent {as : AnticipationStructure Xi Ωj}
    (h : CrossCoherentVia ci Xi Xj as) : CrossCoherent ci Xi Xj :=
  ⟨h.1, as, h.2⟩

/-- **Fixed-structure Def 12.2, resolved:** `CrossCoherentVia ci Xi Xj as` iff `as` is
`Ĉ`-calibrated and `C₂` has bounded density w.r.t. `C₁` (the range condition is automatic from
`Ĉ`-calibration).
Source: [[superconditioning-mismatched-ontologies]] §12.2 Def 12.2 | audit r1
Kind: C
Fidelity: variant (fixed structure)
Hyps: (a) all -/
theorem crossCoherentVia_iff [Countable Ωi] [Countable Ωj] (as : AnticipationStructure Xi Ωj) :
    CrossCoherentVia ci Xi Xj as ↔
      BridgeCalibrated as ci ∧ ∃ B, B ≠ ⊤ ∧ BoundedDensity (ci.C₂ Xj) (ci.C₁ Xi) B := by
  constructor
  · rintro ⟨hm, has⟩
    exact ⟨has, ((commonInfo_condModel_iff ci Xi Xj).1 hm).1⟩
  · rintro ⟨has, hB⟩
    exact ⟨(commonInfo_condModel_iff ci Xi Xj).2 ⟨hB, fun y hy => has.range as ci y hy⟩, has⟩

end T11

end Cleanroom.Udt.UdtSupercondition
