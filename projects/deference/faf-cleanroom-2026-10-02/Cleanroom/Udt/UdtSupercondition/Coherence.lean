import Cleanroom.Udt.UdtSupercondition.Anticipation
import Cleanroom.Udt.UdtSupercondition.DZ
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Epistemic coherence, the downstream order, variable ontologies, utility agreement
(SC §7, §12.1, §12.2 last paragraph, §14, §15 Q7): T15, T16, T17

* T15 `EpistemicallyCoherent` (SC Def 12.1) and its collapse `epistemicallyCoherent_iff_condOn`:
  because a calibrated anticipation structure can always be manufactured from the prior's own
  conditionals (`condAnticipation`), same-ontology coherence is exactly "`Xⱼ` is a conditioning
  of `Xᵢ` on a positive event". The anticipation adds nothing unless it is fixed in advance:
  `CoherentVia as` is that fixed-structure variant (what Claim 12.3 and `corr-reflect-frames`
  need). `Downstream` (SC §14) is a partial order on measures (`downstream_isPartialOrder`) —
  on measures, not on decision-points, whose utilities may differ.
* T16 `VarAnticipation`, `VarCommonInfo`, `universallyShared` (SC Def 7.1, §7.2): definitions,
  with the antitonicity of the universally shared algebra in the set of future ontologies.
* T17 `UtilityAgreement` (SC §12.2 last paragraph, §15 Q7): the note's own proposal
  `uᵢ(O, xᵢ) = uⱼ(O, xⱼ)` whenever `cᵢ xᵢ = cⱼ xⱼ`, made exact: it forces `uᵢ o` to factor
  through `cᵢ` on `cᵢ⁻¹(range cⱼ)` (`UtilityAgreement.factors`), the common factor
  (`commonFactor`) is what both utilities are, and expectations are then comparable through the
  common information (`UtilityAgreement.expectation_eq`, finite carriers). Stated over bare
  `(Ω, u : O → Ω → ℝ)`, without decision-point structure (`udt-harmony-bargain` owns those; the
  separation is by design, plan §0.4 rule 10, not a `(c)`).

**Vocabulary (dp-cf-2-064):** SC's "coherence" (Def 12.1/12.2) is an epistemic relation between
decision-points; it is not v2's Def 22 (Nash-type). Nothing here is called `Coherent`
unqualified.

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

variable {Ω : Type}

/-! ### T15: same-ontology epistemic coherence -/

/-- **Epistemically coherent pair** (SC Def 12.1): `Xⱼ` arises from `Xᵢ` by conditioning on an
atom of *some* calibrated anticipation structure on `Xᵢ`. SC's sense of "coherence", not v2's
Def 22 (dp-cf-2-064). Collapses to `Downstream` (`epistemicallyCoherent_iff_condOn`).
Source: [[superconditioning-mismatched-ontologies]] §12.1 Def 12.1 | udt-rep-076
Kind: D
Fidelity: exact
Scope: same ontology; SC-internal calibration
Hyps: n/a -/
def EpistemicallyCoherent (Xi Xj : PMF Ω) : Prop :=
  ∃ as : AnticipationStructure Xi Ω, as.Calibrated ∧
    ∃ (ā₀ : as.A) (h : 0 < mass Xi (as.a ⁻¹' {ā₀})), Xj = condOn Xi (as.a ⁻¹' {ā₀}) h

/-- **Coherence via a fixed anticipation structure:** `as` is calibrated and `Xⱼ` is the
conditioning of `Xᵢ` on one of its atoms. This is the variant with content (the structure is
given in advance), the one Claim 12.3 and the endorsement theorems need.
Source: [[superconditioning-mismatched-ontologies]] §12.1 Def 12.1 (read with `(Ā, κ)` fixed) |
udt-rep-076 (the inventory's triviality note)
Kind: D
Fidelity: variant: the anticipation structure is a parameter, not existentially quantified
Scope: same ontology; SC-internal calibration
Hyps: n/a -/
def CoherentVia {Xi : PMF Ω} (as : AnticipationStructure Xi Ω) (Xj : PMF Ω) : Prop :=
  as.Calibrated ∧ ∃ (ā₀ : as.A) (h : 0 < mass Xi (as.a ⁻¹' {ā₀})), Xj = condOn Xi (as.a ⁻¹' {ā₀}) h

/-- **Downstream** (SC §14): `Xⱼ` is a Bayesian conditioning of `Xᵢ` on a positive event.
Source: [[superconditioning-mismatched-ontologies]] §14 | udt-rep-076
Kind: D
Fidelity: exact (after the collapse `epistemicallyCoherent_iff_condOn`)
Hyps: n/a -/
def Downstream (Xi Xj : PMF Ω) : Prop :=
  ∃ (S : Set Ω) (h : 0 < mass Xi S), Xj = condOn Xi S h

/-- Coherence via a fixed structure implies coherence.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem CoherentVia.epistemicallyCoherent {Xi Xj : PMF Ω} {as : AnticipationStructure Xi Ω}
    (h : CoherentVia as Xj) : EpistemicallyCoherent Xi Xj :=
  ⟨as, h.1, h.2⟩

/-- Coherence implies downstream.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem EpistemicallyCoherent.downstream {Xi Xj : PMF Ω} (h : EpistemicallyCoherent Xi Xj) :
    Downstream Xi Xj := by
  obtain ⟨as, -, ā₀, hā₀, hXj⟩ := h
  exact ⟨_, hā₀, hXj⟩

/-- **Def 12.1 collapses to conditioning on a positive event** (the inventory's triviality note,
made a theorem): every conditioning `Xᵢ(· | S)` is coherent via the two-atom structure
`a = 𝟙_S` with the prior's own conditionals as kernel, which is calibrated by construction. So
the anticipation structure adds nothing unless `(Ā, κ)` is fixed in advance (`CoherentVia`).
Source: [[superconditioning-mismatched-ontologies]] §12.1 Def 12.1, §14 | udt-rep-076
Kind: P
Fidelity: exact (finding: the definition is degenerate as stated)
Scope: same ontology
Hyps: (a) all -/
theorem epistemicallyCoherent_iff_condOn (Xi Xj : PMF Ω) :
    EpistemicallyCoherent Xi Xj ↔ Downstream Xi Xj := by
  classical
  refine ⟨EpistemicallyCoherent.downstream, ?_⟩
  rintro ⟨S, h, hXj⟩
  let a : Ω → Bool := fun x => decide (x ∈ S)
  have ha : a ⁻¹' {true} = S := by
    ext x; simp [a]
  have hpos : 0 < mass Xi (a ⁻¹' {true}) := by rw [ha]; exact h
  refine ⟨condAnticipation Xi a, calibrated_condAnticipation Xi a, true, hpos, ?_⟩
  have key : ∀ (T : Set Ω) (hT : 0 < mass Xi T), T = S → condOn Xi T hT = condOn Xi S h := by
    intro T hT e; subst e; rfl
  rw [hXj]
  exact (key _ hpos ha).symm

/-- `Downstream` is reflexive: condition on the whole space.
Source: [[superconditioning-mismatched-ontologies]] §14 ("a partial order")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem downstream_refl (Xi : PMF Ω) : Downstream Xi Xi :=
  ⟨univ, by rw [mass_univ]; exact zero_lt_one, (condOn_univ Xi _).symm⟩

/-- `Downstream` is transitive: the chain rule for conditioning.
Source: [[superconditioning-mismatched-ontologies]] §14 ("a partial order")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem downstream_trans {Xi Xj Xk : PMF Ω} (hij : Downstream Xi Xj) (hjk : Downstream Xj Xk) :
    Downstream Xi Xk := by
  obtain ⟨S, hS, rfl⟩ := hij
  obtain ⟨T, hT, rfl⟩ := hjk
  exact ⟨S ∩ T, pos_of_mass_condOn_pos Xi hS hT, condOn_condOn Xi hS hT _⟩

/-- `Downstream` is antisymmetric on measures: mutual conditioning forces `Xᵢ(S) = 1`.
Source: [[superconditioning-mismatched-ontologies]] §14 ("a partial order") | udt-rep-076
Kind: P
Fidelity: exact (on measures; on decision-points with distinct utilities it is not antisymmetric
— one sentence, no Lean)
Hyps: (a) all -/
theorem downstream_antisymm {Xi Xj : PMF Ω} (hij : Downstream Xi Xj) (hji : Downstream Xj Xi) :
    Xi = Xj := by
  obtain ⟨S, hS, hXj⟩ := hij
  obtain ⟨T, hT, hXi⟩ := hji
  have hsupp : ∀ x, Xi x ≠ 0 → x ∈ S := fun x hx => by
    have h1 : Xi x = T.indicator Xj x * (mass Xj T)⁻¹ := by
      conv_lhs => rw [hXi]
      exact condOn_apply Xj T hT x
    have h2 : Xj x ≠ 0 := by
      intro h0
      apply hx
      rw [h1]
      by_cases hxT : x ∈ T
      · rw [indicator_of_mem hxT, h0, zero_mul]
      · rw [indicator_of_notMem hxT, zero_mul]
    by_contra hxS
    apply h2
    rw [hXj, condOn_apply_of_notMem Xi hS hxS]
  have hone : mass Xi S = 1 := (mass_eq_one_iff Xi S).2 hsupp
  refine PMF.ext fun x => ?_
  rw [hXj, condOn_apply, hone, inv_one, mul_one]
  by_cases hxS : x ∈ S
  · rw [indicator_of_mem hxS]
  · rw [indicator_of_notMem hxS]
    by_contra hx
    exact hxS (hsupp x hx)

/-- **`Downstream` is a partial order on `PMF Ω`** (SC §14).
Source: [[superconditioning-mismatched-ontologies]] §14 | udt-rep-076
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem downstream_isPartialOrder : IsPartialOrder (PMF Ω) Downstream where
  refl := downstream_refl
  trans := fun _ _ _ => downstream_trans
  antisymm := fun _ _ => downstream_antisymm

/-! ### T16: variable future ontology -/

/-- **Anticipation structure with variable ontology** (SC Def 7.1): per-atom target types and
kernels.
Source: [[superconditioning-mismatched-ontologies]] §7.1 Def 7.1 | udt-rep-064
Kind: D
Fidelity: exact
Hyps: n/a -/
structure VarAnticipation (P : PMF Ω) where
  /-- The anticipation atoms. -/
  A : Type
  /-- Countability (SC §0.10). -/
  [countable : Countable A]
  /-- The quotient map onto the atoms. -/
  a : Ω → A
  /-- The future ontology of each atom. -/
  Q : A → Type
  /-- The intended kernel on each atom's ontology. -/
  κ : ∀ ā, PMF (Q ā)

attribute [instance] VarAnticipation.countable

/-- **Per-atom common information** (SC §7.2): for each atom a common-information structure
between `Ω` and that atom's future ontology.
Source: [[superconditioning-mismatched-ontologies]] §7.2 | udt-rep-064
Kind: D
Fidelity: exact
Hyps: n/a -/
structure VarCommonInfo {P : PMF Ω} (va : VarAnticipation P) where
  /-- The shared language of each atom. -/
  C : va.A → Type
  /-- The interpretation in `Ω`. -/
  c : ∀ ā, Ω → C ā
  /-- The interpretation in the atom's future ontology. -/
  c' : ∀ ā, va.Q ā → C ā

variable {P : PMF Ω} {va : VarAnticipation P}

/-- The events of `Ω` expressible in the shared language of atom `ā`: `c_ā(C̄_ā)`.
Source: [[superconditioning-mismatched-ontologies]] §7.2
Kind: D
Fidelity: exact
Hyps: n/a -/
def sharedAlgebra (vci : VarCommonInfo va) (ā : va.A) : Set (Set Ω) :=
  Set.range fun T : Set (vci.C ā) => vci.c ā ⁻¹' T

/-- The events expressible in every future ontology of a set `J` of atoms.
Source: [[superconditioning-mismatched-ontologies]] §7.2
Kind: D
Fidelity: exact
Hyps: n/a -/
def universallySharedOn (vci : VarCommonInfo va) (J : Set va.A) : Set (Set Ω) :=
  ⋂ ā ∈ J, sharedAlgebra vci ā

/-- **The universally shared algebra** `Ū = ⋂_ā c_ā(C̄_ā)` (SC §7.2): the events expressible in
all possible future ontologies.
Source: [[superconditioning-mismatched-ontologies]] §7.2 | udt-rep-064
Kind: D
Fidelity: exact
Hyps: n/a -/
def universallyShared (vci : VarCommonInfo va) : Set (Set Ω) :=
  ⋂ ā, sharedAlgebra vci ā

/-- Membership in the universally shared algebra.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mem_universallyShared_iff (vci : VarCommonInfo va) (S : Set Ω) :
    S ∈ universallyShared vci ↔ ∀ ā, ∃ T : Set (vci.C ā), vci.c ā ⁻¹' T = S := by
  simp only [universallyShared, mem_iInter, sharedAlgebra, mem_range]

/-- The universally shared algebra is the one over all atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem universallyShared_eq_on_univ (vci : VarCommonInfo va) :
    universallyShared vci = universallySharedOn vci univ := by
  simp only [universallySharedOn, mem_univ, iInter_true]; rfl

/-- **"As the number of possible future ontologies grows, `Ū` shrinks"** (SC §7.2): the shared
algebra over a larger set of atoms is smaller — antitonicity of the intersection.
Source: [[superconditioning-mismatched-ontologies]] §7.2 | udt-rep-064
Kind: T
Fidelity: exact
Hyps: (a) -/
theorem universallySharedOn_antitone (vci : VarCommonInfo va) {J₁ J₂ : Set va.A} (h : J₁ ⊆ J₂) :
    universallySharedOn vci J₂ ⊆ universallySharedOn vci J₁ :=
  biInter_subset_biInter_left h

/-- The whole space and the empty event are always universally shared.
Source: none: infrastructure (non-vacuity of `universallyShared`)
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem univ_mem_universallyShared (vci : VarCommonInfo va) : univ ∈ universallyShared vci :=
  (mem_universallyShared_iff vci univ).2 fun _ => ⟨univ, preimage_univ⟩

/-! ### T17: cross-ontology utility agreement -/

section Utility

variable {Ωi Ωj O : Type} (ci : CommonInfo Ωi Ωj)

/-- **Utility agreement on shared propositions** (SC §12.2 last paragraph, §15 Q7's proposal):
`uᵢ(o, xᵢ) = uⱼ(o, xⱼ)` whenever `cᵢ xᵢ = cⱼ xⱼ`. Over bare `(Ω, u)`, without decision-point
structure (owned by `udt-harmony-bargain`; separation by design).
Source: [[superconditioning-mismatched-ontologies]] §12.2, §15 item 7 | udt-rep-077
Kind: D
Fidelity: exact (the note's own proposed condition)
Hyps: n/a -/
def UtilityAgreement (ui : O → Ωi → ℝ) (uj : O → Ωj → ℝ) : Prop :=
  ∀ o xi xj, ci.c xi = ci.c' xj → ui o xi = uj o xj

variable {ci} {ui : O → Ωi → ℝ} {uj : O → Ωj → ℝ}

/-- **Agreement forces factoring** (the note's "too strong" worry, made exact): `uᵢ o` is
constant on each `cᵢ`-fibre that meets the range of `cⱼ`.
Source: [[superconditioning-mismatched-ontologies]] §15 item 7 ("may be too strong") |
udt-rep-077
Kind: S
Fidelity: exact
Hyps: (a) -/
theorem UtilityAgreement.factors (h : UtilityAgreement ci ui uj) (o : O) {x₁ x₂ : Ωi}
    (hx : ci.c x₁ = ci.c x₂) (hr : ci.c x₁ ∈ Set.range ci.c') : ui o x₁ = ui o x₂ := by
  obtain ⟨xj, hxj⟩ := hr
  rw [h o x₁ xj hxj.symm, h o x₂ xj (hx ▸ hxj).symm]

open Classical in
/-- The common factor `ū o y`: the value of `uⱼ o` at any point of the `cⱼ`-fibre over `y`
(`0` if the fibre is empty).
Source: [[superconditioning-mismatched-ontologies]] §15 item 7 ("comparable through the common
information")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def commonFactor (ci : CommonInfo Ωi Ωj) (uj : O → Ωj → ℝ) (o : O) (y : ci.C) : ℝ :=
  if h : ∃ xj, ci.c' xj = y then uj o (Classical.choose h) else 0

/-- `uᵢ o` is the common factor of `cᵢ` on `cᵢ⁻¹(range cⱼ)`.
Source: [[superconditioning-mismatched-ontologies]] §15 item 7
Kind: S
Fidelity: exact
Hyps: (a) -/
theorem UtilityAgreement.ui_eq_commonFactor (h : UtilityAgreement ci ui uj) (o : O) (xi : Ωi)
    (hr : ci.c xi ∈ Set.range ci.c') : ui o xi = commonFactor ci uj o (ci.c xi) := by
  have hex : ∃ xj, ci.c' xj = ci.c xi := hr
  rw [commonFactor, dif_pos hex]
  exact h o xi _ (Classical.choose_spec hex).symm

/-- `uⱼ o` is the common factor of `cⱼ` on `cⱼ⁻¹(range cᵢ)`.
Source: [[superconditioning-mismatched-ontologies]] §15 item 7
Kind: S
Fidelity: exact
Hyps: (a) -/
theorem UtilityAgreement.uj_eq_commonFactor (h : UtilityAgreement ci ui uj) (o : O) (xj : Ωj)
    (hr : ci.c' xj ∈ Set.range ci.c) : uj o xj = commonFactor ci uj o (ci.c' xj) := by
  obtain ⟨xi, hxi⟩ := hr
  have hex : ∃ xj', ci.c' xj' = ci.c' xj := ⟨xj, rfl⟩
  rw [commonFactor, dif_pos hex, ← h o xi xj hxi, ← h o xi _ (hxi.trans (Classical.choose_spec hex).symm)]

/-- **Expectations are comparable through the common information** (finite carriers): under
agreement, if every `Xᵢ`-positive point translates into the range of `cⱼ`, then
`𝔼_{Xᵢ}[uᵢ o] = 𝔼_{Cᵢ}[ū o]` for the common factor `ū`. A fibrewise regrouping
(`Finset.sum_fiberwise`), not a squeeze: the mandate's pre-label "S" read as "simple";
[[STANDARDS]] §6's `S` is a squeeze, so the Kind is `L`.
Source: [[superconditioning-mismatched-ontologies]] §15 item 7 | udt-rep-077
Kind: L
Fidelity: variant: finite carriers (`Fintype Ωᵢ`, `Fintype ci.C`), real-valued sums via `toReal`
Hyps: (a) all; `hr` (every `Xᵢ`-positive point translates into `range cⱼ`) is an addition to SC
§15 Q7, which is a question, not a claim — it guards `commonFactor`'s `0` on empty fibres -/
theorem UtilityAgreement.expectation_eq [Fintype Ωi] [Fintype ci.C] [DecidableEq ci.C]
    (h : UtilityAgreement ci ui uj) (Xi : PMF Ωi)
    (hr : ∀ xi, Xi xi ≠ 0 → ci.c xi ∈ Set.range ci.c') (o : O) :
    ∑ xi, (Xi xi).toReal * ui o xi = ∑ y, (ci.C₁ Xi y).toReal * commonFactor ci uj o y := by
  have hC : ∀ y, (ci.C₁ Xi y).toReal = ∑ xi with ci.c xi = y, (Xi xi).toReal := fun y => by
    rw [ci.C₁_apply, mass, PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum
      (fun xi _ => (indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le)).trans_lt
        (PMF.apply_lt_top _ _) |>.ne),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun xi _ => ?_
    by_cases hxi : ci.c xi = y
    · rw [if_pos hxi, indicator_of_mem (show xi ∈ ci.c ⁻¹' {y} from hxi)]
    · rw [if_neg hxi, indicator_of_notMem (show xi ∉ ci.c ⁻¹' {y} from hxi), ENNReal.toReal_zero]
  rw [← Finset.sum_fiberwise Finset.univ ci.c (fun xi => (Xi xi).toReal * ui o xi)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hC, Finset.sum_mul]
  refine Finset.sum_congr rfl fun xi hxi => ?_
  rw [Finset.mem_filter] at hxi
  by_cases h0 : Xi xi = 0
  · rw [h0, ENNReal.toReal_zero, zero_mul, zero_mul]
  · rw [h.ui_eq_commonFactor o xi (hr xi h0), hxi.2]

end Utility

end Cleanroom.Udt.UdtSupercondition
