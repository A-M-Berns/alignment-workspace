import Cleanroom.Udt.UdtEndorsePolicy.Generalize
import Cleanroom.Udt.UdtSupercondition.Anticipation

/-!
# T3: the Reflection Principle as belief endorsement of one's conditional future beliefs, and
the ladder `Calibrated ⟹ BeliefEndorsedAll ⟹ Reflective`

Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle ("if `P₁` is an
agent's beliefs at one time, and `P₂` is an agent's beliefs at a future time, then `P₁` should
belief-endorse `P₂`"); udt-rep-2-014; SC Defs 3.5/3.7, Prop 3.8 via `udt-supercondition`.

**Representation.** The objects are `udt-supercondition`'s: a prior `P : PMF Ω` on a finite
`Ω` and an anticipation structure `as : AnticipationStructure P Ω` (same ontology) — atoms
`as.a : Ω → as.A` and the intended future belief `as.κ ā : PMF Ω` on each atom. The **finite
definition of record is applied to real weights** (`pw P ω := (P ω).toReal`) **and real
reports** (`futureBelief as X ω := (κ_{a ω}(X)).toReal`, `futureExp as V ω := E_{κ_{a ω}} V`):
option (i) of the mandate. No second belief endorsement is defined; the `ℝ≥0∞`/real bridge is
`toReal_mass_finset` and `pw_cls_eq_atomMass`.

* `expectationEndorsedAll_of_calibrated` (P): SC-internal calibration makes every future
  expectation report endorsed; `beliefEndorsedAll_of_calibrated` is the indicator case (T3(b)).
* `beliefEndorsedAll_condAnticipation` (T3(a), the **Reflection Principle**): the future self
  that Bayes-updates on the cell of `a` is belief-endorsed on every event — derived from (b) and
  `calibrated_condAnticipation`.
* `reflective_of_beliefEndorsedAll` (T3(c), P): endorsement on every event forces the
  prior-predictive to equal the prior (total probability, then a `PMF` is its singleton masses).
* Both implications are strict: the witnesses are in `ReflectionWitnesses.lean`
  (`reflective_not_endorsed_witness` on SC's `as38`, `endorsed_not_calibrated_witness` on a
  `Fin 3` structure that is also not expectation-endorsed — T2(d)(ii)).

**Scope.** `Calibrated` is SC-internal calibration (`P(· | ā) = κ_ā` on positive atoms), never
the decision-problems' external calibration. The post's principle is normative ("should"); these
are the descriptive theorems behind it, for the finite same-ontology case.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Finset
open Cleanroom.Udt.UdtSupercondition (AnticipationStructure condAnticipation
  calibrated_condAnticipation)
open scoped ENNReal

noncomputable section

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {P : PMF Ω}

/-! ### The real-weight bridge -/

/-- The real weight of a `PMF`: `pw P ω = (P ω).toReal`.
Source: mandate T3 (representation, option (i))
Kind: D
Fidelity: exact (a `PMF` on a finite carrier is its real weights)
Hyps: n/a -/
def pw (P : PMF Ω) (ω : Ω) : ℝ := (P ω).toReal

omit [Fintype Ω] [DecidableEq Ω] in
/-- Supporting lemma: real weights are non-negative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pw_nonneg (P : PMF Ω) (ω : Ω) : 0 ≤ pw P ω := ENNReal.toReal_nonneg

/-- Supporting lemma: the real mass of a finite event under a `PMF` is the finite sum of real
weights (`udt-supercondition`'s `mass` in `ℝ≥0∞` versus `udt-policy-calc`'s `mass` in `ℝ`).
Source: none: infrastructure (the `ℝ≥0∞`/real bridge)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toReal_mass_finset (P : PMF Ω) (X : Finset Ω) :
    (UdtSupercondition.mass P (↑X : Set Ω)).toReal = mass (pw P) X := by
  have hne : ∀ ω ∈ (univ : Finset Ω), (↑X : Set Ω).indicator P ω ≠ ⊤ := fun ω _ => by
    by_cases h : ω ∈ (↑X : Set Ω)
    · rw [Set.indicator_of_mem h]; exact PMF.apply_ne_top P ω
    · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top
  show (P.toOuterMeasure ↑X).toReal = _
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum hne]
  simp only [Set.indicator_apply, Finset.mem_coe, apply_ite ENNReal.toReal, ENNReal.toReal_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  rfl

/-- Supporting lemma: the real mass of the atom `ā` is `(P.map a) ā` made real.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pw_cls_eq_atomMass {A : Type} [DecidableEq A] (P : PMF Ω) (a : Ω → A) (ā : A) :
    mass (pw P) (cls a ā) = ((P.map a) ā).toReal := by
  rw [UdtSupercondition.map_apply_eq_mass, ← toReal_mass_finset]
  congr 2
  ext ω; simp

/-! ### The future reports and the two "endorsed on everything" predicates -/

/-- The **future belief report** about the event `X`: at `ω`, the mass the intended kernel of
`ω`'s atom puts on `X`, `κ_{a ω}(X)` as a real. This is the post's `"P₂(X)"` when `P₂` is the
agent's own future belief.
Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle | udt-rep-2-014
Kind: D
Fidelity: exact (finite, same ontology)
Hyps: n/a -/
def futureBelief (as : AnticipationStructure P Ω) (X : Finset Ω) (ω : Ω) : ℝ :=
  (UdtSupercondition.mass (as.κ (as.a ω)) (↑X : Set Ω)).toReal

/-- The **future expectation report** of `V`: `E_{κ_{a ω}} V`.
Source: [[meaning-and-agency-reference]] §Expectation Endorsement, §The Van Fraassen Reflection Principle
Kind: D
Fidelity: exact (finite, same ontology)
Hyps: n/a -/
def futureExp (as : AnticipationStructure P Ω) (V : Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ x, (as.κ (as.a ω) x).toReal * V x

/-- Supporting lemma: the future belief report is the future expectation report of the indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem futureBelief_eq_futureExp_ind (as : AnticipationStructure P Ω) (X : Finset Ω) :
    futureBelief as X = futureExp as (ind X) := by
  funext ω
  unfold futureBelief futureExp
  rw [toReal_mass_finset, mass]
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  rfl

/-- **Belief-endorsed on every event**: the prior belief-endorses its intended future belief about
every `X : Finset Ω` (the finite definition of record applied to the real weights and the real
future belief report).
Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle | udt-rep-2-014
Kind: D
Fidelity: exact (finite, same ontology; every event)
Scope: finite `Ω`; the second agent is the future self, entering through its reports only
Hyps: n/a -/
def BeliefEndorsedAll (P : PMF Ω) (as : AnticipationStructure P Ω) : Prop :=
  ∀ X : Finset Ω, BeliefEndorses (pw P) X (futureBelief as X)

/-- **Expectation-endorsed on every variable**: the prior expectation-endorses the intended future
expectation of every `V : Ω → ℝ`.
Source: [[meaning-and-agency-reference]] §Expectation Endorsement | mandate T3(e)
Kind: D
Fidelity: exact (finite, same ontology; every real variable)
Hyps: n/a -/
def ExpectationEndorsedAll (P : PMF Ω) (as : AnticipationStructure P Ω) : Prop :=
  ∀ V : Ω → ℝ, ExpectationEndorses (pw P) V (futureExp as V)

/-! ### Calibration ⟹ endorsement -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- Supporting lemma: calibration on an atom in real form — `P x · [a x = ā] = κ_ā(x) · P(ā)`.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Def 3.5, made real
Kind: L
Fidelity: n/a
Hyps: none -/
theorem calibrated_pointwise_real {as : AnticipationStructure P Ω} [DecidableEq as.A]
    (h : as.Calibrated) (ā : as.A) (x : Ω) :
    (if as.a x = ā then pw P x else 0) = (as.κ ā x).toReal * ((P.map as.a) ā).toReal := by
  have hc := h ā x
  rw [UdtSupercondition.mass_inter_singleton] at hc
  rw [← ENNReal.toReal_mul, ← hc]
  by_cases hx : as.a x = ā
  · rw [if_pos hx, Set.indicator_of_mem (show x ∈ as.a ⁻¹' {ā} from hx)]
    rfl
  · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ as.a ⁻¹' {ā} from hx), ENNReal.toReal_zero]

omit [DecidableEq Ω] in
/-- Supporting lemma: under calibration, the weighted sum of `V` over the atom `ā` is
`P(ā) · E_{κ_ā} V`.
Source: none: infrastructure (T3(b)/(e))
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_atom_of_calibrated {as : AnticipationStructure P Ω} [DecidableEq as.A]
    (h : as.Calibrated) (ā : as.A) (V : Ω → ℝ) :
    wsum (pw P) V (cls as.a ā) = ((P.map as.a) ā).toReal * ∑ x, (as.κ ā x).toReal * V x := by
  rw [wsum_event_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have key := calibrated_pointwise_real h ā x
  by_cases hx : as.a x = ā
  · rw [if_pos hx] at key ⊢
    rw [key]; ring
  · rw [if_neg hx] at key ⊢
    rw [← mul_assoc, mul_comm ((P.map as.a) ā).toReal, ← key, zero_mul]

omit [DecidableEq Ω] in
/-- Supporting lemma: the future expectation report is constant on atoms, so its value classes
are unions of atoms: a fibre of `a` inside a value class is the whole atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem filter_cls_futureExp_eq_atom (as : AnticipationStructure P Ω) [DecidableEq as.A]
    (V : Ω → ℝ) (x : ℝ) (ā : as.A) (hā : ā ∈ (cls (futureExp as V) x).image as.a) :
    (cls (futureExp as V) x).filter (fun ω => as.a ω = ā) = cls as.a ā := by
  obtain ⟨ω₀, hω₀, rfl⟩ := Finset.mem_image.1 hā
  have hx : futureExp as V ω₀ = x := by simpa using hω₀
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro hω
    refine ⟨?_, hω⟩
    rw [← hx]
    unfold futureExp
    rw [hω]

/-- **SC-internal calibration makes every future expectation report endorsed** (P): on the value
class `{E_{κ_{a·}} V = x}`, a union of atoms with `E_{κ_ā} V = x`, calibration gives
`∑_ā P(ā) · E_{κ_ā} V = x · ∑_ā P(ā)`.
Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle | udt-rep-2-014 | SC Def 3.5 (mandate T3(e), the workhorse for T3(b))
Kind: P
Fidelity: exact (finite, same ontology)
Scope: `Calibrated` is SC-internal (Def 3.5), not the decision-problems' external calibration
Hyps: (a) all -/
theorem expectationEndorsedAll_of_calibrated {as : AnticipationStructure P Ω}
    (h : as.Calibrated) : ExpectationEndorsedAll P as := by
  classical
  intro V x _
  set E := cls (futureExp as V) x with hE
  rw [wsum_fiberwise (pw P) V E as.a, ← wsum_one (pw P) E, wsum_fiberwise (pw P) _ E as.a,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ā hā => ?_
  rw [filter_cls_futureExp_eq_atom as V x ā hā, wsum_atom_of_calibrated h ā V,
    wsum_atom_of_calibrated h ā (fun _ => 1)]
  obtain ⟨ω₀, hω₀, rfl⟩ := Finset.mem_image.1 hā
  have hx : futureExp as V ω₀ = x := by simpa [hE] using hω₀
  have h1 : ∑ y, (as.κ (as.a ω₀) y).toReal * (1 : ℝ) = 1 := by
    simp only [mul_one]
    rw [← ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top _ y)]
    have := (as.κ (as.a ω₀)).tsum_coe
    rw [tsum_fintype] at this
    rw [this, ENNReal.toReal_one]
  unfold futureExp at hx
  rw [hx, h1]
  ring

/-- **Expectation endorsement on every variable implies belief endorsement on every event** (T):
indicators are variables.
Source: [[meaning-and-agency-reference]] §Expectation Endorsement (mandate T3(e))
Kind: T
Fidelity: exact
Hyps: (a) none -/
theorem beliefEndorsedAll_of_expectationEndorsedAll {as : AnticipationStructure P Ω}
    (h : ExpectationEndorsedAll P as) : BeliefEndorsedAll P as := fun X => by
  rw [beliefEndorses_iff_expectation_ind, futureBelief_eq_futureExp_ind]
  exact h (ind X)

/-- **T3(b): SC-internal calibration implies belief endorsement on every event.**
Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle | udt-rep-2-014 | SC Def 3.5
Kind: C
Fidelity: exact (finite, same ontology)
Scope: `Calibrated` is SC-internal; converse fails (`endorsed_not_calibrated_witness`)
Hyps: (a) all -/
theorem beliefEndorsedAll_of_calibrated {as : AnticipationStructure P Ω} (h : as.Calibrated) :
    BeliefEndorsedAll P as :=
  beliefEndorsedAll_of_expectationEndorsedAll (expectationEndorsedAll_of_calibrated h)

/-- **T3(a), the Reflection Principle**: the future self that Bayes-updates on the cell of `a`
(`condAnticipation P a`, whose kernel is the prior's own conditionals) is belief-endorsed on
every event. The post states this normatively ("`P₁` *should* belief-endorse `P₂`"); this is the
descriptive theorem behind it in the finite same-ontology case: a future belief that *is* a
conditional of the present one is endorsed. Derived from T3(b) and
`udt-supercondition`'s `calibrated_condAnticipation`.
Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle | udt-rep-2-014
Kind: C
Fidelity: exact for the finite same-ontology case; the post's "should" is normative, this is descriptive
Scope: finite `Ω`; the future belief is `P(· | a⁻¹{a ω})` on positive cells (`P` on null cells, which no positive-mass predicate sees)
Hyps: (a) none -/
theorem beliefEndorsedAll_condAnticipation (P : PMF Ω) {A : Type} [Countable A] (a : Ω → A) :
    BeliefEndorsedAll P (condAnticipation P a) :=
  beliefEndorsedAll_of_calibrated (calibrated_condAnticipation P a)

/-! ### Endorsement ⟹ reflection -/

/-- **T3(c): belief endorsement on every event implies reflection** (P): for each `x`,
endorsement on `{x}` gives `P(x) = ∑_ω P(ω) κ_{a ω}(x) = Q₀(x)` (total probability over the value
classes of the future belief report), and a `PMF` is determined by its singleton masses.
Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle | udt-rep-2-014 | SC Def 3.7
Kind: P
Fidelity: exact (finite, same ontology)
Scope: converse fails (`reflective_not_endorsed_witness`, SC's `as38`)
Hyps: (a) all -/
theorem reflective_of_beliefEndorsedAll {as : AnticipationStructure P Ω}
    (h : BeliefEndorsedAll P as) : as.Reflective := by
  refine PMF.ext fun x => ?_
  rw [AnticipationStructure.priorPredictive_eq_bind, PMF.bind_apply, tsum_fintype]
  have hx := beliefEndorses_total (pw_nonneg P) (h {x})
  have hmass : mass (pw P) {x} = (P x).toReal := by simp [mass, pw]
  rw [hmass] at hx
  have hfb : ∀ ω, futureBelief as {x} ω = (as.κ (as.a ω) x).toReal := fun ω => by
    unfold futureBelief
    rw [Finset.coe_singleton, UdtSupercondition.mass_singleton]
  simp only [wsum, hfb, pw] at hx
  have hne1 : ∑ ω, P ω * (as.κ ∘ as.a) ω x ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun ω _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  rw [← ENNReal.toReal_eq_toReal_iff' hne1 (PMF.apply_ne_top _ _),
    ENNReal.toReal_sum (fun ω _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
  simp only [ENNReal.toReal_mul, Function.comp]
  exact hx.symm

/-- **The ladder, stated once**: `Calibrated ⟹ BeliefEndorsedAll ⟹ Reflective` (both strict;
witnesses in `ReflectionWitnesses.lean`). SC's Prop 3.8 (`calibrated_implies_reflective`) is the
composite.
Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle | udt-rep-2-014 | SC Prop 3.8
Kind: C
Fidelity: exact (finite, same ontology)
Hyps: (a) all -/
theorem calibrated_endorsed_reflective_ladder (as : AnticipationStructure P Ω) :
    (as.Calibrated → BeliefEndorsedAll P as) ∧ (BeliefEndorsedAll P as → as.Reflective) :=
  ⟨beliefEndorsedAll_of_calibrated, reflective_of_beliefEndorsedAll⟩

end

end Cleanroom.Udt.UdtEndorsePolicy
