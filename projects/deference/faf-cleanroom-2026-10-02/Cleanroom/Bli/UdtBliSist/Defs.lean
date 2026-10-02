import Cleanroom.Bli.UdtBliCore.Decomposition
import Cleanroom.Bli.UdtBliCore.Updateful
import Cleanroom.Bli.UdtBliCore.Mugging

/-!
# `udt-bli-sist` · Defs: the class-cut, the two-step objects, the correlation profile (T1)

The definitions of record of the SIST package, over `udt-bli-core`'s `FiniteBLIPrior`.

* **The class-cut** (`classCut`, Kind C): for a class `𝒞` of tables, if no action at `Q` moves any
  branch weight (`ReflectiveAt P Q`) and the off-class branches' values are action-invariant on
  positive cells (`ClassInert P 𝒞 Q`), then
  `EU Q a − EU Q b = ∑_{T ∈ 𝒞} μ(state = T | pp·Q = a) · (condEU T Q a − condEU T Q b)`.
  It generalises `udt-bli-core`'s `branchCut` (`𝒞 = {Q}`, `classCut_singleton`) and is the one
  lemma every verdict of this package is composed from: SIST (`𝒞 = Ask ∪ Rec`), the CM/PH case
  (`𝒞 = 𝒟_CM`), FIST (`𝒞` = the tables reached from an `X`-table) and the two-step crux (`𝒞` =
  the `Σ`-class). Its N− is the mugging with `𝒞 = {Ask}` (`Mugging.not_classInert_ask`).
* **Why the weight clause has no class index** (a finding, F1 of the report): for the off-class
  terms `branchProb T Q a · condEU T Q a − branchProb T Q b · condEU T Q b` to vanish, *every*
  branch weight must be action-invariant, not only the in-class ones; the mandate's
  `ClassReflective P 𝒞 Q̂` is therefore the class-free `ReflectiveAt P Q̂`.
* **Class quantities**: `classMass`, `classProb` (the class's weight under a point), `classEU`
  (the value conditioned on the point *and* the class), with the unconditional identity
  `classProb · classEU = ∑_{T ∈ 𝒞} branchProb · condEU` (`classProb_mul_classEU`).
* **The two-step objects** of bli-soto-b-023 in finite form: `agreesOn Σ Q T` (`T` agrees with
  `Q` on the sentences of `Σ`), the `Σ`-class `sigmaClass Σ Q`, the two-step value
  `twoStepEU P Σ Q a := 𝔼[U | pp·Q = a ∧ agreesOn Σ Q (state)]` (**junk `0` when the `Σ`-class
  under `a` is null** — every theorem guards it), `IsTwoStepChoice`.
* **The term reading** of the policy point (`IsTermChoice`): `A(Q_m) = a` with `Q_m` a term for
  the unknown actual state is, as an event, "whatever state obtains, the action is `a`", i.e.
  `pp ω = const a`; the rule compares `exAnteValue (const ·)`. ATTRIBUTION-UNVETTED as Soto's
  intent (it is the reading bli-soto-a-090 argues against).
* **Correlation of two points** (`condPoint`, `pointCorr`): `μ(pp·T = give | pp·Q = a)` and
  `δ_Q(T) := μ(T = give | Q = give) − μ(T = give | Q = refuse)`, the bracket of bli-soto-b-2-006;
  the profiles `ρ̄` are class averages of `δ` (`classProfile`).
* **`HUnif`, `HPoint`** (bli-soto-a-2-013): properties of a prior, never fields.

Sources: bli-soto-a-019 (the branch-cutting lemma); bli-soto-b-023 / bli-soto-a-075 (two-step);
bli-soto-b-2-006 (the correlation bracket); bli-soto-a-2-013 (`H_unif`/`H_point`); mandate §3.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-! ## Class quantities -/

/-- `μ(state ∈ 𝒞)`: the prior mass of a class of tables.
Source: mandate §3.2 (`μ(Ask) := ∑_{T, Ask T} stateMass T`)
Kind: D
Fidelity: exact -/
def classMass (𝒞 : Finset ↥𝒟) : ℚ := ∑ T ∈ 𝒞, P.stateMass T

/-- `μ(state ∈ 𝒞 | pp·Q = a)`: the class's weight under the policy point, as the sum of the branch
probabilities (junk `0` at a null point).
Source: mandate T1 (`classProb`)
Kind: D
Fidelity: exact -/
def classProb (𝒞 : Finset ↥𝒟) (Q : ↥𝒟) (a : A) : ℚ := ∑ T ∈ 𝒞, P.branchProb T Q a

/-- **The class-conditional value** `classEU 𝒞 Q a := 𝔼[U | pp·Q = a ∧ state ∈ 𝒞]`: the value of
the point `a` at `Q` *given also* that the obtaining table lies in `𝒞`. Junk `0` when the class
is null under the point. The two-step value is this with `𝒞` the `Σ`-class (`twoStepEU_eq_classEU`).
Source: bli-soto-b-023 (the conditional with `σ(Σ, Q)` added); mandate T1
Kind: D
Fidelity: exact -/
def classEU (𝒞 : Finset ↥𝒟) (Q : ↥𝒟) (a : A) : ℚ :=
  condExp P.μ P.U (fun ω => P.pp ω Q = a ∧ P.state ω ∈ 𝒞)

/-- **Reflective at a point**: no action at `Q` moves any branch weight,
`μ(state = T | pp·Q = a) = μ(state = T | pp·Q = b)` for all `T, a, b`. This is the weight
clause of the class-cut; it carries no class index (see the module docstring and report F1) —
the mandate's `ClassReflective P 𝒞 Q̂` is this predicate. It is the point-`Q` instance of
`udt-bli-core`'s `Reflective` without pinning the weight to `stateMass` (`reflectiveAt_of_reflective`).
Source: bli-soto-a-071 (`C(n,m)`'s branch clause: "does not modify the relative probabilities");
bli-soto-a-019; mandate T1
Kind: D
Fidelity: exact (the junk convention: at a null point both sides are `0`) -/
def ReflectiveAt (Q : ↥𝒟) : Prop :=
  ∀ (T : ↥𝒟) (a b : A), P.branchProb T Q a = P.branchProb T Q b

/-- **Class inertness**: outside the class `𝒞`, the value a branch expects does not depend on the
action at `Q`, on positive cells (`T ∉ 𝒞 → 0 < jointMass T Q a → 0 < jointMass T Q b →
condEU T Q a = condEU T Q b`). This is `C(n,m)`'s utility clause relative to a class; with
`𝒞 = {Q}` it is `NoCrossBranch` at `Q`.
Source: bli-soto-a-071 (`C(n,m)`'s utility clause); bli-soto-a-2-015 (inertness of the PH
tables); mandate T1
Kind: D
Fidelity: exact -/
def ClassInert (𝒞 : Finset ↥𝒟) (Q : ↥𝒟) : Prop :=
  ∀ T ∉ 𝒞, ∀ a b : A, 0 < P.jointMass T Q a → 0 < P.jointMass T Q b →
    P.condEU T Q a = P.condEU T Q b

/-- `Reflective` (every point, weight pinned to `stateMass`) implies `ReflectiveAt Q` at every
point of positive mass under every action; the two junk cases are handled separately.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma reflectiveAt_of_reflective (hR : P.Reflective) (Q : ↥𝒟) (hQ : ∀ a, 0 < P.ppMass Q a) :
    ReflectiveAt P Q := by
  intro T a b
  rw [hR T Q a (hQ a), hR T Q b (hQ b)]

/-- `NoCrossBranch` implies `ClassInert {Q} Q` at every `Q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma classInert_singleton_of_noCrossBranch (hN : P.NoCrossBranch) (Q : ↥𝒟) :
    ClassInert P {Q} Q := by
  intro T hT a b ha hb
  exact hN Q T a b (by simpa using hT) ha hb

/-! ## The class-cut -/

/-- A null cell has branch probability `0` (restated from `udt-bli-core`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma branchProb_eq_zero_of_jointMass_eq_zero' {T Q : ↥𝒟} {a : A} (h : P.jointMass T Q a = 0) :
    P.branchProb T Q a = 0 := P.branchProb_eq_zero_of_jointMass_eq_zero h

/-- **The class-cut** (Kind C, the lemma the package is composed from): if no action at `Q` moves
any branch weight and the branches outside `𝒞` are inert, then
`EU Q a − EU Q b = ∑_{T ∈ 𝒞} μ(state = T | pp·Q = a) · (condEU T Q a − condEU T Q b)`.
Holds with the junk conventions (a null cell contributes `0` on both sides). With `𝒞 = {Q}` it
is `udt-bli-core`'s `branchCut` (`classCut_singleton`); with `𝒞 = Ask ∪ Rec` it is Abram's
`//////` decomposition (bli-soto-a-077), with `𝒞 = 𝒟_CM` the CM/PH case (bli-soto-a-2-015), with
`𝒞` the `Σ`-class the two-step crux (`Crux.lean`).
Source: bli-soto-a-019 (Notion 508–511, "we can ignore any branch whose conditional expectation,
and relative branch weight, is the same given each alternative action"); bli-soto-a-077;
mandate §3.1
Kind: C (`EU_eq_sum_branch` twice, the off-class sum killed term by term with the junk cases)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem classCut (𝒞 : Finset ↥𝒟) (Q : ↥𝒟) (a b : A)
    (hbp : ∀ T, P.branchProb T Q a = P.branchProb T Q b)
    (hin : ∀ T ∉ 𝒞, 0 < P.jointMass T Q a → 0 < P.jointMass T Q b →
      P.condEU T Q a = P.condEU T Q b) :
    P.EU Q a - P.EU Q b = ∑ T ∈ 𝒞, P.branchProb T Q a * (P.condEU T Q a - P.condEU T Q b) := by
  rw [P.EU_eq_sum_branch Q a, P.EU_eq_sum_branch Q b, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_sum_compl 𝒞]
  have hoff : ∑ T ∈ 𝒞ᶜ, (P.branchProb T Q a * P.condEU T Q a -
      P.branchProb T Q b * P.condEU T Q b) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    have hT' : T ∉ 𝒞 := Finset.mem_compl.mp hT
    by_cases ha : 0 < P.jointMass T Q a
    · by_cases hb : 0 < P.jointMass T Q b
      · rw [hin T hT' ha hb, hbp T, sub_self]
      · have hzb : P.jointMass T Q b = 0 :=
          le_antisymm (not_lt.mp hb) (P.jointMass_nonneg T Q b)
        rw [hbp T, P.branchProb_eq_zero_of_jointMass_eq_zero hzb, zero_mul, zero_mul, sub_self]
    · have hza : P.jointMass T Q a = 0 :=
        le_antisymm (not_lt.mp ha) (P.jointMass_nonneg T Q a)
      rw [← hbp T, P.branchProb_eq_zero_of_jointMass_eq_zero hza, zero_mul, zero_mul, sub_self]
  rw [hoff, add_zero]
  apply Finset.sum_congr rfl
  intro T _
  rw [hbp T]
  ring

/-- **The class-cut under the named predicates**: `ReflectiveAt P Q ∧ ClassInert P 𝒞 Q` give the
class-cut identity at `Q` for every pair of actions.
Source: mandate §3.1
Kind: C
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem classCut_of (𝒞 : Finset ↥𝒟) (Q : ↥𝒟) (hR : ReflectiveAt P Q) (hI : ClassInert P 𝒞 Q)
    (a b : A) :
    P.EU Q a - P.EU Q b = ∑ T ∈ 𝒞, P.branchProb T Q a * (P.condEU T Q a - P.condEU T Q b) :=
  classCut P 𝒞 Q a b (fun T => hR T a b) (fun T hT => hI T hT a b)

/-- **`𝒞 = {Q}` is `branchCut`**: the class-cut with the singleton class is the home-branch
identity of `udt-bli-core` (its right-hand side is `branchProb Q Q a · (homeEU Q a − homeEU Q b)`).
Source: bli-soto-a-019; mandate §3.1 ("it generalizes `branchCut`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem classCut_singleton (Q : ↥𝒟) (a b : A)
    (hbp : ∀ T, P.branchProb T Q a = P.branchProb T Q b)
    (hcross : ∀ T, T ≠ Q → 0 < P.jointMass T Q a → 0 < P.jointMass T Q b →
      P.condEU T Q a = P.condEU T Q b) :
    P.EU Q a - P.EU Q b = P.branchProb Q Q a * (P.homeEU Q a - P.homeEU Q b) := by
  rw [classCut P {Q} Q a b hbp (fun T hT => hcross T (by simpa using hT)), Finset.sum_singleton]
  rfl

/-! ## Class decompositions -/

/-- The mass of "`pp·Q = a` and the state is in `𝒞`" is the sum of the class's joint masses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_class (𝒞 : Finset ↥𝒟) (Q : ↥𝒟) (a : A) :
    massOf P.μ (fun ω => P.pp ω Q = a ∧ P.state ω ∈ 𝒞) = ∑ T ∈ 𝒞, P.jointMass T Q a := by
  rw [massOf_fiberwise P.μ _ P.state]
  rw [← Finset.sum_add_sum_compl 𝒞]
  have h0 : ∑ T ∈ 𝒞ᶜ, massOf P.μ (fun ω => (P.pp ω Q = a ∧ P.state ω ∈ 𝒞) ∧ P.state ω = T) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    have hT' : T ∉ 𝒞 := Finset.mem_compl.mp hT
    unfold massOf
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    rintro ⟨⟨_, hmem⟩, hst⟩
    exact hT' (hst ▸ hmem)
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro T hT
  unfold FiniteBLIPrior.jointMass
  apply massOf_congr
  intro ω
  constructor
  · rintro ⟨⟨hp, _⟩, hst⟩; exact ⟨hst, hp⟩
  · rintro ⟨hst, hp⟩; exact ⟨⟨hp, hst ▸ hT⟩, hst⟩

/-- The integral of `U` over "`pp·Q = a` and the state is in `𝒞`" is the sum of the class's joint
utilities.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_class (𝒞 : Finset ↥𝒟) (Q : ↥𝒟) (a : A) :
    integralOf P.μ P.U (fun ω => P.pp ω Q = a ∧ P.state ω ∈ 𝒞) = ∑ T ∈ 𝒞, P.jointUtil T Q a := by
  rw [integralOf_fiberwise P.μ P.U _ P.state]
  rw [← Finset.sum_add_sum_compl 𝒞]
  have h0 : ∑ T ∈ 𝒞ᶜ, integralOf P.μ P.U
      (fun ω => (P.pp ω Q = a ∧ P.state ω ∈ 𝒞) ∧ P.state ω = T) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    have hT' : T ∉ 𝒞 := Finset.mem_compl.mp hT
    unfold integralOf
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    rintro ⟨⟨_, hmem⟩, hst⟩
    exact hT' (hst ▸ hmem)
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro T hT
  unfold FiniteBLIPrior.jointUtil
  apply integralOf_congr
  intro ω
  constructor
  · rintro ⟨⟨hp, _⟩, hst⟩; exact ⟨hst, hp⟩
  · rintro ⟨hst, hp⟩; exact ⟨⟨hp, hst ▸ hT⟩, hst⟩

/-- `classProb 𝒞 Q a · ppMass Q a = ∑_{T ∈ 𝒞} jointMass T Q a` (also at a null point).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma classProb_mul_ppMass (𝒞 : Finset ↥𝒟) (Q : ↥𝒟) (a : A) :
    classProb P 𝒞 Q a * P.ppMass Q a = ∑ T ∈ 𝒞, P.jointMass T Q a := by
  unfold classProb FiniteBLIPrior.branchProb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : P.ppMass Q a = 0
  · have hz : P.jointMass T Q a = 0 :=
      le_antisymm (h ▸ P.jointMass_le_ppMass T Q a) (P.jointMass_nonneg T Q a)
    rw [h, hz, mul_zero]
  · exact div_mul_cancel₀ _ h

/-- **The class-conditional value times the class weight is the class's branch sum**:
`classProb 𝒞 Q a · classEU 𝒞 Q a = ∑_{T ∈ 𝒞} branchProb T Q a · condEU T Q a`, unconditionally
(a null class or point gives `0` on both sides).
Source: bli-soto-a-2-012 (ii) (the law of total probability restricted to a class); mandate T1
Kind: L
Fidelity: exact -/
theorem classProb_mul_classEU (𝒞 : Finset ↥𝒟) (Q : ↥𝒟) (a : A) :
    classProb P 𝒞 Q a * classEU P 𝒞 Q a =
      ∑ T ∈ 𝒞, P.branchProb T Q a * P.condEU T Q a := by
  have hbr : ∀ T, P.branchProb T Q a * P.condEU T Q a = P.jointUtil T Q a / P.ppMass Q a := by
    intro T
    unfold FiniteBLIPrior.branchProb
    rw [div_mul_eq_mul_div, mul_comm, P.condEU_mul_jointMass]
  simp only [hbr, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  unfold classEU condExp
  simp only [div_eq_mul_inv]
  rw [massOf_class, integralOf_class]
  by_cases hM : ∑ T ∈ 𝒞, P.jointMass T Q a = 0
  · have hI : ∑ T ∈ 𝒞, P.jointUtil T Q a = 0 := by
      rw [← integralOf_class, integralOf_eq_zero_of_massOf_eq_zero P.μ P.U P.μ_nonneg _ (by
        rw [massOf_class]; exact hM)]
    rw [hI, hM, inv_zero, mul_zero, mul_zero, zero_mul]
  · have hcp : classProb P 𝒞 Q a = (∑ T ∈ 𝒞, P.jointMass T Q a) / P.ppMass Q a := by
      have hpp : P.ppMass Q a ≠ 0 := by
        intro h0
        apply hM
        apply Finset.sum_eq_zero
        intro T _
        exact le_antisymm (h0 ▸ P.jointMass_le_ppMass T Q a) (P.jointMass_nonneg T Q a)
      rw [eq_div_iff hpp, classProb_mul_ppMass]
    rw [hcp, div_eq_mul_inv]
    field_simp

/-! ## The two-step objects (bli-soto-b-023, finite form) -/

/-- `T` agrees with `Q` on every sentence of `Σ` (the finite `σ(Σ, Q)`: `⋀_{φ ∈ Σ} 𝐐_m(φ) = Q(φ)`).
Source: bli-soto-b-023 (`σ(Σ, Q)`); mandate T1
Kind: D
Fidelity: exact (the sentences of `Σ` are day-`m` small sentences; `Supp(Q)` is all of `𝒮.S m`) -/
def agreesOn (Sig : Finset ↥(𝒮.S m)) (Q T : ↥𝒟) : Prop := ∀ φ ∈ Sig, T.1 φ = Q.1 φ

/-- Agreement on a finite set of sentences is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance agreesOn.decidable (Sig : Finset ↥(𝒮.S m)) (Q : ↥𝒟) : DecidablePred (agreesOn Sig Q) :=
  fun T => inferInstanceAs (Decidable (∀ φ ∈ Sig, T.1 φ = Q.1 φ))

/-- **The `Σ`-class of `Q`**: the tables agreeing with `Q` on `Σ`.
Source: bli-soto-b-023; mandate T5
Kind: D
Fidelity: exact -/
def sigmaClass (Sig : Finset ↥(𝒮.S m)) (Q : ↥𝒟) : Finset ↥𝒟 := univ.filter (agreesOn Sig Q)

/-- `Q` is in its own `Σ`-class.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_sigmaClass_self (Sig : Finset ↥(𝒮.S m)) (Q : ↥𝒟) : Q ∈ sigmaClass Sig Q := by
  unfold sigmaClass
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun _ _ => rfl⟩

/-- Membership in the `Σ`-class.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_sigmaClass_iff (Sig : Finset ↥(𝒮.S m)) (Q T : ↥𝒟) :
    T ∈ sigmaClass Sig Q ↔ agreesOn Sig Q T := by
  unfold sigmaClass
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **The two-step value** `twoStepEU Σ Q a := 𝔼[U | pp·Q = a ∧ σ(Σ, Q)]`: the one-step value
with the `Σ`-class of the observed table added to the conditional (Soto's "act by
`argmax_a 𝔼(U | A(Q) = a ∧ σ(Σ, Q))`"). **Junk `0` when the `Σ`-class under `a` is null**; every
theorem about it names the positivity of that cell.
Source: bli-soto-b-023 (`Policy(Σ, Q)`); bli-soto-a-075; mandate T1
Kind: D
Fidelity: exact (finite `Σ`; the outer argmax over programs of bli-soto-b-023 is not modelled —
recorded as ill-posed in the findings) -/
def twoStepEU (Sig : Finset ↥(𝒮.S m)) (Q : ↥𝒟) (a : A) : ℚ :=
  condExp P.μ P.U (fun ω => P.pp ω Q = a ∧ agreesOn Sig Q (P.state ω))

/-- The two-step value is the class-conditional value at the `Σ`-class.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoStepEU_eq_classEU (Sig : Finset ↥(𝒮.S m)) (Q : ↥𝒟) (a : A) :
    twoStepEU P Sig Q a = classEU P (sigmaClass Sig Q) Q a := by
  unfold twoStepEU classEU
  apply condExp_congr
  intro ω
  rw [mem_sigmaClass_iff]

/-- **Two-step choice**: `a` maximizes `twoStepEU Σ Q ·` (ties allowed). Honest scope: the
`Σ`-class positive under every action.
Source: bli-soto-b-023; mandate T1
Kind: D
Fidelity: exact (predicate in place of an argmax function) -/
def IsTwoStepChoice (Sig : Finset ↥(𝒮.S m)) (Q : ↥𝒟) (a : A) : Prop :=
  ∀ b, twoStepEU P Sig Q b ≤ twoStepEU P Sig Q a

/-- `Σ = ∅`: the two-step value is the one-step value (nothing is added to the conditional).
Source: bli-soto-b-2-008 ("one-step" = nothing else in the conditional)
Kind: L
Fidelity: exact -/
lemma twoStepEU_empty (Q : ↥𝒟) (a : A) : twoStepEU P ∅ Q a = P.EU Q a := by
  unfold twoStepEU FiniteBLIPrior.EU
  apply condExp_congr
  intro ω
  simp [agreesOn]

/-! ## The term reading of the policy point -/

/-- The constant policy `fun _ => a`.
Source: mandate §3.3
Kind: D
Fidelity: n/a -/
def constPolicy (a : A) : Policy 𝒟 A := fun _ => a

/-- **The term-reading rule**: with `A(Q_m) = a` read as "whatever state obtains, the action is
`a`" (the event `pp ω = const a`), the rule compares the ex-ante values of the constant policies.
Honest scope: `0 < policyMass (constPolicy b)` for every `b`. ATTRIBUTION-UNVETTED as Soto's
intended reading; it is the reading bli-soto-a-090 argues against and the one under which
bli-soto-a-089's "one tenth" calculation is correct (`Homework.lean`).
Source: bli-soto-a-089/090; mandate §3.3
Kind: D
Fidelity: variant: the term `Q_m` is rendered as the event "the action is `a` in the actual
state", i.e. the constant policy (disclosed) -/
def IsTermChoice (a : A) : Prop :=
  ∀ b, P.exAnteValue (constPolicy b) ≤ P.exAnteValue (constPolicy a)

/-! ## Correlation of policy points (bli-soto-b-2-006) -/

/-- `μ(pp·T = b | pp·Q = a)`: the within-prior conditional probability of one point given another
(junk `0` at a null point `pp·Q = a`).
Source: bli-soto-b-2-006 (`P(A_j = give | A_i = give)`); bli-soto-b-2-015 (the within-table
conditionals); mandate §3.4
Kind: D
Fidelity: exact -/
def condPoint (T Q : ↥𝒟) (b a : A) : ℚ := P.pairMass T Q b a / P.ppMass Q a

/-- **The correlation bracket** `δ_Q(T) := μ(pp·T = give | pp·Q = give) − μ(pp·T = give | pp·Q = refuse)`
of bli-soto-b-2-006: how much conditioning on the point at `Q` moves the point at `T`. `δ_Q(Q) = 1`
at a positive point; `δ = 0` for independent points; `δ = 1` under `HUnif`.
Source: bli-soto-b-2-006 (the bracket `[P(A_j = give | A_i = give) − P(A_j = give | A_i = refuse)]`)
Kind: D
Fidelity: exact -/
def pointCorr (Q T : ↥𝒟) (give refuse : A) : ℚ :=
  condPoint P T Q give give - condPoint P T Q give refuse

/-- **The class profile** `ρ̄_𝒜(Q) := ∑_{T ∈ 𝒜} μ(state = T) · δ_Q(T) / μ(𝒜)`: the class-weighted
average of the correlation bracket (junk `0` for a null class).
Source: bli-soto-b-2-006 (`∑_j P(J = j)·[…]`, with the class weights in place of Omega's `J`);
mandate §3.4 (`ρ̄_i`)
Kind: D
Fidelity: exact -/
def classProfile (𝒜 : Finset ↥𝒟) (Q : ↥𝒟) (give refuse : A) : ℚ :=
  (∑ T ∈ 𝒜, P.stateMass T * pointCorr P Q T give refuse) / classMass P 𝒜

/-- `pairMass T T a b = [a = b] · ppMass T a`: a point paired with itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairMass_self (T : ↥𝒟) (a b : A) :
    P.pairMass T T a b = if a = b then P.ppMass T a else 0 := by
  unfold FiniteBLIPrior.pairMass FiniteBLIPrior.ppMass
  by_cases h : a = b
  · subst h
    rw [if_pos rfl]
    apply massOf_congr
    intro ω
    simp
  · rw [if_neg h]
    unfold massOf
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (h1.symm.trans h2)

/-- `δ_Q(Q) = 1` at a point positive under both actions.
Source: bli-soto-b-2-006 ("the `j = i` term is `1`")
Kind: L
Fidelity: exact -/
lemma pointCorr_self (Q : ↥𝒟) (give refuse : A) (hne : give ≠ refuse)
    (hg : 0 < P.ppMass Q give) (_hr : 0 < P.ppMass Q refuse) :
    pointCorr P Q Q give refuse = 1 := by
  unfold pointCorr condPoint
  rw [pairMass_self, pairMass_self, if_pos rfl, if_neg hne, div_self (ne_of_gt hg), zero_div,
    sub_zero]

/-! ## `H_unif` and `H_point` (bli-soto-a-2-013) -/

/-- **`H_unif`** ("the 100 % correlated picture"): on every world of positive mass, the policy
takes the same value at every table of the class `𝒜` as at `Q`. A property of the prior's policy
law, never a hypothesis of a general verdict (mandate §3.4; Abram: acknowledged unrealistic,
journal ll. 326, 620).
Source: bli-soto-a-2-013 (i) (`H_unif`); bli-soto-a-077 ("the 100% correlated picture")
Kind: D
Fidelity: exact (finite: a.s. constancy on the class) -/
def HUnif (𝒜 : ↥𝒟 → Prop) (Q : ↥𝒟) : Prop :=
  ∀ ω, 0 < P.μ ω → ∀ T, 𝒜 T → P.pp ω T = P.pp ω Q

/-- **`H_point`**: the only table of the class `𝒜` with positive mass is `Q` — "the" ask branch
is the observed one.
Source: bli-soto-a-2-013 (i) (`H_point : P(Q_m = Q̂ | Ask(Q_m)) = 1`)
Kind: D
Fidelity: exact -/
def HPoint (𝒜 : ↥𝒟 → Prop) (Q : ↥𝒟) : Prop := ∀ T, 𝒜 T → T ≠ Q → P.stateMass T = 0

/-- Under `HUnif`, a class table's point is paired with `Q`'s as `Q`'s own:
`pairMass T Q b a = [b = a] · ppMass Q a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairMass_of_hUnif {𝒜 : ↥𝒟 → Prop} {Q : ↥𝒟} (h : HUnif P 𝒜 Q) {T : ↥𝒟} (hT : 𝒜 T)
    (b a : A) : P.pairMass T Q b a = if b = a then P.ppMass Q a else 0 := by
  unfold FiniteBLIPrior.pairMass FiniteBLIPrior.ppMass massOf
  by_cases hba : b = a
  · subst hba
    rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hμ : 0 < P.μ ω
    · have e := h ω hμ T hT
      simp only [e, and_self]
    · have hz : P.μ ω = 0 := le_antisymm (not_lt.mp hμ) (P.μ_nonneg ω)
      simp [hz]
  · rw [if_neg hba]
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hμ : 0 < P.μ ω
    · have e := h ω hμ T hT
      simp only [e]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hba (h1.symm.trans h2)
    · have hz : P.μ ω = 0 := le_antisymm (not_lt.mp hμ) (P.μ_nonneg ω)
      simp [hz]

/-- **Under `HUnif` the bracket is `1` on the class**: `δ_Q(T) = 1` for every `T ∈ 𝒜` at a point
positive under both actions.
Source: bli-soto-a-2-013; mandate §3.4 ("`ρ̄ = 1` under `H_unif`")
Kind: L
Fidelity: exact -/
lemma pointCorr_of_hUnif {𝒜 : ↥𝒟 → Prop} {Q : ↥𝒟} (h : HUnif P 𝒜 Q) {T : ↥𝒟} (hT : 𝒜 T)
    (give refuse : A) (hne : give ≠ refuse) (hg : 0 < P.ppMass Q give)
    (_hr : 0 < P.ppMass Q refuse) : pointCorr P Q T give refuse = 1 := by
  unfold pointCorr condPoint
  rw [pairMass_of_hUnif P h hT, pairMass_of_hUnif P h hT, if_pos rfl, if_neg hne,
    div_self (ne_of_gt hg), zero_div, sub_zero]

/-- **Under `IndependentPoints` the bracket is `0` off `Q`**: `δ_Q(T) = 0` for `T ≠ Q` at a point
positive under both actions.
Source: bli-soto-b-2-006 ("if they're all independent … a tiny influence")
Kind: L
Fidelity: exact -/
lemma pointCorr_of_independentPoints (hI : P.IndependentPoints) {Q T : ↥𝒟} (hne : T ≠ Q)
    (give refuse : A) (hg : 0 < P.ppMass Q give) (hr : 0 < P.ppMass Q refuse) :
    pointCorr P Q T give refuse = 0 := by
  unfold pointCorr condPoint
  rw [hI T Q give give hne, hI T Q give refuse hne, mul_div_assoc, mul_div_assoc,
    div_self (ne_of_gt hg), div_self (ne_of_gt hr), sub_self]

/-! ## The N− of the class-cut: the mugging with `𝒞 = {Ask}` -/

namespace Mugging

open Cleanroom.Bli.UdtBliCore.Mugging

variable (r : Bool → ℚ)

/-- **`ClassInert {Ask} Ask` fails on the mugging prior**: the `Rec` branch's value of the `Ask`
point moves by `100` with the point (this is `Mugging.not_noCrossBranch` read through the class
predicate). So the class-cut with `𝒞 = {Ask}` does not apply there, as the verdict requires.
Source: [[bli-program]] §3.9 U5; §7 item 9; mandate §3.1 ("its N− is the mugging with `𝒞 = {Ask}`")
Kind: N−
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem not_classInert_ask : ¬ ClassInert (muggingPrior r) {askT} askT := by
  intro h
  have hrec : recT ∉ ({askT} : Finset ↥mugTables) := by
    simp only [Finset.mem_singleton]
    exact askT_ne_recT.symm
  have := h recT hrec true false (jointMass_pos r 1 askT true) (jointMass_pos r 1 askT false)
  rw [condEU_rec_ask, condEU_rec_ask] at this
  norm_num at this

/-- **`ReflectiveAt Ask` holds on the mugging prior** (independent points): the whole separation
of the two rules there is cross-branch utility, which the class `{Ask, Rec}` captures and the
class `{Ask}` does not.
Source: mandate T3 (the mugging is `Reflective`)
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem reflectiveAt_ask : ReflectiveAt (muggingPrior r) askT :=
  reflectiveAt_of_reflective _ (reflective r) askT (fun a => ndpol r askT a)

end Mugging

end Cleanroom.Bli.UdtBliSist
