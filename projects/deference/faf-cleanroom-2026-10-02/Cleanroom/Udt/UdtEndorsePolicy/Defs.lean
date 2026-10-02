import Cleanroom.Udt.UdtPolicyCalc.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Endorsement: the six definitions of record (finite, division-free)

Package `udt-endorse-policy` (faf-cleanroom run, 2026-09-30), namespace
`Cleanroom.Udt.UdtEndorsePolicy`. Source: [[meaning-and-agency-reference]] §Endorsement,
§Expectation/Selection/Control Endorsement, §"Absolute" Endorsement, §Conditional Endorsement
(Abram's post, verbatim); udt-rep-2-012.

**Representation of record** ([[udt-endorse-policy-mandate]] §Representation).

* The observer `P₁` is a weight function `w : Ω → ℝ` on a finite `Ω` (`udt-policy-calc`'s
  `FinDist` supplies `μ.w`; theorems take `hw : ∀ ω, 0 ≤ w ω` where they need it). Events are
  `Finset Ω`; `mass w E = ∑ ω ∈ E, w ω` is `udt-policy-calc`'s.
* **A second agent is never a separate probability space.** It enters only through its
  *reports*, random variables on `Ω`: a belief report `Q : Ω → ℝ` (the post's `"P₂(X)"`), an
  expectation report `Q : Ω → ℝ` (the post's `"E_{P₂}(V)"`), a choice `C : Ω → A`. This is the
  post's own convention: "The quotation marks are communicating a translation into P₁'s event
  algebra" (§Endorsement). Fidelity `exact` on this point.
* **Every predicate quantifies over report values of positive mass and is division-free**
  (multiplicative form): belief endorsement reads `P(X ∩ {Q = p}) = p · P(Q = p)` for every
  `p` with `P(Q = p) > 0`, vacuous at null values — the post's `P₁(X | "P₂(X) = p") = p` needs
  the guard the post omits (udt-rep-2-012). The division forms are lemmas
  (`beliefEndorses_iff_condProb`, `expectationEndorses_iff_condExp`,
  `controlEndorses_iff_condExp`), never definitions.
* **Argmax is set-valued**: `IsArgmax f a` (`∀ a', f a' ≤ f a`) from `udt-policy-calc`; the
  post's `C(A | …) = a` is read as `a ∈ argmax` (udt-rep-2-012's tie fix, ATTRIBUTION-UNVETTED).
  Where a source needs uniqueness, `IsStrictArgmax` is used explicitly.
* No FAF object is involved; the package is Mathlib-only finite probability.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Finset

noncomputable section

variable {Ω : Type}

/-! ### Weighted sums, value classes, indicators -/

/-- The weighted sum `∑ ω ∈ E, w ω * f ω` (the unnormalized conditional expectation of `f` on
`E`; `condExpJunk w f E j = wsum w f E / mass w E` on positive `E`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def wsum (w f : Ω → ℝ) (E : Finset Ω) : ℝ := ∑ ω ∈ E, w ω * f ω

/-- The value class `{ω | Q ω = p}` of a report `Q` (the event `"P₂(X) = p"` in `P₁`'s algebra).
Source: [[meaning-and-agency-reference]] §Endorsement (the quotation marks)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev cls [Fintype Ω] {T : Type} [DecidableEq T] (Q : Ω → T) (p : T) : Finset Ω :=
  event fun ω => Q ω = p

/-- The pair class `{ω | V ω = x ∧ W ω = y}` (the post's `X ∧ Y` in §Conditional Endorsement).
Source: [[meaning-and-agency-reference]] §Conditional Endorsement
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev cls2 [Fintype Ω] {T T' : Type} [DecidableEq T] [DecidableEq T'] (V : Ω → T) (x : T)
    (W : Ω → T') (y : T') : Finset Ω :=
  event fun ω => V ω = x ∧ W ω = y

/-- The real indicator `1_X` of a finite event.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ind [DecidableEq Ω] (X : Finset Ω) (ω : Ω) : ℝ := if ω ∈ X then 1 else 0

/-! ### The six definitions of record -/

section Definitions

variable [Fintype Ω] [DecidableEq Ω]

/-- **Belief endorsement** (M&A: "`P₁(X | "P₂(X) = p") = p`"): for every report value `p` of
positive mass, `P(X ∩ {Q = p}) = p · P(Q = p)`. Vacuous at null values, which is the positivity
guard the post omits (udt-rep-2-012); the division form is `beliefEndorses_iff_condProb`.
Source: [[meaning-and-agency-reference]] §Endorsement | udt-rep-2-012
Kind: D
Fidelity: exact: the report `Q` is `"P₂(X)"` translated into `P₁`'s algebra (the post's quotation marks); positive-mass guard added
Scope: finite `Ω`, positive-mass conditioning only (multiplicative form); FAF-free
Hyps: n/a -/
def BeliefEndorses (w : Ω → ℝ) (X : Finset Ω) (Q : Ω → ℝ) : Prop :=
  ∀ p : ℝ, 0 < mass w (cls Q p) → mass w (X ∩ cls Q p) = p * mass w (cls Q p)

/-- **Expectation endorsement** (M&A: "`E_{ω∼P₁}(V(ω) | "E_{ω∼P₂}(V(ω)) = x") = x`"): for every
report value `x` of positive mass, `∑_{Q = x} w · V = x · P(Q = x)`.
Source: [[meaning-and-agency-reference]] §Expectation Endorsement | udt-rep-2-012
Kind: D
Fidelity: exact (multiplicative form; report as a random variable; positive-mass guard added)
Scope: finite `Ω`, positive-mass conditioning only; FAF-free
Hyps: n/a -/
def ExpectationEndorses (w : Ω → ℝ) (V Q : Ω → ℝ) : Prop :=
  ∀ x : ℝ, 0 < mass w (cls Q x) → wsum w V (cls Q x) = x * mass w (cls Q x)

/-- **Selection endorsement** (M&A: "`C¹_{U₂,P₁}(A | "C²_{U₂,P₂}(A) = a") = a`" with a pure
`U : A → ℝ`): every realized choice `a` (positive mass of `{C = a}`) is an argmax of `U`. With a
pure utility the conditioning is inert, so the observer's choice given the report is just an
argmax of `U`; `= a` is read as `a ∈ argmax` (ties allowed, ATTRIBUTION-UNVETTED).
Source: [[meaning-and-agency-reference]] §Selection Endorsement | udt-rep-2-012
Kind: D
Fidelity: exact under the set-valued reading of `argmax`
Scope: finite `Ω`, finite `A`, positive-mass guard; FAF-free
Hyps: n/a -/
def SelectionEndorses {A : Type} [DecidableEq A] (w : Ω → ℝ) (U : A → ℝ) (C : Ω → A) : Prop :=
  ∀ a, 0 < mass w (cls C a) → IsArgmax U a

/-- **Control endorsement** (M&A: the same formula with an impure `U : Ω × A → ℝ`): every
realized choice `a` is an argmax of the conditional expected utility
`a' ↦ E[U(·, a') | C = a]`, written division-free as `a' ↦ ∑_{C = a} w · U(·, a')` (a positive
constant factor does not move the argmax: `controlEndorses_iff_condExp`).
"Control endorsement is the notion of intentional stance that I have been driving towards."
Source: [[meaning-and-agency-reference]] §Control Endorsement | udt-rep-2-012
Kind: D
Fidelity: exact under the set-valued reading of `argmax` (ATTRIBUTION-UNVETTED); report as a random variable
Scope: finite `Ω`, finite `A`, positive-mass guard; FAF-free
Hyps: n/a -/
def ControlEndorses {A : Type} [DecidableEq A] (w : Ω → ℝ) (U : Ω → A → ℝ) (C : Ω → A) :
    Prop :=
  ∀ a, 0 < mass w (cls C a) → IsArgmax (fun a' => wsum w (fun ω => U ω a') (cls C a)) a

/-- **"Absolute" endorsement** (M&A: "control endorsement where `U₂` is the utility function of
the observer whose beliefs are `P₁`"): a parameter choice, not a new relation — `ControlEndorses`
with `U` read as the observer's own utility. Kept as an abbreviation so the reading is on record.
Source: [[meaning-and-agency-reference]] §"Absolute" Endorsement
Kind: D
Fidelity: exact (definitional abbreviation)
Hyps: n/a -/
abbrev AbsoluteEndorses {A : Type} [DecidableEq A] (w : Ω → ℝ) (U₁ : Ω → A → ℝ) (C : Ω → A) :
    Prop :=
  ControlEndorses w U₁ C

/-- **Conditional (control) endorsement** (M&A: "`P₁` endorses `W` given `V` iff
`argmax_{v∈A} E_{ω∼P₁|X∧Y} U(ω,v) = y`, where `X` is the event `V = x` and `Y` is the event
`W = y`"): for every realized pair `(x, y)`, `y` is an argmax of `v ↦ ∑_{V = x, W = y} w · U(·, v)`.
Source: [[meaning-and-agency-reference]] §Conditional Endorsement | udt-rep-2-015
Kind: D
Fidelity: exact under the set-valued `argmax` and the positive-mass guard (ATTRIBUTION-UNVETTED)
Scope: finite `Ω`, finite `A`; FAF-free
Hyps: n/a -/
def CondControlEndorses {A T : Type} [DecidableEq A] [DecidableEq T] (w : Ω → ℝ)
    (U : Ω → A → ℝ) (V : Ω → T) (W : Ω → A) : Prop :=
  ∀ x y, 0 < mass w (cls2 V x W y) →
    IsArgmax (fun v => wsum w (fun ω => U ω v) (cls2 V x W y)) y

/-- **Conditional belief endorsement** (the belief form of §Conditional Endorsement; scout Q4):
`W` (a belief report about `X`) is endorsed given `V` iff for every realized pair `(x, y)`,
`P(X ∩ {V = x, W = y}) = y · P(V = x, W = y)`. Used by the transitivity question (T6).
Source: [[meaning-and-agency-reference]] §Conditional Endorsement, Q1 | udt-rep-2-015 | trust-lab-070
Kind: D
Fidelity: variant: belief form (the post states only the control form); positive-mass guard
Scope: finite `Ω`; FAF-free
Hyps: n/a -/
def CondBeliefEndorses {T : Type} [DecidableEq T] (w : Ω → ℝ) (X : Finset Ω) (V : Ω → T)
    (W : Ω → ℝ) : Prop :=
  ∀ x y, 0 < mass w (cls2 V x W y) → mass w (X ∩ cls2 V x W y) = y * mass w (cls2 V x W y)

end Definitions

/-! ### Elementary lemmas on `mass`, `wsum`, `ind` -/

/-- Supporting lemma: on a null event of non-negative weight, every weight vanishes.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem weight_eq_zero_of_mass_eq_zero {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {E : Finset Ω}
    (h : mass w E = 0) : ∀ ω ∈ E, w ω = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun ω _ => hw ω).1 h

/-- Supporting lemma: `wsum` vanishes on a null event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_eq_zero_of_mass_eq_zero {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (f : Ω → ℝ) {E : Finset Ω}
    (h : mass w E = 0) : wsum w f E = 0 :=
  Finset.sum_eq_zero fun ω hω => by rw [weight_eq_zero_of_mass_eq_zero hw h ω hω, zero_mul]

/-- Supporting lemma: positive mass means a positive-weight point.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem exists_pos_of_mass_pos {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {E : Finset Ω}
    (h : 0 < mass w E) : ∃ ω ∈ E, 0 < w ω := by
  by_contra hcon
  have : mass w E = 0 := Finset.sum_eq_zero fun ω hω =>
    le_antisymm (not_lt.1 fun hlt => hcon ⟨ω, hω, hlt⟩) (hw ω)
  exact absurd this h.ne'

/-- Supporting lemma: a set of positive weight mass that is the whole class of `Q ω` (`w ω > 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_cls_pos [Fintype Ω] {T : Type} [DecidableEq T] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (Q : Ω → T)
    {ω : Ω} (hω : 0 < w ω) : 0 < mass w (cls Q (Q ω)) :=
  mass_pos_of_mem hw (by simp) hω

/-- Supporting lemma: positive pair-class mass at `(V ω, W ω)` for a positive-weight point.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_cls2_pos [Fintype Ω] {T T' : Type} [DecidableEq T] [DecidableEq T'] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (V : Ω → T) (W : Ω → T') {ω : Ω} (hω : 0 < w ω) :
    0 < mass w (cls2 V (V ω) W (W ω)) :=
  mass_pos_of_mem hw (by simp) hω

/-- Supporting lemma: `wsum` of a function constant on the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_const_on {w f : Ω → ℝ} {E : Finset Ω} {c : ℝ} (hc : ∀ ω ∈ E, f ω = c) :
    wsum w f E = c * mass w E := by
  rw [wsum, mass, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω hω => by rw [hc ω hω, mul_comm]

/-- Supporting lemma: the mass of `X ∩ E` is the weighted sum of `1_X` over `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_inter_eq_wsum_ind [DecidableEq Ω] (w : Ω → ℝ) (X E : Finset Ω) :
    mass w (X ∩ E) = wsum w (ind X) E := by
  unfold wsum ind mass
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.inter_comm]

/-- Supporting lemma: `wsum` is additive in the function.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_add (w f g : Ω → ℝ) (E : Finset Ω) :
    wsum w (fun ω => f ω + g ω) E = wsum w f E + wsum w g E := by
  simp only [wsum, mul_add, Finset.sum_add_distrib]

/-- Supporting lemma: `wsum` pulls out a scalar.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_smul (w f : Ω → ℝ) (c : ℝ) (E : Finset Ω) :
    wsum w (fun ω => c * f ω) E = c * wsum w f E := by
  simp only [wsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- Supporting lemma: `wsum` of the constant one is the mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_one (w : Ω → ℝ) (E : Finset Ω) : wsum w (fun _ => 1) E = mass w E := by
  simp [wsum, mass]

/-- Supporting lemma: `wsum` over a finset splits along the fibres of any map.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_fiberwise {T : Type} [DecidableEq T] (w f : Ω → ℝ) (E : Finset Ω) (V : Ω → T) :
    wsum w f E = ∑ x ∈ E.image V, wsum w f (E.filter fun ω => V ω = x) := by
  unfold wsum
  exact (Finset.sum_fiberwise_of_maps_to (fun ω hω => Finset.mem_image_of_mem V hω) _).symm

/-- Supporting lemma: the pair class is symmetric in its two conditions.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cls2_comm [Fintype Ω] {T T' : Type} [DecidableEq T] [DecidableEq T'] (V : Ω → T) (x : T)
    (W : Ω → T') (y : T') : cls2 V x W y = cls2 W y V x := by
  ext ω; simp [and_comm]

/-- Supporting lemma: a fibre of the value class of `V` inside `cls W y` is the pair class.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem filter_cls_eq_cls2 [Fintype Ω] {T T' : Type} [DecidableEq T] [DecidableEq T'] (V : Ω → T) (x : T)
    (W : Ω → T') (y : T') : (cls W y).filter (fun ω => V ω = x) = cls2 V x W y := by
  ext ω; simp [and_comm]

/-- **Class-wise agreement lifts to the whole event.** If two functions have the same weighted
sum on every positive-mass fibre of `V` inside `E`, they have the same weighted sum on `E`
(null fibres contribute zero on both sides).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_eq_of_fibres {T : Type} [DecidableEq T] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (f g : Ω → ℝ) (E : Finset Ω) (V : Ω → T)
    (h : ∀ x, 0 < mass w (E.filter fun ω => V ω = x) →
      wsum w f (E.filter fun ω => V ω = x) = wsum w g (E.filter fun ω => V ω = x)) :
    wsum w f E = wsum w g E := by
  rw [wsum_fiberwise w f E V, wsum_fiberwise w g E V]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases (mass_nonneg hw _).lt_or_eq with hpos | hzero
  · exact h x hpos
  · rw [wsum_eq_zero_of_mass_eq_zero hw f hzero.symm, wsum_eq_zero_of_mass_eq_zero hw g hzero.symm]

/-- **Class-wise inequality lifts to the whole event** (the inequality version of
`wsum_eq_of_fibres`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_le_of_fibres {T : Type} [DecidableEq T] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (f g : Ω → ℝ) (E : Finset Ω) (V : Ω → T)
    (h : ∀ x, 0 < mass w (E.filter fun ω => V ω = x) →
      wsum w f (E.filter fun ω => V ω = x) ≤ wsum w g (E.filter fun ω => V ω = x)) :
    wsum w f E ≤ wsum w g E := by
  rw [wsum_fiberwise w f E V, wsum_fiberwise w g E V]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases (mass_nonneg hw _).lt_or_eq with hpos | hzero
  · exact h x hpos
  · rw [wsum_eq_zero_of_mass_eq_zero hw f hzero.symm, wsum_eq_zero_of_mass_eq_zero hw g hzero.symm]

/-! ### The point forms (quantify over positive-weight points instead of report values) -/

section Forms

variable [Fintype Ω]

/-- **Belief endorsement, point form**: it suffices (and is necessary) to check the class of
each positive-weight point. This is how finite witnesses are verified.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem beliefEndorses_iff_forall_pt [DecidableEq Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Finset Ω)
    (Q : Ω → ℝ) : BeliefEndorses w X Q ↔
      ∀ ω, 0 < w ω → mass w (X ∩ cls Q (Q ω)) = Q ω * mass w (cls Q (Q ω)) := by
  constructor
  · intro h ω hω
    exact h (Q ω) (mass_cls_pos hw Q hω)
  · intro h p hp
    obtain ⟨ω, hωE, hω⟩ := exists_pos_of_mass_pos hw hp
    have : Q ω = p := by simpa using hωE
    rw [← this]
    exact h ω hω

/-- **Expectation endorsement, point form.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem expectationEndorses_iff_forall_pt {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (V Q : Ω → ℝ) :
    ExpectationEndorses w V Q ↔
      ∀ ω, 0 < w ω → wsum w V (cls Q (Q ω)) = Q ω * mass w (cls Q (Q ω)) := by
  constructor
  · intro h ω hω
    exact h (Q ω) (mass_cls_pos hw Q hω)
  · intro h x hx
    obtain ⟨ω, hωE, hω⟩ := exists_pos_of_mass_pos hw hx
    have : Q ω = x := by simpa using hωE
    rw [← this]
    exact h ω hω

/-- **Control endorsement, point form.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem controlEndorses_iff_forall_pt {A : Type} [DecidableEq A] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (U : Ω → A → ℝ) (C : Ω → A) :
    ControlEndorses w U C ↔
      ∀ ω, 0 < w ω → IsArgmax (fun a' => wsum w (fun ω' => U ω' a') (cls C (C ω))) (C ω) := by
  constructor
  · intro h ω hω
    exact h (C ω) (mass_cls_pos hw C hω)
  · intro h a ha
    obtain ⟨ω, hωE, hω⟩ := exists_pos_of_mass_pos hw ha
    have : C ω = a := by simpa using hωE
    rw [← this]
    exact h ω hω

/-- **Conditional belief endorsement, point form.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condBeliefEndorses_iff_forall_pt {T : Type} [DecidableEq T] [DecidableEq Ω] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (X : Finset Ω) (V : Ω → T) (W : Ω → ℝ) :
    CondBeliefEndorses w X V W ↔
      ∀ ω, 0 < w ω → mass w (X ∩ cls2 V (V ω) W (W ω)) =
        W ω * mass w (cls2 V (V ω) W (W ω)) := by
  constructor
  · intro h ω hω
    exact h (V ω) (W ω) (mass_cls2_pos hw V W hω)
  · intro h x y hxy
    obtain ⟨ω, hωE, hω⟩ := exists_pos_of_mass_pos hw hxy
    have hV : V ω = x := (by simpa using hωE : V ω = x ∧ W ω = y).1
    have hW : W ω = y := (by simpa using hωE : V ω = x ∧ W ω = y).2
    rw [← hV, ← hW]
    exact h ω hω

/-- **Conditional control endorsement, point form.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condControlEndorses_iff_forall_pt {A T : Type} [DecidableEq A] [DecidableEq T]
    {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (U : Ω → A → ℝ) (V : Ω → T) (W : Ω → A) :
    CondControlEndorses w U V W ↔
      ∀ ω, 0 < w ω →
        IsArgmax (fun v => wsum w (fun ω' => U ω' v) (cls2 V (V ω) W (W ω))) (W ω) := by
  constructor
  · intro h ω hω
    exact h (V ω) (W ω) (mass_cls2_pos hw V W hω)
  · intro h x y hxy
    obtain ⟨ω, hωE, hω⟩ := exists_pos_of_mass_pos hw hxy
    have hV : V ω = x := (by simpa using hωE : V ω = x ∧ W ω = y).1
    have hW : W ω = y := (by simpa using hωE : V ω = x ∧ W ω = y).2
    rw [← hV, ← hW]
    exact h ω hω

/-! ### The division forms (the sources' `P(X | Q = p) = p`) -/

/-- **Belief endorsement in the sources' division form**: `P(X | Q = p) = p` on every
positive-mass class, with `udt-policy-calc`'s `condProbJunk` (any junk value `j`).
Source: [[meaning-and-agency-reference]] §Endorsement
Kind: L
Fidelity: exact
Hyps: none -/
theorem beliefEndorses_iff_condProb [DecidableEq Ω] (w : Ω → ℝ) (X : Finset Ω) (Q : Ω → ℝ) (j : ℝ) :
    BeliefEndorses w X Q ↔ ∀ p, 0 < mass w (cls Q p) → condProbJunk w X (cls Q p) j = p := by
  unfold BeliefEndorses condProbJunk
  refine forall_congr' fun p => forall_congr' fun hp => ?_
  rw [if_neg hp.ne', div_eq_iff hp.ne']

/-- **Expectation endorsement in the sources' division form**: `E[V | Q = x] = x` on every
positive-mass class, with `condExpJunk`.
Source: [[meaning-and-agency-reference]] §Expectation Endorsement
Kind: L
Fidelity: exact
Hyps: none -/
theorem expectationEndorses_iff_condExp (w : Ω → ℝ) (V Q : Ω → ℝ) (j : ℝ) :
    ExpectationEndorses w V Q ↔
      ∀ x, 0 < mass w (cls Q x) → condExpJunk w V (cls Q x) j = x := by
  unfold ExpectationEndorses
  refine forall_congr' fun x => forall_congr' fun hx => ?_
  rw [condExpJunk_of_pos hx, div_eq_iff hx.ne']
  rfl

/-- Supporting lemma: dividing by a positive constant does not move the argmax.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem isArgmax_div_iff {A : Type} (f : A → ℝ) {m : ℝ} (hm : 0 < m) (a : A) :
    IsArgmax (fun a' => f a' / m) a ↔ IsArgmax f a := by
  unfold IsArgmax
  exact forall_congr' fun a' => div_le_div_iff_of_pos_right hm

/-- **Control endorsement in the sources' division form**: every realized `a` is an argmax of
`a' ↦ E[U(·, a') | C = a]` (`condExpJunk`, any junk value).
Source: [[meaning-and-agency-reference]] §Control Endorsement
Kind: L
Fidelity: exact
Hyps: none -/
theorem controlEndorses_iff_condExp {A : Type} [DecidableEq A] (w : Ω → ℝ) (U : Ω → A → ℝ)
    (C : Ω → A) (j : ℝ) :
    ControlEndorses w U C ↔
      ∀ a, 0 < mass w (cls C a) →
        IsArgmax (fun a' => condExpJunk w (fun ω => U ω a') (cls C a) j) a := by
  unfold ControlEndorses
  refine forall_congr' fun a => forall_congr' fun ha => ?_
  have : (fun a' => condExpJunk w (fun ω => U ω a') (cls C a) j) =
      fun a' => wsum w (fun ω => U ω a') (cls C a) / mass w (cls C a) := by
    funext a'
    rw [condExpJunk_of_pos ha]
    rfl
  rw [this, isArgmax_div_iff _ ha]

/-! ### Total-probability consequences -/

/-- **Belief endorsement forces total probability**: `P(X) = E[Q]` — the report is unbiased.
(The sum over value classes; null classes contribute nothing.)
Source: none: infrastructure (used by T3(c) and T6(c))
Kind: L
Fidelity: n/a
Hyps: none -/
theorem beliefEndorses_total [DecidableEq Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω} {Q : Ω → ℝ}
    (h : BeliefEndorses w X Q) : mass w X = wsum w Q univ := by
  have h1 : mass w X = wsum w (ind X) univ := by
    rw [← mass_inter_eq_wsum_ind, Finset.inter_univ]
  rw [h1]
  refine wsum_eq_of_fibres hw (ind X) Q univ Q fun p hp => ?_
  have hcls : (univ.filter fun ω => Q ω = p) = cls Q p := rfl
  rw [hcls] at hp ⊢
  rw [← mass_inter_eq_wsum_ind, h p hp, wsum_const_on (c := p) (fun ω hω => by simpa using hω)]

/-- **Expectation endorsement forces unbiasedness**: `E[V] = E[Q]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem expectationEndorses_total {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {V Q : Ω → ℝ}
    (h : ExpectationEndorses w V Q) : wsum w V univ = wsum w Q univ := by
  refine wsum_eq_of_fibres hw V Q univ Q fun x hx => ?_
  have hcls : (univ.filter fun ω => Q ω = x) = cls Q x := rfl
  rw [hcls] at hx ⊢
  rw [h x hx, wsum_const_on (c := x) (fun ω hω => by simpa using hω)]

/-- **Conditional belief endorsement, class identity**: on every value class of the conditioning
variable `V`, `∑_{V = x} w · 1_X = ∑_{V = x} w · W` (sum the pair-class identities over `y`).
Source: none: infrastructure (the engine of T6(c))
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condBeliefEndorses_class_eq {T : Type} [DecidableEq T] [DecidableEq Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    {X : Finset Ω} {V : Ω → T} {W : Ω → ℝ} (h : CondBeliefEndorses w X V W) (x : T) :
    wsum w (ind X) (cls V x) = wsum w W (cls V x) := by
  refine wsum_eq_of_fibres hw (ind X) W (cls V x) W fun y hy => ?_
  rw [filter_cls_eq_cls2, cls2_comm] at hy ⊢
  rw [← mass_inter_eq_wsum_ind, h x y hy,
    wsum_const_on (c := y) (fun ω hω => (by simpa using hω : V ω = x ∧ W ω = y).2)]

/-- **Conditional endorsement given any `V` implies unconditional endorsement** (belief form):
average the pair-class identities over the values of `V`. Strengthens udt-rep-2-015(c), whose
hypothesis "`V` a function of `W`" is unnecessary.
Source: [[meaning-and-agency-reference]] §Conditional Endorsement | udt-rep-2-015(c) (T2(d)(iii))
Kind: P
Fidelity: stronger: no hypothesis on `V`
Hyps: (a) all -/
theorem beliefEndorses_of_condBeliefEndorses {T : Type} [DecidableEq T] [DecidableEq Ω] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω} {V : Ω → T} {W : Ω → ℝ}
    (h : CondBeliefEndorses w X V W) : BeliefEndorses w X W := by
  intro y hy
  rw [mass_inter_eq_wsum_ind]
  rw [← wsum_const_on (w := w) (f := W) (c := y) (fun ω hω => by simpa using hω)]
  refine wsum_eq_of_fibres hw (ind X) W (cls W y) V fun x hx => ?_
  rw [filter_cls_eq_cls2] at hx ⊢
  rw [← mass_inter_eq_wsum_ind, h x y hx,
    wsum_const_on (c := y) (fun ω hω => (by simpa using hω : V ω = x ∧ W ω = y).2)]

/-- **Conditional endorsement given any `V` implies unconditional endorsement** (control form):
the conditional argmax inequalities average over the values of `V` with the pair-class weights.
Source: [[meaning-and-agency-reference]] §Conditional Endorsement | udt-rep-2-015(c) (T2(d)(iii))
Kind: P
Fidelity: stronger: no hypothesis on `V`
Hyps: (a) all -/
theorem controlEndorses_of_condControlEndorses {A T : Type} [DecidableEq A] [DecidableEq T]
    {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {U : Ω → A → ℝ} {V : Ω → T} {W : Ω → A}
    (h : CondControlEndorses w U V W) : ControlEndorses w U W := by
  intro y hy v
  refine wsum_le_of_fibres hw (fun ω => U ω v) (fun ω => U ω y) (cls W y) V fun x hx => ?_
  rw [filter_cls_eq_cls2] at hx ⊢
  exact h x y hx v

end Forms

/-! ### Witness toolkit: sums over events as `if`-sums (so `fin_cases` + `norm_num` evaluate them) -/

section Toolkit

variable [Fintype Ω]

/-- Supporting lemma: `wsum` over an event as a sum of `if`s over the carrier.
Source: none: infrastructure (witness layer)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_event_eq (w f : Ω → ℝ) (P : Ω → Prop) [DecidablePred P] :
    wsum w f (event P) = ∑ ω, if P ω then w ω * f ω else 0 := by
  rw [wsum, event, Finset.sum_filter]

/-- Supporting lemma: the mass of an event as a sum of `if`s over the carrier.
Source: none: infrastructure (witness layer)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_event_eq (w : Ω → ℝ) (P : Ω → Prop) [DecidablePred P] :
    mass w (event P) = ∑ ω, if P ω then w ω else 0 := by
  rw [mass, event, Finset.sum_filter]

/-- Supporting lemma: the mass of `X ∩ event P` as a sum of `if`s over the carrier.
Source: none: infrastructure (witness layer)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_inter_event_eq [DecidableEq Ω] (w : Ω → ℝ) (X : Finset Ω) (P : Ω → Prop)
    [DecidablePred P] :
    mass w (X ∩ event P) = ∑ ω, if P ω ∧ ω ∈ X then w ω else 0 := by
  rw [mass_inter_eq_wsum_ind, wsum_event_eq]
  refine Finset.sum_congr rfl fun ω _ => ?_
  unfold ind
  by_cases hP : P ω <;> by_cases hX : ω ∈ X <;> simp [hP, hX]

end Toolkit

end

end Cleanroom.Udt.UdtEndorsePolicy
