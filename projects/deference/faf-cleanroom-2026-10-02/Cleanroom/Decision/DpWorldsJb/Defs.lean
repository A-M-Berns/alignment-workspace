import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Event spaces, worlds, probabilities and Jeffrey–Bolker states: the definitions of record

The §0/§1 ontology of [[decision-problems-v2]] (dp-core-001, dp-core-003), stated over an
**abstract carrier** `E` with `[BooleanAlgebra E]`:

* `Designation E`: a set `J` of families `D ⊆ E`, each with an infimum (v2 §0, "designated
  meets"; designation attaches to the family, the infimum is unique by `IsGLB.unique`).
* `World J` (v2 Definition 1): a set of events with the four consistency constraints verbatim.
* `Prob J` (v2 §1): a finitely additive `P : E → ℝ`, nonnegative, `P ⊤ = 1`, continuous along
  designated meets; `TwoValued P`.
* `JBPair J`, `JBState J` (v2 Definition 2): desirability on the non-null subtype with the
  averaging axiom in multiplicative form; a pair-valued counterfactual structure with success.

Conventions (mandate §3). Scalars are `ℝ` with `0 ≤ P X` stated and `P X ≤ 1` derived
(v2 writes `[0,1]`: `Fidelity: variant: codomain ℝ with nonnegativity`). Infima of designated
families are `IsGLB`, never `sInf`/`⨅` (a `BooleanAlgebra` has no `InfSet`; adding one would
change the object). Continuity along a designated meet is stated with `IsGLB` on the real side
too, so no empty-`sInf` junk. Desirabilities live on the non-null subtype (v2's "each
`P_s`-non-null event"); every quotient of the sources is a product here. The finite atomic
carrier `Finset Ω` used by `Expressivity`/`Gallow`/`JB` is a *variant* of this one: there worlds
are atoms and `J` is moot (v2 §0, last paragraph).

The ultrafilter link (`Worlds.lean`), the measure link (`Sigma.lean`) and the Dirac link are
*theorems* about these definitions, never definitions (mandate §8).

Package: `Cleanroom.Decision.DpWorldsJb` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open Finset in
/-- A **designation** on a Boolean algebra `E` (v2 §0): a set `J` of families `D ⊆ E`, each
of which has an infimum in `E`. Designating `D` licenses the ω-rule "every `A ∈ D` holds ⟹
`⨅ D` holds" (constraint 4 of `World`). `J = ∅` is the default.
Source: [[decision-problems-v2]] §0 (event space `(𝓔, J)`)
Kind: D
Fidelity: exact (the infimum is not carried; it is unique when it exists)
Hyps: n/a -/
def Designation (E : Type*) [BooleanAlgebra E] : Type _ :=
  {J : Set (Set E) // ∀ D ∈ J, ∃ m, IsGLB D m}

variable {E : Type*} [BooleanAlgebra E]

/-- The empty designation `J = ∅` (v2 §0: "always admissible and the default").
Source: [[decision-problems-v2]] §0
Kind: D
Fidelity: exact
Hyps: n/a -/
def Designation.empty : Designation E := ⟨∅, fun _ h => h.elim⟩

instance : EmptyCollection (Designation E) := ⟨Designation.empty⟩

theorem Designation.empty_val : (∅ : Designation E).1 = ∅ := rfl

/-- A **world** of `(E, J)` (v2 Definition 1): a set `ω ⊆ E` of events ("the propositions
true at `ω`") such that (1) exactly one of `X`, `Xᶜ` belongs to `ω`; (2) `ω` is closed under
entailment; (3) under conjunction; (4) under designated conjunction: for every `D ∈ J`, if
every member of `D` is in `ω` then so is its infimum.
Source: [[decision-problems-v2]] §0 Definition 1 | dp-core-001
Kind: D
Fidelity: exact (constraint 4 quantifies over the infimum via `IsGLB`, which is unique)
Hyps: n/a -/
structure World (J : Designation E) where
  /-- The events true at the world. -/
  carrier : Set E
  /-- Constraint 1: exactly one of `X`, `Xᶜ`. -/
  exactly_one : ∀ X, X ∈ carrier ↔ Xᶜ ∉ carrier
  /-- Constraint 2: closed under entailment. -/
  upward : ∀ X Y, X ∈ carrier → X ≤ Y → Y ∈ carrier
  /-- Constraint 3: closed under conjunction. -/
  meet : ∀ X Y, X ∈ carrier → Y ∈ carrier → X ⊓ Y ∈ carrier
  /-- Constraint 4: closed under designated conjunction. -/
  designated : ∀ D ∈ J.1, (∀ A ∈ D, A ∈ carrier) → ∀ m, IsGLB D m → m ∈ carrier

namespace World

variable {J : Designation E}

instance : Membership E (World J) := ⟨fun ω X => X ∈ ω.carrier⟩

theorem mem_iff (ω : World J) (X : E) : X ∈ ω ↔ X ∈ ω.carrier := Iff.rfl

@[ext] theorem ext {ω₁ ω₂ : World J} (h : ω₁.carrier = ω₂.carrier) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; cases h; rfl

/-- `⊥ ∉ ω` (from constraints 1 and 2).
Source: [[decision-problems-v2]] §0 Definition 1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem bot_notMem (ω : World J) : (⊥ : E) ∉ ω := by
  intro h
  have htop : (⊤ : E) ∈ ω := ω.upward ⊥ ⊤ h le_top
  have := (ω.exactly_one ⊤).1 htop
  rw [compl_top] at this
  exact this h

/-- `⊤ ∈ ω`.
Source: [[decision-problems-v2]] §0 Definition 1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem top_mem (ω : World J) : (⊤ : E) ∈ ω := by
  have := ω.exactly_one ⊤
  rw [compl_top] at this
  exact this.2 ω.bot_notMem

/-- Constraint 1 read on the complement: `Xᶜ ∈ ω ↔ X ∉ ω`.
Source: [[decision-problems-v2]] §0 Definition 1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem compl_mem_iff (ω : World J) (X : E) : Xᶜ ∈ ω ↔ X ∉ ω := by
  constructor
  · intro h hX
    exact (ω.exactly_one X).1 hX h
  · intro h
    by_contra h'
    exact h ((ω.exactly_one X).2 h')

/-- Remark 0.1: finite disjunctions are witnessed — `X ⊔ Y ∈ ω → X ∈ ω ∨ Y ∈ ω`.
Source: [[decision-problems-v2]] §0 Remark 0.1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem mem_or_mem_of_sup_mem (ω : World J) {X Y : E} (h : X ⊔ Y ∈ ω) : X ∈ ω ∨ Y ∈ ω := by
  by_contra hc
  push Not at hc
  have hX : Xᶜ ∈ ω := (ω.compl_mem_iff X).2 hc.1
  have hY : Yᶜ ∈ ω := (ω.compl_mem_iff Y).2 hc.2
  have := ω.meet _ _ hX hY
  rw [← compl_sup] at this
  exact (ω.compl_mem_iff _).1 this h

theorem sup_mem_iff (ω : World J) (X Y : E) : X ⊔ Y ∈ ω ↔ X ∈ ω ∨ Y ∈ ω :=
  ⟨ω.mem_or_mem_of_sup_mem, fun h => h.elim (fun h => ω.upward _ _ h le_sup_left)
    (fun h => ω.upward _ _ h le_sup_right)⟩

theorem inf_mem_iff (ω : World J) (X Y : E) : X ⊓ Y ∈ ω ↔ X ∈ ω ∧ Y ∈ ω :=
  ⟨fun h => ⟨ω.upward _ _ h inf_le_left, ω.upward _ _ h inf_le_right⟩,
    fun h => ω.meet _ _ h.1 h.2⟩

/-- The free converse of constraint 4 (Remark 0.1): `⨅ D ∈ ω` entails every `A ∈ D` in `ω`.
Source: [[decision-problems-v2]] §0 Remark 0.1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem mem_of_isGLB_mem (ω : World J) {D : Set E} {m : E} (hm : IsGLB D m) (h : m ∈ ω) :
    ∀ A ∈ D, A ∈ ω :=
  fun A hA => ω.upward m A h (hm.1 hA)

/-- Finite meets of members are members (constraint 3 iterated).
Source: [[decision-problems-v2]] §0 Definition 1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem finset_inf_mem (ω : World J) (F : Finset E) (h : ∀ A ∈ F, A ∈ ω) : F.inf id ∈ ω := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty]
    exact ω.top_mem
  | insert a s _ ih =>
    rw [Finset.inf_insert]
    exact ω.meet _ _ (h a (Finset.mem_insert_self a s))
      (ih fun A hA => h A (Finset.mem_insert_of_mem hA))

/-- A world for a larger designation is a world for a smaller one (constraint 4 weakens).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
def restrict {J J' : Designation E} (h : J.1 ⊆ J'.1) (ω : World J') : World J where
  carrier := ω.carrier
  exactly_one := ω.exactly_one
  upward := ω.upward
  meet := ω.meet
  designated := fun D hD => ω.designated D (h hD)

theorem mem_restrict {J J' : Designation E} (h : J.1 ⊆ J'.1) (ω : World J') (X : E) :
    X ∈ ω.restrict h ↔ X ∈ ω := Iff.rfl

end World

/-- A **probability** on `(E, J)` (v2 §1): finitely additive, nonnegative, `P ⊤ = 1`, and
continuous along every designated meet: for `D ∈ J` with infimum `m`, `P m` is the greatest
lower bound of `{P (⨅ F) | F ⊆ D finite}`.
Source: [[decision-problems-v2]] §1 (the displayed condition) | dp-core-001
Kind: D
Fidelity: variant: codomain `ℝ` with nonnegativity (v2: `[0,1]`); continuity via `IsGLB` on
both sides
Hyps: n/a -/
structure Prob (J : Designation E) where
  /-- The probability function. -/
  P : E → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ X, 0 ≤ P X
  /-- Normalization. -/
  top : P ⊤ = 1
  /-- Finite additivity. -/
  add : ∀ X Y, Disjoint X Y → P (X ⊔ Y) = P X + P Y
  /-- Continuity along designated meets. -/
  cont : ∀ D ∈ J.1, ∀ m, IsGLB D m →
    IsGLB {r | ∃ F : Finset E, ↑F ⊆ D ∧ r = P (F.inf id)} (P m)

/-- `P` is two-valued: every event has probability `0` or `1`.
Source: [[decision-problems-v2]] §1 ("2-valued probabilities")
Kind: D
Fidelity: exact
Hyps: n/a -/
def TwoValued (P : E → ℝ) : Prop := ∀ X, P X = 0 ∨ P X = 1

namespace Prob

variable {J : Designation E}

@[ext] theorem ext {P Q : Prob J} (h : P.P = Q.P) : P = Q := by
  cases P; cases Q; cases h; rfl

/-- `P ⊥ = 0`.
Source: [[decision-problems-v2]] §1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem bot (P : Prob J) : P.P ⊥ = 0 := by
  have := P.add ⊥ ⊥ disjoint_bot_left
  rw [bot_sup_eq] at this
  linarith

/-- `P Xᶜ = 1 - P X`.
Source: [[decision-problems-v2]] §1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem compl (P : Prob J) (X : E) : P.P Xᶜ = 1 - P.P X := by
  have := P.add X Xᶜ disjoint_compl_right
  rw [sup_compl_eq_top, P.top] at this
  linarith

/-- Monotonicity.
Source: [[decision-problems-v2]] §1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem mono (P : Prob J) {X Y : E} (h : X ≤ Y) : P.P X ≤ P.P Y := by
  have h1 := P.add X (Y \ X) disjoint_sdiff_self_right
  rw [sup_sdiff_cancel_right h] at h1
  have := P.nonneg (Y \ X)
  linarith

/-- `P X ≤ 1`.
Source: [[decision-problems-v2]] §1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem le_one (P : Prob J) (X : E) : P.P X ≤ 1 := by
  have := P.mono (le_top : X ≤ ⊤)
  rwa [P.top] at this

/-- The modular law `P (X ⊔ Y) + P (X ⊓ Y) = P X + P Y`.
Source: [[decision-problems-v2]] §1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem modular (P : Prob J) (X Y : E) : P.P (X ⊔ Y) + P.P (X ⊓ Y) = P.P X + P.P Y := by
  have h1 := P.add X (Y \ X) disjoint_sdiff_self_right
  rw [sup_sdiff_self_right] at h1
  have h2 := P.add (X ⊓ Y) (Y \ X) (disjoint_sdiff_self_right.mono_left inf_le_left)
  rw [inf_comm, sup_inf_sdiff] at h2
  rw [inf_comm]
  linarith

theorem inf_ge (P : Prob J) (X Y : E) : P.P X + P.P Y - 1 ≤ P.P (X ⊓ Y) := by
  have := P.modular X Y
  have := P.le_one (X ⊔ Y)
  linarith

theorem pos_of_le_of_pos (P : Prob J) {X Y : E} (h : X ≤ Y) (hX : 0 < P.P X) : 0 < P.P Y :=
  lt_of_lt_of_le hX (P.mono h)

theorem ne_bot_of_pos (P : Prob J) {X : E} (hX : 0 < P.P X) : X ≠ ⊥ := by
  rintro rfl
  rw [P.bot] at hX
  exact lt_irrefl _ hX

theorem sup_le_add (P : Prob J) (X Y : E) : P.P (X ⊔ Y) ≤ P.P X + P.P Y := by
  have := P.modular X Y
  have := P.nonneg (X ⊓ Y)
  linarith

/-- Additivity over a finite pairwise-disjoint family.
Source: [[decision-problems-v2]] §1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem finset_sum {ι : Type*} (P : Prob J) (F : Finset ι) (f : ι → E)
    (hd : (↑F : Set ι).PairwiseDisjoint f) : P.P (F.sup f) = ∑ i ∈ F, P.P (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [P.bot]
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    have hd' : (↑s : Set ι).PairwiseDisjoint f :=
      hd.subset (Finset.coe_subset.2 (Finset.subset_insert a s))
    have hdis : Disjoint (f a) (s.sup f) := by
      rw [Finset.disjoint_sup_right]
      intro i hi
      exact hd (Finset.mem_coe.2 (Finset.mem_insert_self a s))
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem hi)) (fun h => ha (h ▸ hi))
    rw [P.add _ _ hdis, ih hd']

end Prob

/-! ### Jeffrey–Bolker states (v2 Definition 2) -/

/-- A **Jeffrey–Bolker pair** `(P, V)` (v2 Definition 2, clauses 1–2): a probability and a
desirability on the `P`-non-null events satisfying the averaging axiom, here in multiplicative
form `P (X ⊔ Y) · V (X ⊔ Y) = P X · V X + P Y · V Y` for disjoint non-null `X`, `Y` (v2 writes
the quotient; no division, no junk at null events).
Source: [[decision-problems-v2]] §1 Definition 2 (1)–(2) | dp-core-003
Kind: D
Fidelity: exact (multiplicative form of the averaging axiom)
Hyps: n/a -/
structure JBPair (J : Designation E) where
  /-- The probability. -/
  P : Prob J
  /-- The desirability, on non-null events. -/
  V : {X : E // 0 < P.P X} → ℝ
  /-- The averaging axiom (multiplicative form). -/
  avg : ∀ X Y (hX : 0 < P.P X) (hY : 0 < P.P Y), Disjoint X Y →
    P.P (X ⊔ Y) * V ⟨X ⊔ Y, P.pos_of_le_of_pos le_sup_left hX⟩ =
      P.P X * V ⟨X, hX⟩ + P.P Y * V ⟨Y, hY⟩

/-- The **total-`V` variant** of a JB pair: `V` on every event, the averaging axiom on non-null
disjoint pairs only. The drafting chat records "non-`⊥`" as an *amendment* of Definition 2
under which desirability on null events is free data.
Source: `research/decision-problems/chats/2026-07-02__formalizing-decision-problem-consistency-and-coherence__b8914860.md` line 2387 | dp-core-2-049
Kind: D
Fidelity: variant: total `V`
Hyps: n/a -/
structure JBPairTotal (J : Designation E) where
  /-- The probability. -/
  P : Prob J
  /-- The desirability, on every event (free where `P X = 0`). -/
  V : E → ℝ
  /-- The averaging axiom on non-null disjoint pairs. -/
  avg : ∀ X Y, 0 < P.P X → 0 < P.P Y → Disjoint X Y →
    P.P (X ⊔ Y) * V (X ⊔ Y) = P.P X * V X + P.P Y * V Y

/-- A **subjective state** `(P_s, V_s, cf_s)` (v2 Definition 2): a JB pair and a pair-valued
counterfactual structure on the non-`⊥` events, subject only to success `P^a a = 1`.
Source: [[decision-problems-v2]] §1 Definition 2 | dp-core-003
Kind: D
Fidelity: exact
Hyps: n/a -/
structure JBState (J : Designation E) where
  /-- The actual pair `(P_s, V_s)`. -/
  s : JBPair J
  /-- The counterfactual structure: a supposed pair for each non-`⊥` event. -/
  cf : (a : E) → a ≠ ⊥ → JBPair J
  /-- Success: `P^a a = 1`. -/
  success : ∀ a (h : a ≠ ⊥), (cf a h).P.P a = 1

namespace JBState

variable {J : Designation E}

/-- The type "declines to suppose `⊥`": no JB pair has `P ⊥ = 1` (success at `⊥` would
contradict `P ⊥ = 0`).
Source: [[decision-problems-v2]] §1 Definition 2 ("the type itself declines to suppose `⊥`")
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem no_supposition_of_bot : ¬ ∃ p : JBPair J, p.P.P ⊥ = 1 := by
  rintro ⟨p, hp⟩
  rw [p.P.bot] at hp
  exact zero_ne_one hp

/-- Jeffrey's news value `V_s a` (Remark 1.1: the evidential evaluator), on `P_s`-non-null `a`.
Source: [[decision-problems-v2]] §1 Remark 1.1
Kind: D
Fidelity: exact
Hyps: n/a -/
def newsValue (s : JBState J) (a : E) (h : 0 < s.s.P.P a) : ℝ := s.s.V ⟨a, h⟩

/-- The supposed value `V^a_s a` (Remark 1.1: the causal evaluator), always defined since
success gives `P^a a = 1 > 0`.
Source: [[decision-problems-v2]] §1 Remark 1.1
Kind: D
Fidelity: exact
Hyps: n/a -/
def supposedValue (s : JBState J) (a : E) (h : a ≠ ⊥) : ℝ :=
  (s.cf a h).V ⟨a, by rw [s.success a h]; exact one_pos⟩

/-- Conditional probability `P (X | a) := P (X ⊓ a) / P a`; meaningful under `0 < P a`.
Source: [[decision-problems-v2]] §1 Remark 1.1 ("agrees with conditioning")
Kind: D
Fidelity: exact
Hyps: n/a -/
def condProb (P : Prob J) (X a : E) : ℝ := P.P (X ⊓ a) / P.P a

/-- `cf_s` **agrees with conditioning** wherever both are defined: for `0 < P_s a`,
`P^a_s = P_s (· | a)` (Remark 1.1's optional constraint; the wiki's "Abram's constraint").
Source: [[decision-problems-v2]] §1 Remark 1.1; [[learning-cdt-renderings]] "The fork" | dp-core-102
Kind: D
Fidelity: exact (silent at `P_s a = 0`)
Hyps: n/a -/
def AgreesWithConditioning (s : JBState J) : Prop :=
  ∀ a (h : 0 < s.s.P.P a), ∀ X, (s.cf a (s.s.P.ne_bot_of_pos h)).P.P X = condProb s.s.P X a

end JBState

end

end Cleanroom.Decision.DpWorldsJb
