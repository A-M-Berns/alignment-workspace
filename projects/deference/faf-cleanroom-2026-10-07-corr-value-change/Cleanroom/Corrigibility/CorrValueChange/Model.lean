import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# corr-value-change — the finite Kolmogorov model of record (T1)

Package `corr-value-change` (faf-cleanroom run, 2026-10-07). Source: [[value-change-as-epistemic-update]]
§1.1–1.2. A finite type of worlds `Ω`, a probability vector `P : Ω → ℝ` (nonnegative, summing to
one), a utility `U : Ω → ℝ`; events are `Finset Ω`; `P(E) = ∑_{ω ∈ E} P ω`;
`E[U ∣ E] = (∑_{ω ∈ E} P ω · U ω) / P(E)`. Conditional expectation is defined once here
(`Prob.condExp`); Lean's `x / 0 = 0` is a junk value, and every headline that conditions on an
event carries, or derives from the model, `0 < P(E)`.

A *decision* (§1.1) is a finite partition of the sure event into events of positive
probability, indexed by a type `A` of act labels (`Decision`); positivity of every act is a
structure field, the note's standing convention, and is not re-assumed per theorem.

Numbers: ℝ throughout (theorems and witnesses); witnesses are rational literals in ℝ, checked by
`norm_num`, so nothing is lost against the ℚ fixture `value_change_journey.py`.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ## Probability vectors, mass, integral, conditional expectation -/

/-- A probability on a finite type of worlds: nonnegative weights summing to one.
Source: [[value-change-as-epistemic-update]] §1.1 (the Kolmogorov space, finite case)
Kind: D
Fidelity: exact (finite case; the note's `(Ω, 𝓕, P)` with `𝓕 = 2^Ω`) -/
structure Prob (Ω : Type) [Fintype Ω] where
  /-- the weight of each world -/
  p : Ω → ℝ
  /-- weights are nonnegative -/
  nonneg : ∀ ω, 0 ≤ p ω
  /-- weights sum to one -/
  sum_one : ∑ ω, p ω = 1

/-- `P(E) = ∑_{ω ∈ E} P ω`.
Source: [[value-change-as-epistemic-update]] §1.1
Kind: D
Fidelity: exact -/
def Prob.mass (P : Prob Ω) (E : Finset Ω) : ℝ := ∑ ω ∈ E, P.p ω

/-- `∫_E U dP = ∑_{ω ∈ E} P ω · U ω`.
Source: [[value-change-as-epistemic-update]] §1.1
Kind: D
Fidelity: exact -/
def Prob.integral (P : Prob Ω) (U : Ω → ℝ) (E : Finset Ω) : ℝ := ∑ ω ∈ E, P.p ω * U ω

/-- `E[U ∣ E] = (∫_E U dP) / P(E)`; junk (`0`) when `P(E) = 0`, and every headline guards that.
Source: [[value-change-as-epistemic-update]] §1.1
Kind: D
Fidelity: exact on `P(E) > 0` -/
def Prob.condExp (P : Prob Ω) (U : Ω → ℝ) (E : Finset Ω) : ℝ := P.integral U E / P.mass E

/-- Mass is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.mass_nonneg (P : Prob Ω) (E : Finset Ω) : 0 ≤ P.mass E :=
  sum_nonneg fun ω _ => P.nonneg ω

/-- `P(Ω) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.mass_univ (P : Prob Ω) : P.mass univ = 1 := P.sum_one

/-- Mass is monotone.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.mass_mono (P : Prob Ω) {E F : Finset Ω} (h : E ⊆ F) : P.mass E ≤ P.mass F :=
  sum_le_sum_of_subset_of_nonneg h fun ω _ _ => P.nonneg ω

/-- Mass is additive on disjoint events.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.mass_union (P : Prob Ω) {E F : Finset Ω} (h : Disjoint E F) :
    P.mass (E ∪ F) = P.mass E + P.mass F := sum_union h

/-- The integral is additive on disjoint events.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.integral_union (P : Prob Ω) (U : Ω → ℝ) {E F : Finset Ω} (h : Disjoint E F) :
    P.integral U (E ∪ F) = P.integral U E + P.integral U F := sum_union h

/-- `∫_E U dP = E[U ∣ E] · P(E)` when `P(E) > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.integral_eq_condExp_mul (P : Prob Ω) (U : Ω → ℝ) {E : Finset Ω} (h : 0 < P.mass E) :
    P.integral U E = P.condExp U E * P.mass E := by
  unfold Prob.condExp; field_simp

/-- `E[U ∣ E] · P(E) = ∫_E U dP` (the product form).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.condExp_mul_mass (P : Prob Ω) (U : Ω → ℝ) {E : Finset Ω} (h : 0 < P.mass E) :
    P.condExp U E * P.mass E = P.integral U E := (P.integral_eq_condExp_mul U h).symm

/-- `E[U ∣ {ω}] = U ω` at a world of positive probability.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.condExp_singleton (P : Prob Ω) (U : Ω → ℝ) {ω : Ω} (h : 0 < P.p ω) :
    P.condExp U {ω} = U ω := by
  unfold Prob.condExp Prob.integral Prob.mass
  simp only [sum_singleton]
  field_simp

/-- A conditional expectation of a constant is that constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.condExp_const (P : Prob Ω) (c : ℝ) {E : Finset Ω} (h : 0 < P.mass E) :
    P.condExp (fun _ => c) E = c := by
  unfold Prob.condExp Prob.integral
  rw [← sum_mul]
  show (P.mass E * c) / P.mass E = c
  field_simp

/-- Conditional expectation is additive in the utility.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.condExp_add (P : Prob Ω) (U V : Ω → ℝ) (E : Finset Ω) :
    P.condExp (fun ω => U ω + V ω) E = P.condExp U E + P.condExp V E := by
  unfold Prob.condExp Prob.integral
  rw [← add_div, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun ω _ => ?_
  ring

/-- Adding a constant to the utility shifts the conditional expectation by it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.condExp_add_const (P : Prob Ω) (U : Ω → ℝ) (c : ℝ) {E : Finset Ω}
    (h : 0 < P.mass E) : P.condExp (fun ω => U ω + c) E = P.condExp U E + c := by
  rw [P.condExp_add U (fun _ => c) E, P.condExp_const c h]

/-- A world of positive probability exists (the weights sum to one).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.exists_pos (P : Prob Ω) : ∃ ω, 0 < P.p ω := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have : ∑ ω, P.p ω = 0 := sum_eq_zero fun ω _ => le_antisymm (h ω) (P.nonneg ω)
  rw [P.sum_one] at this
  exact one_ne_zero this

/-- Positive mass means a world of positive weight in the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.exists_pos_of_mass_pos (P : Prob Ω) {E : Finset Ω} (h : 0 < P.mass E) :
    ∃ ω ∈ E, 0 < P.p ω := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  have : P.mass E = 0 := sum_eq_zero fun ω hω => le_antisymm (hc ω hω) (P.nonneg ω)
  linarith

/-- Zero mass means every world of the event has weight zero.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Prob.p_eq_zero_of_mass_eq_zero (P : Prob Ω) {E : Finset Ω} (h : P.mass E = 0) {ω : Ω}
    (hω : ω ∈ E) : P.p ω = 0 :=
  (sum_eq_zero_iff_of_nonneg fun ω _ => P.nonneg ω).1 h ω hω

/-! ## Decisions -/

/-- A **decision** (§1.1): a finite partition of the sure event into events of positive
probability, indexed by act labels `A`. Positivity of every act is a structure field — the
note's standing convention ("every act positive probability in every situation we condition
on"), stated once.
Source: [[value-change-as-epistemic-update]] §1.1 ("a decision is a finite partition 𝒜 ⊆ 𝓕 of
the sure event into events of positive probability")
Kind: D
Fidelity: exact -/
structure Decision (P : Prob Ω) (A : Type) [Fintype A] where
  /-- the event "the agent does `a`" -/
  act : A → Finset Ω
  /-- distinct acts are disjoint events -/
  disjoint : ∀ a b, a ≠ b → Disjoint (act a) (act b)
  /-- the acts cover the sure event -/
  cover : ∀ ω, ∃ a, ω ∈ act a
  /-- every act has positive probability -/
  pos : ∀ a, 0 < P.mass (act a)

variable {A : Type} [Fintype A]

/-- The act an outcome lies in is unique.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Decision.act_unique {P : Prob Ω} (D : Decision P A) {ω : Ω} {a b : A}
    (ha : ω ∈ D.act a) (hb : ω ∈ D.act b) : a = b := by
  by_contra h
  exact (Finset.disjoint_left.1 (D.disjoint a b h)) ha hb

/-- Summing an event's mass over the acts recovers the mass:
`∑_a P(a ∧ E) = P(E)`.
Source: none: infrastructure (partition sum)
Kind: L
Fidelity: n/a -/
theorem Decision.sum_mass_inter {P : Prob Ω} (D : Decision P A) (E : Finset Ω) :
    ∑ a, P.mass (D.act a ∩ E) = P.mass E := by
  unfold Prob.mass
  have h1 : ∀ a, ∑ ω ∈ D.act a ∩ E, P.p ω = ∑ ω ∈ E, if ω ∈ D.act a then P.p ω else 0 := by
    intro a; rw [← sum_filter, filter_mem_eq_inter, inter_comm]
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  obtain ⟨a₀, ha₀⟩ := D.cover ω
  rw [sum_eq_single a₀]
  · simp [ha₀]
  · intro b _ hb
    have : ω ∉ D.act b := fun hb' => hb (D.act_unique hb' ha₀)
    simp [this]
  · intro h; exact absurd (mem_univ a₀) h

/-- Summing an integral over the acts recovers it: `∑_a ∫_{a ∧ E} U = ∫_E U`.
Source: none: infrastructure (partition sum)
Kind: L
Fidelity: n/a -/
theorem Decision.sum_integral_inter {P : Prob Ω} (D : Decision P A) (U : Ω → ℝ) (E : Finset Ω) :
    ∑ a, P.integral U (D.act a ∩ E) = P.integral U E := by
  unfold Prob.integral
  have h1 : ∀ a, ∑ ω ∈ D.act a ∩ E, P.p ω * U ω =
      ∑ ω ∈ E, if ω ∈ D.act a then P.p ω * U ω else 0 := by
    intro a; rw [← sum_filter, filter_mem_eq_inter, inter_comm]
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  obtain ⟨a₀, ha₀⟩ := D.cover ω
  rw [sum_eq_single a₀]
  · simp [ha₀]
  · intro b _ hb
    have : ω ∉ D.act b := fun hb' => hb (D.act_unique hb' ha₀)
    simp [this]
  · intro h; exact absurd (mem_univ a₀) h

/-- The value of act `a` under utility `U` in situation `E`: `v_E(a) = E[U ∣ a ∧ E]`.
Source: [[value-change-as-epistemic-update]] §1.3 (`v_E(a) := E_P[U ∣ a ∧ E]`)
Kind: D
Fidelity: exact -/
def Decision.v {P : Prob Ω} (D : Decision P A) (U : Ω → ℝ) (E : Finset Ω) (a : A) : ℝ :=
  P.condExp U (D.act a ∩ E)

/-- The plain value of an act: `E[U ∣ a] = v_Ω(a)`.
Source: [[value-change-as-epistemic-update]] §1.1
Kind: D
Fidelity: exact -/
def Decision.val {P : Prob Ω} (D : Decision P A) (U : Ω → ℝ) (a : A) : ℝ :=
  P.condExp U (D.act a)

/-- `val = v univ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Decision.val_eq_v_univ {P : Prob Ω} (D : Decision P A) (U : Ω → ℝ) (a : A) :
    D.val U a = D.v U univ a := by
  simp [Decision.val, Decision.v]

/-- An act is `U`-optimal when no act beats it.
Source: [[value-change-as-epistemic-update]] §1.1 (`a* ∈ argmax_a E_P[U ∣ a]`)
Kind: D
Fidelity: exact -/
def Decision.IsOpt {P : Prob Ω} (D : Decision P A) (U : Ω → ℝ) (a : A) : Prop :=
  ∀ b, D.val U b ≤ D.val U a

/-! ## T1(b): the simple argument -/

/-- **The simple argument** (§1.2), for any act `a'` and any `U`-maximizer `aK`:
`E_P[U ∣ a'] ≤ E_P[U ∣ aK]`, with strict inequality **iff** `a'` is not `U`-optimal. The act
`a'` is arbitrary — in the note it is the maximizer of some other `U'` (`simple_argument_swap`
below states that form), and the inequality does not depend on how `a'` was chosen.
Source: [[value-change-as-epistemic-update]] §1.2 ("trivially, and strictly whenever `a'` is not
`U`-optimal")
Kind: P
Fidelity: exact (the "strictly whenever" sharpened to an iff)
Hyps: (a) `hK : aK` is a `U`-maximizer (the quantifier "for every maximizer") -/
theorem simple_argument {P : Prob Ω} (D : Decision P A) (U : Ω → ℝ) (a' aK : A)
    (hK : D.IsOpt U aK) :
    D.val U a' ≤ D.val U aK ∧ (D.val U a' < D.val U aK ↔ ¬ D.IsOpt U a') := by
  refine ⟨hK a', ?_⟩
  constructor
  · intro hlt hopt
    exact absurd (hopt aK) (not_le.2 hlt)
  · intro hnot
    rcases lt_or_eq_of_le (hK a') with h | h
    · exact h
    · exfalso; apply hnot; intro b; rw [h]; exact hK b

/-- **The simple argument in the note's form**: if the values were swapped to `U'` before the
decision, the agent would take some `U'`-maximizer `a'`; by the standards of `U` that act is no
better than `U`'s own maximizer, and strictly worse iff it is not `U`-optimal. (`U'` and the
maximization of `U'` by `a'` play no role in the proof: the point of the formal statement is
that nothing about `U'` could make it otherwise.)
Source: [[value-change-as-epistemic-update]] §1.2
Kind: P
Fidelity: exact
Hyps: (a) `a'` a `U'`-maximizer, `aK` a `U`-maximizer -/
theorem simple_argument_swap {P : Prob Ω} (D : Decision P A) (U U' : Ω → ℝ) (a' aK : A)
    (_ha' : D.IsOpt U' a') (hK : D.IsOpt U aK) :
    D.val U a' ≤ D.val U aK ∧ (D.val U a' < D.val U aK ↔ ¬ D.IsOpt U a') :=
  simple_argument D U a' aK hK

/-! ## T1(c): the deterministic form on a trivial model -/

/-- The uniform probability on a nonempty finite type.
Source: none: infrastructure (the trivial model of T1(c))
Kind: D
Fidelity: n/a -/
def uniformProb (X : Type) [Fintype X] [Nonempty X] : Prob X where
  p := fun _ => 1 / (Fintype.card X : ℝ)
  nonneg := fun _ => by positivity
  sum_one := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
    field_simp

/-- The decision whose acts are the singletons `{x}`: each option is one world.
Source: none: infrastructure (the trivial model of T1(c))
Kind: D
Fidelity: n/a -/
def singletonDecision (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] :
    Decision (uniformProb X) X where
  act := fun x => {x}
  disjoint := fun a b h => by simpa using h
  cover := fun x => ⟨x, mem_singleton_self x⟩
  pos := fun x => by
    unfold Prob.mass uniformProb
    simp only [sum_singleton]
    positivity

/-- On the singleton decision, the value of option `x` is `U x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem singletonDecision_val (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] (U : X → ℝ)
    (x : X) : (singletonDecision X).val U x = U x := by
  unfold Decision.val singletonDecision
  apply Prob.condExp_singleton
  unfold uniformProb; positivity

/-- **The deterministic form** `U(argmax U) ≥ U(argmax U')`: for options `x` in a finite set,
if `x*` maximizes `U` and `x'` maximizes `U'`, then `U x' ≤ U x*`, strictly iff `x'` does not
maximize `U`. Obtained from `simple_argument` on the trivial model (uniform probability, acts
the singletons), as the note's "just as … in the deterministic case".
Source: [[value-change-as-epistemic-update]] §1.2
Kind: L
Fidelity: exact
Hyps: (a) `x*` a `U`-maximizer, `x'` a `U'`-maximizer -/
theorem deterministic_simple_argument (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]
    (U U' : X → ℝ) (x' xs : X) (_hx' : ∀ x, U' x ≤ U' x') (hxs : ∀ x, U x ≤ U xs) :
    U x' ≤ U xs ∧ (U x' < U xs ↔ ¬ ∀ x, U x ≤ U x') := by
  have hK : (singletonDecision X).IsOpt U xs := by
    intro b; rw [singletonDecision_val, singletonDecision_val]; exact hxs b
  have := simple_argument (singletonDecision X) U x' xs hK
  simp only [singletonDecision_val, Decision.IsOpt] at this
  exact this

end

end Cleanroom.Corrigibility.CorrValueChange
