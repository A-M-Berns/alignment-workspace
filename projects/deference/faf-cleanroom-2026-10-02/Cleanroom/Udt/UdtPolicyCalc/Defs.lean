import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The policy-modification calculus: definitions of record

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-29), namespace
`Cleanroom.Udt.UdtPolicyCalc`. Dependents (`udt-paper-tiling`, `udt-comm-trust`,
`udt-influence-101`) import these names; none is renamed after its first commit.

* Carriers `S` (situations / observations) and `A` (actions) are arbitrary `Type`s with the
  finiteness/decidability instances stated per declaration; nothing is fixed to `Fin 10 → Fin 5`
  (the source's `BasicSimple`/`Substantive` narrowings are dropped, udt-rep-001).
* `Policy S A := S → A` (an `abbrev`, so `Fintype (S → A)` and the `Function.update` API apply).
* Modification `π[s ↦ a]` **is** Mathlib's `Function.update π s a`; the source's hand-rolled
  `modify` is kept only to prove it extensionally equal (`modify_eq_update`).
* `IsOptimal`, `IsLocallyOptimal` (the source's three-argument shape), `IsLocalOptimum`,
  `IsArgmax` (a predicate, ties allowed), `LocalGlobal`.
* Separability (`Separable`, `CrossSituationDependence`, the policy-dependence test `RTest`,
  the literal formal-single-agent predicate `FSADependence`, ordinal separability `OrdSep`).
* Finite probability: `FinDist` (weight function, non-negative, sums to one), `mass`,
  `condExpJunk` and `condProbJunk` with an **explicit junk value** for null events — no
  division sits in a definition without its zero case ([[STANDARDS]] §3).

Source files: `research/udt-representation-theorem/lean/UDT/Basic.lean` (untrusted, not over
FAF), [[udt-policy-calc-mandate]] §3.
-/

namespace Cleanroom.Udt.UdtPolicyCalc

open Finset

noncomputable section

/-- A **policy** maps situations (observations) to actions. An `abbrev`, so the `Fintype` and
`Function.update` API of `S → A` applies without unfolding.
Source: `lean/UDT/Basic.lean:25` (udt-rep-001)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev Policy (S A : Type) := S → A

section Calculus

variable {S A : Type} [DecidableEq S]

/-- The source's hand-rolled modification `π[o ↦ a]` (`fun o' => if o' = o then a else π o'`),
kept only to be identified with `Function.update` (`modify_eq_update`); nothing else uses it.
Source: `lean/UDT/Basic.lean:33` (udt-rep-001)
Kind: D
Fidelity: exact
Hyps: n/a -/
def modify (π : Policy S A) (s : S) (a : A) : Policy S A := fun s' => if s' = s then a else π s'

/-- The source's `π[o ↦ a]` is extensionally `Function.update π o a`; the source's
`modify_self`/`modify_at`/`modify_other` are `Function.update_eq_self`/`update_self`/`update_of_ne`.
Source: `lean/UDT/Basic.lean:33–81` (udt-rep-001)
Kind: L
Fidelity: exact
Hyps: none -/
theorem modify_eq_update (π : Policy S A) (s : S) (a : A) :
    modify π s a = Function.update π s a := by
  funext s'
  simp only [modify, Function.update_apply]

/-- `π` is **(globally) optimal** for the policy utility `U`: no policy scores higher.
Source: `lean/UDT/Basic.lean:41` (udt-rep-001); [[critical-analysis]] "What we can actually prove"
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsOptimal (U : Policy S A → ℝ) (π : Policy S A) : Prop := ∀ π', U π' ≤ U π

/-- Action `a` is **locally optimal** for `π` at `s`: among the one-situation modifications
`π[s ↦ a']`, `a` scores highest (the source's three-argument shape, so udt-rep-002 reads as
written).
Source: `lean/UDT/Basic.lean:48` (udt-rep-001)
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsLocallyOptimal (U : Policy S A → ℝ) (π : Policy S A) (s : S) (a : A) : Prop :=
  ∀ a', U (Function.update π s a') ≤ U (Function.update π s a)

/-- `π` is a **local optimum**: at every situation its own action is locally optimal
(a UDT1.0 fixed point in Post 1's vocabulary, `PolicySelection.lean`).
Source: `lean/UDT/Theorem.lean:30` (udt-rep-002, the conclusion's shape)
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsLocalOptimum (U : Policy S A → ℝ) (π : Policy S A) : Prop :=
  ∀ s, IsLocallyOptimal U π s (π s)

/-- A local optimum is a policy no one-situation modification improves.
Source: none: infrastructure (udt-rep-001)
Kind: L
Fidelity: exact
Hyps: none -/
theorem isLocalOptimum_iff {U : Policy S A → ℝ} {π : Policy S A} :
    IsLocalOptimum U π ↔ ∀ s a, U (Function.update π s a) ≤ U π := by
  constructor
  · intro h s a
    have := h s a
    rwa [Function.update_eq_self] at this
  · intro h s a
    rw [Function.update_eq_self]
    exact h s a

/-- `x` is an **argmax** of `f` (ties allowed). A predicate, never a function: headline verdicts
are strict inequalities between named candidates.
Source: none: infrastructure ([[udt-policy-calc-mandate]] §3)
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsArgmax {X : Type} (f : X → ℝ) (x : X) : Prop := ∀ x', f x' ≤ f x

/-- `x` is the **strict argmax** of `f`: every other candidate scores strictly less.
Source: none: infrastructure
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsStrictArgmax {X : Type} (f : X → ℝ) (x : X) : Prop := ∀ x', x' ≠ x → f x' < f x

/-- **Local ⟹ global holds for `U`**: every local optimum of `U` is a global optimum
(the property the extension §5 asks whether separability characterizes).
Source: [[udt-policy-calc-mandate]] §5 (udt-rep-003)
Kind: D
Fidelity: exact
Hyps: n/a -/
def LocalGlobal (U : Policy S A → ℝ) : Prop := ∀ π, IsLocalOptimum U π → IsOptimal U π

end Calculus

section Separability

variable {S A : Type} [Fintype S] [DecidableEq S]

/-- `U` is **separable** (no cross-situation dependence): `U π = ∑ s, u s (π s)` for some
per-situation reward `u`. The corpus's weight `P s` is absorbed into `u` (`separable_of_weighted`).
Source: [[topics/policy-types]] "Cross-observation dependence" (negated); [[formal-single-agent]]
"When do split and unified agree?" (udt-rep-047)
Kind: D
Fidelity: exact: the policy-utility form of the corpus's definition; the weight `P` is absorbed
Hyps: n/a -/
def Separable (U : Policy S A → ℝ) : Prop := ∃ u : S → A → ℝ, ∀ π, U π = ∑ s, u s (π s)

/-- **Cross-situation dependence** is the failure of separability. Replaces the source's junk
`hasCrossSituationDependence _ := True` (`Substantive.lean:83`).
Source: [[topics/policy-types]] "Cross-observation dependence" (udt-rep-047)
Kind: D
Fidelity: exact
Hyps: n/a -/
def CrossSituationDependence (U : Policy S A → ℝ) : Prop := ¬ Separable U

/-- The **policy-dependence test** of [[when-udt-edt-diverge]]: per-situation rewards
`R s π` that depend on `π` only through `π s`.
Source: [[when-udt-edt-diverge]] "When are they the same?" (udt-rep-047)
Kind: D
Fidelity: exact
Hyps: n/a -/
def RTest (R : S → Policy S A → ℝ) : Prop := ∀ s π π', π s = π' s → R s π = R s π'

/-- The **literal** cross-situation-dependence predicate of [[formal-single-agent]] lines 61–71:
"there exists a policy `π` with `π(s) = a` … and another policy `π'` with `π'(s) = a` … such
that `E[U | π] ≠ E[U | π'] despite agreeing on action at s`". Refuted as a definition
(`fsaDependence_iff_nonconstant`): on `|S| ≥ 2` it is exactly non-constancy of `U`.
Source: [[formal-single-agent]] lines 61–71 (udt-rep-047; mandate T4(b))
Kind: D
Fidelity: exact (the literal reading; ATTRIBUTION-UNVETTED that this reading was intended)
Hyps: n/a -/
def FSADependence (U : Policy S A → ℝ) : Prop :=
  ∃ (s : S) (π π' : Policy S A), π s = π' s ∧ U π ≠ U π'

/-- **Ordinal separability**: the comparison of two actions at `s` does not depend on the rest of
the policy. Strictly between `Separable` and `LocalGlobal` (`LocalGlobal.lean`, §5).
Source: [[udt-policy-calc-mandate]] §5 (extension; not in any source)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def OrdSep (U : Policy S A → ℝ) : Prop :=
  ∀ (s : S) (a a' : A) (π π' : Policy S A),
    (U (Function.update π s a) ≤ U (Function.update π s a')) ↔
      (U (Function.update π' s a) ≤ U (Function.update π' s a'))

end Separability

/-! ### Finite probability with explicit junk values -/

/-- A **finite distribution**: a non-negative weight function summing to one. Not `PMF` and not
`MeasureTheory.Measure` ([[udt-policy-calc-mandate]] §3): expectations are finite sums and
`norm_num` closes the numerics.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
structure FinDist (X : Type) [Fintype X] where
  /-- The weight of each point. -/
  w : X → ℝ
  /-- Weights are non-negative. -/
  nonneg : ∀ x, 0 ≤ w x
  /-- Weights sum to one. -/
  sum_one : ∑ x, w x = 1

section Prob

variable {X : Type}

/-- Expectation of `f` under `μ`: `∑ x, μ x * f x`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def FinDist.exp [Fintype X] (μ : FinDist X) (f : X → ℝ) : ℝ := ∑ x, μ.w x * f x

/-- The mass `∑ x ∈ E, w x` of a finite event under a weight function.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def mass (w : X → ℝ) (E : Finset X) : ℝ := ∑ x ∈ E, w x

/-- **Conditional expectation with an explicit junk value**: `E[f | E]` when `mass w E ≠ 0`,
and `j` otherwise. The C&T convention is `j = -1` ([[communication-trust-translated]] line 269).
Source: [[communication-trust-translated]] lines 265–270 (udt-rep-090); [[udt-policy-calc-mandate]] §3
Kind: D
Fidelity: exact: C&T's `E(U | X = x) := -1` when `P(X = x) = 0`, with `j` a parameter
Hyps: n/a -/
def condExpJunk (w : X → ℝ) (f : X → ℝ) (E : Finset X) (j : ℝ) : ℝ :=
  if mass w E = 0 then j else (∑ x ∈ E, w x * f x) / mass w E

/-- **Conditional probability with an explicit junk value**: `P(E | F)` when `mass w F ≠ 0`, and
`j` otherwise.
Source: none: infrastructure (mandate T10(d))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def condProbJunk [DecidableEq X] (w : X → ℝ) (E F : Finset X) (j : ℝ) : ℝ :=
  if mass w F = 0 then j else mass w (E ∩ F) / mass w F

/-- The finite event `{x | P x}` as a `Finset`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev event [Fintype X] (P : X → Prop) [DecidablePred P] : Finset X := Finset.univ.filter P

/-- Supporting lemma `mem_event` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_event [Fintype X] {P : X → Prop} [DecidablePred P] {x : X} : x ∈ event P ↔ P x := by
  simp [event]

/-- Supporting lemma `mass_nonneg` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_nonneg {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (E : Finset X) : 0 ≤ mass w E :=
  Finset.sum_nonneg fun x _ => hw x

/-- Supporting lemma `mass_pos_of_mem` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_pos_of_mem {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) {E : Finset X} {x₀ : X} (hx : x₀ ∈ E)
    (hpos : 0 < w x₀) : 0 < mass w E :=
  lt_of_lt_of_le hpos (Finset.single_le_sum (fun x _ => hw x) hx)

/-- Supporting lemma `mass_eq_zero_of_forall` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_eq_zero_of_forall {w : X → ℝ} {E : Finset X} (h : ∀ x ∈ E, w x = 0) : mass w E = 0 :=
  Finset.sum_eq_zero h

/-- Supporting lemma `condExpJunk_of_mass_eq_zero` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_of_mass_eq_zero {w f : X → ℝ} {E : Finset X} {j : ℝ} (h : mass w E = 0) :
    condExpJunk w f E j = j := by
  simp [condExpJunk, h]

/-- Supporting lemma `condExpJunk_of_pos` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_of_pos {w f : X → ℝ} {E : Finset X} {j : ℝ} (h : 0 < mass w E) :
    condExpJunk w f E j = (∑ x ∈ E, w x * f x) / mass w E := by
  simp [condExpJunk, h.ne']

/-- On an event of positive mass where `f` is constantly `c`, the conditional expectation is `c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_const_on {w f : X → ℝ} {E : Finset X} {j c : ℝ}
    (hc : ∀ x ∈ E, f x = c) (h : 0 < mass w E) : condExpJunk w f E j = c := by
  rw [condExpJunk_of_pos h]
  have : ∑ x ∈ E, w x * f x = c * mass w E := by
    rw [mass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x hx => by rw [hc x hx, mul_comm]
  rw [this, mul_div_assoc, div_self h.ne', mul_one]

/-- A conditional expectation over an event of positive mass is bounded above by any pointwise
upper bound of `f` on the event (non-negative weights).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_le_of_le {w f : X → ℝ} (hw : ∀ x, 0 ≤ w x) {E : Finset X} {j c : ℝ}
    (h : 0 < mass w E) (hc : ∀ x ∈ E, f x ≤ c) : condExpJunk w f E j ≤ c := by
  rw [condExpJunk_of_pos h, div_le_iff₀ h, mass, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => by
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hc x hx) (hw x)

/-- A conditional expectation over an event of positive mass is bounded below by any pointwise
lower bound of `f` on the event (non-negative weights).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem le_condExpJunk_of_le {w f : X → ℝ} (hw : ∀ x, 0 ≤ w x) {E : Finset X} {j c : ℝ}
    (h : 0 < mass w E) (hc : ∀ x ∈ E, c ≤ f x) : c ≤ condExpJunk w f E j := by
  rw [condExpJunk_of_pos h, le_div_iff₀ h, mass, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => by
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hc x hx) (hw x)

/-- The point mass at `x₀`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def FinDist.delta [Fintype X] [DecidableEq X] (x₀ : X) : FinDist X where
  w x := if x = x₀ then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_one := by simp

/-- Supporting lemma `FinDist.delta_w` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem FinDist.delta_w [Fintype X] [DecidableEq X] (x₀ x : X) :
    (FinDist.delta x₀).w x = if x = x₀ then 1 else 0 := rfl

/-- The two-point distribution with mass `t` on `x₀` and `1 - t` on `x₁` (if `x₀ = x₁` the
whole mass sits there).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def FinDist.bern [Fintype X] [DecidableEq X] (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (x₀ x₁ : X) : FinDist X where
  w x := (if x = x₀ then t else 0) + (if x = x₁ then 1 - t else 0)
  nonneg x := by
    have : 0 ≤ 1 - t := by linarith
    split_ifs <;> linarith
  sum_one := by
    rw [Finset.sum_add_distrib]
    simp

/-- Supporting lemma `FinDist.bern_w` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem FinDist.bern_w [Fintype X] [DecidableEq X] (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (x₀ x₁ x : X) :
    (FinDist.bern t h0 h1 x₀ x₁).w x = (if x = x₀ then t else 0) + (if x = x₁ then 1 - t else 0) :=
  rfl

/-- The equal mixture of two point masses.
Source: none: infrastructure (mandate T10(c) witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def FinDist.halfHalf [Fintype X] [DecidableEq X] (x₀ x₁ : X) : FinDist X :=
  FinDist.bern (1 / 2) (by norm_num) (by norm_num) x₀ x₁

end Prob

end

end Cleanroom.Udt.UdtPolicyCalc
