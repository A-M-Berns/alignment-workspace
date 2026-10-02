import Cleanroom.Bli.BliFinite.Index
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# `udt-bli-core` · Defs: the finite BLI-structured prior and the one-step decision objects (T1)

The definitions of record for the BLI decision layer. Everything is **finite probability over
one measure `μ`**: a `FiniteBLIPrior` is a finite outcome space `Ω` with a rational probability
`μ`, a coordinate `state : Ω → ↥𝒟` saying which day-`m` table obtains, a coordinate
`pp : Ω → Policy 𝒟 A` giving the values of every policy point `A(T) = ·` in the world, a utility
`U`, and a world truth assignment `small` for the day-`m` small sentences tied to the table by the
`faith` field. Design decisions of record (mandate §3):

1. **One measure, product forms, positivity explicit.** Every "conditional expectation" is
   `integralOf μ U E / massOf μ E` with Lean's `x / 0 = 0` as the **junk value**; each headline
   names the positivity predicate it needs (`NDPOL`, `NDHOME`, `NDPOLICY`, or a single positive
   mass). Nothing is stated at a junk cell without saying so.
2. **Argmax is a predicate, never a function**: `IsOneStepChoice`, `IsUpdatefulChoice`,
   `IsPriorOptimal` are `∀ b, value b ≤ value a` (ties allowed), following `udt-policy-calc`'s
   `IsArgmax` convention over `ℚ`. "One-step = updateful" is an equality of maximizer *sets*.
3. **Policies and points**: `Policy 𝒟 A := ↥𝒟 → A`; the event "`pp · T = a`" is
   `{ω | pp ω T = a}`, "`state = T`" is `{ω | state ω = T}`, the ex-ante event of a policy is
   `{ω | pp ω = π}`. Cross-branch effects are facts about the joint law of `(state, pp, U)`.
4. **Faith is a field about small sentences** (`𝒮.S m`, the day-`m` small index, in place of the
   desiderata's `Sminus m m`: `variant: scope 𝒮.S m`). Most theorems of this package do not use
   it; each docstring says whether it does.
5. **Structural predicates are derived, never fields**: `Reflective`, `NoCrossBranch`
   (point level), `ReflectivePolicy`, `LocalUtility` (policy level), `IndependentPoints`,
   `IndependentPointsGivenState`, `FaithGivenPoints`, `PolicyFair` — each a `Prop` about `μ`,
   each carrying its own positivity guard so it never quantifies over junk cells.
6. **`PolicyFair` needs a procedure coordinate** (`ProcLayer`); on a bare prior it is trivial.

Sources: [[bli-program]] §2.8, [[bli-program-desiderata]] §2.6/U0, bli-paper-047 (a policy is a
function from written-out belief states to actions), bli-slides-032 (the wanted rule conditions
on `A(o) = a`), bli-soto-b-2-008 ("one-step" = nothing else in the conditional),
bli-soto-b-020 (`pp`), bli-paper-051 (conditioning on `π*(𝒬) = a` is the open piece — here it
is a *coordinate* of the finite prior, not derived from an inductor; that is the honest scope).
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

/-! ## Generic finite-probability helpers -/

/-- The rational indicator of a Boolean.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ind (b : Bool) : ℚ := if b then 1 else 0

/-- The mass of an event `E` under a weight function `μ` on a finite type:
`∑ ω, if E ω then μ ω else 0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def massOf {Ω : Type} [Fintype Ω] (μ : Ω → ℚ) (E : Ω → Prop) [DecidablePred E] : ℚ :=
  ∑ ω, if E ω then μ ω else 0

/-- The integral of `f` over the event `E`: `∑ ω, if E ω then μ ω * f ω else 0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def integralOf {Ω : Type} [Fintype Ω] (μ : Ω → ℚ) (f : Ω → ℚ) (E : Ω → Prop)
    [DecidablePred E] : ℚ :=
  ∑ ω, if E ω then μ ω * f ω else 0

/-- **Conditional expectation** `𝔼_μ[f | E] := integralOf μ f E / massOf μ E`. **Junk value:**
Lean's `x / 0 = 0`, so at a null event the conditional expectation is `0`; every theorem that uses
it at a cell names the positivity of that cell.
Source: [[bli-program]] §2.8 (product form); mandate §3.1
Kind: D
Fidelity: exact (with the disclosed junk value) -/
def condExp {Ω : Type} [Fintype Ω] (μ : Ω → ℚ) (f : Ω → ℚ) (E : Ω → Prop)
    [DecidablePred E] : ℚ :=
  integralOf μ f E / massOf μ E

/-! ## Policies and the prior -/

/-- A **policy** over the finite set `𝒟` of possible day-`m` tables: a function from written-out
belief states (tables) to actions (bli-paper-047: "a policy is now a function from full belief
states to actions").
Source: bli-paper-047 (`main.tex` 319–325); [[bli-program]] §2.8
Kind: D
Fidelity: exact (the belief state is the day-`m` table on the small index) -/
abbrev Policy {𝒮 : SmallIndex} {m : ℕ} (𝒟 : Finset (Table 𝒮 m)) (A : Type) : Type := ↥𝒟 → A

/-- **A finite BLI-structured prior**: a finite outcome space with a rational probability `μ`,
the day-`m` table that obtains (`state`, valued in the finite carrier `𝒟`), the values of all
policy points `A(T) = ·` in the world (`pp`), a utility `U`, the world's small truths (`small`),
and **faith** in the written-out state: within `state = T` the `μ`-frequency of each small
sentence `φ` is the table's own price `T φ`.
Faith is the only field beyond the probability axioms; every structural predicate
(`Reflective`, `NoCrossBranch`, …) is a derived `Prop`, never a field (mandate §3.5; the
construction draft's `UDTFrame` with faith axioms as *data* is not adopted, [[bli-program]] §2.8).
Source: [[bli-program]] §2.8 (`FiniteBLIPrior`); [[bli-program-desiderata]] §2.6 (U0)
Kind: D
Fidelity: variant: faith scoped to `𝒮.S m` (the day-`m` small index) in place of the
desiderata's `Sminus m m`; `pp` is a coordinate, not derived from an inductor (bli-paper-051) -/
structure FiniteBLIPrior (𝒮 : SmallIndex) (m : ℕ) (𝒟 : Finset (Table 𝒮 m)) (A : Type) where
  /-- The finite outcome space. -/
  Ω : Type
  [fin : Fintype Ω]
  /-- The prior. -/
  μ : Ω → ℚ
  /-- Nonnegativity. -/
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  /-- Total mass one. -/
  μ_sum_one : ∑ ω, μ ω = 1
  /-- Which day-`m` table obtains. -/
  state : Ω → ↥𝒟
  /-- The policy-point values: `pp ω T` is the action the world `ω` says `A(T)` takes. -/
  pp : Ω → Policy 𝒟 A
  /-- The utility. -/
  U : Ω → ℚ
  /-- The world's truth assignment to the day-`m` small sentences. -/
  small : Ω → ↥(𝒮.S m) → Bool
  /-- Faith in the written-out state: `∑_{state = T} μ · [small φ] = T φ · ∑_{state = T} μ`. -/
  faith : ∀ (T : ↥𝒟) (φ : ↥(𝒮.S m)),
    (∑ ω, if state ω = T then μ ω * ind (small ω φ) else 0) =
      T.1 φ * ∑ ω, if state ω = T then μ ω else 0

attribute [instance] FiniteBLIPrior.fin

namespace FiniteBLIPrior

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-! ## Masses, integrals and conditional values -/

/-- `μ(state = T)`.
Source: [[bli-program]] §2.8
Kind: D
Fidelity: exact -/
def stateMass (T : ↥𝒟) : ℚ := massOf P.μ (fun ω => P.state ω = T)

/-- `μ(pp · T = a)`: the mass of the policy point `A(T) = a`.
Source: [[bli-program]] §2.8 (`NDPOL`'s quantity)
Kind: D
Fidelity: exact -/
def ppMass (T : ↥𝒟) (a : A) : ℚ := massOf P.μ (fun ω => P.pp ω T = a)

/-- `∑_{pp · T = a} μ · U`.
Source: [[bli-program]] §2.8
Kind: D
Fidelity: exact -/
def ppUtil (T : ↥𝒟) (a : A) : ℚ := integralOf P.μ P.U (fun ω => P.pp ω T = a)

/-- **The one-step value** `EU T a := 𝔼_μ[U | pp · T = a]`: the prior's expectation of utility
conditioned on the policy point `A(T) = a` and on **nothing else** ("one-step UDT" =
`argmax_a 𝔼_P(U | A(Q) = a)` with nothing else in the conditional, bli-soto-b-2-008). This is
the rule bli-slides-032 wants (`A(o) = argmax_a 𝕍(A(o) = a)`), as opposed to the material
conditional `𝕍(O = o ⇒ A = a)` (`MaterialConditional.lean`); bli-paper-051 leaves the
extrapolation of `π*(𝒬) = a` from small beliefs open — here `pp` is a coordinate of the prior.
Junk value `0` at `ppMass T a = 0` (`NDPOL` excludes it).
Source: bli-soto-b-2-008; bli-slides-032; bli-paper-051; [[bli-program]] §2.8 (`EU`)
Kind: D
Fidelity: exact (finite; the policy point is a coordinate) -/
def EU (T : ↥𝒟) (a : A) : ℚ := condExp P.μ P.U (fun ω => P.pp ω T = a)

/-- `μ(state = T' ∧ pp · T = a)`: the mass of the branch `T'` inside the policy point `A(T) = a`.
Source: [[bli-program]] §3.9 (branch decomposition)
Kind: D
Fidelity: exact -/
def jointMass (T' T : ↥𝒟) (a : A) : ℚ :=
  massOf P.μ (fun ω => P.state ω = T' ∧ P.pp ω T = a)

/-- `∑_{state = T' ∧ pp · T = a} μ · U`.
Source: [[bli-program]] §3.9
Kind: D
Fidelity: exact -/
def jointUtil (T' T : ↥𝒟) (a : A) : ℚ :=
  integralOf P.μ P.U (fun ω => P.state ω = T' ∧ P.pp ω T = a)

/-- **The branch value** `condEU T' T a := 𝔼_μ[U | state = T' ∧ pp · T = a]`: what branch `T'`
expects given the policy point `A(T) = a`. Junk value `0` at a null cell.
Source: bli-soto-a-2-012 (ii); bli-slides-037 (`𝔼_P(u | φ, o)`)
Kind: D
Fidelity: exact -/
def condEU (T' T : ↥𝒟) (a : A) : ℚ :=
  condExp P.μ P.U (fun ω => P.state ω = T' ∧ P.pp ω T = a)

/-- **The updateful (home-branch) value** `homeEU T a := 𝔼_μ[U | state = T ∧ pp · T = a]`: the
value of the action `a` inside its own branch, the "updateful picture" of bli-soto-a-011.
Source: bli-soto-a-011 (Notion 226–235); bli-soto-a-2-012 (i)
Kind: D
Fidelity: exact -/
def homeEU (T : ↥𝒟) (a : A) : ℚ := P.condEU T T a

/-- **The branch probability** `branchProb T' T a := μ(state = T' | pp · T = a)`. Junk `0` at a
null point.
Source: bli-slides-037 (`P(o | φ)`); [[bli-program]] §3.9
Kind: D
Fidelity: exact -/
def branchProb (T' T : ↥𝒟) (a : A) : ℚ := P.jointMass T' T a / P.ppMass T a

/-- `μ(pp = π)`: the ex-ante mass of a whole policy.
Source: [[bli-program]] §2.8 (`exAnteValue`'s denominator)
Kind: D
Fidelity: exact -/
def policyMass (π : Policy 𝒟 A) : ℚ := massOf P.μ (fun ω => P.pp ω = π)

/-- `∑_{pp = π} μ · U`.
Source: [[bli-program]] §2.8
Kind: D
Fidelity: exact -/
def policyUtil (π : Policy 𝒟 A) : ℚ := integralOf P.μ P.U (fun ω => P.pp ω = π)

/-- **The ex-ante value of a policy** `exAnteValue π := 𝔼_μ[U | pp = π]` (the UDT 1.1 /
policy-level value, the paper's `E_p(u | π* = ⌜π⌝)`). Junk `0` for a null policy; `NDPOLICY`
excludes it. This is the value of an *actual* policy under `μ`, not an array formula
(`sepValue` is the separable formula, identified with this one only under the policy-level
predicates, `Good.lean`).
Source: bli-paper-047 (`main.tex` 145–147, `E_p(u | π* = ⌜π⌝)`); [[bli-program]] §2.8
Kind: D
Fidelity: exact -/
def exAnteValue (π : Policy 𝒟 A) : ℚ := condExp P.μ P.U (fun ω => P.pp ω = π)

/-- `μ(state = T ∧ pp = π)`: the mass of the policy-level cell.
Source: [[bli-program]] §3.9 (Good's theorem, the cells the policy-level predicates speak of)
Kind: D
Fidelity: exact -/
def cellMass (T : ↥𝒟) (π : Policy 𝒟 A) : ℚ :=
  massOf P.μ (fun ω => P.state ω = T ∧ P.pp ω = π)

/-- `∑_{state = T ∧ pp = π} μ · U`.
Source: [[bli-program]] §3.9
Kind: D
Fidelity: exact -/
def cellUtil (T : ↥𝒟) (π : Policy 𝒟 A) : ℚ :=
  integralOf P.μ P.U (fun ω => P.state ω = T ∧ P.pp ω = π)

/-- `cellEU T π := 𝔼_μ[U | state = T ∧ pp = π]`: what branch `T` expects given the whole policy.
Junk `0` at a null cell.
Source: [[bli-program]] §3.9; bli-soto-b-2-016 (T1)
Kind: D
Fidelity: exact -/
def cellEU (T : ↥𝒟) (π : Policy 𝒟 A) : ℚ :=
  condExp P.μ P.U (fun ω => P.state ω = T ∧ P.pp ω = π)

/-- **The separable value** `sepValue π := ∑_T μ(state = T) · homeEU T (π T)`: the array formula
the program's U4/U9 use. It equals `exAnteValue π` under `ReflectivePolicy ∧ LocalUtility` and
`0 < policyMass π` (`Good.lean`, `exAnteValue_eq_sepValue`), and differs from it in general
(the XOR prior, `WitnessXor.lean`, where the point-level package holds and they differ on a
positive policy; the correlated-points prior, `WitnessCorr.lean`, where they differ on a null
policy).
Source: [[bli-program]] §3.9 U4 (`∑_T μ(T) 𝔼[U | T, a]`), U9(3) (`V(a,b) = 1.5`)
Kind: D
Fidelity: exact (this is the program's formula, named as what it is) -/
def sepValue (π : Policy 𝒟 A) : ℚ := ∑ T, P.stateMass T * P.homeEU T (π T)

/-- `μ(pp · T = a ∧ pp · T' = b)`: the joint mass of two policy points.
Source: [[bli-program-desiderata]] (I); [[bli-program]] §2.8 (`IndependentPoints`)
Kind: D
Fidelity: exact -/
def pairMass (T T' : ↥𝒟) (a b : A) : ℚ :=
  massOf P.μ (fun ω => P.pp ω T = a ∧ P.pp ω T' = b)

/-- `μ(state = S ∧ pp · T = a ∧ pp · T' = b)`.
Source: mandate §3.5 (`IndependentPointsGivenState`)
Kind: D
Fidelity: exact -/
def triMass (S T T' : ↥𝒟) (a b : A) : ℚ :=
  massOf P.μ (fun ω => P.state ω = S ∧ P.pp ω T = a ∧ P.pp ω T' = b)

/-! ## Positivity predicates (mandate §3.1) -/

/-- **D-NDPOL**: every policy point has positive mass.
Source: [[bli-program-desiderata]] D-NDPOL; [[bli-program]] §2.8 (`NDPOL`)
Kind: D
Fidelity: exact -/
def NDPOL : Prop := ∀ (T : ↥𝒟) (a : A), 0 < P.ppMass T a

/-- **NDHOME**: every home cell `state = T ∧ pp · T = a` has positive mass.
Source: mandate §3.1
Kind: D
Fidelity: exact -/
def NDHOME : Prop := ∀ (T : ↥𝒟) (a : A), 0 < P.jointMass T T a

/-- **NDPOLICY**: every policy has positive ex-ante mass.
Source: mandate §3.1
Kind: D
Fidelity: exact -/
def NDPOLICY : Prop := ∀ π : Policy 𝒟 A, 0 < P.policyMass π

/-! ## The decision rules as predicates (mandate §3.2) -/

/-- **One-step choice**: `a` maximizes the one-step value `EU T ·` at `T` (ties allowed).
Note the junk: a null point `pp · T = b` has `EU T b = 0`, so the comparison against it is
against the junk value; `NDPOL` is the honest scope of this predicate (every theorem here that
reads it names the positivity it needs).
Source: bli-soto-b-2-008 (one-step UDT); [[bli-program]] §2.8 (`oneStepUDT`, as a predicate)
Kind: D
Fidelity: exact (predicate in place of the program's `argmax` function) -/
def IsOneStepChoice (T : ↥𝒟) (a : A) : Prop := ∀ b, P.EU T b ≤ P.EU T a

/-- **Updateful choice**: `a` maximizes the home-branch value `homeEU T ·` at `T` (ties allowed).
Note the junk: a null home cell `state = T ∧ pp · T = b` has `homeEU T b = 0`, so the comparison
against it is against the junk value; `NDHOME` is the honest scope of this predicate.
Source: bli-soto-a-011; [[bli-program]] §2.8 (`updateful`, as a predicate)
Kind: D
Fidelity: exact -/
def IsUpdatefulChoice (T : ↥𝒟) (a : A) : Prop := ∀ b, P.homeEU T b ≤ P.homeEU T a

/-- **Prior-optimal policy**: `π` maximizes `exAnteValue` over all policies (the UDT 1.1 rule;
ties allowed). Note the junk: a null policy has `exAnteValue = 0`, so `NDPOLICY` is the honest
scope of this predicate; outside it the predicate is not invariant under adding a constant to `U`
(`WitnessGap.lean`, `Shift.corrShift_junk`). Outside `NDPOLICY` use `IsPriorOptimalOnSupport`.
Source: bli-paper-047 (UDT 1.1); [[bli-program]] §2.8 (`exAnteValue`'s argmax)
Kind: D
Fidelity: exact -/
def IsPriorOptimal (π : Policy 𝒟 A) : Prop := ∀ π', P.exAnteValue π' ≤ P.exAnteValue π

/-- **Prior-optimal among positive-mass policies**: `π` maximizes `exAnteValue` over the policies
of positive ex-ante mass (ties allowed). The junk-free form of `IsPriorOptimal`, for priors without
`NDPOLICY`; under `NDPOLICY` the two agree (`Good.lean`, `isPriorOptimalOnSupport_iff`). Added in
repair round 1 (a new definition, not a change to one of record).
Source: bli-paper-047 (UDT 1.1); mandate T7 (the policy-level junk case)
Kind: D
Fidelity: exact (the argmax over the support of the policy law) -/
def IsPriorOptimalOnSupport (π : Policy 𝒟 A) : Prop :=
  ∀ π', 0 < P.policyMass π' → P.exAnteValue π' ≤ P.exAnteValue π

/-- A **one-step policy**: pointwise a one-step choice.
Source: mandate §3.2
Kind: D
Fidelity: exact -/
def IsOneStepPolicy (π : Policy 𝒟 A) : Prop := ∀ T, P.IsOneStepChoice T (π T)

/-- An **updateful policy**: pointwise an updateful choice.
Source: mandate §3.2
Kind: D
Fidelity: exact -/
def IsUpdatefulPolicy (π : Policy 𝒟 A) : Prop := ∀ T, P.IsUpdatefulChoice T (π T)

/-! ## Structural predicates, point level (mandate §3.5) -/

/-- **Reflective (point level)**: no policy point moves any branch probability —
`μ(state = T | pp · T' = a) = μ(state = T)` whenever the point has positive mass.
Source: [[bli-program]] §2.8 (`Reflective`); bli-slides-037 ("does not impact branch
probabilities, `P(o | o₁ ↦ a) = P(o)`")
Kind: D
Fidelity: exact -/
def Reflective : Prop :=
  ∀ (T T' : ↥𝒟) (a : A), 0 < P.ppMass T' a → P.branchProb T T' a = P.stateMass T

/-- **No cross-branch utility influence (point level)**: for `T' ≠ T`, the value branch `T'`
expects does not depend on which action the point at `T` takes, on positive cells.
Source: [[bli-program]] §2.8 (`NoCrossBranch`); bli-slides-037 ("does not impact other
branches, `𝔼_P(u | o₁ ↦ a, o_{≠1}) = 𝔼_P(u | o_{≠1})`"); bli-soto-a-019 (Notion 511, the
invariance form)
Kind: D
Fidelity: weaker: invariance across the actions at `T`, which the slide's equality with the
point-free value implies and which is Notion 511's form (positivity of both cells in the
predicate, so it never quantifies over junk) -/
def NoCrossBranch : Prop :=
  ∀ (T T' : ↥𝒟) (a b : A), T' ≠ T → 0 < P.jointMass T' T a → 0 < P.jointMass T' T b →
    P.condEU T' T a = P.condEU T' T b

/-! ## Structural predicates, policy level (mandate §3.5) -/

/-- **Reflective (policy level)**: no whole policy moves any branch probability —
`μ(state = T | pp = π) = μ(state = T)` for every positive-mass policy.
Source: mandate §3.5 (`ReflectivePolicy`); [[bli-program]] §3.9 (Good's theorem's hypothesis)
Kind: D
Fidelity: exact -/
def ReflectivePolicy : Prop :=
  ∀ (T : ↥𝒟) (π : Policy 𝒟 A), 0 < P.policyMass π → P.cellMass T π / P.policyMass π = P.stateMass T

/-- **Local utility**: inside branch `T`, the expected utility depends on the policy only through
its value at `T` (the tree-without-entanglement condition of bli-soto-b-2-016 (T1)), on positive
cells.
Source: bli-soto-b-2-016 (T1); mandate §3.5 (`LocalUtility`)
Kind: D
Fidelity: exact -/
def LocalUtility : Prop :=
  ∀ (T : ↥𝒟) (π π' : Policy 𝒟 A), π T = π' T → 0 < P.cellMass T π → 0 < P.cellMass T π' →
    P.cellEU T π = P.cellEU T π'

/-- **Independent points**: distinct policy points are `μ`-independent (product form).
Source: [[bli-program-desiderata]] (I); [[bli-program]] §2.8 (`IndependentPoints`)
Kind: D
Fidelity: exact -/
def IndependentPoints : Prop :=
  ∀ (T T' : ↥𝒟) (a b : A), T ≠ T' → P.pairMass T T' a b = P.ppMass T a * P.ppMass T' b

/-- **Independent points given the state**: distinct policy points are conditionally independent
given `state = S`, in product form `μ(S ∧ a ∧ b) · μ(S) = μ(S ∧ a) · μ(S ∧ b)` (no positivity
needed).
Source: mandate §3.5 (`IndependentPointsGivenState`)
Kind: D
Fidelity: exact -/
def IndependentPointsGivenState : Prop :=
  ∀ (S T T' : ↥𝒟) (a b : A), T ≠ T' →
    P.triMass S T T' a b * P.stateMass S = P.jointMass S T a * P.jointMass S T' b

/-- **Faith given points**: faith holds inside every positive cell `state = T ∧ pp · T' = a`
(the refinement SIST's "branches believe …" premises need; strictly stronger than the `faith`
field, `Basic.lean`).
Source: mandate §3.4; bli-soto-a-011 (within-branch), bli-soto-a-012 (across branches)
Kind: D
Fidelity: exact -/
def FaithGivenPoints : Prop :=
  ∀ (T T' : ↥𝒟) (a : A) (φ : ↥(𝒮.S m)), 0 < P.jointMass T T' a →
    integralOf P.μ (fun ω => ind (P.small ω φ)) (fun ω => P.state ω = T ∧ P.pp ω T' = a) =
      T.1 φ * P.jointMass T T' a

/-! ## Procedures and Policy Fairness (mandate §3.6) -/

/-- **A procedure layer** over a prior: a finite type of *procedures* (the agent's code), the
procedure that runs in each world, its effective behaviour `eff`, and the coherence clause that
the world's policy points are the effective behaviour of the world's procedure. The paper's
Policy Fairness compares procedures with the same effective behaviour; on a bare prior the only
handle on the policy is `pp`, so fairness would be trivial (`trivialLayer`, `Bridges.lean`).
Source: bli-paper-047 (`main.tex` 140–147: "written in C++ rather than Python")
Kind: D
Fidelity: variant: `eff` is a map to finite policies (the paper's `eff` is on codes) -/
structure ProcLayer (P : FiniteBLIPrior 𝒮 m 𝒟 A) where
  /-- The procedures. -/
  Proc : Type
  [fin : Fintype Proc]
  [deq : DecidableEq Proc]
  /-- Which procedure runs in each world. -/
  proc : P.Ω → Proc
  /-- The effective behaviour of a procedure. -/
  eff : Proc → Policy 𝒟 A
  /-- The world's policy points are its procedure's effective behaviour. -/
  pp_eff : ∀ ω, P.pp ω = eff (proc ω)

attribute [instance] ProcLayer.fin ProcLayer.deq

variable {P}

/-- `μ(proc = p)`.
Source: bli-paper-047
Kind: D
Fidelity: exact -/
def ProcLayer.procMass (L : ProcLayer P) (p : L.Proc) : ℚ :=
  massOf P.μ (fun ω => L.proc ω = p)

/-- `𝔼_μ[U | proc = p]` (junk `0` at a null procedure).
Source: bli-paper-047 (`E_p(u | π* = ⌜π⌝)` with `π*` the procedure)
Kind: D
Fidelity: exact -/
def ProcLayer.procEU (L : ProcLayer P) (p : L.Proc) : ℚ :=
  condExp P.μ P.U (fun ω => L.proc ω = p)

/-- **Policy Fairness**: procedures with the same effective behaviour have the same value,
`eff p = eff q → 𝔼[U | proc = p] = 𝔼[U | proc = q]`, on positive-mass procedures.
Source: bli-paper-047 (`main.tex` 145–147, Assumption "Policy Fairness")
Kind: D
Fidelity: exact (finite; ATTRIBUTION-UNVETTED that this is the desiderata's (F)) -/
def PolicyFair (L : ProcLayer P) : Prop :=
  ∀ p q : L.Proc, L.eff p = L.eff q → 0 < L.procMass p → 0 < L.procMass q →
    L.procEU p = L.procEU q

end FiniteBLIPrior

end Cleanroom.Bli.UdtBliCore
