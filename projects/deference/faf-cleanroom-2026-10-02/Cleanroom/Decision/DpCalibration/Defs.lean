import Cleanroom.Found.DpCoreTree.Defs
import Cleanroom.Found.DpCoreTree.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# `dp-calibration`: subjective states and the calibration senses — definitions of record

Package `dp-calibration` (area `decision`), the hub of the decision area: eight packages import
these definitions. This file holds the definitions of record for [[decision-problems-v2]] §1
Definition 2 (the state, on a finite carrier), §3.1 Definitions 8, 9, 11, 12, 13 (strict
observation calibration, masked calibration with its 4×2 variant grid, prior calibration,
zero-respecting procedures, per-run and per-occurrence subjective-state calibration), Appendix B
item 2 (self-transparency, named) and `calibration.md` Definition C1 (the masked variants and the
two null-case readings). Definition 10 (trembles, limit calibration) needs polynomials and lives
in `Limit.lean`; Definitions 14–18 and the device taxonomy in `Theories.lean`.

## Modelling choices, disclosed once here (each also on the declaration)

* **States on a finite atomic carrier.** v2 Definition 2 is stated over a general event algebra
  with designated meets; `dp-worlds-jb` develops that object. Here (the decision area's
  finite-carrier state, plan §0.4 rule 10) a state is a `FinDistr K Ω` on the finite type of
  worlds plus a total desirability function `V : Finset Ω → K` with the averaging axiom as a
  `Prop` field in multiplicative, division-free form on events of positive probability.
  `Fidelity: variant: finite atomic carrier`. **`V` on `P`-null events is junk that no theorem
  may read**: every clause that mentions `V X` carries `0 < P(X)`.
* **No `cf` component.** v2 Remark 3.11 keeps `cf_s` uncalibrated and no calibration sense reads
  it; the counterfactual structure would be a separate `StateCf` (mandate T17, stretch; not
  built — no `Subjective.lean` exists).
* **Points carry no state in `dp-core-tree`**; states are attached as `s : ι → State Ω K`,
  observations as `obs : ι → Finset Ω`, action events as `actEv : (d : ι) → acts d → Finset Ω`,
  the parameter discipline of `dp-core-tree`'s `Recording.lean`.
* **Conditionals are never quotients in a definition.** Lean's `x / 0 = 0` would make an
  unguarded "`P = ν(· | O_d)`" decide the null case the wrong way (no state calibrated at a null
  point). Every calibration clause is stated cross-multiplied under an **explicit positivity
  guard**; `nuCond` and `condExp` exist only as readable abbreviations for theorems that have
  already discharged the guard.
* **"For every queried `d`"** is `∀ d ∈ queried B` (computed from the tree); "a.s." is per leaf
  of positive mass, as in `dp-core-tree` (its findings F2).
* **Definition 9's null case** is fixed as the **vacuity reading** (amendment A5): a queried
  point that no admissible self-model can realize is unconstrained. The letter reading is
  defined beside it (`MaskedOCV v .letter`) and the two are separated in `Examples.lean`.
  `MaskedOC := MaskedOCV .LF .vacuity`.
* **Definition 13's `V`-clauses** are "analogous" in v2; the reading of record: per-run,
  `V_{s_d}(X) = 𝔼_μ[r | {λ ⊨ X} ∩ occ(d)]` where that event has positive mass; per-occurrence,
  `V_{s_d}(X) · 𝔼_μ[#_d 1_{λ⊨X}] = 𝔼_μ[#_d · r · 1_{λ⊨X}]` where the normaliser is positive.
  `Fidelity: variant: V-clause reading`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## The probability of an event under a finite distribution -/

section probOf

variable {Ω : Type} [Fintype Ω]

/-- `P(X) := ∑_{ω ∈ X} P.w ω`: the probability of the event `X` under the weight vector `P`.
On a finite atomic algebra a finitely additive probability *is* its weight vector on atoms.
Source: [[decision-problems-v2]] §1 (`P_s ∈ Δ(𝓐)` on a finite atomic algebra)
Kind: D
Fidelity: variant: finite atomic carrier (the general algebra is `dp-worlds-jb`'s) -/
def probOf (P : FinDistr K Ω) (X : Finset Ω) : K := ∑ ω ∈ X, P.w ω

/-- `0 ≤ P(X)`. Source: none: infrastructure. Kind: L -/
theorem probOf_nonneg (P : FinDistr K Ω) (X : Finset Ω) : 0 ≤ probOf P X :=
  Finset.sum_nonneg fun ω _ => P.nonneg ω

/-- `P(⊤) = 1`. Source: none: infrastructure. Kind: L -/
theorem probOf_univ (P : FinDistr K Ω) : probOf P Finset.univ = 1 := P.sum_one

/-- Finite additivity on disjoint events. Source: none: infrastructure. Kind: L -/
theorem probOf_union [DecidableEq Ω] (P : FinDistr K Ω) {X Y : Finset Ω} (h : Disjoint X Y) :
    probOf P (X ∪ Y) = probOf P X + probOf P Y :=
  Finset.sum_union h

/-- Monotonicity. Source: none: infrastructure. Kind: L -/
theorem probOf_mono (P : FinDistr K Ω) {X Y : Finset Ω} (h : X ⊆ Y) :
    probOf P X ≤ probOf P Y :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ω _ _ => P.nonneg ω

/-- `P(X) ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem probOf_le_one (P : FinDistr K Ω) (X : Finset Ω) : probOf P X ≤ 1 := by
  rw [← probOf_univ P]; exact probOf_mono P (Finset.subset_univ X)

/-- `P(∅) = 0`. Source: none: infrastructure. Kind: L -/
@[simp] theorem probOf_empty (P : FinDistr K Ω) : probOf P ∅ = 0 := by simp [probOf]

/-- The probability of a singleton is its weight. Source: none: infrastructure. Kind: L -/
@[simp] theorem probOf_singleton (P : FinDistr K Ω) (ω : Ω) : probOf P {ω} = P.w ω := by
  simp [probOf]

/-- `P(X)` as a sum with an indicator. Source: none: infrastructure. Kind: L -/
theorem probOf_eq_sum_ite [DecidableEq Ω] (P : FinDistr K Ω) (X : Finset Ω) :
    probOf P X = ∑ ω, if ω ∈ X then P.w ω else 0 := by
  unfold probOf; rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- A point mass gives an event probability `1` or `0` according to membership.
Source: none: infrastructure. Kind: L -/
theorem probOf_pure [DecidableEq Ω] (ω : Ω) (X : Finset Ω) :
    probOf (FinDistr.pure (K := K) ω) X = if ω ∈ X then 1 else 0 := by
  unfold probOf
  simp only [FinDistr.pure_w]
  exact Finset.sum_ite_eq' X ω (fun _ => (1 : K))

end probOf

/-! ## States -/

/-- **A subjective state on a finite atomic carrier** (v2 Definition 2, without `cf`): a
probability `P` on worlds and a desirability `V` on events with the averaging axiom, in
multiplicative form on events of positive probability:
`V(X ∨ Y) · P(X ∨ Y) = P(X) V(X) + P(Y) V(Y)` for disjoint `X, Y` with `P(X), P(Y) > 0`.
`V` is total as a function; its values on `P`-null events are junk that no theorem reads.
Source: [[decision-problems-v2]] §1 Definition 2 (clauses 1–2); Remark 3.11 (`cf_s` stays
uncalibrated, hence omitted here)
Kind: D
Fidelity: variant: finite atomic carrier (v2 Definition 2 on a general event algebra is
`dp-worlds-jb`'s); `cf_s` omitted (no calibration sense reads it) -/
structure State (Ω : Type) [Fintype Ω] [DecidableEq Ω] (K : Type) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] where
  /-- The probability component `P_s`. -/
  P : FinDistr K Ω
  /-- The desirability component `V_s`, total as a function (junk off the support). -/
  V : Finset Ω → K
  /-- The averaging axiom, multiplicative form, on events of positive probability. -/
  avg : ∀ X Y : Finset Ω, Disjoint X Y → 0 < probOf P X → 0 < probOf P Y →
    V (X ∪ Y) * probOf P (X ∪ Y) = probOf P X * V X + probOf P Y * V Y

namespace State

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- `P_s(X)`, the state's probability of an event.
Source: [[decision-problems-v2]] §1 (`P_s`)
Kind: D -/
abbrev pr (s : State Ω K) (X : Finset Ω) : K := probOf s.P X

/-- A state with constant desirability `v`: any `P` with `V ≡ v` satisfies the averaging axiom.
Source: none: infrastructure (states stipulated "certain of a world" in v2 §7 have a constant
desirability wherever it is read)
Kind: D -/
def ofConst (P : FinDistr K Ω) (v : K) : State Ω K where
  P := P
  V _ := v
  avg X Y h _ _ := by rw [probOf_union P h]; ring

/-- The state certain of the world `ω`, with desirability `v` wherever it is read.
Source: [[decision-problems-v2]] §7.1 ("`P_{s_k}` certain of the world `(k, k)` and `V_{s_k}` its
conditional value")
Kind: D -/
def dirac (ω : Ω) (v : K) : State Ω K := ofConst (FinDistr.pure ω) v

/-- `P_{dirac ω v}(X) = [ω ∈ X]`. Source: none: infrastructure. Kind: L -/
theorem dirac_pr (ω : Ω) (v : K) (X : Finset Ω) :
    (dirac ω v).pr X = if ω ∈ X then 1 else 0 := probOf_pure ω X

/-- `V_{dirac ω v} ≡ v`. Source: none: infrastructure. Kind: L -/
@[simp] theorem dirac_V (ω : Ω) (v : K) (X : Finset Ω) : (dirac ω v).V X = v := rfl

/-- `V_{ofConst P v} ≡ v`. Source: none: infrastructure. Kind: L -/
@[simp] theorem ofConst_V (P : FinDistr K Ω) (v : K) (X : Finset Ω) : (ofConst P v).V X = v :=
  rfl

/-- `P_{ofConst P v} = P`. Source: none: infrastructure. Kind: L -/
@[simp] theorem ofConst_P (P : FinDistr K Ω) (v : K) : (ofConst P v).P = P := rfl

/-- A default state (uniform `P`, `V ≡ 0`) on a nonempty carrier, used where a state assignment
must be total but a point is unconstrained.
Source: none: infrastructure
Kind: D -/
def trivial [Nonempty Ω] : State Ω K := ofConst FinDistr.uniform 0

/-- Two states *agree* if their probabilities coincide and their desirabilities coincide on
every event of positive probability — equality modulo the junk values of `V`.
Source: none: infrastructure (v2's "`V` is defined on `P`-non-null events" as an equivalence)
Kind: D -/
def Agree (s t : State Ω K) : Prop :=
  s.P = t.P ∧ ∀ X, 0 < s.pr X → s.V X = t.V X

end State

/-! ## Tree-side quantities read by the calibration clauses -/

section treeSide

variable {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [DecidableEq Ω]

/-- The payoff mass of an event: `∑_{ℓ : λ(ℓ) ⊨ X} μ_{B,C}(ℓ) r(ℓ) = 𝔼_μ[r · 1_{λ ⊨ X}]`.
Source: [[decision-problems-v2]] §3.1 Definition 8 clause 2 (the numerator of the conditional
expectation)
Kind: D -/
def paySum (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) : K :=
  ∑ ℓ ∈ worldEv B X, leafLaw C B ℓ * payoff B ℓ

/-- `ν_{B,C}(X | O) := ν(X ∩ O) / ν(O)` — a readable abbreviation; **`0` at `ν(O) = 0`**, so no
definition of record is stated through it (every clause is cross-multiplied under a guard).
Source: [[decision-problems-v2]] §3.1 Definition 8 (`ν(X ∣ O_d)`)
Kind: D -/
def nuCond (C : Proc ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω) : K :=
  nu C B (X ∩ O) / nu C B O

/-- `𝔼_μ[r | λ ⊨ X] := paySum X / ν(X)` — a readable abbreviation with the same caveat as
`nuCond`.
Source: [[decision-problems-v2]] §3.1 Definition 8 clause 2
Kind: D -/
def condExp (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) : K :=
  paySum C B X / nu C B X

/-- `𝔼_μ[#_d · 1_{λ ⊨ X}]`: the occurrence-weighted mass of an event (Definition 13's
per-occurrence numerator; at `X = ⊤` the normaliser `𝔼_μ[#_d]`).
Source: [[decision-problems-v2]] §3.1 Definition 13
Kind: D -/
def countMass [DecidableEq ι] (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (X : Finset Ω) :
    K :=
  ∑ ℓ ∈ worldEv B X, leafLaw C B ℓ * (count d B ℓ : K)

/-- `𝔼_μ[#_d · r · 1_{λ ⊨ X}]`: the occurrence-weighted payoff mass (the per-occurrence
`V`-clause's numerator, reading of record §3.6 of the mandate).
Source: [[decision-problems-v2]] §3.1 Definition 13 ("`V`-clauses analogous")
Kind: D
Fidelity: variant: V-clause reading -/
def countPay [DecidableEq ι] (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (X : Finset Ω) :
    K :=
  ∑ ℓ ∈ worldEv B X, leafLaw C B ℓ * (count d B ℓ : K) * payoff B ℓ

/-- `paySum` as a sum with an indicator. Source: none: infrastructure. Kind: L -/
theorem paySum_eq_sum_ite (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    paySum C B X = ∑ ℓ, if world B ℓ ∈ X then leafLaw C B ℓ * payoff B ℓ else 0 := by
  unfold paySum worldEv; rw [Finset.sum_filter]

/-- `paySum` is additive on disjoint events. Source: none: infrastructure. Kind: L -/
theorem paySum_union (C : Proc ι acts K) (B : Tree Ω ι acts K) {X Y : Finset Ω}
    (h : Disjoint X Y) : paySum C B (X ∪ Y) = paySum C B X + paySum C B Y := by
  simp only [paySum_eq_sum_ite, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hX : world B ℓ ∈ X
  · have hY : world B ℓ ∉ Y := Finset.disjoint_left.mp h hX
    simp [hX, hY]
  · by_cases hY : world B ℓ ∈ Y <;> simp [hX, hY]

/-- The leaf-world event of `⊤` is every leaf. Source: none: infrastructure. Kind: L -/
@[simp] theorem worldEv_univ [Fintype Ω] (B : Tree Ω ι acts K) :
    worldEv B (Finset.univ : Finset Ω) = Finset.univ := by
  ext ℓ; simp [worldEv]

/-- `ν(X) = ∑_{ω ∈ X} ν({ω})`. Source: none: infrastructure. Kind: L -/
theorem nu_eq_sum_singleton (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    nu C B X = ∑ ω ∈ X, nu C B {ω} := by
  simp only [nu_eq_sum, Finset.mem_singleton]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.sum_ite_eq X (world B ℓ) (fun _ => leafLaw C B ℓ)]

end treeSide

/-! ## The calibrated state and Jeffrey conditioning (T1's lemma-lets) -/

section calibratedState

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)]

/-- The weight vector `ν_{B,C}(· | O)` on worlds, given `0 < ν(O)`.
Source: [[decision-problems-v2]] §3.1 Definition 8 clause 1
Kind: D -/
def nuCondDistr (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω) (h : 0 < nu C B O) :
    FinDistr K Ω where
  w ω := if ω ∈ O then nu C B {ω} / nu C B O else 0
  nonneg ω := by
    split_ifs
    · exact div_nonneg (nu_nonneg C B _) (nu_nonneg C B _)
    · exact le_rfl
  sum_one := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div,
      ← nu_eq_sum_singleton]
    exact div_self h.ne'

/-- `ν(· | O)(X) = ν(X ∩ O) / ν(O)`. Source: none: infrastructure. Kind: L -/
theorem probOf_nuCondDistr (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω)
    (h : 0 < nu C B O) (X : Finset Ω) :
    probOf (nuCondDistr C B O h) X = nu C B (X ∩ O) / nu C B O := by
  unfold probOf nuCondDistr
  simp only
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, ← Finset.sum_div,
    nu_eq_sum_singleton C B (X ∩ O)]

/-- **The strictly calibrated state at an observation `O`** with `0 < ν(O)`: `P := ν(· | O)`,
`V(X) := 𝔼_μ[r | λ ⊨ X ∧ O]`. That this pair *is* a state — the averaging axiom holds — is v2's
one-line remark after Definition 8, proved here as the `avg` field (T1's lemma-let).
Source: [[decision-problems-v2]] §3.1 Definition 8 ("given clause 1 it still satisfies the
averaging axiom automatically")
Kind: P
Fidelity: exact
Hyps: (a) `0 < ν(O)` (the positivity guard of Definition 8) -/
def calibratedState (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω)
    (h : 0 < nu C B O) : State Ω K where
  P := nuCondDistr C B O h
  V X := paySum C B (X ∩ O) / nu C B (X ∩ O)
  avg X Y hXY hX hY := by
    rw [probOf_nuCondDistr] at hX hY ⊢
    rw [probOf_nuCondDistr, probOf_nuCondDistr]
    have hXO : 0 < nu C B (X ∩ O) := by
      by_contra hc
      rw [not_lt] at hc
      have := div_nonpos_of_nonpos_of_nonneg hc (nu_nonneg C B O)
      linarith
    have hYO : 0 < nu C B (Y ∩ O) := by
      by_contra hc
      rw [not_lt] at hc
      have := div_nonpos_of_nonpos_of_nonneg hc (nu_nonneg C B O)
      linarith
    have hdisj : Disjoint (X ∩ O) (Y ∩ O) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hXY)
    have hU : (X ∪ Y) ∩ O = (X ∩ O) ∪ (Y ∩ O) := Finset.union_inter_distrib_right X Y O
    rw [hU, nu_union C B hdisj, paySum_union C B hdisj]
    have hsum : 0 < nu C B (X ∩ O) + nu C B (Y ∩ O) := by linarith
    field_simp

/-- `P` of the calibrated state. Source: none: infrastructure. Kind: L -/
theorem calibratedState_pr (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω)
    (h : 0 < nu C B O) (X : Finset Ω) :
    (calibratedState C B O h).pr X = nu C B (X ∩ O) / nu C B O :=
  probOf_nuCondDistr C B O h X

/-- `V` of the calibrated state. Source: none: infrastructure. Kind: L -/
theorem calibratedState_V (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω)
    (h : 0 < nu C B O) (X : Finset Ω) :
    (calibratedState C B O h).V X = paySum C B (X ∩ O) / nu C B (X ∩ O) := rfl

/-- **Jeffrey conditioning of a state on an event `O`** with `0 < P_s(O)`: `P(· | O)`,
`V(· ∧ O)`. Proved to be a state (the averaging axiom transfers), as Proposition 1 needs.
Source: [[decision-problems-v2]] §3.1 Proposition 1 ("its Jeffrey conditioning —
`P_{s_d} = P_{s°}(· | O_d)` and `V_{s_d} = V_{s°}(· ∧ O_d)`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < P_s(O)` -/
def jeffreyCond (s : State Ω K) (O : Finset Ω) (h : 0 < s.pr O) : State Ω K where
  P :=
    { w := fun ω => if ω ∈ O then s.P.w ω / s.pr O else 0
      nonneg := fun ω => by
        split_ifs
        · exact div_nonneg (s.P.nonneg ω) (probOf_nonneg _ _)
        · exact le_rfl
      sum_one := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div]
        exact div_self h.ne' }
  V X := s.V (X ∩ O)
  avg X Y hXY hX hY := by
    have key : ∀ Z : Finset Ω, probOf
        ({ w := fun ω => if ω ∈ O then s.P.w ω / s.pr O else 0,
           nonneg := fun ω => by
             split_ifs
             · exact div_nonneg (s.P.nonneg ω) (probOf_nonneg _ _)
             · exact le_rfl,
           sum_one := by
             rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
               ← Finset.sum_div]
             exact div_self h.ne' } : FinDistr K Ω) Z = s.pr (Z ∩ O) / s.pr O := by
      intro Z
      unfold probOf
      simp only
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, ← Finset.sum_div]
      rfl
    simp only [key] at hX hY ⊢
    simp only [State.pr] at hX hY ⊢
    have hXO : 0 < probOf s.P (X ∩ O) := by
      by_contra hc
      rw [not_lt] at hc
      have := div_nonpos_of_nonpos_of_nonneg hc (probOf_nonneg s.P O)
      linarith
    have hYO : 0 < probOf s.P (Y ∩ O) := by
      by_contra hc
      rw [not_lt] at hc
      have := div_nonpos_of_nonpos_of_nonneg hc (probOf_nonneg s.P O)
      linarith
    have hdisj : Disjoint (X ∩ O) (Y ∩ O) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hXY)
    have hU : (X ∪ Y) ∩ O = (X ∩ O) ∪ (Y ∩ O) := Finset.union_inter_distrib_right X Y O
    have havg := s.avg (X ∩ O) (Y ∩ O) hdisj hXO hYO
    rw [hU, probOf_union s.P hdisj]
    rw [probOf_union s.P hdisj] at havg
    field_simp
    linear_combination havg

/-- `P` of the Jeffrey-conditioned state. Source: none: infrastructure. Kind: L -/
theorem jeffreyCond_pr (s : State Ω K) (O : Finset Ω) (h : 0 < s.pr O) (X : Finset Ω) :
    (jeffreyCond s O h).pr X = s.pr (X ∩ O) / s.pr O := by
  unfold jeffreyCond State.pr probOf
  simp only
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, ← Finset.sum_div]

/-- `V` of the Jeffrey-conditioned state. Source: none: infrastructure. Kind: L -/
theorem jeffreyCond_V (s : State Ω K) (O : Finset Ω) (h : 0 < s.pr O) (X : Finset Ω) :
    (jeffreyCond s O h).V X = s.V (X ∩ O) := rfl

end calibratedState

/-! ## The calibration senses (Definitions 8, 9, 11, 12, 13; Appendix B item 2) -/

section senses

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

variable (s : ι → State Ω K) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **Clause 1 of Definition 8 at `d` under `C`**, cross-multiplied:
`P_{s_d}(X) · ν(O_d) = ν(X ∧ O_d)` for all `X`.
Source: [[decision-problems-v2]] §3.1 Definition 8 clause 1
Kind: D
Fidelity: exact (cross-multiplied; the positivity guard is carried by `StrictOCAt`) -/
def StrictClause1At (d : ι) : Prop :=
  ∀ X, (s d).pr X * nu C B (obs d) = nu C B (X ∩ obs d)

/-- **Clause 2 of Definition 8 at `d` under `C`**, cross-multiplied and guarded:
for every `X` with `P_{s_d}(X) > 0` and `ν(X ∧ O_d) > 0`,
`V_{s_d}(X) · ν(X ∧ O_d) = ∑_{ℓ : λ(ℓ) ⊨ X ∧ O_d} μ(ℓ) r(ℓ)`.
Source: [[decision-problems-v2]] §3.1 Definition 8 clause 2
Kind: D
Fidelity: exact -/
def StrictClause2At (d : ι) : Prop :=
  ∀ X, 0 < (s d).pr X → 0 < nu C B (X ∩ obs d) →
    (s d).V X * nu C B (X ∩ obs d) = paySum C B (X ∩ obs d)

/-- Both clauses of Definition 8 at `d` under `C` (no positivity guard: the guard is added by
`StrictOCAt`, and `MaskedOCAtV` supplies its own for the self-model).
Source: [[decision-problems-v2]] §3.1 Definition 8
Kind: D -/
def StrictClausesAt (d : ι) : Prop :=
  StrictClause1At s obs C B d ∧ StrictClause2At s obs C B d

/-- **Strict observation calibration at one point** (Definition 8 at `d`): if `ν(O_d) > 0` then
both clauses hold; a point with `ν(O_d) = 0` is unconstrained.
Source: [[decision-problems-v2]] §3.1 Definition 8 ("Queried points with `ν(O_d) = 0` are
unconstrained")
Kind: D
Fidelity: exact -/
def StrictOCAt (d : ι) : Prop :=
  0 < nu C B (obs d) → StrictClausesAt s obs C B d

/-- **Definition 8: `B` is strictly observation-calibrated for `C`** (with states `s`,
observations `obs`): `StrictOCAt` at every queried point.
Source: [[decision-problems-v2]] §3.1 Definition 8
Kind: D
Fidelity: exact (worlds a finite type; "queried" computed from the tree) -/
def StrictOC : Prop := ∀ d ∈ queried B, StrictOCAt s obs C B d

/-- The four masked variants of Definition C1 / Appendix B: local or global self-models,
full-support or plain. `LF` is v2 Definition 9's official choice.
Source: `cf-workflow/phase2-notes/repair/calibration.md` Definition C1; [[decision-problems-v2]]
Appendix B ("The masked family")
Kind: D -/
inductive MaskVariant : Type
  | LF
  | LP
  | GF
  | GP
  deriving DecidableEq

/-- The two readings of Definition 9's clause "requiring `ν_{B,C'}(O_d) > 0`" at a point no
admissible self-model can realize: `vacuity` (the point is free; v2's usage in Proposition 8 and
Corollary 9.1; amendment A5's recommendation) or `letter` (the point is not masked-calibrated).
Source: `calibration.md` Definition C1 (the two readings); `v2-amendments.md` A5, E9
Kind: D -/
inductive NullReading : Type
  | vacuity
  | letter
  deriving DecidableEq

/-- The admissible self-models of variant `v` for `C` at `d`: `LF` — `C[d ↦ m]` with `m`
full-support; `LP` — `C[d ↦ m]` with any `m`; `GF` — any full-support procedure (`dp-core-tree`'s
`Proc.FullSupport`); `GP` — any procedure.
Source: `calibration.md` Definition C1; [[decision-problems-v2]] Definition 9, Appendix B
Kind: D
Fidelity: exact -/
def Admissible (v : MaskVariant) (C : Proc ι acts K) (d : ι) (C' : Proc ι acts K) : Prop :=
  match v with
  | .LF => ∃ m : FinDistr K (acts d), (∀ a, 0 < m.w a) ∧ C' = C.deviate d m
  | .LP => ∃ m : FinDistr K (acts d), C' = C.deviate d m
  | .GF => C'.FullSupport
  | .GP => True

/-- **Masked calibration at `d`, variant `v`, null-case reading `r`**: either some admissible
self-model `C'` realizes `O_d` (`0 < ν_{C'}(O_d)`) and the strict clauses hold for `s_d` under
`C'`, or — only under the `vacuity` reading — no admissible self-model realizes `O_d`. The
existential is *inside* the positivity guard, so a null point never satisfies the first disjunct.
Source: [[decision-problems-v2]] §3.1 Definition 9; `calibration.md` Definition C1
Kind: D
Fidelity: variant: null case parametrised by the reading `r` (A5); v2's letter is `r = .letter` -/
def MaskedOCAtV (v : MaskVariant) (r : NullReading) (d : ι) : Prop :=
  (∃ C', Admissible v C d C' ∧ 0 < nu C' B (obs d) ∧ StrictClausesAt s obs C' B d) ∨
  (r = .vacuity ∧ ∀ C', Admissible v C d C' → nu C' B (obs d) = 0)

/-- Masked calibration, variant `v`, reading `r`, at every queried point.
Source: [[decision-problems-v2]] §3.1 Definition 9; `calibration.md` Definition C1
Kind: D
Fidelity: variant: null case parametrised by the reading (A5) -/
def MaskedOCV (v : MaskVariant) (r : NullReading) : Prop :=
  ∀ d ∈ queried B, MaskedOCAtV s obs C B v r d

/-- **Definition 9 at one point, the definition of record**: local full-support self-models, null
case read as vacuity (amendment A5, matching v2's own usage in Proposition 8 and Corollary 9.1).
Source: [[decision-problems-v2]] §3.1 Definition 9; `v2-amendments.md` A5
Kind: D
Fidelity: variant: null case read as vacuity (A5); v2's letter is `MaskedOCAtV .LF .letter` -/
abbrev MaskedOCAt (d : ι) : Prop := MaskedOCAtV s obs C B .LF .vacuity d

/-- **Definition 9, the definition of record: `B` is masked-calibrated for `C`** — `LF` variant,
vacuity reading, at every queried point.
Source: [[decision-problems-v2]] §3.1 Definition 9; `v2-amendments.md` A5
Kind: D
Fidelity: variant: null case read as vacuity (A5); v2's letter is `MaskedOCV .LF .letter` -/
abbrev MaskedOC : Prop := MaskedOCV s obs C B .LF .vacuity

/-- **Definition 11: prior calibration** of a prior state `s°` for `C` on `B`, unconditioned:
`P_{s°}(X) = ν(X)` for all `X`, and `V_{s°}(X) · ν(X) = 𝔼_μ[r · 1_{λ⊨X}]` for `ν`-non-null `X`.
Source: [[decision-problems-v2]] §3.1 Definition 11
Kind: D
Fidelity: exact (strict form; the masked variant of Definition 11 is not formalized) -/
def PriorCalibrated (s₀ : State Ω K) : Prop :=
  (∀ X, s₀.pr X = nu C B X) ∧ (∀ X, 0 < nu C B X → s₀.V X * nu C B X = paySum C B X)

/-- `A_d^+ := {a ∈ A_d : P_{s_d}(a) > 0}`, the subjectively possible actions at `d`.
Source: [[decision-problems-v2]] §3.1 Definition 12; §4 Definition 17
Kind: D -/
def APlus (d : ι) : Finset (acts d) :=
  Finset.univ.filter fun a => 0 < (s d).pr (actEv d a)

/-- **Definition 12: `C` is zero-respecting** (for the states `s`): at every `d` with
`A_d^+ ≠ ∅`, `supp C(d) ⊆ A_d^+`.
Source: [[decision-problems-v2]] §3.1 Definition 12
Kind: D
Fidelity: exact -/
def ZeroRespecting : Prop :=
  ∀ d, (APlus s actEv d).Nonempty → ∀ a, 0 < (C d).w a → a ∈ APlus s actEv d

/-- Clause 1 of per-run SSC at `d`, cross-multiplied: `P_{s_d}(X) · μ(occ(d)) = μ({λ ⊨ X} ∩ occ(d))`.
Source: [[decision-problems-v2]] §3.1 Definition 13 (per-run)
Kind: D -/
def PerRunClause1At (d : ι) : Prop :=
  ∀ X, (s d).pr X * mass C B (occ d B) = mass C B (worldEv B X ∩ occ d B)

/-- The per-run `V`-clause at `d` (reading of record): for `X` with `P_{s_d}(X) > 0` and
`μ({λ ⊨ X} ∩ occ(d)) > 0`, `V_{s_d}(X) · μ({λ ⊨ X} ∩ occ(d)) = ∑_{ℓ ∈ {λ⊨X} ∩ occ(d)} μ(ℓ) r(ℓ)`.
Source: [[decision-problems-v2]] §3.1 Definition 13 ("`V`-clauses analogous")
Kind: D
Fidelity: variant: V-clause reading -/
def PerRunClause2At (d : ι) : Prop :=
  ∀ X, 0 < (s d).pr X → 0 < mass C B (worldEv B X ∩ occ d B) →
    (s d).V X * mass C B (worldEv B X ∩ occ d B) =
      ∑ ℓ ∈ worldEv B X ∩ occ d B, leafLaw C B ℓ * payoff B ℓ

/-- Both per-run clauses at `d`. Source: [[decision-problems-v2]] Definition 13. Kind: D -/
def PerRunClausesAt (d : ι) : Prop := PerRunClause1At s C B d ∧ PerRunClause2At s C B d

/-- **Per-run SSC at one point** (Definition 13): if `μ(occ(d)) > 0` then both clauses.
Source: [[decision-problems-v2]] §3.1 Definition 13
Kind: D
Fidelity: variant: V-clause reading -/
def PerRunSSCAt (d : ι) : Prop := 0 < mass C B (occ d B) → PerRunClausesAt s C B d

/-- **Definition 13: `B` is per-run SSC for `C`.**
Source: [[decision-problems-v2]] §3.1 Definition 13
Kind: D
Fidelity: variant: V-clause reading -/
def PerRunSSC : Prop := ∀ d ∈ queried B, PerRunSSCAt s C B d

/-- Both per-occurrence clauses at `d`: `P_{s_d}(X) · 𝔼_μ[#_d] = 𝔼_μ[#_d · 1_{λ⊨X}]` for all `X`;
and for `X` with `P_{s_d}(X) > 0` and `𝔼_μ[#_d 1_{λ⊨X}] > 0`,
`V_{s_d}(X) · 𝔼_μ[#_d 1_{λ⊨X}] = 𝔼_μ[#_d · r · 1_{λ⊨X}]`.
Source: [[decision-problems-v2]] §3.1 Definition 13 (per-occurrence)
Kind: D
Fidelity: variant: V-clause reading -/
def PerOccClausesAt (d : ι) : Prop :=
  (∀ X, (s d).pr X * countMass C B d Finset.univ = countMass C B d X) ∧
  (∀ X, 0 < (s d).pr X → 0 < countMass C B d X →
    (s d).V X * countMass C B d X = countPay C B d X)

/-- **Per-occurrence SSC at one point**: if `𝔼_μ[#_d] > 0` then both clauses.
Source: [[decision-problems-v2]] §3.1 Definition 13
Kind: D
Fidelity: variant: V-clause reading -/
def PerOccSSCAt (d : ι) : Prop := 0 < countMass C B d Finset.univ → PerOccClausesAt s C B d

/-- **Definition 13: `B` is per-occurrence SSC for `C`.**
Source: [[decision-problems-v2]] §3.1 Definition 13
Kind: D
Fidelity: variant: V-clause reading -/
def PerOccSSC : Prop := ∀ d ∈ queried B, PerOccSSCAt s C B d

/-- **Self-transparency at `d`** (Appendix B item 2, named): `P_{s_d}(a) = C(d)(a)` for every
action `a` of `d`.
Source: [[decision-problems-v2]] Appendix B item 2; Remark 3.6
Kind: D
Fidelity: exact -/
def SelfTransparent (d : ι) : Prop :=
  ∀ a, (s d).pr (actEv d a) = (C d).w a

end senses

end Cleanroom.Decision.DpCalibration
