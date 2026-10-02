import Cleanroom.Decision.DpCalibration.Defs
import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpCausalConsist.Truncate

/-!
# `dp-causal-consist`: definitions of record on the state side

Representation of record (mandate §3), disclosed choice by choice:

* **§3.2 States with a counterfactual component.** `dp-calibration`'s `State Ω K` has no `cf`.
  `CfState Ω K` pairs a state with `cf : (A : Finset Ω) → A.Nonempty → State Ω K` and *success*
  `(cf A h).pr A = 1` — the finite-carrier twin of `dp-worlds-jb`'s `JBState`. A supposition is a
  `State`; its two fields are v2's `(P^a, V^a)`.
* **§3.3 The bridge ℚ → ℝ.** The catalogue trees and their calibrated states live over `ℚ`; FAF's
  `Distr` is real. `State.castℝ` casts a `ℚ`-state, `State.toDistr` reads an `ℝ`-state's `P` as a
  FAF `Distr`; `toDistr_prob`/`castℝ_pr` are the seam (kind `L`).
* **§3.4 Interventional suppositions.** `expState Q u` is the state with probability `Q` and
  desirability `𝔼_Q[u | X]`; `cfG Γ m u a := expState (Γ.truncate m a) u` is `cf^G_s(a)` for a
  supervenient payoff `u` (v2 Remark 3.5).
* **§3.5 Mixtures.** `mixState π t` is the finite Jeffrey mixture. Its desirability reads each
  component on that component's support (`(t i).V (X ∩ supp (t i))`): v2 defines `V` only on
  non-null events, and a Lean `State` may carry arbitrary junk on null events, under which the
  naive formula `∑ π_i P_i(X) V_i(X) / P(X)` fails the averaging axiom. Two-point example: on
  `Ω = {x, y}`, `t₁ = (δ_x, V₁)` with `V₁{x} = 0`, `V₁{x, y} = 100` is a legal `State` (the axiom
  binds only disjoint *positive* pairs), `t₂ = (δ_y, 0)`; the fair naive mixture has
  `V(⊤)·P(⊤) = 50 ≠ 0 = P{x}V{x} + P{y}V{y}` (`mixState_naive_fails` in `MixJunk.lean`), while
  `mixState` gives `V(⊤) = 0` (`mixState_junk_V_univ`). On support-regular components
  (`SuppRegular`) it is the mandate's formula (`mixState_V_of_suppRegular`).
* **§3.6 Axiom NR.** An exogenous designation is a map `exo : Ω → E` with cells `cell exo e`;
  `NRAt` is clauses (i)–(ii) with the `V`-clause guarded by the positivity of the event it is
  read at. `kPart s A exo` is the K-partition state `∑_e P(e) P(· | A, e)`, a *separate*
  definition: on a cell with `P(e) > 0 = P(A ∧ e)` (where the sum is not a probability) it falls
  back to `P(· | e)`, and on a null cell to `s`; `NR.lean` proves when NR forces it.
* **§3.7 Definition PR.** `Responsive C B d X := ∃ a b, ν_{C[d↦a]}(X) ≠ ν_{C[d↦b]}(X)` over pure
  deviations, as the wiki writes it.
* **T2(iv).** `TCdtAt` is `T_CDT` at a point with the causal argmax over *all* of `A_d` (null acts
  included, filled by the CPD); the coincidence with `TEdtAt` (argmax over `A_d^+`) is `Collapse.lean`.
* **T14.** `LLCAntecedent`/`LLCObeys`: the Law of Logical Causality's antecedent ("conditioning on
  `X` changes own-act probability") and the "treat as downstream" reading "the supposition moves `X`".
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

/-! ## The bridge ℚ → ℝ -/

section cast

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The real-valued copy of a rational `FinDistr`. Source: none: infrastructure. Kind: D -/
def FinDistr.castℝ (P : FinDistr ℚ Ω) : FinDistr ℝ Ω where
  w ω := (P.w ω : ℝ)
  nonneg ω := by exact_mod_cast P.nonneg ω
  sum_one := by exact_mod_cast P.sum_one

/-- `probOf` commutes with the cast. Source: none: infrastructure. Kind: L -/
theorem probOf_castℝ (P : FinDistr ℚ Ω) (X : Finset Ω) :
    probOf (FinDistr.castℝ P) X = ((probOf P X : ℚ) : ℝ) := by
  unfold probOf FinDistr.castℝ; push_cast; rfl

/-- **The ℚ → ℝ cast of a state**: both components cast; the averaging axiom transfers.
Source: mandate §3.3 (the seam between the `ℚ` trees and FAF's real `Distr`)
Kind: L -/
def State.castℝ (s : State Ω ℚ) : State Ω ℝ where
  P := FinDistr.castℝ s.P
  V X := (s.V X : ℝ)
  avg X Y h hX hY := by
    rw [probOf_castℝ] at hX hY
    rw [probOf_castℝ, probOf_castℝ, probOf_castℝ]
    have := s.avg X Y h (by exact_mod_cast hX) (by exact_mod_cast hY)
    exact_mod_cast this

/-- `P` of the cast state. Source: none: infrastructure. Kind: L -/
theorem State.castℝ_pr (s : State Ω ℚ) (X : Finset Ω) :
    (State.castℝ s).pr X = ((s.pr X : ℚ) : ℝ) :=
  probOf_castℝ s.P X

/-- `V` of the cast state. Source: none: infrastructure. Kind: L -/
@[simp] theorem State.castℝ_V (s : State Ω ℚ) (X : Finset Ω) :
    (State.castℝ s).V X = (s.V X : ℝ) := rfl

/-- **A real state's probability as a FAF `Distr`.**
Source: mandate §3.3 (`State.toDistr`)
Kind: D -/
def State.toDistr (s : State Ω ℝ) : Distr Ω where
  mass := s.P.w
  nonneg := s.P.nonneg
  sum_eq_one := s.P.sum_one

/-- Mass of `toDistr`. Source: none: infrastructure. Kind: L -/
@[simp] theorem State.toDistr_mass (s : State Ω ℝ) (ω : Ω) : (State.toDistr s).mass ω = s.P.w ω :=
  rfl

/-- **The seam**: `(s.toDistr).prob ↑X = P_s(X)`.
Source: mandate §3.3 (`toDistr_prob`)
Kind: L -/
theorem State.toDistr_prob (s : State Ω ℝ) (X : Finset Ω) :
    (State.toDistr s).prob (↑X : Set Ω) = s.pr X := by
  rw [prob_eq_sum_ite, State.pr, probOf_eq_sum_ite]
  rfl

/-- `toDistr` of a filter-event. Source: none: infrastructure. Kind: L -/
theorem State.toDistr_prob_setOf (s : State Ω ℝ) (p : Ω → Prop) [DecidablePred p] :
    (State.toDistr s).prob {ω | p ω} = s.pr (Finset.univ.filter p) := by
  rw [prob_setOf_eq_sum_ite, State.pr, probOf_eq_sum_ite]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- FAF's `condProb` on `toDistr` is the state's conditional probability.
Source: none: infrastructure
Kind: L -/
theorem State.toDistr_condProb (s : State Ω ℝ) (X A : Finset Ω) :
    (State.toDistr s).condProb ↑X ↑A = s.pr (X ∩ A) / s.pr A := by
  unfold Distr.condProb
  rw [← Finset.coe_inter, State.toDistr_prob, State.toDistr_prob]

end cast

/-! ## States from a distribution and a payoff; support regularity -/

section expState

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **The state with law `Q` and desirability `𝔼_Q[u | X]`** (`V(X) := ∑_{x ∈ X} Q(x) u(x) / Q(X)`,
junk `0` at `Q(X) = 0`). The averaging axiom is the additivity of the numerator.
Source: [[learning-cdt-renderings]] Definition 24 (`V^{G,a}`, the supposed desirability read off
the supposed law and a supervenient payoff `u`; v2 Remark 3.5)
Kind: D
Fidelity: exact for supervenient payoffs (`r = u ∘ λ`); leaf-attached payoffs are open item (4) -/
noncomputable def expState (Q : Distr Ω) (u : Ω → ℝ) : State Ω ℝ where
  P := ⟨Q.mass, Q.nonneg, Q.sum_eq_one⟩
  V X := (∑ x ∈ X, Q.mass x * u x) / ∑ x ∈ X, Q.mass x
  avg X Y h hX hY := by
    simp only [probOf] at hX hY ⊢
    rw [Finset.sum_union h, Finset.sum_union h]
    have hsum : 0 < ∑ x ∈ X, Q.mass x + ∑ x ∈ Y, Q.mass x := by linarith
    field_simp

/-- `P` of `expState`. Source: none: infrastructure. Kind: L -/
theorem expState_pr (Q : Distr Ω) (u : Ω → ℝ) (X : Finset Ω) :
    (expState Q u).pr X = Q.prob ↑X := by
  rw [prob_eq_sum_ite, State.pr, probOf_eq_sum_ite]
  rfl

/-- `V` of `expState`. Source: none: infrastructure. Kind: L -/
theorem expState_V (Q : Distr Ω) (u : Ω → ℝ) (X : Finset Ω) :
    (expState Q u).V X = (∑ x ∈ X, Q.mass x * u x) / ∑ x ∈ X, Q.mass x := rfl

/-- `toDistr` of `expState` is `Q`. Source: none: infrastructure. Kind: L -/
theorem expState_toDistr (Q : Distr Ω) (u : Ω → ℝ) : State.toDistr (expState Q u) = Q := by
  apply Distr.ext; rfl

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The support of a state: the worlds of positive probability.
Source: none: infrastructure
Kind: D -/
def supp (s : State Ω K) : Finset Ω := Finset.univ.filter fun ω => 0 < s.P.w ω

/-- Membership in the support. Source: none: infrastructure. Kind: L -/
theorem mem_supp (s : State Ω K) (ω : Ω) : ω ∈ supp s ↔ 0 < s.P.w ω := by simp [supp]

/-- `P_s(X ∩ supp s) = P_s(X)`. Source: none: infrastructure. Kind: L -/
theorem pr_inter_supp (s : State Ω K) (X : Finset Ω) : s.pr (X ∩ supp s) = s.pr X := by
  unfold State.pr probOf
  rw [← Finset.sum_filter_add_sum_filter_not X (fun ω => ω ∈ supp s)]
  have h0 : ∑ ω ∈ X.filter (fun ω => ω ∉ supp s), s.P.w ω = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    rw [Finset.mem_filter, mem_supp, not_lt] at hω
    exact le_antisymm hω.2 (s.P.nonneg ω)
  rw [h0, add_zero, Finset.filter_mem_eq_inter]

/-- `P_s(X) = 0` iff `X` misses the support. Source: none: infrastructure. Kind: L -/
theorem pr_eq_zero_iff (s : State Ω K) (X : Finset Ω) : s.pr X = 0 ↔ X ∩ supp s = ∅ := by
  unfold State.pr probOf
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => s.P.nonneg ω)]
  constructor
  · intro h
    ext ω
    simp only [Finset.mem_inter, mem_supp, Finset.notMem_empty, iff_false, not_and, not_lt]
    intro hX; exact (h ω hX).le
  · intro h ω hX
    have : ω ∉ supp s := fun hs => by
      have : ω ∈ X ∩ supp s := Finset.mem_inter.mpr ⟨hX, hs⟩
      rw [h] at this; exact Finset.notMem_empty ω this
    rw [mem_supp, not_lt] at this
    exact le_antisymm this (s.P.nonneg ω)

/-- **Support regularity**: the desirability reads only the support (`V(X ∩ supp) = V(X)`).
Every state built from a law and a payoff has it; a bare `State` need not (its `V` is junk on
null events).
Source: none: infrastructure (v2 Definition 2: "`V` is defined on non-null events")
Kind: D -/
def SuppRegular (s : State Ω K) : Prop := ∀ X, s.V (X ∩ supp s) = s.V X

/-- `expState` is support-regular. Source: none: infrastructure. Kind: L -/
theorem expState_suppRegular (Q : Distr Ω) (u : Ω → ℝ) : SuppRegular (expState Q u) := by
  intro X
  simp only [expState_V]
  have key : ∀ f : Ω → ℝ, ∑ x ∈ X ∩ supp (expState Q u), Q.mass x * f x
      = ∑ x ∈ X, Q.mass x * f x := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not X (fun ω => ω ∈ supp (expState Q u))]
    have h0 : ∑ ω ∈ X.filter (fun ω => ω ∉ supp (expState Q u)), Q.mass ω * f ω = 0 := by
      apply Finset.sum_eq_zero
      intro ω hω
      rw [Finset.mem_filter, mem_supp, not_lt] at hω
      have : Q.mass ω = 0 := le_antisymm hω.2 (Q.nonneg ω)
      rw [this, zero_mul]
    rw [h0, add_zero, Finset.filter_mem_eq_inter]
  have key1 : ∑ x ∈ X ∩ supp (expState Q u), Q.mass x = ∑ x ∈ X, Q.mass x := by
    have := key (fun _ => 1); simpa using this
  rw [key, key1]

end expState

/-! ## The interventional supposition of a causal structure -/

section cfG

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)]

/-- **`cf^G_s(a)` (Definition 24)**: the interventional supposition of `a` under the structure
`Γ` — the truncated law `do(m := a)` with desirability `𝔼[u | ·]` for a supervenient payoff `u`.
Source: [[learning-cdt-renderings]] Definition 24 ("`cf^G_s(a) := (P^{G,a}, V^{G,a})` by
truncated factorization")
Kind: D
Fidelity: exact (supervenient payoff) -/
noncomputable def cfG (Γ : CausalStructure Val) (m : V) (u : Pt Val → ℝ) (a : Val m) :
    State (Pt Val) ℝ :=
  expState (Γ.truncate m a) u

/-- The act event `{x | x m = a}` as a finset. Source: none: infrastructure. Kind: D -/
def actEvCoord (m : V) (a : Val m) : Finset (Pt Val) := Finset.univ.filter fun x => x m = a

/-- Membership in `actEvCoord`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_actEvCoord (m : V) (a : Val m) (x : Pt Val) :
    x ∈ actEvCoord m a ↔ x m = a := by simp [actEvCoord]

/-- The coerced act event is the set `{x | x m = a}`. Source: none: infrastructure. Kind: L -/
theorem coe_actEvCoord (m : V) (a : Val m) :
    (↑(actEvCoord m a) : Set (Pt Val)) = {x | x m = a} := by
  ext x; simp

/-- **Success of `cf^G`**: `P^{G,a}(x_m = a) = 1`.
Source: [[decision-problems-v2]] Definition 2 (success); mandate T1 (`cfG_success`)
Kind: L -/
theorem cfG_success (Γ : CausalStructure Val) (m : V) (u : Pt Val → ℝ) (a : Val m) :
    (cfG Γ m u a).pr (actEvCoord m a) = 1 := by
  rw [cfG, expState_pr, coe_actEvCoord]
  exact truncate_prob_act Γ.acyclic Γ.φ m a

/-- `P` of `cf^G` is the truncated law. Source: none: infrastructure. Kind: L -/
theorem cfG_toDistr (Γ : CausalStructure Val) (m : V) (u : Pt Val → ℝ) (a : Val m) :
    State.toDistr (cfG Γ m u a) = Γ.truncate m a :=
  expState_toDistr _ _

end cfG

/-! ## States with a counterfactual component -/

section cfState

variable (Ω : Type) [Fintype Ω] [DecidableEq Ω] (K : Type) [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- **A state with a counterfactual component** (v2 Definition 2 on a finite carrier): a state
`s` and, for every nonempty event `A`, a supposition `cf A` — a state — with *success*
`P_{cf A}(A) = 1`. The finite-carrier twin of `dp-worlds-jb`'s `JBState`.
Source: [[decision-problems-v2]] §1 Definition 2 (`cf_s`, success); mandate §3.2
Kind: D
Fidelity: variant: finite atomic carrier; `cf` total on nonempty events -/
structure CfState where
  /-- The state. -/
  s : State Ω K
  /-- The suppositions, one per nonempty event. -/
  cf : (A : Finset Ω) → A.Nonempty → State Ω K
  /-- Success: the supposition of `A` is certain of `A`. -/
  success : ∀ A h, (cf A h).pr A = 1

end cfState

/-! ## Finite mixtures of states (Definition 25's Jeffrey mixture) -/

section mixState

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {ι' : Type} [Fintype ι']

/-- The mixed law `∑_i π_i P_i`. Source: none: infrastructure. Kind: D -/
def mixDistr (π : FinDistr K ι') (t : ι' → State Ω K) : FinDistr K Ω where
  w ω := ∑ i, π.w i * (t i).P.w ω
  nonneg ω := Finset.sum_nonneg fun i _ => mul_nonneg (π.nonneg i) ((t i).P.nonneg ω)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinDistr.sum_one, mul_one]
    exact π.sum_one

/-- `probOf` of the mixed law. Source: none: infrastructure. Kind: L -/
theorem probOf_mixDistr (π : FinDistr K ι') (t : ι' → State Ω K) (X : Finset Ω) :
    probOf (mixDistr π t) X = ∑ i, π.w i * (t i).pr X := by
  unfold probOf mixDistr State.pr probOf
  simp only
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

/-- **The additivity of a component's numerator read on its support**: for disjoint `X`, `Y`,
`P(X ∪ Y) V((X ∪ Y) ∩ S) = P(X) V(X ∩ S) + P(Y) V(Y ∩ S)` with `S` the support, with no
positivity hypothesis (a null summand contributes `0` and does not move the union's value).
Source: none: infrastructure (the averaging axiom, made total by reading `V` on the support)
Kind: L -/
theorem pr_mul_V_inter_supp_union (s : State Ω K) {X Y : Finset Ω} (h : Disjoint X Y) :
    s.pr (X ∪ Y) * s.V ((X ∪ Y) ∩ supp s)
      = s.pr X * s.V (X ∩ supp s) + s.pr Y * s.V (Y ∩ supp s) := by
  have hU : (X ∪ Y) ∩ supp s = (X ∩ supp s) ∪ (Y ∩ supp s) := Finset.union_inter_distrib_right X Y _
  have hdisj : Disjoint (X ∩ supp s) (Y ∩ supp s) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left h)
  have hprU : probOf s.P (X ∪ Y) = probOf s.P X + probOf s.P Y := probOf_union s.P h
  have hXS : probOf s.P (X ∩ supp s) = probOf s.P X := pr_inter_supp s X
  have hYS : probOf s.P (Y ∩ supp s) = probOf s.P Y := pr_inter_supp s Y
  have hUS : probOf s.P ((X ∪ Y) ∩ supp s) = probOf s.P (X ∪ Y) := pr_inter_supp s (X ∪ Y)
  simp only [State.pr]
  rcases (probOf_nonneg s.P X).lt_or_eq with hX | hX <;>
    rcases (probOf_nonneg s.P Y).lt_or_eq with hY | hY
  · have := s.avg (X ∩ supp s) (Y ∩ supp s) hdisj (by rw [hXS]; exact hX) (by rw [hYS]; exact hY)
    rw [hXS, hYS, ← hU, hUS] at this
    rw [mul_comm]; exact this
  · have hYe : Y ∩ supp s = ∅ := (pr_eq_zero_iff s Y).mp hY.symm
    rw [hU, hYe, Finset.union_empty, hprU, ← hY, add_zero, zero_mul, add_zero]
  · have hXe : X ∩ supp s = ∅ := (pr_eq_zero_iff s X).mp hX.symm
    rw [hU, hXe, Finset.empty_union, hprU, ← hX, zero_add, zero_mul, zero_add]
  · have hXe : X ∩ supp s = ∅ := (pr_eq_zero_iff s X).mp hX.symm
    rw [hU, hXe, Finset.empty_union, hprU, ← hX, ← hY]; ring

/-- **The finite Jeffrey mixture of states (Definition 25)**: `P := ∑_i π_i P_i` and
`V(X) := ∑_i π_i P_i(X) V_i(X ∩ supp_i) / P(X)` (junk at `P(X) = 0`), the averaging axiom proved.
Each component's desirability is read on that component's support (module docstring).
Source: [[defining-cdt-in-the-learning-setting]] Definition 25 ("pairs mixed as Jeffrey states:
`P = ∫ P^{G,a} dπ`, `V(X) = ∫ P^{G,a}(X) V^{G,a}(X) dπ / P(X)`"); mandate §3.5
Kind: L
Fidelity: variant: finite support; components read on their supports -/
def mixState (π : FinDistr K ι') (t : ι' → State Ω K) : State Ω K where
  P := mixDistr π t
  V X := (∑ i, π.w i * (t i).pr X * (t i).V (X ∩ supp (t i))) / ∑ i, π.w i * (t i).pr X
  avg X Y h hX hY := by
    rw [probOf_mixDistr] at hX hY
    rw [probOf_mixDistr, probOf_mixDistr, probOf_mixDistr]
    have hN : ∑ i, π.w i * (t i).pr (X ∪ Y) * (t i).V ((X ∪ Y) ∩ supp (t i))
        = ∑ i, π.w i * (t i).pr X * (t i).V (X ∩ supp (t i))
          + ∑ i, π.w i * (t i).pr Y * (t i).V (Y ∩ supp (t i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := pr_mul_V_inter_supp_union (t i) h
      calc π.w i * (t i).pr (X ∪ Y) * (t i).V ((X ∪ Y) ∩ supp (t i))
          = π.w i * ((t i).pr (X ∪ Y) * (t i).V ((X ∪ Y) ∩ supp (t i))) := by ring
        _ = π.w i * ((t i).pr X * (t i).V (X ∩ supp (t i))
              + (t i).pr Y * (t i).V (Y ∩ supp (t i))) := by rw [this]
        _ = _ := by ring
    have hM : ∑ i, π.w i * (t i).pr (X ∪ Y) = ∑ i, π.w i * (t i).pr X + ∑ i, π.w i * (t i).pr Y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [State.pr, probOf_union (t i).P h]; ring
    rw [hN, hM]
    have hsum : 0 < ∑ i, π.w i * (t i).pr X + ∑ i, π.w i * (t i).pr Y := by linarith
    field_simp

/-- `P` of the mixture. Source: none: infrastructure. Kind: L -/
theorem mixState_pr (π : FinDistr K ι') (t : ι' → State Ω K) (X : Finset Ω) :
    (mixState π t).pr X = ∑ i, π.w i * (t i).pr X :=
  probOf_mixDistr π t X

/-- `V` of the mixture. Source: none: infrastructure. Kind: L -/
theorem mixState_V (π : FinDistr K ι') (t : ι' → State Ω K) (X : Finset Ω) :
    (mixState π t).V X
      = (∑ i, π.w i * (t i).pr X * (t i).V (X ∩ supp (t i))) / ∑ i, π.w i * (t i).pr X := rfl

/-- **The mandate's mixture formula** on support-regular components:
`V(X) = ∑_i π_i P_i(X) V_i(X) / P(X)`.
Source: [[defining-cdt-in-the-learning-setting]] Definition 25; mandate §3.5
Kind: L -/
theorem mixState_V_of_suppRegular (π : FinDistr K ι') (t : ι' → State Ω K)
    (hreg : ∀ i, SuppRegular (t i)) (X : Finset Ω) :
    (mixState π t).V X
      = (∑ i, π.w i * (t i).pr X * (t i).V X) / ∑ i, π.w i * (t i).pr X := by
  rw [mixState_V]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hreg i X]

/-- **The averaging axiom of the mixture** in v2's form, restated outside the structure.
Source: [[decision-problems-v2]] Definition 2 (the averaging axiom); mandate T5 (`mixState_avg`)
Kind: L -/
theorem mixState_avg (π : FinDistr K ι') (t : ι' → State Ω K) (X Y : Finset Ω)
    (h : Disjoint X Y) (hX : 0 < (mixState π t).pr X) (hY : 0 < (mixState π t).pr Y) :
    (mixState π t).V (X ∪ Y) * (mixState π t).pr (X ∪ Y)
      = (mixState π t).pr X * (mixState π t).V X + (mixState π t).pr Y * (mixState π t).V Y :=
  (mixState π t).avg X Y h hX hY

/-- The mixture's success on an event every component is certain of.
Source: none: infrastructure
Kind: L -/
theorem mixState_pr_eq_one (π : FinDistr K ι') (t : ι' → State Ω K) (A : Finset Ω)
    (h : ∀ i, (t i).pr A = 1) : (mixState π t).pr A = 1 := by
  rw [mixState_pr]
  simp_rw [h, mul_one]
  exact π.sum_one

end mixState

/-! ## Exogenous designations, Axiom NR, the K-partition state -/

section nr

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {E : Type} [Fintype E] [DecidableEq E]

/-- The cell `{ω | exo ω = e}` of an exogenous designation.
Source: [[non-responsiveness]] "Axiom NR" (`𝓔_exo`, generated by a coordinate/partition);
mandate §3.6
Kind: D -/
def cell (exo : Ω → E) (e : E) : Finset Ω := Finset.univ.filter fun ω => exo ω = e

/-- Membership in a cell. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_cell (exo : Ω → E) (e : E) (ω : Ω) : ω ∈ cell exo e ↔ exo ω = e := by
  simp [cell]

/-- The cells are disjoint. Source: none: infrastructure. Kind: L -/
theorem cell_disjoint (exo : Ω → E) {e e' : E} (h : e ≠ e') :
    Disjoint (cell exo e) (cell exo e') := by
  rw [Finset.disjoint_left]
  intro ω h1 h2
  rw [mem_cell] at h1 h2
  exact h (h1.symm.trans h2)

/-- Summing over the cells is summing over `Ω`. Source: none: infrastructure. Kind: L -/
theorem sum_cells (exo : Ω → E) (f : Ω → K) : ∑ e, ∑ ω ∈ cell exo e, f ω = ∑ ω, f ω := by
  unfold cell
  exact Finset.sum_fiberwise Finset.univ exo f

/-- A state's probability is the sum of its cell probabilities.
Source: none: infrastructure
Kind: L -/
theorem pr_eq_sum_cells (s : State Ω K) (exo : Ω → E) (X : Finset Ω) :
    s.pr X = ∑ e, s.pr (X ∩ cell exo e) := by
  simp only [State.pr, probOf]
  have h1 : ∀ e, ∑ ω ∈ X ∩ cell exo e, s.P.w ω
      = ∑ ω ∈ cell exo e, if ω ∈ X then s.P.w ω else 0 := by
    intro e
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  simp_rw [h1]
  rw [sum_cells exo, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The distribution of the cells under a state: `e ↦ P_s(cell e)`.
Source: [[non-responsiveness]] "Axiom NR" (the weights `P_s(e)` of the K-partition sum)
Kind: D -/
def cellDistr (s : State Ω K) (exo : Ω → E) : FinDistr K E where
  w e := s.pr (cell exo e)
  nonneg e := probOf_nonneg _ _
  sum_one := by
    have := pr_eq_sum_cells s exo Finset.univ
    simp only [Finset.univ_inter] at this
    rw [← this, State.pr, probOf_univ]

/-- **Axiom NR (exogenous rigidity) at a point** for a state with a counterfactual component,
action events `actEv` and an exogenous designation `exo`: for every act `a` with nonempty event,
(i) `P^a(e) = P(e)` for every cell; (ii) cross-multiplied `P^a(· | e) = P(· | a ∧ e)` wherever
`P(a ∧ e) > 0`; (iii) `V^a(X ∧ a ∧ e) = V(X ∧ a ∧ e)` wherever that event is `P`-positive.
Source: [[non-responsiveness]] "Axiom NR for the next version" (l. 69: "(i) `P^a_s(e) = P_s(e)`
for all `e ∈ 𝓔_exo`; (ii) `P^a_s(· | e) = P_s(· | a ∧ e)` and `V^a_s(X ∧ a ∧ e) = V_s(X ∧ a ∧ e)`
wherever `P_s(a ∧ e) > 0`"); mandate §3.6
Kind: D
Fidelity: variant: the `V`-clause is guarded by `P_s(X ∧ a ∧ e) > 0` (the event it is read at),
not only `P_s(a ∧ e) > 0` — the value of `V` at a null event is junk on both sides -/
def NRAt {A : Type} (t : CfState Ω K) (actEv : A → Finset Ω) (exo : Ω → E) : Prop :=
  ∀ a (h : (actEv a).Nonempty),
    (∀ e, (t.cf (actEv a) h).pr (cell exo e) = t.s.pr (cell exo e)) ∧
    (∀ e X, 0 < t.s.pr (actEv a ∩ cell exo e) →
      (t.cf (actEv a) h).pr (X ∩ cell exo e) * t.s.pr (actEv a ∩ cell exo e)
        = (t.cf (actEv a) h).pr (cell exo e) * t.s.pr (X ∩ actEv a ∩ cell exo e)) ∧
    (∀ e X, 0 < t.s.pr (X ∩ actEv a ∩ cell exo e) →
      (t.cf (actEv a) h).V (X ∩ actEv a ∩ cell exo e) = t.s.V (X ∩ actEv a ∩ cell exo e))

/-- The component of the K-partition state at a cell: `P(· | A ∧ e)` where that is defined; on
a cell with `P(e) > 0 = P(A ∧ e)` the fallback `P(· | e)`; on a null cell `s` itself (weight `0`).
Source: mandate §3.6, §6.4 (the cells on which the K-partition sum is not a probability)
Kind: D -/
noncomputable def kPartComp (s : State Ω K) (A : Finset Ω) (exo : Ω → E) (e : E) : State Ω K :=
  if h1 : 0 < s.pr (A ∩ cell exo e) then jeffreyCond s (A ∩ cell exo e) h1
  else if h2 : 0 < s.pr (cell exo e) then jeffreyCond s (cell exo e) h2 else s

/-- **The K-partition state** `∑_e P(e) · P(· | A ∧ e)` (Lewis–Skyrms dependency hypotheses on the
Jeffrey–Bolker chassis), as a Jeffrey mixture over the cells with the fallbacks of `kPartComp`.
A separate definition from `NRAt`; `NR.lean` proves when NR forces `cf A = kPart`.
Source: [[non-responsiveness]] "Axiom NR" (l. 69: "Hence `P^a_s = ∑_e P_s(e) P_s(· | a, e)`");
mandate §3.6, T8
Kind: D
Fidelity: variant: fallbacks on the cells where the printed sum is not a probability -/
noncomputable def kPart (s : State Ω K) (A : Finset Ω) (exo : Ω → E) : State Ω K :=
  mixState (cellDistr s exo) (kPartComp s A exo)

/-- `P` of the K-partition state on the good cells: `∑_e P(e) P(X ∧ A ∧ e)/P(A ∧ e)` when every
positive cell meets `A` positively.
Source: [[non-responsiveness]] "Axiom NR" (the K-partition sum)
Kind: L -/
theorem kPart_pr_of_pos (s : State Ω K) (A : Finset Ω) (exo : Ω → E)
    (hpos : ∀ e, 0 < s.pr (cell exo e) → 0 < s.pr (A ∩ cell exo e)) (X : Finset Ω) :
    (kPart s A exo).pr X
      = ∑ e, s.pr (cell exo e) * (s.pr (X ∩ (A ∩ cell exo e)) / s.pr (A ∩ cell exo e)) := by
  rw [kPart, mixState_pr]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases (probOf_nonneg s.P (cell exo e)).lt_or_eq with he | he
  · have h1 := hpos e he
    show s.pr (cell exo e) * (kPartComp s A exo e).pr X = _
    rw [kPartComp, dif_pos h1, jeffreyCond_pr]
  · have he' : s.pr (cell exo e) = 0 := he.symm
    show s.pr (cell exo e) * (kPartComp s A exo e).pr X = _
    rw [he']; simp

end nr

/-! ## Definition PR, `T_CDT` at a point, the LLC predicates -/

section pr

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- **Policy-responsiveness (Definition PR)**: `X` is policy-responsive at `d` under `C` if the
all-instance pure deviation of the label at `d` moves its objective frequency:
`∃ a b, ν_{C[d ↦ a]}(X) ≠ ν_{C[d ↦ b]}(X)`.
Source: [[policy-responsiveness]] Definition PR ("`ν_{B, C[d ↦ a]}(X)` varies with `a ∈ A_d`");
mandate §3.7
Kind: D
Fidelity: exact (pure deviations, as the wiki writes it) -/
def Responsive (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (X : Finset Ω) : Prop :=
  ∃ a b : acts d, nu (C.deviatePure d a) B X ≠ nu (C.deviatePure d b) B X

/-- Non-responsiveness, unfolded: every pure deviation gives `X` the same frequency.
Source: none: infrastructure
Kind: L -/
theorem not_responsive_iff (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (X : Finset Ω) :
    ¬ Responsive C B d X ↔
      ∀ a b : acts d, nu (C.deviatePure d a) B X = nu (C.deviatePure d b) B X := by
  simp only [Responsive, not_exists, not_not]

/-- The argmax of a real-valued function over a finite type of acts.
Source: [[learning-cdt-renderings]] Definition 26 (`argmax_a V^{π,a}_{s_d}(a)`)
Kind: D -/
noncomputable def argmaxAll {A : Type} [Fintype A] [DecidableEq A] (v : A → ℝ) : Finset A :=
  Finset.univ.filter fun a => ∀ b, v b ≤ v a

/-- Membership in `argmaxAll`. Source: none: infrastructure. Kind: L -/
theorem mem_argmaxAll {A : Type} [Fintype A] [DecidableEq A] (v : A → ℝ) (a : A) :
    a ∈ argmaxAll v ↔ ∀ b, v b ≤ v a := by simp [argmaxAll]

/-- **`T_CDT` at a point** for a family of suppositions `cf a` (one per act): if `A_d^+ ≠ ∅` then
every act `C` plays with positive weight maximises the *supposed* value `(cf a).V(a)` over
**all** of `A_d` — null acts included, their values filled by the supposition.
Source: [[learning-cdt-renderings]] Theorem 3(iv) ("CDT with `cf^G` and EDT approve the same
labels at `d` whenever the causal argmax meets the positive-probability acts"), Definition 26
(`CDT_π(d) := argmax_a V^{π,a}_{s_d}(a)`); mandate T2(iv)
Kind: D
Fidelity: exact (argmax over `A_d`, the proviso stated in `tcdt_iff_tedt`) -/
def TCdtAt (s : ι → State Ω ℚ) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts ℚ)
    (d : ι) (cf : acts d → State Ω ℝ) : Prop :=
  (APlus s actEv d).Nonempty →
    ∀ a, 0 < (C d).w a → a ∈ argmaxAll fun a => (cf a).V (actEv d a)

/-- **The LLC's antecedent at `X`**: conditioning on `X` changes the probability of some
subjectively possible act — `P(a ∧ X) ≠ P(a) P(X)` for some `a ∈ A_d^+` (cross-multiplied; with
`P(X) > 0` this is `P(a | X) ≠ P(a)`).
Source: [[clean-source-and-llc]] via mandate T14 (`LLCAntecedent`: "`P_{s_d}(a | X) ≠ P_{s_d}(a)`
for some `a ∈ A_d^+`")
Kind: D -/
def LLCAntecedent {A : Type} (s : State Ω K) (actEv : A → Finset Ω) (X : Finset Ω) : Prop :=
  0 < s.pr X ∧ ∃ a, 0 < s.pr (actEv a) ∧ s.pr (actEv a ∩ X) ≠ s.pr (actEv a) * s.pr X

/-- **An LLC-obeying counterfactual component** ("treat `X` as downstream"): whenever the
antecedent holds at `X`, every supposition moves `X`: `P^a(X) ≠ P(X)`. This is the rendering
"downstream = the supposition moves it"; the alternative reading "`X ∉ 𝓔₀^G`" is not defined
here (T14's verdicts are `stretch`, not attempted).
Source: mandate T14 (`LLCObeys`); [[clean-source-and-llc]]
Kind: D
Fidelity: variant: "downstream" rendered as "moved by the supposition" -/
def LLCObeys {A : Type} (t : CfState Ω K) (actEv : A → Finset Ω) : Prop :=
  ∀ X, LLCAntecedent t.s actEv X → ∀ a (h : (actEv a).Nonempty), (t.cf (actEv a) h).pr X ≠ t.s.pr X

end pr

end Cleanroom.Decision.DpCausalConsist
