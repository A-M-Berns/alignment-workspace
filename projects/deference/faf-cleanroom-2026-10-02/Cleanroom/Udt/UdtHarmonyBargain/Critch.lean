import Cleanroom.Udt.UdtHarmonyBargain.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# `udt-harmony-bargain` — Critch coalitions, static shadow (T12), and Claim 12.3 / Q7 (T13, T14)

* `weightedWelfare_eq_mixture`: for a common utility `u` and world-models `μᵢ` on one `X`,
  `∑ᵢ wᵢ Uᵢ(O) = 𝔼_{∑ wᵢ μᵢ}[u(O, ·)]` (the mixture is a `FinDistr`).
* `argmax_weighted_paretoOptimal`: a maximiser of a positively weighted sum is Pareto-optimal.
* `converse_fails`: `(1, 1)` is Pareto-optimal among `{(3,0), (0,3), (1,1)}` and maximises no
  positively weighted sum — the converse fails at the pure grade.
* `condDistr`, `U_condDistr_eq_condExp` (Claim 12.3's definitional core, kind T).
* `AgreeOnShared`, `agree_factors` (Open Q7: cross-ontology agreement on shared propositions forces
  the utilities to factor through the shared language when the coarsenings are surjective).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset SafeParetoImprovements
open Cleanroom.Found.DpCoreTree (FinDistr)

variable {N : Type} [Fintype N] [DecidableEq N]
variable {A : N → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

/-! ### T12: weighted welfare and mixtures -/

/-- The mixture `∑ᵢ wᵢ μᵢ` of finitely many world-models on one space, for weights in the simplex.
Source: bli-paper-2-015 (Critch 2017, the weighted-sum aggregator); mandate T12(i)
Kind: D -/
def mixture {X : Type} [Fintype X] (w : N → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (μ : N → FinDistr ℝ X) : FinDistr ℝ X where
  w x := ∑ i, w i * (μ i).w x
  nonneg x := sum_nonneg fun i _ => mul_nonneg (hw0 i) ((μ i).nonneg x)
  sum_one := by
    rw [sum_comm]
    simp_rw [← mul_sum, (fun i => (μ i).sum_one), mul_one]
    exact hw1

/-- **Weighted welfare is the mixture's expectation**: for a common `u`,
`∑ᵢ wᵢ Uᵢ(O) = 𝔼_{∑ wᵢ μᵢ}[u(O, ·)]`.
Source: bli-paper-2-015 (Critch 2017); `repair/harmony.md` HA-15′ (the linearity identity);
mandate T12(i)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem weightedWelfare_eq_mixture {X : Type} [Fintype X] (w : N → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (μ : N → FinDistr ℝ X) (u : Outcome A → X → ℝ) (O : Outcome A) :
    ∑ i, w i * U ⟨X, μ i, u⟩ O = U ⟨X, mixture w hw0 hw1 μ, u⟩ O := by
  unfold U
  simp only [mixture, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun x _ => ?_
  ring

/-- **A maximiser of a positively weighted sum is Pareto-optimal.**
Source: bli-paper-2-015; mandate T12(ii)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem argmax_weighted_paretoOptimal (Γ : Game N A) (w : N → ℝ) (hw : ∀ i, 0 < w i)
    (O : Outcome A) (hO : ∀ O', ∑ i, w i * Γ.u O' i ≤ ∑ i, w i * Γ.u O i) :
    Game.ParetoOptimalIn (Γ.u O) (Γ.u '' Set.univ) := by
  rw [paretoOptimalIn_iff]
  intro O' hdom
  rw [paretoDom_iff] at hdom
  obtain ⟨hle, i, hi⟩ := hdom
  have : ∑ i, w i * Γ.u O i < ∑ i, w i * Γ.u O' i :=
    sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hw j).le)
      ⟨i, mem_univ _, mul_lt_mul_of_pos_left hi (hw i)⟩
  exact absurd (hO O') (not_le.mpr this)

namespace Converse

/-- Three outcomes `x ↦ (3,0)`, `y ↦ (0,3)`, `z ↦ (1,1)` for two players.
Source: mandate T12(iii)
Kind: D -/
inductive Three : Type
  | x | y | z
  deriving DecidableEq, Fintype

instance : Nonempty Three := ⟨.x⟩

/-- The payoff vectors. Source: mandate T12(iii). Kind: D -/
def pay : Three → Fin 2 → ℝ
  | .x => ![3, 0]
  | .y => ![0, 3]
  | .z => ![1, 1]

/-- A game with a single "outcome-choosing" player whose outcomes are `Three` — the payoff
vectors as a set, which is all `ParetoOptimalIn` looks at.
Source: mandate T12(iii)
Kind: D -/
def Γ : Game (Fin 2) (fun _ => Three) where
  S _ := univ
  nonempty _ := univ_nonempty
  u O i := pay (O 0) i

/-- **The converse fails at the pure grade**: `z = (1,1)` is Pareto-optimal among
`{(3,0), (0,3), (1,1)}` and maximises no positively weighted sum with `w₁ + w₂ = 1`
(`1 < max(3w₁, 3w₂)`).
Source: mandate T12(iii)
Kind: N-
Fidelity: exact
Hyps: (a) all -/
theorem converse_fails :
    Game.ParetoOptimalIn (Γ.u (fun _ => .z)) (Γ.u '' Set.univ) ∧
      ∀ w : Fin 2 → ℝ, (∀ i, 0 < w i) → ∑ i, w i = 1 →
        ¬ ∀ O', ∑ i, w i * Γ.u O' i ≤ ∑ i, w i * Γ.u (fun _ => .z) i := by
  refine ⟨?_, ?_⟩
  · rw [paretoOptimalIn_iff]
    intro O' hdom
    rw [paretoDom_iff] at hdom
    obtain ⟨hle, i, hi⟩ := hdom
    have h0 := hle 0
    have h1 := hle 1
    rcases hO : O' 0 with _ | _ | _ <;> simp [Γ, pay, hO] at h0 h1 hi <;> fin_cases i <;>
      simp [Γ, pay, hO] at hi <;> linarith
  · intro w hw hsum hmax
    have hx := hmax (fun _ => .x)
    have hy := hmax (fun _ => .y)
    simp [Γ, pay, Fin.sum_univ_two] at hx hy
    have := hw 0
    have := hw 1
    rw [Fin.sum_univ_two] at hsum
    linarith

end Converse

/-! ### T13: Claim 12.3's definitional core -/

/-- The conditional distribution `μ(· ∣ E)` on a finite space (the zero-mass case is made explicit:
`μ` itself, so the definition is total; every use carries `μ(E) > 0`).
Source: [[superconditioning-mismatched-ontologies]] §12.1 Def. 12.1 (`X_j = X_i(· ∣ ā₀)`); mandate T13
Kind: D -/
noncomputable def condDistr {X : Type} [Fintype X] [DecidableEq X] (μ : FinDistr ℝ X)
    (E : Finset X) : FinDistr ℝ X :=
  if h : 0 < ∑ x ∈ E, μ.w x then
    { w := fun x => if x ∈ E then μ.w x / ∑ y ∈ E, μ.w y else 0
      nonneg := fun x => by split_ifs <;> [exact div_nonneg (μ.nonneg x) h.le; exact le_refl _]
      sum_one := by
        rw [← sum_filter, filter_mem_eq_inter, univ_inter]
        simp_rw [div_eq_mul_inv]
        rw [← sum_mul, mul_inv_cancel₀ h.ne'] }
  else μ

/-- The conditional expectation `𝔼_μ[f ∣ E]` on a finite space.
Source: [[superconditioning-mismatched-ontologies]] §12.3 Claim 12.3; mandate T13
Kind: D -/
noncomputable def condExpF {X : Type} [Fintype X] [DecidableEq X] (μ : FinDistr ℝ X)
    (f : X → ℝ) (E : Finset X) : ℝ :=
  (∑ x ∈ E, μ.w x * f x) / ∑ x ∈ E, μ.w x

/-- **Claim 12.3's identity**: if `X_j = X_i(· ∣ E)` with `μᵢ(E) > 0` and `uᵢ = uⱼ = u`, then
`Uⱼ(O) = 𝔼_{μᵢ}[u(O, ·) ∣ E]` for every `O`. This is the identity SC states; the claim's
"endorsement" content beyond it is not a statement (finding F10).
Source: [[superconditioning-mismatched-ontologies]] §12.3 Claim 12.3; mandate T13
Kind: T
Fidelity: exact (finite form)
Hyps: (a) all -/
theorem U_condDistr_eq_condExp {X : Type} [Fintype X] [DecidableEq X] (μ : FinDistr ℝ X)
    (E : Finset X) (hE : 0 < ∑ x ∈ E, μ.w x) (u : Outcome A → X → ℝ) (O : Outcome A) :
    U ⟨X, condDistr μ E, u⟩ O = condExpF μ (u O) E := by
  unfold U condDistr condExpF
  rw [dif_pos hE]
  simp only [ite_mul, zero_mul]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  rw [div_eq_mul_inv]
  ring

/-! ### T14: cross-ontology utility agreement (Open Q7) -/

/-- Two decision-points with different world-models `Xᵢ`, `Xⱼ` coarsened to a common `C` by
`cᵢ`, `cⱼ` agree on shared propositions if their utilities agree whenever the worlds have the same
image in `C`.
Source: [[superconditioning-mismatched-ontologies]] §12.2 ("requiring `uᵢ` and `uⱼ` to agree on
shared propositions"); mandate T14 (Open Q7)
Kind: D -/
def AgreeOnShared {Xi Xj C : Type} (ui : Outcome A → Xi → ℝ) (uj : Outcome A → Xj → ℝ)
    (ci : Xi → C) (cj : Xj → C) : Prop :=
  ∀ O xi xj, ci xi = cj xj → ui O xi = uj O xj

/-- **Agreement forces factoring**: if `cⱼ` is surjective, agreement on shared propositions forces
`uᵢ` to factor through `cᵢ` — the note's own worry ("too strong") as a theorem.
Source: [[superconditioning-mismatched-ontologies]] §12.2; mandate T14
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem AgreeOnShared.factors {Xi Xj C : Type} {ui : Outcome A → Xi → ℝ}
    {uj : Outcome A → Xj → ℝ} {ci : Xi → C} {cj : Xj → C} (h : AgreeOnShared ui uj ci cj)
    (hcj : Function.Surjective cj) (O : Outcome A) (x x' : Xi) (hx : ci x = ci x') :
    ui O x = ui O x' := by
  obtain ⟨xj, hxj⟩ := hcj (ci x)
  have h1 := h O x xj hxj.symm
  have h2 := h O x' xj (by rw [← hx, hxj])
  rw [h1, h2]

/-- Both utilities are then expectations of one `ū : Outcome → C → ℝ` under the pushforwards.
Source: [[superconditioning-mismatched-ontologies]] §12.2; mandate T14
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem AgreeOnShared.exists_common {Xi Xj C : Type} [Fintype Xi] [Fintype Xj]
    {ui : Outcome A → Xi → ℝ} {uj : Outcome A → Xj → ℝ} {ci : Xi → C} {cj : Xj → C}
    (h : AgreeOnShared ui uj ci cj) (hci : Function.Surjective ci)
    (hcj : Function.Surjective cj) :
    ∃ ubar : Outcome A → C → ℝ, (∀ O xi, ui O xi = ubar O (ci xi)) ∧
      ∀ O xj, uj O xj = ubar O (cj xj) := by
  classical
  refine ⟨fun O c => ui O (hci c).choose, fun O xi => ?_, fun O xj => ?_⟩
  · exact h.factors hcj O xi _ (hci (ci xi)).choose_spec.symm
  · have hs := (hci (cj xj)).choose_spec
    exact (h O _ xj hs).symm

end Cleanroom.Udt.UdtHarmonyBargain
