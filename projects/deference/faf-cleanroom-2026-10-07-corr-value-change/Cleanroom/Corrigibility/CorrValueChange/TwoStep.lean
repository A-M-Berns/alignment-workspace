import Cleanroom.Corrigibility.CorrValueChange.Model
import Cleanroom.Corrigibility.CorrValueChange.Table

/-!
# corr-value-change — the evidential two-step decision (T2)

Source: [[value-change-as-epistemic-update]] §1.3–1.4. The step-1 events `K` (keep) and
`C = ⋁_j C_j` (change, with outcomes `C_j` of positive probability) partition the sure event; the
step-2 decision `𝒜` is a `Decision`. The installed utilities `U'_j` of §1.3 enter only through the
choices `a^j` they induce, which every theorem takes as free variables (so the results hold for
whatever the outcome installs); they are not a field of the model (audit r1, N2). The note's standing
positivity convention — every act has positive probability in every situation conditioned on —
is the pair of fields `posK`, `posC`. The values `v_E(a) = E[U ∣ a ∧ E]`, `p_j = P(C_j ∣ C)` form a
`ValueTable`, and the decomposition of §1.4 is inherited from `Table.lean` and restated here over
the model with the display sums spelled out.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A J : Type} [Fintype A] [Fintype J]
  [DecidableEq J]

/-- **The two-step decision** (§1.3): keep event `K`, change outcomes `C_j` (pairwise disjoint,
disjoint from `K`, covering the sure event with it), the step-2 decision `D`, and positive
probability of every act in every situation conditioned on (`posK`, `posC`). The installed choices
`a^j` (the note's `argmax_a E[U'_j ∣ a ∧ C_j]`) are free variables of the theorems, not a field.
`[Nonempty J]`: the change has at least one outcome.
Source: [[value-change-as-epistemic-update]] §1.3
Kind: D
Fidelity: exact -/
structure TwoStep (P : Prob Ω) (A J : Type) [Fintype A] [Fintype J] [Nonempty J] where
  /-- the step-2 decision -/
  D : Decision P A
  /-- the keep event -/
  K : Finset Ω
  /-- the outcomes of the change -/
  C : J → Finset Ω
  /-- keep and each outcome are disjoint -/
  K_disj : ∀ j, Disjoint K (C j)
  /-- distinct outcomes are disjoint -/
  C_disj : ∀ i j, i ≠ j → Disjoint (C i) (C j)
  /-- keep and the outcomes cover the sure event -/
  cover : ∀ ω, ω ∈ K ∨ ∃ j, ω ∈ C j
  /-- every act has positive probability in the keep situation -/
  posK : ∀ a, 0 < P.mass (D.act a ∩ K)
  /-- every act has positive probability in every outcome -/
  posC : ∀ a j, 0 < P.mass (D.act a ∩ C j)

variable [Nonempty J] {P : Prob Ω}

namespace TwoStep

variable (S : TwoStep P A J)

/-- The change event `C = ⋁_j C_j`.
Source: [[value-change-as-epistemic-update]] §1.3
Kind: D
Fidelity: exact -/
def changeEvent : Finset Ω := univ.biUnion S.C

include S in
/-- An act exists (from any world of positive probability).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_act : Nonempty A := by
  obtain ⟨ω, _⟩ := P.exists_pos
  obtain ⟨a, _⟩ := S.D.cover ω
  exact ⟨a⟩

/-- Every outcome has positive probability (from `posC`).
Source: none: infrastructure (derived from the model's positivity)
Kind: L
Fidelity: n/a -/
theorem mass_C_pos (j : J) : 0 < P.mass (S.C j) := by
  obtain ⟨a⟩ := S.exists_act
  exact lt_of_lt_of_le (S.posC a j) (P.mass_mono inter_subset_right)

/-- The keep event has positive probability (from `posK`).
Source: none: infrastructure (derived)
Kind: L
Fidelity: n/a -/
theorem mass_K_pos : 0 < P.mass S.K := by
  obtain ⟨a⟩ := S.exists_act
  exact lt_of_lt_of_le (S.posK a) (P.mass_mono inter_subset_right)

/-- `P(C) = ∑_j P(C_j)` (the outcomes partition the change event).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_changeEvent : P.mass S.changeEvent = ∑ j, P.mass (S.C j) := by
  unfold changeEvent Prob.mass
  apply sum_biUnion
  intro i _ j _ hij
  exact S.C_disj i j hij

/-- `P(C) > 0`.
Source: none: infrastructure (derived)
Kind: L
Fidelity: n/a -/
theorem mass_changeEvent_pos : 0 < P.mass S.changeEvent := by
  rw [S.mass_changeEvent]
  obtain ⟨j⟩ := (inferInstance : Nonempty J)
  exact lt_of_lt_of_le (S.mass_C_pos j)
    (single_le_sum (fun i _ => P.mass_nonneg (S.C i)) (mem_univ j))

/-- `p_j = P(C_j ∣ C) = P(C_j) / P(C)`.
Source: [[value-change-as-epistemic-update]] §1.3
Kind: D
Fidelity: exact -/
def p (j : J) : ℝ := P.mass (S.C j) / P.mass S.changeEvent

/-- `p_j > 0`.
Source: none: infrastructure (derived)
Kind: L
Fidelity: n/a -/
theorem p_pos (j : J) : 0 < S.p j := div_pos (S.mass_C_pos j) S.mass_changeEvent_pos

/-- `∑_j p_j = 1`.
Source: none: infrastructure (derived)
Kind: L
Fidelity: n/a -/
theorem p_sum : ∑ j, S.p j = 1 := by
  unfold p
  rw [← sum_div, ← S.mass_changeEvent]
  exact div_self S.mass_changeEvent_pos.ne'

/-- `v_K(a) = E[U ∣ a ∧ K]`.
Source: [[value-change-as-epistemic-update]] §1.3
Kind: D
Fidelity: exact -/
def vK (U : Ω → ℝ) (a : A) : ℝ := S.D.v U S.K a

/-- `v_j(a) = E[U ∣ a ∧ C_j]`, by the present `U`.
Source: [[value-change-as-epistemic-update]] §1.3
Kind: D
Fidelity: exact -/
def v (U : Ω → ℝ) (j : J) (a : A) : ℝ := S.D.v U (S.C j) a

/-- The model's value table.
Source: [[value-change-as-epistemic-update]] §1.3–1.4
Kind: D
Fidelity: exact -/
def table (U : Ω → ℝ) : ValueTable A J where
  p := S.p
  p_pos := S.p_pos
  p_sum := S.p_sum
  vK := S.vK U
  v := S.v U

/-- `Val(K) = v_K(a^K)`.
Source: [[value-change-as-epistemic-update]] §1.3
Kind: D
Fidelity: exact -/
def ValK (U : Ω → ℝ) (aK : A) : ℝ := S.vK U aK

/-- `Val(C) = ∑_j p_j v_j(a^j)`.
Source: [[value-change-as-epistemic-update]] §1.3
Kind: D
Fidelity: exact -/
def ValC (U : Ω → ℝ) (aj : J → A) : ℝ := ∑ j, S.p j * S.v U j (aj j)

/-- **T2(a), the decomposition over the model** (§1.4): for the two-step decision, with `a^K` any
act, `a^j` the installed choices and `â^j` any acts,
`Val(C) − Val(K) = ∑_j p_j [v_j(a^j) − v_j(â^j)] + ∑_j p_j [v_j(â^j) − v_j(a^K)] + ∑_j p_j [v_j(a^K) − v_K(a^K)]`,
with `p_j = P(C_j ∣ C)`, `v_E(a) = E[U ∣ a ∧ E]`. An identity: no hypothesis beyond the model's
positivity fields (which make the `p_j` sum to one). Derived in `Table.lean` outcome by outcome
and by the telescoping split (`ValueTable.ValC_sub_ValK`, `ValueTable.bracket_split`).
Source: [[value-change-as-epistemic-update]] §1.4 (third display)
Kind: P
Fidelity: exact
Hyps: (a) none beyond the model -/
theorem decomposition (U : Ω → ℝ) (aj ahat : J → A) (aK : A) :
    S.ValC U aj - S.ValK U aK =
      (∑ j, S.p j * (S.v U j (aj j) - S.v U j (ahat j))) +
      (∑ j, S.p j * (S.v U j (ahat j) - S.v U j aK)) +
      (∑ j, S.p j * (S.v U j aK - S.vK U aK)) :=
  (S.table U).decomposition aj ahat aK

/-- **T2(b), (A) ≤ 0** over the model, from `â^j` maximizing `v_j` only.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: P
Fidelity: exact
Hyps: (a) `hhat : ∀ j a, v_j a ≤ v_j (â^j)` -/
theorem termA_nonpos (U : Ω → ℝ) (aj ahat : J → A) (hhat : ∀ j a, S.v U j a ≤ S.v U j (ahat j)) :
    ∑ j, S.p j * (S.v U j (aj j) - S.v U j (ahat j)) ≤ 0 :=
  (S.table U).termA_nonpos aj ahat hhat

/-- **T2(b), (B) ≥ 0** over the model, from `â^j` maximizing `v_j` only.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: P
Fidelity: exact
Hyps: (a) `hhat` -/
theorem termB_nonneg (U : Ω → ℝ) (ahat : J → A) (aK : A)
    (hhat : ∀ j a, S.v U j a ≤ S.v U j (ahat j)) :
    0 ≤ ∑ j, S.p j * (S.v U j (ahat j) - S.v U j aK) :=
  (S.table U).termB_nonneg ahat aK hhat

/-- **(B) = 0 iff `a^K` maximizes every `v_j`**, over the model.
Source: [[value-change-as-epistemic-update]] §1.4; mandate Known issues 1
Kind: P
Fidelity: exact
Hyps: (a) `hhat` -/
theorem termB_eq_zero_iff (U : Ω → ℝ) (ahat : J → A) (aK : A)
    (hhat : ∀ j a, S.v U j a ≤ S.v U j (ahat j)) :
    (∑ j, S.p j * (S.v U j (ahat j) - S.v U j aK)) = 0 ↔ ∀ j a, S.v U j a ≤ S.v U j aK :=
  (S.table U).termB_eq_zero_iff ahat aK hhat

/-- **T2(c), the intrinsic case** over the model: `v_j = v_K + β_j` pointwise ⇒
`Val(C) − Val(K) = ∑_j p_j β_j − ∑_j p_j [v_K(a^K) − v_K(a^j)]`, the subtracted loss `ℓ ≥ 0`.
Source: [[value-change-as-epistemic-update]] §1.4 (first route)
Kind: P
Fidelity: exact
Hyps: (a) `hβ`, `hK` -/
theorem intrinsic_case (U : Ω → ℝ) (aj : J → A) (aK : A) (β : J → ℝ)
    (hβ : ∀ j a, S.v U j a = S.vK U a + β j) (hK : ∀ a, S.vK U a ≤ S.vK U aK) :
    S.ValC U aj - S.ValK U aK =
        (∑ j, S.p j * β j) - ∑ j, S.p j * (S.vK U aK - S.vK U (aj j)) ∧
      0 ≤ ∑ j, S.p j * (S.vK U aK - S.vK U (aj j)) :=
  (S.table U).intrinsic_case aj aK β hβ hK

/-- **T2(d), single outcome with `v_C = v_K`**: (B) = 0 (for any number of outcomes with
`v_j = v_K`, in particular for one).
Source: [[value-change-as-epistemic-update]] §1.4 ("Uncertainty is required")
Kind: L (`ValueTable.termB_zero_of_v_eq_vK`: one rewrite into `termB_eq_zero_iff` plus `hK`)
Fidelity: stronger (any `J`)
Hyps: (a) `hv`, `hhat`, `hK` -/
theorem termB_zero_of_v_eq_vK (U : Ω → ℝ) (ahat : J → A) (aK : A)
    (hv : ∀ j a, S.v U j a = S.vK U a) (hhat : ∀ j a, S.v U j a ≤ S.v U j (ahat j))
    (hK : ∀ a, S.vK U a ≤ S.vK U aK) :
    ∑ j, S.p j * (S.v U j (ahat j) - S.v U j aK) = 0 :=
  (S.table U).termB_zero_of_v_eq_vK ahat aK hv hhat hK

/-! ## Finding: `Val(C)` is the situation-weighted policy value, not the value of a policy event

The note *defines* `Val(C) := ∑_j p_j v_j(a^j)`. In the evidential picture one might instead
evaluate the event "the agent follows the installed policy", `Pol = ⋁_j (a^j ∧ C_j)`, by
`E[U ∣ Pol]`. The two agree iff the weights `P(a^j ∧ C_j) / P(Pol)` equal `p_j`, which holds when
the self-model gives every chosen act the same conditional probability in its outcome
(`P(a^j ∧ C_j) = c · P(C_j)`), and fails in general (findings F-pol). -/

/-- The event "follow the installed policy": `⋁_j (a^j ∧ C_j)`.
Source: none: infrastructure (finding F-pol)
Kind: D
Fidelity: n/a -/
def policyEvent (aj : J → A) : Finset Ω := univ.biUnion fun j => S.D.act (aj j) ∩ S.C j

/-- `∫_{Pol} U = ∑_j ∫_{a^j ∧ C_j} U` and `P(Pol) = ∑_j P(a^j ∧ C_j)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem policyEvent_sums (U : Ω → ℝ) (aj : J → A) :
    P.integral U (S.policyEvent aj) = ∑ j, P.integral U (S.D.act (aj j) ∩ S.C j) ∧
      P.mass (S.policyEvent aj) = ∑ j, P.mass (S.D.act (aj j) ∩ S.C j) := by
  have hd : (↑(univ : Finset J) : Set J).PairwiseDisjoint fun j => S.D.act (aj j) ∩ S.C j := by
    intro i _ j _ hij
    exact Finset.disjoint_of_subset_left inter_subset_right
      (Finset.disjoint_of_subset_right inter_subset_right (S.C_disj i j hij))
  exact ⟨sum_biUnion hd, sum_biUnion hd⟩

/-- **F-pol, the agreement condition**: if `P(a^j ∧ C_j) = c · P(C_j)` for every `j` (the chosen
act's self-model probability does not depend on the outcome), then `E[U ∣ Pol] = Val(C)`.
Source: none: finding about [[value-change-as-epistemic-update]] §1.3's definition of `Val(C)`
Kind: P
Fidelity: n/a (a finding)
Hyps: (a) `hc : ∃ c, ∀ j, P(a^j ∧ C_j) = c · P(C_j)` -/
theorem condExp_policyEvent_eq_ValC (U : Ω → ℝ) (aj : J → A) (c : ℝ)
    (hc : ∀ j, P.mass (S.D.act (aj j) ∩ S.C j) = c * P.mass (S.C j)) :
    P.condExp U (S.policyEvent aj) = S.ValC U aj := by
  obtain ⟨hI, hM⟩ := S.policyEvent_sums U aj
  have hcpos : 0 < c := by
    obtain ⟨j⟩ := (inferInstance : Nonempty J)
    have h1 := S.posC (aj j) j
    have h2 := S.mass_C_pos j
    rw [hc j] at h1
    by_contra hneg
    have : c ≤ 0 := not_lt.1 hneg
    nlinarith
  unfold Prob.condExp ValC
  rw [hI, hM]
  have hsum : ∑ j, P.mass (S.D.act (aj j) ∩ S.C j) = c * P.mass S.changeEvent := by
    rw [S.mass_changeEvent, mul_sum]; exact sum_congr rfl fun j _ => hc j
  rw [hsum]
  have hC := S.mass_changeEvent_pos
  rw [div_eq_iff (by positivity)]
  rw [sum_mul]
  refine sum_congr rfl fun j _ => ?_
  unfold p v Decision.v
  rw [P.integral_eq_condExp_mul U (S.posC (aj j) j), hc j]
  field_simp

end TwoStep

end

end Cleanroom.Corrigibility.CorrValueChange
