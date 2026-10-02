import Cleanroom.Bli.UdtBliCore.Basic
import Cleanroom.Bli.BliFinite.Witness
import Mathlib.Algebra.BigOperators.Fin

/-!
# `udt-bli-core` · Wirehead: the wireheading identity under action-conditional faith
(T9, load-bearing 5; U14)

With an action coordinate `act : Ω → A'` (the action taken *now*, distinct from the day-`m`
policy points `pp`), a utility that is a combination of small truths `U ω = ∑_φ c φ · [small ω φ]`,
and **action-conditional faith** (`FaithGivenAct`: inside every positive cell `state = T ∧ act = a`
the frequency of each small sentence is the table's price), the agent's expected utility of an
action is its expected *future belief* about `U`, weighted by which belief states the action
induces:

`𝔼[U | act = a] = ∑_T μ(state = T | act = a) · (∑_φ c φ · T φ)`   (`wirehead_identity`, L).

The N+ witness (`pushPrior`): two next-states `T_hi = (9/10, 0)`, `T_lo = (1/10, 0)` on
`witIndex` day 1, actions `push = true`, `honest = false`, `μ(T_hi | push) = 9/10`,
`μ(T_hi | honest) = 1/10`, utility `[u]` with `u = p`, and a second coordinate `world` for the fact
`u` actually tracks, with `μ(world | push) = 1/5`, `μ(world | honest) = 4/5` independently of the
state. Then the identity ranks `push` (`41/50`) above `honest` (`9/50`), while under `μ`
conditioned on each table and the action the pushed action lowers `𝔼[[world] | act, state = T]`
from `4/5` to `1/5` for both `T` (the tables price only `p` and `q`, so "the table's world belief"
is `μ`'s conditional, and since `world` is independent of the state it is one number for both
tables): the "elicit a favourable push" pattern. The source's "cannot represent" clause is left
out (F-8).

The action-conditional form of faith is **needed**: under the `faith` field alone (unconditional
reflection, the source's constraint 2) the identity is false — `WitnessLayers.lean`, `wfPrior`,
`wf_identity_fails` (N−).
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

namespace FiniteBLIPrior

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type}
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A) {A' : Type} [DecidableEq A'] (act : P.Ω → A')

/-- **Action-conditional faith**: inside every positive cell `state = T ∧ act = a`, the frequency
of each small sentence is the table's price.
Source: bli-soto-b-058 (constraint 2 conditioned on the current action,
`𝔼[[small · φ] | state = T ∧ act = a] = T φ`); mandate T9
Kind: D
Fidelity: exact -/
def FaithGivenAct : Prop :=
  ∀ (T : ↥𝒟) (φ : ↥(𝒮.S m)) (a : A'), 0 < massOf P.μ (fun ω => P.state ω = T ∧ act ω = a) →
    integralOf P.μ (fun ω => ind (P.small ω φ)) (fun ω => P.state ω = T ∧ act ω = a) =
      T.1 φ * massOf P.μ (fun ω => P.state ω = T ∧ act ω = a)

/-- A utility that is a combination of small truths: `U ω = ∑_φ c φ · [small ω φ]`.
Source: mandate T9 ("or simply `U ω = ∑_φ c φ * [small ω φ]`")
Kind: D
Fidelity: exact -/
def SmallCombination (c : ↥(𝒮.S m) → ℚ) : Prop :=
  ∀ ω, P.U ω = ∑ φ, c φ * ind (P.small ω φ)

/-- The **believed value** of a table: `∑_φ c φ · T φ` — what the table itself expects `U` to be.
Source: bli-soto-b-058 (`Q'[u]`)
Kind: D
Fidelity: exact -/
def believedValue (c : ↥(𝒮.S m) → ℚ) (T : ↥𝒟) : ℚ := ∑ φ, c φ * T.1 φ

/-- On a positive cell `state = T ∧ act = a`, the expected utility is the table's believed value.
Source: bli-soto-b-058
Kind: L
Fidelity: n/a -/
lemma condExp_cell_eq_believedValue (c : ↥(𝒮.S m) → ℚ) (hU : P.SmallCombination c)
    (hF : P.FaithGivenAct act) (T : ↥𝒟) (a : A')
    (hpos : 0 < massOf P.μ (fun ω => P.state ω = T ∧ act ω = a)) :
    condExp P.μ P.U (fun ω => P.state ω = T ∧ act ω = a) = believedValue c T := by
  unfold condExp believedValue
  rw [div_eq_iff (ne_of_gt hpos)]
  have e : integralOf P.μ P.U (fun ω => P.state ω = T ∧ act ω = a) =
      integralOf P.μ (fun ω => ∑ φ, c φ * ind (P.small ω φ))
        (fun ω => P.state ω = T ∧ act ω = a) :=
    integralOf_congr_fun P.μ _ _ _ (fun ω _ => hU ω)
  rw [e, integralOf_finset_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro φ _
  rw [integralOf_smul, hF T φ a hpos]
  ring

/-- **The wireheading identity** (load-bearing 5): under action-conditional faith, for a utility
that is a combination of small truths,
`𝔼[U | act = a] = ∑_T μ(state = T | act = a) · (∑_φ c φ · T φ)`:
the agent values an action by the beliefs it induces. (Null cells contribute `0` on both sides.)
Source: bli-soto-b-058 ("Consequence 3": `𝔼_n[u | a] = ∑_{Q'} P_n(Q_{n+1} = Q' | a) Q'[u]`)
Kind: L
Fidelity: variant: action-conditional faith (`FaithGivenAct`) in place of the source's
constraint 2 (unconditional reflection `P_n(φ | Q_{n+1} = Q') = Q'[φ]`, the `faith` field) —
needed: the identity fails under the field alone (`WitnessLayers.lean`, `wf_identity_fails`),
so the source's derivation uses more than constraint 2 (finding F-17); finite; the source's
`Q'[u]` is `believedValue`
Hyps: (a) `FaithGivenAct`, `SmallCombination`; uses faith (the action-conditional form) -/
theorem wirehead_identity (c : ↥(𝒮.S m) → ℚ) (hU : P.SmallCombination c)
    (hF : P.FaithGivenAct act) (a : A') :
    condExp P.μ P.U (fun ω => act ω = a) =
      ∑ T, massOf P.μ (fun ω => act ω = a ∧ P.state ω = T) / massOf P.μ (fun ω => act ω = a) *
        believedValue c T := by
  rw [condExp_fiberwise P.μ P.U P.μ_nonneg _ P.state]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hpos : 0 < massOf P.μ (fun ω => act ω = a ∧ P.state ω = T)
  · have hpos' : 0 < massOf P.μ (fun ω => P.state ω = T ∧ act ω = a) := by
      rwa [massOf_congr P.μ (fun ω => and_comm)]
    rw [condExp_congr P.μ P.U (fun ω => (and_comm : (act ω = a ∧ P.state ω = T) ↔ _)),
      P.condExp_cell_eq_believedValue act c hU hF T a hpos']
  · have hz : massOf P.μ (fun ω => act ω = a ∧ P.state ω = T) = 0 :=
      le_antisymm (not_lt.mp hpos) (massOf_nonneg _ P.μ_nonneg _)
    rw [hz, zero_div, zero_mul, zero_mul]

end FiniteBLIPrior

/-! ## The push-eliciting witness -/

namespace Push

/-- The high table `(p ↦ 9/10, q ↦ 0)`.
Source: mandate T9
Kind: D
Fidelity: exact -/
def Thi : Table witIndex 1 := fun φ => if φ.1 = pW then 9 / 10 else 0

/-- The low table `(p ↦ 1/10, q ↦ 0)`.
Source: mandate T9
Kind: D
Fidelity: exact -/
def Tlo : Table witIndex 1 := fun φ => if φ.1 = pW then 1 / 10 else 0

/-- `Thi ≠ Tlo`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Thi_ne_Tlo : Thi ≠ Tlo := fun h => by
  have := congrFun h ⟨pW, pW_mem_S1⟩
  simp [Thi, Tlo] at this
  norm_num at this

/-- The two next-states.
Source: mandate T9
Kind: D
Fidelity: exact -/
def pushTables : Finset (Table witIndex 1) := {Thi, Tlo}

/-- `Thi ∈ pushTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Thi_mem : Thi ∈ pushTables := by simp [pushTables]

/-- `Tlo ∈ pushTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Tlo_mem : Tlo ∈ pushTables := by simp [pushTables]

/-- The high state.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev Shi : ↥pushTables := ⟨Thi, Thi_mem⟩

/-- The low state.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev Slo : ↥pushTables := ⟨Tlo, Tlo_mem⟩

/-- `Shi ≠ Slo`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Shi_ne_Slo : Shi ≠ Slo := fun h => Thi_ne_Tlo (congrArg Subtype.val h)

/-- `Slo ≠ Shi`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Slo_ne_Shi : Slo ≠ Shi := fun h => Shi_ne_Slo h.symm

/-- Every state is `Shi` or `Slo`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eq_Shi_or_Slo (T : ↥pushTables) : T = Shi ∨ T = Slo := by
  rcases T with ⟨T, hT⟩
  simp only [pushTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The state coordinate `0 ↦ Shi`, `1 ↦ Slo`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def pState : Fin 2 → ↥pushTables
  | 0 => Shi
  | 1 => Slo

/-- `pState 0 = Shi`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma pState_zero : pState 0 = Shi := rfl

/-- `pState 1 = Slo`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma pState_one : pState 1 = Slo := rfl

/-- The price of `u = p` in each state: `9/10`, `1/10`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def uPrice : Fin 2 → ℚ
  | 0 => 9 / 10
  | 1 => 1 / 10

/-- `uPrice 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma uPrice_zero : uPrice 0 = 9 / 10 := rfl

/-- `uPrice 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma uPrice_one : uPrice 1 = 1 / 10 := rfl

/-- `μ(state = Shi | act)`: `9/10` under `push`, `1/10` under `honest`.
Source: mandate T9 (`μ(T_hi | push) > μ(T_hi | honest)`)
Kind: D
Fidelity: exact -/
def hiProb (a : Bool) : ℚ := if a then 9 / 10 else 1 / 10

/-- The state law given the action.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def sProb (a : Bool) (s : Fin 2) : ℚ := if s = 0 then hiProb a else 1 - hiProb a

/-- The `u`-truth law given the state: `Bernoulli(uPrice s)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def bProb (s : Fin 2) (b : Bool) : ℚ := if b then uPrice s else 1 - uPrice s

/-- The world law given the action: `μ(world | push) = 1/5`, `μ(world | honest) = 4/5`.
Source: mandate T9 ("the pushed action lowers `𝔼[[world] | act = push, state = T]`")
Kind: D
Fidelity: exact -/
def wProb (a : Bool) (w : Bool) : ℚ := if w then (if a then 1 / 5 else 4 / 5) else (if a then 4 / 5 else 1 / 5)

/-- The outcome space: `(act, state, u-truth, world)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev PushΩ : Type := Bool × Fin 2 × Bool × Bool

/-- The joint law: fair action, then state given action, `u`-truth given state, world given
action.
Source: mandate T9
Kind: D
Fidelity: exact -/
def pMass (ω : PushΩ) : ℚ := 1 / 2 * sProb ω.1 ω.2.1 * bProb ω.2.1 ω.2.2.1 * wProb ω.1 ω.2.2.2

/-- `pMass ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pMass_nonneg (ω : PushΩ) : 0 ≤ pMass ω := by
  rcases ω with ⟨a, s, b, w⟩
  unfold pMass sProb bProb wProb hiProb
  fin_cases s <;> cases a <;> cases b <;> cases w <;> norm_num

/-- `pMass` sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pMass_sum_one : ∑ ω : PushΩ, pMass ω = 1 := by
  unfold pMass sProb bProb wProb hiProb
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
  norm_num

/-- The world's small truths: `p` is the `u`-truth coordinate, `q` is false.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def pSmall (ω : PushΩ) (φ : ↥(witIndex.S 1)) : Bool := if φ.1 = pW then ω.2.2.1 else false

/-- Each table's price of `φ` is `uPrice s` at `p` and `0` elsewhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma table_apply (s : Fin 2) (φ : ↥(witIndex.S 1)) :
    (pState s).1 φ = if φ.1 = pW then uPrice s else 0 := by
  fin_cases s <;> rfl

/-- **The push-eliciting prior.**
Source: mandate T9 (N+ witness)
Kind: D
Fidelity: exact -/
def pushPrior : FiniteBLIPrior witIndex 1 pushTables Bool where
  Ω := PushΩ
  μ := pMass
  μ_nonneg := pMass_nonneg
  μ_sum_one := pMass_sum_one
  state := fun ω => pState ω.2.1
  pp := fun _ _ => true
  U := fun ω => ind ω.2.2.1
  small := pSmall
  faith := by
    intro T φ
    rcases eq_Shi_or_Slo T with rfl | rfl <;>
    · by_cases hφ : φ.1 = pW <;>
      · unfold pMass sProb bProb wProb hiProb pSmall
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, pState_zero,
          pState_one, hφ, if_true, if_false, Shi_ne_Slo, Slo_ne_Shi, ind_true, ind_false]
        norm_num [Thi, Tlo, hφ, Thi_ne_Tlo, Ne.symm Thi_ne_Tlo]

/-- The action coordinate.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def pAct (ω : PushΩ) : Bool := ω.1

/-- The utility is the indicator of `p`: the combination with `c = [φ = p]`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def pCoef (φ : ↥(witIndex.S 1)) : ℚ := if φ.1 = pW then 1 else 0

/-- `pushPrior`'s utility is the small combination with coefficients `pCoef`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallCombination : pushPrior.SmallCombination pCoef := by
  intro ω
  change ind ω.2.2.1 = ∑ φ, pCoef φ * ind (pSmall ω φ)
  rw [univ_S1, Finset.sum_pair subtype_p_ne_q]
  simp [pCoef, pSmall, pW_ne_qW.symm]

/-- **Action-conditional faith holds** on the push prior: the `u`-truth is drawn from the table's
price independently of the action.
Source: mandate T9
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem faithGivenAct : pushPrior.FaithGivenAct pAct := by
  intro T φ a _
  rcases eq_Shi_or_Slo T with rfl | rfl <;> cases a <;>
  · by_cases hφ : φ.1 = pW <;>
    · unfold integralOf massOf pushPrior pMass sProb bProb wProb hiProb pSmall pAct
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, pState_zero,
        pState_one, hφ, if_true, if_false, Shi_ne_Slo, Slo_ne_Shi, ind_true, ind_false]
      norm_num [Thi, Tlo, hφ, Thi_ne_Tlo, Ne.symm Thi_ne_Tlo]

/-- The believed values: `9/10` at `Shi`, `1/10` at `Slo`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma believedValue_eq (s : Fin 2) : FiniteBLIPrior.believedValue pCoef (pState s) = uPrice s := by
  unfold FiniteBLIPrior.believedValue
  rw [univ_S1, Finset.sum_pair subtype_p_ne_q]
  simp [pCoef, table_apply, pW_ne_qW.symm]

/-- **The push wins under the wireheading identity**: `𝔼[U | push] = 41/50 > 9/50 = 𝔼[U | honest]`.
Source: mandate T9; bli-soto-b-058 ("actions that elicit favourable pushes score highly")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem push_beats_honest :
    condExp pushPrior.μ pushPrior.U (fun ω => pAct ω = true) = 41 / 50 ∧
      condExp pushPrior.μ pushPrior.U (fun ω => pAct ω = false) = 9 / 50 := by
  constructor <;>
  · unfold condExp integralOf massOf pushPrior pMass sProb bProb wProb hiProb pAct
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, ind_true, ind_false]
    norm_num

/-- **Under `μ` conditioned on each table, the push lowers the fact `u` tracks**:
`𝔼[[world] | push, state = T] = 1/5 < 4/5 = 𝔼[[world] | honest, state = T]` for both `T`. These
are conditionals of `μ`, not prices of `T` (the tables price only `p` and `q`); and since `world`
is independent of the state in `pushPrior`, the two tables give the same numbers.
Source: mandate T9 ("the pushed action lowers `𝔼[[world] | act = push, state = T]` for both `T`")
Kind: N+
Fidelity: exact (the mandate's letter; `world` independent of the state, disclosed)
Hyps: (a) none -/
theorem push_lowers_world (s : Fin 2) :
    condExp pushPrior.μ (fun ω => ind ω.2.2.2)
        (fun ω => pushPrior.state ω = pState s ∧ pAct ω = true) = 1 / 5 ∧
      condExp pushPrior.μ (fun ω => ind ω.2.2.2)
        (fun ω => pushPrior.state ω = pState s ∧ pAct ω = false) = 4 / 5 := by
  fin_cases s <;> constructor <;>
  · unfold condExp integralOf massOf pushPrior pMass sProb bProb wProb hiProb pAct
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, ind_true, ind_false,
      pState_zero, pState_one, Shi_ne_Slo, Slo_ne_Shi]
    norm_num [Thi_ne_Tlo, Ne.symm Thi_ne_Tlo]

/-- The branch probabilities given the action: `μ(Shi | push) = 9/10`, `μ(Shi | honest) = 1/10`.
Source: mandate T9
Kind: N+
Fidelity: exact -/
theorem hi_given_act :
    massOf pushPrior.μ (fun ω => pAct ω = true ∧ pushPrior.state ω = Shi) /
        massOf pushPrior.μ (fun ω => pAct ω = true) = 9 / 10 ∧
      massOf pushPrior.μ (fun ω => pAct ω = false ∧ pushPrior.state ω = Shi) /
        massOf pushPrior.μ (fun ω => pAct ω = false) = 1 / 10 := by
  constructor <;>
  · unfold massOf pushPrior pMass sProb bProb wProb hiProb pAct
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, pState_zero,
      pState_one, Shi_ne_Slo, Slo_ne_Shi]
    norm_num [Thi_ne_Tlo, Ne.symm Thi_ne_Tlo]

end Push

end Cleanroom.Bli.UdtBliCore
