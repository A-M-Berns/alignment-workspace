import Cleanroom.Bli.UdtBliCore.WitnessCorr
import Cleanroom.Bli.UdtBliCore.Decomposition
import Cleanroom.Bli.UdtBliCore.MaterialConditional

/-!
# `udt-bli-core` · Lca: the latest-common-ancestor rule refuted (T4c; bli-soto-b-2-023)

Diffractor's counterexample to his own rule, as Abram read it (journal l. 1488–1508;
ATTRIBUTION-UNVETTED): counterlogical mugging with epistemic states *prior* → *informed* →
{*give*, *get*}; *get* is good iff the *give* branch gives; *prior* thinks paying is good;
*informed* has a good guess of the coin and thinks not. The latest common ancestor of *give* and
*get* is *informed*, so the LCA rule — evaluate cross-branch effects from the LCA's epistemic
state — says don't pay, against the prior-optimal policy.

Finite model (`lcaPrior`): the decision-day tables are `give = Ask = (1, 0)` and
`get = Rec = (0, 1)`, each of prior mass `1/2`; the *informed* state is the intermediate signal
`guess : Bool` (`true` = "the coin says give"), right with probability `19/20`; the policy point
at `give` is `pay = true` / `refuse = false`, independent and fair; the utility is `−10·[pay]` on
`give` and `100·[pay]` on `get`. Then:

* the one-step rule at `give` pays (`EU give pay = 45 > 0`), and the constant pay policy is
  prior-optimal among the positive-mass policies (`45 > 0`) — the *prior* verdict. The policy
  coordinate is one coin for both tables (`pp ω _ = ω.2.2`), so `IndependentPoints` fails and
  the only positive policies are the two constants; every non-constant policy is null, which is
  why the optimality clause is stated with the guarded `IsPriorOptimalOnSupport` (the unguarded
  predicate would compare against the junk `exAnteValue = 0` of the null policies);
* the **LCA rule**, `lcaValue a := 𝔼[U | pp · give = a ∧ guess = true]` (the give point evaluated
  from the informed state's information), refuses: `lcaValue pay = −9/2 < 0 = lcaValue refuse`;
* the surviving neighbour is partition invariance (`EU_eq_sum_partition`): the one-step value is
  the *sum* over both values of the informed signal, `45 = ½·(−9/2) + ½·(189/2)`, of which the LCA
  rule keeps one summand.

`refuted` per [[plan]] §0.4 rule 3: (i) the source's sentence, "Diff argues that the latest common
ancestor is the one to make happy when thinking about cross-branch effects between b and c … Diff
now recants on this view" (journal l. 1488–1490); (ii) the reading formalized: the LCA rule
evaluates the give point under the informed state's conditional measure (ATTRIBUTION-UNVETTED);
(iii) the surviving neighbour: the partition-invariant decomposition.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

namespace Lca

/-- The masses of the four-branch model: `(state, guess, point)`; the guess is right with
probability `19/20`, the point is a fair coin independent of everything.
Source: bli-soto-b-2-023 ("*informed* has a good guess about the value of the logical coin")
Kind: D
Fidelity: exact (the numbers are this run's; the source gives none) -/
def lcaMass : Fin 2 × Bool × Bool → ℚ := fun ω =>
  1 / 2 * (if (ω.1 = 0) = (ω.2.1 = true) then 19 / 20 else 1 / 20) * (1 / 2)

/-- The utility: `−10·[pay]` on `give`, `100·[pay]` on `get`.
Source: bli-slides-034 (the mugging table)
Kind: D
Fidelity: exact -/
def lcaU : Fin 2 × Bool × Bool → ℚ := fun ω =>
  if ω.1 = 0 then (if ω.2.2 then -10 else 0) else (if ω.2.2 then 100 else 0)

/-- **The four-branch prior** (states `give`, `get`; signal `guess` for the informed state).
Source: bli-soto-b-2-023; mandate T4(c)
Kind: D
Fidelity: variant: the *prior* and *informed* states are the prior measure and the signal
coordinate, not day-`m` tables (disclosed) -/
def lcaPrior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool × Bool) lcaMass
    (fun ω => by unfold lcaMass; split_ifs <;> norm_num)
    (by
      unfold lcaMass
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
      norm_num)
    (fun ω => twoState ω.1) two_zeroOne (fun ω _ => ω.2.2) lcaU

/-- The informed signal.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def guess (ω : Fin 2 × Bool × Bool) : Bool := ω.2.1

/-- **The LCA rule's value** of the give point: the expectation conditioned on the point *and on
the informed state's information* `guess = true`.
Source: bli-soto-b-2-023 (the LCA rule, as read: ATTRIBUTION-UNVETTED)
Kind: D
Fidelity: variant: "the informed state" is the event `guess = true` (disclosed) -/
def lcaValue (a : Bool) : ℚ :=
  condExp lcaPrior.μ lcaPrior.U (fun ω => lcaPrior.pp ω T1 = a ∧ guess ω = true)

/-- The informed state believes the coin says `give` with probability `19/20`.
Source: bli-soto-b-2-023 ("a good guess")
Kind: L
Fidelity: n/a -/
lemma informed_believes_give :
    massOf lcaPrior.μ (fun ω => guess ω = true ∧ lcaPrior.state ω = T1) /
      massOf lcaPrior.μ (fun ω => guess ω = true) = 19 / 20 := by
  unfold lcaPrior
  rw [handPrior_massOf, handPrior_massOf]
  simp only [handPrior]
  norm_num [massOf, lcaMass, guess, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- The one-step values at `give`: `45` for pay, `0` for refuse.
Source: bli-soto-b-2-023 ("*prior* thinks it's a good idea to pay up")
Kind: L
Fidelity: n/a -/
lemma EU_give (a : Bool) : lcaPrior.EU T1 a = if a then 45 else 0 := by
  cases a <;>
  · unfold FiniteBLIPrior.EU lcaPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, lcaMass, lcaU, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- The LCA values: `−9/2` for pay, `0` for refuse.
Source: bli-soto-b-2-023 ("*informed* … doesn't think it is worth paying up")
Kind: L
Fidelity: n/a -/
lemma lcaValue_eq (a : Bool) : lcaValue a = if a then -9 / 2 else 0 := by
  cases a <;>
  · unfold lcaValue lcaPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, lcaMass, lcaU, guess, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- The ex-ante values of the constant policies: `45` for pay, `0` for refuse; non-constant
policies are null.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exAnteValue_const (c : Bool) : lcaPrior.exAnteValue (fun _ => c) = if c then 45 else 0 := by
  cases c <;>
  · unfold FiniteBLIPrior.exAnteValue lcaPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, lcaMass, lcaU, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- Non-constant policies are null.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_eq_zero (π : Policy twoTables Bool) (h : ∀ c, (fun _ : ↥twoTables => c) ≠ π) :
    lcaPrior.policyMass π = 0 := by
  unfold FiniteBLIPrior.policyMass lcaPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  simp [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, h]

/-- **The LCA rule refuted**: the one-step rule at `give` pays and the constant pay policy is
prior-optimal among the positive-mass policies (the two constants; every other policy is null
on this prior, so the guarded predicate is the honest one), while the LCA rule refuses.
Source: bli-soto-b-2-023 (journal l. 1488–1490, Diffractor's recantation as Abram reads it:
ATTRIBUTION-UNVETTED); mandate T4(c)
Kind: N+
Fidelity: exact (finite four-branch model; the informed state as a signal coordinate; optimality
among positive-mass policies)
Hyps: (a) none -/
theorem lca_refuted :
    lcaPrior.IsOneStepChoice T1 true ∧ ¬ lcaPrior.IsOneStepChoice T1 false ∧
      lcaPrior.IsPriorOptimalOnSupport (fun _ => true) ∧
      lcaValue true < lcaValue false ∧ ¬ MatCond.IsArgmax lcaValue true := by
  refine ⟨fun b => ?_, fun h => ?_, fun π' hπ' => ?_, ?_, fun h => ?_⟩
  · rw [EU_give, EU_give]; cases b <;> norm_num
  · have := h true; rw [EU_give, EU_give] at this; norm_num at this
  · rw [exAnteValue_const]
    by_cases hc : ∃ c, (fun _ : ↥twoTables => c) = π'
    · obtain ⟨c, rfl⟩ := hc
      rw [exAnteValue_const]; cases c <;> norm_num
    · have : ∀ c, (fun _ : ↥twoTables => c) ≠ π' := fun c hc' => hc ⟨c, hc'⟩
      rw [policyMass_eq_zero π' this] at hπ'
      exact absurd hπ' (lt_irrefl _)
  · rw [lcaValue_eq, lcaValue_eq]; norm_num
  · have := h false; rw [lcaValue_eq, lcaValue_eq] at this; norm_num at this

/-- **The surviving neighbour**: the one-step value decomposes over the informed signal —
`EU give pay = ½ · (−9/2) + ½ · (189/2) = 45` — and the LCA rule keeps only the `guess = true`
summand. Partition invariance (`EU_eq_sum_partition`) is the well-posed statement.
Source: bli-soto-b-2-023 ("UDT cares about a weighted sum over any *partition*")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem partition_survives :
    massOf lcaPrior.μ (fun ω => lcaPrior.pp ω T1 = true ∧ guess ω = true) /
        lcaPrior.ppMass T1 true = 1 / 2 ∧
      massOf lcaPrior.μ (fun ω => lcaPrior.pp ω T1 = true ∧ guess ω = false) /
        lcaPrior.ppMass T1 true = 1 / 2 ∧
      condExp lcaPrior.μ lcaPrior.U (fun ω => lcaPrior.pp ω T1 = true ∧ guess ω = false) =
        189 / 2 ∧
      lcaPrior.EU T1 true = ∑ g, massOf lcaPrior.μ (fun ω => lcaPrior.pp ω T1 = true ∧ guess ω = g) /
        lcaPrior.ppMass T1 true *
        condExp lcaPrior.μ lcaPrior.U (fun ω => lcaPrior.pp ω T1 = true ∧ guess ω = g) := by
  refine ⟨?_, ?_, ?_, lcaPrior.EU_eq_sum_partition guess T1 true⟩ <;>
  · simp only [FiniteBLIPrior.ppMass, lcaPrior]
    simp only [handPrior_massOf, handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, lcaMass, lcaU, guess, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

end Lca

end Cleanroom.Bli.UdtBliCore
