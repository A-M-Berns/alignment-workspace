import Cleanroom.Bli.UdtBliTiling.Defs
import Cleanroom.Bli.UdtBliCore.Mugging

/-!
# `udt-bli-tiling` · MuggingTiles: the mugging prior tiles for one-step UDT and not for the
updateful rule (T3, load-bearing 3)

On `muggingPrior r` (`|r a| ≤ 10`): every one-step policy pays at `Ask`, is prior-optimal and
has no strict preference for precommitment (`oneStep_tiles`); every updateful policy refuses at
`Ask` and strictly prefers the precommitment "pay at `Ask`" (`updateful_not_tiles`); and the
structural audit (`structure_audit`): `IndependentPoints`, `ReflectivePolicy`, `NDHOME`,
`NDPOLICY` hold while `LocalUtility` and `NoCrossBranch` fail. So T1's package is **sufficient,
not necessary** for one-step tiling, and the updateless/updateful separation (U5) and the tiling
failure (T2) live on different priors ([[bli-program]] §3.9 U9(4)).

"The one-step policy" is not unique here: `EU` at `Rec` and `Other` is constant in the action
(the value reads only the `Ask` point, `exAnteValue_eq`), so every statement quantifies over all
one-step policies, and `tie_witness` records the consequence for bli-soto-a-2-016's "coincide":
two policies with different decisions, both tiling, with equal value.

Sources: [[bli-program]] §3.9 U9(4); bli-soto-b-034 (D0's "trivial form" theorems — these rows
are exactly those); bli-soto-a-2-016 ("updating didn't make that big a difference"); mandate T3.
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Mugging Finset

namespace MuggingTiles

variable (r : Bool → ℚ)

/-- A one-step policy pays at `Ask` (for `|r| ≤ 10`).
Source: [[bli-program]] §3.9 U5
Kind: L
Fidelity: n/a -/
lemma oneStepPolicy_ask (hr : ∀ a, |r a| ≤ 10) (π : Policy mugTables Bool)
    (h1 : (muggingPrior r).IsOneStepPolicy π) : π askT = true := by
  by_contra h
  have h' : π askT = false := by simpa using h
  exact not_isOneStepChoice_ask_refuse r hr (h' ▸ h1 askT)

/-- **Every one-step policy on the mugging prior tiles**: it pays at `Ask`, is prior-optimal and
has no strict preference for precommitment — although `LocalUtility` and `NoCrossBranch` fail
here (`structure_audit`), so this is tiling *outside* T1's package.
Source: [[bli-program]] §3.9 U9(4) ("on the mugging prior one-step UDT tiles by direct
computation"); bli-soto-b-034 (D0 "trivial form"); mandate T3(i)
Kind: C (`exAnteValue_eq`, `isPriorOptimal_const_pay`, `noStrictPrecommit_of_priorOptimal`)
Fidelity: exact
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem oneStep_tiles (hr : ∀ a, |r a| ≤ 10) (π : Policy mugTables Bool)
    (h1 : (muggingPrior r).IsOneStepPolicy π) :
    π askT = true ∧ (muggingPrior r).IsPriorOptimal π ∧ NoStrictPrecommit (muggingPrior r) π := by
  have hask := oneStepPolicy_ask r hr π h1
  have hopt : (muggingPrior r).IsPriorOptimal π := by
    intro π'
    rw [exAnteValue_eq, exAnteValue_eq, hask]
    have := isPriorOptimal_const_pay r hr π'
    rw [exAnteValue_eq, exAnteValue_eq] at this
    simpa using this
  exact ⟨hask, hopt, noStrictPrecommit_of_priorOptimal (ndpolicy r) hopt⟩

/-- **No updateful policy on the mugging prior tiles**: it refuses at `Ask`, and the one-point
precommitment "pay at `Ask`" is strictly better by `441/10 + (2/100)(r pay − r refuse) > 0`; so
`¬ NoStrictPrecommitAt π Ask` and `π` is not prior-optimal.
Source: [[bli-program]] §3.9 U9(4) ("the updateful rule fails tiling"); mandate T3(ii)
Kind: N− (for Good's theorem's package: `LocalUtility` fails and so does the conclusion) / C
Fidelity: exact
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem updateful_not_tiles (hr : ∀ a, |r a| ≤ 10) (π : Policy mugTables Bool)
    (hu : (muggingPrior r).IsUpdatefulPolicy π) :
    π askT = false ∧ ¬ NoStrictPrecommitAt (muggingPrior r) π askT ∧
      ¬ (muggingPrior r).IsPriorOptimal π := by
  obtain ⟨hlt, hnopt⟩ := not_isPriorOptimal_of_updateful r hr π hu
  have hask : π askT = false := by
    by_contra h
    have h' : π askT = true := by simpa using h
    exact not_isUpdatefulChoice_ask_pay r (h' ▸ hu askT)
  refine ⟨hask, ?_, hnopt⟩
  apply not_noStrictPrecommitAt_of_lt (b := true) (ndpolicy r _)
  have e : (muggingPrior r).exAnteValue (Function.update π askT true) =
      (muggingPrior r).exAnteValue (fun _ => true) := by
    rw [exAnteValue_eq, exAnteValue_eq, Function.update_self]
  rw [e]; exact hlt

/-- **The structural audit of the mugging prior**: `IndependentPoints`, `ReflectivePolicy`,
`NDHOME`, `NDPOLICY` hold; `LocalUtility` and `NoCrossBranch` fail. Tiling holds here
(`oneStep_tiles`) outside T1's package.
Source: [[bli-program]] §3.9 U9(4); mandate T3(iii)
Kind: N+ / N−
Fidelity: exact
Hyps: (a) none -/
theorem structure_audit :
    (muggingPrior r).IndependentPoints ∧ (muggingPrior r).ReflectivePolicy ∧
      (muggingPrior r).NDHOME ∧ (muggingPrior r).NDPOLICY ∧
      ¬ (muggingPrior r).LocalUtility ∧ ¬ (muggingPrior r).NoCrossBranch :=
  ⟨independentPoints r, reflectivePolicy r, ndhome r, ndpolicy r, not_localUtility r,
    not_noCrossBranch r⟩

/-- **The tie witness for "coincide"**: the pay-everywhere policy and its variant refusing at
`Rec` differ, have the same ex-ante value, and both have no strict preference for precommitment.
So "`P` tiles with respect to `P_σ` only if `P_σ`'s decisions coincide with `P`'s"
(bli-soto-a-2-016) is too strong by the tie case; the tie-aware form is
`noStrictPrecommit_iff_updateful_of_separable` (on separable priors) and, here, "coincide at the
positive-stake table".
Source: bli-soto-a-2-016; mandate T4(f) (the tie witness); mandate T3 trap ("ties at `Rec`")
Kind: N+
Fidelity: exact
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem tie_witness (hr : ∀ a, |r a| ≤ 10) :
    Function.update (fun _ : ↥mugTables => true) recT false ≠ (fun _ => true) ∧
      (muggingPrior r).exAnteValue (Function.update (fun _ => true) recT false) =
        (muggingPrior r).exAnteValue (fun _ => true) ∧
      NoStrictPrecommit (muggingPrior r) (Function.update (fun _ => true) recT false) ∧
      NoStrictPrecommit (muggingPrior r) (fun _ => true) := by
  have hask : Function.update (fun _ : ↥mugTables => true) recT false askT = true :=
    Function.update_of_ne askT_ne_recT _ _
  have hval : (muggingPrior r).exAnteValue (Function.update (fun _ => true) recT false) =
      (muggingPrior r).exAnteValue (fun _ => true) := by
    rw [exAnteValue_eq, exAnteValue_eq, hask]
  have hopt' : (muggingPrior r).IsPriorOptimal (Function.update (fun _ => true) recT false) := by
    intro π'; rw [hval]; exact isPriorOptimal_const_pay r hr π'
  refine ⟨fun h => ?_, hval, noStrictPrecommit_of_priorOptimal (ndpolicy r) hopt',
    noStrictPrecommit_of_priorOptimal (ndpolicy r) (isPriorOptimal_const_pay r hr)⟩
  have := congrFun h recT
  rw [Function.update_self] at this
  exact Bool.false_ne_true this

end MuggingTiles

end Cleanroom.Bli.UdtBliTiling
