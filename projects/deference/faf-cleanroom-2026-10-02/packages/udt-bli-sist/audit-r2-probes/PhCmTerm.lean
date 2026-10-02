import Cleanroom.Bli.UdtBliSist.PhCm

/-!
# Audit r2 (fidelity) probe — the term reading on the CM/PH prior "mixes both problems"

Not imported by the library. bli-soto-a-2-015's claim has two halves: under the written-out
reading the argmax at `CM_A` is the CM-optimal action although `P(CM) = ½` (shipped:
`PhCm.verdict`, `PhCm.isOneStepChoice_pay`); "under Soto's term reading `A(Q_m) = a` the argmax
mixes both problems". The package renders the second half only as the *responsive* variant
(`PhCm.verdict_responsive`: the PH tables reading `CM_A`), whose `Source:` line cites the term
reading. This probe checks the term reading itself — `IsTermChoice`, the constant policy, the
package's own rendering of `A(Q_m) = a` (mandate §3.3) — on the honest prior (`X = PH_A`):

* `term_exAnte`: `exAnteValue (const a) = ∑_s w s · phPay s a` for every `X` — the constant
  policy never sees which table the PH states read;
* `term_diff`: `exAnteValue (const pay) − exAnteValue (const refuse) =
  w(CM_R)·V − w(CM_A)·c + w(PH_R)·V' − w(PH_A)·c'` — numerically the responsive variant's
  difference, on the honest prior, by a different mechanism (the constant policy pays at every
  node, so every class's payoff enters);
* `term_instance_refuse`: at the shipped instance (`1/4` each, `(100, 10)`, `c' = 200`,
  `V' = 0`) the term rule refuses (`−55/2`) while the one-step rule pays (`PhCm.instance_pay`,
  `45/2`) — bli-soto-a-2-015's "mixes both problems", machine-checked under the constant-policy
  reading.
-/

namespace Cleanroom.Bli.UdtBliSist.PhCm

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable (w : Fin 4 → ℚ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) (X : ↥fourTables)
  (c V c' V' : ℚ)

/-- The term reading's value on the CM/PH prior: the base-weighted payoff of the constant policy,
whatever table the PH states read.
Source: audit r2 probe (bli-soto-a-2-015, the term-reading half)
Kind: P
Fidelity: exact -/
theorem term_exAnte (a : Bool) :
    (phPrior w hw hw1 X c V c' V').exAnteValue (constPolicy a) =
      ∑ s, w s * phPay c V c' V' s a := by
  unfold phPrior FiniteBLIPrior.exAnteValue condExp
  change (phData w hw hw1 X c V c' V').toPrior.policyUtil (constPolicy a) /
    (phData w hw hw1 X c V c' V').toPrior.policyMass (constPolicy a) = _
  rw [IndepData.policyUtil_toPrior, IndepData.policyMass_toPrior]
  have hν : 0 < (phData w hw hw1 X c V c' V').ν (constPolicy a) :=
    prodLaw_pos (fun _ _ => by simp [fourHalf]) _
  rw [mul_div_cancel_left₀ _ (ne_of_gt hν)]
  rfl

/-- The term reading mixes both problems: the difference carries the PH payoffs with the PH
masses, for every `X` (in particular on the honest prior `X = PH_A`).
Source: audit r2 probe (bli-soto-a-2-015: "under Soto's term reading … the argmax mixes both
problems")
Kind: P
Fidelity: exact -/
theorem term_diff :
    (phPrior w hw hw1 X c V c' V').exAnteValue (constPolicy true) -
        (phPrior w hw hw1 X c V c' V').exAnteValue (constPolicy false) =
      w 1 * V - w 0 * c + w 2 * V' - w 3 * c' := by
  rw [term_exAnte, term_exAnte, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [phPay, ind_true, ind_false]
  ring

/-- At the shipped instance, on the honest prior (`X = PH_A`): the term rule refuses
(difference `−55/2`) while the one-step rule pays (`PhCm.instance_pay`, `45/2`).
Source: audit r2 probe (bli-soto-a-2-015)
Kind: N+
Fidelity: exact -/
theorem term_instance_refuse :
    (phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0).exAnteValue (constPolicy true) -
        (phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0).exAnteValue (constPolicy false) =
      -(55 / 2) ∧
    IsTermChoice (phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0) false ∧
      ¬ IsTermChoice (phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0) true := by
  have hd := term_diff wQ wQ_nonneg wQ_sum fOther 10 100 200 0
  have hd' : (phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0).exAnteValue (constPolicy true) -
      (phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0).exAnteValue (constPolicy false) =
        -(55 / 2) := by
    rw [hd]; norm_num [wQ]
  refine ⟨hd', fun b => ?_, fun h => ?_⟩
  · cases b
    · exact le_rfl
    · linarith
  · have := h false
    linarith

end Cleanroom.Bli.UdtBliSist.PhCm
