/-
  lateral-dtype.lean  —  UNCHECKED — for the Lean-verify agent.

  Companion to findings/lateral.md §1.5.

  WHAT THIS IS MEANT TO CAPTURE (plain English):
  The "systematized winning / why-ain'cha-rich" face of v2's conditional-martingale ⇒ Value step.
  On a finite world set W and finite option menu J, with a novice weighting π, expert estimates
  `Eo : J → ℝ` of each option (the row-wise expert expectations, i.e. 𝔼_π(E(O^j))), the novice's
  own estimate `Ediag : ℝ` of the realized (diagonal) return of the recommended strategy, and the
  novice's estimate `Eopt : J → ℝ` of each fixed option:
    IF
      (CM)  the conditional-martingale defect vanishes:  Ediag = ∑ⱼ (α j) * Eo j
            [the diagonal return's novice-expectation equals the α-weighted future verdicts —
             this is exactly Thm 4.12.3 (thm:ccee) applied per option and summed, the line-3 step]
      (UM)  the unconditional-martingale defect vanishes per option: Eopt j = Eo j
            [𝔼_π(O^j) = 𝔼_π(E O^j), i.e. Thm 4.12.1 (thm:cee), the line-6 step]
      (WIN) the recommended (argmax) strategy's α-weighted verdict dominates every fixed option's
            verdict:  ∀ i, ∑ⱼ (α j) * Eo j  ≥  Eo i      [hard argmax: α concentrates on the max,
             so the weighted mean is ≥ any single coordinate — the δ→0 / soft-gap=0 face]
    THEN
      WAR-optimality:  ∀ i, Ediag ≥ Eopt i
      ("the realized return of deferring to the expert beats committing to any fixed option" —
       Value (LI form), in the δ=0 hard-selection shadow).

  This is the δ=0 shadow re-skinned in "no fixed option beats the policy" language so the
  optimality / why-ain'cha-rich reading is explicit. It is a specialization of the same content as
  Deference.value_of_CM in lean-deference/LeanDeference.lean, kept fully self-contained here (no
  cross-file import) so the verifier can check it in isolation.

  FAITHFULNESS / NON-VACUITY ANALYSIS (read before trusting):
  - Quantifiers: the conclusion is ∀ i, an inequality between two REALS (Ediag, Eopt i). Good —
    matches "for every fixed option i, deferring beats committing to i."
  - Are hypotheses faithful (not smuggling the conclusion)? The conclusion is `Ediag ≥ Eopt i`.
    The hypotheses are: CM (an EQUALITY defining Ediag via the α-weighted verdicts), UM (an
    EQUALITY Eopt j = Eo j), WIN (the *weighted-verdict* dominates each *verdict*). None of these is
    `Ediag ≥ Eopt i` directly. The proof is: Eopt i = Eo i (UM) ≤ ∑ⱼ α j * Eo j (WIN) = Ediag (CM).
    So WIN does the real work — and WIN is the genuine softmax/argmax content, NOT the conclusion:
    WIN compares α-weighted verdicts to single verdicts (`Eo`), whereas the conclusion compares
    `Ediag` to `Eopt`. They coincide only AFTER applying CM and UM, which are the trusted LI
    theorems. So no smuggling.
  - Non-vacuous? It FAILS without CM: take the DDB Fig. 2 / v2 §1.3 anti-expert frame where the
    conditional-martingale defect is nonzero (Ediag ≠ ∑ α Eo); then `WAR_of_martingale` is simply
    not applicable (its CM hypothesis is false there), matching the fact that Value genuinely fails
    on that frame. And the inequality is real (not 0=0): with Eo = (1,0), α=(1,0), i=1: LHS Eopt 1 =
    0 ≤ Ediag = 1, a strict inequality, so the statement is not a disguised `True`/`x ≤ x`.
  - WHAT IT DOES NOT CLAIM: it does not prove CM, UM, or WIN — those are hypotheses (CM, UM are the
    LI martingale theorems; WIN is the hard-argmax/softmax-gap fact). It does not handle the δ>0
    slack (the −δ log k term); this is the δ=0 idealization. It says NOTHING about asymptotics ≂ₙ.
    It is purely the finite real-arithmetic core of the optimality reading.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Real.Basic

open Finset

namespace LateralDType

variable {J : Type*} [Fintype J]

/-- **WAR-optimality from the martingale identities (δ=0 hard-selection shadow).**
    `Ediag` = novice-expectation of the realized (diagonal) return of the recommended strategy;
    `Eo j` = novice-expectation of the future self's verdict on option `j`;
    `Eopt j` = novice-expectation of fixed option `j`; `α j` = (hard) selection weights.
    Under CM (diagonal tracks the α-weighted verdicts), UM (`Eopt = Eo`), and WIN (weighted verdict
    dominates each verdict), the realized return beats every fixed option. -/
theorem WAR_of_martingale
    (α : J → ℝ) (Eo Eopt : J → ℝ) (Ediag : ℝ)
    (CM  : Ediag = ∑ j, α j * Eo j)
    (UM  : ∀ j, Eopt j = Eo j)
    (WIN : ∀ i, Eo i ≤ ∑ j, α j * Eo j) :
    ∀ i, Eopt i ≤ Ediag := by
  intro i
  calc Eopt i = Eo i := UM i
    _ ≤ ∑ j, α j * Eo j := WIN i
    _ = Ediag := CM.symm

/-- **The WIN hypothesis is discharged for an honest convex combination dominating its own
    coordinates' max.** If `α` is a probability weight (nonneg, sums to 1) then the α-weighted mean
    of `Eo` is ≥ the value at any coordinate that attains the maximum. This is the hard (δ=0) face of
    the softmax gap: at temperature 0 the weighted verdict equals the max verdict, which dominates
    every single verdict. We state the clean special case: if `α` concentrates all weight on a
    maximizer `m` (α m = 1, α j = 0 otherwise), the weighted mean equals `Eo m = max`, hence ≥ Eo i.
    (The general softmax bound with slack −δ·card J is `DeferenceExtra.softmax_lower_bound` in the
    confirmed file; here we only need the δ=0 corner to feed `WAR_of_martingale`.) -/
theorem WIN_of_argmax
    [DecidableEq J] (Eo : J → ℝ) (m : J) (hm : ∀ j, Eo j ≤ Eo m) :
    ∀ i, Eo i ≤ ∑ j, (if j = m then (1:ℝ) else 0) * Eo j := by
  intro i
  have hsum : (∑ j, (if j = m then (1:ℝ) else 0) * Eo j) = Eo m := by
    -- turn `(if j=m then 1 else 0) * Eo j` into `if j=m then Eo j else 0`, then collapse the sum.
    -- `Finset.sum_ite_eq'` over `univ` reduces `∑ j, if j=m then Eo j else 0` to `Eo m`
    -- (using `Finset.mem_univ`); `simp` picks the right `sum_ite_eq'` (Fintype/Finset variant).
    simp [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hsum]
  exact hm i

/-- **End-to-end (δ=0): recommended hard-argmax strategy + martingales ⇒ WAR-optimal.**
    Combines the two lemmas: with the hard-argmax selection concentrating on a maximizer `m`,
    CM and UM give that the realized diagonal return beats every fixed option. -/
theorem WAR_of_argmax
    [DecidableEq J] (Eo Eopt : J → ℝ) (Ediag : ℝ) (m : J)
    (hm : ∀ j, Eo j ≤ Eo m)
    (CM : Ediag = ∑ j, (if j = m then (1:ℝ) else 0) * Eo j)
    (UM : ∀ j, Eopt j = Eo j) :
    ∀ i, Eopt i ≤ Ediag :=
  WAR_of_martingale (fun j => if j = m then 1 else 0) Eo Eopt Ediag CM UM (WIN_of_argmax Eo m hm)

end LateralDType

#print axioms LateralDType.WAR_of_martingale
#print axioms LateralDType.WIN_of_argmax
#print axioms LateralDType.WAR_of_argmax
