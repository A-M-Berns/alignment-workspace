/-
  CANDIDATE — UNCHECKED. For the dedicated Lean-verify agent ONLY.
  Do NOT compile under the multi-agent run (OOM risk). A single serial agent checks this.

  ===========================================================================
  WHAT THIS FILE IS ABOUT (Fast-Student / Slow-Teacher merge, v2 §10 + idea 3/4)
  ===========================================================================
  The merge builds  B_t(φ) := E^A_t(⌜P^H_{f(t)}(φ)⌝)  — the fast AI `A`'s day-t estimate
  of the slow human `H`'s day-f(t) price of φ. The human `H` is asked to ENDORSE B as an
  external expert in the sense of v2 §10 (Value). The crux (ideate idea 3 "Hop 2") is the
  CROSS-AGENT step, which is NOT honestly Lean-statable without LI's feedback machinery
  (LUVs, generable weightings, the criterion). So this file does NOT attempt the LI
  martingale.

  Instead it kernel-checks the SMALL ALGEBRAIC MECHANISM that the Python micro-example
  (models/merging_inductors_micro.py) verified numerically and that makes the difference
  between "good feedback ⇒ endorsement" and "no feedback ⇒ endorsement FAILS":

     In the 2-option merge menu  O¹ = μ  ("φ true"),  O² = 1−μ  ("φ false"),  μ ∈ [1/2,1],
     the softmax selector at temperature δ uses the EXPERT ESTIMATE b = B_t(φ) (NOT the
     truth μ = P^H_{f(t)}(φ)). The realized strategy return is
         S(b) := σ(b)·μ + (1−σ(b))·(1−μ),   σ(b) := softmax weight on O¹ from (b, 1−b).
     CLAIM (this file): S(b) is MONOTONE NONDECREASING in the estimate b.
     Hence a DOWNWARD feedback bias (b < μ, the no-feedback case) can only LOWER the
     realized return below the unbiased value S(μ); an UNBIASED estimate (b = μ, what
     good feedback delivers, thm:wubexp) maximizes it. This is exactly why endorsement
     tracks the feedback bias.

  HOW FAITHFUL IS THIS? (the load-bearing self-audit, per SCOPE rule 4)
  --------------------------------------------------------------------------
  * It CAPTURES: the precise sense in which a biased B-estimate degrades the deferred
    decision through the softmax selector — the engine of part (b)'s no-feedback hole.
  * It does NOT capture, and does NOT claim to: (i) that B is a logical inductor;
    (ii) the cross-agent martingale E^H_t(X·w) ≂ E^H_t(B·w) (idea 3 Hop 2 — the genuine
    open step); (iii) any asymptotic ≂ statement; (iv) any LI theorem. Those need LI
    machinery absent from this finite real-arithmetic lemma.
  * NON-VACUITY: the conclusion is a nontrivial inequality `S b ≤ S c` for `b ≤ c`; it is
    FALSE if one drops `μ ≥ 1/2` (then S is *decreasing* in b — the bet flips), so the
    hypothesis is load-bearing, not smuggled. We model σ abstractly by ANY nondecreasing
    selector with σ ∈ [0,1]; the softmax IS such a selector (monotone in b for fixed δ),
    so the lemma applies to it, but we do not re-prove softmax monotonicity here (it is in
    the confirmed LeanDeference.softmax_lower_bound family). Stating it for a general
    monotone σ makes the *mechanism* explicit and keeps the file tiny.
  * SMUGGLING CHECK: we do NOT assume S(b) ≥ μ (that would be the conclusion of Value).
    We assume only σ monotone & in [0,1] and μ ≥ 1/2, and CONCLUDE monotonicity of S and
    the corollary that the unbiased estimate dominates any downward-biased one. The Value
    inequality S ≥ O^i itself is the SEPARATE confirmed content of LeanDeference; here we
    isolate the orthogonal fact "bias only hurts".
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MergingInductors

/-- The realized 2-option strategy return as a function of the softmax weight `σ ∈ [0,1]`
    on option `O¹ = μ` (with `O² = 1−μ`):
      `S = σ·μ + (1−σ)·(1−μ) = (1−μ) + σ·(2μ−1)`.
    Here `σ = σ(b)` is the selector applied to the EXPERT ESTIMATE `b = B_t(φ)`. -/
def S (μ σ : ℝ) : ℝ := σ * μ + (1 - σ) * (1 - μ)

/-- Algebraic rewrite: `S μ σ = (1 - μ) + σ * (2*μ - 1)`. -/
theorem S_eq (μ σ : ℝ) : S μ σ = (1 - μ) + σ * (2 * μ - 1) := by
  unfold S; ring

/-- **MAIN: bias only hurts (monotonicity of the realized return in the estimate).**

    If the option value satisfies `μ ≥ 1/2` (so betting "φ true" is the right/weakly-right
    bet) and the selector `σ` is monotone in the estimate (`σb ≤ σc` whenever the estimate
    rises `b ≤ c`), then the realized return is monotone: `S μ σb ≤ S μ σc`.

    INTERPRETATION: raising the AI's estimate `b = B_t(φ)` toward (or above) the truth `μ`
    can only RAISE the deferred decision's value. Hence a persistent DOWNWARD feedback bias
    (`σb < σμ`, the unobservable/no-feedback class) strictly lowers `S` below the unbiased
    value `S μ σμ`. Good feedback (`thm:wubexp`) drives `b → μ`, recovering the maximum. -/
theorem bias_only_hurts (μ σb σc : ℝ)
    (hμ : (1:ℝ)/2 ≤ μ) (hσ : σb ≤ σc) :
    S μ σb ≤ S μ σc := by
  rw [S_eq, S_eq]
  have h2μ : (0:ℝ) ≤ 2 * μ - 1 := by linarith
  have : σb * (2 * μ - 1) ≤ σc * (2 * μ - 1) :=
    mul_le_mul_of_nonneg_right hσ h2μ
  linarith

/-- **Corollary: the unbiased estimate dominates any downward-biased one.**
    If the selector at the biased estimate is no larger than at the truth (`σbias ≤ σtrue`,
    which holds for a monotone selector when the estimate is biased downward), then the
    biased realized return is `≤` the unbiased one. This is the formal shadow of the
    Python result: `tail-avg Shat (no feedback) = 0.30 < 0.70 = tail-avg Shat (good feedback)`
    on `μ = 0.70`. -/
theorem unbiased_dominates (μ σbias σtrue : ℝ)
    (hμ : (1:ℝ)/2 ≤ μ) (h : σbias ≤ σtrue) :
    S μ σbias ≤ S μ σtrue :=
  bias_only_hurts μ σbias σtrue hμ h

/-- **Sanity / non-vacuity witness.** The hypothesis `μ ≥ 1/2` is load-bearing: when
    `μ < 1/2` the monotonicity REVERSES (a higher estimate hurts). This lemma exhibits the
    reversal, certifying that `bias_only_hurts` is not vacuously true and that we did not
    smuggle a sign. With `μ = 0` we get `S 0 σ = 1 - σ`, strictly decreasing in σ. -/
theorem reversal_when_mu_small (σb σc : ℝ) (hσ : σb ≤ σc) :
    S 0 σc ≤ S 0 σb := by
  have e1 : S 0 σc = 1 - σc := by unfold S; ring
  have e2 : S 0 σb = 1 - σb := by unfold S; ring
  rw [e1, e2]; linarith

end MergingInductors

-- Axiom audit: a genuine proof prints only [propext, Classical.choice, Quot.sound];
-- any `sorryAx` means NOT verified.
#print axioms MergingInductors.bias_only_hurts
#print axioms MergingInductors.unbiased_dominates
#print axioms MergingInductors.reversal_when_mu_small
