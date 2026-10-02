import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# info-voi-latents — the finite information layer (Target 2)

Total variation, the finite Kullback–Leibler divergence, and **Pinsker's inequality** on
`stdSimplex ℝ W`, proved from elementary calculus (no measure theory). Also the log-sum
(grouping) inequality, Jensen for `√`, and `klFin p q = 0 ↔ p = q` under absolute continuity.

Junk values, stated once here: Lean's `x / 0 = 0` and `Real.log 0 = 0` make the finite sum
`∑ w, p w * log (p w / q w)` *finite and zero* on disjoint supports, where the true divergence
is `+∞`. Pinsker is therefore **false** for `klFin` without absolute continuity
(`pinsker_fails_without_absCont`, a test of the encoding), and every KL-carrying statement in
this package carries `AbsCont p q : ∀ w, q w = 0 → p w = 0`.

Mandate: `run/wp/info-voi-latents/info-voi-latents-mandate.md`, Target 2.
-/

namespace Cleanroom.Info.InfoVoiLatents

open Finset Real

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W]

/-- **Total variation** between two finite vectors, `(1/2) ∑ w, |p w − q w|`.
Source: [[generalization-final]] S2 l. 61 (the `TV` of the VOI bound); none: infrastructure
Kind: D
Fidelity: exact -/
def tv (p q : W → ℝ) : ℝ := (1 / 2) * ∑ w, |p w - q w|

/-- **Finite Kullback–Leibler divergence** `∑ w, p w · log (p w / q w)`. With Lean's junk
values (`x / 0 = 0`, `log 0 = 0`) a coordinate with `q w = 0` contributes `0` whatever `p w`
is; the definition renders `KL(p‖q)` only under `AbsCont p q` (see the module docstring).
Source: [[generalization-final]] S2 l. 61, P2 l. 107; none: infrastructure
Kind: D
Fidelity: exact under `AbsCont p q`; junk `0` on the `q w = 0` coordinates otherwise -/
def klFin (p q : W → ℝ) : ℝ := ∑ w, p w * Real.log (p w / q w)

/-- **Absolute continuity** of `p` with respect to `q` on a finite carrier: `q w = 0 → p w = 0`.
Source: none: infrastructure (the hypothesis every KL statement here carries)
Kind: D
Fidelity: exact -/
def AbsCont (p q : W → ℝ) : Prop := ∀ w, q w = 0 → p w = 0

/-! ### Total variation: basic facts and the set form -/

/-- `tv` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tv_nonneg (p q : W → ℝ) : 0 ≤ tv p q := by
  unfold tv
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun w _ => abs_nonneg _)

/-- `tv` is symmetric.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tv_comm (p q : W → ℝ) : tv p q = tv q p := by
  unfold tv
  congr 1
  exact Finset.sum_congr rfl fun w _ => abs_sub_comm _ _

/-- `tv p p = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tv_self (p : W → ℝ) : tv p p = 0 := by
  simp [tv]

/-- **The set form of total variation**: for two distributions,
`tv p q = ∑ w ∈ {w | q w < p w}, (p w − q w)` — the mass `p` puts above `q`. This is the
form the Lipschitz step (Target 3) and the Pinsker reduction use.
Source: none: infrastructure (Target 2(c))
Kind: P
Fidelity: exact -/
theorem tv_eq_sum_filter {p q : W → ℝ} (hp : p ∈ stdSimplex ℝ W) (hq : q ∈ stdSimplex ℝ W) :
    tv p q = ∑ w ∈ univ.filter (fun w => q w < p w), (p w - q w) := by
  have hsum : ∑ w, (p w - q w) = 0 := by
    rw [Finset.sum_sub_distrib, hp.2, hq.2, sub_self]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun w => q w < p w)] at hsum
  have habs : ∑ w, |p w - q w| = ∑ w ∈ univ.filter (fun w => q w < p w), (p w - q w)
      + ∑ w ∈ univ.filter (fun w => ¬ q w < p w), (q w - p w) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun w => q w < p w)]
    congr 1
    · refine Finset.sum_congr rfl fun w hw => ?_
      simp only [mem_filter] at hw
      rw [abs_of_pos (by linarith [hw.2])]
    · refine Finset.sum_congr rfl fun w hw => ?_
      simp only [mem_filter, not_lt] at hw
      rw [abs_of_nonpos (by linarith [hw.2])]
      ring
  have hneg : ∑ w ∈ univ.filter (fun w => ¬ q w < p w), (q w - p w)
      = - ∑ w ∈ univ.filter (fun w => ¬ q w < p w), (p w - q w) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  unfold tv
  rw [habs, hneg]
  linarith

/-! ### The log-sum (grouping) inequality -/

/-- The per-coordinate inequality behind the log-sum inequality: for `0 ≤ a ≤ P`, `0 ≤ b`,
`(b = 0 → a = 0)`, `0 < Q`: `a·log(P/Q) + a − b·(P/Q) ≤ a·log(a/b)`.
Source: none: infrastructure (Target 2(b))
Kind: L
Fidelity: n/a -/
theorem mul_log_div_ge_aux {a b P Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0)
    (hP : 0 ≤ P) (hQ : 0 < Q) (haP : a ≤ P) :
    a * Real.log (P / Q) + a - b * (P / Q) ≤ a * Real.log (a / b) := by
  rcases ha.lt_or_eq with ha' | ha'
  · have hb' : 0 < b := by
      rcases hb.lt_or_eq with h | h
      · exact h
      · exact absurd (hab h.symm) ha'.ne'
    have hP' : 0 < P := lt_of_lt_of_le ha' haP
    have key : 1 - ((a * Q) / (b * P))⁻¹ ≤ Real.log ((a * Q) / (b * P)) :=
      Real.one_sub_inv_le_log_of_pos (by positivity)
    have hlog : Real.log ((a * Q) / (b * P)) = Real.log (a / b) - Real.log (P / Q) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul ha'.ne' hQ.ne',
        Real.log_mul hb'.ne' hP'.ne', Real.log_div ha'.ne' hb'.ne', Real.log_div hP'.ne' hQ.ne']
      ring
    rw [hlog] at key
    have h2 : a * (1 - ((a * Q) / (b * P))⁻¹) = a - b * (P / Q) := by
      rw [inv_div]
      field_simp
    have h3 := mul_le_mul_of_nonneg_left key ha'.le
    rw [h2, mul_sub] at h3
    linarith
  · rw [← ha']
    have : 0 ≤ b * (P / Q) := by positivity
    simp only [zero_mul, zero_add, zero_sub, zero_div]
    linarith

/-- **Log-sum inequality** over a finset: for nonnegative `p q` with `q w = 0 → p w = 0` on
`A`, `(∑_A p) · log ((∑_A p) / (∑_A q)) ≤ ∑_A p w · log (p w / q w)`. Junk-safe: if
`∑_A q = 0` both sides are `0`.
Source: none: infrastructure (Target 2(b), the grouping step of Pinsker)
Kind: P
Fidelity: exact -/
theorem sum_mul_log_div_ge (A : Finset W) (p q : W → ℝ) (hp : ∀ w ∈ A, 0 ≤ p w)
    (hq : ∀ w ∈ A, 0 ≤ q w) (hac : ∀ w ∈ A, q w = 0 → p w = 0) :
    (∑ w ∈ A, p w) * Real.log ((∑ w ∈ A, p w) / (∑ w ∈ A, q w))
      ≤ ∑ w ∈ A, p w * Real.log (p w / q w) := by
  have hP : 0 ≤ ∑ w ∈ A, p w := Finset.sum_nonneg hp
  have hQ : 0 ≤ ∑ w ∈ A, q w := Finset.sum_nonneg hq
  rcases hQ.lt_or_eq with hQ' | hQ'
  · have hterm : ∀ w ∈ A,
        p w * Real.log ((∑ w ∈ A, p w) / (∑ w ∈ A, q w)) + p w
          - q w * ((∑ w ∈ A, p w) / (∑ w ∈ A, q w)) ≤ p w * Real.log (p w / q w) :=
      fun w hw => mul_log_div_ge_aux (hp w hw) (hq w hw) (hac w hw) hP hQ'
        (Finset.single_le_sum hp hw)
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      at hsum
    have hc : (∑ w ∈ A, q w) * ((∑ w ∈ A, p w) / (∑ w ∈ A, q w)) = ∑ w ∈ A, p w := by
      field_simp
    linarith
  · have hq0 : ∀ w ∈ A, q w = 0 := (Finset.sum_eq_zero_iff_of_nonneg hq).1 hQ'.symm
    have hp0 : ∀ w ∈ A, p w = 0 := fun w hw => hac w hw (hq0 w hw)
    rw [Finset.sum_eq_zero hp0, zero_mul]
    exact Finset.sum_nonneg fun w hw => by rw [hp0 w hw]; simp

/-- `0 ≤ klFin p q` for distributions under absolute continuity (Gibbs' inequality).
Source: none: infrastructure (Target 2)
Kind: P
Fidelity: exact -/
theorem klFin_nonneg {p q : W → ℝ} (hp : p ∈ stdSimplex ℝ W) (hq : q ∈ stdSimplex ℝ W)
    (hac : AbsCont p q) : 0 ≤ klFin p q := by
  have h := sum_mul_log_div_ge univ p q (fun w _ => hp.1 w) (fun w _ => hq.1 w)
    (fun w _ => hac w)
  rw [hp.2, hq.2] at h
  simpa [klFin] using h

/-- **Grouping**: splitting the carrier by a predicate `P`, `klFin p q` dominates the binary
divergence of the two group masses.
Source: none: infrastructure (Target 2(b))
Kind: P
Fidelity: exact -/
theorem klFin_ge_grouped {p q : W → ℝ} (hp : p ∈ stdSimplex ℝ W) (hq : q ∈ stdSimplex ℝ W)
    (hac : AbsCont p q) (P : W → Prop) [DecidablePred P] :
    (∑ w ∈ univ.filter P, p w) * Real.log ((∑ w ∈ univ.filter P, p w) / (∑ w ∈ univ.filter P, q w))
      + (∑ w ∈ univ.filter (fun w => ¬ P w), p w)
        * Real.log ((∑ w ∈ univ.filter (fun w => ¬ P w), p w)
          / (∑ w ∈ univ.filter (fun w => ¬ P w), q w))
      ≤ klFin p q := by
  unfold klFin
  rw [← Finset.sum_filter_add_sum_filter_not univ P]
  exact add_le_add
    (sum_mul_log_div_ge _ p q (fun w _ => hp.1 w) (fun w _ => hq.1 w) (fun w _ => hac w))
    (sum_mul_log_div_ge _ p q (fun w _ => hp.1 w) (fun w _ => hq.1 w) (fun w _ => hac w))

/-! ### Binary Pinsker by calculus -/

/-- `a·log(a/b) = −negMulLog a − a·log b` for `0 ≤ a`, `0 < b` (junk-safe at `a = 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mul_log_div_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log (a / b) = -negMulLog a - a * Real.log b := by
  rcases ha.lt_or_eq with ha' | ha'
  · rw [Real.log_div ha'.ne' hb.ne', negMulLog]
    ring
  · rw [← ha']
    simp

/-- The auxiliary function `a ↦ log a − log (1 − a) − 4a` has derivative
`1/a + 1/(1 − a) − 4` on `(0, 1)`.
Source: none: infrastructure (Target 2(a))
Kind: L
Fidelity: n/a -/
theorem hasDerivAt_logitAux {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun a : ℝ => Real.log a - Real.log (1 - a) - 4 * a)
      (1 / a + 1 / (1 - a) - 4) a := by
  have h1 : HasDerivAt Real.log a⁻¹ a := Real.hasDerivAt_log ha.1.ne'
  have h2 : HasDerivAt (fun a : ℝ => Real.log (1 - a)) ((1 - a)⁻¹ * (-1)) a :=
    (Real.hasDerivAt_log (sub_pos.2 ha.2).ne').comp a ((hasDerivAt_id a).const_sub 1)
  have h3 : HasDerivAt (fun a : ℝ => 4 * a) 4 a := by
    simpa using (hasDerivAt_id a).const_mul (4 : ℝ)
  exact ((h1.sub h2).sub h3).congr_deriv (by ring)

/-- `a ↦ log a − log (1 − a) − 4a` is monotone on `(0, 1)`: its derivative
`1/a + 1/(1 − a) − 4 = (1 − 2a)² / (a(1 − a))` is nonnegative there.
Source: none: infrastructure (Target 2(a))
Kind: P
Fidelity: exact -/
theorem logitAux_monotoneOn :
    MonotoneOn (fun a : ℝ => Real.log a - Real.log (1 - a) - 4 * a) (Set.Ioo 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · intro a ha
    exact (hasDerivAt_logitAux ha).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    intro a ha
    exact (hasDerivAt_logitAux ha).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro a ha
    rw [(hasDerivAt_logitAux ha).deriv]
    have ha0 : 0 < a := ha.1
    have ha1 : 0 < 1 - a := sub_pos.2 ha.2
    have : 1 / a + 1 / (1 - a) - 4 = (1 - 2 * a) ^ 2 / (a * (1 - a)) := by
      field_simp
      ring
    rw [this]
    positivity

/-- The binary Pinsker defect `φ_b(a) := KL(a‖b) − 2(a − b)²`, written with `negMulLog` so
that it is continuous on all of `ℝ` (and agrees with `a·log(a/b) + (1−a)·log((1−a)/(1−b))
− 2(a−b)²` for `a ∈ [0,1]`, `b ∈ (0,1)`; `mul_log_div_eq`).
Source: none: infrastructure (Target 2(a))
Kind: D
Fidelity: n/a -/
def binPhi (b a : ℝ) : ℝ :=
  -negMulLog a - negMulLog (1 - a) - a * Real.log b - (1 - a) * Real.log (1 - b)
    - 2 * (a - b) ^ 2

/-- `φ_b(b) = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem binPhi_self (b : ℝ) : binPhi b b = 0 := by
  unfold binPhi negMulLog
  ring

/-- `φ_b` is continuous.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem continuous_binPhi (b : ℝ) : Continuous (binPhi b) := by
  unfold binPhi
  fun_prop

/-- `φ_b'(a) = (log a − log (1−a) − 4a) − (log b − log (1−b) − 4b)` on `(0, 1)`.
Source: none: infrastructure (Target 2(a))
Kind: L
Fidelity: n/a -/
theorem hasDerivAt_binPhi (b : ℝ) {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (binPhi b)
      ((Real.log a - Real.log (1 - a) - 4 * a) - (Real.log b - Real.log (1 - b) - 4 * b)) a := by
  have h1 : HasDerivAt negMulLog (-Real.log a - 1) a := Real.hasDerivAt_negMulLog ha.1.ne'
  have h2 : HasDerivAt (fun a : ℝ => negMulLog (1 - a)) ((-Real.log (1 - a) - 1) * (-1)) a :=
    (Real.hasDerivAt_negMulLog (sub_pos.2 ha.2).ne').comp a ((hasDerivAt_id a).const_sub 1)
  have h3 : HasDerivAt (fun a : ℝ => a * Real.log b) (Real.log b) a := by
    simpa using (hasDerivAt_id a).mul_const (Real.log b)
  have h4 : HasDerivAt (fun a : ℝ => (1 - a) * Real.log (1 - b)) (-Real.log (1 - b)) a :=
    (((hasDerivAt_id a).const_sub 1).mul_const (Real.log (1 - b))).congr_deriv (by ring)
  have h5 : HasDerivAt (fun a : ℝ => 2 * (a - b) ^ 2) (2 * (2 * (a - b))) a :=
    ((((hasDerivAt_id a).sub_const b).fun_pow 2).const_mul (2 : ℝ)).congr_deriv (by norm_num)
  unfold binPhi
  exact (((((h1.neg).sub h2).sub h3).sub h4).sub h5).congr_deriv (by ring)

/-- `φ_b ≥ 0` on `[0, 1]` for `b ∈ (0, 1)`: `φ_b` is antitone on `[0, b]` and monotone on
`[b, 1]` (its derivative has the sign of `a − b` by `logitAux_monotoneOn`), and `φ_b(b) = 0`.
Source: none: infrastructure (Target 2(a))
Kind: P
Fidelity: exact -/
theorem binPhi_nonneg {b : ℝ} (hb : b ∈ Set.Ioo (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ binPhi b a := by
  have hmono := logitAux_monotoneOn
  rcases le_or_gt a b with hab | hab
  · have hanti : AntitoneOn (binPhi b) (Set.Icc 0 b) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 b) (continuous_binPhi b).continuousOn
      · rw [interior_Icc]
        intro x hx
        exact (hasDerivAt_binPhi b ⟨hx.1, hx.2.trans hb.2⟩).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hb.2⟩
        rw [(hasDerivAt_binPhi b hx').deriv]
        have := hmono hx' hb hx.2.le
        linarith
    have := hanti ⟨ha.1, hab⟩ ⟨hb.1.le, le_rfl⟩ hab
    rwa [binPhi_self] at this
  · have hmon : MonotoneOn (binPhi b) (Set.Icc b 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc b 1) (continuous_binPhi b).continuousOn
      · rw [interior_Icc]
        intro x hx
        exact (hasDerivAt_binPhi b ⟨hb.1.trans hx.1, hx.2⟩).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hb.1.trans hx.1, hx.2⟩
        rw [(hasDerivAt_binPhi b hx').deriv]
        have := hmono hb hx' hx.1.le
        linarith
    have := hmon ⟨le_rfl, hb.2.le⟩ ⟨hab.le, ha.2⟩ hab.le
    rwa [binPhi_self] at this

/-- **Binary Pinsker**: for `b ∈ (0, 1)` and `a ∈ [0, 1]`,
`2 (a − b)² ≤ a·log(a/b) + (1 − a)·log((1 − a)/(1 − b))`.
Source: none: infrastructure (Target 2(a); rigor critique 13 of [[generalization-final]])
Kind: P
Fidelity: exact -/
theorem binary_pinsker {b : ℝ} (hb : b ∈ Set.Ioo (0 : ℝ) 1) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    2 * (a - b) ^ 2 ≤ a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  have h := binPhi_nonneg hb ha
  have e1 : a * Real.log (a / b) = -negMulLog a - a * Real.log b := mul_log_div_eq ha.1 hb.1
  have e2 : (1 - a) * Real.log ((1 - a) / (1 - b))
      = -negMulLog (1 - a) - (1 - a) * Real.log (1 - b) :=
    mul_log_div_eq (by linarith [ha.2]) (by linarith [hb.2])
  rw [e1, e2]
  unfold binPhi at h
  linarith

/-! ### Pinsker's inequality -/

/-- **Pinsker's inequality, finite form**: for distributions `p q ∈ stdSimplex ℝ W` with `p`
absolutely continuous with respect to `q`, `tv p q ≤ √(klFin p q / 2)`. Proof: the set form
of `tv` (`tv_eq_sum_filter`) makes `tv = a − b` with `a = p(A)`, `b = q(A)`,
`A = {q < p}`; grouping (`klFin_ge_grouped`) gives `klFin ≥ KL(a‖b)`; binary Pinsker
(`binary_pinsker`) gives `KL(a‖b) ≥ 2(a − b)²`. The boundary cases `b ∈ {0, 1}` are where
absolute continuity bites: both force `tv = 0`.
Source: [[generalization-final]] S2 l. 61, P2 l. 107 ("Pinsker", used as (b) textbook four
times across the corpus); items 126, 129, 2-078, wf14b-038
Kind: P
Fidelity: exact
Hyps: (a) all — `hp hq` membership in the simplex, `hac` absolute continuity (the hypothesis
without which the statement is false: `pinsker_fails_without_absCont`) -/
theorem pinsker {p q : W → ℝ} (hp : p ∈ stdSimplex ℝ W) (hq : q ∈ stdSimplex ℝ W)
    (hac : AbsCont p q) : tv p q ≤ Real.sqrt (klFin p q / 2) := by
  have htv := tv_eq_sum_filter hp hq
  rw [Finset.sum_sub_distrib] at htv
  have hgrp := klFin_ge_grouped hp hq hac (fun w => q w < p w)
  have hpc : ∑ w ∈ univ.filter (fun w => ¬ q w < p w), p w
      = 1 - ∑ w ∈ univ.filter (fun w => q w < p w), p w := by
    have := Finset.sum_filter_add_sum_filter_not univ (fun w => q w < p w) p
    rw [hp.2] at this
    linarith
  have hqc : ∑ w ∈ univ.filter (fun w => ¬ q w < p w), q w
      = 1 - ∑ w ∈ univ.filter (fun w => q w < p w), q w := by
    have := Finset.sum_filter_add_sum_filter_not univ (fun w => q w < p w) q
    rw [hq.2] at this
    linarith
  rw [hpc, hqc] at hgrp
  set a := ∑ w ∈ univ.filter (fun w => q w < p w), p w with ha_def
  set b := ∑ w ∈ univ.filter (fun w => q w < p w), q w with hb_def
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun w _ => hp.1 w
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun w _ => hq.1 w
  have ha1 : a ≤ 1 := by
    rw [← hp.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun w _ _ => hp.1 w
  have hb1 : b ≤ 1 := by
    rw [← hq.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun w _ _ => hq.1 w
  have hba : b ≤ a := Finset.sum_le_sum fun w hw => by
    simp only [mem_filter] at hw
    exact hw.2.le
  rw [htv]
  by_cases hbz : b = 0
  · -- `q = 0` on `A`, hence `p = 0` on `A` by `hac`, contradicting `q < p` unless `A = ∅`
    have hA : ∀ w ∈ univ.filter (fun w => q w < p w), p w = 0 := by
      intro w hw
      have hq0 : q w = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hq.1 w).1 hbz w hw
      exact hac w hq0
    have haz : a = 0 := Finset.sum_eq_zero hA
    rw [haz, hbz, sub_zero]
    exact Real.sqrt_nonneg _
  by_cases hbo : b = 1
  · -- `q = 0` off `A`, hence `p = 0` off `A`, so `a = 1`
    have hqc0 : ∑ w ∈ univ.filter (fun w => ¬ q w < p w), q w = 0 := by rw [hqc, hbo]; ring
    have hpc0 : ∑ w ∈ univ.filter (fun w => ¬ q w < p w), p w = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      exact hac w ((Finset.sum_eq_zero_iff_of_nonneg fun w _ => hq.1 w).1 hqc0 w hw)
    have hao : a = 1 := by linarith [hpc, hpc0]
    rw [hao, hbo, sub_self]
    exact Real.sqrt_nonneg _
  · have hb : b ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hb0 (Ne.symm hbz), lt_of_le_of_ne hb1 hbo⟩
    have hbin := binary_pinsker hb (⟨ha0, ha1⟩ : a ∈ Set.Icc (0 : ℝ) 1)
    apply Real.le_sqrt_of_sq_le
    linarith

/-- **The encoding test**: without absolute continuity, `klFin` is junk and Pinsker fails.
On `Fin 2` with `p = δ₀`, `q = δ₁`: `tv = 1` while the junk-guarded `klFin = 0`
(`1 · log (1/0) = 1 · log 0 = 0`), so `tv ≤ √(klFin/2)` is false. This is a test that `hac`
in `pinsker` is load-bearing, not a theorem about divergences.
Source: none: infrastructure (Target 2, trap)
Kind: N-
Fidelity: n/a (degenerate on purpose: disjoint point masses) -/
theorem pinsker_fails_without_absCont :
    tv (![1, 0] : Fin 2 → ℝ) ![0, 1] = 1 ∧ klFin (![1, 0] : Fin 2 → ℝ) ![0, 1] = 0 ∧
      ¬ tv (![1, 0] : Fin 2 → ℝ) ![0, 1]
        ≤ Real.sqrt (klFin (![1, 0] : Fin 2 → ℝ) ![0, 1] / 2) := by
  have h1 : tv (![1, 0] : Fin 2 → ℝ) ![0, 1] = 1 := by
    simp [tv, Fin.sum_univ_two]
    norm_num
  have h2 : klFin (![1, 0] : Fin 2 → ℝ) ![0, 1] = 0 := by
    simp [klFin, Fin.sum_univ_two]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  norm_num

/-! ### `klFin = 0 ↔ p = q`, via `InformationTheory.klFun` -/

/-- `klFin p q = ∑ w, q w · klFun (p w / q w)` for distributions under absolute continuity
(the `klFun` form makes every summand nonnegative).
Source: none: infrastructure (Target 2)
Kind: L
Fidelity: n/a -/
theorem klFin_eq_sum_klFun {p q : W → ℝ} (hp : p ∈ stdSimplex ℝ W) (hq : q ∈ stdSimplex ℝ W)
    (hac : AbsCont p q) : klFin p q = ∑ w, q w * InformationTheory.klFun (p w / q w) := by
  have hterm : ∀ w, q w * InformationTheory.klFun (p w / q w) = p w * Real.log (p w / q w) + (q w - p w) := by
    intro w
    rcases (hq.1 w).lt_or_eq with hqw | hqw
    · unfold InformationTheory.klFun
      field_simp
      ring
    · rw [← hqw, hac w hqw.symm]
      simp
  unfold klFin
  rw [Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hp.2, hq.2]
  ring

/-- **`klFin p q = 0 ↔ p = q`** for distributions under absolute continuity.
Source: none: infrastructure (Target 2, "Also (kind L)")
Kind: P
Fidelity: exact -/
theorem klFin_eq_zero_iff {p q : W → ℝ} (hp : p ∈ stdSimplex ℝ W) (hq : q ∈ stdSimplex ℝ W)
    (hac : AbsCont p q) : klFin p q = 0 ↔ p = q := by
  constructor
  · intro h
    rw [klFin_eq_sum_klFun hp hq hac] at h
    have hnn : ∀ w ∈ (univ : Finset W), 0 ≤ q w * InformationTheory.klFun (p w / q w) := fun w _ =>
      mul_nonneg (hq.1 w) (InformationTheory.klFun_nonneg (div_nonneg (hp.1 w) (hq.1 w)))
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
    funext w
    have hw := hzero w (mem_univ w)
    rcases (hq.1 w).lt_or_eq with hqw | hqw
    · have : InformationTheory.klFun (p w / q w) = 0 := by
        rcases mul_eq_zero.1 hw with h' | h'
        · exact absurd h' hqw.ne'
        · exact h'
      have h1 := (InformationTheory.klFun_eq_zero_iff (div_nonneg (hp.1 w) (hq.1 w))).1 this
      field_simp at h1
      linarith
    · rw [← hqw, hac w hqw.symm]
  · rintro rfl
    simp [klFin]

/-! ### Jensen for the square root -/

/-- **Jensen for `√`**: for a probability vector `P` and `x ≥ 0`,
`∑ s, P s · √(x s) ≤ √(∑ s, P s · x s)` (concavity of `√`; used by Targets 3, 6, 9).
Source: none: infrastructure (Target 2, "Also (kind L)")
Kind: P
Fidelity: exact -/
theorem sum_mul_sqrt_le {S : Type} [Fintype S] {P x : S → ℝ} (hP : P ∈ stdSimplex ℝ S)
    (hx : ∀ s, 0 ≤ x s) : ∑ s, P s * Real.sqrt (x s) ≤ Real.sqrt (∑ s, P s * x s) := by
  have := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum (t := univ) (w := P) (p := x)
    (fun i _ => hP.1 i) hP.2 (fun i _ => hx i)
  simpa [smul_eq_mul] using this

end

end Cleanroom.Info.InfoVoiLatents
