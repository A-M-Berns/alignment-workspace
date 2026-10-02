import Cleanroom.Udt.UdtSupercondition.Mass
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# The "geometric update" is Bayesian conditioning when the divergence is KL (T18)

bli-paper-2-023: the chat's "Phase 3.2 geometric update" `argmin_Q D(Q‖P)` subject to
`Q(x) = 1` is `P(· | x)` when `D` is the Kullback–Leibler divergence, and no other `D` is named.
Finite hand-rolled version (`klFin`, sums over a `Fintype`, real-valued, with the convention
`0 · log(0/p) = 0`; stated only under absolute continuity `Q ≪ P`, since without it the finite
formula is junk — Mathlib's `klDiv` returns `⊤` there):

* `klFin_nonneg`, `klFin_eq_zero_iff` — Gibbs' inequality and its converse, from
  `Real.log_le_sub_one_of_pos` / `Real.log_lt_sub_one_of_pos`;
* `klFin_condOn_chain` — for `Q` supported in `S`, `KL(Q‖P) = KL(Q‖P(·|S)) − log P(S)`;
* `geometricUpdate_ge`, `geometricUpdate_eq_iff` — the I-projection: `KL(Q‖P) ≥ −log P(S)` with
  equality iff `Q = P(· | S)`.

The measure-level form over Mathlib's `InformationTheory.klDiv` is stated as
`geometricUpdate_klDiv_open` and left OPEN (listed in `udt-supercondition-open.txt`): the
obstacle is relating `llr Q.toMeasure P.toMeasure` pointwise to `log (Q x / P x)` on a discrete
carrier (Mathlib characterizes `rnDeriv` only up to a.e. equality through the Lebesgue
decomposition), which the finite version sidesteps.

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

variable {Ω : Type}

/-- Absolute continuity of PMFs on the same carrier: `P x = 0 → Q x = 0`.
Source: [[superconditioning-mismatched-ontologies]] §0.9
Kind: D
Fidelity: exact
Hyps: n/a -/
def AbsCont (Q P : PMF Ω) : Prop := ∀ x, P x = 0 → Q x = 0

/-- The termwise hypotheses, from `AbsCont`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem AbsCont.toReal {Q P : PMF Ω} (h : AbsCont Q P) (x : Ω) :
    (P x).toReal = 0 → (Q x).toReal = 0 := by
  intro hx
  rw [ENNReal.toReal_eq_zero_iff] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (h x hx)
  · exact absurd hx (PMF.apply_ne_top _ _)

variable [Fintype Ω]

/-- The finite Kullback–Leibler divergence `∑ Q x · log (Q x / P x)` (real-valued, convention
`0 · log 0 = 0`; meaningful only under `AbsCont Q P`).
Source: bli-paper-2-023 (finite case: "`KL(Q‖P) = KL(Q‖P(·|x)) − log P(x)`")
Kind: D
Fidelity: variant: finite carrier, real-valued, `AbsCont` assumed at every use
Hyps: n/a -/
noncomputable def klFin (Q P : PMF Ω) : ℝ :=
  ∑ x, (Q x).toReal * Real.log ((Q x).toReal / (P x).toReal)

/-- The real masses of a PMF on a finite carrier sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_toReal_eq_one (P : PMF Ω) : ∑ x, (P x).toReal = 1 := by
  have := P.tsum_coe
  rw [tsum_fintype] at this
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top P x), this, ENNReal.toReal_one]

/-- Termwise Gibbs: `q − p ≤ q · log (q/p)` for `q, p ≥ 0` with `p = 0 → q = 0`.
Source: none: infrastructure (from `Real.log_le_sub_one_of_pos`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sub_le_mul_log_div {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) (hac : p = 0 → q = 0) :
    q - p ≤ q * Real.log (q / p) := by
  rcases hq.eq_or_lt with hq0 | hq0
  · rw [← hq0, zero_mul, zero_sub]
    linarith
  · have hp0 : 0 < p := lt_of_le_of_ne hp fun h => hq0.ne' (hac h.symm)
    have h1 := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
    rw [Real.log_div hp0.ne' hq0.ne'] at h1
    rw [Real.log_div hq0.ne' hp0.ne']
    calc q - p = q * (1 - p / q) := by rw [mul_sub, mul_one, mul_div_cancel₀ _ hq0.ne']
      _ ≤ q * (Real.log q - Real.log p) := mul_le_mul_of_nonneg_left (by linarith) hq0.le

/-- Termwise Gibbs, strict: `q − p < q · log (q/p)` when moreover `q ≠ p`.
Source: none: infrastructure (from `Real.log_lt_sub_one_of_pos`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sub_lt_mul_log_div {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) (hac : p = 0 → q = 0)
    (hne : q ≠ p) : q - p < q * Real.log (q / p) := by
  rcases hq.eq_or_lt with hq0 | hq0
  · rw [← hq0, zero_mul, zero_sub]
    have : p ≠ 0 := fun h => hne (hq0.symm.trans h.symm)
    linarith [lt_of_le_of_ne hp (Ne.symm this)]
  · have hp0 : 0 < p := lt_of_le_of_ne hp fun h => hq0.ne' (hac h.symm)
    have hpq : p / q ≠ 1 := fun h => hne ((div_eq_one_iff_eq hq0.ne').1 h).symm
    have h1 := Real.log_lt_sub_one_of_pos (div_pos hp0 hq0) hpq
    rw [Real.log_div hp0.ne' hq0.ne'] at h1
    rw [Real.log_div hq0.ne' hp0.ne']
    calc q - p = q * (1 - p / q) := by rw [mul_sub, mul_one, mul_div_cancel₀ _ hq0.ne']
      _ < q * (Real.log q - Real.log p) := mul_lt_mul_of_pos_left (by linarith) hq0

/-- **Gibbs' inequality (finite):** `0 ≤ KL(Q‖P)` under `Q ≪ P`.
Source: bli-paper-2-023 (Gibbs)
Kind: P
Fidelity: variant: finite carrier
Hyps: (a) all -/
theorem klFin_nonneg {Q P : PMF Ω} (h : AbsCont Q P) : 0 ≤ klFin Q P := by
  have h1 : ∑ x, ((Q x).toReal - (P x).toReal) ≤ klFin Q P :=
    Finset.sum_le_sum fun x _ =>
      sub_le_mul_log_div ENNReal.toReal_nonneg ENNReal.toReal_nonneg (h.toReal x)
  rwa [Finset.sum_sub_distrib, sum_toReal_eq_one, sum_toReal_eq_one, sub_self] at h1

/-- Two PMFs with equal real masses are equal (finite carrier).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem PMF.ext_toReal {Q P : PMF Ω} (h : ∀ x, (Q x).toReal = (P x).toReal) : Q = P :=
  PMF.ext fun x =>
    (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1 (h x)

/-- **Converse Gibbs (finite):** under `Q ≪ P`, `KL(Q‖P) = 0` iff `Q = P`.
Source: bli-paper-2-023 (Gibbs)
Kind: P
Fidelity: variant: finite carrier
Hyps: (a) all -/
theorem klFin_eq_zero_iff {Q P : PMF Ω} (h : AbsCont Q P) : klFin Q P = 0 ↔ Q = P := by
  constructor
  · intro h0
    by_contra hne
    obtain ⟨x, hx⟩ : ∃ x, (Q x).toReal ≠ (P x).toReal := by
      by_contra hall
      push_neg at hall
      exact hne (PMF.ext_toReal hall)
    have hlt : ∑ y, ((Q y).toReal - (P y).toReal) < klFin Q P :=
      Finset.sum_lt_sum
        (fun y _ => sub_le_mul_log_div ENNReal.toReal_nonneg ENNReal.toReal_nonneg (h.toReal y))
        ⟨x, Finset.mem_univ x,
          sub_lt_mul_log_div ENNReal.toReal_nonneg ENNReal.toReal_nonneg (h.toReal x) hx⟩
    rw [Finset.sum_sub_distrib, sum_toReal_eq_one, sum_toReal_eq_one, sub_self, h0] at hlt
    exact lt_irrefl _ hlt
  · rintro rfl
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : (Q x).toReal = 0
    · rw [hx, zero_mul]
    · rw [div_self hx, Real.log_one, mul_zero]

/-- The real mass of the conditioned measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condOn_toReal (P : PMF Ω) (S : Set Ω) (h : 0 < mass P S) (x : Ω) :
    (condOn P S h x).toReal = (S.indicator P x).toReal / (mass P S).toReal := by
  rw [condOn_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv]

/-- **The chain rule for conditioning (finite):** for `Q ≪ P` supported in `S`,
`KL(Q‖P) = KL(Q‖P(·|S)) − log P(S)`.
Source: bli-paper-2-023 ("`KL(Q‖P) = KL(Q‖P(·|x)) − log P(x)` for `Q` supported on `x`")
Kind: P
Fidelity: variant: finite carrier, any positive event `S` in place of a point
Hyps: (a) all -/
theorem klFin_condOn_chain {Q P : PMF Ω} (h : AbsCont Q P) (S : Set Ω) (hS : 0 < mass P S)
    (hQS : ∀ x, x ∉ S → Q x = 0) :
    klFin Q P = klFin Q (condOn P S hS) - Real.log (mass P S).toReal := by
  have hm : 0 < (mass P S).toReal := ENNReal.toReal_pos hS.ne' (mass_ne_top P S)
  have key : ∀ x, (Q x).toReal * Real.log ((Q x).toReal / (condOn P S hS x).toReal) =
      (Q x).toReal * Real.log ((Q x).toReal / (P x).toReal) +
        (Q x).toReal * Real.log (mass P S).toReal := fun x => by
    by_cases hq : (Q x).toReal = 0
    · rw [hq, zero_mul, zero_mul, zero_mul, add_zero]
    · have hxS : x ∈ S := by
        by_contra hx
        exact hq (by rw [hQS x hx, ENNReal.toReal_zero])
      have hp : (P x).toReal ≠ 0 := fun hp => hq (h.toReal x hp)
      have hp0 : 0 < (P x).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp)
      have hq0 : 0 < (Q x).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hq)
      rw [condOn_toReal, indicator_of_mem hxS, ← mul_add, ← Real.log_mul (div_pos hq0 hp0).ne' hm.ne']
      congr 2
      field_simp
  have hsum : ∑ x, (Q x).toReal * Real.log (mass P S).toReal = Real.log (mass P S).toReal := by
    rw [← Finset.sum_mul, sum_toReal_eq_one, one_mul]
  unfold klFin
  rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib, hsum]
  ring

/-- `Q ≪ P(·|S)` follows from `Q ≪ P` and support in `S`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem AbsCont.condOn {Q P : PMF Ω} (h : AbsCont Q P) (S : Set Ω) (hS : 0 < mass P S)
    (hQS : ∀ x, x ∉ S → Q x = 0) : AbsCont Q (condOn P S hS) := fun x hx => by
  rw [condOn_apply, mul_eq_zero] at hx
  rcases hx with hx | hx
  · by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS] at hx; exact h x hx
    · exact hQS x hxS
  · exact absurd hx (ENNReal.inv_ne_zero.2 (mass_ne_top P S))

/-- **The geometric update is Bayesian conditioning, lower bound (finite):** for `Q ≪ P` supported
in `S`, `KL(Q‖P) ≥ −log P(S)`.
Source: bli-paper-2-023 | mandate T18
Kind: P
Fidelity: variant: finite carrier; the constraint `Q(x) = 1` generalized to support in `S`
Hyps: (a) all -/
theorem geometricUpdate_ge {Q P : PMF Ω} (h : AbsCont Q P) (S : Set Ω) (hS : 0 < mass P S)
    (hQS : ∀ x, x ∉ S → Q x = 0) : -Real.log (mass P S).toReal ≤ klFin Q P := by
  rw [klFin_condOn_chain h S hS hQS]
  linarith [klFin_nonneg (h.condOn S hS hQS)]

/-- **The geometric update is Bayesian conditioning, equality case (finite):** the bound is
attained iff `Q = P(· | S)` — the I-projection onto `{Q | Q(S) = 1}` is conditioning, so the
"geometric update" of bli-paper-2-023 adds nothing for `D = KL`.
Source: bli-paper-2-023 | mandate T18
Kind: P
Fidelity: variant: finite carrier
Hyps: (a) all -/
theorem geometricUpdate_eq_iff {Q P : PMF Ω} (h : AbsCont Q P) (S : Set Ω) (hS : 0 < mass P S)
    (hQS : ∀ x, x ∉ S → Q x = 0) :
    klFin Q P = -Real.log (mass P S).toReal ↔ Q = condOn P S hS := by
  rw [klFin_condOn_chain h S hS hQS, sub_eq_neg_self, klFin_eq_zero_iff (h.condOn S hS hQS)]

/-- **OPEN — the measure-level form over Mathlib's `InformationTheory.klDiv`:** for `P` on a
finite discrete carrier and `Q` with `Q(S) = 1`, `klDiv Q.toMeasure P.toMeasure ≥
ofReal (−log P(S))`, with equality iff `Q = P(·|S)`. Obstacle: identifying `llr Q P` with
`x ↦ log (Q x / P x)` pointwise on a discrete carrier through Mathlib's `rnDeriv` (a.e.
characterization via the Lebesgue decomposition); the finite form `geometricUpdate_eq_iff` is
proved and is the content.
Source: bli-paper-2-023 | mandate T18
Kind: OPEN
Fidelity: variant: finite carrier (`[Fintype Ω]`, the file-level variable); the mandate's
measure-level target was countable `Ω`
Hyps: n/a -/
theorem geometricUpdate_klDiv_open (P Q : PMF Ω) (S : Set Ω) (hS : 0 < mass P S)
    (hQS : mass Q S = 1) :
    letI : MeasurableSpace Ω := ⊤
    ENNReal.ofReal (-Real.log (mass P S).toReal) ≤ InformationTheory.klDiv Q.toMeasure P.toMeasure ∧
      (InformationTheory.klDiv Q.toMeasure P.toMeasure = ENNReal.ofReal (-Real.log (mass P S).toReal) ↔
        Q = condOn P S hS) := by
  sorry

end Cleanroom.Udt.UdtSupercondition
