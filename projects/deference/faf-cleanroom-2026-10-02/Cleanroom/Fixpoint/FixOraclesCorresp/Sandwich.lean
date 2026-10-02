import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.Sandwich`: the eval sandwich (finite-state form)

Target 16 (fixpoint-lit-2-003/2-009). FTC App. B classifies a machine state by its first step —
halt with `0`, halt with `1`, halt with another output, or a mixture over successor states (coin flips
and oracle calls are both mixtures once the oracle's answers are fixed) — and asserts, "by
induction", that any `eval` satisfying the one-step equations is sandwiched between the probability
of halting with `1` within `T` steps and one minus the probability of halting with `0` within `T` steps.

Finite-state form: `Step S` with `step : S → Step S`, `reach1 T s` / `reach0 T s` by recursion on `T`,
`IsEval step e` the one-step equations (with `e` valued in `[0,1]`). **Headline** `sandwich`:
`reach1 T s ≤ e s ≤ 1 − reach0 T s` for all `T`. Corollary (§7's strengthened principle coincides with
the original for a.s.-halting states): if `reach1 T s + reach0 T s → 1` then `e s = lim reach1 T s`
(`eval_eq_limit_reach1`, from the abstract squeeze `tendsto_of_sandwich`). N+ witness: the two-state
loop (`loopStep`) whose `e 0` is forced to `1` while `reach1 (T+1) 0 = 1 − (1/2)^T` (one step is spent
on the halt, so the mandate's `1 − 2^{−T}` is indexed by `T + 1` here).
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set Filter Topology Finset

/-- **A machine's first step** on a finite state space `S`: halt with `0`, with `1`, with another
output, or move to a successor drawn from a probability vector `w`.
Source: FTC 2015 App. B ("any machine `M` can be classified as performing one of the following
operations as its first step … (i)–(iv)"); [[fixpoint-lit-2-inventory]] 003
Kind: D
Fidelity: variant: finite-state; a deterministic step is the mixture `w = δ_{s'}`, and a coin flip
and an oracle call are both mixtures once the answers are fixed
Hyps: n/a -/
inductive Step (S : Type*) [Fintype S]
  | halt0
  | halt1
  | haltOther
  | mix (w : S → ℝ) (nonneg : ∀ s, 0 ≤ w s) (sum_one : ∑ s, w s = 1)

variable {S : Type*} [Fintype S]

/-- The probability of halting with `1` within `T` steps from `s`.
Source: FTC 2015 App. B ("the probability that `M^{O'}()` returns 1 after at most `T` timesteps")
Kind: D
Fidelity: variant: finite-state
Hyps: n/a -/
noncomputable def reach1 (step : S → Step S) : ℕ → S → ℝ
  | 0, _ => 0
  | T + 1, s =>
    match step s with
    | .halt1 => 1
    | .halt0 => 0
    | .haltOther => 0
    | .mix w _ _ => ∑ s', w s' * reach1 step T s'

/-- The probability of halting with `0` within `T` steps from `s`.
Source: FTC 2015 App. B ("the probability that it returns something other than 0 within this time
bound" is `1 −` this)
Kind: D
Fidelity: variant: finite-state
Hyps: n/a -/
noncomputable def reach0 (step : S → Step S) : ℕ → S → ℝ
  | 0, _ => 0
  | T + 1, s =>
    match step s with
    | .halt1 => 0
    | .halt0 => 1
    | .haltOther => 0
    | .mix w _ _ => ∑ s', w s' * reach0 step T s'

/-- The one-step condition on the value `v` of `e` at a state whose step is `st`.
Source: FTC 2015 App. B (the four cases for `eval'(M)`)
Kind: D
Fidelity: variant: finite-state
Hyps: n/a -/
def Step.evalOk (st : Step S) (e : S → ℝ) (v : ℝ) : Prop :=
  match st with
  | .halt0 => v = 0
  | .halt1 => v = 1
  | .haltOther => True
  | .mix w _ _ => v = ∑ s', w s' * e s'

/-- **An evaluation function**: `e : S → ℝ` valued in `[0, 1]` satisfying the one-step equations at
every state (a fixed point of App. B's `eval ↦ eval'`).
Source: FTC 2015 App. B; [[fixpoint-lit-2-inventory]] 003
Kind: D
Fidelity: variant: finite-state
Hyps: n/a -/
def IsEval (step : S → Step S) (e : S → ℝ) : Prop :=
  ∀ s, e s ∈ Icc (0 : ℝ) 1 ∧ (step s).evalOk e (e s)

/-- **Target 16, the eval sandwich**: for every `T` and `s`, `reach1 T s ≤ e s ≤ 1 − reach0 T s`.
Induction on `T`; at a mixture, `∑ w s' * reach1 T s' ≤ ∑ w s' * e s' = e s ≤ ∑ w s' * (1 − reach0 T s')
= 1 − ∑ w s' * reach0 T s'`.
Source: FTC 2015 App. B ("it can be shown by induction that for every `T ∈ ℕ` and every `M`, `eval(M)`
is `≥` the probability that `M` returns 1 after at most `T` timesteps, and `≤` the probability that it
returns something other than 0 within this time bound"); [[fixpoint-lit-2-inventory]] 003
Kind: P
Fidelity: variant: finite-state
Hyps: (a) none -/
theorem sandwich {step : S → Step S} {e : S → ℝ} (he : IsEval step e) (T : ℕ) (s : S) :
    reach1 step T s ≤ e s ∧ e s ≤ 1 - reach0 step T s := by
  induction T generalizing s with
  | zero =>
    simp only [reach1, reach0, sub_zero]
    exact (he s).1
  | succ T ih =>
    obtain ⟨hI, hok⟩ := he s
    simp only [reach1, reach0]
    cases h : step s with
    | halt0 =>
      rw [h] at hok; simp only [Step.evalOk] at hok
      simp only [hok]; norm_num
    | halt1 =>
      rw [h] at hok; simp only [Step.evalOk] at hok
      simp only [hok]; norm_num
    | haltOther =>
      simp only [sub_zero]; exact hI
    | mix w hw hsum =>
      rw [h] at hok; simp only [Step.evalOk] at hok
      rw [hok]
      constructor
      · exact Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (ih s').1 (hw s')
      · calc ∑ s', w s' * e s' ≤ ∑ s', w s' * (1 - reach0 step T s') :=
              Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (ih s').2 (hw s')
          _ = 1 - ∑ s', w s' * reach0 step T s' := by
              simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum]

/-- **The abstract squeeze**: if `P1 T ≤ e ≤ 1 − P0 T` for all `T` and `P1 T + P0 T → 1`, then
`P1 T → e`.
Source: FTC 2015 §7 ("identical to the former principle if `M^O()` is guaranteed to halt");
[[fixpoint-lit-2-inventory]] 009 (i)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_of_sandwich {P0 P1 : ℕ → ℝ} {e : ℝ} (h : ∀ T, P1 T ≤ e ∧ e ≤ 1 - P0 T)
    (hlim : Tendsto (fun T => P1 T + P0 T) atTop (𝓝 1)) : Tendsto P1 atTop (𝓝 e) := by
  have hg : Tendsto (fun T => e - (1 - (P1 T + P0 T))) atTop (𝓝 e) := by
    have := tendsto_const_nhds (x := e) |>.sub (tendsto_const_nhds (x := (1 : ℝ)) |>.sub hlim)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg tendsto_const_nhds ?_ ?_
  · intro T; have := (h T).2; simp only; linarith
  · intro T; exact (h T).1

/-- **Corollary (2-009 (i))**: at an almost-surely-halting state (`reach1 T s + reach0 T s → 1`), the
evaluation is the limit of `reach1 T s` — so §7's strengthened reflection principle coincides with the
original there.
Source: FTC 2015 §7; [[fixpoint-lit-2-inventory]] 009 (i)
Kind: C
Fidelity: variant: finite-state
Hyps: (a) none -/
theorem eval_eq_limit_reach1 {step : S → Step S} {e : S → ℝ} (he : IsEval step e) (s : S)
    (hlim : Tendsto (fun T => reach1 step T s + reach0 step T s) atTop (𝓝 1)) :
    Tendsto (fun T => reach1 step T s) atTop (𝓝 (e s)) :=
  tendsto_of_sandwich (fun T => sandwich he T s) hlim

/-! ### N+ witness: the two-state loop -/

/-- The two-state loop: state `0` moves to `0` or `1` with probability `1/2` each; state `1` halts with
`1`.
Source: mandate target 16 (N+ witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def loopStep : Fin 2 → Step (Fin 2) :=
  ![Step.mix ![1 / 2, 1 / 2] (fun s => by fin_cases s <;> norm_num) (by simp [Fin.sum_univ_two]; norm_num),
    Step.halt1]

/-- `loopStep 0` is the fair mixture.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem loopStep_zero : loopStep 0 = Step.mix ![1 / 2, 1 / 2] (fun s => by fin_cases s <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) := rfl

/-- `loopStep 1` halts with `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem loopStep_one : loopStep 1 = Step.halt1 := rfl

/-- On the loop, any evaluation function is forced to `1` at both states (`e 1 = 1` at the halt;
`e 0 = ½ e 0 + ½ e 1` forces `e 0 = 1`).
Source: mandate target 16 ("whose `ev` is forced to `1`")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem isEval_loopStep_iff (e : Fin 2 → ℝ) : IsEval loopStep e ↔ e 0 = 1 ∧ e 1 = 1 := by
  constructor
  · intro he
    have h1 := (he 1).2
    have h0 := (he 0).2
    simp only [loopStep, Matrix.cons_val_one, Matrix.cons_val_zero, Step.evalOk] at h1
    simp only [loopStep, Matrix.cons_val_zero, Step.evalOk, Fin.sum_univ_two,
      Matrix.cons_val_one] at h0
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    rw [IsEval, Fin.forall_fin_two]
    constructor
    · refine ⟨by rw [h0]; exact ⟨zero_le_one, le_rfl⟩, ?_⟩
      simp only [loopStep, Matrix.cons_val_zero, Step.evalOk, Fin.sum_univ_two,
        Matrix.cons_val_one, h0, h1]
      norm_num
    · refine ⟨by rw [h1]; exact ⟨zero_le_one, le_rfl⟩, ?_⟩
      simp only [loopStep, Matrix.cons_val_one, Matrix.cons_val_zero, Step.evalOk, h1]

/-- One step of `reach1` at state `0` of the loop.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem reach1_loopStep_succ_zero (T : ℕ) :
    reach1 loopStep (T + 1) 0 = 1 / 2 * reach1 loopStep T 0 + 1 / 2 * reach1 loopStep T 1 := by
  simp only [reach1, loopStep_zero, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- One step of `reach1` at state `1` of the loop.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem reach1_loopStep_succ_one (T : ℕ) : reach1 loopStep (T + 1) 1 = 1 := by
  simp [reach1, loopStep_one]

/-- One step of `reach0` at state `0` of the loop.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem reach0_loopStep_succ_zero (T : ℕ) :
    reach0 loopStep (T + 1) 0 = 1 / 2 * reach0 loopStep T 0 + 1 / 2 * reach0 loopStep T 1 := by
  simp only [reach0, loopStep_zero, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- One step of `reach0` at state `1` of the loop.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem reach0_loopStep_succ_one (T : ℕ) : reach0 loopStep (T + 1) 1 = 0 := by
  simp [reach0, loopStep_one]

/-- On the loop, `reach1 (T + 1) 0 = 1 − (1/2)^T` (and `reach1 (T + 1) 1 = 1`).
Source: mandate target 16 ("`reach1 T = 1 − 2^{−T}`"; here indexed by `T + 1` because the halt takes a
step)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem reach1_loopStep (T : ℕ) :
    reach1 loopStep (T + 1) 1 = 1 ∧ reach1 loopStep (T + 1) 0 = 1 - (1 / 2 : ℝ) ^ T := by
  induction T with
  | zero =>
    constructor
    · exact reach1_loopStep_succ_one 0
    · rw [reach1_loopStep_succ_zero]; simp [reach1]
  | succ T ih =>
    constructor
    · exact reach1_loopStep_succ_one _
    · rw [reach1_loopStep_succ_zero, ih.1, ih.2]
      ring

/-- On the loop, `reach1 T 0 + reach0 T 0 → 1`, so the corollary applies and the forced value `e 0 = 1`
is indeed `lim reach1 T 0`.
Source: mandate target 16
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem loopStep_halts : Tendsto (fun T => reach1 loopStep T 0 + reach0 loopStep T 0) atTop (𝓝 1) := by
  have hr0 : ∀ T, reach0 loopStep T 0 = 0 ∧ reach0 loopStep T 1 = 0 := by
    intro T
    induction T with
    | zero => simp [reach0]
    | succ T ih =>
      constructor
      · rw [reach0_loopStep_succ_zero, ih.1, ih.2]; ring
      · exact reach0_loopStep_succ_one _
  have h : ∀ T, reach1 loopStep (T + 1) 0 + reach0 loopStep (T + 1) 0 = 1 - (1 / 2 : ℝ) ^ T := by
    intro T; rw [(reach1_loopStep T).2, (hr0 (T + 1)).1, add_zero]
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  simp only [h]
  have : Tendsto (fun T : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ T) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  simpa using this

end Cleanroom.Fixpoint.FixOraclesCorresp
