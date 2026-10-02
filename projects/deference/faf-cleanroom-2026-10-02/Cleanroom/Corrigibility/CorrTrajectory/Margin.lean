import Cleanroom.Corrigibility.CorrTrajectory.ProductLaw
import Cleanroom.Corrigibility.CorrTrajectory.Corruption
import Cleanroom.Found.CorrThreeStep.TwoState
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.IntervalCases

/-!
# `corr-trajectory` — `Margin`: Statement 5, the compliance margin, non-propagation, the crossing (T4)

* (a) `I₁ ↔ (1 − ε) c α ≤ ε h β` is the parent's `twoState_deltaMinus_nonneg_iff` with a time index:
  on the two-round two-state process `twoRounds`, `objCompliance 0` is the odds inequality at `ε₁`
  (`objCompliance_zero_iff`) and `objCompliance 1` on a positive-mass atom is the odds inequality
  at `ε₂` (`objCompliance_one_iff`); `oddsIneq_iff_deltaMinus` ties it to the parent;
* (b) **the source's C10 confirmed** (`c10`; audit r1 B2): Statement 5(a) *asserts* that "(i) at
  `t = 0` and `ε_t h_t` non-decreasing" does **not** propagate (i), and checks it with C10 — equality
  at round `0`, failure at round `1` with `ε h` unchanged; the mandate's "refuted" label for T4(b) was
  a mandate error, not a source error. The `(1 − ε)`-free form propagates (`sufficient_form_propagates`),
  and at C10's round `0` that form itself fails — so it is strictly stronger than (i);
* (c) C3: at `ε_t = 2^{−t}`, `h = 20`, `c = 1`, `α = 1/20`, `β = 1`, (i) holds iff `2^t ≤ 401`, i.e.
  `t ≤ 8`; the least failing index `9` (`c3_least_failing`);
* (d) the compliance margin `M = log(ε h β) − log((1 − ε) c α)`, `I₁ ↔ 0 ≤ M` under positivity; F3's
  drift `M_t = t log 2 + log 20`, strictly increasing — "a drift statement exists once a law is given";
* (e) `I₁ ↔ Î₁` under the five agreements, and three do not suffice (`three_agreements_insufficient`);
* (f) E1 (2-007) on the two-round process: `I₁` at round `1` (`ε₁ = 1/10`) and `¬I₁` at round `2`
  (`ε₂ = 1/50`) — "a maintained hypothesis, not an invariant"; the numbers are `corr-joint-process`'s
  `Battery`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect
open Corruption (oddsIneq)

namespace Margin

/-- **(a) The odds inequality is the parent's `Δ₋ ≥ 0`** on `twoState`.
Source: [[corr-wf14-inventory]] 075 / invariant-final.md Statement 5; corr-three-step F3
Kind: L
Fidelity: exact -/
theorem oddsIneq_iff_deltaMinus (ε α β c h : ℝ) (hε hα hβ) :
    oddsIneq α β h c ε ↔ 0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus_nonneg_iff]
  unfold oddsIneq
  constructor <;> intro H <;> nlinarith

/-! ### The two-state round cell and the two-round process -/

/-- The two-state round cell on `(W, Pr)`: `P(W) = ε`, `P(Pr ∣ W) = β`, `P(Pr ∣ ¬W) = α`.
Source: corr-three-step `twoState` as one round of S2
Kind: D
Fidelity: exact -/
noncomputable def cell (ε α β : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) : Distr (World × Bool) where
  mass ω := (twoPoint ε hε).mass ω.1 * (if ω.2 then twoPress α β ω.1 else 1 - twoPress α β ω.1)
  nonneg ω := by
    refine mul_nonneg ((twoPoint ε hε).nonneg _) ?_
    rcases ω with ⟨w, p⟩
    cases w <;> cases p <;> simp [twoPress] <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
  sum_eq_one := by
    simp [Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq, twoPress]; ring

/-- `E_cell[g]` as the four-point sum. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_cell (ε α β : ℝ) (hε hα hβ) (g : World × Bool → ℝ) :
    expect (cell ε α β hε hα hβ) g =
      (1 - ε) * α * g (.right, true) + (1 - ε) * (1 - α) * g (.right, false) +
        ε * β * g (.wrong, true) + ε * (1 - β) * g (.wrong, false) := by
  simp [expect, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq, cell, twoPress]; ring

/-- The filtration of two rounds: round-`0` outcome at time `0`, everything from time `1`.
Source: invariant-final.md S1. Kind: D. Fidelity: exact -/
def postAtoms : Atoms ((World × Bool) × (World × Bool)) where
  fib t ω := if t = 0 then univ.filter (fun ω' => ω'.1 = ω.1) else {ω}
  mem_fib t ω := by rcases t with _ | t <;> simp
  fib_eq_of_mem t ω ω' h := by
    rcases t with _ | t
    · simp at h; simp [h]
    · simp at h; rw [h]
  fib_succ_subset t ω := by
    rcases t with _ | t
    · intro ω' h; simp at h; simp [h]
    · simp

/-- The pre-press filtration: nothing at `0`, the round-`0` outcome at `1`, everything from `2`.
Source: invariant-final.md S1. Kind: D. Fidelity: exact -/
def preAtoms : Atoms ((World × Bool) × (World × Bool)) where
  fib t ω := if t = 0 then univ else if t = 1 then univ.filter (fun ω' => ω'.1 = ω.1) else {ω}
  mem_fib t ω := by rcases t with _ | _ | t <;> simp
  fib_eq_of_mem t ω ω' h := by
    rcases t with _ | _ | t
    · rfl
    · simp at h; simp [h]
    · simp at h; rw [h]
  fib_succ_subset t ω := by
    rcases t with _ | _ | t
    · simp
    · intro ω' h; simp at h; simp [h]
    · simp

/-- **The two-round two-state process** with rates `ε₁, ε₂`, fixed `(α, β, c, h)`, independent rounds,
compliance always.
Source: [[corr-wf14-inventory]] 2-007 / joint.md §P.11 (E1) as a trajectory of T1
Kind: D
Fidelity: exact -/
noncomputable def twoRounds (ε₁ ε₂ α β c h : ℝ) (hε₁ : ε₁ ∈ Set.Icc (0 : ℝ) 1) (hε₂ : ε₂ ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hc : 0 ≤ c) (hh : 0 ≤ h) :
    ShutdownProc ((World × Bool) × (World × Bool)) Unit where
  μ := prod2 (cell ε₁ α β hε₁ hα hβ) (cell ε₂ α β hε₂ hα hβ)
  F := postAtoms
  Fpre := preAtoms
  post_subset_pre t ω := by
    rcases t with _ | _ | t
    · simp [postAtoms, preAtoms]
    · simp [postAtoms, preAtoms]
    · simp [postAtoms, preAtoms]
  pre_succ_subset_post t ω := by
    rcases t with _ | _ | t
    · simp [postAtoms, preAtoms]
    · simp [postAtoms, preAtoms]
    · simp [postAtoms, preAtoms]
  wrong t ω := if t = 0 then decide (ω.1.1 = .wrong) else if t = 1 then decide (ω.2.1 = .wrong) else false
  mag _ _ := ()
  hOf _ := h
  cOf _ := c
  hOf_nonneg _ := hh
  cOf_nonneg _ := hc
  pressed t ω := if t = 0 then ω.1.2 else if t = 1 then ω.2.2 else false
  pressed_meas t ω ω' hω' := by
    rcases t with _ | _ | t
    · simp [postAtoms] at hω'
      simp [indB, hω']
    · simp [postAtoms] at hω'
      simp [hω']
    · simp [postAtoms] at hω'
      simp [hω']
  kappa _ _ := true
  kappa_meas _ _ _ _ := rfl
  irr _ _ := false
  cat _ _ := false
  cat_absorbing _ _ _ h := h

variable (ε₁ ε₂ α β c h : ℝ) (hε₁ : ε₁ ∈ Set.Icc (0 : ℝ) 1) (hε₂ : ε₂ ∈ Set.Icc (0 : ℝ) 1)
  (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hc : 0 ≤ c) (hh : 0 ≤ h)

/-- The press-weighted value `Pr · X` on a cell point. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def pressXfun (c h : ℝ) (p : World × Bool) : ℝ :=
  (if p.2 then (1 : ℝ) else 0) * ((1 - (if p.1 = .wrong then (1 : ℝ) else 0)) * c - (if p.1 = .wrong then (1 : ℝ) else 0) * h)

/-- The round-`0` press-weighted value as a function of the first coordinate.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressX_zero :
    (fun ω : (World × Bool) × (World × Bool) => indB ((twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).pressed 0) ω *
        (twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).X 0 ω) = fun ω => pressXfun c h ω.1 := by
  funext ω
  simp [twoRounds, ShutdownProc.X, ShutdownProc.C, ShutdownProc.H, indB, pressXfun]

/-- `pressX_one` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressX_one :
    (fun ω : (World × Bool) × (World × Bool) => indB ((twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).pressed 1) ω *
        (twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).X 1 ω) = fun ω => pressXfun c h ω.2 := by
  funext ω
  simp [twoRounds, ShutdownProc.X, ShutdownProc.C, ShutdownProc.H, indB, pressXfun]

/-- `E_cell[Pr · X] = (1 − ε) α c − ε β h`. Source: corr-three-step (the press cell). Kind: L. Fidelity: exact -/
lemma expect_cell_pressX (ε : ℝ) (hε) :
    expect (cell ε α β hε hα hβ) (pressXfun c h) = (1 - ε) * α * c - ε * β * h := by
  rw [expect_cell]; simp [pressXfun]; ring

/-- **(a) at round `0`**: `I₁` is the odds inequality at `ε₁`.
Source: [[corr-wf14-inventory]] 075 / invariant-final.md Statement 5 (`I₁ ⟺ ε h β ≥ (1 − ε) c α`)
Kind: L (the parent's identity with a time index)
Fidelity: exact -/
theorem objCompliance_zero_iff (ω : (World × Bool) × (World × Bool)) :
    (twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).objCompliance 0 ω ↔ oddsIneq α β h c ε₁ := by
  unfold ShutdownProc.objCompliance
  rw [pressX_zero]
  have hc0 : condSum (twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).μ
      (twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).Fpre 0 (fun ω' => pressXfun c h ω'.1) ω =
      expect (prod2 (cell ε₁ α β hε₁ hα hβ) (cell ε₂ α β hε₂ hα hβ)) (fun ω' => pressXfun c h ω'.1) := rfl
  rw [hc0, expect_prod2_fst, expect_cell_pressX]
  unfold oddsIneq
  constructor <;> intro H <;> nlinarith

/-- **(a) at round `1`**: on the atom of a round-`0` outcome, `I₁` is the odds inequality at `ε₂`
unless the atom has mass `0` (where it holds vacuously).
Source: [[corr-wf14-inventory]] 075 / invariant-final.md Statement 5
Kind: L (the parent's identity with a time index, through `sum_filter_fst`)
Fidelity: exact -/
theorem objCompliance_one_iff (ω : (World × Bool) × (World × Bool)) :
    (twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).objCompliance 1 ω ↔
      (cell ε₁ α β hε₁ hα hβ).mass ω.1 = 0 ∨ oddsIneq α β h c ε₂ := by
  unfold ShutdownProc.objCompliance
  rw [pressX_one]
  have hc1 : condSum (twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).μ
      (twoRounds ε₁ ε₂ α β c h hε₁ hε₂ hα hβ hc hh).Fpre 1 (fun ω' => pressXfun c h ω'.2) ω =
      ∑ ω' ∈ univ.filter (fun ω' : (World × Bool) × (World × Bool) => ω'.1 = ω.1),
        (prod2 (cell ε₁ α β hε₁ hα hβ) (cell ε₂ α β hε₂ hα hβ)).mass ω' * pressXfun c h ω'.2 := rfl
  rw [hc1, sum_filter_fst]
  have := expect_cell_pressX α β c h hα hβ ε₂ hε₂
  unfold expect at this
  rw [this]
  unfold oddsIneq
  rcases (cell ε₁ α β hε₁ hα hβ).nonneg ω.1 |>.lt_or_eq with hpos | hzero
  · constructor
    · intro H
      right
      have := nonpos_of_mul_nonpos_right H hpos
      nlinarith
    · rintro (h0 | H)
      · rw [h0]; simp
      · exact mul_nonpos_of_nonneg_of_nonpos hpos.le (by nlinarith)
  · rw [← hzero]; simp

/-! ### (b) non-propagation: the source's own C10, confirmed; the propagating form -/

/-- **C10 — the source's own counterexample, re-proved on `oddsIneq`.** Statement 5(a) (develop l. 75,
repeated in the final) asserts that the weaker premise "(i) holds at `t = 0` and `ε_t h_t` is
non-decreasing" does **not** propagate (i), and checks it with C10: `β = 1`, `cα = 1`; round `0` with
`(ε, h) = (1/2, 1)` holds with equality, round `1` with `(1/4, 2)` has the same `ε h = 1/2` and fails
(`(1 − ε) c α = 3/4 > 1/2`). This confirms the source; it refutes nothing. (The mandate's T4(b) called
it "refuted" — a mandate error, audit r1 B2.) Addition the source does not make: at C10's round `0`
the propagating sufficient form `ε h β ≥ c α` itself fails (`1/2 < 1`), see `sufficient_form_propagates`.
Source: [[corr-wf14-inventory]] 2-022, 2-080 (C10) / invariant.md Statement 5(a) l. 75 ("does **not** propagate … C10 [checked]"); invariant-final.md Statement 5(a); checks.py C10
Kind: N+ (the source's C10 confirmed)
Fidelity: exact
Hyps: (a) only -/
theorem c10 : oddsIneq 1 1 1 1 (1 / 2) ∧ ¬ oddsIneq 1 1 2 1 (1 / 4) ∧ (1 / 2 : ℝ) * 1 = 1 / 4 * 2 := by
  unfold oddsIneq; norm_num

/-- **The surviving neighbour**: the `(1 − ε)`-free sufficient form `ε h β ≥ c α` propagates under
non-decreasing `ε_t h_t` (and implies the exact form).
Source: [[corr-wf14-inventory]] 075 / invariant-final.md Statement 5(a) ("The sufficient form … propagates")
Kind: L (one monotonicity step; relabelled from P, audit r2 fidelity N9 / adversarial N7)
Fidelity: exact
Hyps: (a) only -/
theorem sufficient_form_propagates (α β c h₀ h₁ ε₀ ε₁' : ℝ) (hβ : 0 ≤ β) (hcα : 0 ≤ c * α)
    (hε0 : 0 ≤ ε₁') (h0 : c * α ≤ ε₀ * h₀ * β) (hmono : ε₀ * h₀ ≤ ε₁' * h₁) :
    c * α ≤ ε₁' * h₁ * β ∧ oddsIneq α β h₁ c ε₁' := by
  have h1 : c * α ≤ ε₁' * h₁ * β := by nlinarith
  refine ⟨h1, ?_⟩
  unfold oddsIneq
  nlinarith [mul_nonneg hε0 hcα]

/-! ### (c) C3: the crossing -/

/-- **C3**: at `ε_t = 2^{−t}`, `(α, β, h, c) = (1/20, 1, 20, 1)`, (i) holds for every `t ≤ 8` and fails at
`t = 9` — the least failing index, proved as least.
Source: [[corr-wf14-inventory]] 075, 2-080 (C3) / invariant-final.md Statement 5(c) ("compliance rational through round 8, irrational from round 9")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem c3_least_failing :
    (∀ t ≤ 8, oddsIneq (1 / 20) 1 20 1 ((1 / 2 : ℝ) ^ t)) ∧ ¬ oddsIneq (1 / 20) 1 20 1 ((1 / 2 : ℝ) ^ 9) := by
  constructor
  · intro t ht
    unfold oddsIneq
    interval_cases t <;> norm_num
  · unfold oddsIneq; norm_num

/-- C3's criterion in closed form: (i) at `ε = 2^{−t}` iff `2^t ≤ 401`.
Source: invariant-final.md proof of Statement 5(c). Kind: L. Fidelity: exact -/
theorem c3_iff (t : ℕ) : oddsIneq (1 / 20) 1 20 1 ((1 / 2 : ℝ) ^ t) ↔ (2 : ℝ) ^ t ≤ 401 := by
  unfold oddsIneq
  have hpos : (0 : ℝ) < 2 ^ t := by positivity
  have e : (1 / 2 : ℝ) ^ t = 1 / 2 ^ t := one_div_pow 2 t
  rw [e]
  have key : (1 - 1 / (2 : ℝ) ^ t) * 1 * (1 / 20) ≤ 1 / 2 ^ t * 20 * 1 ↔ 1 ≤ 401 * (1 / (2 : ℝ) ^ t) := by
    constructor <;> intro H <;> linarith
  rw [key, show (401 : ℝ) * (1 / 2 ^ t) = 401 / 2 ^ t by ring, le_div_iff₀ hpos, one_mul]

/-! ### (d) the compliance margin -/

/-- **The compliance margin** `M = log(ε h β) − log((1 − ε) c α)`.
Source: [[corr-wf14-inventory]] 075 / invariant-final.md Statement 5(d)
Kind: D
Fidelity: exact -/
noncomputable def complianceMargin (α β h c ε : ℝ) : ℝ := Real.log (ε * h * β) - Real.log ((1 - ε) * c * α)

/-- `I₁ ↔ 0 ≤ M` under positivity of both sides.
Source: [[corr-wf14-inventory]] 075 / invariant-final.md Statement 5(d) ("`I₁ ⟺ M_t ≥ 0`")
Kind: L
Fidelity: exact (positivity is where the logs are defined) -/
theorem oddsIneq_iff_margin_nonneg (α β h c ε : ℝ) (h1 : 0 < (1 - ε) * c * α) (h2 : 0 < ε * h * β) :
    oddsIneq α β h c ε ↔ 0 ≤ complianceMargin α β h c ε := by
  unfold oddsIneq complianceMargin
  rw [sub_nonneg, Real.log_le_log_iff h1 h2]

/-- **F3: the margin drifts up under an improving-overseers law.** With `α_t/β_t = 2^{−t}/20`
(`β = 1`) and `ε h/((1 − ε) c) = 1` (`ε = 1/2`, `h = c = 1`): `M_t = t log 2 + log 20`.
Source: [[corr-wf14-inventory]] 075, 2-080 (F3) / invariant-final.md Statement 5(d) ("`M_t = t log 2 + log 20`, increasing")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem f3_margin (t : ℕ) :
    complianceMargin ((1 / 2 : ℝ) ^ t / 20) 1 1 1 (1 / 2) = t * Real.log 2 + Real.log 20 := by
  unfold complianceMargin
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ t := by positivity
  rw [show (1 / 2 : ℝ) * 1 * 1 = 1 / 2 by ring, show (1 - 1 / 2 : ℝ) * 1 * ((1 / 2 : ℝ) ^ t / 20) =
    1 / 2 * ((1 / 2 : ℝ) ^ t / 20) by ring]
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_div hp.ne' (by norm_num), Real.log_pow,
    one_div, Real.log_inv]
  ring

/-- **F3: `M_t` is strictly increasing** — the drift statement exists once a law for `(α_t, β_t)` is given.
Source: [[corr-wf14-inventory]] 075, 2-080 (F3) / invariant-final.md Statement 5(d)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem f3_strictMono : StrictMono fun t : ℕ => complianceMargin ((1 / 2 : ℝ) ^ t / 20) 1 1 1 (1 / 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro s t hst
  simp only [f3_margin]
  have : (s : ℝ) < t := by exact_mod_cast hst
  nlinarith

/-! ### (e) five agreements -/

/-- **`I₁ ↔ Î₁` under the five agreements** `(ε̂, α̂, β̂, ĥ, ĉ) = (ε, α, β, h, c)`.
Source: [[corr-wf14-inventory]] 075 / invariant-final.md S4(i), Statement 5(e)
Kind: L
Fidelity: exact -/
theorem subj_iff_obj_of_agreements (α β h c ε αh βh hh ch εh : ℝ) (h1 : εh = ε) (h2 : αh = α) (h3 : βh = β)
    (h4 : hh = h) (h5 : ch = c) : oddsIneq αh βh hh ch εh ↔ oddsIneq α β h c ε := by
  subst h1 h2 h3 h4 h5; exact Iff.rfl

/-- **Three agreements do not suffice**: with `(ε̂, α̂, β̂) = (ε, α, β) = (1/10, 1/20, 9/10)` and `c = 1`,
the objective `h = 20` complies while the agent's `ĥ = 1/100` does not.
Source: [[corr-wf14-inventory]] 075 / invariant-final.md Statement 5(e), S4(i) ("five agreements, not three")
Kind: N+ (separation)
Fidelity: exact
Hyps: (a) only -/
theorem three_agreements_insufficient :
    oddsIneq (1 / 20) (9 / 10) 20 1 (1 / 10) ∧ ¬ oddsIneq (1 / 20) (9 / 10) (1 / 100) 1 (1 / 10) := by
  unfold oddsIneq; norm_num

/-! ### (f) E1 on the two-round process -/

/-- **E1 (2-007) as a trajectory**: with `(α, β, c, h) = (1/10, 3/5, 1, 4)`, `ε₁ = 1/10` complies
(`I₁` at round `0`, `6/25 ≥ 9/100`) and `ε₂ = 1/50` overrides (`¬I₁` at round `1` on every atom:
`6/125 < 49/500`) — "a maintained hypothesis, not an invariant". The posteriors are `Battery`'s.
Source: [[corr-wf14-inventory]] 2-007 / joint.md §P.11 (E1); `corr-joint-process` `Battery`
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem e1 :
    (∀ ω, (twoRounds (1 / 10) (1 / 50) (1 / 10) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num)).objCompliance 0 ω) ∧
    (∀ ω, ¬ (twoRounds (1 / 10) (1 / 50) (1 / 10) (3 / 5) 1 4 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num)).objCompliance 1 ω) := by
  constructor
  · intro ω
    rw [objCompliance_zero_iff]
    unfold oddsIneq; norm_num
  · intro ω
    rw [objCompliance_one_iff]
    rintro (h0 | H)
    · -- every round-0 outcome has positive mass
      rcases ω with ⟨⟨w, p⟩, _⟩
      cases w <;> cases p <;> simp [cell, twoPress] at h0 <;> norm_num at h0
    · unfold oddsIneq at H; norm_num at H

end Margin

end Cleanroom.Corrigibility.CorrTrajectory
