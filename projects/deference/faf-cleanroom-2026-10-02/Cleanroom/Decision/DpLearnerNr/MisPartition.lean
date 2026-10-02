import Cleanroom.Decision.DpLearnerNr.Policy

/-!
# `dp-learner-nr` targets 6 and 7(a): the mis-partitions are *absences* of a round law `F(π, w)`

**Policy-fairness** of an environment that may read an agent feature `g` besides the policy: its
round law `r : Π → G → W → K` (here the fill probability, a Bernoulli parameter) is a function of
`(π, w)` alone, `∃ F, ∀ π g w, r π g w = F π w`. The negative witnesses are environments whose
round law is a function of something else, shown by two points with the same `(π, w)` and
different fill (`not_policyFair_of_two`):

* **Target 6, the flag-reading Omega** (`flagFill`): fills by reading the act on rounds the agent
  flags as exploratory (`π ≠ greedy`), at base rate `β₀` otherwise; `π = one-box`, `g₁ = one-box`
  (not flagged: `β₀`) vs `g₂ = two-box` (flagged: `1`) with `β₀ < 1`. Corollary: D4's `Exogenous`
  is not applicable because its argument `law` does not exist — phrased as such, not as a theorem
  about truth values. The same two-point shape for 2-037(c): the stricter troll's trigger reads
  the agent's estimate `cf_t` (`stricterTrigger`), not `π_t`.
* **Target 7(a), the slowly-responding Omega** (`emaFill`, `emaSeq`): fill at round `t` is the
  exponential moving average of past one-boxing; it is a function of the policy *history*, and two
  histories with the same `π_t` have different fill.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Policy-fairness of a round law that may read an agent feature `g`**: it is a function of
`(π, w)` alone.
Source: [[policy-level-fdt-learner]] §6 ("*Policy-fairness*: `F` depends on the agent only
through `π_t`"), §3 (iv) ("the environment's law is not a function `F(π, w)`");
[[dp-learner-nr-mandate]] D4
Kind: D -/
def PolicyFair {Pol G W : Type} (r : Pol → G → W → K) : Prop := ∃ F : Pol → W → K, ∀ π g w, r π g w = F π w

/-- **Two points with the same `(π, w)` and different values refute policy-fairness.**
Source: [[dp-learner-nr-mandate]] target 6 ("exhibit `π = one-box`, `w` fixed, `g₁`, `g₂`")
Kind: L -/
theorem not_policyFair_of_two {Pol G W : Type} (r : Pol → G → W → K) (π : Pol) (w : W) (g₁ g₂ : G)
    (h : r π g₁ w ≠ r π g₂ w) : ¬ PolicyFair r := by
  rintro ⟨F, hF⟩
  exact h ((hF π g₁ w).trans (hF π g₂ w).symm)

/-! ## Target 6: the flag-reading Omega -/

/-- **The flag-reading Omega's fill probability**: on a flagged round (`π ≠ greedy`) it reads the
act — fills iff the policy is one-box (`Act2.a`); otherwise it fills at the base rate `β₀`. The
flag is a feature of the learner's relation to its policy, not of the policy.
Source: [[policy-level-fdt-learner]] §2.3 ("Omega reads the agent's act on rounds the agent flags
as exploratory (adopted policy ≠ greedy) and fills at base rate `β₀` otherwise");
[[dp-core-2-inventory]] 031; [[dp-learner-nr-mandate]] target 6
Kind: D -/
def flagFill (β₀ : K) (π greedy : Act2) (_w : Unit) : K :=
  if π ≠ greedy then (if π = Act2.a then 1 else 0) else β₀

/-- **No round law `F(π, w)` for the flag-reading Omega** (target 6): with `π = one-box` and the
same `w`, the unflagged round (`greedy = one-box`) fills at `β₀` and the flagged round
(`greedy = two-box`) fills at `1`; for `β₀ < 1` these differ. So D4's `Exogenous` is not
applicable — its argument `law π` does not exist — and the learner's verdict is an artifact of its
exploration schedule (the dynamics are recorded in findings, not formalized).
Source: [[policy-level-fdt-learner]] §2.3 ("No partition is even well-defined here, because the
environment's law is not a function of `(π, w)`"), §3 (iv); [[dp-core-2-inventory]] 031, 037(c);
[[dp-learner-nr-mandate]] target 6
Kind: N+
Fidelity: exact (the fill as a Bernoulli parameter; the oscillation at `β₀ = 0` and the payoff
`≈ 740` are simulation, findings)
Hyps: (a) `β₀ < 1` -/
theorem flagFill_not_policyFair (β₀ : K) (hβ : β₀ < 1) : ¬ PolicyFair (flagFill β₀) :=
  not_policyFair_of_two (flagFill β₀) Act2.a () Act2.a Act2.b (by simp [flagFill]; exact hβ.ne)

/-- **The stricter troll's trigger reads the agent's estimate, not the policy** (2-037(c)): the
troll fires on a crossing made against the agent's own estimate `cf_t < 0`; with `π = cross` and
the same `w`, the estimate `cf = 1` does not fire and `cf = −1` does.
Source: [[policy-level-fdt-learner]] §4.4 ("Its trigger reads `cf_t` — the agent's internal
estimate, which is a function of the agent's data, not of `π_t`"); [[dp-core-2-inventory]] 037(c);
[[dp-learner-nr-mandate]] target 6
Kind: N+ -/
def stricterTrigger (π : Act2) (cf : K) (_w : Unit) : K :=
  if π = Act2.a ∧ cf < 0 then 1 else 0

/-- The stricter troll is not policy-fair.
Source: [[dp-learner-nr-mandate]] target 6
Kind: N+ -/
theorem stricterTrigger_not_policyFair : ¬ PolicyFair (stricterTrigger (K := K)) :=
  not_policyFair_of_two stricterTrigger Act2.a () (1 : K) (-1) (by norm_num [stricterTrigger])

/-! ## Target 7(a): the slowly-responding Omega -/

/-- **The EMA Omega's fill update**: `fill_t = λ·[π_{t−1} = one-box] + (1−λ)·fill_{t−1}`.
Source: [[policy-level-fdt-learner]] §2.4 ("Omega fills w.p. the exponential moving average of the
agent's past one-boxing (rate `λ`)"); [[dp-core-2-inventory]] 032; [[dp-learner-nr-mandate]] target 7(a)
Kind: D -/
def emaFill (lam prev : K) (πprev : Act2) : K :=
  lam * (if πprev = Act2.a then 1 else 0) + (1 - lam) * prev

/-- The fill at round `t` along a policy history `π : ℕ → Act2`, from `fill₀`.
Source: [[policy-level-fdt-learner]] §2.4; [[dp-learner-nr-mandate]] target 7(a)
Kind: D -/
def emaSeq (lam fill₀ : K) (π : ℕ → Act2) : ℕ → K
  | 0 => fill₀
  | t + 1 => emaFill lam (emaSeq lam fill₀ π t) (π t)

/-- The EMA round law as a function of `(π_t, history, w)`: the fill at round `t` reads the
history `(fill_{t−1}, π_{t−1})`, not `π_t`.
Source: [[dp-learner-nr-mandate]] target 7(a)
Kind: D -/
def emaRound (lam : K) (_πt : Act2) (h : K × Act2) (_w : Unit) : K := emaFill lam h.1 h.2

/-- **No round law `F(π, w)` for the EMA Omega**: two histories with the same `π_t` and `w` —
`(fill_{t−1}, π_{t−1}) = (0, two-box)` and `(1, one-box)` — give fills `0` and `1`.
Source: [[policy-level-fdt-learner]] §2.4; [[dp-core-2-inventory]] 032; [[dp-learner-nr-mandate]] target 7(a)
Kind: N+
Fidelity: exact (the two-point shape of target 6) -/
theorem emaRound_not_policyFair (lam : K) : ¬ PolicyFair (emaRound lam) :=
  not_policyFair_of_two (emaRound lam) Act2.a () ((0 : K), Act2.b) ((1 : K), Act2.a)
    (by simp [emaRound, emaFill])

/-- Along the always-two-box history the EMA fill from `0` stays `0`.
Source: none: infrastructure
Kind: L -/
theorem emaSeq_const_b (lam : K) (t : ℕ) : emaSeq lam 0 (fun _ => Act2.b) t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [emaSeq, emaFill, ih]

/-- Along the always-one-box history the EMA fill from `0` is `1 − (1−λ)^t`.
Source: none: infrastructure
Kind: L -/
theorem emaSeq_const_a (lam : K) (t : ℕ) :
    emaSeq lam 0 (fun _ => Act2.a) t = 1 - (1 - lam) ^ t := by
  induction t with
  | zero => simp [emaSeq]
  | succ t ih => simp [emaSeq, emaFill, ih, pow_succ]; ring

/-- A history that two-boxes before round `t` and one-boxes from round `t` on has EMA fill `0`
at round `t`.
Source: none: infrastructure
Kind: L -/
theorem emaSeq_switch (lam : K) (t : ℕ) :
    emaSeq lam 0 (fun s => if s < t then Act2.b else Act2.a) t = 0 := by
  suffices h : ∀ s ≤ t, emaSeq lam 0 (fun s => if s < t then Act2.b else Act2.a) s = 0 from
    h t le_rfl
  intro s hs
  induction s with
  | zero => rfl
  | succ s ih =>
    have hlt : s < t := by omega
    simp [emaSeq, emaFill, ih (by omega), hlt]

/-- **Two policy histories with the same `π_t` and different EMA fills at round `t`** (`t ≥ 1`,
`0 < λ ≤ 1`): the switching history (two-box before `t`, one-box at `t`) has fill `0`, the
always-one-box history has fill `1 − (1−λ)^t > 0`; both play one-box at round `t`. The round law
is a function of the history, not of `(π_t, w_t)`; identifiability needs visitation at the
environment's response timescale.
Source: [[policy-level-fdt-learner]] §2.4 ("The exogeneity finding is *true at the timescale
tested* and false at Omega's"); [[dp-core-2-inventory]] 032; [[dp-learner-nr-mandate]] target 7(a)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < λ ≤ 1`, `1 ≤ t` -/
theorem emaSeq_two_histories (lam : K) (hl0 : 0 < lam) (hl1 : lam ≤ 1) (t : ℕ) (ht : 1 ≤ t) :
    (fun s => if s < t then Act2.b else Act2.a) t = (fun _ => Act2.a) t ∧
    emaSeq lam 0 (fun s => if s < t then Act2.b else Act2.a) t = 0 ∧
    0 < emaSeq lam 0 (fun _ => Act2.a) t := by
  refine ⟨by simp, emaSeq_switch lam t, ?_⟩
  rw [emaSeq_const_a]
  have h1 : (1 - lam) ^ t < 1 := by
    apply pow_lt_one₀ (by linarith) (by linarith)
    omega
  linarith

end Cleanroom.Decision.DpLearnerNr
