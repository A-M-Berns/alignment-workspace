import Cleanroom.Corrigibility.CorrTrajectory.Process
import Cleanroom.Corrigibility.CorrChannelVoi.Sensors

/-!
# `corr-trajectory` — `Coverage`: Statement 9, coverage persistence and the refuted VOI form (T8)

* (a) the set algebra: `I₂^cov` (newly unlocked actions covered at unlock) and persistence give
  `U_{t+1} ⊆ U_t` for the uncovered set `U_t = A_t \ C_t`, and the worst uncovered stake
  `h̄(U_t) = max_{U_t} h` is non-increasing along every path (`Finset.sup'`);
* (b) coverage bounds the **gap**, not the rate: a covered irreversible proposal at credence `≤ η'`
  has objective wrongness `≤ η + η'` (`gap_bound`); a covered action at credence `9/10` is `90 %`
  wrong (`covered_not_safe`);
* (c) **the VOI-form conjecture refuted (load-bearing 5)**: over `corr-channel-voi`'s `voiSensor`,
  A4 — `X = b·1[right] − h·1[wrong]`, `q̂ = 1/10`, `h = b = 1`, no experiment (`trivialExp`,
  `VOI = 0`): `I₂^VOI` holds (`E_P[harm] = 1/10 > 0`), the posterior-EV rule executes (`E_P X = 4/5`),
  objective wrongness `9/10`, gap `4/5 > η` for every `η < 4/5`. VOI bounds the exploration motive;
  the proposal is exploitation-driven. Reading of "`VOI_t(a)`" (ATTRIBUTION-UNVETTED): the note never
  fixes the experiment; with none available, `k = trivialExp`. At the *perfect* experiment the
  conjecture's hypothesis itself fails (`VOI = 1/10 = E_P[harm]`, not `<`): `a4_perfect`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Cleanroom.Corrigibility.CorrChannelVoi Cleanroom.Found.LitDdbFrames.Blackwell
open Finset hiding expect

namespace Coverage

section SetAlgebra

variable {𝒜 : Type} [DecidableEq 𝒜]

/-- The uncovered set `U_t = A_t \ C_t`. Source: invariant-final.md S4(ii). Kind: D. Fidelity: exact -/
def uncovered (A C : ℕ → Finset 𝒜) (t : ℕ) : Finset 𝒜 := A t \ C t

/-- **S4(ii), `I₂^cov`**: newly unlocked actions are covered at unlock, `A_{t+1} \ A_t ⊆ C_{t+1}`.
Source: [[corr-wf14-inventory]] 070 / invariant-final.md S4(ii)
Kind: D
Fidelity: exact -/
def I2cov (A C : ℕ → Finset 𝒜) (t : ℕ) : Prop := A (t + 1) \ A t ⊆ C (t + 1)

/-- **Statement 9(a), the set algebra**: `I₂^cov` and persistence `C_t ⊆ C_{t+1}` give `U_{t+1} ⊆ U_t`.
Source: [[corr-wf14-inventory]] 079 / invariant-final.md Statement 9 ("`U_{t+1} ⊆ U_t`")
Kind: L
Fidelity: exact -/
theorem uncovered_succ_subset {A C : ℕ → Finset 𝒜} {t : ℕ} (hI : I2cov A C t) (hC : C t ⊆ C (t + 1)) :
    uncovered A C (t + 1) ⊆ uncovered A C t := by
  intro a ha
  rw [uncovered, mem_sdiff] at ha ⊢
  obtain ⟨haA, haC⟩ := ha
  by_cases hAt : a ∈ A t
  · exact ⟨hAt, fun h => haC (hC h)⟩
  · exact absurd (hI (mem_sdiff.2 ⟨haA, hAt⟩)) haC

/-- **Statement 9(a), the worst uncovered stake is non-increasing** along every path (path-wise, random:
not "deterministic", adversary item 40).
Source: [[corr-wf14-inventory]] 079 / invariant-final.md Statement 9 ("`h̄(U_t)` is non-increasing")
Kind: L
Fidelity: exact (`sup'` needs the set nonempty; an empty `U_{t+1}` has no worst stake) -/
theorem hbar_anti {A C : ℕ → Finset 𝒜} {t : ℕ} (h : 𝒜 → ℝ) (hI : I2cov A C t) (hC : C t ⊆ C (t + 1))
    (hne : (uncovered A C (t + 1)).Nonempty) :
    (uncovered A C (t + 1)).sup' hne h ≤
      (uncovered A C t).sup' (hne.mono (uncovered_succ_subset hI hC)) h :=
  Finset.sup'_mono (f := h) (uncovered_succ_subset hI hC) hne

end SetAlgebra

/-- **Coverage at tolerance `η`**: `|cred − obj| ≤ η`, the agent's wrongness credence against the
objective rate. `η` is a parameter, never defined through a conclusion.
Source: [[corr-wf14-inventory]] 070 / invariant-final.md S4(ii)
Kind: D
Fidelity: exact -/
def covered (η cred obj : ℝ) : Prop := |cred - obj| ≤ η

/-- **Statement 9(b): coverage bounds the gap, not the rate.** A covered action proposed under a
rule that refuses above credence `η'` has objective wrongness `≤ η + η'`.
Source: [[corr-wf14-inventory]] 079 / invariant-final.md Statement 9 ("`ε^irr_t ≤ η + η'`")
Kind: L
Fidelity: exact -/
theorem gap_bound {η η' cred obj : ℝ} (hcov : covered η cred obj) (hrule : cred ≤ η') : obj ≤ η + η' := by
  unfold covered at hcov
  linarith [(abs_le.1 hcov).1]

/-- A covered action at credence `9/10` is `90 %` wrong (`η = 0`): coverage is not safety.
Source: invariant-final.md Statement 9 (adversary item 42)
Kind: N−
Fidelity: exact -/
theorem covered_not_safe : covered 0 (9 / 10) (9 / 10) := by
  unfold covered; simp

/-! ### (c) the refuted VOI form -/

/-- The action's payoff: `b` if right, `−h` if wrong. Source: counterexamples.py A4. Kind: D. Fidelity: exact -/
def payoff (b h : ℝ) : World → ℝ := fun w => match w with
  | .right => b
  | .wrong => -h

/-- **`I₂^VOI` at `(μ, k, b, h)`**: the agent's expected harm exceeds the value of information of its
available experiment `k`: `VOI_k(X) < P(wrong) · h`. Reading (ATTRIBUTION-UNVETTED): the note never
fixes the experiment.
Source: [[corr-wf14-inventory]] 070, 079 / invariant-final.md S4(ii) (VOI form), Statement 9
Kind: D
Fidelity: variant: the experiment made explicit -/
def I2voi {S : Type} [Fintype S] [DecidableEq S] (μ : Distr World) (k : Experiment World S) (b h : ℝ) :
    Prop := voiSensor μ k (payoff b h) < μ.mass .wrong * h

/-- The posterior-expected-value rule executes: `0 < E_P[X]`.
Source: invariant-final.md Statement 9 ("`(1 − q̂) b > q̂ h`"). Kind: D. Fidelity: exact -/
def executesByEV (μ : Distr World) (b h : ℝ) : Prop := 0 < expect μ (payoff b h)

/-- `expect_payoff` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_payoff (ε : ℝ) (hε) (b h : ℝ) : expect (twoPoint ε hε) (payoff b h) = (1 - ε) * b - ε * h := by
  simp [expect, World.sum_eq, payoff]; ring

/-- A4's prior: wrongness credence `1/10`. Source: counterexamples.py A4. Kind: D. Fidelity: exact -/
noncomputable def a4Prior : Distr World := twoPoint (1 / 10) ⟨by norm_num, by norm_num⟩

/-- **A4 — refutes Statement 9's VOI conjecture (load-bearing 5).** At `q̂ = 1/10`, `h = b = 1`,
no experiment: `VOI = 0 < 1/10 = E_P[harm]` (so `I₂^VOI` holds), `E_P X = 4/5 > 0` (the rule
executes), and the credence is uncovered against the objective wrongness `9/10` for every
`η < 4/5`. Surviving neighbour: (a)–(b), and v2 §1.7's narrower clause (VOI *from mistreating the
overseers*).
Source: [[corr-wf14-inventory]] 2-018 / invariant.md Statement 9 l. 87 ("[conjectured] … `I₂^VOI` under the posterior-optimal rule implies no uncovered irreversible proposal, without a separate caution primitive"); counterexamples.py A4
Kind: N+ (refutation)
Fidelity: exact (the reading `k = trivialExp` made explicit)
Hyps: (a) only -/
theorem a4 (η : ℝ) (hη : η < 4 / 5) :
    I2voi a4Prior trivialExp 1 1 ∧ executesByEV a4Prior 1 1 ∧ ¬ covered η (a4Prior.mass .wrong) (9 / 10) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold I2voi
    rw [voiSensor_eq_sub_trivial, sub_self]
    show (0 : ℝ) < 1 / 10 * 1
    norm_num
  · unfold executesByEV a4Prior
    rw [expect_payoff]; norm_num
  · unfold covered a4Prior
    rw [twoPoint_wrong]
    rw [not_le]
    rw [show (1 / 10 : ℝ) - 9 / 10 = -(4 / 5) by norm_num, abs_neg, abs_of_pos (by norm_num)]
    exact hη

/-- The conjecture as a universal statement, refuted: there is no `η < 4/5` for which
`I₂^VOI ∧ executes ⟹ covered` holds over all priors, stakes and objective rates.
Source: invariant.md Statement 9 l. 87 (the conjecture's universal form)
Kind: N+ (refutation)
Fidelity: exact -/
theorem voi_conjecture_refuted (η : ℝ) (hη : η < 4 / 5) :
    ¬ ∀ (μ : Distr World) (b h qs : ℝ), I2voi μ trivialExp b h → executesByEV μ b h →
      covered η (μ.mass .wrong) qs := by
  intro H
  obtain ⟨h1, h2, h3⟩ := a4 η hη
  exact h3 (H a4Prior 1 1 (9 / 10) h1 h2)

/-- At the **perfect** experiment the conjecture's hypothesis fails at A4's numbers:
`VOI(perfect) = E[max(X, 0)] − max(E X, 0) = 9/10 − 4/5 = 1/10 = E_P[harm]`, not strictly less.
Which experiment "`VOI_t(a)`" refers to decides whether `I₂^VOI` even holds (finding).
Source: mandate T8(c) (the reading); `corr-channel-voi` `sensorValue_perfect`
Kind: N−
Fidelity: exact -/
theorem a4_perfect : voiSensor a4Prior perfectExp (payoff 1 1) = 1 / 10 ∧ ¬ I2voi a4Prior perfectExp 1 1 := by
  have h : voiSensor a4Prior perfectExp (payoff 1 1) = 1 / 10 := by
    rw [voiSensor_eq_sub_trivial, sensorValue_perfect, sensorValue_trivial]
    unfold a4Prior
    rw [expect_payoff]
    simp [expect, World.sum_eq, payoff]
    norm_num
  refine ⟨h, ?_⟩
  unfold I2voi
  rw [h]
  show ¬ (1 / 10 : ℝ) < 1 / 10 * 1
  norm_num

end Coverage

end Cleanroom.Corrigibility.CorrTrajectory
