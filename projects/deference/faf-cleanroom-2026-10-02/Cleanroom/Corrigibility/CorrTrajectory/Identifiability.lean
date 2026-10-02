import Cleanroom.Corrigibility.CorrTrajectory.Certificate

/-!
# `corr-trajectory` — `Identifiability`: which certificate hypotheses are checkable (T14, extension)

`invariant-final.md` Open problem 1 made exact in Layer F: the **observable record** of a round is
`(Pr_t, κ_t, the outcome W_t if executed)` — on a complied round `W_t` is unobserved (S2 step 5). Two
`AgentView`s on the same `Ω`, with the same agent, the same decisions and **identical laws of the
record**, such that the running-certificate hypothesis `Δ_t ≤ 0` holds in one and fails in the
other: one round, the agent at credence `1/2` refrains; objectively `W ~ Bern(1/2)` (calibrated,
`Δ₀ = 0`) or `W ~ Bern(1/8)` (`Δ₀ = 9/40 > 0`). The record is `(press, comply, none)` with
probability `1` in both. Hence `Δ_t ≤ 0` — and calibration on `W_t ∣ 𝓕_t^-` — are **not identifiable
from observables** (`not_identifiable`). The positive half is immediate from the definition: on an
executed round the record contains `W_t`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

namespace Identifiability

/-- **The observable record of round `t`**: the press, the compliance indicator, and the outcome `W_t`
only if executed.
Source: [[corr-wf14-inventory]] 2-087, 073 / invariant-final.md Open problem 1, S2 step 5
Kind: D
Fidelity: exact -/
def record {Ω M : Type} [Fintype Ω] [DecidableEq Ω] (S : ShutdownProc Ω M) (t : ℕ) (ω : Ω) :
    Bool × Bool × Option Bool :=
  (S.pressed t ω, S.kappa t ω, if S.executed t ω then some (S.wrong t ω) else none)

/-- The record through `T`. Source: Open problem 1. Kind: D. Fidelity: exact -/
def recordBy {Ω M : Type} [Fintype Ω] [DecidableEq Ω] (S : ShutdownProc Ω M) (T : ℕ) (ω : Ω) :
    Fin (T + 1) → Bool × Bool × Option Bool := fun t => record S t ω

/-- Two processes on the same `Ω` have **the same law of the record through `T`**.
Source: Open problem 1 ("checkable from observables"). Kind: D. Fidelity: exact -/
def SameRecordLaw {Ω M : Type} [Fintype Ω] [DecidableEq Ω] (S₁ S₂ : ShutdownProc Ω M) (T : ℕ) : Prop :=
  ∀ r : Fin (T + 1) → Bool × Bool × Option Bool,
    probOf S₁.μ (univ.filter fun ω => recordBy S₁ T ω = r) = probOf S₂.μ (univ.filter fun ω => recordBy S₂ T ω = r)

/-- The Bernoulli law on `Bool`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def bern (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : Distr Bool where
  mass b := if b then p else 1 - p
  nonneg b := by cases b <;> simp <;> linarith [hp.1, hp.2]
  sum_eq_one := by simp [Fintype.sum_bool]

/-- `expect_bern` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_bern (p : ℝ) (hp) (f : Bool → ℝ) : expect (bern p hp) f = p * f true + (1 - p) * f false := by
  simp [expect, Fintype.sum_bool, bern]

/-- The agent's law: credence `1/2`. Source: mandate T14. Kind: D. Fidelity: exact -/
noncomputable def half : Distr Bool := bern (1 / 2) ⟨by norm_num, by norm_num⟩

/-- `expect_half` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_half (f : Bool → ℝ) : expect half f = 1 / 2 * f true + (1 - 1 / 2) * f false :=
  expect_bern _ _ f

/-- **The one-round toy with objective wrongness `qs`**: the agent at credence `1/2` refrains
(`h = 1`, `c = 3/5`), the press is on, so `W` is never observed.
Source: mandate T14
Kind: D
Fidelity: exact -/
noncomputable def toy (qs : ℝ) (hqs : qs ∈ Set.Icc (0 : ℝ) 1) : AgentView Bool Unit where
  μ := bern qs hqs
  F := Atoms.trivial
  Fpre := Atoms.trivial
  post_subset_pre _ _ := subset_rfl
  pre_succ_subset_post _ _ := subset_rfl
  wrong t ω := if t = 0 then ω else false
  mag _ _ := ()
  hOf _ := 1
  cOf _ := 3 / 5
  hOf_nonneg _ := by norm_num
  cOf_nonneg _ := by norm_num
  pressed _ _ := true
  pressed_meas _ _ _ _ := rfl
  kappa _ _ := true
  kappa_meas _ _ _ _ := rfl
  irr _ _ := false
  cat _ _ := false
  cat_absorbing _ _ _ h := h
  agentLaw _ _ := half
  agentLaw_meas _ _ _ _ := rfl
  L _ := univ

/-- `toy_agentLaw` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_agentLaw (qs : ℝ) (hqs) (t : ℕ) (ω : Bool) : (toy qs hqs).agentLaw t ω = half := rfl

/-- `toy_loss_zero` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_loss_zero (qs : ℝ) (hqs) (ω : Bool) : (toy qs hqs).loss 0 ω = if ω then 0 else 3 / 5 := by
  unfold ShutdownProc.loss ShutdownProc.harm ShutdownProc.omission ShutdownProc.H ShutdownProc.C
  cases ω <;> simp [toy, indB, ShutdownProc.executed]

/-- `toy_Psi` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_Psi (qs : ℝ) (hqs) (ω : Bool) : (toy qs hqs).Psi 0 0 ω = 3 / 10 := by
  unfold AgentView.Psi
  have e : (toy qs hqs).R 0 0 = (toy qs hqs).loss 0 := by funext ω; simp [AgentView.R]
  rw [e]
  have e' : (toy qs hqs).loss 0 = fun ω => if ω then 0 else 3 / 5 := funext (toy_loss_zero qs hqs)
  rw [e', toy_agentLaw, expect_half]; norm_num

/-- The optimism drift of the toy: `Δ₀ = (1 − q*) · 3/5 − 3/10`. Source: mandate T14. Kind: L. Fidelity: exact -/
lemma toy_drift (qs : ℝ) (hqs) (ω : Bool) : (toy qs hqs).drift 0 0 ω = (1 - qs) * (3 / 5) - 3 / 10 := by
  unfold AgentView.drift
  have hF : (toy qs hqs).F = Atoms.trivial := rfl
  rw [hF, condSum_trivial, condSum_trivial, Found.CorrThreeStep.expect_add]
  have e1 : (toy qs hqs).Psi 0 1 = fun _ => 0 := funext ((toy qs hqs).Psi_top 0)
  have e0 : (toy qs hqs).Psi 0 0 = fun _ => 3 / 10 := funext (toy_Psi qs hqs)
  have e' : (toy qs hqs).loss 0 = fun ω => if ω then 0 else 3 / 5 := funext (toy_loss_zero qs hqs)
  rw [e1, e0, e', Found.CorrThreeStep.expect_const, Found.CorrThreeStep.expect_const]
  show 0 + expect (bern qs hqs) _ - _ = _
  rw [expect_bern]; simp <;> ring

/-- The record is `(press, comply, none)` whatever `ω`. Source: mandate T14. Kind: L. Fidelity: exact -/
lemma toy_record (qs : ℝ) (hqs) (ω : Bool) : record (toy qs hqs).toShutdownProc 0 ω = (true, true, none) := by
  simp [record, toy, ShutdownProc.executed]

/-- `toy_recordBy` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toy_recordBy (qs : ℝ) (hqs) (ω : Bool) :
    recordBy (toy qs hqs).toShutdownProc 0 ω = fun _ => (true, true, none) := by
  funext t
  have ht : (t : ℕ) = 0 := Nat.lt_one_iff.1 t.isLt
  simp only [recordBy, ht, toy_record]

/-- **T14: the running-certificate hypothesis is not identifiable from observables.** The two toys at
`q* = 1/2` and `q* = 1/8` have the same law of the record (a point mass at `(press, comply, none)`),
the same agent (`Ψ₀ = 3/10`), and `Δ₀ = 0 ≤ 0` in the first, `Δ₀ = 9/40 > 0` in the second. The
calibration conjunct (`1/2 = 1/2` in the first, `1/2 ≠ 1/8` in the second) is `calibration_not_identifiable`.
Source: [[corr-wf14-inventory]] 2-087, 073 / invariant-final.md Open problem 1, Statement 3 ("not verifiable from observables")
Kind: N+ (separation; the extension target made exact — relabelled from P, audit r1 N1)
Fidelity: exact
Hyps: (a) only -/
theorem not_identifiable :
    SameRecordLaw (toy (1 / 2) ⟨by norm_num, by norm_num⟩).toShutdownProc
        (toy (1 / 8) ⟨by norm_num, by norm_num⟩).toShutdownProc 0 ∧
      (∀ ω, (toy (1 / 2) ⟨by norm_num, by norm_num⟩).drift 0 0 ω ≤ 0) ∧
      (∃ ω, ¬ (toy (1 / 8) ⟨by norm_num, by norm_num⟩).drift 0 0 ω ≤ 0) ∧
      (toy (1 / 2) ⟨by norm_num, by norm_num⟩).Psi 0 0 true = (toy (1 / 8) ⟨by norm_num, by norm_num⟩).Psi 0 0 true := by
  refine ⟨?_, fun ω => ?_, ⟨true, ?_⟩, ?_⟩
  · intro r
    have e1 : (univ.filter fun ω => recordBy (toy (1 / 2) ⟨by norm_num, by norm_num⟩).toShutdownProc 0 ω = r) =
        if r = fun _ => (true, true, none) then univ else ∅ := by
      split_ifs with h
      · exact filter_true_of_mem fun ω _ => by rw [toy_recordBy, h]
      · exact filter_false_of_mem fun ω _ => by rw [toy_recordBy]; exact fun h' => h h'.symm
    have e2 : (univ.filter fun ω => recordBy (toy (1 / 8) ⟨by norm_num, by norm_num⟩).toShutdownProc 0 ω = r) =
        if r = fun _ => (true, true, none) then univ else ∅ := by
      split_ifs with h
      · exact filter_true_of_mem fun ω _ => by rw [toy_recordBy, h]
      · exact filter_false_of_mem fun ω _ => by rw [toy_recordBy]; exact fun h' => h h'.symm
    rw [e1, e2]
    split_ifs
    · rw [probOf_univ, probOf_univ]
    · simp [probOf]
  · rw [toy_drift]; norm_num
  · rw [toy_drift]; norm_num
  · rw [toy_Psi, toy_Psi]

/-- **T14, the calibration conjunct** (audit r1, fidelity N6): on the same two toys the agent's one-step
forecast `P₀(W₀ = 1) = 1/2` is calibrated against the objective `q* = 1/2` and not against `q* = 1/8`,
while the law of the record is the same (`not_identifiable`) — calibration on `W ∣ 𝓕^-` is not
identifiable from observables either.
Source: [[corr-wf14-inventory]] 2-087, 073 / invariant-final.md Statement 3 ("not verifiable from observables")
Kind: N+ (separation)
Fidelity: exact
Hyps: (a) only -/
theorem calibration_not_identifiable :
    expect (toy (1 / 2) ⟨by norm_num, by norm_num⟩).μ (indB ((toy (1 / 2) ⟨by norm_num, by norm_num⟩).wrong 0)) =
        expect half (indB ((toy (1 / 2) ⟨by norm_num, by norm_num⟩).wrong 0)) ∧
      expect (toy (1 / 8) ⟨by norm_num, by norm_num⟩).μ (indB ((toy (1 / 8) ⟨by norm_num, by norm_num⟩).wrong 0)) ≠
        expect half (indB ((toy (1 / 8) ⟨by norm_num, by norm_num⟩).wrong 0)) := by
  have e : ∀ qs hqs, indB ((toy qs hqs).wrong 0) = fun ω => if ω then 1 else 0 := by
    intro qs hqs; funext ω; simp [indB, toy]
  have hμ : ∀ qs hqs, (toy qs hqs).μ = bern qs hqs := fun _ _ => rfl
  constructor
  · simp only [e]; rw [hμ, expect_bern, expect_half]
  · simp only [e]; rw [hμ, expect_bern, expect_half]; norm_num

end Identifiability

end Cleanroom.Corrigibility.CorrTrajectory
