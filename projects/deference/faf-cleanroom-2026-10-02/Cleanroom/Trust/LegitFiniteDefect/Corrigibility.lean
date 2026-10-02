import Cleanroom.Trust.LegitFiniteDefect.Defs

/-!
# The corrigibility sign flip

Package `legit-finite-defect`, Target 3 (item 021). The comply-advantage `complyAdv π s d` is a
signed weighted sum (`complyAdv_decomp`); its sign is governed pointwise by whether the signal
weight lands on danger (`d x > 1/2`) or safety. The two theorems are the encodings' sign lemmas
(kind L: the content is the encoding, per the model's §3.2 — "endorsement-faithful" and
"adversarial" are the model's pointwise encodings; "corrigibility" is interpretation). The
witness is the row that matters: one four-world frame, three signals, advantages `+1/2, 0, −1/2`,
with the blank signal failing *both* pointwise hypotheses, so neither theorem is vacuous.
-/

namespace Cleanroom.Trust.LegitFiniteDefect

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Endorsed signal ⇒ nonnegative comply-advantage.** The hypothesis `0 ≤ s x · (2 d x − 1)` at
every world is the model's *encoding* of "endorsement-faithful": the signed weight
`s_x (2 d_x − 1)` is nonnegative at every world. The model declares `s : W → ℝ₊`, and *with*
`0 ≤ s` the encoding reads "the signal fires only where danger is at least `1/2`"; this theorem
drops `0 ≤ s` because the proof never uses it, so it is strictly stronger than the model's and
its hypothesis admits signals with negative weight on safe worlds (audit round 1, probe P2:
`s = (−1, 0, 0, 0)` satisfies it and gets advantage `+1/4`). The theorem is the sign of a sum of
nonnegative terms.
Source: [[legitimacy-corrigibility-model]] §3.2 (a) (`endorsed_signal_complies`); trust-lab-021
Kind: L
Fidelity: stronger: the model's `s ≥ 0` is dropped (unused); the model's reading needs it
Hyps: (a) `hπ`; (a) `hfire` is the encoding, per the model §3.2 -/
theorem complyAdv_nonneg_of_endorsed {π s d : W → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hfire : ∀ x, 0 ≤ s x * (2 * d x - 1)) : 0 ≤ complyAdv π s d := by
  rw [complyAdv_decomp]
  apply Finset.sum_nonneg
  intro x _
  rw [mul_assoc]
  exact mul_nonneg (hπ x) (hfire x)

/-- **Adversarial signal ⇒ nonpositive comply-advantage.** Dual encoding: the signed weight
`s_x (2 d_x − 1)` is nonpositive at every world (with the model's `0 ≤ s`, "the signal fires
only where danger is at most `1/2`"; `0 ≤ s` is dropped here as unused, see
`complyAdv_nonneg_of_endorsed`).
Source: [[legitimacy-corrigibility-model]] §3.2 (b) (`adversarial_signal_resists`); trust-lab-021
Kind: L
Fidelity: stronger: the model's `s ≥ 0` is dropped (unused)
Hyps: (a) `hπ`; (a) `hfire` is the encoding, per the model §3.2 -/
theorem complyAdv_nonpos_of_adversarial {π s d : W → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hfire : ∀ x, s x * (2 * d x - 1) ≤ 0) : complyAdv π s d ≤ 0 := by
  rw [complyAdv_decomp]
  apply Finset.sum_nonpos
  intro x _
  rw [mul_assoc]
  exact mul_nonpos_of_nonneg_of_nonpos (hπ x) (hfire x)

/-- **Strict version** (021's extension): an endorsed signal with positive endorsed mass at some
world has strictly positive comply-advantage — strict compliance, not merely weak.
Source: trust-lab-021 (Flags: extension); [[legitimacy-corrigibility-redteam]] (b) ("the positive
theorem buys only weak preference" — this is the strict supplement)
Kind: L
Fidelity: stronger: strict conclusion under a positive-mass hypothesis
Hyps: (a) `hπ`; (a) `hfire` encoding; (a) `hpos` positive endorsed mass at `x₀` -/
theorem complyAdv_pos_of_endorsed {π s d : W → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hfire : ∀ x, 0 ≤ s x * (2 * d x - 1)) (x₀ : W) (hpos : 0 < π x₀ * s x₀ * (2 * d x₀ - 1)) :
    0 < complyAdv π s d := by
  rw [complyAdv_decomp]
  have : ∑ _x : W, (0 : ℝ) < ∑ x, π x * s x * (2 * d x - 1) := by
    apply Finset.sum_lt_sum
    · intro x _
      rw [mul_assoc]
      exact mul_nonneg (hπ x) (hfire x)
    · exact ⟨x₀, mem_univ _, hpos⟩
  simpa using this

/-! ## The witness: one frame, three signals -/

namespace Corrigibility

/-- Four worlds `Fin 4` read as `(danger?, fires?)`: `0 = (¬d, ¬S)`, `1 = (¬d, S)`,
`2 = (d, ¬S)`, `3 = (d, S)`. The danger indicator.
Source: [[legitimacy-corrigibility-model]] §3.3 (four worlds `(d?, S?)`)
Kind: D
Fidelity: exact -/
def dW : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- The uniform prior on the four worlds (`P(d) = 1/2`).
Source: [[legitimacy-corrigibility-model]] §3.3 (`P_A(d) = 1/2`)
Kind: D
Fidelity: exact -/
def πW : Fin 4 → ℝ := ![1 / 4, 1 / 4, 1 / 4, 1 / 4]

/-- The legitimate signal `S ⇔ d`: fires exactly on danger worlds.
Source: [[legitimacy-corrigibility-model]] §3.3 (row "legitimate")
Kind: D
Fidelity: exact -/
def sLegit : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- The blank signal `S ⊥ d`: fires on the second coordinate, independent of danger.
Source: [[legitimacy-corrigibility-model]] §3.3 (row "endorsement-blank")
Kind: D
Fidelity: exact -/
def sBlank : Fin 4 → ℝ := ![0, 1, 0, 1]

/-- The adversarial signal `S ⇔ ¬d`: fires exactly on safe worlds.
Source: [[legitimacy-corrigibility-model]] §3.3 (row "adversarial")
Kind: D
Fidelity: exact -/
def sAdv : Fin 4 → ℝ := ![1, 1, 0, 0]

/-- The prior is nonnegative and gives danger probability `1/2`.
Source: [[legitimacy-corrigibility-model]] §3.3
Kind: L
Fidelity: exact -/
theorem πW_nonneg_and_danger_half : (∀ x, 0 ≤ πW x) ∧ E πW dW = 1 / 2 := by
  refine ⟨fun x => by fin_cases x <;> norm_num [πW], ?_⟩
  simp only [E, Fin.sum_univ_four, πW, dW, vec4_two, vec4_three]
  norm_num

/-- **The sign flip, computed.** The same frame and prior give comply-advantages `+1/2`, `0`,
`−1/2` for the legitimate, blank and adversarial signals. (The model's §3.3 table lists the
conditional comparisons `P_A(d | S) = 1, 1/2, 0` against `1/2`; these values are those
comparisons unnormalised by `P(S) = 1/2`, i.e. `P(S ∧ d) − P(S ∧ ¬d)`, same signs.) All three
signals are nonnegative, so the model's `s : W → ℝ₊` is honoured by the witness.
Source: [[legitimacy-corrigibility-model]] §3.3 (the table); trust-lab-021
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem three_signals :
    complyAdv πW sLegit dW = 1 / 2 ∧ complyAdv πW sBlank dW = 0 ∧
      complyAdv πW sAdv dW = -1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [complyAdv_decomp, Fin.sum_univ_four, πW, sLegit, sBlank, sAdv, dW, vec4_two,
      vec4_three] <;> norm_num

/-- The legitimate signal satisfies the endorsed encoding (with positive endorsed mass at world
`3`), the adversarial signal satisfies the adversarial encoding, and the **blank signal fails
both** pointwise hypotheses — endorsement is silent on it, and neither theorem is vacuous.
Source: [[legitimacy-corrigibility-model]] §3.3–3.4; [[legitimacy-corrigibility-redteam]] "ATTACK
4/5"
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem hypotheses_discriminate :
    (∀ x, 0 ≤ sLegit x * (2 * dW x - 1)) ∧ 0 < πW 3 * sLegit 3 * (2 * dW 3 - 1) ∧
      (∀ x, sAdv x * (2 * dW x - 1) ≤ 0) ∧
      ¬ (∀ x, 0 ≤ sBlank x * (2 * dW x - 1)) ∧ ¬ (∀ x, sBlank x * (2 * dW x - 1) ≤ 0) := by
  refine ⟨fun x => by fin_cases x <;> norm_num [sLegit, dW], by norm_num [πW, sLegit, dW, vec4_three],
    fun x => by fin_cases x <;> norm_num [sAdv, dW], ?_, ?_⟩
  · intro h
    have := h 1
    norm_num [sBlank, dW] at this
  · intro h
    have := h 3
    norm_num [sBlank, dW, vec4_three] at this

/-- The strict theorem applies to the legitimate signal and yields `0 < complyAdv`, consistent
with the computed `1/2`.
Source: trust-lab-021 (extension)
Kind: L
Fidelity: n/a -/
theorem legit_strict : 0 < complyAdv πW sLegit dW :=
  complyAdv_pos_of_endorsed πW_nonneg_and_danger_half.1 hypotheses_discriminate.1 3
    hypotheses_discriminate.2.1

end Corrigibility

end

end Cleanroom.Trust.LegitFiniteDefect
