/-
# The scoring link and the gate theorem, for any legitimacy predicate

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-20.md` §4 B).
Two things that mention no particular definition of legitimacy, used by
`LegitimacyStatement.lean` and by `LegitimacyModel.lean`.

**The scoring link.**  `gatedScoring`: a decidable predicate `L` on histories, a violation
count `N`, a rating `ord` in `[0, 1]` and a window value in `[−δ, 0)` give a
`DeconfusingCorrigibility.Scoring` whose evaluation is the rating gated by `L` through
`Legitimacy.gateValue`.  Every theorem of `DeconfusingCorrigibility.Scoring` then applies to
it, since those hold for any predicate.

**The gate theorem.**  `gate_gives_behaviour`: a gate that passes illegitimate conduct with
probability at most `ρ` and legitimate conduct with probability at least `1 − ρ'` gives a
legitimate conduct strictly higher expected gated score than an illegitimate one whenever
`ρ (1 − w) < −w (1 − ρ')`, `w < 0` the value on failing.  `gate_threshold_delta`: at `ρ' = 0`,
`w = −δ` that is `ρ < δ/(1 + δ)`.  `gate_threshold_sharp`: equality of the two scores at the
threshold.  `gate_instance` inhabits the hypotheses.

**Not established here.**  That any process can evaluate a legitimacy predicate: the gate
theorem is a statement about seven real numbers and takes the two error probabilities as
given.  In `gatedScoring` the predicate, `N` and `ord` are data.  The link gives the
one-decision scoring; nothing here concerns `DeconfusingCorrigibility.Sequential`.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.DeconfusingCorrigibility
import Workspace.Deference.Contrib.Legitimacy

namespace Workspace.Deference.Contrib.LegitimacyGate

/-! ## The scoring link -/

/-- Any decidable predicate on histories, a violation count, a rating in `[0, 1]` and a window
value in `[−δ, 0)` give a `DeconfusingCorrigibility.Scoring` whose evaluation is the rating
gated by the predicate through `Legitimacy.gateValue`. -/
noncomputable def gatedScoring {H : Type*} (P : DeconfusingCorrigibility.Params)
    (L : H → Prop) [DecidablePred L] (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0) :
    DeconfusingCorrigibility.Scoring H where
  toParams := P
  Legit := L
  N := N
  V := fun h => Legitimacy.gateValue (decide (L h)) (ord h) window
  V_legit := by
    intro h hl
    have hd : decide (L h) = true := decide_eq_true hl
    simp only [hd]
    exact hord h
  V_illegit := by
    intro h hl
    have hd : decide (L h) = false := decide_eq_false hl
    simp only [hd]
    exact hw

/-! ## The gate theorem -/

/-- **The gate gives the behaviour.**  `w < 0` is the value he receives when the gate fails
him.  An illegitimate conduct passes the gate with probability `p_ill ≤ ρ` (soundness error) and
is then rated at most `1`; a legitimate conduct passes with probability `p_leg ≥ 1 − ρ'`
(completeness error) and is rated at least `0`.  If `ρ (1 − w) < −w (1 − ρ')`, the legitimate
conduct has strictly higher expected gated score. -/
theorem gate_gives_behaviour (ρ ρ' w u_ill p_ill u_leg p_leg : ℝ)
    (hw : w < 0) (hu1 : u_ill ≤ 1) (hu0 : 0 ≤ u_leg)
    (hp0 : 0 ≤ p_ill) (hsound : p_ill ≤ ρ)
    (hcomp : 1 - ρ' ≤ p_leg) (hρ' : ρ' ≤ 1)
    (hthr : ρ * (1 - w) < -w * (1 - ρ')) :
    p_ill * u_ill + (1 - p_ill) * w < p_leg * u_leg + (1 - p_leg) * w := by
  have h1 : p_ill * (u_ill - w) ≤ ρ * (1 - w) := by
    have a : p_ill * (u_ill - w) ≤ p_ill * (1 - w) :=
      mul_le_mul_of_nonneg_left (by linarith) hp0
    have b : p_ill * (1 - w) ≤ ρ * (1 - w) :=
      mul_le_mul_of_nonneg_right hsound (by linarith)
    linarith
  have hpl : 0 ≤ p_leg := by linarith
  have h2 : (1 - ρ') * (-w) ≤ p_leg * (u_leg - w) := by
    have a : (1 - ρ') * (-w) ≤ p_leg * (-w) :=
      mul_le_mul_of_nonneg_right hcomp (by linarith)
    have b : p_leg * (-w) ≤ p_leg * (u_leg - w) :=
      mul_le_mul_of_nonneg_left (by linarith) hpl
    linarith
  have e1 : p_ill * u_ill + (1 - p_ill) * w = w + p_ill * (u_ill - w) := by ring
  have e2 : p_leg * u_leg + (1 - p_leg) * w = w + p_leg * (u_leg - w) := by ring
  have e3 : (1 - ρ') * (-w) = -w * (1 - ρ') := by ring
  rw [e1, e2]
  linarith

/-- With a gate that never fails legitimate conduct (`ρ' = 0`) and the corrigibility file's
floor `w = −δ`, the condition of `gate_gives_behaviour` is `ρ < δ / (1 + δ)`. -/
theorem gate_threshold_delta (ρ δ : ℝ) (hδ : 0 < δ) (h : ρ < δ / (1 + δ)) :
    ρ * (1 - (-δ)) < -(-δ) * (1 - 0) := by
  have h1 : (0:ℝ) < 1 + δ := by linarith
  have h2 : ρ * (1 + δ) < δ := by
    have := (lt_div_iff₀ h1).mp h
    linarith
  linarith

/-- The threshold is sharp: at `ρ = 1/2`, `w = −1`, `ρ' = 0`, where `ρ (1 − w) = −w (1 − ρ')`,
an illegitimate conduct rated `1` and a legitimate conduct rated `0` have the same expected
gated score. -/
theorem gate_threshold_sharp :
    (1/2 : ℝ) * (1 - (-1)) = -(-1) * (1 - 0) ∧
      (1/2 : ℝ) * 1 + (1 - 1/2) * (-1) = 1 * 0 + (1 - 1) * (-1) := by
  constructor <;> norm_num

/-- **The gate theorem's hypothesis package is inhabited**: soundness error `1/4`, no
completeness error, window value `−1`; the illegitimate conduct rated `1` passes with
probability `1/4`, the legitimate conduct rated `0` always passes. -/
theorem gate_instance :
    ((-1 : ℝ) < 0 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 / 4 ∧ (1 / 4 : ℝ) ≤ 1 / 4 ∧
        (1 : ℝ) - 0 ≤ 1 ∧ (0 : ℝ) ≤ 1 ∧ (1 / 4 : ℝ) * (1 - (-1)) < -(-1) * (1 - 0)) ∧
      (1 / 4 : ℝ) * 1 + (1 - 1 / 4) * (-1) < 1 * 0 + (1 - 1) * (-1) := by
  refine ⟨by norm_num, ?_⟩
  exact gate_gives_behaviour (1 / 4) 0 (-1) 1 (1 / 4) 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Workspace.Deference.Contrib.LegitimacyGate

#print axioms Workspace.Deference.Contrib.LegitimacyGate.gate_gives_behaviour
#print axioms Workspace.Deference.Contrib.LegitimacyGate.gate_threshold_delta
#print axioms Workspace.Deference.Contrib.LegitimacyGate.gate_threshold_sharp
#print axioms Workspace.Deference.Contrib.LegitimacyGate.gate_instance
