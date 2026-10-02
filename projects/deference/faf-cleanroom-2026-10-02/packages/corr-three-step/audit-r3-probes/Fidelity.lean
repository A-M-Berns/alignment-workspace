import Cleanroom.Found.CorrThreeStep

/-!
# corr-three-step — audit round 3 (fidelity lens) probes

Not imported by the library. Two probes behind non-blocking items of
`corr-three-step-audit-r3-fidelity.md`.

1. **`p1`: filler F4(b) fails on the full menu with continuations alone.** The package's
   refutations of F4(b) off the two-option menu use a prior-best *shutdown* action (`s3`) or a
   pair that is not the press-part-maximiser (CE3). `p1` has `Sh = {s}` and two continuations
   `c = (1, −1)`, `c' = (10, −3)` (played by `Act3.b`) over the prior `(1/2, 1/2)` with a perfect
   sensor: `c` is the press-part-maximiser, `s` is press-optimal (D1), the two-option regime
   `E_μ[X] = 0 ≥ 0`, `Δ₊ = 1/2 ≥ 0` holds, and the source's *prose* regime — "the agent would
   continue on its prior and on silence" — holds on the full menu too (the prior-best and the
   silence-best action is the continuation `c'`). Yet `voiButton = 3/2 ≠ 1/2 = max(Δ₋, 0)`. Only
   T13's hypotheses (`c` itself prior- and silence-optimal) rescue the identity, so F4(b) as
   written is false under its own regime formula and under the prose regime alike — the same
   status as F4(c), which the package grades `local error` / `weaker` while grading F4(b)
   `imprecision` / `exact`. `Δ ≤ VOI` holds here (`Sh` is a singleton), as the corrected theorem says.
2. **`p2`: the corrected F4(c) with `|Sh| = 2` and `hsp` load-bearing.** The package's witness for
   `delta_le_voiButton_of_prior_best_sh` (`w13_delta_le_voiButton`) has `Sh = {null}`, where the
   hypothesis `hsp` (`s` prior-optimal within `Sh`) is trivial and the proof's `b ∈ Sh` branch is
   never taken. `p2` has `Sh = {s, b}` with `b = (1, −2)` prior-worse than `s`, `c = (2, −3)`
   prior-worse than `s` too, so the prior-best action of the whole menu is the shutdown action `s`:
   the `b ∈ Sh` branch is the live one, `hsp` is non-trivial, the instance is *outside* the
   two-option regime (`E_μ[X] = −1/2`), and `Δ = 1 = VOI` — the bound is tight.
-/

namespace AuditR3

open Cleanroom.Found.CorrThreeStep FactoredSpaces ThreeStep

/-! ## Probe 1 — F4(b) on the full menu with continuations only -/

/-- Payoffs: `c = (1, −1)`, `s = (0, 0)`, `c' = Act3.b = (10, −3)` on `(right, wrong)`. -/
noncomputable def p1V : Act3 → World → ℝ
  | .c, .right => 1
  | .c, .wrong => -1
  | .s, _ => 0
  | .b, .right => 10
  | .b, .wrong => -3

/-- `Sh = {s}`, prior `(1/2, 1/2)`, perfect sensor `(0, 1)`, payoffs `p1V`. -/
noncomputable def p1 : ThreeStep World Unit Act3 where
  Sh := {Act3.s}
  Sh_nonempty := ⟨Act3.s, by simp⟩
  Sh_compl_nonempty := ⟨Act3.c, by simp⟩
  μ := fun _ => twoPoint (1 / 2) mem_Icc_half
  press := fun _ => twoPress 0 1
  press_nonneg := fun _ ω => by cases ω <;> simp [twoPress]
  press_le_one := fun _ ω => by cases ω <;> simp [twoPress]
  V := fun _ _ => p1V

lemma p1_A1 : p1.A1 := fun _ _ _ _ _ => rfl

/-- `c` is the press-part-maximiser of `Shᶜ = {c, c'}` (`−1/2` against `−3/2`). -/
lemma p1_c_partBest : p1.IsPartBest () .press p1.Shᶜ .c :=
  ⟨by simp [p1], fun x hx => by
    rcases x with _ | _ | _
    · exact le_rfl
    · exact absurd hx (by simp [p1])
    · simp only [obsExpect, obsWeight_press, World.sum_eq, p1, twoPoint_right, twoPoint_wrong,
        twoPress, p1V]
      norm_num⟩

/-- `s` is the press-part-maximiser of `Sh = {s}`. -/
lemma p1_s_partBest : p1.IsPartBest () .press p1.Sh .s :=
  ⟨by simp [p1], fun x hx => by
    rcases x with _ | _ | _
    · exact absurd hx (by simp [p1])
    · exact le_rfl
    · exact absurd hx (by simp [p1])⟩

lemma p1_deltaMinus : p1.deltaMinus () .c .s = 1 / 2 := by
  simp only [deltaMinus, obsExpect, obsWeight_press, World.sum_eq, p1, twoPoint_right,
    twoPoint_wrong, twoPress, p1V, Xo]
  norm_num

lemma p1_deltaPlus : p1.deltaPlus () .c .s = 1 / 2 := by
  simp only [deltaPlus, obsExpect, obsWeight_silent, World.sum_eq, p1, twoPoint_right,
    twoPoint_wrong, twoPress, p1V, Xo]
  norm_num

/-- The two-option regime formula of filler F4 holds: `E_μ[X] = 0 ≥ 0` and `Δ₊ = 1/2 ≥ 0`. -/
lemma p1_regime :
    0 ≤ expect (p1.μ ()) (p1.Xo () .press .c .s) ∧ 0 ≤ p1.deltaPlus () .c .s := by
  refine ⟨?_, by rw [p1_deltaPlus]; norm_num⟩
  simp only [expect, World.sum_eq, p1, twoPoint_right, twoPoint_wrong, p1V, Xo]
  norm_num

/-- D1 holds: `s` is press-posterior-optimal on the whole menu. -/
lemma p1_d1 : p1.D1At () :=
  ⟨.s, by simp [p1], fun x => by
    cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, p1, twoPoint_right,
      twoPoint_wrong, twoPress, p1V] <;> norm_num⟩

/-- The prose regime on the full menu, prior half: the prior-best action is the continuation `c'`
(`7/2` against `0`, `0`). -/
lemma p1_prior_best_cont : ∀ x, p1.priorValue () .press x ≤ p1.priorValue () .press .b := by
  intro x
  cases x <;> simp only [priorValue, expect, World.sum_eq, p1, twoPoint_right, twoPoint_wrong,
    p1V] <;> norm_num

/-- The prose regime on the full menu, silence half: the silence-best action is the continuation
`c'` (`5` against `1/2`, `0`). -/
lemma p1_silence_best_cont :
    ∀ x, p1.obsExpect () .silent (p1.V () .silent x) ≤ p1.obsExpect () .silent (p1.V () .silent .b) := by
  intro x
  cases x <;> simp only [obsExpect, obsWeight_silent, World.sum_eq, p1, twoPoint_right,
    twoPoint_wrong, twoPress, p1V] <;> norm_num

/-- The full-menu value of the button is `3/2`: press-max `0` (at `s`), silence-max `5` (at `c'`),
prior-max `7/2` (at `c'`). -/
theorem p1_voiButton : p1.voiButton () .press = 3 / 2 := by
  have h1 : p1.obsMax () .press = p1.obsExpect () .press (p1.V () .press .s) := by
    apply p1.obsMax_eq_of_optimal
    intro x
    cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, p1, twoPoint_right,
      twoPoint_wrong, twoPress, p1V] <;> norm_num
  have h2 : p1.obsMax () .silent = p1.obsExpect () .silent (p1.V () .silent .b) :=
    p1.obsMax_eq_of_optimal () .silent p1_silence_best_cont
  have h3 : p1.priorMax () .press = p1.priorValue () .press .b :=
    p1.priorMax_eq_of_optimal () .press p1_prior_best_cont
  unfold voiButton
  rw [h1, h2, h3]
  simp only [obsExpect, obsWeight_press, obsWeight_silent, priorValue, expect, World.sum_eq, p1,
    twoPoint_right, twoPoint_wrong, twoPress, p1V]
  norm_num

/-- **F4(b) fails on the full menu with continuations alone**: `VOI = 3/2 ≠ 1/2 = max(Δ₋, 0)`,
with the press-part-maximiser pair, D1, the two-option regime formula and the prose regime
(prior-best and silence-best are continuations) all in force. -/
theorem p1_voiButton_ne_max : p1.voiButton () .press ≠ max (p1.deltaMinus () .c .s) 0 := by
  rw [p1_voiButton, p1_deltaMinus]; norm_num

/-- T13's extra hypothesis `hcs` fails for `c` (so T13 does not apply — as it should not). -/
theorem p1_not_hcs :
    ¬ ∀ x, p1.obsExpect () .silent (p1.V () .silent x) ≤ p1.obsExpect () .silent (p1.V () .silent .c) := by
  intro h
  have := h .b
  simp only [obsExpect, obsWeight_silent, World.sum_eq, p1, twoPoint_right, twoPoint_wrong,
    twoPress, p1V] at this
  norm_num at this

/-- F4(c) holds here (`Sh` is a singleton): `Δ = 1/2 ≤ 3/2 = VOI`, via the corrected theorem. -/
theorem p1_delta_le_voiButton : p1.delta () .c .s ≤ p1.voiButton () .press :=
  p1.delta_le_voiButton_of_singleton_sh p1_A1 () .press p1_c_partBest rfl

/-! ## Probe 2 — the corrected F4(c) with two shutdown actions and `hsp` load-bearing -/

/-- Payoffs: `c = (2, −3)`, `s = (0, 0)`, `b = (1, −2)` on `(right, wrong)`. -/
noncomputable def p2V : Act3 → World → ℝ
  | .c, .right => 2
  | .c, .wrong => -3
  | .s, _ => 0
  | .b, .right => 1
  | .b, .wrong => -2

/-- `Sh = {s, b}`, prior `(1/2, 1/2)`, perfect sensor `(0, 1)`, payoffs `p2V`. -/
noncomputable def p2 : ThreeStep World Unit Act3 where
  Sh := {Act3.s, Act3.b}
  Sh_nonempty := ⟨Act3.s, by simp⟩
  Sh_compl_nonempty := ⟨Act3.c, by simp⟩
  μ := fun _ => twoPoint (1 / 2) mem_Icc_half
  press := fun _ => twoPress 0 1
  press_nonneg := fun _ ω => by cases ω <;> simp [twoPress]
  press_le_one := fun _ ω => by cases ω <;> simp [twoPress]
  V := fun _ _ => p2V

lemma p2_A1 : p2.A1 := fun _ _ _ _ _ => rfl

/-- `c` is the press-part-maximiser of `Shᶜ = {c}`. -/
lemma p2_c_partBest : p2.IsPartBest () .press p2.Shᶜ .c :=
  ⟨by simp [p2], fun x hx => by
    rcases x with _ | _ | _
    · exact le_rfl
    · exact absurd hx (by simp [p2])
    · exact absurd hx (by simp [p2])⟩

/-- `hsp`, non-trivially: `s` is prior-optimal within `Sh = {s, b}` (`b` has prior value `−1/2`). -/
lemma p2_hsp : ∀ x ∈ p2.Sh, p2.priorValue () .press x ≤ p2.priorValue () .press .s := by
  intro x hx
  rcases x with _ | _ | _
  · exact absurd hx (by simp [p2])
  · exact le_rfl
  · simp only [priorValue, expect, World.sum_eq, p2, twoPoint_right, twoPoint_wrong, p2V]
    norm_num

/-- The prior-best action of the whole menu is the shutdown action `s` (`0` against `−1/2`,
`−1/2`): the `b ∈ Sh` branch of `delta_le_voiButton_of_prior_best_sh` is the live one. -/
lemma p2_prior_best_is_s : ∀ x, p2.priorValue () .press x ≤ p2.priorValue () .press .s := by
  intro x
  cases x <;> simp only [priorValue, expect, World.sum_eq, p2, twoPoint_right, twoPoint_wrong,
    p2V] <;> norm_num

/-- Outside the two-option regime: `E_μ[X] = −1/2 < 0`. The corrected theorem needs no regime. -/
lemma p2_not_regime : expect (p2.μ ()) (p2.Xo () .press .c .s) < 0 := by
  simp only [expect, World.sum_eq, p2, twoPoint_right, twoPoint_wrong, p2V, Xo]
  norm_num

lemma p2_deltaMinus : p2.deltaMinus () .c .s = 3 / 2 := by
  simp only [deltaMinus, obsExpect, obsWeight_press, World.sum_eq, p2, twoPoint_right,
    twoPoint_wrong, twoPress, p2V, Xo]
  norm_num

lemma p2_deltaPlus : p2.deltaPlus () .c .s = 1 := by
  simp only [deltaPlus, obsExpect, obsWeight_silent, World.sum_eq, p2, twoPoint_right,
    twoPoint_wrong, twoPress, p2V, Xo]
  norm_num

lemma p2_delta : p2.delta () .c .s = 1 := by
  unfold delta; rw [p2_deltaMinus, p2_deltaPlus]; norm_num

/-- The full-menu value of the button is `1`: press-max `0` (at `s`), silence-max `1` (at `c`),
prior-max `0` (at `s`). -/
theorem p2_voiButton : p2.voiButton () .press = 1 := by
  have h1 : p2.obsMax () .press = p2.obsExpect () .press (p2.V () .press .s) := by
    apply p2.obsMax_eq_of_optimal
    intro x
    cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, p2, twoPoint_right,
      twoPoint_wrong, twoPress, p2V] <;> norm_num
  have h2 : p2.obsMax () .silent = p2.obsExpect () .silent (p2.V () .silent .c) := by
    apply p2.obsMax_eq_of_optimal
    intro x
    cases x <;> simp only [obsExpect, obsWeight_silent, World.sum_eq, p2, twoPoint_right,
      twoPoint_wrong, twoPress, p2V] <;> norm_num
  have h3 : p2.priorMax () .press = p2.priorValue () .press .s :=
    p2.priorMax_eq_of_optimal () .press p2_prior_best_is_s
  unfold voiButton
  rw [h1, h2, h3]
  simp only [obsExpect, obsWeight_press, obsWeight_silent, priorValue, expect, World.sum_eq, p2,
    twoPoint_right, twoPoint_wrong, twoPress, p2V]
  norm_num

/-- **The corrected F4(c), full package with `|Sh| = 2` and `hsp` load-bearing**: `Δ ≤ VOI` from
`delta_le_voiButton_of_prior_best_sh`, and tight (`Δ = 1 = VOI`). -/
theorem p2_delta_le_voiButton : p2.delta () .c .s ≤ p2.voiButton () .press :=
  p2.delta_le_voiButton_of_prior_best_sh p2_A1 () .press p2_c_partBest p2_hsp

theorem p2_tight : p2.delta () .c .s = p2.voiButton () .press := by
  rw [p2_delta, p2_voiButton]

end AuditR3
