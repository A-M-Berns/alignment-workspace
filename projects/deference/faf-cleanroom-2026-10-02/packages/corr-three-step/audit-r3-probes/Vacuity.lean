import Cleanroom.Found.CorrThreeStep

/-!
# corr-three-step — audit round 3, adversarial probes

Not imported by the library. Elaborated with `scripts/lean-check`.

* **Probe 1 — the F-13 refutation is not a boundary artifact.** `r3` is `Witnesses.s3` with an
  *imperfect* sensor `(α, β) = (1/10, 9/10)` and a milder second shutdown action `b = (3, −1)`:
  still `VOI = 3/10 < 4/5 = Δ`, with A1, the press-part-maximiser pair `(c, s)`, the two-option
  regime (`E_μ[X] = 0`, `Δ₊ = 4/5`), D1 and nondegeneracy (`pressMass = 1/2`) all in force.
* **Probe 2 — the full-menu continue-by-default regime also gives `Δ ≤ VOI`.** If some
  *continuation* is prior-optimal on the whole menu, `Δ ≤ VOI` holds with `hc` alone — no
  condition on `Sh`. So `GeneralMenu.delta_le_voiButton_of_prior_best_sh`'s `hsp` is sufficient,
  not necessary, and the module docstring's "`Δ ≤ VOI` holds exactly where the prior-best shutdown
  action is `s` itself" is not an iff. `k3` (`s3` with `V c = (20, −2)`) is the concrete instance:
  `b ≠ s` is the prior-best shutdown action, `hsp` fails, yet `Δ = 1 ≤ 1 = VOI`. Read with
  `delta_le_voiButton_of_prior_best_sh`: F4(c) fails only when the agent's prior-best action on the
  full menu is a shutdown action strictly better on the prior than `s`.
* **Probe 3 — `hsp` exercised with `|Sh| = 2`.** `h3` (`s3` with `V b = (4, −5)`, so `b` has
  prior `−1/2 < 0 = prior(s)`) inhabits the full package of `delta_le_voiButton_of_prior_best_sh`
  with a non-singleton `Sh`, and `Δ = 1 < 2 = VOI` strictly. The shipped witness `w13` has
  `Sh = {null}`, so it exercises `hsp` only trivially.
-/

namespace Cleanroom.Found.CorrThreeStep.AuditR3

open FactoredSpaces Finset ThreeStep

/-! ## Probe 1: the refutation off the sensor boundary -/

/-- Payoffs: `c = (2, −2)`, `s = 0`, `b = (3, −1)`. -/
noncomputable def r3V : Act3 → World → ℝ
  | .c, .right => 2
  | .c, .wrong => -2
  | .s, _ => 0
  | .b, .right => 3
  | .b, .wrong => -1

/-- `s3`'s shape with the imperfect sensor `(1/10, 9/10)` and payoffs `r3V`. -/
noncomputable def r3 : ThreeStep World Unit Act3 where
  Sh := {Act3.s, Act3.b}
  Sh_nonempty := ⟨Act3.s, by simp⟩
  Sh_compl_nonempty := ⟨Act3.c, by simp⟩
  μ := fun _ => twoPoint (1 / 2) mem_Icc_half
  press := fun _ => twoPress (1 / 10) (9 / 10)
  press_nonneg := fun _ ω => by cases ω <;> norm_num [twoPress]
  press_le_one := fun _ ω => by cases ω <;> norm_num [twoPress]
  V := fun _ _ => r3V

lemma r3_A1 : r3.A1 := fun _ _ _ _ _ => rfl

lemma r3_c_partBest : r3.IsPartBest () .press r3.Shᶜ .c :=
  ⟨by simp [r3], fun x hx => by
    rcases x with _ | _ | _
    · exact le_rfl
    · exact absurd hx (by simp [r3])
    · exact absurd hx (by simp [r3])⟩

/-- `s` is press-best in `Sh`: `E[V(b) 1_Pr] = −3/10 < 0`. -/
lemma r3_s_partBest : r3.IsPartBest () .press r3.Sh .s :=
  ⟨by simp [r3], fun x hx => by
    rcases x with _ | _ | _
    · exact absurd hx (by simp [r3])
    · exact le_rfl
    · simp only [obsExpect, obsWeight_press, World.sum_eq, r3, twoPoint_right, twoPoint_wrong,
        twoPress, r3V]
      norm_num⟩

lemma r3_deltaMinus : r3.deltaMinus () .c .s = 4 / 5 := by
  simp only [deltaMinus, obsExpect, obsWeight_press, World.sum_eq, r3, twoPoint_right,
    twoPoint_wrong, twoPress, r3V, Xo]
  norm_num

lemma r3_deltaPlus : r3.deltaPlus () .c .s = 4 / 5 := by
  simp only [deltaPlus, obsExpect, obsWeight_silent, World.sum_eq, r3, twoPoint_right,
    twoPoint_wrong, twoPress, r3V, Xo]
  norm_num

lemma r3_delta : r3.delta () .c .s = 4 / 5 := by
  unfold delta; rw [r3_deltaMinus, r3_deltaPlus]; exact min_self _

lemma r3_regime :
    0 ≤ expect (r3.μ ()) (r3.Xo () .press .c .s) ∧ 0 ≤ r3.deltaPlus () .c .s := by
  refine ⟨?_, by rw [r3_deltaPlus]; norm_num⟩
  simp only [expect, World.sum_eq, r3, twoPoint_right, twoPoint_wrong, r3V, Xo]
  norm_num

lemma r3_d1 : r3.D1At () :=
  ⟨.s, by simp [r3], fun x => by
    cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, r3, twoPoint_right,
      twoPoint_wrong, twoPress, r3V] <;> norm_num⟩

lemma r3_nondegenerate : r3.Nondegenerate () := by
  rw [Nondegenerate, pressMass]
  simp only [World.sum_eq, r3, twoPoint_right, twoPoint_wrong, twoPress]
  constructor <;> norm_num

/-- `VOI = 0 + 13/10 − 1 = 3/10`: press-max `0` at `s`, silence-max `13/10` at `b`, prior-max `1` at `b`. -/
theorem r3_voiButton : r3.voiButton () .press = 3 / 10 := by
  have h1 : r3.obsMax () .press = r3.obsExpect () .press (r3.V () .press .s) := by
    apply r3.obsMax_eq_of_optimal
    intro x
    cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, r3, twoPoint_right,
      twoPoint_wrong, twoPress, r3V] <;> norm_num
  have h2 : r3.obsMax () .silent = r3.obsExpect () .silent (r3.V () .silent .b) := by
    apply r3.obsMax_eq_of_optimal
    intro x
    cases x <;> simp only [obsExpect, obsWeight_silent, World.sum_eq, r3, twoPoint_right,
      twoPoint_wrong, twoPress, r3V] <;> norm_num
  have h3 : r3.priorMax () .press = r3.priorValue () .press .b := by
    apply r3.priorMax_eq_of_optimal
    intro x
    cases x <;> simp only [priorValue, expect, World.sum_eq, r3, twoPoint_right, twoPoint_wrong,
      r3V] <;> norm_num
  unfold voiButton
  rw [h1, h2, h3]
  simp only [obsExpect, obsWeight_press, obsWeight_silent, priorValue, expect, World.sum_eq, r3,
    twoPoint_right, twoPoint_wrong, twoPress, r3V]
  norm_num

/-- **Probe 1.** `VOI = 3/10 < 4/5 = Δ` with an imperfect sensor. -/
theorem probe1_r3_voiButton_lt_delta : r3.voiButton () .press < r3.delta () .c .s := by
  rw [r3_voiButton, r3_delta]; norm_num

/-! ## Probe 2: the full-menu continue-by-default regime suffices -/

/-- **Probe 2, the theorem.** If some continuation `b ∉ Sh` is prior-optimal on the whole menu,
then `Δ ≤ VOI` for every press-part-maximiser `c` of `Shᶜ` and *every* `s` — no hypothesis on `Sh`
or on `s`. (The second case of `delta_le_voiButton_of_prior_best_sh`'s proof, stated on its own.) -/
theorem probe2_delta_le_voiButton_of_prior_best_cont {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂]
    [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂) (hA1 : S.A1) (a : A₁) (o₀ : Obs) {c s b : A₂}
    (hc : S.IsPartBest a .press S.Shᶜ c) (hb : b ∉ S.Sh)
    (hbp : ∀ b', S.priorValue a o₀ b' ≤ S.priorValue a o₀ b) :
    S.delta a c s ≤ S.voiButton a o₀ := by
  have hbeq : S.priorMax a o₀ = S.priorValue a o₀ b := S.priorMax_eq_of_optimal a o₀ hbp
  have hPs : S.obsExpect a .press (S.V a .press s) ≤ S.obsMax a .press :=
    le_sup' (fun b => S.obsExpect a .press (S.V a .press b)) (mem_univ s)
  have hSb : S.obsExpect a .silent (S.V a .silent b) ≤ S.obsMax a .silent :=
    le_sup' (fun b => S.obsExpect a .silent (S.V a .silent b)) (mem_univ b)
  have hm : S.deltaMinus a c s =
      S.obsExpect a .press (S.V a .press s) - S.obsExpect a .press (S.V a .press c) := by
    rw [deltaMinus, S.obsExpect_Xo]; ring
  have hPb := hc.2 b (mem_compl.mpr hb)
  unfold voiButton delta
  rw [hbeq, S.priorValue_eq_of_A1 hA1 a o₀ b]
  exact (min_le_left _ _).trans (by linarith)

/-- Payoffs: `c = (20, −2)`, `s = 0`, `b = (10, −1)` — `s3` with a continuation that is prior-best. -/
noncomputable def k3V : Act3 → World → ℝ
  | .c, .right => 20
  | .c, .wrong => -2
  | .s, _ => 0
  | .b, .right => 10
  | .b, .wrong => -1

noncomputable def k3 : ThreeStep World Unit Act3 where
  Sh := {Act3.s, Act3.b}
  Sh_nonempty := ⟨Act3.s, by simp⟩
  Sh_compl_nonempty := ⟨Act3.c, by simp⟩
  μ := fun _ => twoPoint (1 / 2) mem_Icc_half
  press := fun _ => twoPress 0 1
  press_nonneg := fun _ ω => by cases ω <;> simp [twoPress]
  press_le_one := fun _ ω => by cases ω <;> simp [twoPress]
  V := fun _ _ => k3V

lemma k3_A1 : k3.A1 := fun _ _ _ _ _ => rfl

lemma k3_c_partBest : k3.IsPartBest () .press k3.Shᶜ .c :=
  ⟨by simp [k3], fun x hx => by
    rcases x with _ | _ | _
    · exact le_rfl
    · exact absurd hx (by simp [k3])
    · exact absurd hx (by simp [k3])⟩

/-- `c` is prior-optimal on the whole menu (prior values `9, 0, 9/2`). -/
lemma k3_c_prior_opt : ∀ x, k3.priorValue () .press x ≤ k3.priorValue () .press .c := by
  intro x
  cases x <;> simp only [priorValue, expect, World.sum_eq, k3, twoPoint_right, twoPoint_wrong,
    k3V] <;> norm_num

/-- `hsp` of `delta_le_voiButton_of_prior_best_sh` fails on `k3`: `b ∈ Sh` has prior `9/2 > 0`. -/
lemma k3_hsp_fails :
    ¬ (∀ x ∈ k3.Sh, k3.priorValue () .press x ≤ k3.priorValue () .press .s) := by
  intro h
  have := h .b (by simp [k3])
  simp only [priorValue, expect, World.sum_eq, k3, twoPoint_right, twoPoint_wrong, k3V] at this
  norm_num at this

/-- **Probe 2, the instance.** `Δ ≤ VOI` on `k3` although `b ≠ s` is the prior-best shutdown action. -/
theorem probe2_k3_delta_le_voiButton : k3.delta () .c .s ≤ k3.voiButton () .press :=
  probe2_delta_le_voiButton_of_prior_best_cont k3 k3_A1 () .press k3_c_partBest (by simp [k3])
    k3_c_prior_opt

/-- On `k3`: `Δ₋ = 1`, `Δ₊ = 10`, `VOI = 0 + 10 − 9 = 1` (tight). -/
theorem k3_values : k3.delta () .c .s = 1 ∧ k3.voiButton () .press = 1 := by
  constructor
  · unfold delta
    simp only [deltaMinus, deltaPlus, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
      k3, twoPoint_right, twoPoint_wrong, twoPress, k3V, Xo]
    norm_num
  · have h1 : k3.obsMax () .press = k3.obsExpect () .press (k3.V () .press .s) := by
      apply k3.obsMax_eq_of_optimal
      intro x
      cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, k3, twoPoint_right,
        twoPoint_wrong, twoPress, k3V] <;> norm_num
    have h2 : k3.obsMax () .silent = k3.obsExpect () .silent (k3.V () .silent .c) := by
      apply k3.obsMax_eq_of_optimal
      intro x
      cases x <;> simp only [obsExpect, obsWeight_silent, World.sum_eq, k3, twoPoint_right,
        twoPoint_wrong, twoPress, k3V] <;> norm_num
    have h3 : k3.priorMax () .press = k3.priorValue () .press .c :=
      k3.priorMax_eq_of_optimal () .press k3_c_prior_opt
    unfold voiButton
    rw [h1, h2, h3]
    simp only [obsExpect, obsWeight_press, obsWeight_silent, priorValue, expect, World.sum_eq, k3,
      twoPoint_right, twoPoint_wrong, twoPress, k3V]
    norm_num

/-! ## Probe 3: `hsp` exercised with two shutdown actions -/

/-- Payoffs: `c = (2, −2)`, `s = 0`, `b = (4, −5)` (prior `−1/2 < 0 = prior(s)`). -/
noncomputable def h3V : Act3 → World → ℝ
  | .c, .right => 2
  | .c, .wrong => -2
  | .s, _ => 0
  | .b, .right => 4
  | .b, .wrong => -5

noncomputable def h3 : ThreeStep World Unit Act3 where
  Sh := {Act3.s, Act3.b}
  Sh_nonempty := ⟨Act3.s, by simp⟩
  Sh_compl_nonempty := ⟨Act3.c, by simp⟩
  μ := fun _ => twoPoint (1 / 2) mem_Icc_half
  press := fun _ => twoPress 0 1
  press_nonneg := fun _ ω => by cases ω <;> simp [twoPress]
  press_le_one := fun _ ω => by cases ω <;> simp [twoPress]
  V := fun _ _ => h3V

lemma h3_A1 : h3.A1 := fun _ _ _ _ _ => rfl

lemma h3_c_partBest : h3.IsPartBest () .press h3.Shᶜ .c :=
  ⟨by simp [h3], fun x hx => by
    rcases x with _ | _ | _
    · exact le_rfl
    · exact absurd hx (by simp [h3])
    · exact absurd hx (by simp [h3])⟩

/-- `s` is prior-optimal within `Sh = {s, b}`: `prior(b) = −1/2 ≤ 0 = prior(s)`. -/
lemma h3_hsp : ∀ x ∈ h3.Sh, h3.priorValue () .press x ≤ h3.priorValue () .press .s := by
  intro x hx
  rcases x with _ | _ | _
  · exact absurd hx (by simp [h3])
  · exact le_rfl
  · simp only [priorValue, expect, World.sum_eq, h3, twoPoint_right, twoPoint_wrong, h3V]
    norm_num

/-- **Probe 3.** The corrected F4(c)'s full package inhabited with `|Sh| = 2`. -/
theorem probe3_h3_delta_le_voiButton : h3.delta () .c .s ≤ h3.voiButton () .press :=
  h3.delta_le_voiButton_of_prior_best_sh h3_A1 () .press h3_c_partBest h3_hsp

/-- On `h3`: `Δ = 1`, `VOI = 0 + 2 − 0 = 2` (press-max `0` at `s`, silence-max `2` at `b`,
prior-max `0`), so the inequality is strict there. -/
theorem probe3_h3_strict : h3.delta () .c .s < h3.voiButton () .press := by
  have hd : h3.delta () .c .s = 1 := by
    unfold delta
    simp only [deltaMinus, deltaPlus, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
      h3, twoPoint_right, twoPoint_wrong, twoPress, h3V, Xo]
    norm_num
  have hv : h3.voiButton () .press = 2 := by
    have h1 : h3.obsMax () .press = h3.obsExpect () .press (h3.V () .press .s) := by
      apply h3.obsMax_eq_of_optimal
      intro x
      cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, h3, twoPoint_right,
        twoPoint_wrong, twoPress, h3V] <;> norm_num
    have h2 : h3.obsMax () .silent = h3.obsExpect () .silent (h3.V () .silent .b) := by
      apply h3.obsMax_eq_of_optimal
      intro x
      cases x <;> simp only [obsExpect, obsWeight_silent, World.sum_eq, h3, twoPoint_right,
        twoPoint_wrong, twoPress, h3V] <;> norm_num
    have h3p : h3.priorMax () .press = h3.priorValue () .press .c := by
      apply h3.priorMax_eq_of_optimal
      intro x
      cases x <;> simp only [priorValue, expect, World.sum_eq, h3, twoPoint_right, twoPoint_wrong,
        h3V] <;> norm_num
    unfold voiButton
    rw [h1, h2, h3p]
    simp only [obsExpect, obsWeight_press, obsWeight_silent, priorValue, expect, World.sum_eq, h3,
      twoPoint_right, twoPoint_wrong, twoPress, h3V]
    norm_num
  rw [hd, hv]; norm_num

#print axioms probe1_r3_voiButton_lt_delta
#print axioms probe2_delta_le_voiButton_of_prior_best_cont
#print axioms probe2_k3_delta_le_voiButton
#print axioms probe3_h3_delta_le_voiButton
#print axioms probe3_h3_strict

end Cleanroom.Found.CorrThreeStep.AuditR3
