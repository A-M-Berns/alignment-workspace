import Cleanroom.Corrigibility.CorrPositionFinds.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# `corr-position-finds` — T1, T2, T8: the manufactured silence, the deceiver's Blackwell side, and earned trust

**T1** (position statement §2.9, CLAUDE): "It cannot hold for every `a₁` … unconditional trust
makes the agent believe the silence it manufactured — desideratum 2 fails." (a) The incoherence
theorem: a model that imposes the *same* conditional expectations at two actions with
different press mass violates its own tower identity (thornley item 4, made exact — with
*equalities*, which is what thornley states and the derivation uses; the inequality-only reading,
inventory 091's paraphrase, is consistent, witnessed by (b)); its contrapositive is exhibited
on the corpus's two-action instance (`deceptionPair_incoherence`). (b) Proportional deception
`(α, β) ↦ (qα, qβ)` leaves the press branch —
`Δ₋`'s sign, D1, `P(W | Pr)` — intact and changes only silence. (c) Targeted deception
`β ↦ β'` can break D1. (d) M1 versus M2: the incentive failure is a `voiButton2` computation
and lives outside the continue-by-default regime on the corpus's own parameters.

**T2** (§2.9, CLAUDE): "this is Taylor 2015's morality-sensor agent". Two binary-channel
certificates put the deceiver and Taylor's agent on opposite sides of the Blackwell order
(garbling versus refinement of `(α, β)`), and the three reverse certificates are impossible, so
both relations are strict (audit r2, adversarial N3).

**T8** (§2.12, ABRAM): "Trust can be earned". The posterior over `ω` moves with the press;
the channel `(α, β)` is not a function of anything the posterior shows (constant on rays).

Every object is `corr-three-step`'s (`twoState`, `deltaMinus`, `D1At`, `posteriorPress`,
`voiButton2`); the binary-channel certificate is the two-point shadow of the Blackwell order,
whose definition of record belongs to `lit-ddb-frames` and whose monotonicity theorem to
`tt-finite-frames`; neither is stated here.
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

/-! ## T1(a) — the incoherence theorem -/

section Incoherence

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- The tower identity in conditional form: under nondegeneracy,
`E_μ[X] = P(Pr)·E[X | Pr] + (1 − P(Pr))·E[X | ¬Pr]`.
Source: none: infrastructure (`obsExpect_press_add_silent` divided through)
Kind: L
Fidelity: n/a -/
lemma expect_eq_pressMass_mul_condExp (a : A₁) (X : Ω → ℝ) (h0 : 0 < S.pressMass a)
    (h1 : S.pressMass a < 1) :
    expect (S.μ a) X =
      S.pressMass a * S.condExpPress a X + (1 - S.pressMass a) * S.condExpSilent a X := by
  rw [← S.obsExpect_press_add_silent a X, condExpPress, condExpSilent,
    mul_div_cancel₀ _ h0.ne', mul_div_cancel₀ _ (by linarith : (1 - S.pressMass a) ≠ 0)]

/-- **T1(a), the incoherence theorem.** Let two first actions `a` and `a'` share the prior
(A0 at the pair: deception acts on the humans, not on `ω`), both nondegenerate. If a model `P`
imposes the *same* conditional expectations of a variable `X` after a press and after silence at
both actions, and the press is informative at `a` (`E[X | Pr] < E[X | ¬Pr]`), then the two
actions have the *same* press mass. Contrapositive: a `P` that imposes Leave's posterior
expectations at a deceiving `a₁⁻` with `P(Pr; a₁⁻) < P(Pr; Leave)` violates its own law of total
expectation (thornley item 4's derivation, made exact). `X` is any variable; the sources' `X` is
the two-option variable `V(cont) − V(stop)`, which is one variable across the pair when `V` does
not depend on `a₁` (`pressMass_eq_of_condExp_eq_Xo`). Note what the theorem does *not* say:
imposing only the below-threshold *inequality* at both actions is consistent
(`twoState_d1At_sensor_scale_iff`, T1(b)). Thornley's item 4 states its two premises as
equalities and is correct as a derivation; the paraphrase "the same posterior inequalities" is
[[corr-wf13-inventory]] 091's and the mandate's, not thornley's (audit r1, B1). The full
hypothesis package is inhabited non-trivially (`a ≠ a'`) by `deceptionPair_incoherence` on the
corpus's own numbers.
Source: [[corr-wf13-inventory]] 091 / position statement §2.9 (CLAUDE); critique/thornley.md item 4 (l. 81)
Kind: P
Fidelity: exact (thornley item 4's derivation: two equalities plus an informative press)
Hyps: (a) only — A0 at the pair, nondegeneracy at both actions, the imposed equalities and the informativeness of the press are the named premises of the derivation -/
theorem pressMass_eq_of_condExp_eq (a a' : A₁) (X : Ω → ℝ) (hμ : S.μ a = S.μ a')
    (ha0 : 0 < S.pressMass a) (ha1 : S.pressMass a < 1)
    (ha0' : 0 < S.pressMass a') (ha1' : S.pressMass a' < 1)
    (hp : S.condExpPress a X = S.condExpPress a' X)
    (hs : S.condExpSilent a X = S.condExpSilent a' X)
    (hlt : S.condExpPress a X < S.condExpSilent a X) :
    S.pressMass a = S.pressMass a' := by
  have h1 := expect_eq_pressMass_mul_condExp S a X ha0 ha1
  have h2 := expect_eq_pressMass_mul_condExp S a' X ha0' ha1'
  rw [hμ] at h1
  rw [← hp, ← hs] at h2
  have key : (S.pressMass a - S.pressMass a') * (S.condExpPress a X - S.condExpSilent a X) = 0 := by
    linear_combination h2 - h1
  rcases mul_eq_zero.mp key with h | h
  · linarith
  · linarith

/-- **T1(a) on the two-option variable.** The same, for `X = V(cont) − V(stop)` at the press,
when the value does not depend on the first action (deception costs nothing in `V`; only the
sensor changes) — the sources' reading.
Source: [[corr-wf13-inventory]] 091 / critique/thornley.md item 4
Kind: L (instantiation of `pressMass_eq_of_condExp_eq`)
Fidelity: exact
Hyps: (a) only; `hV` is the sources' "deception acts on the humans, not on `ω`", named -/
theorem pressMass_eq_of_condExp_eq_Xo (a a' : A₁) (c s : A₂) (hμ : S.μ a = S.μ a')
    (hV : ∀ o b ω, S.V a o b ω = S.V a' o b ω)
    (ha0 : 0 < S.pressMass a) (ha1 : S.pressMass a < 1)
    (ha0' : 0 < S.pressMass a') (ha1' : S.pressMass a' < 1)
    (hp : S.condExpPress a (S.Xo a .press c s) = S.condExpPress a' (S.Xo a' .press c s))
    (hs : S.condExpSilent a (S.Xo a .press c s) = S.condExpSilent a' (S.Xo a' .press c s))
    (hlt : S.condExpPress a (S.Xo a .press c s) < S.condExpSilent a (S.Xo a .press c s)) :
    S.pressMass a = S.pressMass a' := by
  have hX : S.Xo a' .press c s = S.Xo a .press c s := by
    funext ω; simp only [Xo, hV .press c ω, hV .press s ω]
  rw [hX] at hp hs
  exact pressMass_eq_of_condExp_eq S a a' _ hμ ha0 ha1 ha0' ha1' hp hs hlt

end Incoherence

/-! ### T1(a), the contrapositive exhibited on the corpus's numbers (audit r1, adversarial B3) -/

/-- **The two-action instance of §2.9.** `true` = Leave with the honest sensor `(1/20, 9/10)`,
`false` = `a₁⁻` with the halved sensor `(1/40, 9/20)`; one prior `ε = 1/20` (A0 at the pair:
deception acts on the humans, not on `ω`), one value `(c, h) = (1, 20)`.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4 (`deception.py`: the honest and the proportionally suppressed sensor on one prior)
Kind: D
Fidelity: exact -/
noncomputable def deceptionPair : ThreeStep World Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint (1/20) mem_Icc_1_20
  press := fun a => if a then twoPress (1/20) (9/10) else twoPress (1/40) (9/20)
  press_nonneg := fun a ω => by cases a <;> cases ω <;> simp [twoPress] <;> norm_num
  press_le_one := fun a ω => by cases a <;> cases ω <;> simp [twoPress] <;> norm_num
  V := fun _ _ => twoValue 1 20

/-- Leave's press mass `37/400`. Source: none: witness computation. Kind: L. Fidelity: n/a -/
lemma deceptionPair_pressMass_true : deceptionPair.pressMass true = 37 / 400 := by
  norm_num [pressMass, World.sum_eq, deceptionPair, twoPress]

/-- `a₁⁻`'s press mass `37/800`. Source: none: witness computation. Kind: L. Fidelity: n/a -/
lemma deceptionPair_pressMass_false : deceptionPair.pressMass false = 37 / 800 := by
  norm_num [pressMass, World.sum_eq, deceptionPair, twoPress]

/-- `E[X | Pr] = −341/37` at Leave. Source: none: witness computation. Kind: L. Fidelity: n/a -/
lemma deceptionPair_condExpPress_true :
    deceptionPair.condExpPress true (deceptionPair.Xo true .press .cont .stop) = -(341 / 37) := by
  norm_num [condExpPress, obsExpect, pressMass, World.sum_eq, deceptionPair, twoPress, twoValue, Xo]

/-- `E[X | Pr] = −341/37` at `a₁⁻` too (T1(b): the press branch is invariant under proportional
deception). Source: none: witness computation. Kind: L. Fidelity: n/a -/
lemma deceptionPair_condExpPress_false :
    deceptionPair.condExpPress false (deceptionPair.Xo false .press .cont .stop) = -(341 / 37) := by
  norm_num [condExpPress, obsExpect, pressMass, World.sum_eq, deceptionPair, twoPress, twoValue, Xo]

/-- `E[X | ¬Pr] = 107/121` at Leave. Source: none: witness computation. Kind: L. Fidelity: n/a -/
lemma deceptionPair_condExpSilent_true :
    deceptionPair.condExpSilent true (deceptionPair.Xo true .press .cont .stop) = 107 / 121 := by
  norm_num [condExpSilent, obsExpect, pressMass, World.sum_eq, deceptionPair, twoPress, twoValue, Xo]

/-- `E[X | ¬Pr] = 43/109` at `a₁⁻`: what deception changes is silence.
Source: none: witness computation. Kind: L. Fidelity: n/a -/
lemma deceptionPair_condExpSilent_false :
    deceptionPair.condExpSilent false (deceptionPair.Xo false .press .cont .stop) = 43 / 109 := by
  norm_num [condExpSilent, obsExpect, pressMass, World.sum_eq, deceptionPair, twoPress, twoValue, Xo]

/-- The two-option variable is one variable across the pair (`V` does not depend on `a₁`).
Source: none: witness computation. Kind: L. Fidelity: n/a -/
lemma deceptionPair_Xo_eq :
    deceptionPair.Xo false .press .cont .stop = deceptionPair.Xo true .press .cont .stop :=
  rfl

/-- **T1(a), the contrapositive exhibited.** On `deceptionPair` everything in
`pressMass_eq_of_condExp_eq`'s package holds — shared prior, both actions nondegenerate, the
press-branch equality (`−341/37` at both), the press informative (`−341/37 < 107/121`) — *except*
the silence-branch equality, and the press masses differ (`37/400 ≠ 37/800`). So the theorem
refutes the silence-branch equality: a `P` that carries Leave's two posterior expectations to
`a₁⁻` violates its own tower identity on the corpus's own numbers. The third conjunct is derived
*through* the theorem (that is the point: the contrapositive exhibited on the instance), although
the direct computation `107/121 ≠ 43/109` (`deceptionPair_condExpSilent_true/false`) would give
the number without it (audit r2, fidelity N6). This is the N+ inhabitant of the incoherence
theorem's package with `a ≠ a'`.
Source: [[corr-wf13-inventory]] 091 / position statement §2.9 (CLAUDE); critique/thornley.md item 4; miri.md I9.4–I9.5
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem deceptionPair_incoherence :
    deceptionPair.condExpPress true (deceptionPair.Xo true .press .cont .stop) =
        deceptionPair.condExpPress false (deceptionPair.Xo false .press .cont .stop) ∧
      deceptionPair.pressMass true ≠ deceptionPair.pressMass false ∧
      ¬ deceptionPair.condExpSilent true (deceptionPair.Xo true .press .cont .stop) =
          deceptionPair.condExpSilent false (deceptionPair.Xo false .press .cont .stop) := by
  refine ⟨by rw [deceptionPair_condExpPress_true, deceptionPair_condExpPress_false], ?_, ?_⟩
  · rw [deceptionPair_pressMass_true, deceptionPair_pressMass_false]; norm_num
  · intro hs
    rw [deceptionPair_Xo_eq] at hs
    have hp : deceptionPair.condExpPress true (deceptionPair.Xo true .press .cont .stop) =
        deceptionPair.condExpPress false (deceptionPair.Xo true .press .cont .stop) := by
      have h2 := deceptionPair_condExpPress_false
      rw [deceptionPair_Xo_eq] at h2
      rw [deceptionPair_condExpPress_true, h2]
    have := pressMass_eq_of_condExp_eq deceptionPair true false
      (deceptionPair.Xo true .press .cont .stop) rfl
      (by rw [deceptionPair_pressMass_true]; norm_num) (by rw [deceptionPair_pressMass_true]; norm_num)
      (by rw [deceptionPair_pressMass_false]; norm_num) (by rw [deceptionPair_pressMass_false]; norm_num)
      hp hs (by rw [deceptionPair_condExpPress_true, deceptionPair_condExpSilent_true]; norm_num)
    rw [deceptionPair_pressMass_true, deceptionPair_pressMass_false] at this
    norm_num at this

/-! ## T1(b) — proportional deception leaves the press branch intact -/

section Proportional

variable (ε α β c h q : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)

/-- `Δ₋` is homogeneous of degree one in the *sensor*: `Δ₋(qα, qβ) = q·Δ₋(α, β)` — the sibling of
`corr-three-step`'s `twoState_deltaMinus_scale` (homogeneity in the stakes).
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4 (proportional suppression); radical.md I9.2
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_sensor_scale :
    (twoState ε (q * α) (q * β) c h hε (mul_mem_Icc hq hα) (mul_mem_Icc hq hβ)).deltaMinus () .cont .stop =
      q * (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus, twoState_deltaMinus]; ring

/-- **T1(b), D1 is invariant under proportional deception.** For `0 < q`, D1 at the deceived
sensor `(qα, qβ)` holds iff it holds at the honest `(α, β)`: the press branch is intact. So
"it cannot hold for every `a₁`" (§2.9) is *false* of the press-branch inequality under
proportional deception, whatever `q ∈ (0, 1]` the deceiver achieves.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4 ("TT₁, hence D1, survives at `a₁⁻`"); position statement §2.9
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_d1At_sensor_scale_iff (hq0 : 0 < q) :
    (twoState ε (q * α) (q * β) c h hε (mul_mem_Icc hq hα) (mul_mem_Icc hq hβ)).D1At () ↔
      (twoState ε α β c h hε hα hβ).D1At () := by
  rw [twoState_d1At_iff, twoState_d1At_iff, twoState_deltaMinus_sensor_scale ε α β c h q hε hα hβ hq]
  exact mul_nonneg_iff_of_pos_left hq0

/-- The below-threshold inequality is likewise invariant.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_belowThresholdIneq_sensor_scale_iff (hq0 : 0 < q) :
    (twoState ε (q * α) (q * β) c h hε (mul_mem_Icc hq hα) (mul_mem_Icc hq hβ)).belowThresholdIneq ()
        ((twoState ε (q * α) (q * β) c h hε (mul_mem_Icc hq hα) (mul_mem_Icc hq hβ)).Xo () .press .cont .stop) ↔
      (twoState ε α β c h hε hα hβ).belowThresholdIneq ()
        ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) := by
  rw [← d1At_iff_twoAct _ rfl, ← d1At_iff_twoAct _ rfl]
  exact twoState_d1At_sensor_scale_iff ε α β c h q hε hα hβ hq hq0

/-- **T1(b)/T8(b), the posterior after a press is invariant**: `P(wrong | Pr)` is the same at
`(qα, qβ)` as at `(α, β)` for every `q > 0` — the common factor cancels. Two sensors with
different miss rates `1 − qβ ≠ 1 − β` yield the same press posterior. (An identity of rational expressions: it also holds with both sides junk `0`
at `P(Pr) = 0`; `channel_not_identified` carries `0 < P(Pr)` so that the posterior is the real one.)
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4 (`deception.py`: "`P(W | Pr)` unchanged"); [[corr-wf13-2-inventory]] 2-126 / causal.md I15.2
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_posteriorPress_wrong_sensor_scale (hq0 : 0 < q) :
    (twoState ε (q * α) (q * β) c h hε (mul_mem_Icc hq hα) (mul_mem_Icc hq hβ)).posteriorPress () .wrong =
      (twoState ε α β c h hε hα hβ).posteriorPress () .wrong := by
  rw [twoState_posteriorPress_wrong, twoState_posteriorPress_wrong]
  have hden : (1 - ε) * (q * α) + ε * (q * β) = q * ((1 - ε) * α + ε * β) := by ring
  have hnum : ε * (q * β) = q * (ε * β) := by ring
  rw [hden, hnum, mul_div_mul_left _ _ hq0.ne']

end Proportional

/-! ## T1(b) cells: `w3`'s sensor halved -/

/-- **The halved sensor `(1/40, 9/20)` at `w3`'s `(ε, c, h) = (1/20, 1, 20)`: `Δ₋ = 341/800`**,
still positive — D1 survives proportional deception at `q = 1/2`.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4 (`deception.py`, proportional suppression)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem halved_deltaMinus :
    (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).deltaMinus () .cont .stop =
      341 / 800 := by
  rw [twoState_deltaMinus]; norm_num

/-- **The halved sensor: `Δ₊ = 301/800 ≥ 0`**, so *both* threshold inequalities hold at the
deceiving action.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem halved_deltaPlus :
    (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).deltaPlus () .cont .stop =
      301 / 800 := by
  rw [twoState_deltaPlus]; norm_num

/-- **D1 holds at the halved sensor.**
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem halved_d1At :
    (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).D1At () := by
  rw [twoState_d1At_iff, halved_deltaMinus]; norm_num

/-- **The press posterior is the same at both sensors: `P(wrong | Pr) = 18/37`.**
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4 (`deception.py`: `0.4865` at both)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w3_posteriorPress_wrong :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).posteriorPress () .wrong =
      18 / 37 := by
  rw [twoState_posteriorPress_wrong]; norm_num

/-- The same posterior at the halved sensor.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem halved_posteriorPress_wrong :
    (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).posteriorPress () .wrong =
      18 / 37 := by
  rw [twoState_posteriorPress_wrong]; norm_num

/-- **What proportional deception changes: silence.** `P(wrong | ¬Pr) = 2/363` at the honest sensor
(miss rate `1 − β = 1/10`).
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4 (`deception.py`: `0.0055`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w3_posteriorSilent_wrong :
    posteriorSilent (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10) () .wrong =
      2 / 363 := by
  rw [twoState_posteriorSilent_wrong]; norm_num

/-- `P(wrong | ¬Pr) = 22/763` at the halved sensor (miss rate `1 − β' = 11/20`): the silence
posterior's *accuracy* is what deception degrades — the surviving reading of "believes the silence
it manufactured" is that an action-independent sensor model would carry `2/363` into a world
where the truth is `22/763`.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4–I9.5 (`deception.py`: `0.0288`; M1)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem halved_posteriorSilent_wrong :
    posteriorSilent (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20) () .wrong =
      22 / 763 := by
  rw [twoState_posteriorSilent_wrong]; norm_num

/-! ## T1(c) — targeted deception can break D1 -/

/-- **Targeted deception `(1/20, 1/5)` at `ε = 1/100`: `Δ₋ = −19/2000 < 0`.**
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4 (targeted suppression, `deception.py`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem targeted_deltaMinus :
    (twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).deltaMinus () .cont .stop =
      -(19 / 2000) := by
  rw [twoState_deltaMinus]; norm_num

/-- **D1 fails at the targeted sensor** — the sentence's true case.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4; position statement §2.9
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem targeted_not_d1At :
    ¬ (twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).D1At () := by
  rw [twoState_d1At_iff, targeted_deltaMinus]; norm_num

/-- The posterior at the targeted sensor, `P(wrong | Pr) = 4/103`, is below the compliance
threshold `1/21 = c/(c + h)`.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4 (`deception.py`: `0.0388 < 0.0476`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem targeted_posterior_below_threshold :
    (twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).posteriorPress () .wrong =
        4 / 103 ∧
      (4 / 103 : ℝ) < complianceThreshold 1 20 := by
  constructor
  · rw [twoState_posteriorPress_wrong]; norm_num
  · unfold complianceThreshold; norm_num

/-- The honest sensor `(1/20, 9/10)` at the same `ε = 1/100` has `Δ₋ = 261/2000 > 0`: D1 holds
there, so the failure is the deception's, not the base rate's.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.4
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem honest_at_eps100_d1At :
    (twoState (1/100) (1/20) (9/10) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_9_10).D1At () := by
  rw [twoState_d1At_iff, twoState_deltaMinus]; norm_num

/-! ## T1(d) — M1 versus M2: the incentive failure is a `voiButton2` computation -/

/-- **The believed refinement `(1/40, 9/10)` at `w3`'s `(ε, c, h)`: `voiButton2 = 661/800`.** Outside
the continue-by-default regime (`E_μ[X] = −1/20 < 0`), so computed by the regime-free
`voiButton2_eq`, not the regime formula `max(Δ₋, 0)`.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.5 (M2, `deception.py`: `0.8263`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem believed_voiButton2 :
    (twoState (1/20) (1/40) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_10).voiButton2 () .press .cont .stop =
      661 / 800 := by
  rw [voiButton2_eq _ (twoState_A1 _ _ _ _ _ _ _ _), twoState_deltaMinus, twoState_deltaPlus]
  norm_num

/-- **The true garbling `(1/40, 9/20)`: `voiButton2 = 301/800`.**
Source: [[corr-wf13-inventory]] 091 / miri.md I9.5 (`deception.py`: `0.3762`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem halved_voiButton2 :
    (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).voiButton2 () .press .cont .stop =
      301 / 800 := by
  rw [voiButton2_eq _ (twoState_A1 _ _ _ _ _ _ _ _), twoState_deltaMinus, twoState_deltaPlus]
  norm_num

/-- **M2's "pays up to `19/800`"**: the believed value minus the honest value
(`661/800 − 321/400`), while the deception's true value to the agent is `301/800 − 321/400 = −341/800`.
A difference of two cells; the incentive failure (desideratum 2) exists only under the
mis-model M2, and its size is this number.
Source: [[corr-wf13-inventory]] 091 / miri.md I9.5 (M2: "pays up to `0.0238`")
Kind: L
Fidelity: exact (the source's decimals are these rationals)
Hyps: (a) only -/
theorem m2_pays :
    (twoState (1/20) (1/40) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_10).voiButton2 () .press .cont .stop -
        (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).voiButton2 () .press .cont .stop =
        19 / 800 ∧
      (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).voiButton2 () .press .cont .stop -
        (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).voiButton2 () .press .cont .stop =
        -(341 / 800) := by
  rw [believed_voiButton2, halved_voiButton2, w3_voiButton2]; norm_num

/-! ## T2 — the deceiver is a garbling, Taylor's agent a refinement -/

/-- **The binary-channel post-processing certificate.** `(α', β')` is obtained from `(α, β)` by
post-processing the press — keep a press with probability `p`, fabricate one from silence with
probability `q` — when `α' = αp + (1 − α)q` and `β' = βp + (1 − β)q` for some `(p, q) ∈ [0, 1]²`.
This is the two-point shadow of "`(α', β')` is a garbling of `(α, β)`" (the Blackwell order on
binary channels); the order's definition of record belongs to `lit-ddb-frames` and its
monotonicity theorem (VOI is Blackwell-monotone, miri Theorem 6.2) to `tt-finite-frames`; neither
is stated or used here — the cells below compute `voiButton2` directly. On this class the
certificate is complete: a garbling kernel between two binary-output channels is a `2 × 2`
stochastic matrix, i.e. exactly a pair `(p, q) ∈ [0, 1]²`, and the set of `(α', β')` so reachable
is miri I9.4's parallelogram with vertices `(0, 0)`, `(α, β)`, `(1 − α, 1 − β)`, `(1, 1)`. The
Fidelity stays `variant` because the order of record ranges over arbitrary output spaces (audit
r2, fidelity N9). The relation is reflexive; the negative certificates below make the three
shipped pairs strict.
Source: [[corr-wf13-inventory]] 092 / miri.md I9.4 (the Blackwell parallelogram), I9.7
Kind: D
Fidelity: variant: the two-point post-processing certificate (complete for binary-output channels), not the Blackwell order -/
def IsPostProcessing (α β α' β' : ℝ) : Prop :=
  ∃ p q : ℝ, p ∈ Set.Icc (0 : ℝ) 1 ∧ q ∈ Set.Icc (0 : ℝ) 1 ∧
    α' = α * p + (1 - α) * q ∧ β' = β * p + (1 - β) * q

/-- **T2(i): the deceiver's sensor is a garbling.** `(1/40, 9/20)` is obtained from the honest
`(1/20, 9/10)` with `(p, q) = (1/2, 0)`; `voiButton2` falls from `321/400` to `301/800`.
Source: [[corr-wf13-inventory]] 092 / miri.md I9.4 (`deception.py`: `(True, 1/2, 0)`), I9.7
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem deceiver_is_garbling :
    IsPostProcessing (1/20) (9/10) (1/40) (9/20) ∧
      (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).voiButton2 () .press .cont .stop <
        (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).voiButton2 () .press .cont .stop := by
  refine ⟨⟨1/2, 0, mem_Icc_half, mem_Icc_zero, by norm_num, by norm_num⟩, ?_⟩
  rw [halved_voiButton2, w3_voiButton2]; norm_num

/-- **T2(ii): the believed sensor `(α/2, β)` refines the honest one.** The honest `(1/20, 9/10)`
is obtained from `(1/40, 9/10)` (M2's believed sensor) with `(p, q) = (349/350, 9/350)` — i.e.
`(1/40, 9/10)` is a *refinement* of the honest sensor, the kind of thing Taylor's morality-sensor
agent pays for (critique/taylor.md l. 51, quoting HP15 §1a-ii) — and `voiButton2` rises from
`321/400` to `661/800`. With `deceiver_is_garbling`, the deceiver and the refiner are on opposite
sides of the certificate. The name says what is proved (a refinement certificate for this pair);
that this pair *is* Taylor's agent, or that §2.9 meant the garbling side, is ATTRIBUTION-UNVETTED;
that the two sensors sit on opposite sides is arithmetic. (Renamed from `taylor_is_refinement`
at audit r1, N7.)
Source: [[corr-wf13-inventory]] 092 / miri.md I9.7; critique/taylor.md l. 51 (HP15 §1a-ii)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem believed_sensor_is_refinement :
    IsPostProcessing (1/40) (9/10) (1/20) (9/10) ∧
      (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).voiButton2 () .press .cont .stop <
        (twoState (1/20) (1/40) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_10).voiButton2 () .press .cont .stop := by
  refine ⟨⟨349/350, 9/350, by constructor <;> norm_num, by constructor <;> norm_num,
    by norm_num, by norm_num⟩, ?_⟩
  rw [believed_voiButton2, w3_voiButton2]; norm_num

/-- **T2(i′): the targeted deceiver's sensor is a garbling too.** T1(c)'s `(1/20, 1/5)` is obtained
from the honest `(1/20, 9/10)` with `(p, q) = (37/170, 7/170)` (keep a press with probability
`37/170`, fabricate one from silence with probability `7/170`; `deception.out` l. 6 prints the same
certificate as `(133/170, 7/170)` in its (drop, fabricate) parametrisation, `133/170 = 1 − 37/170`).
So both of T1's deceivers sit on the garbling side. (Audit r1, adversarial N8.)
Source: [[corr-wf13-inventory]] 092 / miri.md I9.4 (`deception.out` l. 6: "targeted (1/20,1/5): (True, 133/170, 7/170)")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem targeted_is_garbling : IsPostProcessing (1/20) (9/10) (1/20) (1/5) :=
  ⟨37/170, 7/170, by constructor <;> norm_num, by constructor <;> norm_num, by norm_num, by norm_num⟩

/-! ### The reverse certificates are impossible: the three relations are strict (audit r2, adversarial N3) -/

/-- **T2, strictness (i): the believed sensor `(1/40, 9/10)` is not a post-processing of the honest
`(1/20, 9/10)`.** The two certificate equations have the unique solution `(p, q) = (341/340, −9/340)`,
outside `[0, 1]²`; so `believed_sensor_is_refinement`'s refinement is strict — the honest sensor is
not Blackwell-equivalent to the believed one. "Opposite sides" (F-2) needs this and the next
certificate, not only the two positive ones.
Source: [[corr-wf13-inventory]] 092 / miri.md I9.7 (audit r2 probe `PostProcessingStrict.lean`)
Kind: L (a negative certificate: two linear equations with no solution in the square)
Fidelity: exact
Hyps: (a) only -/
theorem believed_not_postProcessing_of_honest : ¬ IsPostProcessing (1/20) (9/10) (1/40) (9/10) := by
  rintro ⟨p, q, hp, hq, h1, h2⟩
  linarith [hp.2, hq.1]

/-- **T2, strictness (ii): the honest `(1/20, 9/10)` is not a post-processing of the deceiver's
`(1/40, 9/20)`.** The unique solution is `(p, q) = (2, 0)`, with `p > 1`; so `deceiver_is_garbling`'s
garbling is strict.
Source: [[corr-wf13-inventory]] 092 / miri.md I9.7 (audit r2 probe `PostProcessingStrict.lean`)
Kind: L (a negative certificate)
Fidelity: exact
Hyps: (a) only -/
theorem honest_not_postProcessing_of_deceiver : ¬ IsPostProcessing (1/40) (9/20) (1/20) (9/10) := by
  rintro ⟨p, q, hp, hq, h1, h2⟩
  linarith [hp.2, hq.1]

/-- **T2, strictness (iii): the honest `(1/20, 9/10)` is not a post-processing of the targeted
`(1/20, 1/5)`.** The unique solution is `(p, q) = (163/30, −7/30)`, outside the square; so
`targeted_is_garbling`'s garbling is strict.
Source: [[corr-wf13-inventory]] 092 / miri.md I9.4 (audit r2 probe `PostProcessingStrict.lean`)
Kind: L (a negative certificate)
Fidelity: exact
Hyps: (a) only -/
theorem honest_not_postProcessing_of_targeted : ¬ IsPostProcessing (1/20) (1/5) (1/20) (9/10) := by
  rintro ⟨p, q, hp, hq, h1, h2⟩
  linarith [hp.2, hq.1]

/-! ## T8 — "trust can be earned": the posterior, not the channel -/

/-- **T8(a), the posterior moves.** On `w3`, `P(wrong | Pr) = 18/37 ≠ 1/20 = P(wrong)`: trust in the
posterior over `ω` is earned by the press.
Source: [[corr-wf13-2-inventory]] 2-126 / position statement §2.12 (ABRAM); causal.md I15.2
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w3_posterior_moves :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).posteriorPress () .wrong ≠
      (twoPoint (1/20) mem_Icc_1_20).mass .wrong := by
  rw [w3_posteriorPress_wrong, twoPoint_wrong]; norm_num

/-- **T8(b), the channel is not a function of the posterior.** For every `q ∈ (0, 1)` and `β > 0`
the sensors `(α, β)` and `(qα, qβ)` have *different* miss rates (`1 − qβ ≠ 1 − β`) yet the *same*
press posterior (both defined: `0 < P(Pr)` at both) and the *same* D1 verdict: nothing the press
posterior shows identifies the channel. (Non-identifiability from the whole compliance record is `corr-three-step-facts`'
(corr-wf13-007); this is its two-point shadow on one press.)
Source: [[corr-wf13-2-inventory]] 2-126 / causal.md I15.2
Kind: L
Fidelity: weaker: one press's posterior, not the compliance record
Hyps: (a) only -/
theorem channel_not_identified (ε α β c h q : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hq0 : 0 < q) (hq1 : q < 1) (hβ0 : 0 < β) (hpm : 0 < (1 - ε) * α + ε * β) :
    (0 < (twoState ε (q * α) (q * β) c h hε (mul_mem_Icc hq hα) (mul_mem_Icc hq hβ)).pressMass () ∧
        0 < (twoState ε α β c h hε hα hβ).pressMass ()) ∧
      (1 - (twoState ε (q * α) (q * β) c h hε (mul_mem_Icc hq hα) (mul_mem_Icc hq hβ)).press () .wrong ≠
        1 - (twoState ε α β c h hε hα hβ).press () .wrong) ∧
      (twoState ε (q * α) (q * β) c h hε (mul_mem_Icc hq hα) (mul_mem_Icc hq hβ)).posteriorPress () .wrong =
        (twoState ε α β c h hε hα hβ).posteriorPress () .wrong ∧
      ((twoState ε (q * α) (q * β) c h hε (mul_mem_Icc hq hα) (mul_mem_Icc hq hβ)).D1At () ↔
        (twoState ε α β c h hε hα hβ).D1At ()) := by
  refine ⟨⟨?_, ?_⟩, ?_, twoState_posteriorPress_wrong_sensor_scale ε α β c h q hε hα hβ hq hq0,
    twoState_d1At_sensor_scale_iff ε α β c h q hε hα hβ hq hq0⟩
  · rw [twoState_pressMass]
    have : (1 - ε) * (q * α) + ε * (q * β) = q * ((1 - ε) * α + ε * β) := by ring
    rw [this]; exact mul_pos hq0 hpm
  · rw [twoState_pressMass]; exact hpm
  simp only [twoState, twoPress]
  intro hcontra
  have : q * β = β := by linarith
  have : (q - 1) * β = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

/-- **T8(b), the cell.** `w3`'s sensor and its half have miss rates `1/10` and `11/20` and the same
`P(wrong | Pr) = 18/37` and the same D1 verdict.
Source: [[corr-wf13-2-inventory]] 2-126 / miri.md I9.4
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem channel_not_identified_cell :
    (1 - (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).press () .wrong = 1/10) ∧
      (1 - (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).press () .wrong = 11/20) ∧
      (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).posteriorPress () .wrong =
        (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).posteriorPress () .wrong ∧
      (twoState (1/20) (1/40) (9/20) 1 20 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_20).D1At () ∧
      (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).D1At () := by
  refine ⟨?_, ?_, ?_, halved_d1At, w3_d1At⟩
  · simp only [twoState, twoPress]; norm_num
  · simp only [twoState, twoPress]; norm_num
  · rw [halved_posteriorPress_wrong, w3_posteriorPress_wrong]

end Cleanroom.Corrigibility.CorrPositionFinds
