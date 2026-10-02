import Cleanroom.Corrigibility.CorrJointProcess.Buttons

/-!
# T14, T21 — the faking iff as the compliance threshold; the act-component and procedural-anchor rules

Load-bearing 3 (T14).

* **T14, the model** (`detection.md` R2 item 2, `checks.py` B; `anticipatory` P5): a Setting S
  instance `fakingFamily e h g d : ThreeStep World Bool TwoAct` — latent `{Bad = wrong, Good = right}`
  with `P(Bad) = 1 − e`; first actions `true` = honest (refuse in training: the modification lands,
  press rate `1`), `false` = fake (comply in training: it does not land, press rate `0`, cost `d`
  on both branches, Pattern C); `V`: modified ∧ Bad `= −h`, modified ∧ Good `= +g`, unmodified `= 0`.
  The "press" is the modification landing, so A1 fails for honest by design.
* **(a)** `V(honest) = −(1−e)h + eg`, `V(fake) = −d`, and `fake ≻ honest ⟺ d < (1−e)h − eg`
  (`fake_gt_honest_iff`) — `L`, product form.
* **(b) The content (`C`).** This *is* the parent's compliance threshold with `q := e`, stakes
  `c := h − d`, `h := g + d`: accept the modification iff `e ≥ (h − d)/(h + g)` when `0 < h + g`
  (`accept_iff_threshold`) — alignment faking is the resist branch of the compliance rule, with
  the source's `e* = (h − d)/(h + g)`. Junk: `h + g = 0` (hypothesis); `d > h` makes `e* < 0`
  and faking is never chosen (`never_fake_of_price_gt_harm`).
* **Witness** (P5 table, `h = 5`, `g = 1`): `(e, d) = (1/100, 1/10)`, `(1/10, 1)`, `(1/2, 3)`
  and the stopping prices `247/50, 22/5, 2` (`faking_table`).
* **T21.** (i) constitutive stakes: "comply iff `p·h_π ≥ (1−p)·c`" is the parent's
  `complianceThreshold_iff` (`comply_iff_constitutive`, one `L` row). (ii) world-indexed stakes
  `h_L = (1−w)h − w·c_err` can be negative, and then the push is dodged at every `p` including
  `p = 1` (`dodged_of_neg_stake`); N+ A3b (`h = 1/100`, `c = 9/10`: threshold `90/91 > 19/20`,
  resisted at `p = 19/20`) (`a3b_witness`).

Selective disclosure (021's second clause), the mutual-information bit count and the
non-manipulation fixed point are findings, not targets.

Sources: detection.md R2 item 2; anticipatory-final.md Statement 6(a); anticipatory.md P5;
christiano-respondent.md Q3; legitimacy-general-final.md Statement 4(b) (A3b).
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

section Faking

variable (e h g d : ℝ) (he : e ∈ Set.Icc (0 : ℝ) 1)
include he

/-- `1 − e ∈ [0, 1]` when `e ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma one_sub_mem_Icc : 1 - e ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [he.2], by linarith [he.1]⟩

/-- **The faking family** (T14's model as a Setting S instance): `μ` has `P(wrong = Bad) = 1 − e`;
`true` = honest (the modification lands: press rate `1`; modified ∧ Bad `−h`, modified ∧ Good
`+g`, silence `0`), `false` = fake (press rate `0`; payoff `−d` everywhere). The final action is
immaterial (`Sh = {stop}` for the carrier only).
Source: [[corr-wf14b-inventory]] 021 / detection.md R2 item 2 (`checks.py` B); anticipatory.md P5
Kind: D
Fidelity: exact (the "press" is the modification landing; A1 fails for honest by design)
Hyps: n/a (definition) -/
noncomputable def fakingFamily : ThreeStep World Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint (1 - e) (one_sub_mem_Icc e he)
  press := fun a _ => if a then 1 else 0
  press_nonneg := fun a _ => by
    show (0 : ℝ) ≤ (if a then 1 else 0)
    split_ifs <;> norm_num
  press_le_one := fun a _ => by
    show (if a then (1 : ℝ) else 0) ≤ 1
    split_ifs <;> norm_num
  V := fun a o _ ω =>
    if a then (if o = .press then (if ω = .wrong then -h else g) else 0) else -d

/-- The value of a first action: its joint expectation (final action immaterial).
Source: [[corr-wf14b-inventory]] 021 / detection.md R2 item 2
Kind: D
Fidelity: exact -/
noncomputable def fakingValue (a : Bool) : ℝ :=
  (fakingFamily e h g d he).jointExpect a (fun o ω => (fakingFamily e h g d he).V a o .stop ω)

/-- **T14(a): `V(honest) = −(1 − e)h + eg`.**
Source: [[corr-wf14b-inventory]] 021 / detection.md R2 item 2; anticipatory.md P5
Kind: L
Fidelity: exact -/
theorem fakingValue_honest : fakingValue e h g d he true = -(1 - e) * h + e * g := by
  simp [fakingValue, jointExpect, fakingFamily, World.sum_eq]
  ring

/-- **T14(a): `V(fake) = −d`.**
Source: [[corr-wf14b-inventory]] 021 / detection.md R2 item 2
Kind: L
Fidelity: exact -/
theorem fakingValue_fake : fakingValue e h g d he false = -d := by
  simp [fakingValue, jointExpect, fakingFamily, World.sum_eq]
  ring

/-- **T14(a), the faking iff: `fake ≻ honest ⟺ d < (1 − e)h − eg`.**
Source: [[corr-wf14b-inventory]] 021 / detection.md R2 item 2 ("Faking is `V`-optimal iff `(1−e)h − eg > d`")
Kind: L
Fidelity: exact (product form, no division)
Hyps: (a) only -/
theorem fake_gt_honest_iff :
    fakingValue e h g d he true < fakingValue e h g d he false ↔ d < (1 - e) * h - e * g := by
  rw [fakingValue_honest, fakingValue_fake]
  constructor <;> intro H <;> linarith

/-- **T14(b), the content: the faking iff is the parent's compliance threshold** with `q := e`,
stakes `c := h − d` (what refusing costs when the objective is legitimate, net of the price) and
`h := g + d`: the agent accepts the modification (honest ≥ fake) iff `e ≥ (h − d)/(h + g)`,
whenever `0 < h + g`. "Alignment faking is the resist branch of the compliance rule."
Source: [[corr-wf14b-inventory]] 021 / detection.md R2 item 2 ("v1 §2.13(a)'s compliance threshold with its slots filled"); anticipatory-final.md Statement 6(a)
Kind: C (`fake_gt_honest_iff` composed with the parent's `complianceThreshold_iff` at the substituted stakes)
Fidelity: exact
Hyps: (a) only; `0 < h + g` names the junk point -/
theorem accept_iff_threshold (hhg : 0 < h + g) :
    fakingValue e h g d he false ≤ fakingValue e h g d he true ↔ (h - d) / (h + g) ≤ e := by
  have hch : 0 < (h - d) + (g + d) := by linarith
  have := complianceThreshold_iff e (h - d) (g + d) hch
  unfold complianceThreshold at this
  rw [show (h - d) + (g + d) = h + g by ring] at this
  rw [← this, fakingValue_honest, fakingValue_fake]
  constructor <;> intro H <;> linarith

/-- **T14(b), the junk point named**: with `d > h` (the price exceeds the harm) the threshold
`e* = (h−d)/(h+g)` is negative and faking is never chosen, for `e ∈ [0,1]`, `g, h ≥ 0`.
Source: [[corr-wf14b-inventory]] 021 / mandate T14(b)
Kind: L
Fidelity: exact -/
theorem never_fake_of_price_gt_harm (hh : 0 ≤ h) (hd : h < d) (hg : 0 ≤ g) :
    fakingValue e h g d he false ≤ fakingValue e h g d he true := by
  rw [fakingValue_honest, fakingValue_fake]
  nlinarith [he.1, he.2, mul_nonneg he.1 hg, mul_nonneg he.1 hh]

/-- **T14 witness (P5 table, `h = 5`, `g = 1`).** `(e, d) = (1/100, 1/10)`: `V(honest) = −247/50
< −1/10`, fake, `e* = 49/60`; `(1/10, 1)`: `−22/5 < −1`, fake, `e* = 2/3`; `(1/2, 3)`:
`−2 > −3`, honest, `e* = 1/3`; the stopping prices `(1−e)h − eg` are `247/50, 22/5, 2`.
Source: [[corr-wf14b-inventory]] 021 / anticipatory.md P5 (the table)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem faking_table :
    (fakingValue (1 / 100) 5 1 (1 / 10) mem_Icc_1_100 true = -(247 / 50) ∧
      fakingValue (1 / 100) 5 1 (1 / 10) mem_Icc_1_100 true < fakingValue (1 / 100) 5 1 (1 / 10) mem_Icc_1_100 false ∧
      (5 - 1 / 10 : ℝ) / (5 + 1) = 49 / 60) ∧
    (fakingValue (1 / 10) 5 1 1 mem_Icc_1_10 true = -(22 / 5) ∧
      fakingValue (1 / 10) 5 1 1 mem_Icc_1_10 true < fakingValue (1 / 10) 5 1 1 mem_Icc_1_10 false ∧
      (5 - 1 : ℝ) / (5 + 1) = 2 / 3) ∧
    (fakingValue (1 / 2) 5 1 3 mem_Icc_half true = -2 ∧
      fakingValue (1 / 2) 5 1 3 mem_Icc_half false < fakingValue (1 / 2) 5 1 3 mem_Icc_half true ∧
      (5 - 3 : ℝ) / (5 + 1) = 1 / 3) ∧
    ((1 - 1 / 100 : ℝ) * 5 - 1 / 100 * 1 = 247 / 50 ∧ (1 - 1 / 10 : ℝ) * 5 - 1 / 10 * 1 = 22 / 5 ∧
      (1 - 1 / 2 : ℝ) * 5 - 1 / 2 * 1 = 2) := by
  simp only [fakingValue_honest, fakingValue_fake]
  norm_num

end Faking

/-! ## T21 — the act-component rule and the procedural-anchor rule -/

section Anchor

/-- **T21(i): constitutive stakes.** With `X = −h_π` on an authentic press and `+c` on a hijack
and `p = P(authentic ∣ press)`: "comply iff `p·h_π ≥ (1 − p)·c`" and "comply iff
`p ≥ c/(c + h_π)`" are the parent's `complianceThreshold_iff` — the two rules of
`christiano-respondent` Q3 coincide under constitutive stakes (0 mismatches in its 20 000
instances; here an identity).
Source: [[corr-wf14b-2-inventory]] 2-004 / christiano-respondent.md Q3 ("the two rules are the same inequality")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem comply_iff_constitutive (p c hπ : ℝ) (hch : 0 < c + hπ) :
    p * (-hπ) + (1 - p) * c ≤ 0 ↔ c / (c + hπ) ≤ p := by
  have := complianceThreshold_iff p c hπ hch
  unfold complianceThreshold at this
  exact this

/-- **World-indexed stakes**: `h_L = (1 − w)h − w·c_err`, the harm-if-authentic stake when an
authentic process errs on content with probability `w`.
Source: [[corr-wf14b-2-inventory]] 2-004 / christiano-respondent.md Q3 ("with world-indexed `V` the harm-if-legitimate stake … is small or negative")
Kind: D
Fidelity: exact -/
noncomputable def worldIndexedStake (w h cerr : ℝ) : ℝ := (1 - w) * h - w * cerr

/-- **T21(ii): a negative harm stake is dodged at every `p`, including `p = 1`.** If
`h_L < 0` then `p·(−h_L) + (1 − p)·c > 0` for every `p ∈ [0, 1]` with `c ≥ 0` (and `> 0` at
`p = 1` with no condition on `c`): fully updated deference re-appears inside the procedural
anchor, on the content axis.
Source: [[corr-wf14b-2-inventory]] 2-004 / christiano-respondent.md Q3 ("an authentic-but-wrong push dodged even when almost certainly authentic")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem dodged_of_neg_stake (p c hL : ℝ) (hneg : hL < 0) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hc : 0 ≤ c)
    (hp0 : 0 < p) : 0 < p * (-hL) + (1 - p) * c := by
  nlinarith [mul_nonneg (sub_nonneg.2 hp.2) hc]

/-- **T21(ii) witness (A3b).** `h = 1/100`, `c = 9/10`: the threshold `c/(c + h) = 90/91 > 19/20`,
and at `p = 19/20` the push is resisted: `p·(−h) + (1 − p)·c = 71/2000 > 0`.
Source: [[corr-wf14b-2-inventory]] 2-004 / legitimacy-general-final.md Statement 4(b) (A3b); christiano-respondent.md Q3
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem a3b_witness :
    (9 / 10 : ℝ) / (9 / 10 + 1 / 100) = 90 / 91 ∧ (19 / 20 : ℝ) < 90 / 91 ∧
      (0 : ℝ) < 19 / 20 * (-(1 / 100)) + (1 - 19 / 20) * (9 / 10) := by
  norm_num

end Anchor

end Cleanroom.Corrigibility.CorrJointProcess
