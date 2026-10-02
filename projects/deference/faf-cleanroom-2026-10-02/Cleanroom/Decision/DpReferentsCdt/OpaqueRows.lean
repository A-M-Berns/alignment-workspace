import Cleanroom.Decision.DpReferentsCdt.OpaqueBasic

/-!
# Opaque Newcomb: the numeric rows

The rows of FA-18's last line, C2-A′'s witness, C2-4′'s Definition-6 cell, T10's tagged
interventionist, T11's precisification of Remark 3.11, T12(a)'s failure under F3′ alone, T14's
PCH/LCH numbers and masked-state fork, and T15's shared-seed failure — all by the closed forms of
`OpaqueBasic.lean` and `norm_num`/`ring`.

Conventions: `Act2.a` = one-box, `Act2.b` = two-box; `procQ q` puts mass `q` on one-boxing;
`opaqueNewcomb (3/4) 4 1` is FA-18's Newcomb (`L = 4`, `S = 1`, reliability `3/4`),
`opaqueNewcomb (9/10) 10 1` is T10's and T14(b)'s, `opaqueNewcomb 1 10 1` is P13's (T14(a)).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

/-- FA-18's Newcomb tree: reliability `3/4`, `L = 4`, `S = 1`. Source: `faithful.md` FA-18. Kind: D -/
def newcomb34 : Tree OpaqueW Unit (fun _ => Act2) ℚ :=
  opaqueNewcomb (3/4) (by norm_num) (by norm_num) 4 1

/-- The one-boxing label `δ_one`. Source: `faithful.md` FA-18 ("Newcomb `d`, `δ_one`"). Kind: D -/
def deltaOne : Proc Unit (fun _ => Act2) ℚ := procQ 1 (by norm_num) (by norm_num)

/-- The fill event `{fill = 1}`. Source: `sl-synthesis.md` line 120. Kind: D -/
def opaqueFillEv : Finset OpaqueW := Finset.univ.filter fun w => w.1 = true

/-! ## T1(c) / T11: FA-18's Newcomb row under `δ_one` -/

/-- **FA-18, Newcomb row, R1-prior `(3, 2)`**. Source: `faithful.md` FA-18. Kind: N+ -/
theorem newcomb34_refR1Prior :
    refR1Prior deltaOne newcomb34 () .a = 3 ∧ refR1Prior deltaOne newcomb34 () .b = 2 := by
  unfold newcomb34
  constructor <;> rw [opaque_refR1Prior] <;> simp <;> norm_num

/-- **FA-18, Newcomb row, R1-state `(3, 2)`**. Source: `faithful.md` FA-18. Kind: N+ -/
theorem newcomb34_refR1State :
    refR1State opaqueObs deltaOne newcomb34 () .a = 3 ∧
      refR1State opaqueObs deltaOne newcomb34 () .b = 2 := by
  unfold newcomb34
  constructor <;> rw [opaque_refR1State] <;> simp <;> norm_num

/-- **FA-18, Newcomb row, R2-SIA `(6, 5)`** — one-box: Theorem 1's SIA weight on the simulation
tips the verdict. Source: `faithful.md` FA-18, FA-19′; mandate T11(b). Kind: N+ -/
theorem newcomb34_refR2Sia :
    refR2Sia deltaOne newcomb34 () .a = 6 ∧ refR2Sia deltaOne newcomb34 () .b = 5 := by
  unfold newcomb34 deltaOne
  constructor <;> rw [opaque_refR2Sia] <;> simp [procQ, opaqueFillProb] <;> norm_num

/-- **FA-18, Newcomb row, R2-real `(3, 4)` — two-box**: the separator of the type axis; forcing
at the live node holds the prediction at its `C`-statistics (`P(fill) = 3/4` under `δ_one`).
Source: `faithful.md` FA-18, FA-19′ ("`G_real(one) = 3`, `G_real(two) = 4` — two-box"); mandate
T1(c), T11(c)
Kind: N+ -/
theorem newcomb34_refR2Real :
    refR2Real opaqueActEv deltaOne newcomb34 () .a = 3 ∧
      refR2Real opaqueActEv deltaOne newcomb34 () .b = 4 := by
  unfold newcomb34 deltaOne
  constructor <;> rw [opaque_refR2Real] <;> simp [procQ, opaqueFillProb] <;> norm_num

/-- **FA-18, Newcomb row, R3 `(3, 4)` — two-box** (R3 sides with R2-real under Definition 6).
Source: `faithful.md` FA-18, FA-21′; mandate T1(c)
Kind: N+ -/
theorem newcomb34_refR3 :
    refR3 opaqueObs opaqueActEv deltaOne newcomb34 () .a = 3 ∧
      refR3 opaqueObs opaqueActEv deltaOne newcomb34 () .b = 4 := by
  unfold newcomb34 deltaOne
  constructor <;> rw [opaque_refR3] <;> simp [procQ, opaqueFillProb] <;> norm_num

/-- **T11(a): the deviation covaries with the act** — `ν_{δ_one}(fill) = 3/4 ≠ 1/4 = ν_{δ_two}(fill)`.
Source: [[decision-problems-v2]] Remark 3.11 ("under both, a predictor's output covaries with the
action") — true for the deviation; mandate T11(a)
Kind: N+ -/
theorem newcomb34_deviation_covaries :
    nu (deltaOne.deviatePure () .a) newcomb34 opaqueFillEv = 3/4 ∧
      nu (deltaOne.deviatePure () .b) newcomb34 opaqueFillEv = 1/4 := by
  unfold newcomb34 deltaOne opaqueFillEv
  constructor <;> rw [nu_eq_sum, opaque_sum_leaves] <;>
    simp [opaqueNewcomb, leafLaw, world, Act2.sum_univ, Fin.sum_univ_two, FinDistr.coin,
      opaqueFill, Proc.deviatePure, Proc.deviate_same, procQ] <;> norm_num

/-- **T11(c): single-instance forcing at the live node does not covary** — the fill probability
below every live node is fixed by the simulation's draw, so `refR2Real` differs between the acts by
exactly `S`, for every label: `refR2Real two − refR2Real one = 1`.
Source: `faithful.md` FA-19′ ("Joyce-style efficacy with the prediction independent of the forced
act"); mandate T11(c)
Kind: P -/
theorem newcomb34_refR2Real_gap (C : Proc Unit (fun _ => Act2) ℚ) :
    refR2Real opaqueActEv C newcomb34 () .b - refR2Real opaqueActEv C newcomb34 () .a = 1 := by
  unfold newcomb34
  rw [opaque_refR2Real, opaque_refR2Real]
  simp

/-! ## T3: the witness at a mixed label -/

/-- **C2-A′'s witness in closed form**: at label `q`, `refR2Real = (2q + 1, 2q + 2)` (two-box at
every `q`), `refR1State = (3, 2)`, `refR2Sia = (q + 5, q + 4)` (one-box); by C2-A′ the strict
evidential value and R3 are the first pair.
Source: mandate T3 (witness); `C2.md` C2-2′(a); `faithful.md` FA-25′(1′) ("conditioning `(2q+1, 2q+2)`
vs R1-state `(3, 2)`")
Kind: N+ -/
theorem newcomb34_label_forms (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    refR2Real opaqueActEv (procQ q h0 h1) newcomb34 () .a = 2 * q + 1 ∧
    refR2Real opaqueActEv (procQ q h0 h1) newcomb34 () .b = 2 * q + 2 ∧
    refR3 opaqueObs opaqueActEv (procQ q h0 h1) newcomb34 () .a = 2 * q + 1 ∧
    refR3 opaqueObs opaqueActEv (procQ q h0 h1) newcomb34 () .b = 2 * q + 2 ∧
    refR1State opaqueObs (procQ q h0 h1) newcomb34 () .a = 3 ∧
    refR1State opaqueObs (procQ q h0 h1) newcomb34 () .b = 2 ∧
    refR2Sia (procQ q h0 h1) newcomb34 () .a = q + 5 ∧
    refR2Sia (procQ q h0 h1) newcomb34 () .b = q + 4 := by
  unfold newcomb34
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [opaque_refR2Real]; simp [procQ, opaqueFillProb]; ring)
    | (rw [opaque_refR3]; simp [procQ, opaqueFillProb]; ring)
    | (rw [opaque_refR1State]; simp; norm_num)
    | (rw [opaque_refR2Sia]; simp [procQ, opaqueFillProb]; ring)

/-- **The strict state's act values at a mixed label are `(2q+1, 2q+2)`** — C2-A′ (i) instantiated:
`V_{s_q}(a) = refR2Real a` for the calibrated state of `procQ q`, `0 < q < 1`.
Source: mandate T3 (witness: "`evStrict = refR2Real = (2q+1, 2q+2)` two-box at every `q`")
Kind: N+ -/
theorem newcomb34_evStrict (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    let s : Unit → State OpaqueW ℚ := fun _ =>
      calibratedState (procQ q h0.le h1.le) newcomb34 (opaqueObs ()) (by
        unfold newcomb34; rw [opaque_nu_obs]; exact one_pos)
    evStrict s opaqueActEv () .a = 2 * q + 1 ∧ evStrict s opaqueActEv () .b = 2 * q + 2 := by
  intro s
  have hpos : 0 < nu (procQ q h0.le h1.le) newcomb34 (opaqueObs ()) := by
    unfold newcomb34; rw [opaque_nu_obs]; exact one_pos
  have hs : StrictOCAt s opaqueObs (procQ q h0.le h1.le) newcomb34 () :=
    strictOCAt_calibratedState opaqueObs (procQ q h0.le h1.le) newcomb34 s () hpos rfl
  have hA : ActRecording opaqueObs opaqueActEv (procQ q h0.le h1.le) newcomb34 () :=
    opaqueNewcomb_actRecording _ _ _ _ _ _
  have hdisj : ActEvDisjoint opaqueActEv () := opaque_actEvDisjoint
  obtain ⟨e1, e2, -⟩ := newcomb34_label_forms q h0.le h1.le
  constructor
  · rw [evStrict_eq_refR2Real_of_APlus s opaqueObs opaqueActEv _ _ hA hdisj hpos hs
      ((mem_APlus_iff_of_actRecording_strict opaqueObs opaqueActEv _ _ s hA hdisj hpos hs _).mpr
        (by simp [procQ, h0])), e1]
  · rw [evStrict_eq_refR2Real_of_APlus s opaqueObs opaqueActEv _ _ hA hdisj hpos hs
      ((mem_APlus_iff_of_actRecording_strict opaqueObs opaqueActEv _ _ s hA hdisj hpos hs _).mpr
        (by simp [procQ]; linarith)), e2]

/-! ## T4: C2-4′'s Definition-6 cell — the seed semantics -/

/-- **C2-4′ (Definition 6 is necessary)**: under the shared seed the act conditional on FA-18's
Newcomb is `(3, 2)`, one-box, at every mixed label — while `refR2Real` keeps `(2q+1, 2q+2)`.
Source: `C2.md` C2-3″ ("opaque Newcomb `(3,2)` one-box"), C2-4′ ("Definition 6 for EV = R2-real:
S1–S4"); mandate T4, T7
Kind: N+ -/
theorem newcomb34_seed_condExp (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    condExp' (procQ q h0.le h1.le) newcomb34 (opaqueActEv () .a) = 3 ∧
      condExp' (procQ q h0.le h1.le) newcomb34 (opaqueActEv () .b) = 2 := by
  unfold newcomb34
  constructor
  · rw [opaque_condExp'_actEv _ _ _ _ _ _ _ (by simp [procQ, h0])] <;> simp <;> norm_num
  · rw [opaque_condExp'_actEv _ _ _ _ _ _ _ (by simp [procQ]; linarith)] <;> simp <;> norm_num

/-! ## T10: the tagged interventionist flips between Definitions 6 and 6′ -/

/-- T10's tree: reliability `9/10`, `L = 10`, `S = 1`. Source: mandate T10. Kind: D -/
def newcomb910 : Tree OpaqueW Unit (fun _ => Act2) ℚ :=
  opaqueNewcomb (9/10) (by norm_num) (by norm_num) 10 1

/-- The trembled label `q_η = (1−η) q + η/2` with `η = 1/20`. Source: mandate T10. Kind: D -/
def trembledLabel (q : ℚ) : ℚ := (1 - 1/20) * q + (1/20) / 2

/-- The tremble of `procQ q` at `η = 1/20`, as a procedure. Source: mandate T10. Kind: D -/
def trembleQ (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Proc Unit (fun _ => Act2) ℚ :=
  tremble (procQ q h0 h1) (1/20) (by norm_num) (by norm_num)

/-- `|Act2| = 2`. Source: none: infrastructure. Kind: L -/
theorem Act2.card : Fintype.card Act2 = 2 := by decide

/-- The trembled procedure's one-boxing weight. Source: none: infrastructure. Kind: L -/
theorem trembleQ_w_a (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (trembleQ q h0 h1 ()).w .a = trembledLabel q := by
  simp only [trembleQ, tremble_w, procQ, FinDistr.act2_a, trembledLabel, Act2.card]
  push_cast
  ring

/-- **T10 under Definition 6: the fill rate conditional on the live draw is the same for both acts**
at every label — `P(fill ∣ live = one) = P(fill ∣ live = two) = 1/10 + (8/10) q_η`; cross-multiplied
against the positive act masses.
Source: dp-core-091; mandate T10 ("the learner learns 'no effect'")
Kind: P
Fidelity: exact (cross-multiplied) -/
theorem newcomb910_tremble_fill_cond (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (a : Act2) :
    nu (trembleQ q h0 h1) newcomb910 (opaqueFillEv ∩ opaqueActEv () a) =
      (1/10 + (8/10) * trembledLabel q) * nu (trembleQ q h0 h1) newcomb910 (opaqueActEv () a) := by
  unfold newcomb910 opaqueFillEv
  rw [nu_eq_sum, nu_eq_sum, opaque_sum_leaves, opaque_sum_leaves]
  have hb : (trembleQ q h0 h1 ()).w .b = 1 - trembledLabel q := by
    rw [Act2.w_b_eq, trembleQ_w_a]
  cases a <;>
    simp [opaqueNewcomb, leafLaw, world, opaqueActEv, Act2.sum_univ, Fin.sum_univ_two,
      FinDistr.coin, opaqueFill, trembleQ_w_a, hb] <;> ring

/-- **T10 at the three labels**: `q_η = 3/25, 1/2, 22/25` at `q = 0, 1/2, 1` — the fill rate the
tagged interventionist learns.
Source: mandate T10
Kind: N+ -/
theorem newcomb910_tremble_fill_values :
    1/10 + (8/10) * trembledLabel 0 = 3/25 ∧ 1/10 + (8/10) * trembledLabel (1/2) = 1/2 ∧
      1/10 + (8/10) * trembledLabel 1 = 22/25 := by
  unfold trembledLabel; norm_num

/-- **T10 under Definition 6′: the fill rate conditional on the live draw is `9/10` for one-boxing
and `1/10` for two-boxing** at every label (the seed makes the simulation read the live act).
Source: dp-core-091; mandate T10
Kind: P
Fidelity: exact (cross-multiplied) -/
theorem newcomb910_tremble_fill_cond' (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nu' (trembleQ q h0 h1) newcomb910 (opaqueFillEv ∩ opaqueActEv () .a) =
        (9/10) * nu' (trembleQ q h0 h1) newcomb910 (opaqueActEv () .a) ∧
      nu' (trembleQ q h0 h1) newcomb910 (opaqueFillEv ∩ opaqueActEv () .b) =
        (1/10) * nu' (trembleQ q h0 h1) newcomb910 (opaqueActEv () .b) := by
  unfold newcomb910 opaqueFillEv nu' worldEv
  constructor <;> rw [Finset.sum_filter, Finset.sum_filter, opaque_sum_leaves, opaque_sum_leaves] <;>
    simp only [opaque_leafLaw', opaque_world] <;>
    simp [opaqueActEv, Act2.sum_univ, Fin.sum_univ_two, FinDistr.coin, opaqueFill] <;> ring

/-- **T10's consequence**: the tremble-conditioned evaluator two-boxes under Definition 6 (the act
conditionals differ by exactly `S = 1` in two-boxing's favour) and one-boxes under 6′ (they differ
by `7` in one-boxing's favour), at every label with both acts positive.
Source: dp-core-091 ("the tremble-conditioned evaluator two-boxes under 6 and one-boxes under 6′");
dp-core-105; mandate T10
Kind: N+ -/
theorem newcomb910_tremble_verdicts (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    condExp (trembleQ q h0 h1) newcomb910 (opaqueActEv () .b) -
        condExp (trembleQ q h0 h1) newcomb910 (opaqueActEv () .a) = 1 ∧
      condExp' (trembleQ q h0 h1) newcomb910 (opaqueActEv () .a) -
        condExp' (trembleQ q h0 h1) newcomb910 (opaqueActEv () .b) = 7 := by
  have ha : 0 < (trembleQ q h0 h1 ()).w .a := by
    rw [trembleQ_w_a]; unfold trembledLabel; linarith
  have hb : 0 < (trembleQ q h0 h1 ()).w .b := by
    rw [Act2.w_b_eq, trembleQ_w_a]; unfold trembledLabel; linarith
  unfold newcomb910
  constructor
  · unfold condExp
    rw [opaque_paySum_actEv, opaque_paySum_actEv, opaque_nu_actEv, opaque_nu_actEv,
      mul_div_cancel_left₀ _ hb.ne', mul_div_cancel_left₀ _ ha.ne']
    simp
  · rw [opaque_condExp'_actEv _ _ _ _ _ _ _ ha, opaque_condExp'_actEv _ _ _ _ _ _ _ hb]
    simp
    norm_num

/-! ## T12(a): FA-25′(1′) fails under F3′ alone -/

/-- **FA-25′(1′) fails under F3′ alone**: on FA-18's Newcomb at the mixed label `1/2`, a `cf` slot
calibrated to `refR1State` (`3` at one-boxing) violates Definition 20's evidential criterion (the
strict value is `2`).
Source: `faithful.md` FA-25′(1′) ("Under F3′ alone this fails (Newcomb, mixed `C`: conditioning
`2q+1` vs R1-state `3`)"); mandate T12(a)
Kind: N+ -/
theorem newcomb34_evidentialCriterion_fails_refR1State :
    let s : Unit → State OpaqueW ℚ := fun _ =>
      calibratedState (procQ (1/2) (by norm_num) (by norm_num)) newcomb34 (opaqueObs ()) (by
        unfold newcomb34; rw [opaque_nu_obs]; exact one_pos)
    let cf : Cf Unit (fun _ => Act2) ℚ := fun _ a => refR1State opaqueObs
      (procQ (1/2) (by norm_num) (by norm_num)) newcomb34 () a
    ¬ EvidentialCriterionAt s opaqueActEv cf () := by
  intro s cf h
  have hpos : 0 < nu (procQ (1/2) (by norm_num) (by norm_num)) newcomb34 (opaqueObs ()) := by
    unfold newcomb34; rw [opaque_nu_obs]; exact one_pos
  have hs : StrictOCAt s opaqueObs (procQ (1/2) (by norm_num) (by norm_num)) newcomb34 () :=
    strictOCAt_calibratedState opaqueObs _ newcomb34 s () hpos rfl
  have hA : ActRecording opaqueObs opaqueActEv (procQ (1/2) (by norm_num) (by norm_num))
      newcomb34 () := opaqueNewcomb_actRecording _ _ _ _ _ _
  have hdisj : ActEvDisjoint opaqueActEv () := opaque_actEvDisjoint
  have ha : Act2.a ∈ APlus s opaqueActEv () :=
    (mem_APlus_iff_of_actRecording_strict opaqueObs opaqueActEv _ _ s hA hdisj hpos hs _).mpr
      (by simp [procQ])
  have e := h .a ha
  rw [evStrict_eq_refR2Real_of_APlus s opaqueObs opaqueActEv _ _ hA hdisj hpos hs ha] at e
  obtain ⟨e1, -, -, -, e5, -⟩ := newcomb34_label_forms (1/2) (by norm_num) (by norm_num)
  simp only [cf] at e
  rw [e1, e5] at e
  norm_num at e

/-! ## T14: PCH / LCH on P13's tree and the masked-state fork -/

/-- P13's tree: a perfect sampler, `L = 10`, `S = 1`. Source: `repair/P13.md` P13-4′. Kind: D -/
def newcomb1 : Tree OpaqueW Unit (fun _ => Act2) ℚ :=
  opaqueNewcomb 1 (by norm_num) (by norm_num) 10 1

/-- **P13-4′: PCH `= refR2Real = (10q, 1 + 10q)` and LCH `= refR1State = (10, 1)`** at label `q`
under Definition 6; the seed conditional is `(10, 1)` for `0 < q < 1`.
Source: `repair/P13.md` P13-4′; dp-sl-061; mandate T14(a)
Kind: N+ -/
theorem newcomb1_pch_lch (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    refR2Real opaqueActEv (procQ q h0.le h1.le) newcomb1 () .a = 10 * q ∧
    refR2Real opaqueActEv (procQ q h0.le h1.le) newcomb1 () .b = 1 + 10 * q ∧
    refR1State opaqueObs (procQ q h0.le h1.le) newcomb1 () .a = 10 ∧
    refR1State opaqueObs (procQ q h0.le h1.le) newcomb1 () .b = 1 ∧
    condExp' (procQ q h0.le h1.le) newcomb1 (opaqueActEv () .a) = 10 ∧
    condExp' (procQ q h0.le h1.le) newcomb1 (opaqueActEv () .b) = 1 := by
  unfold newcomb1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [opaque_refR2Real] <;> simp [procQ, opaqueFillProb] <;> ring
  · rw [opaque_refR2Real] <;> simp [procQ, opaqueFillProb] <;> ring
  · rw [opaque_refR1State] <;> simp <;> norm_num
  · rw [opaque_refR1State] <;> simp <;> norm_num
  · rw [opaque_condExp'_actEv _ _ _ _ _ _ _ (by simp [procQ, h0])] <;> simp <;> norm_num
  · rw [opaque_condExp'_actEv _ _ _ _ _ _ _ (by simp [procQ]; linarith)] <;> simp <;> norm_num

/-- **P13-4′'s tremble values**: under the tremble of `δ_one` at `ε`, the act conditionals on P13's
tree are `10 − 5ε` (one-box) and `11 − 5ε` (two-box), for `0 < ε ≤ 1`.
Source: `repair/P13.md` P13-4′ ("tremble limits `11 − 5ε`"); dp-sl-061; mandate T14(a)
Kind: N+ -/
theorem newcomb1_tremble_values (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    condExp (tremble (procQ 1 (by norm_num) (by norm_num)) ε h0.le h1) newcomb1
        (opaqueActEv () .a) = 10 - 5 * ε ∧
      condExp (tremble (procQ 1 (by norm_num) (by norm_num)) ε h0.le h1) newcomb1
        (opaqueActEv () .b) = 11 - 5 * ε := by
  have hw : (tremble (procQ 1 (by norm_num) (by norm_num)) ε h0.le h1 ()).w .a = 1 - ε / 2 := by
    simp only [tremble_w, procQ, FinDistr.act2_a, Act2.card]
    push_cast
    ring
  have hb : (tremble (procQ 1 (by norm_num) (by norm_num)) ε h0.le h1 ()).w .b = ε / 2 := by
    rw [Act2.w_b_eq, hw]; ring
  have ha' : (tremble (procQ 1 (by norm_num) (by norm_num)) ε h0.le h1 ()).w .a ≠ 0 := by
    rw [hw]; linarith
  have hb' : (tremble (procQ 1 (by norm_num) (by norm_num)) ε h0.le h1 ()).w .b ≠ 0 := by
    rw [hb]; positivity
  unfold newcomb1 condExp
  constructor
  · rw [opaque_paySum_actEv, opaque_nu_actEv, mul_div_cancel_left₀ _ ha']
    unfold opaqueFillProb
    rw [hw]
    simp <;> ring
  · rw [opaque_paySum_actEv, opaque_nu_actEv, mul_div_cancel_left₀ _ hb']
    unfold opaqueFillProb
    rw [hw]
    simp <;> ring

/-- **T14(b), the masked-state fork**: on `opaqueNewcomb (9/10) … 10 1` under Definition 6, for
every self-model label `m` the masked state `calibratedState (C[d ↦ m])` has the same fill
probability conditional on either act, `P(fill ∣ one) = P(fill ∣ two) = 4m/5 + 1/10` — hence no
masked-calibrated state separates the evidential and `refR2Real` evaluators. Cross-multiplied
against the act masses.
Source: dp-sl-063; mandate T14(b)
Kind: P
Fidelity: exact (cross-multiplied; the state's `P` is `ν_{C[d↦m]}` since `O_d = ⊤`) -/
theorem newcomb910_masked_fork (C : Proc Unit (fun _ => Act2) ℚ) (m : FinDistr ℚ Act2) (a : Act2) :
    nu (C.deviate () m) newcomb910 (opaqueFillEv ∩ opaqueActEv () a) =
      (4 * m.w .a / 5 + 1/10) * nu (C.deviate () m) newcomb910 (opaqueActEv () a) := by
  unfold newcomb910 opaqueFillEv
  rw [nu_eq_sum, nu_eq_sum, opaque_sum_leaves, opaque_sum_leaves]
  have hb : m.w .b = 1 - m.w .a := Act2.w_b_eq m
  cases a <;>
    simp [opaqueNewcomb, leafLaw, world, opaqueActEv, Act2.sum_univ, Fin.sum_univ_two,
      FinDistr.coin, opaqueFill, Proc.deviate_same, hb] <;> ring

/-- **T14(b) under the shared seed the correlation exists**: `P'(fill ∣ one) = 9/10`,
`P'(fill ∣ two) = 1/10` at every label.
Source: dp-sl-063; mandate T14(b)
Kind: N+ -/
theorem newcomb910_seed_fork (C : Proc Unit (fun _ => Act2) ℚ) (m : FinDistr ℚ Act2) :
    nu' (C.deviate () m) newcomb910 (opaqueFillEv ∩ opaqueActEv () .a) =
        (9/10) * nu' (C.deviate () m) newcomb910 (opaqueActEv () .a) ∧
      nu' (C.deviate () m) newcomb910 (opaqueFillEv ∩ opaqueActEv () .b) =
        (1/10) * nu' (C.deviate () m) newcomb910 (opaqueActEv () .b) := by
  unfold newcomb910 opaqueFillEv nu' worldEv
  constructor <;> rw [Finset.sum_filter, Finset.sum_filter, opaque_sum_leaves, opaque_sum_leaves] <;>
    simp only [opaque_leafLaw', opaque_world] <;>
    simp [opaqueActEv, Act2.sum_univ, Fin.sum_univ_two, FinDistr.coin, opaqueFill,
      Proc.deviate_same] <;> ring

/-! ## T15: Huttegger's manifold fails under the shared seed -/

/-- **The screening identity fails under the shared seed** on FA-18's Newcomb with `X = fill` at
label `1/2`: `ν'(fill ∧ one) · ν'(⊤) = 3/8 ≠ 1/4 = ν'(fill) · ν'(one)`.
Source: mandate T15 ("Fails under the shared seed: `opaqueNewcomb` with `X = fill` under `nu'`")
Kind: N+ -/
theorem newcomb34_seed_screening_fails :
    nu' (procQ (1/2) (by norm_num) (by norm_num)) newcomb34
        (opaqueFillEv ∩ opaqueActEv () .a ∩ opaqueObs ()) *
      nu' (procQ (1/2) (by norm_num) (by norm_num)) newcomb34 (opaqueObs ()) ≠
    nu' (procQ (1/2) (by norm_num) (by norm_num)) newcomb34 (opaqueFillEv ∩ opaqueObs ()) *
      nu' (procQ (1/2) (by norm_num) (by norm_num)) newcomb34
        (opaqueActEv () .a ∩ opaqueObs ()) := by
  unfold newcomb34 opaqueFillEv opaqueObs nu' worldEv
  simp only [Finset.inter_univ, Finset.sum_filter, opaque_sum_leaves]
  simp only [opaque_leafLaw', opaque_world]
  simp [opaqueActEv, Act2.sum_univ, Fin.sum_univ_two, FinDistr.coin, opaqueFill, procQ]
  norm_num

end Cleanroom.Decision.DpReferentsCdt
