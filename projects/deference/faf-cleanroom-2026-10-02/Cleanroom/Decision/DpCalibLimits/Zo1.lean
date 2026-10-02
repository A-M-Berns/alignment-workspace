import Cleanroom.Decision.DpCalibLimits.TwoRoute

/-!
# T6(a),(c) — ZO-1's letter-proof separation on the AMD; the grid's uniform substitution

[[dp-calib-limits-mandate]] T6(a),(c) (dp-cf-2-042, zoo.md ZO-1, dp-sl-2-062 / C1 Open 8).

* **ZO-1** on the AMD (`amd`, last-draw action events, `O = ⊤`) with `C = procQ (3/4)` and the
  state `s` strictly calibrated to the self-model `C[d ↦ ¼]`: `P_s = (¼, 3/16, 9/16)` on
  `(sa, sba, sbb)`, `V_s(a) = 12/7`, `V_s(b) = 1`. `s` is masked-calibrated under the
  **letter** (`zo1_masked_letter`; `ν(⊤) = 1`, no vacuity used), its self-model is unique
  (`zo1_selfModel_unique`), it is neither strictly nor limit-calibrated for `C`
  (`zo1_not_strict`, `zo1_not_limit`; `O = ⊤` is realized so limit = strict), and the EDT
  verdicts differ: `argmax = {a}` at `s` (`zo1_argmax`), `{b}` at the strict state of `C`
  (`4/5 < 1`, `zo1Strict_argmax`).
* **Necessity of `¬ Nested`** for the cancellation lemma (`Cancellation.lean`): the AMD is
  nested (`amd_nested`) and the cross-multiplied cancellation identity fails on it
  (`amd_cancellation_fails`: `12/7 ≠ 4/5`).
* **The grid's substitution** (dp-sl-2-062): the uniform-column verdict implies Definition 9
  (`maskedUniformAt_imp_maskedOCAt`), and ZO-1's state is masked-calibrated but not
  uniform-column calibrated (`zo1_not_maskedUniform`: its unique self-model is `¼`, not `½`)
  — the substitution is strictly stronger.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-! ## Two-action argmax helpers -/

section argmaxHelpers

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- On a one-point two-action tree with both act events subjectively possible, the argmax is
`{a}` when `V(b) < V(a)`. Source: none: infrastructure. Kind: L -/
theorem argmaxPlus_act2_eq_a (s : Unit → State Ω K) (actEv : (d : Unit) → Act2 → Finset Ω)
    (ha : 0 < (s ()).pr (actEv () .a)) (hb : 0 < (s ()).pr (actEv () .b))
    (hlt : (s ()).V (actEv () .b) < (s ()).V (actEv () .a)) :
    argmaxPlus s actEv () = {.a} := by
  have hmema : Act2.a ∈ APlus s actEv () := by
    unfold APlus; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩
  have hmemb : Act2.b ∈ APlus s actEv () := by
    unfold APlus; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb⟩
  ext x
  rw [mem_argmaxPlus, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    cases x
    · rfl
    · exact absurd (h .a hmema) (not_le.mpr hlt)
  · rintro rfl
    refine ⟨hmema, fun b _ => ?_⟩
    cases b
    · exact le_rfl
    · exact le_of_lt hlt

/-- The mirror image: the argmax is `{b}` when `V(a) < V(b)`. Source: none: infrastructure. Kind: L -/
theorem argmaxPlus_act2_eq_b (s : Unit → State Ω K) (actEv : (d : Unit) → Act2 → Finset Ω)
    (ha : 0 < (s ()).pr (actEv () .a)) (hb : 0 < (s ()).pr (actEv () .b))
    (hlt : (s ()).V (actEv () .a) < (s ()).V (actEv () .b)) :
    argmaxPlus s actEv () = {.b} := by
  have hmema : Act2.a ∈ APlus s actEv () := by
    unfold APlus; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩
  have hmemb : Act2.b ∈ APlus s actEv () := by
    unfold APlus; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb⟩
  ext x
  rw [mem_argmaxPlus, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    cases x
    · exact absurd (h .b hmemb) (not_le.mpr hlt)
    · rfl
  · rintro rfl
    refine ⟨hmemb, fun b _ => ?_⟩
    cases b
    · exact le_of_lt hlt
    · exact le_rfl

end argmaxHelpers

/-! ## AMD arithmetic -/

/-- A sum over the leaves of the AMD. Source: none: infrastructure. Kind: L -/
theorem amd_sum (f : amd.Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, .a, ()⟩ + f ⟨.b, .b, ()⟩ := by
  unfold amd at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  ring

/-- `ν` on the AMD. Source: none: infrastructure. Kind: L -/
theorem amd_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset AmdW) :
    nu C amd X = (if AmdW.sa ∈ X then (C ()).w .a else 0) +
      (if AmdW.sba ∈ X then (C ()).w .b * (C ()).w .a else 0) +
      (if AmdW.sbb ∈ X then (C ()).w .b * (C ()).w .b else 0) := by
  rw [nu_eq_sum, amd_sum]
  simp [amd, leafLaw_decision, world_decision]

/-- `paySum` on the AMD. Source: none: infrastructure. Kind: L -/
theorem amd_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset AmdW) :
    paySum C amd X = (if AmdW.sba ∈ X then (C ()).w .b * (C ()).w .a * 4 else 0) +
      (if AmdW.sbb ∈ X then (C ()).w .b * (C ()).w .b else 0) := by
  rw [paySum_eq_sum_ite, amd_sum]
  simp [amd, leafLaw_decision, world_decision, payoff_decision]

/-! ## ZO-1 -/

/-- ZO-1's procedure `C(d)(a) = ¾`. Source: zoo.md ZO-1. Kind: D -/
def zo1Proc : Proc Unit (fun _ => Act2) ℚ := procQ (3 / 4) (by norm_num) (by norm_num)

/-- ZO-1's self-model `m(a) = ¼`. Source: zoo.md ZO-1. Kind: D -/
def zo1Model : FinDistr ℚ Act2 := FinDistr.act2 (1 / 4) (by norm_num) (by norm_num)

/-- `zo1Model` is full-support. Source: zoo.md ZO-1. Kind: L -/
theorem zo1Model_pos (a : Act2) : 0 < zo1Model.w a := by cases a <;> simp [zo1Model] <;> norm_num

/-- **ZO-1's state**: the strict state of `C[d ↦ ¼]` at `O = ⊤`.
Source: zoo.md ZO-1 ("state `s :=` the strict state of `C[d ↦ m]` with `m(a) = ¼`")
Kind: D -/
noncomputable def zo1State : State AmdW ℚ :=
  calibratedState (zo1Proc.deviate () zo1Model) amd Finset.univ (nu_univ_pos _ _)

/-- The strict state of `C` itself at `O = ⊤`. Source: zoo.md ZO-1. Kind: D -/
noncomputable def zo1Strict : State AmdW ℚ := calibratedState zo1Proc amd Finset.univ (nu_univ_pos _ _)

/-- `P_s = (¼, 3/16, 9/16)`. Source: zoo.md ZO-1. Kind: L -/
theorem zo1State_pr :
    zo1State.pr {.sa} = 1 / 4 ∧ zo1State.pr {.sba} = 3 / 16 ∧ zo1State.pr {.sbb} = 9 / 16 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [zo1State, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, amd_nu]
     simp [zo1Proc, zo1Model, procQ]; try norm_num)

/-- `V_s(a) = 12/7`, `V_s(b) = 1` (last-draw events). Source: zoo.md ZO-1. Kind: L -/
theorem zo1State_V :
    zo1State.V (amdActEvLast () .a) = 12 / 7 ∧ zo1State.V (amdActEvLast () .b) = 1 := by
  constructor <;> simp [zo1State, calibratedState_V, amd_nu, amd_paySum, amdActEvLast, zo1Proc,
    zo1Model, procQ] <;> norm_num

/-- At the strict state of `C`: `V(a) = 4/5`, `V(b) = 1`. Source: zoo.md ZO-1. Kind: L -/
theorem zo1Strict_V :
    zo1Strict.V (amdActEvLast () .a) = 4 / 5 ∧ zo1Strict.V (amdActEvLast () .b) = 1 := by
  constructor <;> simp [zo1Strict, calibratedState_V, amd_nu, amd_paySum, amdActEvLast, zo1Proc,
    procQ] <;> norm_num

/-- **ZO-1: masked-calibrated under the letter**: the self-model `C[d ↦ ¼]` is local and
full-support, realizes `⊤`, and `s` is its strict state — no vacuity reading is used.
Source: zoo.md ZO-1 ("Masked OC … calibrated, unique self-model `m = (¼, ¾)`, `ν = 1 > 0` — the
letter's positivity requirement is met"); dp-cf-2-042
Kind: N+
Fidelity: exact
Hyps: none -/
theorem zo1_masked_letter : MaskedOCAtV (fun _ => zo1State) amdObs zo1Proc amd .LF .letter () :=
  Or.inl ⟨zo1Proc.deviate () zo1Model, ⟨zo1Model, zo1Model_pos, rfl⟩, nu_univ_pos _ _,
    strictClausesAt_calibratedState amdObs _ amd (fun _ => zo1State) () (nu_univ_pos _ _) rfl⟩

/-- **Uniqueness of ZO-1's self-model**: any full-support local self-model whose strict clauses
`s` satisfies has `m(a) = ¼` (clause 1 at `{sa}`).
Source: zoo.md ZO-1 ("unique self-model")
Kind: P
Fidelity: exact -/
theorem zo1_selfModel_unique (m : FinDistr ℚ Act2) (_ : ∀ a, 0 < m.w a)
    (h : StrictClausesAt (fun _ => zo1State) amdObs (zo1Proc.deviate () m) amd ()) :
    m.w .a = 1 / 4 := by
  have := h.1 {.sa}
  simp only [amdObs, nu_univ, mul_one, Finset.inter_univ] at this
  rw [zo1State, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, amd_nu, amd_nu] at this
  simp [zo1Proc, zo1Model, procQ] at this
  linarith

/-- **ZO-1 is not strictly calibrated for `C`**: `ν_C(sa) = ¾ ≠ ¼`.
Source: zoo.md ZO-1 ("strict OC … violated")
Kind: P
Fidelity: exact -/
theorem zo1_not_strict : ¬ StrictOCAt (fun _ => zo1State) amdObs zo1Proc amd () := by
  intro h
  have := (h (nu_univ_pos _ _)).1 {.sa}
  simp only [amdObs, nu_univ, mul_one, Finset.inter_univ] at this
  rw [zo1State, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, amd_nu, amd_nu] at this
  simp [zo1Proc, zo1Model, procQ] at this
  norm_num at this

/-- **ZO-1 is not limit-calibrated for `C`**: `O = ⊤` is realized, so limit = strict.
Source: zoo.md ZO-1 ("limit OC … violated")
Kind: C
Fidelity: exact -/
theorem zo1_not_limit : ¬ LimitOCAt (fun _ => zo1State) amdObs zo1Proc amd () := fun h =>
  zo1_not_strict ((limitOCAt_iff_strictOCAt_of_pos (fun _ => zo1State) amdObs zo1Proc amd ()
    (nu_univ_pos zo1Proc amd)).mp h)

/-- **The EDT verdict at ZO-1's state is `a`** (`12/7 > 1`).
Source: zoo.md ZO-1 ("EDT at the masked state `12/7 > 1 ⇒ a`")
Kind: P
Fidelity: exact -/
theorem zo1_argmax : argmaxPlus (fun _ => zo1State) amdActEvLast () = {.a} := by
  obtain ⟨hva, hvb⟩ := zo1State_V
  apply argmaxPlus_act2_eq_a
  · show 0 < zo1State.pr _
    rw [zo1State, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, amd_nu]
    simp [amdActEvLast, zo1Proc, zo1Model, procQ]; try norm_num
  · show 0 < zo1State.pr _
    rw [zo1State, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, amd_nu]
    simp [amdActEvLast, zo1Proc, zo1Model, procQ]; try norm_num
  · rw [hva, hvb]; norm_num

/-- **The EDT verdict at the strict state of `C` is `b`** (`4/5 < 1`).
Source: zoo.md ZO-1 ("at the limit-pinned state `4/5 < 1 ⇒ b`")
Kind: P
Fidelity: exact -/
theorem zo1Strict_argmax : argmaxPlus (fun _ => zo1Strict) amdActEvLast () = {.b} := by
  obtain ⟨hva, hvb⟩ := zo1Strict_V
  apply argmaxPlus_act2_eq_b
  · show 0 < zo1Strict.pr _
    rw [zo1Strict, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, amd_nu]
    simp [amdActEvLast, zo1Proc, procQ]; try norm_num
  · show 0 < zo1Strict.pr _
    rw [zo1Strict, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, amd_nu]
    simp [amdActEvLast, zo1Proc, procQ]; try norm_num
  · rw [hva, hvb]; norm_num

/-- **ZO-1, bundled**: letter-proof masked calibration, unique self-model, not strict, not
limit, and the two EDT verdicts.
Source: zoo.md ZO-1 (dp-cf-2-042)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem zo1_separation :
    MaskedOCAtV (fun _ => zo1State) amdObs zo1Proc amd .LF .letter () ∧
    (∀ m : FinDistr ℚ Act2, (∀ a, 0 < m.w a) →
      StrictClausesAt (fun _ => zo1State) amdObs (zo1Proc.deviate () m) amd () → m.w .a = 1 / 4) ∧
    ¬ StrictOCAt (fun _ => zo1State) amdObs zo1Proc amd () ∧
    ¬ LimitOCAt (fun _ => zo1State) amdObs zo1Proc amd () ∧
    argmaxPlus (fun _ => zo1State) amdActEvLast () = {.a} ∧
    argmaxPlus (fun _ => zo1Strict) amdActEvLast () = {.b} :=
  ⟨zo1_masked_letter, zo1_selfModel_unique, zo1_not_strict, zo1_not_limit, zo1_argmax,
    zo1Strict_argmax⟩

/-! ## Necessity of `¬ Nested` for the cancellation lemma -/

/-- The AMD is nested at its point: the `(b, ·)` leaves meet two `d`-nodes.
Source: `seeds.md` SE-2; zoo.md ZO-1 ("nested fiber (two `d`-nodes on the `b`-path)")
Kind: L -/
theorem amd_nested : Nested amd () :=
  ⟨by rw [show Fintype.card Act2 = 2 from rfl], ⟨⟨.b, .a, ()⟩, by simp [Positive, amd],
    by simp [amd, count]⟩⟩

/-- **The cancellation identity fails on the nested AMD**: with `X = {sba}` and the last-draw
`a`-event, `ν_{C[d↦¼]}(X ∩ a) · ν_C(a) = (3/16)(15/16) ≠ (3/16)(7/16) = ν_C(X ∩ a) · ν_{C[d↦¼]}(a)`
(the conditionals `12/7` vs `4/5`). So `¬ Nested` cannot be dropped from `cancellation`.
Source: zoo.md ZO-1; dp-cf-2-042 (the cancellation lemma's hypothesis)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem amd_cancellation_fails :
    nu (zo1Proc.deviate () zo1Model) amd ({.sba} ∩ (amdActEvLast () .a ∩ amdObs ())) *
        nu zo1Proc amd (amdActEvLast () .a ∩ amdObs ()) ≠
      nu zo1Proc amd ({.sba} ∩ (amdActEvLast () .a ∩ amdObs ())) *
        nu (zo1Proc.deviate () zo1Model) amd (amdActEvLast () .a ∩ amdObs ()) := by
  simp [amd_nu, amdActEvLast, amdObs, zo1Proc, zo1Model, procQ]
  norm_num

/-! ## The grid's uniform substitution -/

section uniformSub

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- **The uniform column implies Definition 9**: the uniform self-model is local and
full-support, so its strict clauses are a masked witness.
Source: C1 Open 8 (dp-sl-2-062)
Kind: L
Fidelity: exact -/
theorem maskedUniformAt_imp_maskedOCAt (obs : ι → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (s : ι → State Ω K) (d : ι) (h : MaskedUniformAt obs C B s d) :
    MaskedOCAt s obs C B d :=
  Or.inl ⟨C.deviate d FinDistr.uniform, ⟨FinDistr.uniform, fun a => FinDistr.uniform_w_pos a, rfl⟩,
    h.1, h.2⟩

end uniformSub

/-- **The converse fails on ZO-1**: its state is masked-calibrated (even under the letter) but
not uniform-column calibrated — the unique self-model is `¼`, not `½`. Every masked-grade
verdict computed from the grid's uniform column is therefore a `(c)` substitution strictly
stronger than Definition 9.
Source: C1 Open 8 (dp-sl-2-062) ("every masked-grade verdict inherited from the grid was
computed at the strict state of `C[d ↦ ½]`, not Definition 9's existential")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem zo1_not_maskedUniform :
    MaskedOCAt (fun _ => zo1State) amdObs zo1Proc amd () ∧
    ¬ MaskedUniformAt amdObs zo1Proc amd (fun _ => zo1State) () := by
  refine ⟨Or.inl ⟨zo1Proc.deviate () zo1Model, ⟨zo1Model, zo1Model_pos, rfl⟩, nu_univ_pos _ _,
    strictClausesAt_calibratedState amdObs _ amd (fun _ => zo1State) () (nu_univ_pos _ _) rfl⟩,
    fun ⟨_, h⟩ => ?_⟩
  have := zo1_selfModel_unique FinDistr.uniform (fun a => FinDistr.uniform_w_pos a) h
  rw [FinDistr.uniform_w, act2_card_rat] at this
  norm_num at this

end Cleanroom.Decision.DpCalibLimits
