import Cleanroom.Decision.DpCalibLimits.Defs

/-!
# T5 — Appendix B's four masked variants cannot carry the theorem (the 4×2 cell table)

[[dp-calib-limits-mandate]] T5 (dp-cf-041, CA-1′, Appendix B, `dp-calibration` T2's decision).

`MaskedEdtConsistent v r C B := ∃ s, MaskedOCV s obs C B v r ∧ TEdt s actEv C B`. The cells,
each on the tree CA-1′ names, with `dp-calibration`'s null-case decision (vacuity) as a
parameter:

* **LP, GP, both readings** (`t1_masked_plain`, `t1_not_tOpt`): on the one-point tree `t1`
  (`a ↦ 0`, `b ↦ 1`, `O = ⊤`), `δ_a` is masked-EDT-consistent with the plain self-model
  `C' = C` (`A_d^+ = {a}`, `T_EDT` vacuous) and not optimal.
* **GF, both readings** (`fantasy241_GF`, `fantasy241_outX_not_tOpt`): on `fantasy241`,
  `(out, x)` with the global full-support self-model `(½; ¼)` prices `in` at `7/4 < 2` and is
  approved; `value = 2 < 4`.
* **LF, vacuity** (`fantasy241_LF_vacuity`, `fantasy241_outY_not_tOpt`): on `fantasy241`,
  `(out, y)`: `p2` is null under every local self-model and vacuity frees it; at `p1` every
  local self-model prices `out` at `2 > 1`; `value = 2 < 4`.
* **LF, letter** (`fantasy541_letter_empty`): on `fantasy541` no procedure is LF-letter
  masked-EDT-consistent: `in` in the support is rejected (`5 > V(in) ≤ 4` at every local
  self-model), and `δ_out` leaves `p2` null under every local self-model, which the letter
  refuses. On `fantasy241` the letter does admit `(in, x)`, which is optimal
  (`fantasy241_letter_inX`): the letter's failure is existence, not optimality.
* **The verdict** (`appendixB_verdict`): on the named catalogue trees no variant, under either
  reading, yields existence and the optimality implication together. The universal over `𝔉`
  is `dp-edt-udt-fair`'s (CA-2′).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- **Masked-EDT-consistency in variant `v` under reading `r`**: some state assignment is
masked-calibrated (variant `v`, reading `r`) and `T_EDT`-approves `C`.
Source: [[decision-problems-v2]] Appendix B ("the masked family"); `calibration.md` CA-1′
Kind: D -/
def MaskedEdtConsistent {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] [DecidableEq ι] (v : MaskVariant) (r : NullReading)
    (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) : Prop :=
  ∃ s : ι → State Ω K, MaskedOCV s obs C B v r ∧ TEdt s actEv C B

/-! ## Two-point tree arithmetic -/

section twoPointLemmas

variable (C : Proc Pt2 (fun _ => Act2) ℚ) (r1 r2 r3 : ℚ)

/-- `ν` on a two-point tree. Source: none: infrastructure. Kind: L -/
theorem twoPoint_nu (X : Finset TwoW) :
    nu C (twoPoint r1 r2 r3) X =
      (if TwoW.out ∈ X then (C .p1).w .a else 0) +
      (if TwoW.inX ∈ X then (C .p1).w .b * (C .p2).w .a else 0) +
      (if TwoW.inY ∈ X then (C .p1).w .b * (C .p2).w .b else 0) := by
  rw [nu_eq_sum, twoPoint_sum]
  simp [twoPoint, leafLaw_decision, world_decision]

/-- `paySum` on a two-point tree. Source: none: infrastructure. Kind: L -/
theorem twoPoint_paySum (X : Finset TwoW) :
    paySum C (twoPoint r1 r2 r3) X =
      (if TwoW.out ∈ X then (C .p1).w .a * r1 else 0) +
      (if TwoW.inX ∈ X then (C .p1).w .b * (C .p2).w .a * r2 else 0) +
      (if TwoW.inY ∈ X then (C .p1).w .b * (C .p2).w .b * r3 else 0) := by
  rw [paySum_eq_sum_ite, twoPoint_sum]
  simp [twoPoint, leafLaw_decision, world_decision, payoff_decision]

/-- The value of a two-point tree. Source: none: infrastructure. Kind: L -/
theorem twoPoint_value :
    value C (twoPoint r1 r2 r3) =
      (C .p1).w .a * r1 + (C .p1).w .b * ((C .p2).w .a * r2 + (C .p2).w .b * r3) := by
  unfold value
  rw [twoPoint_sum]
  simp [twoPoint, leafLaw_decision, payoff_decision]
  ring

/-- Both points are queried. Source: none: infrastructure. Kind: L -/
theorem twoPoint_queried (d : Pt2) : d ∈ queried (twoPoint r1 r2 r3) := by
  cases d <;> simp [twoPoint, queried_decision, queried_leaf, Act2.univ_eq]

end twoPointLemmas

/-- `(out, x)`. Source: CA-1′(ii). Kind: D -/
def procOutX : Proc Pt2 (fun _ => Act2) ℚ := Proc.ofFun fun | .p1 => .a | .p2 => .a

/-- `(in, x)`. Source: CA-1′(iii) ("on `fantasy (5;4,1)` both optimal procedures …"). Kind: D -/
def procInX : Proc Pt2 (fun _ => Act2) ℚ := Proc.ofFun fun | .p1 => .b | .p2 => .a

/-- The mixed action `(½, ½)`. Source: none: infrastructure. Kind: D -/
def half : FinDistr ℚ Act2 := FinDistr.act2 (1 / 2) (by norm_num) (by norm_num)

/-- `half` is full-support. Source: none: infrastructure. Kind: L -/
theorem half_pos (a : Act2) : 0 < half.w a := by cases a <;> simp [half] <;> norm_num

/-! ## (i) `t1`: LP and GP, both readings -/

/-- **`T₁`**: one point, `O = ⊤`, `a ↦ 0`, `b ↦ 1`; the world records the act.
Source: CA-1′(i) ("`T₁` = one point `d = (s, ⊤, {a,b})`, `a → 0`, `b → 1`")
Kind: D -/
def t1 : Tree Act2 Unit (fun _ => Act2) ℚ := .decision () fun x => .leaf x (if x = .a then 0 else 1)

/-- `O = ⊤` on `T₁`. Source: CA-1′(i). Kind: D -/
def t1Obs : Unit → Finset Act2 := fun _ => Finset.univ

/-- Action events on `T₁`: the recorded act. Source: CA-1′(i). Kind: D -/
def t1ActEv (_ : Unit) (x : Act2) : Finset Act2 := {x}

/-- `δ_a` on `T₁`. Source: CA-1′(i). Kind: D -/
def procA1 : Proc Unit (fun _ => Act2) ℚ := fun _ => FinDistr.pure .a

/-- A sum over the leaves of `T₁`. Source: none: infrastructure. Kind: L -/
theorem t1_sum {M : Type} [AddCommMonoid M] (f : t1.Leaves → M) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, ()⟩ := by
  unfold t1 at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- `ν` on `T₁`. Source: none: infrastructure. Kind: L -/
theorem t1_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset Act2) :
    nu C t1 X = (if Act2.a ∈ X then (C ()).w .a else 0) + (if Act2.b ∈ X then (C ()).w .b else 0) := by
  rw [nu_eq_sum, t1_sum]; simp [t1]

/-- `paySum` on `T₁`. Source: none: infrastructure. Kind: L -/
theorem t1_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset Act2) :
    paySum C t1 X = if Act2.b ∈ X then (C ()).w .b else 0 := by
  rw [paySum_eq_sum_ite, t1_sum]; simp [t1]

/-- The value on `T₁` is the weight of `b`. Source: none: infrastructure. Kind: L -/
theorem t1_value (C : Proc Unit (fun _ => Act2) ℚ) : value C t1 = (C ()).w .b := by
  unfold value; rw [t1_sum]; simp [t1]

/-- **LP and GP on `T₁`, both readings**: `δ_a` is masked-EDT-consistent with the plain
self-model `C' = C` — the state is the strict state of `δ_a`, `A_d^+ = {a}`, `T_EDT` is vacuous.
Source: CA-1′(i) ("plain masking admits `C' = C` (strict calibration), `A_d^+ = {a}`, `T_EDT`
vacuous … Remark 3.9's collapse"); Appendix B
Kind: N+
Fidelity: exact
Hyps: none -/
theorem t1_masked_plain (v : MaskVariant) (hv : v = .LP ∨ v = .GP) (r : NullReading) :
    MaskedEdtConsistent v r t1Obs t1ActEv procA1 t1 := by
  refine ⟨fun _ => calibratedState procA1 t1 Finset.univ (nu_univ_pos _ _), fun d _ => ?_,
    fun d _ _ a ha => ?_⟩
  · cases d
    refine Or.inl ⟨procA1, ?_, nu_univ_pos _ _,
      strictClausesAt_calibratedState t1Obs procA1 t1 _ () (nu_univ_pos _ _) rfl⟩
    rcases hv with rfl | rfl
    · exact ⟨procA1 (), by simp [Proc.deviate]⟩
    · trivial
  · cases d
    have ha' : a = .a := by
      cases a
      · rfl
      · simp [procA1] at ha
    subst ha'
    rw [mem_argmaxPlus]
    refine ⟨?_, fun b hb => ?_⟩
    · unfold APlus; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
      rw [calibratedState_pr]; simp [t1_nu, t1ActEv, procA1]
    · have hb' : b = .a := by
        cases b
        · rfl
        · exfalso
          unfold APlus at hb; rw [Finset.mem_filter, calibratedState_pr] at hb
          simp [t1_nu, t1ActEv, procA1] at hb
      subst hb'; exact le_rfl

/-- `δ_a` is not optimal on `T₁` (`0 < 1`). Source: CA-1′(i) ("`V = 0 < 1`"). Kind: N+ -/
theorem t1_not_tOpt : ¬ TOpt procA1 t1 := by
  intro h
  have := h (fun _ => FinDistr.pure .b)
  rw [t1_value, t1_value] at this
  simp [procA1] at this
  linarith

/-! ## (ii) GF on `fantasy241`: `(out, x)` with the global self-model `(½; ¼)` -/

/-- The global full-support self-model `(½; ¼)`. Source: CA-1′(ii) ("`C'(d₂)(x) = ¼`"). Kind: D -/
def gfModel : Proc Pt2 (fun _ => Act2) ℚ
  | .p1 => half
  | .p2 => FinDistr.act2 (1 / 4) (by norm_num) (by norm_num)

/-- `gfModel` is full-support. Source: CA-1′(ii). Kind: L -/
theorem gfModel_fullSupport : gfModel.FullSupport := by
  intro d a; cases d <;> cases a <;> simp [gfModel, half] <;> norm_num

/-- `gfModel` realizes both observations. Source: CA-1′(ii). Kind: L -/
theorem gfModel_pos (d : Pt2) : 0 < nu gfModel fantasy241 (twoObs d) := by
  cases d <;> simp [fantasy241, twoPoint_nu, twoObs, gfModel, half] <;> norm_num

/-- The GF states: the calibrated states of `gfModel` at each observation.
Source: CA-1′(ii). Kind: D -/
noncomputable def gfState : Pt2 → State TwoW ℚ :=
  fun d => calibratedState gfModel fantasy241 (twoObs d) (gfModel_pos d)

/-- **GF on `fantasy241`, both readings**: `(out, x)` is masked-EDT-consistent with the global
self-model `(½; ¼)` — `V(in) = 7/4 < 2 = V(out)` at `p1`, `V(x) = 4 > 1` at `p2`.
Source: CA-1′(ii) ("`C'(d₂)(x) = ¼` gives `7/4 < 2` and approves out … App. B's 'mis-models
its own downstream behaviour' made concrete")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem fantasy241_GF (r : NullReading) :
    MaskedEdtConsistent .GF r twoObs twoActEv procOutX fantasy241 := by
  refine ⟨gfState, fun d _ => Or.inl ⟨gfModel, gfModel_fullSupport, gfModel_pos d,
    strictClausesAt_calibratedState twoObs gfModel fantasy241 gfState d (gfModel_pos d) rfl⟩,
    fun d _ _ a ha => ?_⟩
  cases d
  · have ha' : a = .a := by
      cases a
      · rfl
      · simp [procOutX] at ha
    subst ha'
    rw [mem_argmaxPlus]
    refine ⟨?_, fun b hb => ?_⟩
    · unfold APlus; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
      simp only [gfState]; rw [calibratedState_pr]
      simp [fantasy241, twoPoint_nu, twoObs, twoActEv, gfModel, half]
      try norm_num
    · cases b
      · exact le_rfl
      · simp [gfState, calibratedState_V, fantasy241, twoPoint_nu, twoPoint_paySum, twoObs,
          twoActEv, gfModel, half]
        norm_num
  · have ha' : a = .a := by
      cases a
      · rfl
      · simp [procOutX] at ha
    subst ha'
    rw [mem_argmaxPlus]
    refine ⟨?_, fun b hb => ?_⟩
    · unfold APlus; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
      simp only [gfState]; rw [calibratedState_pr]
      simp [fantasy241, twoPoint_nu, twoObs, twoActEv, gfModel, half]
      try norm_num
    · cases b
      · exact le_rfl
      · simp [gfState, calibratedState_V, fantasy241, twoPoint_nu, twoPoint_paySum, twoObs,
          twoActEv, gfModel, half]
        norm_num

/-- `(out, x)` is not optimal on `fantasy241` (`2 < 4`). Source: CA-1′(ii). Kind: N+ -/
theorem fantasy241_outX_not_tOpt : ¬ TOpt procOutX fantasy241 := by
  intro h
  have := h procInX
  rw [fantasy241, twoPoint_value, twoPoint_value] at this
  simp [procOutX, procInX] at this
  norm_num at this

/-! ## (iii) LF, vacuity on `fantasy241`: `(out, y)` -/

/-- The vacuity states for `(out, y)`: at `p1` the calibrated state of the local self-model
`(½)`; at `p2` (null under every local self-model, hence free) the state certain of `(in, y)`.
Source: CA-1′(iii); A5
Kind: D -/
noncomputable def vacState : Pt2 → State TwoW ℚ
  | .p1 => calibratedState (procOutY.deviate .p1 half) fantasy241 Finset.univ (nu_univ_pos _ _)
  | .p2 => State.dirac .inY 0

/-- **LF under the vacuity reading on `fantasy241`**: `(out, y)` is masked-EDT-consistent —
`p2` is free (`fantasy_maskedOC_vacuity`), at `p1` the local self-model `(½)` prices `out` at
`2 > 1 = V(in)` (the true continuation plays `y`). At the free point `p2` the state is the
chosen `State.dirac inY 0`, so `A_{p2}^+ = {y}` and `T_EDT` holds there by that choice, not by
anything in the tree — exactly the vacuity artifact CA-1′(iii) describes ("`d₂` is free").
Source: CA-1′(iii) ("under the vacuity reading `C = (out, y)` on `T₂` is LF-masked-EDT-
consistent"); A5
Kind: N+
Fidelity: variant: null case read as vacuity (the record)
Hyps: none -/
theorem fantasy241_LF_vacuity :
    MaskedEdtConsistent .LF .vacuity twoObs twoActEv procOutY fantasy241 := by
  refine ⟨vacState, fun d _ => ?_, fun d _ _ a ha => ?_⟩
  · cases d
    · exact Or.inl ⟨procOutY.deviate .p1 half, ⟨half, half_pos, rfl⟩, nu_univ_pos _ _,
        strictClausesAt_calibratedState twoObs _ fantasy241 vacState .p1 (nu_univ_pos _ _) rfl⟩
    · exact fantasy_maskedOC_vacuity vacState
  · cases d
    · have ha' : a = .a := by
        cases a
        · rfl
        · simp [procOutY] at ha
      subst ha'
      rw [mem_argmaxPlus]
      refine ⟨?_, fun b hb => ?_⟩
      · unfold APlus; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        simp only [vacState]; rw [calibratedState_pr]
        simp [fantasy241, twoPoint_nu, twoObs, twoActEv, procOutY, half, Proc.deviate,
          Function.update_of_ne, Function.update_self]
      · cases b
        · exact le_rfl
        · simp [vacState, calibratedState_V, fantasy241, twoPoint_nu, twoPoint_paySum, twoObs,
            twoActEv, procOutY, half, Proc.deviate, Function.update_of_ne, Function.update_self]
          norm_num
    · have ha' : a = .b := by
        cases a
        · simp [procOutY] at ha
        · rfl
      subst ha'
      rw [mem_argmaxPlus]
      refine ⟨?_, fun b hb => ?_⟩
      · unfold APlus; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        simp only [vacState]; rw [State.dirac_pr]; simp [twoActEv]
      · cases b
        · exfalso
          unfold APlus at hb; rw [Finset.mem_filter] at hb
          simp only [vacState] at hb; rw [State.dirac_pr] at hb; simp [twoActEv] at hb
        · exact le_rfl

/-- `(out, y)` is not optimal on `fantasy241` (`2 < 4`). Source: CA-1′(iii). Kind: N+ -/
theorem fantasy241_outY_not_tOpt : ¬ TOpt procOutY fantasy241 := by
  intro h
  have := h procInX
  rw [fantasy241, twoPoint_value, twoPoint_value] at this
  simp [procOutY, procInX] at this
  norm_num at this

/-! ## (iv) LF, letter -/

/-- **Under the letter reading no procedure is LF masked-EDT-consistent on `fantasy541`**: if
`in` is in `supp C(p1)`, every local self-model at `p1` prices `out` at `5` and `in` at
`4 C(p2)(x) + C(p2)(y) ≤ 4`, so `T_EDT` rejects `C`; if `C(p1) = δ_out`, `p2` is null under
every local self-model and the letter makes the masked existential fail.
Source: CA-1′(iii) ("on fantasy `(5;4,1)` both optimal procedures `(out,x), (out,y)` leave
`d₂` off-path and the LF-letter set is empty")
Kind: P
Fidelity: exact
Hyps: none -/
theorem fantasy541_letter_empty :
    ¬ ∃ C, MaskedEdtConsistent .LF .letter twoObs twoActEv C fantasy541 := by
  rintro ⟨C, s, hM, hT⟩
  have hC2 : (C .p2).w .a + (C .p2).w .b = 1 := by
    have := (C .p2).sum_one; rwa [Act2.sum_univ] at this
  have hC2a := (C .p2).nonneg .a
  have hC2b := (C .p2).nonneg .b
  by_cases hin : 0 < (C .p1).w .b
  · rcases hM .p1 (twoPoint_queried _ _ _ .p1) with ⟨C', ⟨m, hm, rfl⟩, _, h1, h2⟩ | ⟨h, -⟩
    · have hma := hm .a
      have hmb := hm .b
      -- the state's probabilities and values at `p1`
      have hnuout : nu (C.deviate .p1 m) fantasy541 (twoActEv .p1 .a ∩ twoObs .p1) = m.w .a := by
        simp only [twoObs, Finset.inter_univ]
        rw [fantasy541, twoPoint_nu]
        simp [twoActEv, Proc.deviate, Function.update_of_ne, Function.update_self]
      have hnuin : nu (C.deviate .p1 m) fantasy541 (twoActEv .p1 .b ∩ twoObs .p1) = m.w .b := by
        simp only [twoObs, Finset.inter_univ]
        rw [fantasy541, twoPoint_nu]
        simp [twoActEv, Proc.deviate, Function.update_of_ne, Function.update_self]
        rw [← mul_add, hC2, mul_one]
      have hpayout : paySum (C.deviate .p1 m) fantasy541 (twoActEv .p1 .a ∩ twoObs .p1) = m.w .a * 5 := by
        simp only [twoObs, Finset.inter_univ]
        rw [fantasy541, twoPoint_paySum]
        simp [twoActEv, Proc.deviate, Function.update_of_ne, Function.update_self]
      have hpayin : paySum (C.deviate .p1 m) fantasy541 (twoActEv .p1 .b ∩ twoObs .p1) =
          m.w .b * (4 * (C .p2).w .a + (C .p2).w .b) := by
        simp only [twoObs, Finset.inter_univ]
        rw [fantasy541, twoPoint_paySum]
        simp [twoActEv, Proc.deviate, Function.update_of_ne, Function.update_self]
        ring
      have hPout : (s .p1).pr (twoActEv .p1 .a) = m.w .a := by
        have := h1 (twoActEv .p1 .a)
        rw [hnuout] at this
        simpa [twoObs, nu_univ] using this
      have hPin : (s .p1).pr (twoActEv .p1 .b) = m.w .b := by
        have := h1 (twoActEv .p1 .b)
        rw [hnuin] at this
        simpa [twoObs, nu_univ] using this
      have hVout : (s .p1).V (twoActEv .p1 .a) = 5 := by
        have := h2 (twoActEv .p1 .a) (by rw [hPout]; exact hma) (by rw [hnuout]; exact hma)
        rw [hnuout, hpayout] at this
        exact mul_right_cancel₀ hma.ne' (by linarith)
      have hVin : (s .p1).V (twoActEv .p1 .b) = 4 * (C .p2).w .a + (C .p2).w .b := by
        have := h2 (twoActEv .p1 .b) (by rw [hPin]; exact hmb) (by rw [hnuin]; exact hmb)
        rw [hnuin, hpayin] at this
        exact mul_right_cancel₀ hmb.ne' (by linarith)
      -- `T_EDT` at `p1` approves `in`, so `V(out) ≤ V(in)`
      have hAout : Act2.a ∈ APlus s twoActEv .p1 := by
        unfold APlus; rw [Finset.mem_filter, hPout]; exact ⟨Finset.mem_univ _, hma⟩
      have hmem := hT .p1 (twoPoint_queried _ _ _ .p1) ⟨.a, hAout⟩ .b hin
      rw [mem_argmaxPlus] at hmem
      have := hmem.2 .a hAout
      rw [hVout, hVin] at this
      linarith
    · cases h
  · have hb0 : (C .p1).w .b = 0 := le_antisymm (not_lt.mp hin) ((C .p1).nonneg _)
    rcases hM .p2 (twoPoint_queried _ _ _ .p2) with ⟨C', ⟨m, -, rfl⟩, hpos, -⟩ | ⟨h, -⟩
    · rw [fantasy541, twoPoint_nu] at hpos
      simp [twoObs, Proc.deviate, Function.update_of_ne, Function.update_self, hb0] at hpos
    · cases h

/-- The local self-models `(in, x)[d ↦ ½]`. Source: CA-1′(iii). Kind: D -/
def inXModel (d : Pt2) : Proc Pt2 (fun _ => Act2) ℚ := procInX.deviate d half

/-- Each `inXModel d` realizes `O_d` (in particular `ν(O₂) = 1` since `p1` plays `in`).
Source: CA-1′(iii). Kind: L -/
theorem inXModel_pos (d : Pt2) : 0 < nu (inXModel d) fantasy241 (twoObs d) := by
  cases d <;> simp [inXModel, fantasy241, twoPoint_nu, twoObs, procInX, half, Proc.deviate,
    Function.update_of_ne, Function.update_self] <;> norm_num

/-- The letter-reading states for `(in, x)`. Source: CA-1′(iii). Kind: D -/
noncomputable def inXState : Pt2 → State TwoW ℚ :=
  fun d => calibratedState (inXModel d) fantasy241 (twoObs d) (inXModel_pos d)

/-- **Under the letter reading `(in, x)` is LF masked-EDT-consistent on `fantasy241`, and
optimal**: both observations are realized by the local self-models, `V(in) = 4 > 2` at `p1`,
`V(x) = 4 > 1` at `p2`, and `value = 4` is the maximum. So the letter's failure on the
fantasy trees is existence (`fantasy541_letter_empty`), not optimality.
Source: CA-1′(iii) ("LF-letter-masked-EDT-consistent procedures have every queried
observation on-path and are `V`-optimal")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem fantasy241_letter_inX :
    MaskedEdtConsistent .LF .letter twoObs twoActEv procInX fantasy241 ∧ TOpt procInX fantasy241 := by
  refine ⟨⟨inXState, fun d _ => Or.inl ⟨inXModel d, ⟨half, half_pos, rfl⟩, inXModel_pos d,
    strictClausesAt_calibratedState twoObs _ fantasy241 inXState d (inXModel_pos d) rfl⟩,
    fun d _ _ a ha => ?_⟩, fun C' => ?_⟩
  · cases d
    · have ha' : a = .b := by
        cases a
        · simp [procInX] at ha
        · rfl
      subst ha'
      rw [mem_argmaxPlus]
      refine ⟨?_, fun b hb => ?_⟩
      · unfold APlus; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        simp only [inXState]; rw [calibratedState_pr]
        simp [inXModel, fantasy241, twoPoint_nu, twoObs, twoActEv, procInX, half, Proc.deviate,
          Function.update_of_ne, Function.update_self]
        try norm_num
      · cases b
        · simp [inXState, inXModel, calibratedState_V, fantasy241, twoPoint_nu, twoPoint_paySum,
            twoObs, twoActEv, procInX, half, Proc.deviate, Function.update_of_ne,
            Function.update_self]
          norm_num
        · exact le_rfl
    · have ha' : a = .a := by
        cases a
        · rfl
        · simp [procInX] at ha
      subst ha'
      rw [mem_argmaxPlus]
      refine ⟨?_, fun b hb => ?_⟩
      · unfold APlus; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        simp only [inXState]; rw [calibratedState_pr]
        simp [inXModel, fantasy241, twoPoint_nu, twoObs, twoActEv, procInX, half, Proc.deviate,
          Function.update_of_ne, Function.update_self]
        try norm_num
      · cases b
        · exact le_rfl
        · simp [inXState, inXModel, calibratedState_V, fantasy241, twoPoint_nu, twoPoint_paySum,
            twoObs, twoActEv, procInX, half, Proc.deviate, Function.update_of_ne,
            Function.update_self]
          norm_num
  · rw [fantasy241, twoPoint_value, twoPoint_value]
    simp only [procInX, Proc.ofFun_w]
    have h1 := (C' .p1).sum_one
    have h2 := (C' .p2).sum_one
    rw [Act2.sum_univ] at h1 h2
    have := (C' .p1).nonneg .a
    have := (C' .p1).nonneg .b
    have := (C' .p2).nonneg .a
    have := (C' .p2).nonneg .b
    simp
    nlinarith

/-! ## (v) The verdict -/

/-- **Within Appendix B's grid no variant, under either reading, yields existence and the
optimality implication together — on the named catalogue trees**: LP/GP admit the
non-optimal `δ_a` on `T₁`; GF admits the non-optimal `(out, x)` on `fantasy241`; LF under
vacuity admits the non-optimal `(out, y)` on `fantasy241`; LF under the letter admits
nothing on `fantasy541`. CA-1′(v) is a *negative* universal ("no variant … yields both
existence and the optimality implication on `𝔉`"), so one tree per variant and reading is
logically all it needs; what is not stated here is only that `t1`, `fantasy241`, `fantasy541`
lie in `𝔉` (membership in the fair class, `dp-edt-udt-fair`'s object), which is the sole
reason for the `weaker` grade.
Source: CA-1′ (dp-cf-041); [[decision-problems-v2]] Appendix B
Kind: N+
Fidelity: weaker: on the named catalogue trees, whose membership in `𝔉` is not stated
Hyps: none -/
theorem appendixB_verdict :
    (∀ r, MaskedEdtConsistent .LP r t1Obs t1ActEv procA1 t1 ∧
      MaskedEdtConsistent .GP r t1Obs t1ActEv procA1 t1) ∧ ¬ TOpt procA1 t1 ∧
    (∀ r, MaskedEdtConsistent .GF r twoObs twoActEv procOutX fantasy241) ∧
      ¬ TOpt procOutX fantasy241 ∧
    MaskedEdtConsistent .LF .vacuity twoObs twoActEv procOutY fantasy241 ∧
      ¬ TOpt procOutY fantasy241 ∧
    ¬ ∃ C, MaskedEdtConsistent .LF .letter twoObs twoActEv C fantasy541 :=
  ⟨fun r => ⟨t1_masked_plain .LP (Or.inl rfl) r, t1_masked_plain .GP (Or.inr rfl) r⟩, t1_not_tOpt,
    fantasy241_GF, fantasy241_outX_not_tOpt, fantasy241_LF_vacuity, fantasy241_outY_not_tOpt,
    fantasy541_letter_empty⟩

end Cleanroom.Decision.DpCalibLimits
