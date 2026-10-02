import Cleanroom.Decision.DpSmokingLesion.Prop11
import Cleanroom.Decision.DpCalibration.Bridge
import Cleanroom.Decision.DpCalibration.Chain

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# T3: Proposition 13 — the shared argmax, the other grades, the headline corollary

[[dp-smoking-lesion-mandate]] T3 (load-bearing 2); the statistics identities are in
`General.lean` (T3(a): `prop13_ev_eq_r1State`; T3(b): `prop13_ev_eq_r2Sia`,
`r2Real_eq_r2Sia_of_hStar`). This file adds:

* **(c) the shared argmax** (`aPlus_eq_filter_nu_pos`, `V_le_iff_r1State`, `V_le_iff_r2Sia`,
  `mem_argmaxPlus_iff_r1State`, `mem_argmaxPlus_iff_r2Sia`): at a state satisfying Definition 8's
  two clauses with `ν(O_d) > 0`, `A_d^+ = {a : ν(a ∧ O_d) > 0}`, and on it the evidential
  order is the R1-state order (under `RecordsFor` for `C`) and the R2-SIA order (under `H*`),
  as iffs of orders (never an equality of `Finset`s computed through division).
* **(d) the other grades**: limit (via `limitOCAt_imp_strictOCAt`), masked (recording for the
  self-model `C[d ↦ m]`; the R1-state referent is label-free, `deviate_deviatePure`), per-run SSC
  (`perRunSSCAt_iff_strictOCAt_of_hStar`) and per-occurrence SSC
  (`perOccSSCAt_iff_perRunSSCAt_of_count_le_one_ae`: almost-fairness on positive runs suffices,
  and `H*` supplies it).
* **(f) the headline corollary**: no act in `A_d^+` strictly beats the evidential maximiser
  under R1-state (recording) or R2-SIA (`H*`) — the textbook contrast "EDT refrains, the referent
  smokes" is well-defined at no calibrated state, for any procedure and any tree
  (`no_contrast_r1State`, `no_contrast_r2Sia`); on `slOne` every referent smokes by exactly `α`
  (`prop13_slOne_smokes_by_alpha`), at the strict grade non-vacuously only for an interior label
  (`A_d^+` is a singleton for a deterministic `C`, `aPlus_eq_singleton_of_deterministic`), and at
  the masked grade at every interior self-model (`prop13_slOne_masked_smokes_by_alpha`).
* **(e)**, the refutation of the R2-SIA / R2-real / SSC clauses under `RecordsFor` alone, is
  `Prop13Mug.lean`.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-! ## (c) `A_d^+` and the shared order -/

section argmax

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (s : ι → State Ω K)

/-- **`A_d^+ = {a : ν(a ∧ O_d) > 0}`** at a state satisfying clause 1 with `ν(O_d) > 0`.
Source: [[decision-problems-v2]] §3.1 Definition 12 (`A_d^+`) with Definition 8 clause 1;
mandate T3(c) ("prove this `L`")
Kind: L -/
theorem aPlus_eq_filter_nu_pos (hpos : 0 < nu C B (obs d)) (h1 : StrictClause1At s obs C B d) :
    APlus s actEv d = Finset.univ.filter fun a => 0 < nu C B (actEv d a ∩ obs d) := by
  ext a
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← h1 (actEv d a)]
  exact ⟨fun h => mul_pos h hpos, fun h => (mul_pos_iff_of_pos_right hpos).mp h⟩

/-- Membership in `A_d^+` as positivity of `ν(a ∧ O_d)`. Source: none: infrastructure. Kind: L -/
theorem mem_aPlus_iff (hpos : 0 < nu C B (obs d)) (h1 : StrictClause1At s obs C B d) (a : acts d) :
    a ∈ APlus s actEv d ↔ 0 < nu C B (actEv d a ∩ obs d) := by
  rw [aPlus_eq_filter_nu_pos obs actEv C B d s hpos h1]
  simp

/-- At a state satisfying both clauses, the act value of `a ∈ A_d^+` is the evidential
statistic: `V_{s_d}(a) · ν(a ∧ O_d) = paySum(a ∧ O_d)`.
Source: [[decision-problems-v2]] Definition 8 clause 2 (the hypothesis instance)
Kind: L -/
theorem V_mul_nu_eq_paySum (hpos : 0 < nu C B (obs d)) (hs : StrictClausesAt s obs C B d)
    (a : acts d) (ha : a ∈ APlus s actEv d) :
    (s d).V (actEv d a) * nu C B (actEv d a ∩ obs d) = paySum C B (actEv d a ∩ obs d) := by
  have hν := (mem_aPlus_iff obs actEv C B d s hpos hs.1 a).mp ha
  have hP : 0 < (s d).pr (actEv d a) := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and] at ha; exact ha
  exact hs.2 (actEv d a) hP hν

/-- Under recording, `a ∈ A_d^+` makes the R1-state normaliser positive.
Source: none: infrastructure. Kind: L -/
theorem r1StateNu_pos_of_mem_aPlus (hrec : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (h1 : StrictClause1At s obs C B d) (a : acts d) (ha : a ∈ APlus s actEv d) :
    0 < r1StateNu obs C B d a := by
  have hν := (mem_aPlus_iff obs actEv C B d s hpos h1 a).mp ha
  rw [nu_actEv_inter_obs_eq_deviatePure obs actEv C B d hrec a] at hν
  unfold r1StateNu
  rcases (nu_nonneg (C.deviatePure d a) B (obs d)).lt_or_eq with h | h
  · exact h
  · rw [← h, mul_zero] at hν; exact absurd hν (lt_irrefl 0)

/-- **The evidential order is the R1-state order on `A_d^+`** (under recording for `C`):
for `a, b ∈ A_d^+`, `V_{s_d}(a) ≤ V_{s_d}(b) ↔ r1Pay(a) · r1Nu(b) ≤ r1Pay(b) · r1Nu(a)`.
Source: `sl-defensible-claims.md` S1 (Proposition 13, "the argmax on `A_d^+` is shared");
mandate T3(c)
Kind: C
Fidelity: exact (iff of orders, cross-multiplied)
Hyps: (a) recording for `C`; (a) `0 < ν(O_d)`; (a) both clauses of Definition 8 at `d` -/
theorem V_le_iff_r1State (hrec : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) (a b : acts d) (ha : a ∈ APlus s actEv d)
    (hb : b ∈ APlus s actEv d) :
    (s d).V (actEv d a) ≤ (s d).V (actEv d b) ↔
      r1StatePay obs C B d a * r1StateNu obs C B d b ≤
        r1StatePay obs C B d b * r1StateNu obs C B d a := by
  have hνa := (mem_aPlus_iff obs actEv C B d s hpos hs.1 a).mp ha
  have hνb := (mem_aPlus_iff obs actEv C B d s hpos hs.1 b).mp hb
  have hra := r1StateNu_pos_of_mem_aPlus obs actEv C B d s hrec hpos hs.1 a ha
  have hrb := r1StateNu_pos_of_mem_aPlus obs actEv C B d s hrec hpos hs.1 b hb
  have eVa := V_mul_nu_eq_paySum obs actEv C B d s hpos hs a ha
  have eVb := V_mul_nu_eq_paySum obs actEv C B d s hpos hs b hb
  have e1 := prop13_ev_eq_r1State obs actEv C B d hrec a
  have e2 := prop13_ev_eq_r1State obs actEv C B d hrec b
  -- `V(a) = r1Pay(a) / r1Nu(a)`
  have hVa : (s d).V (actEv d a) = r1StatePay obs C B d a / r1StateNu obs C B d a := by
    rw [eq_div_iff hra.ne']
    have : (s d).V (actEv d a) * r1StateNu obs C B d a * nu C B (actEv d a ∩ obs d) =
        r1StatePay obs C B d a * nu C B (actEv d a ∩ obs d) := by
      calc (s d).V (actEv d a) * r1StateNu obs C B d a * nu C B (actEv d a ∩ obs d)
          = ((s d).V (actEv d a) * nu C B (actEv d a ∩ obs d)) * r1StateNu obs C B d a := by ring
        _ = paySum C B (actEv d a ∩ obs d) * r1StateNu obs C B d a := by rw [eVa]
        _ = _ := e1
    exact mul_right_cancel₀ hνa.ne' this
  have hVb : (s d).V (actEv d b) = r1StatePay obs C B d b / r1StateNu obs C B d b := by
    rw [eq_div_iff hrb.ne']
    have : (s d).V (actEv d b) * r1StateNu obs C B d b * nu C B (actEv d b ∩ obs d) =
        r1StatePay obs C B d b * nu C B (actEv d b ∩ obs d) := by
      calc (s d).V (actEv d b) * r1StateNu obs C B d b * nu C B (actEv d b ∩ obs d)
          = ((s d).V (actEv d b) * nu C B (actEv d b ∩ obs d)) * r1StateNu obs C B d b := by ring
        _ = paySum C B (actEv d b ∩ obs d) * r1StateNu obs C B d b := by rw [eVb]
        _ = _ := e2
    exact mul_right_cancel₀ hνb.ne' this
  rw [hVa, hVb, div_le_div_iff₀ hra hrb]

/-- **The evidential order is the R2-SIA order on `A_d^+`** (under `H*`): for `a, b ∈ A_d^+`,
`V_{s_d}(a) ≤ V_{s_d}(b) ↔ r2Sia(a) ≤ r2Sia(b)` (the common normaliser `∑_q R_q = ν(O_d) > 0`
cancels).
Source: `sl-defensible-claims.md` S1 (Proposition 13, the R2-SIA clause); mandate T3(c)
Kind: C
Fidelity: exact (iff of orders)
Hyps: (a) `H*`; (a) `0 < ν(O_d)`; (a) both clauses of Definition 8 at `d` -/
theorem V_le_iff_r2Sia (hH : HStar obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) (a b : acts d) (ha : a ∈ APlus s actEv d)
    (hb : b ∈ APlus s actEv d) :
    (s d).V (actEv d a) ≤ (s d).V (actEv d b) ↔ r2Sia C B d a ≤ r2Sia C B d b := by
  have hνa := (mem_aPlus_iff obs actEv C B d s hpos hs.1 a).mp ha
  have hνb := (mem_aPlus_iff obs actEv C B d s hpos hs.1 b).mp hb
  have hF : 0 < fiberMass C B d := by rw [← nu_obs_eq_fiberMass obs actEv C B d hH]; exact hpos
  have eVa := V_mul_nu_eq_paySum obs actEv C B d s hpos hs a ha
  have eVb := V_mul_nu_eq_paySum obs actEv C B d s hpos hs b hb
  have e1 := prop13_ev_eq_r2Sia obs actEv C B d hH a
  have e2 := prop13_ev_eq_r2Sia obs actEv C B d hH b
  have hVa : (s d).V (actEv d a) = r2Sia C B d a / fiberMass C B d := by
    rw [eq_div_iff hF.ne']
    have : (s d).V (actEv d a) * fiberMass C B d * nu C B (actEv d a ∩ obs d) =
        r2Sia C B d a * nu C B (actEv d a ∩ obs d) := by
      calc (s d).V (actEv d a) * fiberMass C B d * nu C B (actEv d a ∩ obs d)
          = ((s d).V (actEv d a) * nu C B (actEv d a ∩ obs d)) * fiberMass C B d := by ring
        _ = paySum C B (actEv d a ∩ obs d) * fiberMass C B d := by rw [eVa]
        _ = _ := e1
    exact mul_right_cancel₀ hνa.ne' this
  have hVb : (s d).V (actEv d b) = r2Sia C B d b / fiberMass C B d := by
    rw [eq_div_iff hF.ne']
    have : (s d).V (actEv d b) * fiberMass C B d * nu C B (actEv d b ∩ obs d) =
        r2Sia C B d b * nu C B (actEv d b ∩ obs d) := by
      calc (s d).V (actEv d b) * fiberMass C B d * nu C B (actEv d b ∩ obs d)
          = ((s d).V (actEv d b) * nu C B (actEv d b ∩ obs d)) * fiberMass C B d := by ring
        _ = paySum C B (actEv d b ∩ obs d) * fiberMass C B d := by rw [eVb]
        _ = _ := e2
    exact mul_right_cancel₀ hνb.ne' this
  rw [hVa, hVb, div_le_div_iff_of_pos_right hF]

/-- **The evidential argmax on `A_d^+` is the R1-state argmax** (under recording for `C`).
Source: `sl-defensible-claims.md` S1 ("the argmax on `A_d^+` is shared"); mandate T3(c)
Kind: C
Fidelity: exact
Hyps: (a) recording for `C`; (a) `0 < ν(O_d)`; (a) both clauses -/
theorem mem_argmaxPlus_iff_r1State (hrec : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) (a : acts d) :
    a ∈ argmaxPlus s actEv d ↔ a ∈ APlus s actEv d ∧ ∀ b ∈ APlus s actEv d,
      r1StatePay obs C B d b * r1StateNu obs C B d a ≤
        r1StatePay obs C B d a * r1StateNu obs C B d b := by
  rw [mem_argmaxPlus]
  constructor
  · rintro ⟨ha, hmax⟩
    exact ⟨ha, fun b hb => (V_le_iff_r1State obs actEv C B d s hrec hpos hs b a hb ha).mp (hmax b hb)⟩
  · rintro ⟨ha, hmax⟩
    exact ⟨ha, fun b hb => (V_le_iff_r1State obs actEv C B d s hrec hpos hs b a hb ha).mpr (hmax b hb)⟩

/-- **The evidential argmax on `A_d^+` is the R2-SIA argmax** (under `H*`).
Source: `sl-defensible-claims.md` S1; mandate T3(c)
Kind: C
Fidelity: exact
Hyps: (a) `H*`; (a) `0 < ν(O_d)`; (a) both clauses -/
theorem mem_argmaxPlus_iff_r2Sia (hH : HStar obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) (a : acts d) :
    a ∈ argmaxPlus s actEv d ↔ a ∈ APlus s actEv d ∧ ∀ b ∈ APlus s actEv d,
      r2Sia C B d b ≤ r2Sia C B d a := by
  rw [mem_argmaxPlus]
  constructor
  · rintro ⟨ha, hmax⟩
    exact ⟨ha, fun b hb => (V_le_iff_r2Sia obs actEv C B d s hH hpos hs b a hb ha).mp (hmax b hb)⟩
  · rintro ⟨ha, hmax⟩
    exact ⟨ha, fun b hb => (V_le_iff_r2Sia obs actEv C B d s hH hpos hs b a hb ha).mpr (hmax b hb)⟩

/-! ## (f) The headline corollary, general form -/

/-- **No calibrated state has the textbook contrast against R1-state, on `A_d^+`**: at a
strictly calibrated recorded point, no `a ∈ A_d^+` strictly beats an evidential maximiser `b`
under R1-state (cross-multiplied) — **with the referent's comparison taken on `A_d^+` too**, as
S1 line 20 frames it ("for every `a ∈ A_d^+` … the argmax on `A_d^+` is shared"). "EDT refrains
while R1-state smokes" is then well-defined at no calibrated state, for any procedure, on any
tree recorded for it, *in this `A_d^+` sense*. At a deterministic label the comparison ranges
over a singleton (`A_d^+ = {C(d)}`, N−): there the all-actions R1-state referent can prefer the
unplayed act — on `slOne` at `δ_refrain` it prefers smoke by `α` while `T_EDT` approves refrain
(`slOne_refrain_contrast_all_acts`) — so the stronger all-actions reading of the gloss is false
and is not what this theorem says.
Source: `sl-defensible-claims.md` S1 ("'calibrated EDT refrains, calibrated CDT smokes' is
well-defined at **no** calibrated state"); mandate T3(f), §3.5 (a universal over states)
Kind: C
Fidelity: exact (the contrast quantified over `A_d^+` on both sides, as S1 states it; weaker
than the all-actions reading, which `slOne_refrain_contrast_all_acts` refutes)
Hyps: (a) recording for `C`; (a) `StrictOCAt`; (a) `0 < ν(O_d)` -/
theorem no_contrast_r1State (hrec : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d) (a b : acts d) (ha : a ∈ APlus s actEv d)
    (hb : b ∈ argmaxPlus s actEv d) :
    ¬ (r1StatePay obs C B d b * r1StateNu obs C B d a <
        r1StatePay obs C B d a * r1StateNu obs C B d b) := by
  have h := ((mem_argmaxPlus_iff_r1State obs actEv C B d s hrec hpos (hs hpos) b).mp hb).2 a ha
  exact not_lt.mpr h

/-- **No calibrated state has the textbook contrast against R2-SIA, on `A_d^+`** (under `H*`);
the referent's comparison is taken on `A_d^+` too, and at a deterministic label it ranges over
a singleton (N−; see `no_contrast_r1State` and `slOne_refrain_contrast_all_acts`).
Source: `sl-defensible-claims.md` S1; mandate T3(f)
Kind: C
Fidelity: exact (on `A_d^+`; weaker than the all-actions reading)
Hyps: (a) `H*`; (a) `StrictOCAt`; (a) `0 < ν(O_d)` -/
theorem no_contrast_r2Sia (hH : HStar obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d) (a b : acts d) (ha : a ∈ APlus s actEv d)
    (hb : b ∈ argmaxPlus s actEv d) : ¬ (r2Sia C B d b < r2Sia C B d a) := by
  have h := ((mem_argmaxPlus_iff_r2Sia obs actEv C B d s hH hpos (hs hpos) b).mp hb).2 a ha
  exact not_lt.mpr h

/-! ## (d) The other grades -/

/-- Limit grade: the order iffs transfer through `limitOCAt_imp_strictOCAt`.
Source: `sl-defensible-claims.md` S1 ("at the strict and limit states"); mandate T3(d)
Kind: C
Fidelity: exact
Hyps: (a) `H*`; (a) `0 < ν(O_d)`; (a) `LimitOCAt` -/
theorem V_le_iff_r2Sia_of_limit [∀ d, Nonempty (acts d)] (hH : HStar obs actEv C B d)
    (hpos : 0 < nu C B (obs d)) (hs : LimitOCAt s obs C B d) (a b : acts d)
    (ha : a ∈ APlus s actEv d) (hb : b ∈ APlus s actEv d) :
    (s d).V (actEv d a) ≤ (s d).V (actEv d b) ↔ r2Sia C B d a ≤ r2Sia C B d b :=
  V_le_iff_r2Sia obs actEv C B d s hH hpos (limitOCAt_imp_strictOCAt s obs C B d hs hpos) a b ha hb

/-- A point-deviation of a point-deviation at the same point is the later one:
`(C[d ↦ m])[d ↦ a] = C[d ↦ a]`. So the R1-state referent read at a self-model is the R1-state
referent read at `C`: **R1-state is label-free**.
Source: `calibration.md` CA-12′ (the act values at `d` do not depend on `C(d)`); mandate T3(d)
Kind: L -/
theorem deviate_deviatePure (m : FinDistr K (acts d)) (a : acts d) :
    (C.deviate d m).deviatePure d a = C.deviatePure d a := by
  unfold Proc.deviatePure Proc.deviate
  funext d'
  by_cases h : d' = d
  · subst h; simp [Function.update_self]
  · simp [Function.update_of_ne h]

/-- **Masked grade**: at a state strictly calibrated to a full-support self-model `C[d ↦ m]`
(the first disjunct of Definition 9 at `d`) with the self-model recording, the evidential order
on `A_d^+` is the R1-state order read at `C` itself — the self-model drops out (CA-12′'s
label-freedom). Stated with the self-model explicit: under the vacuity reading a masked state
at a point no self-model realizes is unconstrained, so `MaskedOCAt` alone cannot carry the
conclusion.
Source: `sl-defensible-claims.md` S1 ("with recording ∀C also at masked … states"); dp-sl-2-061
(ii) (recording for the self-models); mandate T3(d)
Kind: C
Fidelity: exact (recording form: for the self-model `C[d ↦ m]`; masked = first disjunct)
Hyps: (a) recording for `C[d ↦ m]`; (a) `0 < ν_{C[d↦m]}(O_d)`; (a) the strict clauses under the
self-model -/
theorem V_le_iff_r1State_of_selfModel (m : FinDistr K (acts d))
    (hrec : RecordsFor obs actEv (C.deviate d m) B d) (hpos : 0 < nu (C.deviate d m) B (obs d))
    (hcl : StrictClausesAt s obs (C.deviate d m) B d) (a b : acts d) (ha : a ∈ APlus s actEv d)
    (hb : b ∈ APlus s actEv d) :
    (s d).V (actEv d a) ≤ (s d).V (actEv d b) ↔
      r1StatePay obs C B d a * r1StateNu obs C B d b ≤
        r1StatePay obs C B d b * r1StateNu obs C B d a := by
  have h := V_le_iff_r1State obs actEv (C.deviate d m) B d s hrec hpos hcl a b ha hb
  unfold r1StatePay r1StateNu at h ⊢
  rwa [deviate_deviatePure, deviate_deviatePure] at h

/-- **Masked grade, R2-SIA**: at a state strictly calibrated to a self-model `C[d ↦ m]` with
`H*` for the self-model, the evidential order on `A_d^+` is the R2-SIA order **read at the
self-model** (R2-SIA is not label-free: `∑_q R_q G_q` weights the nodes by the self-model's
reach).
Source: `sl-defensible-claims.md` S1; mandate T3(d) ("`H*` for the self-model for (b)")
Kind: C
Fidelity: exact
Hyps: (a) `H*` for `C[d ↦ m]`; (a) `0 < ν_{C[d↦m]}(O_d)`; (a) the strict clauses under the
self-model -/
theorem V_le_iff_r2Sia_of_selfModel (m : FinDistr K (acts d))
    (hH : HStar obs actEv (C.deviate d m) B d) (hpos : 0 < nu (C.deviate d m) B (obs d))
    (hcl : StrictClausesAt s obs (C.deviate d m) B d) (a b : acts d) (ha : a ∈ APlus s actEv d)
    (hb : b ∈ APlus s actEv d) :
    (s d).V (actEv d a) ≤ (s d).V (actEv d b) ↔
      r2Sia (C.deviate d m) B d a ≤ r2Sia (C.deviate d m) B d b :=
  V_le_iff_r2Sia obs actEv (C.deviate d m) B d s hH hpos hcl a b ha hb

/-! ### The SSC grades under `H*` -/

/-- `H*` gives Proposition 3's hypothesis `H_d`: coverage and a.s. subtree-veridicality at
every `d`-node.
Source: `sl-synthesis.md` line 20 (`H*` = Proposition 3's hypothesis); mandate T3(b)
Kind: L -/
theorem hStar_covers_and_svAS (hH : HStar obs actEv C B d) :
    Covers obs C B d ∧ ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q := by
  refine ⟨hH.1.covers obs actEv, fun q hq ℓ hℓ hpos => ?_⟩
  rw [mem_leavesBelow] at hℓ
  have hc := count_pos_of_edge B q ℓ hℓ
  rw [hq] at hc ⊢
  exact hH.2 ℓ hpos hc

/-- **Per-run SSC = strict OC under `H*`** at `d` (Proposition 3 transported).
Source: [[decision-problems-v2]] Proposition 3; `sl-defensible-claims.md` S1 ("the SSC states
under `H*`"); mandate T3(d)
Kind: C
Fidelity: exact
Hyps: (a) `H*` -/
theorem perRunSSCAt_iff_strictOCAt_of_hStar (hH : HStar obs actEv C B d) :
    PerRunSSCAt s C B d ↔ StrictOCAt s obs C B d :=
  perRunSSCAt_iff_strictOCAt obs C B s (hStar_covers_and_svAS obs actEv C B d hH).1
    (hStar_covers_and_svAS obs actEv C B d hH).2

/-- Under `H*`, every positive run meets `d` at most once.
Source: none: infrastructure (Definition 7 clause 1 + `H*`'s second clause)
Kind: L -/
theorem count_le_one_ae_of_hStar (hH : HStar obs actEv C B d) :
    ∀ ℓ, 0 < leafLaw C B ℓ → count d B ℓ ≤ 1 := by
  intro ℓ hpos
  by_cases hc : 0 < count d B ℓ
  · exact (hH.1 ℓ hpos (hH.2 ℓ hpos hc)).1.le
  · omega

/-- `𝔼[#_d 1_X] = μ({λ⊨X} ∩ occ(d))` when `#_d ≤ 1` on positive runs (the a.s. form of
`dp-calibration`'s `countMass_eq_of_almostFair`).
Source: `zoo.md` ZO-3, a.s. form; mandate T3(d) ("prove that `AlmostFair`-on-positive-runs
suffices")
Kind: L -/
theorem countMass_eq_of_count_le_one_ae (hAF : ∀ ℓ, 0 < leafLaw C B ℓ → count d B ℓ ≤ 1)
    (X : Finset Ω) : countMass C B d X = mass C B (worldEv B X ∩ occ d B) := by
  unfold countMass mass
  rw [← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · have h := hAF ℓ hpos
    rcases Nat.lt_or_ge 0 (count d B ℓ) with hc | hc
    · have h1 : count d B ℓ = 1 := by omega
      have hmem : ℓ ∈ occ d B := (mem_occ d B ℓ).mpr hc
      rw [if_pos hmem, h1]; simp
    · have h0 : count d B ℓ = 0 := by omega
      have hmem : ℓ ∉ occ d B := fun hc' => by rw [mem_occ] at hc'; omega
      rw [if_neg hmem, h0]; simp
  · rw [← hzero]; simp

/-- `𝔼[#_d r 1_X] = ∑_{{λ⊨X} ∩ occ(d)} μ r` when `#_d ≤ 1` on positive runs.
Source: `zoo.md` ZO-3, a.s. form
Kind: L -/
theorem countPay_eq_of_count_le_one_ae (hAF : ∀ ℓ, 0 < leafLaw C B ℓ → count d B ℓ ≤ 1)
    (X : Finset Ω) :
    countPay C B d X = ∑ ℓ ∈ worldEv B X ∩ occ d B, leafLaw C B ℓ * payoff B ℓ := by
  unfold countPay
  rw [← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · have h := hAF ℓ hpos
    rcases Nat.lt_or_ge 0 (count d B ℓ) with hc | hc
    · have h1 : count d B ℓ = 1 := by omega
      have hmem : ℓ ∈ occ d B := (mem_occ d B ℓ).mpr hc
      rw [if_pos hmem, h1]; simp
    · have h0 : count d B ℓ = 0 := by omega
      have hmem : ℓ ∉ occ d B := fun hc' => by rw [mem_occ] at hc'; omega
      rw [if_neg hmem, h0]; simp
  · rw [← hzero]; simp

/-- **Per-occurrence SSC = per-run SSC when `#_d ≤ 1` on positive runs** (the a.s. form of
`perRunSSCAt_iff_perOccSSCAt_of_almostFair`: almost-fairness is needed only on positive runs).
Source: `zoo.md` ZO-2, a.s. form; mandate T3(d)
Kind: C
Fidelity: stronger (a.s. hypothesis in place of `AlmostFair B`)
Hyps: (a) `#_d ≤ 1` on positive runs -/
theorem perOccSSCAt_iff_perRunSSCAt_of_count_le_one_ae
    (hAF : ∀ ℓ, 0 < leafLaw C B ℓ → count d B ℓ ≤ 1) :
    PerOccSSCAt s C B d ↔ PerRunSSCAt s C B d := by
  unfold PerOccSSCAt PerRunSSCAt PerOccClausesAt PerRunClausesAt PerRunClause1At PerRunClause2At
  simp only [countMass_eq_of_count_le_one_ae C B d hAF, countPay_eq_of_count_le_one_ae C B d hAF,
    worldEv_univ, Finset.univ_inter]

/-- **Per-occurrence SSC = per-run SSC = strict OC under `H*`** at `d`: Proposition 13's SSC
clause — the order iffs of (c) hold at both SSC states.
Source: `sl-defensible-claims.md` S1 ("at **all five** grades … the SSC states under `H*`");
mandate T3(d)
Kind: C
Fidelity: exact
Hyps: (a) `H*` -/
theorem perOccSSCAt_iff_strictOCAt_of_hStar (hH : HStar obs actEv C B d) :
    PerOccSSCAt s C B d ↔ StrictOCAt s obs C B d := by
  rw [perOccSSCAt_iff_perRunSSCAt_of_count_le_one_ae C B d s
    (count_le_one_ae_of_hStar obs actEv C B d hH)]
  exact perRunSSCAt_iff_strictOCAt_of_hStar obs actEv C B d s hH

/-! ### The headline corollary at the other grades (one line each from the iffs above) -/

/-- The no-contrast corollary against R2-SIA at the **limit** grade (on `A_d^+`).
Source: `sl-defensible-claims.md` S1 ("all five grades"); mandate T3(f)
Kind: C
Fidelity: exact (on `A_d^+`)
Hyps: (a) `H*`; (a) `LimitOCAt`; (a) `0 < ν(O_d)` -/
theorem no_contrast_r2Sia_of_limit [∀ d, Nonempty (acts d)] (hH : HStar obs actEv C B d)
    (hpos : 0 < nu C B (obs d)) (hs : LimitOCAt s obs C B d) (a b : acts d)
    (ha : a ∈ APlus s actEv d) (hb : b ∈ argmaxPlus s actEv d) :
    ¬ (r2Sia C B d b < r2Sia C B d a) :=
  no_contrast_r2Sia obs actEv C B d s hH hpos (fun _ => limitOCAt_imp_strictOCAt s obs C B d hs hpos)
    a b ha hb

/-- The no-contrast corollary against R1-state at the **masked** grade (recording for the
self-model; the referent read at `C`, label-free; on `A_d^+`).
Source: `sl-defensible-claims.md` S1; mandate T3(f)
Kind: C
Fidelity: exact (on `A_d^+`; masked = first disjunct at the self-model)
Hyps: (a) recording for `C[d ↦ m]`; (a) `0 < ν_{C[d↦m]}(O_d)`; (a) the strict clauses under the
self-model -/
theorem no_contrast_r1State_of_selfModel (m : FinDistr K (acts d))
    (hrec : RecordsFor obs actEv (C.deviate d m) B d) (hpos : 0 < nu (C.deviate d m) B (obs d))
    (hcl : StrictClausesAt s obs (C.deviate d m) B d) (a b : acts d) (ha : a ∈ APlus s actEv d)
    (hb : b ∈ argmaxPlus s actEv d) :
    ¬ (r1StatePay obs C B d b * r1StateNu obs C B d a <
        r1StatePay obs C B d a * r1StateNu obs C B d b) := by
  rw [mem_argmaxPlus] at hb
  have h := (V_le_iff_r1State_of_selfModel obs actEv C B d s m hrec hpos hcl a b ha hb.1).mp
    (hb.2 a ha)
  exact not_lt.mpr h

/-- The no-contrast corollary against R2-SIA at the **per-run SSC** grade under `H*`
(on `A_d^+`).
Source: `sl-defensible-claims.md` S1; mandate T3(f)
Kind: C
Fidelity: exact (on `A_d^+`)
Hyps: (a) `H*`; (a) `PerRunSSCAt`; (a) `0 < ν(O_d)` -/
theorem no_contrast_r2Sia_of_perRun (hH : HStar obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : PerRunSSCAt s C B d) (a b : acts d) (ha : a ∈ APlus s actEv d)
    (hb : b ∈ argmaxPlus s actEv d) : ¬ (r2Sia C B d b < r2Sia C B d a) :=
  no_contrast_r2Sia obs actEv C B d s hH hpos
    ((perRunSSCAt_iff_strictOCAt_of_hStar obs actEv C B d s hH).mp hs) a b ha hb

/-- The no-contrast corollary against R2-SIA at the **per-occurrence SSC** grade under `H*`
(on `A_d^+`).
Source: `sl-defensible-claims.md` S1; mandate T3(f)
Kind: C
Fidelity: exact (on `A_d^+`)
Hyps: (a) `H*`; (a) `PerOccSSCAt`; (a) `0 < ν(O_d)` -/
theorem no_contrast_r2Sia_of_perOcc (hH : HStar obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : PerOccSSCAt s C B d) (a b : acts d) (ha : a ∈ APlus s actEv d)
    (hb : b ∈ argmaxPlus s actEv d) : ¬ (r2Sia C B d b < r2Sia C B d a) :=
  no_contrast_r2Sia obs actEv C B d s hH hpos
    ((perOccSSCAt_iff_strictOCAt_of_hStar obs actEv C B d s hH).mp hs) a b ha hb

end argmax

/-! ## (f) on `slOne`: every referent smokes by exactly `α` -/

section slOneAlpha

variable (L : Lesion) (α β : ℚ) (C : Proc Unit (fun _ => Bool) ℚ)

/-- `paySum(m) = C(d)(m) · (α·[m] − β κ̄)` on `slOne`, with `κ̄ = ρ γ₁ + (1−ρ) γ₀`.
Source: [[decision-problems-v2]] §7.3 Proposition 12 ("computes a difference of `α`")
Kind: L -/
theorem slOne_paySum_m (m : Bool) :
    paySum C (slOne L α β) (evM m) =
      (C ()).w m * ((if m then α else 0) - β * (L.ρ * L.γ₁ + (1 - L.ρ) * L.γ₀)) := by
  rw [slOne_paySum]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, mem_evM, ticklePay]
  cases m <;> simp <;> ring

/-- **On `slOne` every referent smokes by exactly `α`**: for every procedure and every strictly
calibrated state at `⊤`, when both acts are subjectively possible,
`V_{s_d}(smoke) − V_{s_d}(refrain) = α`; and the R1-state values (`𝔼_{μ_{C[d↦a]}}[r]`,
label-free) differ by `α` for every `C`. So no calibrated state has "refrain" as the evidential
argmax while the referents have "smoke": the textbook contrast is well-defined at no
calibrated state on the recorded class.
Source: `sl-defensible-claims.md` S1 ("All of them differ by `α` and smoke"); [[decision-problems-v2]]
§7.3 Proposition 12 ("a difference of `α > 0` and smokes"); mandate T3(f)
Kind: C
Fidelity: exact on the enumerated instantiation; at a deterministic `C` the first clause is
vacuous (`A_d^+ = {C(d)}`, `aPlus_eq_singleton_of_deterministic`) — N− there, N+ at an
interior label (`prop13_slOne_instance`)
Hyps: (a) `StrictOCAt` at `⊤`; (a) both acts in `A_d^+` (first clause only) -/
theorem prop13_slOne_smokes_by_alpha (s : Unit → State TickleW ℚ)
    (hs : StrictOCAt s slObs C (slOne L α β) ()) :
    (true ∈ APlus s slActEv () → false ∈ APlus s slActEv () →
      (s ()).V (evM true) - (s ()).V (evM false) = α) ∧
    r1StateVal slObs C (slOne L α β) () true - r1StateVal slObs C (slOne L α β) () false = α := by
  have hpos : 0 < nu C (slOne L α β) (slObs ()) := by rw [slObs_apply]; exact nu_univ_pos _ _
  have hcl := hs hpos
  constructor
  · intro ht hf
    have et := V_mul_nu_eq_paySum slObs slActEv C (slOne L α β) () s hpos hcl true ht
    have ef := V_mul_nu_eq_paySum slObs slActEv C (slOne L α β) () s hpos hcl false hf
    have hνt := (mem_aPlus_iff slObs slActEv C (slOne L α β) () s hpos hcl.1 true).mp ht
    have hνf := (mem_aPlus_iff slObs slActEv C (slOne L α β) () s hpos hcl.1 false).mp hf
    simp only [slActEv_apply, slObs_apply, Finset.inter_univ] at et ef hνt hνf
    rw [slOne_paySum_m, slOne_nu_m] at et ef
    rw [slOne_nu_m] at hνt hνf
    simp only [if_true, Bool.false_eq_true, if_false] at et ef
    have ht' : (s ()).V (evM true) = α - β * (L.ρ * L.γ₁ + (1 - L.ρ) * L.γ₀) := by
      have := mul_right_cancel₀ hνt.ne' (by rw [et]; ring :
        (s ()).V (evM true) * (C ()).w true = (α - β * (L.ρ * L.γ₁ + (1 - L.ρ) * L.γ₀)) * (C ()).w true)
      exact this
    have hf' : (s ()).V (evM false) = 0 - β * (L.ρ * L.γ₁ + (1 - L.ρ) * L.γ₀) := by
      have := mul_right_cancel₀ hνf.ne' (by rw [ef]; ring :
        (s ()).V (evM false) * (C ()).w false = (0 - β * (L.ρ * L.γ₁ + (1 - L.ρ) * L.γ₀)) * (C ()).w false)
      exact this
    rw [ht', hf']; ring
  · unfold r1StateVal r1StatePay r1StateNu
    simp only [slObs_apply, nu_univ, div_one]
    have key : ∀ (C' : Proc Unit (fun _ => Bool) ℚ) (m : Bool), C' () = FinDistr.pure m →
        paySum C' (slOne L α β) Finset.univ =
          (if m then α else 0) - β * (L.ρ * L.γ₁ + (1 - L.ρ) * L.γ₀) := by
      intro C' m hC'
      rw [paySum_eq_sum_ite, slOne_sum]
      simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, slOne_payoff, Finset.mem_univ,
        if_true, hC', FinDistr.pure_w, ticklePay]
      cases m <;> simp <;> ring
    rw [key _ true (Proc.deviate_same C () _), key _ false (Proc.deviate_same C () _)]
    simp

/-- **N+ for the `α`-gap at the strict grade**: at the FDT numbers and `C(d) = ½`, both acts
are in `A_d^+` at the strictly calibrated state and `V(smoke) − V(refrain) = 1000`; the values
are `V(smoke) = 1000 − 500 000 = −499 000` and `V(refrain) = −500 000`.
Source: mandate T3(f) ("N+ at interior `q`")
Kind: N+ -/
theorem prop13_slOne_instance :
    let C₀ := procBool (1/2) (by norm_num) (by norm_num)
    let B₀ := slOne Lesion.fdt 1000 1000000
    let s₀ : Unit → State TickleW ℚ := fun _ => calibratedState C₀ B₀ Finset.univ (nu_univ_pos _ _)
    true ∈ APlus s₀ slActEv () ∧ false ∈ APlus s₀ slActEv () ∧
      (s₀ ()).V (evM true) = -499000 ∧ (s₀ ()).V (evM false) = -500000 := by
  intro C₀ B₀ s₀
  have hp : ∀ m, (s₀ ()).pr (evM m) = 1/2 := by
    intro m
    simp only [s₀, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, B₀, C₀]
    rw [slOne_nu_m]; cases m <;> simp [procBool]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, slActEv_apply, hp]; norm_num
  · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, slActEv_apply, hp]; norm_num
  · simp only [s₀, calibratedState_V, Finset.inter_univ, B₀, C₀]
    rw [slOne_paySum_m, slOne_nu_m]; simp [procBool, Lesion.fdt]; norm_num
  · simp only [s₀, calibratedState_V, Finset.inter_univ, B₀, C₀]
    rw [slOne_paySum_m, slOne_nu_m]; simp [procBool, Lesion.fdt]; norm_num

/-- **N+ for the R2-SIA clause on an `H*` tree**: on `slOne` at the FDT numbers and `C(d) = ½`
(`H*` by `slOne_hStar`), `r2Sia(smoke) = −499 000`, `r2Sia(refrain) = −500 000` and
`fiberMass = 1` — the same values as the evidential ones in `prop13_slOne_instance`, as
Proposition 13 says. (E13 and E2a, cited before audit r1, do not inhabit `H*`: their R2-SIA
values are contrast computations on non-recording trees.)
Source: `sl-defensible-claims.md` S1 (Proposition 13, R2-SIA clause); audit r1 adversarial B1
Kind: N+ -/
theorem slOne_r2Sia_half :
    r2Sia (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) () true =
        -499000 ∧
    r2Sia (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) () false =
        -500000 ∧
    fiberMass (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) () = 1 := by
  have hH := slOne_hStar Lesion.fdt 1000 1000000 (procBool (1/2) (by norm_num) (by norm_num))
  have ht := paySum_actEv_inter_obs_eq_mul_r2Sia slObs slActEv _ _ () hH true
  have hf := paySum_actEv_inter_obs_eq_mul_r2Sia slObs slActEv _ _ () hH false
  simp only [slActEv_apply, slObs_apply, Finset.inter_univ] at ht hf
  rw [slOne_paySum_m] at ht hf
  have hw : ((procBool (1/2) (by norm_num) (by norm_num) : Proc Unit (fun _ => Bool) ℚ) ()).w true
      = 1/2 := by simp [procBool]
  have hw' : ((procBool (1/2) (by norm_num) (by norm_num) : Proc Unit (fun _ => Bool) ℚ) ()).w false
      = 1/2 := by simp [procBool]; norm_num
  rw [hw] at ht
  rw [hw'] at hf
  have hρ : Lesion.fdt.ρ = 1/2 := rfl
  have hγ₁ : Lesion.fdt.γ₁ = 99/100 := rfl
  have hγ₀ : Lesion.fdt.γ₀ = 1/100 := rfl
  rw [hρ, hγ₁, hγ₀] at ht hf
  norm_num at ht hf
  refine ⟨by linarith, by linarith, ?_⟩
  have h := nu_obs_eq_fiberMass slObs slActEv _ _ () hH
  rw [slObs_apply, nu_univ] at h
  exact h.symm

/-- **`prop13_ev_eq_r2Sia` instantiated on an `H*` tree with its numbers**: on `slOne` at the
FDT numbers and `C(d) = ½`, `paySum(smoke) · fiberMass = r2Sia(smoke) · ν(smoke)` reads
`(−249 500) · 1 = (−499 000) · ½`.
Source: `sl-defensible-claims.md` S1 (Proposition 13, R2-SIA clause); audit r1 adversarial B1
Kind: N+ -/
theorem slOne_prop13_r2Sia_instance :
    paySum (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) (evM true) *
        fiberMass (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) () =
      r2Sia (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) () true *
        nu (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) (evM true) ∧
    paySum (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) (evM true) =
        -249500 ∧
    nu (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) (evM true) =
        1/2 := by
  have hH := slOne_hStar Lesion.fdt 1000 1000000 (procBool (1/2) (by norm_num) (by norm_num))
  have h := prop13_ev_eq_r2Sia slObs slActEv _ _ () hH true
  simp only [slActEv_apply, slObs_apply, Finset.inter_univ] at h
  refine ⟨h, ?_, ?_⟩
  · rw [slOne_paySum_m]; norm_num [procBool, Lesion.fdt]
  · rw [slOne_nu_m]; simp [procBool]

/-- **The `α`-gap at the masked grade, non-vacuously for every procedure**: at the state
strictly calibrated to an interior self-model `C[d ↦ m]` on `slOne` (a masked witness for `C`
by `maskedOCAt_calibratedState`), both acts are subjectively possible and
`V(smoke) − V(refrain) = α`. This is the non-vacuous "smokes by `α`" for a deterministic `C`
(dp-sl-014): masked, at an interior self-model.
Source: [[decision-problems-v2]] §7.3 Proposition 12 ("masked-calibrated instantiations … smokes");
`sl-defensible-claims.md` S5 rider (i); mandate T3(d), T6(b)
Kind: C
Fidelity: exact (masked = first disjunct at the self-model `m`)
Hyps: (a) `m` full-support -/
theorem prop13_slOne_masked_smokes_by_alpha (m : FinDistr ℚ Bool) (hm : ∀ a, 0 < m.w a) :
    let s₀ : Unit → State TickleW ℚ :=
      fun _ => calibratedState (C.deviate () m) (slOne L α β) Finset.univ (nu_univ_pos _ _)
    MaskedOCAt s₀ slObs C (slOne L α β) () ∧ true ∈ APlus s₀ slActEv () ∧
      false ∈ APlus s₀ slActEv () ∧ (s₀ ()).V (evM true) - (s₀ ()).V (evM false) = α := by
  intro s₀
  have hstrict : StrictOCAt s₀ slObs (C.deviate () m) (slOne L α β) () :=
    strictOCAt_calibratedState slObs _ _ s₀ () _ rfl
  have hp : ∀ a, (s₀ ()).pr (evM a) = m.w a := by
    intro a
    simp only [s₀, calibratedState_pr, Finset.inter_univ, nu_univ, div_one]
    rw [slOne_nu_m, Proc.deviate_same]
  have ht : true ∈ APlus s₀ slActEv () := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, slActEv_apply, hp]; exact hm true
  have hf : false ∈ APlus s₀ slActEv () := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, slActEv_apply, hp]; exact hm false
  refine ⟨maskedOCAt_calibratedState slObs C (slOne L α β) s₀ () m hm _ rfl, ht, hf, ?_⟩
  exact (prop13_slOne_smokes_by_alpha L α β (C.deviate () m) s₀ hstrict).1 ht hf

/-- The strictly calibrated state of `δ_refrain` on `slOne` at the FDT numbers.
Source: none: infrastructure (audit r1 adversarial N1, probe `ContrastAllActs`)
Kind: D -/
def slOneRefrainState : Unit → State TickleW ℚ :=
  fun _ => calibratedState procRefrain (slOne Lesion.fdt 1000 1000000) Finset.univ (nu_univ_pos _ _)

/-- **The all-actions reading of "no contrast" is false, and the `A_d^+` reading is N− at a
deterministic label**: at `δ_refrain`'s strict state on `slOne` (FDT numbers) the state is
strictly calibrated, `A_d^+ = {refrain}`, `T_EDT` approves it, yet the label-free R1-state
referent read over *all* actions prefers smoke by `α = 1000`
(`r1StateVal(smoke) − r1StateVal(refrain) = 1000`); and the `no_contrast_r1State` comparison
ranges over the singleton (`∀ a ∈ A_d^+, ∀ b ∈ argmaxPlus, a = b`). So the textbook contrast
*is* realized at a calibrated recorded state in the all-actions sense, and `no_contrast_*`
exclude it only by restricting the referent's comparison to `A_d^+` — the sense S1 line 20
states. Disclosure witness for the `no_contrast_*` rows.
Source: `sl-defensible-claims.md` S1 line 20 (the `A_d^+` quantifier); dp-sl-014 (the strict
grade's vacuity at deterministic labels); audit r1 adversarial N1
Kind: N− -/
theorem slOne_refrain_contrast_all_acts :
    StrictOCAt slOneRefrainState slObs procRefrain (slOne Lesion.fdt 1000 1000000) () ∧
    APlus slOneRefrainState slActEv () = {false} ∧
    TEdtAt slOneRefrainState slActEv procRefrain () ∧
    r1StateVal slObs procRefrain (slOne Lesion.fdt 1000 1000000) () true -
      r1StateVal slObs procRefrain (slOne Lesion.fdt 1000 1000000) () false = 1000 ∧
    (∀ a ∈ APlus slOneRefrainState slActEv (),
      ∀ b ∈ argmaxPlus slOneRefrainState slActEv (), a = b) := by
  have hpos : 0 < nu procRefrain (slOne Lesion.fdt 1000 1000000) (slObs ()) := by
    rw [slObs_apply]; exact nu_univ_pos _ _
  have hs : StrictOCAt slOneRefrainState slObs procRefrain (slOne Lesion.fdt 1000 1000000) () :=
    strictOCAt_calibratedState slObs procRefrain _ slOneRefrainState () _ rfl
  obtain ⟨hA, hT⟩ := tEdtAt_of_deterministic_recorded slOneRefrainState slActEv slObs procRefrain
    (slOne Lesion.fdt 1000 1000000) false rfl (slOne_recordsFor Lesion.fdt 1000 1000000 procRefrain)
    hpos hs
  refine ⟨hs, hA, hT,
    (prop13_slOne_smokes_by_alpha Lesion.fdt 1000 1000000 procRefrain slOneRefrainState hs).2, ?_⟩
  intro a ha b hb
  have hb' : b ∈ APlus slOneRefrainState slActEv () :=
    argmaxPlus_subset slOneRefrainState slActEv () hb
  rw [hA, Finset.mem_singleton] at ha hb'
  rw [ha, hb']

end slOneAlpha

end Cleanroom.Decision.DpSmokingLesion
