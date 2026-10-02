import Cleanroom.Decision.DpCalibLimits.Zo1

/-!
# T12 — Per-run SSC with a full-support self-model on `TB(θ)`

[[dp-calib-limits-mandate]] T12 (dp-sl-075, P11 §A4 / P11-12′(e), synthesis §5.4 item 10).

**`tbTheta θ`** (P11's forced-crossing tree `TB(θ, 0, ·)`): a chance root; with probability `θ`
the run reaches the world `bot` with payoff `−10` (the crossing is *forced*: no `d`-node on that
branch — rendered here as a dummy point `forced` both of whose edges lead to that leaf, so the
tree has a uniform shape), with probability `1 − θ` the point `d` is queried (`cross ↦ 10`,
`not ↦ 0`); `O_d = ⊤`; act events by the world's act coordinate (`cross = {bot, topCross}`,
`not = {topNot}`). `occ(d)` is the `1 − θ` branch while `O_d = ⊤` covers both, so the tree does
not record at `d`. At `C = δ_not`:

* **(i) per-run SSC alone** (`tb_perRun_not_approved`): `P_{s_d}(cross)·μ(occ) = μ(cross ∩ occ)
  = 0`, so `A_d^+ = {not}` and `T_EDT` approves `not` vacuously (P11-12′(e)).
* **(ii) with a full-support self-model** (`tb_perRunMasked_rejects`): inside `occ(d)` the
  act-conditional values are `V(cross) = 10 > 0 = V(not)` for every `m`, so `T_EDT` at the
  combined state rejects `not` (and `argmax = {cross}`) at every self-model.
* **(iii) the contrast** (`tb_masked_flip`): the event-conditioned masked state (Definition 9
  at `O = ⊤`) has `V_s(cross) = (−10θ + 10(1−θ)m)/(θ + (1−θ)m)`, whose sign flips at
  `m = θ/(1−θ)`: `V(cross) < 0 = V(not)` when `(1−θ)m < θ` and `V(cross) > 0` when
  `θ < (1−θ)m`.

`Fidelity: exact on TB(θ)` up to the dummy point; the tree is not Troll Bridge (P11's
register: "reproduced on TB(θ)", never CONFIRMED). T12(c) (mug1) not attempted.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- The points of `TB(θ)`: `d` (the live query) and `forced` (the forced crossing, a dummy point
both of whose edges lead to the forced leaf). Source: P11 line 57; mandate T12(b). Kind: D -/
inductive TbPt : Type
  | d
  | forced
  deriving DecidableEq, Fintype

instance : Nonempty TbPt := ⟨.d⟩

/-- The worlds of `TB(θ)`: `bot` (forced crossing, `−10`), `topCross` (`10`), `topNot` (`0`).
Source: P11 line 57. Kind: D -/
inductive TbW : Type
  | bot
  | topCross
  | topNot
  deriving DecidableEq, Fintype

/-- The point met on branch `i`: `forced` on `0`, `d` on `1`. Kind: D. Source: mandate T12(b). -/
def tbPt (i : Fin 2) : TbPt := if i = 0 then .forced else .d

/-- The leaf world on branch `i` after act `x` (`a` = cross, `b` = not).
Kind: D. Source: mandate T12(b). -/
def tbW (i : Fin 2) (x : Act2) : TbW :=
  if i = 0 then .bot else (if x = .a then .topCross else .topNot)

/-- The payoffs: forced `−10`; `cross ↦ 10`, `not ↦ 0`. Kind: D. Source: P11 line 57. -/
def tbPay (i : Fin 2) (x : Act2) : ℚ :=
  if i = 0 then -10 else (if x = .a then 10 else 0)

/-- **`TB(θ)`**: with probability `θ` the forced branch, with `1 − θ` the `d`-node. The dummy
point `forced` is *queried* (`queried (tbTheta θ)` contains it), so a `∀ d ∈ queried` statement
on this tree would see it; every T12 statement is "at `d`" and none reads it.
Source: P11 line 57 (`TB(θ, 0, ·)`); mandate T12(b)
Kind: D
Fidelity: variant: the forced branch carries a dummy (queried) point with both edges to the
forced leaf -/
def tbTheta (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : Tree TbW TbPt (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin θ h0 h1) fun i =>
    .decision (tbPt i) fun x => .leaf (tbW i x) (tbPay i x)

/-- `O_d = ⊤` (and `⊤` at the dummy point). Source: P11. Kind: D -/
def tbObs : TbPt → Finset TbW := fun _ => Finset.univ

/-- Action events by the world's act coordinate: `cross = {bot, topCross}`, `not = {topNot}`.
The dummy point `forced` gets the same events as `d` (the match ignores the point); harmless, since
no T12 statement reads the events at `forced` (see `tbTheta`).
Source: P11 §A4; mandate T12(b) ("act events by the world's act coordinate"). Kind: D -/
def tbActEv : (p : TbPt) → Act2 → Finset TbW
  | _, .a => {.bot, .topCross}
  | _, .b => {.topNot}

/-- `C = δ_not` at `d` (and `δ_a` at the dummy point). Source: P11-12′(e) (`q = 0`). Kind: D -/
def tbProc : Proc TbPt (fun _ => Act2) ℚ
  | .d => FinDistr.pure .b
  | .forced => FinDistr.pure .a

/-- A sum over the leaves of `TB(θ)`. Source: none: infrastructure. Kind: L -/
theorem tb_sum (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (f : (tbTheta θ h0 h1).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ x : Act2, f ⟨i, x, ()⟩ := by
  unfold tbTheta at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

section masses

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (m : FinDistr ℚ Act2)

local macro "tb_eval" : tactic =>
  `(tactic| (simp [tbTheta, leafLaw, tbPt, tbW, tbPay, tbObs, tbActEv, tbProc, count, occ, Fin.sum_univ_two, Act2.sum_univ, FinDistr.coin, Proc.deviate, Function.update_of_ne, Function.update_self]; try ring))

/-- The run-space masses under `C[d ↦ m]`: `μ(occ) = 1 − θ`, `μ(cross ∩ occ) = (1−θ) m(a)`,
`μ(not ∩ occ) = (1−θ) m(b)`, and the payoff masses `10(1−θ)m(a)`, `0`.
Source: P11 §A4; mandate T12(b). Kind: L -/
theorem tb_occ_masses :
    mass (tbProc.deviate .d m) (tbTheta θ h0 h1) (occ .d (tbTheta θ h0 h1)) = 1 - θ ∧
    mass (tbProc.deviate .d m) (tbTheta θ h0 h1)
        (worldEv (tbTheta θ h0 h1) (tbActEv .d .a) ∩ occ .d (tbTheta θ h0 h1)) = (1 - θ) * m.w .a ∧
    mass (tbProc.deviate .d m) (tbTheta θ h0 h1)
        (worldEv (tbTheta θ h0 h1) (tbActEv .d .b) ∩ occ .d (tbTheta θ h0 h1)) = (1 - θ) * m.w .b ∧
    (∑ ℓ ∈ worldEv (tbTheta θ h0 h1) (tbActEv .d .a) ∩ occ .d (tbTheta θ h0 h1),
        leafLaw (tbProc.deviate .d m) (tbTheta θ h0 h1) ℓ * payoff (tbTheta θ h0 h1) ℓ) =
      10 * ((1 - θ) * m.w .a) ∧
    (∑ ℓ ∈ worldEv (tbTheta θ h0 h1) (tbActEv .d .b) ∩ occ .d (tbTheta θ h0 h1),
        leafLaw (tbProc.deviate .d m) (tbTheta θ h0 h1) ℓ * payoff (tbTheta θ h0 h1) ℓ) = 0 := by
  have hsum := m.sum_one
  rw [Act2.sum_univ] at hsum
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [mass, worldEv, occ, ← Finset.filter_and, Finset.sum_filter]
     rw [tb_sum]
     tb_eval) <;>
    linear_combination (1 - θ) * hsum

/-- The event masses under `C = δ_not` (`m = δ_b`) on the run space.
Source: P11-12′(e). Kind: L -/
theorem tb_occ_masses_pure :
    mass tbProc (tbTheta θ h0 h1) (occ .d (tbTheta θ h0 h1)) = 1 - θ ∧
    mass tbProc (tbTheta θ h0 h1)
        (worldEv (tbTheta θ h0 h1) (tbActEv .d .a) ∩ occ .d (tbTheta θ h0 h1)) = 0 := by
  have hself : tbProc.deviate .d (tbProc .d) = tbProc := Function.update_eq_self _ _
  obtain ⟨h1', h2', -, -, -⟩ := tb_occ_masses θ h0 h1 (tbProc .d)
  rw [hself] at h1' h2'
  refine ⟨h1', ?_⟩
  rw [h2']; simp [tbProc]

end masses

section verdicts

variable (θ : ℚ) (h0 : 0 < θ) (h1 : θ < 1)

/-- **(i) Per-run SSC alone approves `δ_not` vacuously**: any state satisfying the per-run
clauses at `d` under `δ_not` has `P_s(cross) = 0` (since `μ(cross ∩ occ) = 0` and
`μ(occ) = 1 − θ > 0`), so `A_d^+ ⊆ {not}` and `T_EDT` approves `not`.
Source: P11-12′(e) ("per-run SSC alone: `P_{s_d}(cross)·μ(occ) = μ(cross ∩ occ) = 0`, so
`A_d^+ = {not}` and `T_EDT` approves `not` vacuously")
Kind: C (clause 1 at one event plus `APlus`/`argmaxPlus` bookkeeping; regraded in repair round 2, fidelity N5)
Fidelity: exact on `TB(θ)`
Hyps: (a) `PerRunClausesAt` under `δ_not` -/
theorem tb_perRun_not_approved (s : TbPt → State TbW ℚ)
    (hs : PerRunClausesAt s tbProc (tbTheta θ h0.le h1.le) .d) :
    (s .d).pr (tbActEv .d .a) = 0 ∧ TEdtAt s tbActEv tbProc .d := by
  obtain ⟨hocc, hcross⟩ := tb_occ_masses_pure θ h0.le h1.le
  have hP : (s .d).pr (tbActEv .d .a) = 0 := by
    have := hs.1 (tbActEv .d .a)
    rw [hocc, hcross] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  refine ⟨hP, fun _ a ha => ?_⟩
  have ha' : a = .b := by
    cases a
    · simp [tbProc] at ha
    · rfl
  subst ha'
  have hAplus : ∀ b, b ∈ APlus s tbActEv .d → b = .b := fun b hb => by
    unfold APlus at hb; rw [Finset.mem_filter] at hb
    cases b
    · rw [hP] at hb; exact absurd hb.2 (lt_irrefl 0)
    · rfl
  rw [mem_argmaxPlus]
  refine ⟨?_, fun b hb => ?_⟩
  · -- `not` is in `A_d^+` (it is the only candidate and `A_d^+` is nonempty by the hypothesis)
    obtain ⟨b, hb⟩ := ‹(APlus s tbActEv .d).Nonempty›
    have := hAplus b hb; subst this; exact hb
  · have := hAplus b hb; subst this; exact le_rfl

/-- **(ii) Per-run SSC with a full-support self-model rejects `δ_not`**: for any full-support
`m`, the per-run state of `C[d ↦ m]` has `P(cross) = m(a) > 0`, `P(not) = m(b) > 0`,
`V(cross) = 10`, `V(not) = 0`, so `argmax = {cross}` and `T_EDT` rejects `not`.
Source: P11 §A4 ("inside `occ(d)` the act-conditional values are `V(cross) = 10 > 0 = V(not)`
for every `m`"); dp-sl-075
Kind: P
Fidelity: exact on `TB(θ)`
Hyps: (a) `PerRunSSCMaskedAt` -/
theorem tb_perRunMasked_rejects (s : TbPt → State TbW ℚ)
    (hs : PerRunSSCMaskedAt tbProc (tbTheta θ h0.le h1.le) s .d) :
    argmaxPlus s tbActEv .d = {.a} ∧ ¬ TEdtAt s tbActEv tbProc .d := by
  obtain ⟨m, hm, -, hcl⟩ := hs
  obtain ⟨hocc, hcross, hnot, hpayc, hpayn⟩ := tb_occ_masses θ h0.le h1.le m
  have h1θ : (0 : ℚ) < 1 - θ := by linarith
  have hPa : (s .d).pr (tbActEv .d .a) = m.w .a := by
    have := hcl.1 (tbActEv .d .a)
    rw [hocc, hcross] at this
    exact mul_right_cancel₀ h1θ.ne' (by linarith)
  have hPb : (s .d).pr (tbActEv .d .b) = m.w .b := by
    have := hcl.1 (tbActEv .d .b)
    rw [hocc, hnot] at this
    exact mul_right_cancel₀ h1θ.ne' (by linarith)
  have hVa : (s .d).V (tbActEv .d .a) = 10 := by
    have := hcl.2 (tbActEv .d .a) (by rw [hPa]; exact hm .a)
      (by rw [hcross]; exact mul_pos h1θ (hm .a))
    rw [hcross, hpayc] at this
    exact mul_right_cancel₀ (mul_pos h1θ (hm .a)).ne' (by linarith)
  have hVb : (s .d).V (tbActEv .d .b) = 0 := by
    have := hcl.2 (tbActEv .d .b) (by rw [hPb]; exact hm .b)
      (by rw [hnot]; exact mul_pos h1θ (hm .b))
    rw [hnot, hpayn] at this
    exact (mul_eq_zero.mp this).resolve_right (mul_pos h1θ (hm .b)).ne'
  have hmax : argmaxPlus s tbActEv .d = {.a} := by
    have hmema : Act2.a ∈ APlus s tbActEv .d := by
      unfold APlus; rw [Finset.mem_filter, hPa]; exact ⟨Finset.mem_univ _, hm .a⟩
    have hmemb : Act2.b ∈ APlus s tbActEv .d := by
      unfold APlus; rw [Finset.mem_filter, hPb]; exact ⟨Finset.mem_univ _, hm .b⟩
    ext x
    rw [mem_argmaxPlus, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      cases x
      · rfl
      · have := h .a hmema; rw [hVa, hVb] at this; norm_num at this
    · rintro rfl
      refine ⟨hmema, fun b _ => ?_⟩
      cases b
      · exact le_rfl
      · rw [hVa, hVb]; norm_num
  refine ⟨hmax, fun hT => ?_⟩
  have := hT ⟨.a, argmaxPlus_subset _ _ _ (by rw [hmax]; exact Finset.mem_singleton_self _)⟩ .b
    (by simp [tbProc])
  rw [hmax, Finset.mem_singleton] at this
  cases this

/-- The event-conditioned (Definition 9, `O = ⊤`) masked state of `C[d ↦ m]`.
Source: P11-11′; mandate T12(b)(iii). Kind: D -/
noncomputable def tbMaskedState (m : FinDistr ℚ Act2) : State TbW ℚ :=
  calibratedState (tbProc.deviate .d m) (tbTheta θ h0.le h1.le) Finset.univ (nu_univ_pos _ _)

/-- `ν` and `paySum` of the cross event under `C[d ↦ m]` on `TB(θ)`: `θ + (1−θ)m(a)` and
`−10θ + 10(1−θ)m(a)`. Source: P11-11′. Kind: L -/
theorem tb_cross_event (m : FinDistr ℚ Act2) :
    nu (tbProc.deviate .d m) (tbTheta θ h0.le h1.le) (tbActEv .d .a) = θ + (1 - θ) * m.w .a ∧
    paySum (tbProc.deviate .d m) (tbTheta θ h0.le h1.le) (tbActEv .d .a) =
      -10 * θ + 10 * ((1 - θ) * m.w .a) := by
  constructor
  · rw [nu_eq_sum, tb_sum]
    simp [tbTheta, leafLaw, tbPt, tbW, tbActEv, tbProc, Fin.sum_univ_two, Act2.sum_univ,
      FinDistr.coin, Proc.deviate, Function.update_of_ne, Function.update_self]
    try ring
  · rw [paySum_eq_sum_ite, tb_sum]
    simp [tbTheta, leafLaw, tbPt, tbW, tbPay, tbActEv, tbProc, Fin.sum_univ_two, Act2.sum_univ,
      FinDistr.coin, Proc.deviate, Function.update_of_ne, Function.update_self]
    try ring

/-- **(iii) The contrast — the event-conditioned masked verdict flips at `m = θ/(1−θ)`**:
`V_s(cross) = (−10θ + 10(1−θ)m)/(θ + (1−θ)m)` is negative when `(1−θ)m < θ` and positive
when `θ < (1−θ)m`, while `V_s(not) = 0`; so Definition 9 at `O = ⊤` approves `δ_not` on one
side and rejects it on the other, unlike the per-run masked state which rejects it at every `m`.
Source: P11-11′, P11-12′(f) ("its verdict flips at `m = q* = θ/(1−θ)`")
Kind: P
Fidelity: exact on `TB(θ)`
Hyps: (a) `m` full-support, (a) the side of `q*` -/
theorem tb_masked_flip (m : FinDistr ℚ Act2) (hm : ∀ a, 0 < m.w a) :
    ((1 - θ) * m.w .a < θ → (tbMaskedState θ h0 h1 m).V (tbActEv .d .a) < 0) ∧
    (θ < (1 - θ) * m.w .a → 0 < (tbMaskedState θ h0 h1 m).V (tbActEv .d .a)) ∧
    (tbMaskedState θ h0 h1 m).V (tbActEv .d .b) = 0 := by
  obtain ⟨hnu, hpay⟩ := tb_cross_event θ h0 h1 m
  have hden : 0 < θ + (1 - θ) * m.w .a := by
    have := mul_nonneg (by linarith : (0 : ℚ) ≤ 1 - θ) (hm .a).le
    linarith
  refine ⟨fun hlt => ?_, fun hgt => ?_, ?_⟩
  · simp only [tbMaskedState, calibratedState_V, Finset.inter_univ]
    rw [hnu, hpay]
    apply div_neg_of_neg_of_pos _ hden
    linarith
  · simp only [tbMaskedState, calibratedState_V, Finset.inter_univ]
    rw [hnu, hpay]
    apply div_pos _ hden
    linarith
  · simp only [tbMaskedState, calibratedState_V, Finset.inter_univ]
    rw [paySum_eq_sum_ite, tb_sum]
    simp [tbTheta, leafLaw, tbPt, tbW, tbPay, tbActEv, tbProc, Fin.sum_univ_two, Act2.sum_univ,
      FinDistr.coin, Proc.deviate, Function.update_of_ne, Function.update_self]

end verdicts

end Cleanroom.Decision.DpCalibLimits
