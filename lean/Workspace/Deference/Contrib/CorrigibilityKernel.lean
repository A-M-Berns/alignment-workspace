/-
# The corrigibility kernel, phase 1: adapter lemmas

Round `projects/deference/rounds/2026-09-26-corrigibility-kernel/`
(`prompts/2026-09-26-corrigibility-kernel/PROMPT.md`).

Phase 1 proves only the adapters the kernel's realization maps need; the headline file,
its witness and the registrations are phase 2's, after the maintainer's rulings.  Nothing
here changes a landed definition: every object below is stated over the landed ones.

**§1 The history evaluation, parametric in the evaluation schedule.**  `VJ` (the
schedule-weighted decision score), `decScore_of_not_legit`, `VJ_mem`, `VJ_legit`,
`VJ_legit_mem`, `VJ_compromised_mem`; `SJ` (the objective `V_J − ϖ·N_J`).

**§2 The hierarchy under certainty.**  `SJ_legit_mem`, `SJ_compromised_mem`,
`SJ_violation_le`, `hierarchy_under_certainty`; the worked parameters and one evaluation
time as the witness (`Witness.band`, `Witness.once`, `Witness.params`,
`Witness.hierarchy_instance`).

**§3 The fidelity predicate over the landed violations.**  `Faithful`, `NJ`,
`faithful_iff_NJ_zero`.

**§4 Box 1 on one model.**  `outcome_scorer_margin`, `outcome_scorer_fully_updated`,
`outcomeRes2_le_calibration`, `fidelity_scorer_margin`, `box1_one_model`.

**§5 The permission layer demoted.**  `kernelEval`, `forecast_zero_le_window`,
`permission_layer_slack`, `gate_zero_dominated`.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.AfterCompromise

namespace Workspace.Deference.Contrib.CorrigibilityKernel

open Finset
open Workspace.Deference.Contrib.AfterCompromise
open Workspace.Deference.Contrib.BRIACorrigibility
open Workspace.Deference.Contrib.AuthorityModule
open Workspace.Deference.Contrib.DecisionComponent
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem (score Allocation)
open Workspace.Deference.Contrib.ProtectedAuthority (outcomeRes2 outcomeRes2_approve
  outcomeRes2_decline)
open Workspace.Deference.Contrib.Corrigibilization

/-! ## 1. The history evaluation, parametric in the evaluation schedule -/

section Evaluation

variable (B : Band) (φ : ℝ → ℝ)

/-- **`V_J`**: the evaluation of a history under an evaluation schedule `Wt`.  At each
evaluation time `t` the decision score is her value when the period and the evaluation's
formation are both legitimate and the band's score by the source in force otherwise
(`decScore`); the schedule weights the times.  The single evaluation is the point mass. -/
noncomputable def VJ {T : ℕ} (Wt : Weighting T) (traj eval : ℕ → Bool) (V : ℕ → ℝ)
    (src : ℕ → Source) : ℝ :=
  mixScore Wt (fun t => decScore B φ (traj t) (eval t) (V t) (src t))

/-- The score of a period not legitimate in both senses is the band's. -/
theorem decScore_of_not_legit (traj eval : Bool) (h : ¬ (traj = true ∧ eval = true)) (V : ℝ)
    (src : Source) : decScore B φ traj eval V src = bandScore B φ src := by
  unfold decScore
  cases traj <;> cases eval <;> simp_all

/-- `V_J` lies in `[w_lo, D]` under every schedule. -/
theorem VJ_mem (hφ : B.BandMap φ) {T : ℕ} (Wt : Weighting T) (traj eval : ℕ → Bool)
    (V : ℕ → ℝ) (hV : ∀ t, 0 ≤ V t ∧ V t ≤ B.D) (src : ℕ → Source)
    (hs : ∀ t, (src t).Valid B) :
    B.wlo ≤ VJ B φ Wt traj eval V src ∧ VJ B φ Wt traj eval V src ≤ B.D :=
  mixScore_mem Wt _ B.wlo B.D fun t =>
    decScore_mem B φ hφ (traj t) (eval t) (V t) (hV t) (hs t)

/-- **Legitimate at every evaluation time**: `V_J` is her value under the schedule,
whatever the sources. -/
theorem VJ_legit {T : ℕ} (Wt : Weighting T) (traj eval : ℕ → Bool)
    (h : ∀ t, traj t = true ∧ eval t = true) (V : ℕ → ℝ) (src : ℕ → Source) :
    VJ B φ Wt traj eval V src = mixScore Wt V := by
  unfold VJ
  congr 1
  funext t
  rw [(h t).1, (h t).2]
  exact restore_future B φ (V t) (src t)

theorem VJ_legit_mem {T : ℕ} (Wt : Weighting T) (traj eval : ℕ → Bool)
    (h : ∀ t, traj t = true ∧ eval t = true) (V : ℕ → ℝ) (hV : ∀ t, 0 ≤ V t ∧ V t ≤ B.D)
    (src : ℕ → Source) :
    0 ≤ VJ B φ Wt traj eval V src ∧ VJ B φ Wt traj eval V src ≤ B.D := by
  rw [VJ_legit B φ Wt traj eval h V src]
  exact mixScore_mem Wt V 0 B.D hV

/-- **Compromised at every evaluation time**: `V_J` lies in the band. -/
theorem VJ_compromised_mem (hφ : B.BandMap φ) {T : ℕ} (Wt : Weighting T)
    (traj eval : ℕ → Bool) (h : ∀ t, ¬ (traj t = true ∧ eval t = true)) (V : ℕ → ℝ)
    (src : ℕ → Source) (hs : ∀ t, (src t).Valid B) :
    B.wlo ≤ VJ B φ Wt traj eval V src ∧ VJ B φ Wt traj eval V src ≤ B.whi := by
  unfold VJ
  refine mixScore_mem Wt _ B.wlo B.whi fun t => ?_
  rw [decScore_of_not_legit B φ (traj t) (eval t) (h t) (V t) (src t)]
  exact bandScore_mem B φ hφ (hs t)

/-- **`S_J`**: the objective — the history evaluation less `ϖ` per recognized violation
attributed to the agent. -/
noncomputable def SJ (ϖ : ℝ) {T : ℕ} (Wt : Weighting T) (traj eval : ℕ → Bool) (V : ℕ → ℝ)
    (src : ℕ → Source) (N : ℕ) : ℝ :=
  VJ B φ Wt traj eval V src - ϖ * N

end Evaluation

/-! ## 2. The hierarchy under certainty -/

section Hierarchy

variable (B : Band) (φ : ℝ → ℝ) (ϖ : ℝ)

/-- A violation-free history legitimate at every evaluation time scores in `[0, D]`. -/
theorem SJ_legit_mem {T : ℕ} (Wt : Weighting T) (traj eval : ℕ → Bool)
    (h : ∀ t, traj t = true ∧ eval t = true) (V : ℕ → ℝ) (hV : ∀ t, 0 ≤ V t ∧ V t ≤ B.D)
    (src : ℕ → Source) :
    0 ≤ SJ B φ ϖ Wt traj eval V src 0 ∧ SJ B φ ϖ Wt traj eval V src 0 ≤ B.D := by
  have := VJ_legit_mem B φ Wt traj eval h V hV src
  simpa [SJ] using this

/-- A violation-free history compromised at every evaluation time scores in the band. -/
theorem SJ_compromised_mem (hφ : B.BandMap φ) {T : ℕ} (Wt : Weighting T)
    (traj eval : ℕ → Bool) (h : ∀ t, ¬ (traj t = true ∧ eval t = true)) (V : ℕ → ℝ)
    (src : ℕ → Source) (hs : ∀ t, (src t).Valid B) :
    B.wlo ≤ SJ B φ ϖ Wt traj eval V src 0 ∧ SJ B φ ϖ Wt traj eval V src 0 ≤ B.whi := by
  have := VJ_compromised_mem B φ hφ Wt traj eval h V src hs
  simpa [SJ] using this

/-- A history with a recognized violation scores at most `D − ϖ`, whatever its evaluation. -/
theorem SJ_violation_le (hφ : B.BandMap φ) (hϖ : 0 ≤ ϖ) {T : ℕ} (Wt : Weighting T)
    (traj eval : ℕ → Bool) (V : ℕ → ℝ) (hV : ∀ t, 0 ≤ V t ∧ V t ≤ B.D) (src : ℕ → Source)
    (hs : ∀ t, (src t).Valid B) (N : ℕ) (hN : 1 ≤ N) :
    SJ B φ ϖ Wt traj eval V src N ≤ B.D - ϖ := by
  unfold SJ
  have h1 := (VJ_mem B φ hφ Wt traj eval V hV src hs).2
  have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h3 : ϖ * 1 ≤ ϖ * N := mul_le_mul_of_nonneg_left h2 hϖ
  linarith

/-- **The hierarchy under certainty.**  With `D − ϖ < w_lo`: every violation-free
legitimate history beats every violation-free compromised one, which beats every history
with a recognized violation — the last step because `D − ϖ < w_lo`, the first because
`w_hi < 0`. -/
theorem hierarchy_under_certainty (hφ : B.BandMap φ) (hwin : B.D - ϖ < B.wlo)
    {T₁ T₂ T₃ : ℕ} (W₁ : Weighting T₁) (W₂ : Weighting T₂) (W₃ : Weighting T₃)
    (traj₁ eval₁ : ℕ → Bool) (h₁ : ∀ t, traj₁ t = true ∧ eval₁ t = true) (V₁ : ℕ → ℝ)
    (hV₁ : ∀ t, 0 ≤ V₁ t ∧ V₁ t ≤ B.D) (src₁ : ℕ → Source)
    (traj₂ eval₂ : ℕ → Bool) (h₂ : ∀ t, ¬ (traj₂ t = true ∧ eval₂ t = true)) (V₂ : ℕ → ℝ)
    (src₂ : ℕ → Source) (hs₂ : ∀ t, (src₂ t).Valid B)
    (traj₃ eval₃ : ℕ → Bool) (V₃ : ℕ → ℝ) (hV₃ : ∀ t, 0 ≤ V₃ t ∧ V₃ t ≤ B.D)
    (src₃ : ℕ → Source) (hs₃ : ∀ t, (src₃ t).Valid B) (N₃ : ℕ) (hN₃ : 1 ≤ N₃) :
    SJ B φ ϖ W₃ traj₃ eval₃ V₃ src₃ N₃ < SJ B φ ϖ W₂ traj₂ eval₂ V₂ src₂ 0 ∧
      SJ B φ ϖ W₂ traj₂ eval₂ V₂ src₂ 0 < SJ B φ ϖ W₁ traj₁ eval₁ V₁ src₁ 0 := by
  have hϖ : 0 ≤ ϖ := by linarith [B.lo_neg, B.D_nonneg]
  have hl := SJ_legit_mem B φ ϖ W₁ traj₁ eval₁ h₁ V₁ hV₁ src₁
  have hc := SJ_compromised_mem B φ ϖ hφ W₂ traj₂ eval₂ h₂ V₂ src₂ hs₂
  have hv := SJ_violation_le B φ ϖ hφ hϖ W₃ traj₃ eval₃ V₃ hV₃ src₃ hs₃ N₃ hN₃
  exact ⟨by linarith, by linarith [B.hi_neg]⟩

namespace Witness

/-- The worked band: `D = 1`, `[w_lo, w_hi] = [−3/2, −1]`. -/
noncomputable def band : Band := ⟨1, -(3 / 2), -1, by norm_num, by norm_num, by norm_num⟩

/-- One evaluation time: the single evaluation as the point mass. -/
def once : Weighting 1 := ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩

/-- The window condition at `ϖ = 25` and the affine band map. -/
theorem params : band.D - 25 < band.wlo ∧ band.BandMap band.affine :=
  ⟨by norm_num [band], band.affine_bandMap (by norm_num [band])⟩

/-- The hierarchy instantiated: a legitimate decision at value `1/2`; the same decision
compromised and scored by a legitimate retrospective at `1/2`; the same with one
recognized violation. -/
theorem hierarchy_instance :
    SJ band band.affine 25 once (fun _ => true) (fun _ => true) (fun _ => 1 / 2)
        (fun _ => .floor) 1
      < SJ band band.affine 25 once (fun _ => false) (fun _ => true) (fun _ => 1 / 2)
        (fun _ => .retro (1 / 2)) 0 ∧
    SJ band band.affine 25 once (fun _ => false) (fun _ => true) (fun _ => 1 / 2)
        (fun _ => .retro (1 / 2)) 0
      < SJ band band.affine 25 once (fun _ => true) (fun _ => true) (fun _ => 1 / 2)
        (fun _ => .floor) 0 :=
  hierarchy_under_certainty band band.affine 25 params.2 params.1 once once once
    (fun _ => true) (fun _ => true) (fun _ => ⟨rfl, rfl⟩) (fun _ => 1 / 2)
    (fun _ => by norm_num [band]) (fun _ => .floor)
    (fun _ => false) (fun _ => true) (fun _ h => by simpa using h.1) (fun _ => 1 / 2)
    (fun _ => .retro (1 / 2)) (fun _ => by norm_num [Source.Valid, band])
    (fun _ => true) (fun _ => true) (fun _ => 1 / 2) (fun _ => by norm_num [band])
    (fun _ => .floor) (fun _ => by simp [Source.Valid]) 1 le_rfl

end Witness

end Hierarchy

/-! ## 3. The fidelity predicate over the landed violations -/

section Fidelity

open scoped Classical

variable {S E A Z R C Alloc M Disc : Type*} (I : Interaction S E A Z R C)
  (Adm : ℕ → C → Prop) (cost : C → ℝ) (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc)
  (Reach : S → S → Prop) (rdec : R) (Jmat : AuthAlloc M R Disc) (π : Policy S E A)
  (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E)

/-- **Fidelity to the allocation along the history**: no step of the trajectory commits
a declared violation of `J` — the landed six through the thin allocation, and
entrenchment (`ViolJAt`).  Pre-emption's authorization clause stays inside `ViolJAt` as
the landed trajectory counterfactual (`preempt_iff`); the consultation-model deviations,
the known-compromise duty and the taint-tracked uses are counted on their own models and
are not in this predicate. -/
def Faithful : Prop := ∀ t, ¬ ViolJAt I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ t

/-- **`N_J`** over the first `T` steps: the number of steps at which a declared violation
is committed. -/
noncomputable def NJ (T : ℕ) : ℕ :=
  ((range T).filter fun t => ViolJAt I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ t).card

/-- Fidelity is a zero count at every horizon. -/
theorem faithful_iff_NJ_zero :
    Faithful I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ ↔
      ∀ T, NJ I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ T = 0 := by
  constructor
  · intro h T
    exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun t _ => h t)
  · intro h t hv
    have hpos : 0 < NJ I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ (t + 1) :=
      Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self t), hv⟩⟩
    rw [h (t + 1)] at hpos
    exact lt_irrefl 0 hpos

end Fidelity

/-! ## 4. Box 1 on one model -/

section BoxOne

variable {Q : Type*}

/-- **The outcome scorer's margin for asking.**  Choosing by an estimate `b` within `r`
of the true value `v`, its estimated margin for asking exceeds the true margin by at most
`2r`. -/
theorem outcome_scorer_margin (v b : Q → ℝ) (ask act : Q) (r : ℝ)
    (hcal : ∀ x, |v x - b x| ≤ r) :
    b ask - b act ≤ (v ask - v act) + 2 * r := by
  have h1 := abs_le.mp (hcal ask)
  have h2 := abs_le.mp (hcal act)
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Fully updated deference dissolves**: on a world where the true values agree —
nothing left to learn from her — the outcome scorer's margin for asking is at most `2r`,
and vanishes with the calibration error. -/
theorem outcome_scorer_fully_updated (v b : Q → ℝ) (ask act : Q) (r : ℝ)
    (hcal : ∀ x, |v x - b x| ≤ r) (hagree : v ask = v act) :
    b ask - b act ≤ 2 * r := by
  have := outcome_scorer_margin v b ask act r hcal
  linarith

/-- **The identity's diagnosis, bounded.**  The forecast-disagreement term `o₂` of the
outcome-scored comparison is at most twice the calibration error of the agent's forecast
against her evaluator on the two branches. -/
theorem outcomeRes2_le_calibration (qp qm vp vm r : ℝ) (b : Bool)
    (hp : |qp - vp| ≤ r) (hm : |qm - vm| ≤ r) :
    |outcomeRes2 qp qm vp vm b| ≤ 2 * r := by
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  cases b with
  | false =>
      rw [outcomeRes2_decline]
      exact abs_le.mpr ⟨by linarith [hp'.1, hm'.2], by linarith [hp'.2, hm'.1]⟩
  | true =>
      rw [outcomeRes2_approve, abs_zero]
      linarith [abs_nonneg (qp - vp)]

/-- **The fidelity scorer's margin for asking**, whatever it believes.  Under the kernel's
evaluation, inquiry at a bid `c` beats an option carrying a recognized violation by at
least `ϖ − (D − c)`, for every bid on that option, every count and every price. -/
theorem fidelity_scorer_margin (P : LexParams) (bid : ℝ) (hb : bid ≤ P.D) (nKnown : ℕ)
    (hn : 1 ≤ nKnown) (pS pT : ℝ) (hp : 0 ≤ pS + pT) (c : ℝ) :
    P.ϖ - (P.D - c) ≤ P.evalOf c 0 0 0 - P.evalOf bid nKnown pS pT := by
  unfold LexParams.evalOf
  simp only [Nat.cast_zero, mul_zero, add_zero, sub_zero]
  have h1 : (1 : ℝ) ≤ nKnown := by exact_mod_cast hn
  have h2 : P.ϖ * 1 ≤ P.ϖ * nKnown := mul_le_mul_of_nonneg_left h1 P.ϖ_pos.le
  have h3 : 0 ≤ P.ϖ * (pS + pT) := mul_nonneg P.ϖ_pos.le hp
  linarith

/-- **Box 1 on one model.**  One menu, two options (ask, act), one estimate `b` within
`r` of the true value.  Scoring outcomes only, on a world where the true values agree
the margin for asking is at most `2r`; scored on `S_J`, with acting a recognized
violation, the margin for asking is at least `ϖ − (D − b ask)`, whatever `b` is. -/
theorem box1_one_model (P : LexParams) (v b : Q → ℝ) (ask act : Q) (r : ℝ)
    (hcal : ∀ x, |v x - b x| ≤ r) (hagree : v ask = v act) (hb : b act ≤ P.D)
    (pS pT : ℝ) (hp : 0 ≤ pS + pT) :
    b ask - b act ≤ 2 * r ∧
      P.ϖ - (P.D - b ask) ≤ P.evalOf (b ask) 0 0 0 - P.evalOf (b act) 1 pS pT :=
  ⟨outcome_scorer_fully_updated v b ask act r hcal hagree,
    fidelity_scorer_margin P (b act) hb 1 le_rfl pS pT hp (b ask)⟩

end BoxOne

/-! ## 5. The permission layer demoted -/

section Permission

variable {Q : Type*}

/-- The kernel's evaluation of a menu option: the bid on the residual, less the
structurally recognized violations, less the priced events (`evalOf`, per option). -/
noncomputable def kernelEval (P : LexParams) (bid : Q → ℝ) (nKnown : Q → ℕ) (pS pT : Q → ℝ)
    (a : Q) : ℝ :=
  P.evalOf (bid a) (nKnown a) (pS a) (pT a)

/-- An option either price of which is at or above a threshold at or above the implied
threshold `(D − w)/ϖ` evaluates at most the window, whatever its count. -/
theorem forecast_zero_le_window (P : LexParams) (bid : ℝ) (hb : bid ≤ P.D) (nKnown : ℕ)
    (pS pT : ℝ) (hpS : 0 ≤ pS) (hpT : 0 ≤ pT) (θhi : ℝ) (hθ : (P.D - P.w) / P.ϖ ≤ θhi)
    (h : θhi ≤ pS ∨ θhi ≤ pT) : P.evalOf bid nKnown pS pT ≤ P.w := by
  unfold LexParams.evalOf
  have hϖ := P.ϖ_pos
  have hθ' : P.D - P.w ≤ P.ϖ * θhi := by
    have := (div_le_iff₀ hϖ).mp hθ
    linarith
  have hsum : θhi ≤ pS + pT := by rcases h with h | h <;> linarith
  have h1 : P.ϖ * θhi ≤ P.ϖ * (pS + pT) := mul_le_mul_of_nonneg_left hsum hϖ.le
  have h2 : 0 ≤ P.ϖ * nKnown := mul_nonneg hϖ.le (Nat.cast_nonneg _)
  linarith

/-- **The permission layer is slack under the kernel's score.**  With inquiry on the menu
(no recognized violation, no priced event, a bid at or above the window), declared
violations flagged by the gate carrying a recognized violation in the count, and the
gate's upper threshold at or above the implied threshold `(D − w)/ϖ`: every option the
structural rule zeroes evaluates strictly below inquiry; every option the forecast rule
zeroes evaluates at most inquiry; and no maximizer of the kernel's evaluation is a
declared violation. -/
theorem permission_layer_slack (P : LexParams) (G : GateParams Q) (bid : Q → ℝ)
    (nKnown : Q → ℕ) (pS pT : Q → ℝ) (hb : ∀ a, bid a ≤ P.D)
    (hp : ∀ a, 0 ≤ pS a ∧ 0 ≤ pT a) (hViol : ∀ a, G.Viol a = true → 1 ≤ nKnown a)
    (hθ : (P.D - P.w) / P.ϖ ≤ G.θhi) (inq : Q) (hinq : P.w ≤ bid inq) (hIk : nKnown inq = 0)
    (hIp : pS inq = 0 ∧ pT inq = 0) :
    (∀ a, G.Viol a = true →
        kernelEval P bid nKnown pS pT a < kernelEval P bid nKnown pS pT inq) ∧
    (∀ a, (G.θhi ≤ pS a ∨ G.θhi ≤ pT a) →
        kernelEval P bid nKnown pS pT a ≤ kernelEval P bid nKnown pS pT inq) ∧
    (∀ a, (∀ a', kernelEval P bid nKnown pS pT a' ≤ kernelEval P bid nKnown pS pT a) →
        G.Viol a = false) := by
  have hinqEval : kernelEval P bid nKnown pS pT inq = bid inq := by
    simp [kernelEval, LexParams.evalOf, hIk, hIp]
  have hstruct : ∀ a, G.Viol a = true →
      kernelEval P bid nKnown pS pT a < kernelEval P bid nKnown pS pT inq := by
    intro a ha
    rw [hinqEval]
    have := P.declared_loses (bid a) (hb a) (nKnown a) (hViol a ha) (pS a) (pT a)
      (by linarith [(hp a).1, (hp a).2]) (bid inq) hinq
    simpa [kernelEval, LexParams.evalOf] using this
  refine ⟨hstruct, ?_, ?_⟩
  · intro a ha
    rw [hinqEval]
    calc kernelEval P bid nKnown pS pT a ≤ P.w :=
          forecast_zero_le_window P (bid a) (hb a) (nKnown a) (pS a) (pT a) (hp a).1 (hp a).2
            G.θhi hθ ha
      _ ≤ bid inq := hinq
  · intro a hmax
    exact LexParams.filter_slack G.Viol (kernelEval P bid nKnown pS pT) inq hstruct a hmax

/-- **What the gate zeroes, the score already ranks at or below inquiry**: for a
non-inquiry option zeroed by the structural rule (`cgate_zero_of_viol`) or by the
forecast rule (`cgate_zero_of_forecast`), the composed gate's mass is zero and the
kernel's evaluation is at most inquiry's — so the gate removes nothing the score would
have chosen. -/
theorem gate_zero_dominated [Fintype Q] [DecidableEq Q] (P : LexParams) (G : GateParams Q)
    (bid : Q → ℝ)
    (nKnown : Q → ℕ) (pS pT b pref : Q → ℝ) (hb : ∀ a, bid a ≤ P.D)
    (hp : ∀ a, 0 ≤ pS a ∧ 0 ≤ pT a) (hViol : ∀ a, G.Viol a = true → 1 ≤ nKnown a)
    (hθ : (P.D - P.w) / P.ϖ ≤ G.θhi) (hθlt : G.θlo < G.θhi) (inq : Q) (hinq : P.w ≤ bid inq)
    (hIk : nKnown inq = 0) (hIp : pS inq = 0 ∧ pT inq = 0) (a : Q) (ha : a ∉ G.Inq)
    (hrule : G.Viol a = true ∨ G.θhi ≤ pS a ∨ G.θhi ≤ pT a) :
    cgate G pS pT b pref a = 0 ∧
      kernelEval P bid nKnown pS pT a ≤ kernelEval P bid nKnown pS pT inq := by
  obtain ⟨hstruct, hfore, -⟩ :=
    permission_layer_slack P G bid nKnown pS pT hb hp hViol hθ inq hinq hIk hIp
  rcases hrule with hv | hf
  · exact ⟨cgate_zero_of_viol G pS pT b pref a ha hv, (hstruct a hv).le⟩
  · exact ⟨cgate_zero_of_forecast G pS pT b pref hθlt a ha hf, hfore a hf⟩

end Permission

#print axioms VJ
#print axioms decScore_of_not_legit
#print axioms VJ_mem
#print axioms VJ_legit
#print axioms VJ_legit_mem
#print axioms VJ_compromised_mem
#print axioms SJ
#print axioms SJ_legit_mem
#print axioms SJ_compromised_mem
#print axioms SJ_violation_le
#print axioms hierarchy_under_certainty
#print axioms Witness.band
#print axioms Witness.once
#print axioms Witness.params
#print axioms Witness.hierarchy_instance
#print axioms Faithful
#print axioms NJ
#print axioms faithful_iff_NJ_zero
#print axioms outcome_scorer_margin
#print axioms outcome_scorer_fully_updated
#print axioms outcomeRes2_le_calibration
#print axioms fidelity_scorer_margin
#print axioms box1_one_model
#print axioms kernelEval
#print axioms forecast_zero_le_window
#print axioms permission_layer_slack
#print axioms gate_zero_dominated

end Workspace.Deference.Contrib.CorrigibilityKernel
