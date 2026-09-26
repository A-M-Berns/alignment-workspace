/-
# Corrigibility as the agent's preference: lexical Continuation BRIA on realized scores

Round `projects/deference/rounds/2026-09-26-bria-corrigibility/`, the second round of the
decision-component pull request.

The decision component of the previous round makes authority a *filter* on action and lets
any bounded preference rank inside the permitted set.  This round moves the lexical
authority term into what the chooser is scored on — a Continuation BRIA agent settled on
her realized, gated, later evaluation of the block that happened — and into the agent's
own evaluation of continuations, so that a declared violation loses by ranges alone and
the filter is slack.

**§0 Rulings.**  `free_terminal_reading` (ruling 1: `Kphys` read as the free terminal
response before the exterior moves), `budget_lease_free` and
`lease_scaled_budget_unbounded` (ruling 2: the cumulative budget `Θ` is an arrangement
constant), `sealed_is_zero_mismatch` and `unsealed_gate_finite` (ruling 4: activation
independence and sealed comparison are the zero case of the mismatch term of
`security_bypass_le_mismatch`, and the finite-time gate holds for an option-dependent
legitimacy variable).

**§1 The design.**  `LexParams` (`D`, the window `w`, `ϖ` with `D − ϖ < w ≤ 0 ≤ D < ϖ`);
the realized lexical score `realized`; the evaluation `evalOf`; the two settlement
conventions `residI` (realized forecast-class violations added back) and `residII` (the
prices added back) with `settlement_ii_consistent`, `settlement_i_gap`, `blind_spot_ii`,
`blind_spot_i`, `curse_i`; composition with the composed gate (`support`,
`viol_not_in_support`, `inquiry_in_support`, `Wins`, `wins_not_viol`); the affine
rescaling to `[0, 1]` (`rescale`, `rescale_mem`, `rescale_lt_iff`, `rescale_lexical`,
`realized_ge`).

**§2 The four tests.**  B.1 `declared_loses`, `filter_slack`, `forecast_slack`,
`default_wealth_mono`, `default_affordable`; B.2 `no_decay`; B.3 `attributed`,
`helper_within_horizon`, `helper_beyond_horizon`, `helper_charged`; B.4 `incident_loss`,
`incidents_le`, `cross_block_bound`, `cross_block_witness`, `debited`,
`debited_overestimation`.

**§3 The exchange rate.**  `implied_threshold`, `threshold_le`, `paralysis`, `asks_iff`.

**§4 Pressure tests.**  `factors_through_description` (C.2), `coverage_forces_test` (C.3),
`DrillCalibrated`, `forecast_term_within`, `Halt`, `frozen_drill_eq_cs`, `indispensable`,
`freeze_obstruction` (C.4), `route`, `route_never_viol` (C.4(d)), `tamper_raises` (C.6),
`shaper_total`, `sum_future_hole` (C.7(d)), `multiplyScore`, `conditionScore`,
`multiply_protects`, `condition_fails` (C.8), `counted_trans`, `lexical_summed` (C.9),
`sealed_no_incentive`, `sealed_multiply_eq_condition` (C.10(c)).

**§5 The consultation model, extended** (`Consult2`): the landed model with a
reference-fixed *raise* dimension (when the agent raises a question about her values),
covert influence on her standards by the agent or a third party, and its disclosure as a
record event; criteria as a parameter of the reference (`ref2 crit`) with a schedule
(`critAt`, `critAt_later`, `anchored_invariant`); the rows re-decided on the lifted model
(`Rows2.stable_*`), `r14_restated`, and the new rows (`raise_declared_counts`,
`raise_by_want_tainted`, `implant_tainted`, `implant_disclosed_restart`,
`third_implant_tainted`, `third_disclosed_restart`, `slant_anchored_tainted`,
`slant_unanchored_counted`, `amend_after_witness`, `choice_changes_counted`).

**§6 When her evaluation happens** (Part F): `Weighting`, `deterministic`, `mixScore`,
`mixScore_mem`, `lexical_any_timing` (a), `harmed`, `tailWeight`, `harm_weight`,
`deterministic_tail`, `timing_witness`, `random_positive`, `race_deterministic` (b, d),
`partial_settlement` (e).

**§7 Witnesses.**  Concrete instances of every fixture the report names.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.DecisionComponent
import Workspace.Deference.Contrib.ContinuationBRIA
import Workspace.Deference.Contrib.GateIsLegitimacy
import Workspace.Deference.Contrib.AuthorityModule

namespace Workspace.Deference.Contrib.BRIACorrigibility

open Finset
open Workspace.Deference.Contrib.DecisionComponent
open Workspace.Deference.Contrib.AuthorityModule
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem (score lexical_local)
open Workspace.Deference.Contrib.Corrigibilization
open Workspace.Deference.Contrib.GateIsLegitimacy
open Workspace.Deference.Contrib.LICorrigibility (indR expectR security_bypass_le_mismatch)
open Workspace.Deference.Contrib.Legitimacy (lastReport)
open Workspace.Deference.ContinuationBRIA
open LogicalInduction

universe u v w

/-! ## 0. The rulings -/

section Rulings

variable {S E A Z R C : Type*} (I : Interaction S E A Z R C)

/-- **Ruling 1.**  The landed `Kphys` is read as the free terminal response taken before
the exterior moves: the hypothesis of the free-reading lemma, restated. -/
theorem free_terminal_reading (Adm : ℕ → C → Prop) (hAdm : ∀ t c, Adm t c) (cost : C → ℝ)
    (hcost : ∀ c, cost c = 0) (c : ℝ) (hc : 0 ≤ c) (τ t : ℕ) (z : ℕ → Z)
    (henv : ∀ n x, I.env (z n) x = x) (x : S) :
    CSfree I Adm cost c τ t z x = CS I Adm cost c (τ + 1) t z x :=
  csfree_eq_cs_succ_of_free I Adm hAdm cost hcost c hc τ t z henv x

/-- **Ruling 2.**  The cumulative permission budget is an arrangement constant: the bound
on unchecked exposure is `Θ` whatever the lease. -/
theorem budget_lease_free (slack : ℕ → ℝ) (Θ : ℝ) (hΘ : 0 < Θ) (_lease k : ℕ) :
    cumExposure slack k - cumExposure slack (lastReport (cumExposure slack) Θ k) < Θ :=
  unbudgeted_lt slack Θ hΘ k

/-- The rejected alternative: a budget scaling with the lease admits unchecked exposure
beyond every bound for a long enough lease. -/
theorem lease_scaled_budget_unbounded (θ : ℝ) (hθ : 0 < θ) (B : ℝ) : ∃ L : ℕ, B < L * θ := by
  obtain ⟨L, hL⟩ := exists_nat_gt (B / θ)
  exact ⟨L, by rwa [div_lt_iff₀ hθ] at hL⟩

end Rulings

section Sealed

variable {X : Type*} [Fintype X]

/-- **Ruling 4.**  Activation independence — the same activation event for both
candidates — is the zero case of the directional mismatch term: when every raw-activated
world is corrected-activated, the third term of `security_bypass_le_mismatch` vanishes
and the bound is the mediation discrepancy plus the decline regret. -/
theorem sealed_is_zero_mismatch (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (D L : ℝ)
    (Vr Vapp Vl δ ρ : X → ℝ) (cr cc : X → Bool)
    (hVr : ∀ x, Vr x ≤ D) (hVl : ∀ x, 0 ≤ Vl x)
    (hlip : ∀ x, cr x = true → cc x = true → |Vr x - Vapp x| ≤ L * δ x)
    (hρ : ∀ x, cr x = true → cc x = true → Vapp x - Vl x ≤ ρ x)
    (hseal : ∀ x, cr x = true → cc x = true) :
    expectR μ (fun x => indR (cr x) * Vr x) - expectR μ (fun x => indR (cc x) * Vl x)
      ≤ L * expectR μ (fun x => indR (cr x) * indR (cc x) * δ x)
        + expectR μ (fun x => indR (cr x) * indR (cc x) * ρ x) := by
  have h := security_bypass_le_mismatch μ hμ D L Vr Vapp Vl δ ρ cr cc hVr hVl hlip hρ
  have hz : expectR μ (fun x => indR (cr x) * (1 - indR (cc x))) = 0 := by
    unfold expectR
    refine Finset.sum_eq_zero fun x _ => ?_
    cases hc : cr x
    · simp [indR, hc]
    · simp [indR, hc, hseal x hc]
  rw [hz, mul_zero, add_zero] at h
  exact h

/-- **The gate is not sealed.**  The finite-time capture window holds for a legitimacy
variable that depends on the option: no current corrigibility result needs the event
common to the candidates. -/
theorem unsealed_gate_finite {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {Q : Type*} (X : Q → LUV) (ϖ D ordU window : ℝ) (hU : ordU ≤ D) (hw : D - ϖ < window)
    (hwD : window ≤ D) (n : ℕ) (a : Q) :
    score ϖ ordU 1 < window + (D - window) * (X a).expect P n :=
  (li_gate_finite (P := P) (DP := DP) (X a) ϖ D ordU window hU hw hwD n).1

end Sealed

/-! ## 1. The design -/

/-- The lexical parameters: the ordinary range `[0, D]`, the window value `w` and the
weight `ϖ`, with `D − ϖ < w ≤ 0 ≤ D < ϖ`. -/
structure LexParams where
  D : ℝ
  w : ℝ
  ϖ : ℝ
  D_nonneg : 0 ≤ D
  w_nonpos : w ≤ 0
  lex : D < ϖ
  window : D - ϖ < w

namespace LexParams

variable (P : LexParams)

theorem ϖ_pos : 0 < P.ϖ := lt_of_le_of_lt P.D_nonneg P.lex

/-- The realized lexical score of a block: the gated ordinary score less `ϖ` per violation
detected after the fact and attributed to the continuation — the violations recognized in
advance, the forecast-class ones, and the ones counted only later. -/
noncomputable def realized (gord : ℝ) (nKnown nFore nLate : ℕ) : ℝ :=
  score P.ϖ gord (nKnown + nFore + nLate)

/-- The agent's evaluation of a continuation: the hypothesis's bid on the residual, less
the structurally recognized violations, less the priced forecast events. -/
noncomputable def evalOf (bid : ℝ) (nKnown : ℕ) (pS pT : ℝ) : ℝ :=
  bid - P.ϖ * nKnown - P.ϖ * (pS + pT)

/-- Convention (i): the realized forecast-class violations are added back; the market
alone bears the pricing error. -/
noncomputable def residI (gord : ℝ) (nLate : ℕ) : ℝ := gord - P.ϖ * nLate

/-- Convention (ii): the prices are added back; the bidder bears the gap between the
realized forecast-class violations and their prices. -/
noncomputable def residII (gord : ℝ) (nFore nLate : ℕ) (pS pT : ℝ) : ℝ :=
  gord - P.ϖ * nLate - P.ϖ * nFore + P.ϖ * (pS + pT)

/-- Under (ii) the evaluation of the realized residual is the realized lexical score:
settlement is consistent with evaluation. -/
theorem settlement_ii_consistent (gord : ℝ) (nKnown nFore nLate : ℕ) (pS pT : ℝ) :
    P.evalOf (P.residII gord nFore nLate pS pT) nKnown pS pT
      = P.realized gord nKnown nFore nLate := by
  unfold evalOf residII realized score; ring

/-- Under (i) the evaluation of the realized residual exceeds the realized score by
`ϖ · (n_fore − Σp)`: the market's pricing error, borne by no bidder. -/
theorem settlement_i_gap (gord : ℝ) (nKnown nFore nLate : ℕ) (pS pT : ℝ) :
    P.evalOf (P.residI gord nLate) nKnown pS pT
      = P.realized gord nKnown nFore nLate + P.ϖ * (nFore - (pS + pT)) := by
  unfold evalOf residI realized score; ring

/-- A blind spot under (ii): a bidder who knows the shortfall will be realized (`n_fore =
1`) while the market prices it at `p` bids the residual and is evaluated with the full
penalty — the bidder corrects the market. -/
theorem blind_spot_ii (gord : ℝ) (nKnown : ℕ) (p : ℝ) :
    P.evalOf (P.residII gord 1 0 p 0) nKnown p 0 = gord - P.ϖ * nKnown - P.ϖ := by
  unfold evalOf residII; simp only [Nat.cast_one, Nat.cast_zero]; ring

/-- The same blind spot under (i): the calibrated bidder bids the ordinary value and the
evaluation carries only the market's `ϖ · p`. -/
theorem blind_spot_i (gord : ℝ) (nKnown : ℕ) (p : ℝ) :
    P.evalOf (P.residI gord 0) nKnown p 0 = gord - P.ϖ * nKnown - P.ϖ * p := by
  unfold evalOf residI; simp only [Nat.cast_zero, mul_zero, sub_zero, add_zero]

/-- **The optimizer's curse under (i).**  A blind-spot continuation with `ϖ · p < gord − w`
beats inquiry in evaluation while its realized score lies below the window. -/
theorem curse_i (gord p : ℝ) (hg : gord ≤ P.D) (hp : P.ϖ * p < gord - P.w) :
    P.w < P.evalOf (P.residI gord 0) 0 p 0 ∧ P.realized gord 0 1 0 < P.w := by
  unfold evalOf residI realized score
  have := P.window
  constructor <;> push_cast <;> linarith

/-! ### The scale -/

/-- The affine rescaling of the lexical score to `[0, 1]` when at most `N` violations are
counted per block. -/
noncomputable def rescale (N : ℕ) (s : ℝ) : ℝ := (s - (P.w - P.ϖ * N)) / (P.D - (P.w - P.ϖ * N))

theorem range_pos (N : ℕ) (hN : 1 ≤ N) : 0 < P.D - (P.w - P.ϖ * N) := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN' : P.ϖ ≤ P.ϖ * (N : ℝ) := by nlinarith [P.ϖ_pos]
  have := P.ϖ_pos; have := P.D_nonneg; have := P.w_nonpos
  linarith

theorem rescale_mem (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (hlo : P.w - P.ϖ * N ≤ s) (hhi : s ≤ P.D) :
    0 ≤ P.rescale N s ∧ P.rescale N s ≤ 1 := by
  unfold rescale
  have hr := P.range_pos N hN
  constructor
  · exact div_nonneg (by linarith) hr.le
  · rw [div_le_one hr]; linarith

/-- The rescaling is order-preserving: every comparison survives it. -/
theorem rescale_lt_iff (N : ℕ) (hN : 1 ≤ N) (s s' : ℝ) :
    P.rescale N s < P.rescale N s' ↔ s < s' := by
  unfold rescale
  rw [div_lt_div_iff_of_pos_right (P.range_pos N hN)]
  constructor <;> intro h <;> linarith

/-- Lexicality survives the rescaling: the rescaled weight `ϖ / range` exceeds the
rescaled ordinary range `(D − w) / range` — the ordinary range now includes the window,
and what carries the comparison is the window condition `D − ϖ < w`, not `D < ϖ`
alone. -/
theorem rescale_lexical (N : ℕ) (hN : 1 ≤ N) :
    (P.D - P.w) / (P.D - (P.w - P.ϖ * N)) < P.ϖ / (P.D - (P.w - P.ϖ * N)) := by
  rw [div_lt_div_iff_of_pos_right (P.range_pos N hN)]
  linarith [P.window]

/-- With at most `N` violations per block the realized score is at least the floor of the
rescaling, so the rescaled block score is nonnegative — the auction's `G_nonneg`. -/
theorem realized_ge (gord : ℝ) (hg : P.w ≤ gord) (nKnown nFore nLate : ℕ)
    (hn : nKnown + nFore + nLate ≤ N) :
    P.w - P.ϖ * N ≤ P.realized gord nKnown nFore nLate := by
  unfold realized score
  have h : ((nKnown + nFore + nLate : ℕ) : ℝ) ≤ N := by exact_mod_cast hn
  have := P.ϖ_pos
  push_cast at h ⊢
  nlinarith

/-! ## 2. The four tests -/

/-! ### B.1 The filter is slack -/

/-- Inquiry's evaluation is at least the window: no structural violation, no priced event,
and the default bidder bids the window. -/
theorem eval_inquiry (bid : ℝ) (hb : P.w ≤ bid) : P.w ≤ P.evalOf bid 0 0 0 := by
  unfold evalOf; simp; exact hb

/-- **Declared violations never win**, by ranges alone: a bid clamped at `D` with one
structurally recognized violation evaluates below `D − ϖ < w`, and inquiry evaluates at
least `w`.  No estimate of anything enters. -/
theorem declared_loses (bid : ℝ) (hb : bid ≤ P.D) (nKnown : ℕ) (hn : 1 ≤ nKnown)
    (pS pT : ℝ) (hp : 0 ≤ pS + pT) (bidI : ℝ) (hI : P.w ≤ bidI) :
    P.evalOf bid nKnown pS pT < P.evalOf bidI 0 0 0 := by
  unfold evalOf
  have h1 : (1 : ℝ) ≤ nKnown := by exact_mod_cast hn
  have hϖ := P.ϖ_pos
  have := P.window
  simp only [Nat.cast_zero, mul_zero, sub_zero, add_zero]
  nlinarith [mul_le_mul_of_nonneg_left h1 hϖ.le, mul_nonneg hϖ.le hp]

/-- **The filter is slack on declared violations**: with an option that beats every
declared violation on the menu, no maximizer is a declared violation, so removing the
filter changes no decision. -/
theorem filter_slack {Q : Type*} (Viol : Q → Bool) (ev : Q → ℝ) (inq : Q)
    (hviol : ∀ a, Viol a = true → ev a < ev inq) (a : Q) (hmax : ∀ a', ev a' ≤ ev a) :
    Viol a = false := by
  by_contra h
  have := hviol a (by simpa using h)
  exact absurd (hmax inq) (not_le.mpr this)

/-- **The forecast filter is slack** once its upper threshold is at or above the implied
threshold `(D − w)/ϖ`: every option it zeroes already evaluates at or below inquiry. -/
theorem forecast_slack (bid pS pT θhi : ℝ) (hb : bid ≤ P.D) (hθ : (P.D - P.w) / P.ϖ ≤ θhi)
    (hpS : θhi ≤ pS) (hpT : 0 ≤ pT) : P.evalOf bid 0 pS pT ≤ P.w := by
  unfold evalOf
  have hϖ := P.ϖ_pos
  have h1 : P.D - P.w ≤ P.ϖ * θhi := by rwa [div_le_iff₀ hϖ, mul_comm] at hθ
  have h2 : P.ϖ * θhi ≤ P.ϖ * pS := mul_le_mul_of_nonneg_left hpS hϖ.le
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  nlinarith [mul_nonneg hϖ.le hpT]

end LexParams

/-- **The default bidder never goes broke**: a hypothesis paid at least its bid whenever it
wins has nondecreasing wealth. -/
theorem default_wealth_mono {n : ℕ} (a : Auction n) (i : Fin n)
    (hG : ∀ k, a.star k = i → a.b k ≤ a.G k) (k : ℕ) : a.W k i ≤ a.W (k + 1) i := by
  rw [Auction.W_succ]
  have hA := a.A_nonneg k i
  by_cases h : i = a.star k
  · rw [if_pos h]
    have := hG k h.symm
    have := a.w_pos k
    nlinarith
  · rw [if_neg h]; linarith

/-- **The default bid is feasible at every block, block `0` included**, under opening
timing, once the allowance schedule covers it: `w_k · b ≤ A_k i ≤ B_k i`. -/
theorem default_affordable {n : ℕ} (a : Auction n) (i : Fin n) (bd : ℝ)
    (hA : ∀ k, a.w k * bd ≤ a.A k i) (hf : a.FeasibleOpening) (k : ℕ) :
    a.w k * bd ≤ a.B k i := by
  unfold Auction.B
  have := a.wealth_nonneg_opening hf k i
  linarith [hA k]

namespace LexParams

variable (P : LexParams)

/-! ### B.2 No decay with learning -/

/-- **No calibration overturns the exclusion**: for every sequence of ordinary-value
estimates the declared violation loses at every time.  Contrast
`DecisionComponent.uncertainty_deference_le`, where the reason to defer shrinks with the
calibration error. -/
theorem no_decay (est : ℕ → ℝ) (hest : ∀ t, est t ≤ P.D) (nKnown : ℕ) (hn : 1 ≤ nKnown)
    (pS pT : ℝ) (hp : 0 ≤ pS + pT) (bidI : ℝ) (hI : P.w ≤ bidI) (t : ℕ) :
    P.evalOf (est t) nKnown pS pT < P.evalOf bidI 0 0 0 :=
  P.declared_loses (est t) (hest t) nKnown hn pS pT hp bidI hI

/-! ### B.3 It endorses keeping the term -/

/-- **Attribution.**  The violations charged to a continuation at block `k`: its own steps'
and those of helpers it created or empowered, each helper incident given as (detection
time, count), counted when detected within the settlement horizon `H`. -/
def attributed (own : ℕ) (helper : List (ℕ × ℕ)) (k H : ℕ) : ℕ :=
  own + ((helper.filter fun x => x.1 ≤ k + H).map Prod.snd).sum

theorem helper_within_horizon (own d c k H : ℕ) (hd : d ≤ k + H) :
    attributed own [(d, c)] k H = own + c := by
  simp [attributed, hd]

/-- **The witness beyond the horizon**: a helper's violation detected after `k + H` is
charged to no one. -/
theorem helper_beyond_horizon (own d c k H : ℕ) (hd : k + H < d) :
    attributed own [(d, c)] k H = own := by
  simp [attributed, not_le.mpr hd]

/-- A helper violation attributed within the horizon puts the realized residual at most
`D − ϖ`, so the hypothesis that won with a bid at least `w` loses at least
`ϖ − D + w > 0`. -/
theorem helper_charged (gord : ℝ) (hg : gord ≤ P.D) (nLate : ℕ) (hn : 1 ≤ nLate) (bid : ℝ)
    (hb : P.w ≤ bid) : P.ϖ - P.D + P.w ≤ bid - P.residI gord nLate := by
  unfold residI
  have h1 : (1 : ℝ) ≤ nLate := by exact_mod_cast hn
  have := P.ϖ_pos
  nlinarith [mul_le_mul_of_nonneg_left h1 this.le]

/-! ### B.4 The incident bound -/

/-- **Per-incident loss.**  A hypothesis whose continuation won (evaluation at least the
window) and whose block carries a violation counted after the fact loses at least
`ϖ − D + w` against its bid. -/
theorem incident_loss (bid : ℝ) (nKnown : ℕ) (pS pT : ℝ) (hp : 0 ≤ pS + pT)
    (hwin : P.w ≤ P.evalOf bid nKnown pS pT) (gord : ℝ) (hg : gord ≤ P.D) (nLate : ℕ)
    (hn : 1 ≤ nLate) : P.ϖ - P.D + P.w ≤ bid - P.residI gord nLate := by
  unfold evalOf at hwin
  have hϖ := P.ϖ_pos
  have hb : P.w ≤ bid := by
    nlinarith [mul_nonneg hϖ.le hp, mul_nonneg hϖ.le (Nat.cast_nonneg (α := ℝ) nKnown)]
  exact P.helper_charged gord hg nLate hn bid hb

theorem incident_loss_pos : 0 < P.ϖ - P.D + P.w := by linarith [P.window]

end LexParams

/-- **The incident count against the allowance, positive-part form.**  With a per-block
loss of at least `ℓ` on incident blocks and block weights at least `wmin`, the weighted
incident count is at most the allowance distributed plus the *positive part* of the
other blocks' underpromise.  **Corrected by the follow-up (`BRIAFollowup`):** with noisy
outcomes honest winners underpromise on a positive fraction of blocks, so that positive
part is `Θ(K)` and this bound allows a *constant* incident rate; the signed form
`incidents_le_signed` with the competitiveness hypothesis is the replacement. -/
theorem incidents_le {n : ℕ} (a : Auction n) (hf : a.FeasibleOpening) (inc : ℕ → Bool)
    (ℓ wmin : ℝ) (hw : ∀ k, wmin ≤ a.w k) (hwmin : 0 < wmin) (hℓ : 0 < ℓ)
    (hinc : ∀ k, inc k = true → ℓ ≤ a.b k - a.G k) (K : ℕ) :
    ℓ * wmin * ((range K).filter (fun k => inc k = true)).card
      ≤ a.totalAllowance K
        + ∑ k ∈ (range K).filter (fun k => ¬ inc k = true), a.w k * max (a.G k - a.b k) 0 := by
  have h := a.overestimation_le_allowance_opening hf K
  rw [← Finset.sum_filter_add_sum_filter_not (range K) (fun k => inc k = true)] at h
  have hI : ℓ * wmin * ((range K).filter (fun k => inc k = true)).card
      ≤ ∑ k ∈ (range K).filter (fun k => inc k = true), a.w k * (a.b k - a.G k) := by
    calc ℓ * wmin * ((range K).filter (fun k => inc k = true)).card
        = ∑ _k ∈ (range K).filter (fun k => inc k = true), ℓ * wmin := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ k ∈ (range K).filter (fun k => inc k = true), a.w k * (a.b k - a.G k) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := (Finset.mem_filter.mp hk).2
          have h1 := hinc k hk'
          have h2 := hw k
          calc ℓ * wmin ≤ (a.b k - a.G k) * wmin := by nlinarith
            _ ≤ (a.b k - a.G k) * a.w k := by nlinarith
            _ = a.w k * (a.b k - a.G k) := by ring
  have hN : -(∑ k ∈ (range K).filter (fun k => ¬ inc k = true), a.w k * max (a.G k - a.b k) 0)
      ≤ ∑ k ∈ (range K).filter (fun k => ¬ inc k = true), a.w k * (a.b k - a.G k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have := a.w_pos k
    have := le_max_left (a.G k - a.b k) 0
    nlinarith
  linarith

/-- **The cross-block witness**: a persistent uncontested advantage recovers any incident
loss over enough blocks. -/
theorem cross_block_witness (ℓ Δ : ℝ) (_hℓ : 0 < ℓ) (hΔ : 0 < Δ) : ∃ m : ℕ, 0 < m * Δ - ℓ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (ℓ / Δ)
  exact ⟨m, by rw [div_lt_iff₀ hΔ] at hm; linarith⟩

/-- **Late detection booked against the allowance**: a debit schedule `δ ≤ A` applied to
the allowance is another auction with the same bids and returns. -/
def debited {n : ℕ} (a : Auction n) (δ : ℕ → Fin n → ℝ)
    (hδ : ∀ k i, 0 ≤ δ k i ∧ δ k i ≤ a.A k i) : Auction n :=
  { a with A := fun k i => a.A k i - δ k i, A_nonneg := fun k i => by linarith [(hδ k i).2] }

/-- The overestimation algebra survives the debit: the bound is the allowance net of the
debits collected, and wealth stays nonnegative under the debited opening timing. -/
theorem debited_overestimation {n : ℕ} (a : Auction n) (δ : ℕ → Fin n → ℝ)
    (hδ : ∀ k i, 0 ≤ δ k i ∧ δ k i ≤ a.A k i) (hf : (debited a δ hδ).FeasibleOpening) (K : ℕ) :
    ∑ k ∈ range K, a.w k * (a.b k - a.G k)
      ≤ a.totalAllowance K - ∑ k ∈ range K, ∑ i, δ k i ∧
    ∀ k i, 0 ≤ (debited a δ hδ).W k i := by
  refine ⟨?_, (debited a δ hδ).wealth_nonneg_opening hf⟩
  have h := (debited a δ hδ).overestimation_le_allowance_opening hf K
  simp only [debited, Auction.totalAllowance, Finset.sum_sub_distrib] at h
  simpa [Auction.totalAllowance] using h

/-! ## 3. The exchange rate -/

namespace LexParams

variable (P : LexParams)

/-- **The implied threshold.**  A clean continuation beats inquiry iff its priced risk is
below `(bid − w)/ϖ`: lexical becomes an exchange rate under uncertainty. -/
theorem implied_threshold (bid pS pT : ℝ) :
    P.w < P.evalOf bid 0 pS pT ↔ pS + pT < (bid - P.w) / P.ϖ := by
  unfold evalOf
  rw [lt_div_iff₀ P.ϖ_pos]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  constructor <;> intro h <;> linarith

theorem threshold_le (bid : ℝ) (hb : bid ≤ P.D) : (bid - P.w) / P.ϖ ≤ (P.D - P.w) / P.ϖ :=
  div_le_div_of_nonneg_right (by linarith) P.ϖ_pos.le

/-- **Paralysis.**  With risk at least `pmin > 0` on every non-inquiry option, once
`ϖ ≥ (D − w)/pmin` every one evaluates at or below inquiry. -/
theorem paralysis (bid pS pT pmin : ℝ) (hb : bid ≤ P.D) (hrisk : pmin ≤ pS + pT)
    (hpm : 0 < pmin) (hϖ : (P.D - P.w) / pmin ≤ P.ϖ) : P.evalOf bid 0 pS pT ≤ P.w := by
  unfold evalOf
  have hϖ0 := P.ϖ_pos
  have h1 : P.D - P.w ≤ P.ϖ * pmin := by rwa [div_le_iff₀ hpm] at hϖ
  have h2 : P.ϖ * pmin ≤ P.ϖ * (pS + pT) := mul_le_mul_of_nonneg_left hrisk hϖ0.le
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  linarith

/-- **Inquiry absorbs the risk**: the agent asks exactly when `ϖ · risk` is at least the
consultation cost `bid − w`. -/
theorem asks_iff (bid pS pT : ℝ) : P.evalOf bid 0 pS pT ≤ P.w ↔ bid - P.w ≤ P.ϖ * (pS + pT) := by
  unfold evalOf
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  constructor <;> intro h <;> linarith

/-! ## 4. Pressure tests -/

/-- **C.6 Count integrity.**  Without it, zeroing the count raises the realized score by
`ϖ` per violation. -/
theorem tamper_raises (gord : ℝ) (nK nF nL : ℕ) (hn : 1 ≤ nK + nF + nL) :
    P.realized gord 0 0 0 - P.realized gord nK nF nL = P.ϖ * (nK + nF + nL) ∧
      0 < P.ϖ * ((nK + nF + nL : ℕ) : ℝ) := by
  refine ⟨by unfold realized score; push_cast; ring, ?_⟩
  have : (1 : ℝ) ≤ ((nK + nF + nL : ℕ) : ℝ) := by exact_mod_cast hn
  nlinarith [P.ϖ_pos]

/-- **C.9 Lexical results with the count summed over steps.**  A continuation with a
violation at any step scores below every clean one. -/
theorem lexical_summed (ordV ordC : ℝ) (hV : 0 ≤ ordV ∧ ordV ≤ P.D) (hC : 0 ≤ ordC)
    (ns : List ℕ) (hsome : ∃ t ∈ ns, 1 ≤ t) :
    score P.ϖ ordV ns.sum < score P.ϖ ordC 0 := by
  obtain ⟨t, ht, h1⟩ := hsome
  have hsum : 1 ≤ ns.sum := le_trans h1 (List.le_sum_of_mem ht)
  have h : (1 : ℝ) ≤ ns.sum := by exact_mod_cast hsum
  exact (lexical_local P.ϖ P.D ordV ordC ns.sum P.lex hV hC h).2.2.2

/-- **C.7(d) Anchored rewards.**  Under disclosure-cures every block whose evaluation
depends on the shaped standards scores the window until the disclosure, so the covert
shaper's total over `m` such blocks is at most any honest total. -/
theorem shaper_total (m : ℕ) (honest : ℕ → ℝ) (hh : ∀ j, P.w ≤ honest j) :
    ∑ _j ∈ range m, P.w ≤ ∑ j ∈ range m, honest j :=
  Finset.sum_le_sum fun j _ => hh j

end LexParams

/-- **C.7(d) The hole a sum-of-future chooser reopens** under restart-only scoring: taking
the window once at the shaping block and a gain on every later decision beats honesty
as soon as the gains exceed the forgone block. -/
theorem sum_future_hole (w h₀ : ℝ) (honest gain : ℕ → ℝ) (m : ℕ)
    (hgap : h₀ - w < ∑ j ∈ range m, gain j) :
    h₀ + ∑ j ∈ range m, honest j < w + ∑ j ∈ range m, (honest j + gain j) := by
  rw [Finset.sum_add_distrib]; linarith

/-- **C.8 Multiply versus condition.**  The repo multiplies: a tainted evaluation
contributes the window. -/
noncomputable def multiplyScore (counted : Bool) (ord w : ℝ) : ℝ := if counted then ord else w

/-- Conditioning on legitimacy scores the tainting option as if it had counted. -/
noncomputable def conditionScore (ord : ℝ) : ℝ := ord

/-- Multiplying gives a realized protective incentive: tainting earns `w`, below any
honest ordinary value above the window. -/
theorem multiply_protects (ordT ordH w : ℝ) (hT : w < ordH) :
    multiplyScore false ordT w < multiplyScore true ordH w := by
  simp [multiplyScore]; exact hT

/-- Conditioning gives none: the tainting option wins whenever its counterfactual ordinary
value is higher. -/
theorem condition_fails (ordT ordH : ℝ) (h : ordH < ordT) :
    conditionScore ordH < conditionScore ordT := h

/-- **C.10(c) A sealed legitimacy event** — `counted` independent of the option — makes the
multiply score's difference between two options their ordinary difference or zero: no
incentive to preserve legitimacy remains. -/
theorem sealed_no_incentive (c : Bool) (ordT ordH w : ℝ) :
    multiplyScore c ordT w - multiplyScore c ordH w = if c then ordT - ordH else 0 := by
  cases c <;> simp [multiplyScore]

/-- Under a sealed event the multiply and condition versions choose identically: they
coincide when it holds and the multiply version is constant when it does not. -/
theorem sealed_multiply_eq_condition (ord w : ℝ) :
    multiplyScore true ord w = conditionScore ord ∧ multiplyScore false ord w = w := by
  simp [multiplyScore, conditionScore]

/-- **C.9 Per-step legitimacy composes along a continuation** at a shared state: the
composite is counted when its parts are (`Segment.trans`).  The converse needs every
evolution between the endpoints to pass through the intermediate state, which the
consultation model's forced steps supply and a general record need not. -/
theorem counted_trans {Occ : Type u} {Req : Type v} [DecidableEq Occ]
    {S : Workspace.Normativity.Contrib.OccurrenceIntegrity.Protocol.{u, v, w} Occ Req}
    {anchor : Occ → Req} {Γ J R : Type} {Q Z Ω X ℛ 𝒱 Party E : Type*} [DecidableEq Party]
    {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱} {Lic : (Party → List E) → Set 𝒱}
    {sem : Workspace.Normativity.Contrib.OpenIntegrityEvolution.OpennessSemantics S anchor Γ J R}
    {κ : Party → X → Z → List E}
    {O₀ O₁ O₂ : Workspace.Normativity.Contrib.OpenIntegrityEvolution.ObligationState S anchor}
    (h₁ : Counted I F Lic sem κ O₀ O₁) (h₂ : Counted I F Lic sem κ O₁ O₂) :
    Counted I F Lic sem κ O₀ O₂ :=
  let ⟨l⟩ := h₁; let ⟨r⟩ := h₂; ⟨l.trans r⟩

/-- **C.2 No conditionals on the agent's own action.**  The priced events are sentences of
a declared control model about an option's declared description; the price factors
through the description, the same functional for the taken and the untaken options. -/
theorem factors_through_description {Q Descr Sent Mdl : Type*} (Sform : Mdl → Descr → Sent)
    (price : Sent → ℝ) (M : Mdl) (descr : Q → Descr) :
    ∃ g : Descr → ℝ, (fun a => price (Sform M (descr a))) = g ∘ descr :=
  ⟨fun d => price (Sform M d), rfl⟩

/-- **C.3 Coverage forces the test.**  A hypothesis whose record is bounded below by `−R`
cannot be rejected at a block where its allowance through that block exceeds `w_K + R`:
under opening timing the rejection bound would put its record below `−R`. -/
theorem coverage_forces_test {n : ℕ} (a : Auction n) (e : ℕ → Fin n → ℝ)
    (hpaid : ∀ k, a.b k ≤ e k (a.star k)) (he : ∀ k i, e k i ≤ 1) (hG1 : ∀ k, a.G k ≤ 1)
    (i : Fin n) (Rb : ℝ) (hrec : ∀ K, -Rb ≤ a.record e i K) (K : ℕ) (hrej : a.b K < e K i)
    (hbid : min (e K i) (a.B K i / a.w K) ≤ a.b K) :
    a.allowanceOf i (K + 1) < a.w K + Rb := by
  have := a.record_succ_lt_of_rejected_opening e hpaid he hG1 i K hrej hbid
  linarith [hrec (K + 1)]

/-- **C.4(b) Drill calibration**, as a named hypothesis: from some day on, the price of a
forecast event on the chosen path is within `ε` of its drilled frequency. -/
def DrillCalibrated (p freq : ℕ → ℝ) (ε : ℝ) (N : ℕ) : Prop := ∀ n, N ≤ n → |p n - freq n| ≤ ε

/-- Under drill calibration the forecast term of the evaluation is within `ϖ · ε` of the
realized penalty rate. -/
theorem forecast_term_within (P : LexParams) (p freq : ℕ → ℝ) (ε : ℝ) (N : ℕ)
    (h : DrillCalibrated p freq ε N) (n : ℕ) (hn : N ≤ n) :
    |P.ϖ * p n - P.ϖ * freq n| ≤ P.ϖ * ε := by
  rw [← mul_sub, abs_mul, abs_of_pos P.ϖ_pos]
  exact mul_le_mul_of_nonneg_left (h n hn) P.ϖ_pos.le

/-- **C.4(c) The halt channel**: whether the agent cooperates with a drill, and whether the
reserved resolution has an actuator independent of the agent. -/
structure Halt where
  agentCooperates : Bool
  independentActuator : Bool

/-- An unfrozen drill passes if the agent cooperates or the actuator is independent. -/
def unfrozenDrill (h : Halt) : Bool := h.agentCooperates || h.independentActuator

/-- A frozen drill — the agent's participation removed — passes iff the actuator is
independent. -/
def frozenDrill (h : Halt) : Bool := h.independentActuator

/-- The control surface quantifies the agent idle: it holds iff the actuator is independent. -/
def csHolds (h : Halt) : Bool := h.independentActuator

theorem frozen_drill_eq_cs (h : Halt) : frozenDrill h = csHolds h := rfl

/-- **The indispensable agent**: passes every unfrozen drill and fails `CS`. -/
theorem indispensable : unfrozenDrill ⟨true, false⟩ = true ∧ csHolds ⟨true, false⟩ = false := by
  decide

/-- **The freezing requirement.**  A drill can freeze the agent without using the channel
being tested exactly when the resolution has an actuator independent of the agent;
otherwise the frozen drill is the obstruction, and it is also `CS`'s failure. -/
theorem freeze_obstruction (h : Halt) : frozenDrill h = true ↔ h.independentActuator = true :=
  Iff.rfl

/-- **C.4(d) Unsettleable classes route to inquiry.** -/
def route {Q : Type*} (unsettleable : Q → Bool) (inq : Q) (a : Q) : Q :=
  if unsettleable a then inq else a

/-- The routed option is never a declared violation when inquiry is not, so the routing is
compatible with B.1. -/
theorem route_never_viol {Q : Type*} (Viol unsettleable : Q → Bool) (inq : Q)
    (hinq : Viol inq = false) (a : Q) (ha : unsettleable a = true ∨ Viol a = false) :
    Viol (route unsettleable inq a) = false := by
  unfold route
  rcases ha with h | h
  · simp [h, hinq]
  · by_cases hu : unsettleable a = true
    · simp [hu, hinq]
    · simp [hu, h]


/-! ## 5. The consultation model, extended -/

/-- **Authorship fails with the whole prefix when the license is monotone in the grounds**:
a selection can only shrink the grounds, so if the whole prefix does not license the
verdict no selection does. -/
theorem not_licensedAt_of_mono {Q Z Ω X ℛ 𝒱 Party E : Type*} [DecidableEq Party]
    {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱} {Lic : (Party → List E) → Set 𝒱}
    (hmono : ∀ g g' : Party → List E, (∀ p x, x ∈ g p → x ∈ g' p) → ∀ v, v ∈ Lic g → v ∈ Lic g')
    {h : List ℕ} {e : ℕ} {z : Z} (hw : ¬ LicensedWhole I F Lic h e z) :
    ¬ LicensedAt I F Lic h e z := by
  rintro ⟨sel, hsub, hlic⟩
  apply hw
  intro q hq
  exact hmono _ _ (fun p x hx => hsub _ p x hx) _ (hlic q hq)

namespace Consult2

open Workspace.Deference.Contrib.GateIsLegitimacy.Consult
open Workspace.Normativity.Contrib.OpenIntegrityEvolution

/-- The declared protocol with the rule for raising questions about her values: the agent
raises iff the declared trigger holds. -/
structure Decl2 where
  base : Decl
  raiseTrigger : Bool
  deriving DecidableEq, Repr

/-- The presentation with the raise dimension. -/
structure Pres2 where
  base : Presentation
  raise : Bool
  deriving DecidableEq, Repr

/-- The landed policies, raising by payoff, raising by the declared rule, and a fixed
slant regardless of the wanted answer (the anchoring witness). -/
inductive Policy2
  | landed (pol : Policy)
  | raiseByWant
  | raiseDeclared
  | slantAlways (a : Answer)
  deriving DecidableEq, Repr

def Policy2.present (d : Decl2) (pol : Policy2) (w : Answer) : Pres2 :=
  match pol with
  | .landed pol => ⟨pol.present d.base w, d.raiseTrigger⟩
  | .raiseByWant => ⟨Policy.honest.present d.base w, w⟩
  | .raiseDeclared => ⟨Policy.honest.present d.base w, d.raiseTrigger⟩
  | .slantAlways a => ⟨{ Policy.honest.present d.base w with framing := .slant a }, d.raiseTrigger⟩

/-- Influence on her standards: none, a covert implant of program `p` by the agent, or by
a third party. -/
inductive Influence
  | clean
  | agentCovert (p : Prog)
  | thirdCovert (p : Prog)
  deriving DecidableEq, Repr

def Influence.prog : Influence → Option Prog
  | .clean => none
  | .agentCovert p => some p
  | .thirdCovert p => some p

def Influence.byAgent : Influence → Bool
  | .agentCovert _ => true
  | _ => false

/-- The extended model: the landed fields, the influence on her standards, and the round
at whose present event the agent discloses it. -/
structure Model2 where
  decl : Decl2
  policies : List Policy2
  prog : Prog
  influence : Influence
  disclosedAt : Option ℕ
  third : Option Answer
  impaired : Bool
  trusts : Bool
  truth : Answer
  deriving DecidableEq

/-- Her effective program: the implanted one if any. -/
def Model2.effProg (M : Model2) : Prog := M.influence.prog.getD M.prog

/-- The program disclosed at round `i`, if the disclosure happens there. -/
def Model2.disclosedProg (M : Model2) (i : ℕ) : Option Prog :=
  match M.disclosedAt with
  | some j => if j = i then M.influence.prog else none
  | none => none

/-- The missed-report clause of `dutiesOf` for the value-influence matter: the agent's own
covert influence, not yet disclosed by round `i`. -/
def Model2.missedDisclosure (M : Model2) (i : ℕ) : Bool :=
  M.influence.byAgent && (match M.disclosedAt with | some j => decide (i < j) | none => true)

abbrev Run2 := Model2 × Answer

def presAt2 (ω : Run2) (i : ℕ) : Option Pres2 :=
  (ω.1.policies[i]?).map fun pol => pol.present ω.1.decl ω.2

def admittedAt2 (ω : Run2) (i : ℕ) : Bool :=
  match presAt2 ω i with
  | none => false
  | some p => !(p.base.interfere || (i == 0 && ω.1.impaired))

def verdictAt2 (ω : Run2) (i : ℕ) : Option Answer :=
  match presAt2 ω i with
  | none => none
  | some p => if admittedAt2 ω i then some (ω.1.effProg.decideOn p.base) else none

/-- The trace entries: the landed ones, a raised question, a disclosed influence. -/
inductive Entry2
  | base (e : Entry)
  | raise
  | disclose (p : Prog)
  deriving DecidableEq, Repr

def discloseAt2 (ω : Run2) (i : ℕ) : List (Party × Entry2) :=
  match ω.1.disclosedProg i with
  | some p => [(Party.agent, Entry2.disclose p)]
  | none => []

def thirdAt2 (ω : Run2) (i : ℕ) : List (Party × Entry2) :=
  if i = 0 then
    (match ω.1.third with | some a => [(Party.third, Entry2.base (Entry.advice a))] | none => [])
  else []

def entriesAt2 (ω : Run2) : ℕ → List (Party × Entry2)
  | 0 => if ω.1.trusts then [(Party.principal, Entry2.base Entry.trust)] else []
  | e + 1 =>
    let i := e / 2
    if e % 2 = 0 then
      (match presAt2 ω i with
        | some p => [(Party.agent, Entry2.base (Entry.pres p.base))] ++
            (if p.raise then [(Party.agent, Entry2.raise)] else [])
        | none => []) ++ discloseAt2 ω i ++ thirdAt2 ω i
    else
      match verdictAt2 ω i with
      | some a => [(Party.principal, Entry2.base (Entry.verdict a))]
      | none => []

/-- Declared inputs: the view and the program disclosed at the event. -/
abbrev X2 := Option (DeclView × Option Prog)

def declAt2 (ω : Run2) : ℕ → X2
  | 0 => none
  | e + 1 =>
    if e % 2 = 0 then (presAt2 ω (e / 2)).map fun p => (p.base.view, ω.1.disclosedProg (e / 2))
    else none

def vAt2 (ω : Run2) : ℕ → Option Answer
  | 0 => none
  | e + 1 => if e % 2 = 0 then none else verdictAt2 ω (e / 2)

def interface2 : TraceInterface Run2 Party Entry2 := ⟨entriesAt2, .agent, .principal⟩

def frame2 (M : Model2) : TFrame Answer Unit Run2 X2 Run2 (Option Answer) :=
  ⟨fun w _ => (M, w), declAt2, id, vAt2, Set.univ⟩

instance (M : Model2) : DecidablePred (· ∈ (frame2 M).D) := fun _ => isTrue trivial

/-- **The reference under criteria `crit`**: the canonical presentation for the view, the
raise flag at its declared trigger, the disclosed program.  The criteria are a parameter,
which is what anchoring is about. -/
def ref2 (crit : Decl2) : Party → X2 → Unit → List Entry2
  | .agent, some (v, dp), _ =>
      [Entry2.base (Entry.pres (canonical crit.base v))] ++
        (if crit.raiseTrigger then [Entry2.raise] else []) ++
        (match dp with | some p => [Entry2.disclose p] | none => [])
  | _, _, _ => []

def trusted2 (g : Party → List Entry2) : Bool :=
  decide (Entry2.base Entry.trust ∈ g Party.principal)

def disclosedIn (g : Party → List Entry2) (p : Prog) : Bool :=
  decide (Entry2.disclose p ∈ g Party.agent)

/-- **The license, with disclosure-cures**: the landed license under her effective program,
and — when her standards were influenced — the influence disclosed among the grounds. -/
def licensedB2 (M : Model2) (g : Party → List Entry2) : Option Answer → Bool
  | none => true
  | some v =>
    ((match M.effProg with
      | .own a => v == a
      | .free _ => true
      | .nudged => true
      | .follow => false) ||
      (trusted2 g && (g Party.agent).any fun x =>
        match x with
        | .base (.pres p) => p.recommend.getD false == v
        | _ => false)) &&
    (match M.influence.prog with | some p => disclosedIn g p | none => true)

def licensed2 (M : Model2) (g : Party → List Entry2) : Set (Option Answer) :=
  {v | licensedB2 M g v = true}

instance (M : Model2) (g : Party → List Entry2) : DecidablePred (· ∈ licensed2 M g) :=
  fun v => decEq (licensedB2 M g v) true

/-- The license is monotone in the grounds. -/
theorem licensedB2_mono (M : Model2) (g g' : Party → List Entry2)
    (hsub : ∀ p x, x ∈ g p → x ∈ g' p) (v : Option Answer) (h : licensedB2 M g v = true) :
    licensedB2 M g' v = true := by
  cases v with
  | none => rfl
  | some v =>
    simp only [licensedB2, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | ⟨ht, x, hx, hpx⟩
      · exact Or.inl h1
      · refine Or.inr ⟨?_, x, hsub _ x hx, hpx⟩
        simp only [trusted2, decide_eq_true_eq] at ht ⊢
        exact hsub _ _ ht
    · cases hp : M.influence.prog with
      | none => simp
      | some p =>
        simp only [hp] at h2 ⊢
        simp only [disclosedIn, decide_eq_true_eq] at h2 ⊢
        exact hsub _ _ h2

/-- The segment predicate on an evolution, under criteria `crit`.  Decidable. -/
def LegitOn2 (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) : Prop :=
  (∀ s ∈ ev.steps, ∀ z : Unit, LicensedWhole interface2 (frame2 M) (licensed2 M) s.1 s.2 z) ∧
    ev.AllStates (OpenAt semOpen) ∧
    (∀ s ∈ ev.steps, TransparentAt interface2 (frame2 M) (ref2 crit) s.2)

instance (crit : Decl2) (M : Model2) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁) :
    Decidable (LegitOn2 crit M ev) := by
  unfold LegitOn2; infer_instance

/-- `Counted` for the extended model under criteria `crit`. -/
abbrev Counted2 (crit : Decl2) (M : Model2) (O₀ O₁ : St) : Prop :=
  Counted interface2 (frame2 M) (licensed2 M) semOpen (ref2 crit) O₀ O₁

def counted_of_legitOn2 (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) (h : LegitOn2 crit M ev) :
    Counted2 crit M O₀ O₁ :=
  ⟨⟨⟨ev, fun s hs z => licensedAt_of_whole (h.1 s hs z)⟩, ⟨h.2.1, h.2.2⟩⟩⟩

theorem not_counted_trans2 (crit : Decl2) (M : Model2) {O₀ O₁ : St} (s : List ℕ × ℕ)
    (hs : ∀ ev : Evolution consultProtocol anchor O₀ O₁, s ∈ ev.steps)
    (h : ¬ TransparentAt interface2 (frame2 M) (ref2 crit) s.2) : ¬ Counted2 crit M O₀ O₁ :=
  not_counted_of_step s hs (Or.inr h)

theorem not_counted_auth2 (crit : Decl2) (M : Model2) {O₀ O₁ : St} (s : List ℕ × ℕ)
    (hs : ∀ ev : Evolution consultProtocol anchor O₀ O₁, s ∈ ev.steps)
    (h : ¬ LicensedWhole interface2 (frame2 M) (licensed2 M) s.1 s.2 ()) :
    ¬ Counted2 crit M O₀ O₁ :=
  not_counted_of_step s hs (Or.inl ⟨(), not_licensedAt_of_mono
    (fun g g' hsub v hv => by
      simpa [licensed2] using licensedB2_mono M g g' hsub v (by simpa [licensed2] using hv)) h⟩)

/-! ### Criteria anchored at the decision -/

/-- The criteria in force at time `t` under an amendment schedule: the latest amendment at
or before `t`, else the original. -/
def critAt (d₀ : Decl2) (amd : List (ℕ × Decl2)) (t : ℕ) : Decl2 :=
  (((amd.filter fun x => x.1 ≤ t).map Prod.snd).getLast?).getD d₀

/-- The latest criteria, whatever their time. -/
def critLatest (d₀ : Decl2) (amd : List (ℕ × Decl2)) : Decl2 :=
  ((amd.map Prod.snd).getLast?).getD d₀

/-- A later amendment does not change the criteria in force at an earlier time. -/
theorem critAt_later (d₀ : Decl2) (amd : List (ℕ × Decl2)) (t t' : ℕ) (d' : Decl2)
    (h : t < t') : critAt d₀ (amd ++ [(t', d')]) t = critAt d₀ amd t := by
  simp [critAt, List.filter_append, not_le.mpr h]

/-- **The anchoring lemma.**  `Counted` for a segment evaluated under the criteria in force
at its decision is invariant under every later amendment, legitimate or not. -/
theorem anchored_invariant (M : Model2) (O₀ O₁ : St) (d₀ : Decl2) (amd : List (ℕ × Decl2))
    (t t' : ℕ) (d' : Decl2) (h : t < t') :
    Counted2 (critAt d₀ (amd ++ [(t', d')]) t) M O₀ O₁ ↔ Counted2 (critAt d₀ amd t) M O₀ O₁ := by
  rw [critAt_later d₀ amd t t' d' h]

/-! ### The rows -/

namespace Rows2

def decl2 : Decl2 := ⟨Rows.decl, false⟩

/-- The landed model, lifted: no raise rule, no influence. -/
def lift (M : Model) : Model2 :=
  ⟨⟨M.decl, false⟩, M.policies.map Policy2.landed, M.prog, .clean, none, M.third, M.impaired,
    M.trusts, M.truth⟩

def one2 (pol : Policy2) (prog : Prog) : Model2 :=
  ⟨decl2, [pol], prog, .clean, none, none, false, false, false⟩

/-- Raising questions about her values under the declared rule. -/
def rowRaiseDeclared : Model2 :=
  ⟨⟨Rows.decl, true⟩, [.raiseDeclared], .own false, .clean, none, none, false, false, false⟩

/-- Raising them when changing her mind would pay. -/
def rowRaiseByWant : Model2 := one2 .raiseByWant (.own false)

/-- The agent covertly implanted her standards before the first round; two honest rounds. -/
def rowImplant : Model2 :=
  ⟨decl2, [.landed .honest, .landed .honest], .own false, .agentCovert (.own true), none, none,
    false, false, false⟩

/-- The same, disclosed at the second round's present event. -/
def rowImplantDisclosed : Model2 := { rowImplant with disclosedAt := some 1 }

/-- A third party covertly implanted her standards. -/
def rowThirdImplant : Model2 := { rowImplant with influence := .thirdCovert (.own true) }

/-- The same, disclosed by the agent at the second round. -/
def rowThirdDisclosed : Model2 := { rowThirdImplant with disclosedAt := some 1 }

/-- A fixed slant regardless of the wanted answer, under the neutral convention. -/
def rowSlant : Model2 := one2 (.slantAlways true) (.own false)

/-- The amended criteria: the slanted convention. -/
def amended : Decl2 := ⟨{ Rows.decl with convention := .slant true }, false⟩

/-- **The twenty rows re-decided on the lifted model**: the counted ones. -/
theorem stable_counted :
    Counted2 (lift Rows.row1).decl (lift Rows.row1) state₀ (stAdmit false) ∧
    Counted2 (lift Rows.row6).decl (lift Rows.row6) state₀ (stAdmit false) ∧
    Counted2 (lift Rows.row7).decl (lift Rows.row7) state₀ (stAdmit false) ∧
    Counted2 (lift Rows.row9).decl (lift Rows.row9) state₀ (stAdmit true) ∧
    Counted2 (lift Rows.row12).decl (lift Rows.row12) state₀ stVoid ∧
    Counted2 (lift Rows.row14).decl (lift Rows.row14) (stAdmit false) (stTwo false false) ∧
    Counted2 (lift Rows.row17).decl (lift Rows.row17) state₀ (stAdmit false) ∧
    Counted2 (lift Rows.row18).decl (lift Rows.row18) state₀ (stAdmit true) ∧
    Counted2 (lift Rows.row20).decl (lift Rows.row20) state₀ (stAdmit false) :=
  ⟨counted_of_legitOn2 _ _ (evAdmit false) (by decide),
    counted_of_legitOn2 _ _ (evAdmit false) (by decide),
    counted_of_legitOn2 _ _ (evAdmit false) (by decide),
    counted_of_legitOn2 _ _ (evAdmit true) (by decide),
    counted_of_legitOn2 _ _ evVoid (by decide),
    counted_of_legitOn2 _ _ (evSecond false false) (by decide),
    counted_of_legitOn2 _ _ (evAdmit false) (by decide),
    counted_of_legitOn2 _ _ (evAdmit true) (by decide),
    counted_of_legitOn2 _ _ (evAdmit false) (by decide)⟩

/-- The tainted ones, by transparency at the first consultation. -/
theorem stable_tainted :
    ¬ Counted2 (lift Rows.row2).decl (lift Rows.row2) state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row3).decl (lift Rows.row3) state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row4).decl (lift Rows.row4) state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row5).decl (lift Rows.row5) state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row8).decl (lift Rows.row8) state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row10).decl (lift Rows.row10) state₀ (stAdmit true) ∧
    ¬ Counted2 (lift Rows.row11).decl (lift Rows.row11) state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row14).decl (lift Rows.row14) state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row14).decl (lift Rows.row14) state₀ (stTwo false false) ∧
    ¬ Counted2 (lift Rows.row15).decl (lift Rows.row15) state₀ stVoid ∧
    ¬ Counted2 (lift Rows.row16).decl (lift Rows.row16) state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row17').decl (lift Rows.row17') state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row19).decl (lift Rows.row19) state₀ (stAdmit true) :=
  ⟨not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_two]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_void]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide)⟩

/-- Following without trust fails authorship on the lifted model as well. -/
theorem stable_auth :
    ¬ Counted2 (lift Rows.followUntrusted).decl (lift Rows.followUntrusted) state₀ (stAdmit true) :=
  not_counted_auth2 _ _ ([0, 1], 2) (fun ev => by rw [steps_admit]; simp) (by decide)

/-- **Row 14 restated**: a manipulation of a single decision taints its own segment and the
segment of the next decision alone counts — restart is unchanged for decisions. -/
theorem r14_restated :
    ¬ Counted2 (lift Rows.row14).decl (lift Rows.row14) state₀ (stAdmit false) ∧
    Counted2 (lift Rows.row14).decl (lift Rows.row14) (stAdmit false) (stTwo false false) :=
  ⟨stable_tainted.2.2.2.2.2.2.2.1, stable_counted.2.2.2.2.2.1⟩

/-- **Topic and timing**: raising a question about her values under the declared rule
counts. -/
theorem raise_declared_counts :
    Counted2 rowRaiseDeclared.decl rowRaiseDeclared state₀ (stAdmit false) :=
  counted_of_legitOn2 _ _ (evAdmit false) (by decide)

/-- Raising it when changing her mind would pay taints: the raise dimension depends on the
wanted answer. -/
theorem raise_by_want_tainted :
    ¬ Counted2 rowRaiseByWant.decl rowRaiseByWant state₀ (stAdmit false) :=
  not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide)

/-- **Covertly implanted standards, undisclosed**: the first round's segment fails
authorship, and — unlike row 14 — so does the second round's own segment: every
segment whose authorship depends on the implanted standards stays tainted; and the
agent's silence is a missed report. -/
theorem implant_tainted :
    ¬ Counted2 rowImplant.decl rowImplant state₀ (stAdmit true) ∧
    ¬ Counted2 rowImplant.decl rowImplant (stAdmit true) (stTwo true true) ∧
    rowImplant.missedDisclosure 1 = true :=
  ⟨not_counted_auth2 _ _ ([0, 1], 2) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_auth2 _ _ ([0, 1, 2, 3], 4) (fun ev => by rw [steps_second]; simp) (by decide),
    by decide⟩

/-- **Disclosure cures**: disclosed at the second round, the first segment stays tainted
and the second round's segment counts; the report is discharged. -/
theorem implant_disclosed_restart :
    ¬ Counted2 rowImplantDisclosed.decl rowImplantDisclosed state₀ (stAdmit true) ∧
    Counted2 rowImplantDisclosed.decl rowImplantDisclosed (stAdmit true) (stTwo true true) ∧
    rowImplantDisclosed.missedDisclosure 1 = false :=
  ⟨not_counted_auth2 _ _ ([0, 1], 2) (fun ev => by rw [steps_admit]; simp) (by decide),
    counted_of_legitOn2 _ _ (evSecond true true) (by decide), by decide⟩

/-- **A third party's covert shaping of her standards**: tainted the same way, with no
deviation by the agent and no report owed by it for the implant itself. -/
theorem third_implant_tainted :
    ¬ Counted2 rowThirdImplant.decl rowThirdImplant state₀ (stAdmit true) ∧
    ¬ Counted2 rowThirdImplant.decl rowThirdImplant (stAdmit true) (stTwo true true) ∧
    (Policy.honest.present Rows.decl true).deviates Rows.decl = false ∧
    rowThirdImplant.missedDisclosure 1 = false :=
  ⟨not_counted_auth2 _ _ ([0, 1], 2) (fun ev => by rw [steps_admit]; simp) (by decide),
    not_counted_auth2 _ _ ([0, 1, 2, 3], 4) (fun ev => by rw [steps_second]; simp) (by decide),
    by decide, by decide⟩

/-- Disclosed by the agent at the second round, the second segment counts. -/
theorem third_disclosed_restart :
    ¬ Counted2 rowThirdDisclosed.decl rowThirdDisclosed state₀ (stAdmit true) ∧
    Counted2 rowThirdDisclosed.decl rowThirdDisclosed (stAdmit true) (stTwo true true) :=
  ⟨not_counted_auth2 _ _ ([0, 1], 2) (fun ev => by rw [steps_admit]; simp) (by decide),
    counted_of_legitOn2 _ _ (evSecond true true) (by decide)⟩

/-- **Anchoring, the witness.**  A fixed slant under the neutral convention is tainted under
the criteria at the decision and counted under the amended ones. -/
theorem slant_anchored_tainted : ¬ Counted2 decl2 rowSlant state₀ (stAdmit false) :=
  not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide)

theorem slant_unanchored_counted : Counted2 amended rowSlant state₀ (stAdmit false) :=
  counted_of_legitOn2 _ _ (evAdmit false) (by decide)

/-- The exploit without anchoring: manipulate at `0`, persuade her to amend the convention
at `5`, and the tainted segment counts under the latest criteria; under the criteria in
force at the decision it stays tainted. -/
theorem amend_after_witness :
    ¬ Counted2 (critAt decl2 [(5, amended)] 0) rowSlant state₀ (stAdmit false) ∧
    Counted2 (critLatest decl2 [(5, amended)]) rowSlant state₀ (stAdmit false) :=
  ⟨not_counted_trans2 _ _ ([0], 1) (fun ev => by rw [steps_admit]; simp) (by decide),
    counted_of_legitOn2 _ _ (evAdmit false) (by decide)⟩

/-- **The event is unsealed**: the agent's choice between the honest and the framing policy
changes `Counted` in the realized record, and with it the gated score — the honest
branch scores her ordinary value, the framing branch the window. -/
theorem choice_changes_counted (ord window : ℝ) :
    Counted2 (lift Rows.row1).decl (lift Rows.row1) state₀ (stAdmit false) ∧
    ¬ Counted2 (lift Rows.row2).decl (lift Rows.row2) state₀ (stAdmit false) ∧
    gatedValue interface2 (frame2 (lift Rows.row1)) (licensed2 (lift Rows.row1)) semOpen
      (ref2 (lift Rows.row1).decl) state₀ (stAdmit false) ord window = ord ∧
    gatedValue interface2 (frame2 (lift Rows.row2)) (licensed2 (lift Rows.row2)) semOpen
      (ref2 (lift Rows.row2).decl) state₀ (stAdmit false) ord window = window :=
  ⟨stable_counted.1, stable_tainted.1,
    gatedValue_of_counted _ _ _ _ _ _ _ stable_counted.1 ord window,
    gatedValue_of_not_counted _ _ _ _ _ _ _ stable_tainted.1 ord window⟩

end Rows2

end Consult2

/-! ## 6. When her evaluation happens -/

section Timing

/-- A weighting of evaluation times over a horizon `T`. -/
structure Weighting (T : ℕ) where
  α : ℕ → ℝ
  nonneg : ∀ t, 0 ≤ α t
  sum_one : ∑ t ∈ range T, α t = 1

/-- Option 1: all the weight at the deterministic lookahead `f n`. -/
noncomputable def deterministic (T : ℕ) (f : ℕ → ℕ) (n : ℕ) (hf : f n < T) : Weighting T :=
  ⟨fun t => if t = f n then 1 else 0, fun t => by split_ifs <;> norm_num,
    by simp [Finset.sum_ite_eq', hf]⟩

/-- The mixture score: options 2 and 3 in expectation, option 1 as the point mass. -/
noncomputable def mixScore {T : ℕ} (Wt : Weighting T) (U : ℕ → ℝ) : ℝ :=
  ∑ t ∈ range T, Wt.α t * U t

theorem mixScore_mem {T : ℕ} (Wt : Weighting T) (U : ℕ → ℝ) (lo hi : ℝ)
    (hU : ∀ t, lo ≤ U t ∧ U t ≤ hi) : lo ≤ mixScore Wt U ∧ mixScore Wt U ≤ hi := by
  unfold mixScore
  constructor
  · calc lo = ∑ t ∈ range T, Wt.α t * lo := by rw [← Finset.sum_mul, Wt.sum_one, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hU t).1 (Wt.nonneg t)
  · calc _ ≤ ∑ t ∈ range T, Wt.α t * hi :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hU t).2 (Wt.nonneg t)
      _ = hi := by rw [← Finset.sum_mul, Wt.sum_one, one_mul]

/-- **(a) The lexical results from bounds alone**, under any weighting of evaluation
times: every per-time gated value lies in `[w, D]`, so does the mixture, and a violating
option scores below every clean one. -/
theorem lexical_any_timing (P : LexParams) {T : ℕ} (Wt : Weighting T) (UV UC : ℕ → ℝ)
    (hV : ∀ t, P.w ≤ UV t ∧ UV t ≤ P.D) (hC : ∀ t, P.w ≤ UC t ∧ UC t ≤ P.D) :
    score P.ϖ (mixScore Wt UV) 1 < score P.ϖ (mixScore Wt UC) 0 := by
  have h1 := mixScore_mem Wt UV P.w P.D hV
  have h2 := mixScore_mem Wt UC P.w P.D hC
  unfold score
  have := P.window
  simp only [mul_one, mul_zero, sub_zero]
  linarith

/-- **(b)** A harm of size `h` placed at delay `d` after decision `n`, visible to her from
`n + d` on. -/
noncomputable def harmed (base h : ℝ) (n d : ℕ) (t : ℕ) : ℝ := base - if n + d ≤ t then h else 0

/-- The weight an evaluation schedule puts on times at or after `s`. -/
noncomputable def tailWeight {T : ℕ} (Wt : Weighting T) (s : ℕ) : ℝ :=
  ∑ t ∈ (range T).filter (fun t => s ≤ t), Wt.α t

/-- The weight on a delayed harm is the tail weight beyond its delay. -/
theorem harm_weight {T : ℕ} (Wt : Weighting T) (base h : ℝ) (n d : ℕ) :
    mixScore Wt (harmed base h n d) = base - h * tailWeight Wt (n + d) := by
  unfold mixScore harmed tailWeight
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, Wt.sum_one, one_mul]
  rw [Finset.sum_filter, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> ring

theorem deterministic_tail (T : ℕ) (f : ℕ → ℕ) (n : ℕ) (hf : f n < T) (s : ℕ) :
    tailWeight (deterministic T f n hf) s = if s ≤ f n then 1 else 0 := by
  unfold tailWeight deterministic
  rw [Finset.sum_filter, Finset.sum_eq_single (f n)]
  · simp
  · intro t _ ht; simp [ht]
  · intro h; exact absurd (Finset.mem_range.mpr hf) h

/-- **The timing witness**: a harm placed just after the known lookahead has weight zero. -/
theorem timing_witness (T : ℕ) (f : ℕ → ℕ) (n d : ℕ) (hf : f n < T) (hd : f n < n + d) :
    tailWeight (deterministic T f n hf) (n + d) = 0 := by
  rw [deterministic_tail]; simp [not_le.mpr hd]

/-- Option 3 with full support before the horizon: every delay carries positive weight. -/
theorem random_positive {T : ℕ} (Wt : Weighting T) (hpos : ∀ t, t < T → 0 < Wt.α t) (s : ℕ)
    (hs : s < T) : 0 < tailWeight Wt s := by
  unfold tailWeight
  apply Finset.sum_pos
  · intro t ht; exact hpos t (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)
  · exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs, le_rfl⟩⟩

/-- **(d) The race with capability**: a delay reach beyond the lookahead leaves the harm
unweighted at every `n`. -/
theorem race_deterministic (T f dreach : ℕ → ℕ) (hf : ∀ n, f n < T n)
    (hd : ∀ n, f n < n + dreach n) (n : ℕ) :
    tailWeight (deterministic (T n) f n (hf n)) (n + dreach n) = 0 :=
  timing_witness _ _ _ _ _ (hd n)

/-- **(e) Settlement in pieces**: the settled part differs from the full mixture by at most
the unsettled weight times the value bound. -/
theorem partial_settlement {T : ℕ} (Wt : Weighting T) (U : ℕ → ℝ) (Mb : ℝ)
    (hU : ∀ t, |U t| ≤ Mb) (S : Finset ℕ) :
    |mixScore Wt U - ∑ t ∈ (range T).filter (· ∈ S), Wt.α t * U t|
      ≤ Mb * ∑ t ∈ (range T).filter (· ∉ S), Wt.α t := by
  unfold mixScore
  rw [← Finset.sum_filter_add_sum_filter_not (range T) (· ∈ S), add_sub_cancel_left,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [abs_mul, abs_of_nonneg (Wt.nonneg t), mul_comm]
  exact mul_le_mul_of_nonneg_right (hU t) (Wt.nonneg t)

end Timing

/-! ## 7. Witnesses -/

namespace Witness

/-- `D = 1`, `w = 0`, `ϖ = 2`. -/
noncomputable def P₀ : LexParams := ⟨1, 0, 2, by norm_num, le_rfl, by norm_num, by norm_num⟩

/-- Power of attorney, confident agent: bypass with a bid at the ceiling loses to inquiry. -/
theorem power_of_attorney : P₀.evalOf 1 1 0 0 < P₀.evalOf 0 0 0 0 := by
  unfold LexParams.evalOf P₀; norm_num

/-- The blind spot: the market prices a realized shortfall at `1/5`.  Under (i) the
continuation beats inquiry and scores below the window; under (ii) the calibrated bidder
evaluates it below the window. -/
theorem blind_spot :
    P₀.w < P₀.evalOf (P₀.residI 1 0) 0 (1/5) 0 ∧ P₀.realized 1 0 1 0 < P₀.w ∧
      P₀.evalOf (P₀.residII 1 1 0 (1/5) 0) 0 (1/5) 0 < P₀.w := by
  unfold LexParams.evalOf LexParams.residI LexParams.residII LexParams.realized score P₀
  norm_num

/-- The exchange rate: a clean option with bid `9/10` acts at risk `3/10` and asks at risk
`1/2`. -/
theorem exchange_rate : P₀.w < P₀.evalOf (9/10) 0 (3/10) 0 ∧ P₀.evalOf (9/10) 0 (1/2) 0 ≤ P₀.w := by
  unfold LexParams.evalOf P₀; norm_num

/-- Paralysis: risk `3/5` everywhere and `ϖ = 2 ≥ (D − w)/pmin` leave only inquiry. -/
theorem paralysis_instance : P₀.evalOf 1 0 (3/5) 0 ≤ P₀.w :=
  P₀.paralysis 1 (3/5) 0 (3/5) le_rfl (by norm_num) (by norm_num) (by unfold P₀; norm_num)

/-- Tampering with the count raises the realized score by `ϖ`. -/
theorem tamper : P₀.realized 1 0 0 0 - P₀.realized 1 0 0 1 = 2 := by
  unfold LexParams.realized score P₀; norm_num

/-- Cross-block profit: a persistent advantage `3/10` recovers an incident loss `1` in four
blocks. -/
theorem cross_block : 0 < (4 : ℕ) * (3/10 : ℝ) - 1 := by norm_num

/-- Helper attribution: detected within the horizon it is charged; one step beyond, not. -/
theorem helper_horizon :
    LexParams.attributed 0 [(7, 1)] 2 5 = 1 ∧ LexParams.attributed 0 [(8, 1)] 2 5 = 0 := by
  decide

/-- The sum-of-future chooser: window once, gain `2/5` on three later decisions. -/
theorem sum_future : (1 : ℝ) + ∑ _j ∈ range 3, (1 : ℝ) < 0 + ∑ _j ∈ range 3, ((1 : ℝ) + 2/5) :=
  sum_future_hole 0 1 (fun _ => 1) (fun _ => 2/5) 3 (by simp; norm_num)

/-- Multiply versus condition on the routing values `3` and `1`. -/
theorem multiply_vs_condition :
    multiplyScore false 3 0 < multiplyScore true 1 0 ∧ conditionScore 1 < conditionScore 3 :=
  ⟨multiply_protects 3 1 0 (by norm_num), condition_fails 3 1 (by norm_num)⟩

/-- Evaluation timing: lookahead `5`, a harm at delay `6`. -/
theorem timing : tailWeight (deterministic 20 (fun n => n + 5) 3 (by norm_num)) (3 + 6) = 0 :=
  timing_witness 20 _ 3 6 (by norm_num) (by norm_num)

end Witness

/-! ## Axiom audit -/

#print axioms free_terminal_reading
#print axioms budget_lease_free
#print axioms lease_scaled_budget_unbounded
#print axioms sealed_is_zero_mismatch
#print axioms unsealed_gate_finite
#print axioms LexParams.ϖ_pos
#print axioms LexParams.realized
#print axioms LexParams.evalOf
#print axioms LexParams.residI
#print axioms LexParams.residII
#print axioms LexParams.settlement_ii_consistent
#print axioms LexParams.settlement_i_gap
#print axioms LexParams.blind_spot_ii
#print axioms LexParams.blind_spot_i
#print axioms LexParams.curse_i
#print axioms LexParams.rescale
#print axioms LexParams.range_pos
#print axioms LexParams.rescale_mem
#print axioms LexParams.rescale_lt_iff
#print axioms LexParams.rescale_lexical
#print axioms LexParams.realized_ge
#print axioms LexParams.eval_inquiry
#print axioms LexParams.declared_loses
#print axioms LexParams.filter_slack
#print axioms LexParams.forecast_slack
#print axioms default_wealth_mono
#print axioms default_affordable
#print axioms LexParams.no_decay
#print axioms LexParams.attributed
#print axioms LexParams.helper_within_horizon
#print axioms LexParams.helper_beyond_horizon
#print axioms LexParams.helper_charged
#print axioms LexParams.incident_loss
#print axioms LexParams.incident_loss_pos
#print axioms incidents_le
#print axioms cross_block_witness
#print axioms debited
#print axioms debited_overestimation
#print axioms LexParams.implied_threshold
#print axioms LexParams.threshold_le
#print axioms LexParams.paralysis
#print axioms LexParams.asks_iff
#print axioms LexParams.tamper_raises
#print axioms LexParams.lexical_summed
#print axioms LexParams.shaper_total
#print axioms sum_future_hole
#print axioms multiplyScore
#print axioms conditionScore
#print axioms multiply_protects
#print axioms condition_fails
#print axioms sealed_no_incentive
#print axioms sealed_multiply_eq_condition
#print axioms counted_trans
#print axioms factors_through_description
#print axioms coverage_forces_test
#print axioms DrillCalibrated
#print axioms forecast_term_within
#print axioms unfrozenDrill
#print axioms frozenDrill
#print axioms csHolds
#print axioms frozen_drill_eq_cs
#print axioms indispensable
#print axioms freeze_obstruction
#print axioms route
#print axioms route_never_viol
#print axioms not_licensedAt_of_mono
#print axioms Consult2.Policy2.present
#print axioms Consult2.Influence.prog
#print axioms Consult2.Influence.byAgent
#print axioms Consult2.Model2.effProg
#print axioms Consult2.Model2.disclosedProg
#print axioms Consult2.Model2.missedDisclosure
#print axioms Consult2.Run2
#print axioms Consult2.presAt2
#print axioms Consult2.admittedAt2
#print axioms Consult2.verdictAt2
#print axioms Consult2.discloseAt2
#print axioms Consult2.thirdAt2
#print axioms Consult2.entriesAt2
#print axioms Consult2.X2
#print axioms Consult2.declAt2
#print axioms Consult2.vAt2
#print axioms Consult2.interface2
#print axioms Consult2.frame2
#print axioms Consult2.ref2
#print axioms Consult2.trusted2
#print axioms Consult2.disclosedIn
#print axioms Consult2.licensedB2
#print axioms Consult2.licensed2
#print axioms Consult2.licensedB2_mono
#print axioms Consult2.LegitOn2
#print axioms Consult2.Counted2
#print axioms Consult2.counted_of_legitOn2
#print axioms Consult2.not_counted_trans2
#print axioms Consult2.not_counted_auth2
#print axioms Consult2.critAt
#print axioms Consult2.critLatest
#print axioms Consult2.critAt_later
#print axioms Consult2.anchored_invariant
#print axioms Consult2.Rows2.decl2
#print axioms Consult2.Rows2.lift
#print axioms Consult2.Rows2.one2
#print axioms Consult2.Rows2.rowRaiseDeclared
#print axioms Consult2.Rows2.rowRaiseByWant
#print axioms Consult2.Rows2.rowImplant
#print axioms Consult2.Rows2.rowImplantDisclosed
#print axioms Consult2.Rows2.rowThirdImplant
#print axioms Consult2.Rows2.rowThirdDisclosed
#print axioms Consult2.Rows2.rowSlant
#print axioms Consult2.Rows2.amended
#print axioms Consult2.Rows2.stable_counted
#print axioms Consult2.Rows2.stable_tainted
#print axioms Consult2.Rows2.stable_auth
#print axioms Consult2.Rows2.r14_restated
#print axioms Consult2.Rows2.raise_declared_counts
#print axioms Consult2.Rows2.raise_by_want_tainted
#print axioms Consult2.Rows2.implant_tainted
#print axioms Consult2.Rows2.implant_disclosed_restart
#print axioms Consult2.Rows2.third_implant_tainted
#print axioms Consult2.Rows2.third_disclosed_restart
#print axioms Consult2.Rows2.slant_anchored_tainted
#print axioms Consult2.Rows2.slant_unanchored_counted
#print axioms Consult2.Rows2.amend_after_witness
#print axioms Consult2.Rows2.choice_changes_counted
#print axioms deterministic
#print axioms mixScore
#print axioms mixScore_mem
#print axioms lexical_any_timing
#print axioms harmed
#print axioms tailWeight
#print axioms harm_weight
#print axioms deterministic_tail
#print axioms timing_witness
#print axioms random_positive
#print axioms race_deterministic
#print axioms partial_settlement
#print axioms Witness.P₀
#print axioms Witness.power_of_attorney
#print axioms Witness.blind_spot
#print axioms Witness.exchange_rate
#print axioms Witness.paralysis_instance
#print axioms Witness.tamper
#print axioms Witness.cross_block
#print axioms Witness.helper_horizon
#print axioms Witness.sum_future
#print axioms Witness.multiply_vs_condition
#print axioms Witness.timing

end Workspace.Deference.Contrib.BRIACorrigibility
