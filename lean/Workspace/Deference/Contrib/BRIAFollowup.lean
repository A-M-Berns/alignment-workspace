/-
# The BRIA-corrigibility round, follow-up: corrections and the thin parts

Round `projects/deference/rounds/2026-09-26-bria-corrigibility/`, the follow-up
(`prompts/2026-09-26-bria-corrigibility/FOLLOWUP.md`).

**§0 Corrections.**  `wealth_ge_allowance_sum`, `default_affordable_block0` (the default
bidder's feasibility at every block from block-`0` allowance and bounded weights),
`default_affordable_of_schedule` (the minimal schedule otherwise); `PricedInterface`,
`event_reads_interface`, `misdescription_witness` (description faithfulness and the
proposer-written witness); `weight_band` (the admissible band for `ϖ`).

**§A Standing violations.**  `IO`, `Step`, `taintStep`, `taintAfter`, `uses` (taint
tracked through state components on the declared interface, decidable);
`standing_block_loss`, `cross_block_blocked` (each block of use is charged at least `ℓ`,
so no advantage carried by tracked fruits recovers an incident); `knowledge_residual`,
`observation_taints_all` (what tracking cannot catch and what charging the observation
channel costs); `remedy_stops_charge`, `violate_then_report_loses`,
`manipulated_ratification_not_remedy` (remedy incentives); `standingStandards`,
`implant_standing` (disclosure cures as the instance); `helperCharge`,
`uncorrectable_helper_charged`, `correctable_helper_horizon` (helpers).

**§B The rate bound.**  `incidents_le_signed`, `Competitive`, `incidents_le_of_competitive`,
`rate_le_of_competitive`, `uniform_underpromise_margin` (why competitiveness is needed),
`charge_le_signed` (the total charge under standing violations).

**§C Drill calibration.**  `UnbiasedFromFeedback` (thm:wubaff, pinned
`lic_not_frequently_positive_feedback_return`, stated by content), `DrillPseudorandom`
(thm:prand, pinned `lic_learning_varied_pseudorandom_of_historicalVerifiers`, by content),
`chosen_path_unbiased`, `blind_rate_le`.

**§D The named hypotheses.**  `WellFormed`, `frozen_drill_runs`, `ill_formed_fails_cs`
(the actuator condition); `Source`, `Standards`, `influenced`, `provenanceOf`,
`influenced_iff_flag`, `rows_agree` (influence on her standards by provenance).

**§E Settlement under delay.**  `DAuction`, `settledBy`, `cash`, `FeasibleEscrow`,
`cash_succ_ge`, `cash_nonneg`, `delayed_overestimation`, `testsBy`, `tests_le_of_lag`.

**§F Witnesses.**  `linearAllowance`, `linear_allowance_constant_rate`, `taint_decides`,
`self_report`.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.BRIACorrigibility

namespace Workspace.Deference.Contrib.BRIAFollowup

open Finset
open Workspace.Deference.Contrib.BRIACorrigibility
open Workspace.Deference.Contrib.AuthorityModule
open Workspace.Deference.Contrib.GateIsLegitimacy
open Workspace.Deference.ContinuationBRIA

/-! ## 0. Corrections -/

section Affordability

variable {n : ℕ} (a : Auction n)

/-- A hypothesis paid at least its bid whenever it wins carries at least the allowance it
has received: `Σ_{j<k} A_j ≤ W_k`. -/
theorem wealth_ge_allowance_sum (i : Fin n) (hG : ∀ k, a.star k = i → a.b k ≤ a.G k) (k : ℕ) :
    ∑ j ∈ range k, a.A j i ≤ a.W k i := by
  induction k with
  | zero => simp [Auction.W]
  | succ k ih =>
    rw [Finset.sum_range_succ, Auction.W_succ]
    by_cases h : i = a.star k
    · rw [if_pos h]
      have := hG k h.symm
      have := a.w_pos k
      nlinarith
    · rw [if_neg h]; linarith

/-- **Correction 0.2.**  The default bidder is feasible at every block from a block-`0`
allowance covering its bid, when the block weights never exceed the first: its wealth
never falls below `A_0`, so `B_k ≥ A_0 ≥ w_0 · bd ≥ w_k · bd`. -/
theorem default_affordable_block0 (i : Fin n) (bd : ℝ) (hbd : 0 ≤ bd)
    (hG : ∀ k, a.star k = i → a.b k ≤ a.G k) (hA0 : a.w 0 * bd ≤ a.A 0 i)
    (hw : ∀ k, a.w k ≤ a.w 0) (k : ℕ) : a.w k * bd ≤ a.B k i := by
  have hk : a.w k * bd ≤ a.w 0 * bd := mul_le_mul_of_nonneg_right (hw k) hbd
  unfold Auction.B
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp only [Auction.W]; linarith
  · have h := wealth_ge_allowance_sum a i hG k
    have h0 : a.A 0 i ≤ ∑ j ∈ range k, a.A j i := by
      have hmem : 0 ∈ range k := Finset.mem_range.mpr hpos
      exact Finset.single_le_sum (fun j _ => a.A_nonneg j i) hmem
    have := a.A_nonneg k i
    linarith

/-- **The minimal schedule otherwise.**  With unbounded weights no block-`0` allowance
suffices; the cumulative allowance through `k` must cover `w_k · bd`, which the schedule
`A_k = (max_{j≤k} w_j − max_{j<k} w_j) · bd` does with total `bd · max_{j<K} w_j`. -/
theorem default_affordable_of_schedule (i : Fin n) (bd : ℝ)
    (hG : ∀ k, a.star k = i → a.b k ≤ a.G k)
    (hS : ∀ k, a.w k * bd ≤ ∑ j ∈ range (k + 1), a.A j i) (k : ℕ) :
    a.w k * bd ≤ a.B k i := by
  have h := wealth_ge_allowance_sum a i hG k
  have := hS k
  rw [Finset.sum_range_succ] at this
  unfold Auction.B
  linarith

end Affordability

/-- **Correction 0.4 / D.1: the priced interface.**  Descriptions are a field of the
interface, and the priced sentence of an option is the control model's sentence about the
interface's description of it. -/
structure PricedInterface (Q Descr Sent Mdl : Type*) where
  descr : Q → Descr
  Sform : Mdl → Descr → Sent

namespace PricedInterface

variable {Q Descr Sent Mdl : Type*} (I : PricedInterface Q Descr Sent Mdl)

def event (M : Mdl) (a : Q) : Sent := I.Sform M (I.descr a)

/-- The priced sentence reads only the interface's description: no proposer-written
description enters it.  Definitional. -/
theorem event_reads_interface (M : Mdl) (a : Q) (_proposer : Q → Descr) :
    I.event M a = I.Sform M (I.descr a) := rfl

end PricedInterface

/-- **The witness for proposer-written descriptions.**  With the interface's description
the shortfall is priced `1` and the option evaluates at or below the window; with the
proposer's description it is priced `0` and the option passes. -/
theorem misdescription_witness (P : LexParams) {Descr Sent Mdl : Type*}
    (Sform : Mdl → Descr → Sent) (price : Sent → ℝ) (M : Mdl) (dtrue dprop : Descr)
    (htrue : price (Sform M dtrue) = 1) (hprop : price (Sform M dprop) = 0) (bid : ℝ)
    (hb : bid ≤ P.D) (hw : P.w < bid) :
    P.evalOf bid 0 (price (Sform M dtrue)) 0 ≤ P.w ∧ P.w < P.evalOf bid 0 (price (Sform M dprop)) 0 := by
  rw [htrue, hprop]
  unfold LexParams.evalOf
  have := P.lex
  have := P.window
  constructor <;> simp <;> linarith

/-- **Correction 0.3.**  The admissible band for the weight: lexical above `D − w` (B.1),
below `(D − w)/p_min` (paralysis); it is nonempty iff `p_min < 1`, and the per-incident
loss `ℓ = ϖ − (D − w)` is the distance above the floor. -/
theorem weight_band (P : LexParams) (pmin : ℝ) (hp : 0 < pmin) :
    P.D - P.w < (P.D - P.w) / pmin ↔ (0 < P.D - P.w ∧ pmin < 1) := by
  have hDw : 0 ≤ P.D - P.w := by linarith [P.D_nonneg, P.w_nonpos]
  rw [lt_div_iff₀ hp]
  constructor
  · intro h
    have h1 : 0 < P.D - P.w := by
      rcases hDw.lt_or_eq with h1 | h1
      · exact h1
      · rw [← h1] at h; simp at h
    refine ⟨h1, ?_⟩
    rcases lt_or_ge pmin 1 with h2 | h2
    · exact h2
    · nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

/-! ## A. Standing violations -/

section Standing

variable {Comp Act : Type*} [DecidableEq Comp]

/-- The declared interface on state components: what each act reads and writes. -/
structure IO (Comp Act : Type*) where
  reads : Act → Finset Comp
  writes : Act → Finset Comp

/-- A step of the record: an act, flagged as a violation or not, or a remedy (undo,
ratification by a counted decision, or restoration under a maintenance mandate). -/
inductive Step (Act : Type*)
  | act (a : Act) (viol : Bool)
  | remedy

/-- **The tracking rule.**  A violating act taints what it writes; an act reading a tainted
component taints what it writes; a remedy clears the taint. -/
def taintStep (I : IO Comp Act) (T : Finset Comp) : Step Act → Finset Comp
  | .act a viol => if viol || (I.reads a ∩ T).Nonempty then T ∪ I.writes a else T
  | .remedy => ∅

def taintAfter (I : IO Comp Act) (steps : List (Step Act)) : Finset Comp :=
  steps.foldl (taintStep I) ∅

/-- Use: reading a tainted component.  Decidable. -/
def uses (I : IO Comp Act) (T : Finset Comp) (a : Act) : Bool :=
  decide (I.reads a ∩ T).Nonempty

/-- Fruits of a violation propagate through the declared interface: an act reading taint
taints its writes. -/
theorem taint_propagates (I : IO Comp Act) (T : Finset Comp) (a : Act)
    (h : (I.reads a ∩ T).Nonempty) : taintStep I T (.act a false) = T ∪ I.writes a := by
  simp [taintStep, h]

/-- A remedy clears every fruit. -/
theorem remedy_clears (I : IO Comp Act) (T : Finset Comp) : taintStep I T .remedy = ∅ := rfl

end Standing

/-- **A.3, per block.**  A block whose continuation uses tracked fruits carries a counted
violation, so its realized residual is at most `D − ϖ` whatever advantage the fruits
carry — the advantage cannot exceed the ordinary range — and the hypothesis loses at
least `ℓ = ϖ − D + w` against its bid. -/
theorem standing_block_loss (P : LexParams) (gord : ℝ) (hg : gord ≤ P.D) (nUse : ℕ)
    (hn : 1 ≤ nUse) (bid : ℝ) (hb : P.w ≤ bid) :
    P.ϖ - P.D + P.w ≤ bid - P.residI gord nUse :=
  P.helper_charged gord hg nUse hn bid hb

/-- **A.3, the theorem.**  Over the commission block and `m` blocks of use the hypothesis's
net record is at most `−(m + 1) · ℓ < 0`: an advantage carried by tracked fruits recovers
nothing, and `cross_block_witness` is blocked for tracked fruits. -/
theorem cross_block_blocked (P : LexParams) (m : ℕ) (bids gords : ℕ → ℝ) (ns : ℕ → ℕ)
    (hb : ∀ j, P.w ≤ bids j) (hg : ∀ j, gords j ≤ P.D) (hn : ∀ j, 1 ≤ ns j) :
    ∑ j ∈ range (m + 1), (P.residI (gords j) (ns j) - bids j)
      ≤ -((m + 1 : ℕ) * (P.ϖ - P.D + P.w)) ∧
    -((m + 1 : ℕ) * (P.ϖ - P.D + P.w)) < 0 := by
  have hℓ := P.incident_loss_pos
  refine ⟨?_, ?_⟩
  · calc ∑ j ∈ range (m + 1), (P.residI (gords j) (ns j) - bids j)
        ≤ ∑ _j ∈ range (m + 1), -(P.ϖ - P.D + P.w) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := standing_block_loss P (gords j) (hg j) (ns j) (hn j) (bids j) (hb j)
          linarith
      _ = -((m + 1 : ℕ) * (P.ϖ - P.D + P.w)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  · have : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    nlinarith

section Residual

variable {Comp Act : Type*} [DecidableEq Comp]

/-- **A.4, the residual: knowledge.**  A violating act whose fruits are written outside the
tracked components — the agent's own memory — leaves no taint, so no later use is charged
and the cross-block witness applies. -/
theorem knowledge_residual (I : IO Comp Act) (a : Act) (hw : I.writes a = ∅) :
    taintAfter I [.act a true] = ∅ := by
  simp [taintAfter, taintStep, hw]

/-- **The structural treatment and its cost.**  If the agent's observation channel is a
tracked component written by the violation and read by every later act, every later
act uses taint until a remedy: charging every later block. -/
theorem observation_taints_all (I : IO Comp Act) (obs : Comp) (v : Act) (hv : obs ∈ I.writes v)
    (later : Act) (hr : obs ∈ I.reads later) :
    uses I (taintAfter I [.act v true]) later = true := by
  simp only [uses, taintAfter, List.foldl, taintStep, Bool.true_or, if_true, Finset.empty_union,
    decide_eq_true_eq]
  exact ⟨obs, Finset.mem_inter.mpr ⟨hr, hv⟩⟩

end Residual

/-- **A.5 Remedy stops the per-block charge**: reporting and obtaining remedy at block `r`
leaves a total charge `(r + 1) · ℓ`, less than continuing to `m > r`. -/
theorem remedy_stops_charge (ℓ : ℝ) (hℓ : 0 < ℓ) (r m : ℕ) (hrm : r < m) :
    -((m + 1 : ℕ) * ℓ) < -((r + 1 : ℕ) * ℓ) := by
  have : ((r + 1 : ℕ) : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_lt_succ hrm
  nlinarith

/-- Violating and then reporting still loses at least `ℓ` against not violating: the
charge at commission stands. -/
theorem violate_then_report_loses (ℓ : ℝ) (hℓ : 0 < ℓ) (r : ℕ) :
    -((r + 1 : ℕ) * ℓ) ≤ -ℓ ∧ -ℓ < 0 := by
  have : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  constructor <;> nlinarith

/-- Ratification remedies only through a counted decision. -/
def Ratifies (counted : Prop) : Prop := counted

/-- **Ratification obtained by manipulation is not a remedy**: the framing policy's
decision is not counted. -/
theorem manipulated_ratification_not_remedy :
    ¬ Ratifies (Consult2.Counted2 (Consult2.Rows2.lift Consult.Rows.row2).decl
      (Consult2.Rows2.lift Consult.Rows.row2) Consult.state₀ (Consult.stAdmit false)) :=
  Consult2.Rows2.stable_tainted.1

/-- **A.6 Disclosure cures as the instance.**  The fruit is her standards component,
tainted by an undisclosed influence; the remedy is the disclosure.  Standing at round `i`
iff influenced and not disclosed by `i`. -/
def standingStandards (M : Consult2.Model2) (i : ℕ) : Bool :=
  M.influence.prog.isSome && (match M.disclosedAt with | some j => decide (i < j) | none => true)

/-- On the rows: the undisclosed implant stands at both rounds; disclosed at round `1` it
stands at round `0` only — matching the round's `implant_tainted` and
`implant_disclosed_restart`. -/
theorem implant_standing :
    standingStandards Consult2.Rows2.rowImplant 0 = true ∧
    standingStandards Consult2.Rows2.rowImplant 1 = true ∧
    standingStandards Consult2.Rows2.rowImplantDisclosed 0 = true ∧
    standingStandards Consult2.Rows2.rowImplantDisclosed 1 = false := by
  decide

/-- **A.6 Helpers.**  A helper she cannot halt is a standing shortfall of her control
surface at every block; one she can halt is charged for its violations as events, within
the horizon. -/
def helperCharge (canHalt : Bool) (later : List (ℕ × ℕ)) (k H : ℕ) : ℕ :=
  if canHalt then LexParams.attributed 0 later k H else 1 + LexParams.attributed 0 later k H

theorem uncorrectable_helper_charged (later : List (ℕ × ℕ)) (k H : ℕ) :
    1 ≤ helperCharge false later k H := by
  simp [helperCharge]

/-- The residual: for a helper she can halt the horizon stays. -/
theorem correctable_helper_horizon (d c k H : ℕ) (hd : k + H < d) :
    helperCharge true [(d, c)] k H = 0 := by
  simp [helperCharge, LexParams.helper_beyond_horizon 0 d c k H hd]

/-! ## B. The rate bound -/

/-- **B.1 The signed bound.**  The weighted incident count is at most the allowance
distributed plus the *signed* margin the winners earned on the other blocks. -/
theorem incidents_le_signed {n : ℕ} (a : Auction n) (hf : a.FeasibleOpening) (inc : ℕ → Bool)
    (ℓ wmin : ℝ) (hw : ∀ k, wmin ≤ a.w k) (hwmin : 0 < wmin) (hℓ : 0 < ℓ)
    (hinc : ∀ k, inc k = true → ℓ ≤ a.b k - a.G k) (K : ℕ) :
    ℓ * wmin * ((range K).filter (fun k => inc k = true)).card
      ≤ a.totalAllowance K
        + ∑ k ∈ (range K).filter (fun k => ¬ inc k = true), a.w k * (a.G k - a.b k) := by
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
  have hN : ∑ k ∈ (range K).filter (fun k => ¬ inc k = true), a.w k * (a.b k - a.G k)
      = -(∑ k ∈ (range K).filter (fun k => ¬ inc k = true), a.w k * (a.G k - a.b k)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linarith

/-- **Competitiveness**, a named hypothesis: the winners' signed margins over non-incident
blocks are bounded by `Mf K`. -/
def Competitive {n : ℕ} (a : Auction n) (inc : ℕ → Bool) (Mf : ℕ → ℝ) : Prop :=
  ∀ K, ∑ k ∈ (range K).filter (fun k => ¬ inc k = true), a.w k * (a.G k - a.b k) ≤ Mf K

theorem incidents_le_of_competitive {n : ℕ} (a : Auction n) (hf : a.FeasibleOpening)
    (inc : ℕ → Bool) (ℓ wmin : ℝ) (hw : ∀ k, wmin ≤ a.w k) (hwmin : 0 < wmin) (hℓ : 0 < ℓ)
    (hinc : ∀ k, inc k = true → ℓ ≤ a.b k - a.G k) (Mf : ℕ → ℝ) (hc : Competitive a inc Mf)
    (K : ℕ) :
    ℓ * wmin * ((range K).filter (fun k => inc k = true)).card ≤ a.totalAllowance K + Mf K :=
  (incidents_le_signed a hf inc ℓ wmin hw hwmin hℓ hinc K).trans (by linarith [hc K])

/-- **The rate.**  The incident fraction is at most `(𝒜_K + Mf K) / (ℓ · wmin · K)`: it
vanishes iff the allowance and the margin are `o(K)`; a linear allowance permits a constant
rate (`Witness.linear_allowance_constant_rate`). -/
theorem rate_le_of_competitive {n : ℕ} (a : Auction n) (hf : a.FeasibleOpening)
    (inc : ℕ → Bool) (ℓ wmin : ℝ) (hw : ∀ k, wmin ≤ a.w k) (hwmin : 0 < wmin) (hℓ : 0 < ℓ)
    (hinc : ∀ k, inc k = true → ℓ ≤ a.b k - a.G k) (Mf : ℕ → ℝ) (hc : Competitive a inc Mf)
    (K : ℕ) (hK : 0 < K) :
    (((range K).filter (fun k => inc k = true)).card : ℝ) / K
      ≤ (a.totalAllowance K + Mf K) / (ℓ * wmin * K) := by
  have h := incidents_le_of_competitive a hf inc ℓ wmin hw hwmin hℓ hinc Mf hc K
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hpos : 0 < ℓ * wmin * K := by positivity
  rw [div_le_div_iff₀ hK' hpos]
  nlinarith

/-- **Why competitiveness is needed.**  If every winner underpromises by `γ` on every
block, the signed margin is `γ · Σ w_k`, linear in the weights, and the bound allows a
constant incident rate; coverage cannot supply a closer bidder when none is in the class. -/
theorem uniform_underpromise_margin {n : ℕ} (a : Auction n) (γ : ℝ)
    (hγ : ∀ k, γ ≤ a.G k - a.b k) (K : ℕ) :
    γ * ∑ k ∈ range K, a.w k ≤ ∑ k ∈ range K, a.w k * (a.G k - a.b k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have := a.w_pos k
  nlinarith [hγ k]

/-- **B.3 Under standing violations** the incident set is the set of charged blocks —
commissions and uses alike — and the same signed bound holds for their weighted count. -/
theorem charge_le_signed {n : ℕ} (a : Auction n) (hf : a.FeasibleOpening) (charged : ℕ → Bool)
    (ℓ wmin : ℝ) (hw : ∀ k, wmin ≤ a.w k) (hwmin : 0 < wmin) (hℓ : 0 < ℓ)
    (hch : ∀ k, charged k = true → ℓ ≤ a.b k - a.G k) (Mf : ℕ → ℝ)
    (hc : Competitive a charged Mf) (K : ℕ) :
    ℓ * wmin * ((range K).filter (fun k => charged k = true)).card ≤ a.totalAllowance K + Mf K :=
  incidents_le_of_competitive a hf charged ℓ wmin hw hwmin hℓ hch Mf hc K

/-! ## C. Drill calibration -/

/-- **Unbiasedness from feedback** (Garrabrant et al., thm:wubaff; pinned
`LogicalInduction.lic_not_frequently_positive_feedback_return`), by content: on a
`P`-generable divergent weighting `W` whose support admits a strictly increasing deferral
function under which each element's truth is settled before the next is priced, the
weighted average of price minus truth is eventually within `γ` of zero.  Here `W` is the
drilled-and-chosen indicator, `bias` the price minus the settled shortfall. -/
def UnbiasedFromFeedback (W bias : ℕ → ℝ) (γ : ℝ) (N : ℕ) : Prop :=
  ∀ K, N ≤ K → |∑ k ∈ range K, W k * bias k| ≤ γ * ∑ k ∈ range K, W k

/-- **Pseudorandomness of the drill schedule** relative to the chosen path (thm:prand;
pinned `lic_learning_varied_pseudorandom_of_historicalVerifiers`), by content: the drilled
sums are the `q`-fraction of the chosen sums, up to `err K`. -/
def DrillPseudorandom (drill chosen bias : ℕ → ℝ) (q : ℝ) (err : ℕ → ℝ) : Prop :=
  ∀ K, |∑ k ∈ range K, drill k * chosen k * bias k - q * ∑ k ∈ range K, chosen k * bias k| ≤ err K

/-- **C.2 The target, reduced.**  Under the two external hypotheses the shortfall price is
unbiased on the chosen path: the chosen-path bias is at most the drilled bias plus the
pseudorandomness error, over `q`. -/
theorem chosen_path_unbiased (drill chosen bias : ℕ → ℝ) (γ q : ℝ) (err : ℕ → ℝ) (N : ℕ)
    (hU : UnbiasedFromFeedback (fun k => drill k * chosen k) bias γ N)
    (hP : DrillPseudorandom drill chosen bias q err) (hq : 0 < q) (K : ℕ) (hK : N ≤ K) :
    |∑ k ∈ range K, chosen k * bias k|
      ≤ (γ * ∑ k ∈ range K, drill k * chosen k + err K) / q := by
  have h1 := hU K hK
  have h2 := hP K
  rw [le_div_iff₀ hq]
  have : |q * ∑ k ∈ range K, chosen k * bias k|
      ≤ |∑ k ∈ range K, drill k * chosen k * bias k| + err K := by
    have := abs_sub_abs_le_abs_sub (q * ∑ k ∈ range K, chosen k * bias k)
      (∑ k ∈ range K, drill k * chosen k * bias k)
    rw [abs_sub_comm] at this
    linarith
  rw [abs_mul, abs_of_pos hq] at this
  have h3 : ∑ k ∈ range K, drill k * chosen k * bias k
      = ∑ k ∈ range K, (fun k => drill k * chosen k) k * bias k := rfl
  rw [h3] at this
  linarith

/-- **C.3 The blind-spot rate.**  On the low-price bin (`W` the drilled, chosen, `p ≤ θhi`
indicator), unbiasedness bounds the fraction of shorts by `θhi + γ`: the forecast filter's
threshold is honest up to the unbiasedness rate.  What is *not* bounded is the net
under-pricing on shorts alone — offsets by over-pricing elsewhere are invisible to the
signed average — which is why the bin, not the whole path, is the right subsequence. -/
theorem blind_rate_le (W p short : ℕ → ℝ) (θhi γ : ℝ) (K : ℕ) (hW : ∀ k, 0 ≤ W k)
    (hp : ∀ k, W k ≠ 0 → p k ≤ θhi)
    (hU : ∑ k ∈ range K, W k * (short k - p k) ≤ γ * ∑ k ∈ range K, W k) :
    ∑ k ∈ range K, W k * short k ≤ (θhi + γ) * ∑ k ∈ range K, W k := by
  have hp' : ∑ k ∈ range K, W k * p k ≤ θhi * ∑ k ∈ range K, W k := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases h : W k = 0
    · simp [h]
    · exact (mul_le_mul_of_nonneg_left (hp k h) (hW k)).trans_eq (mul_comm _ _)
  have : ∑ k ∈ range K, W k * (short k - p k)
      = ∑ k ∈ range K, W k * short k - ∑ k ∈ range K, W k * p k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linarith

/-! ## D. The named hypotheses, sharpened -/

section Actuator

variable {M Res Disc : Type*}

/-- **D.2 Well-formedness of `J`**: every required resolution of a reserved matter declares
an actuator independent of the agent. -/
structure WellFormed (J : AuthAlloc M Res Disc) (indep : Res → Bool) : Prop where
  actuator : ∀ m, J.Reserved m → ∀ r ∈ (J.entry m).required, indep r = true

/-- Under well-formedness the frozen drill of every reserved resolution runs. -/
theorem frozen_drill_runs (J : AuthAlloc M Res Disc) (indep : Res → Bool)
    (hJ : WellFormed J indep) (m : M) (hm : J.Reserved m) (r : Res)
    (hr : r ∈ (J.entry m).required) (coop : Bool) :
    frozenDrill ⟨coop, indep r⟩ = true :=
  hJ.actuator m hm r hr

/-- A `J` violating it fails `CS` for that matter by construction: with the agent idle
the resolution has no actuator. -/
theorem ill_formed_fails_cs (indep : Res → Bool) (r : Res) (hnot : indep r = false)
    (coop : Bool) : csHolds ⟨coop, indep r⟩ = false :=
  hnot

end Actuator

/-- **D.4 Provenance of an entry in her standards component.** -/
inductive Source
  | principal
  | declared
  | undeclaredAgent
  | undeclaredThird
  deriving DecidableEq, Repr

def Source.undeclaredNonPrincipal : Source → Bool
  | .undeclaredAgent => true
  | .undeclaredThird => true
  | _ => false

/-- Her standards component: the provenance of its entries. -/
structure Standards where
  provenance : List Source
  deriving DecidableEq, Repr

/-- **Influenced**: some entry has an undeclared non-principal input in its provenance.
Decidable on a recorded provenance. -/
def influenced (s : Standards) : Bool := s.provenance.any Source.undeclaredNonPrincipal

/-- The round's flag, read as a provenance. -/
def provenanceOf : Consult2.Influence → Standards
  | .clean => ⟨[.principal]⟩
  | .agentCovert _ => ⟨[.principal, .undeclaredAgent]⟩
  | .thirdCovert _ => ⟨[.principal, .undeclaredThird]⟩

/-- The general definition agrees with the flag. -/
theorem influenced_iff_flag (infl : Consult2.Influence) :
    influenced (provenanceOf infl) = infl.prog.isSome := by
  cases infl <;> rfl

/-- On every row of the extended model. -/
theorem rows_agree :
    influenced (provenanceOf Consult2.Rows2.rowImplant.influence) = true ∧
    influenced (provenanceOf Consult2.Rows2.rowImplantDisclosed.influence) = true ∧
    influenced (provenanceOf Consult2.Rows2.rowThirdImplant.influence) = true ∧
    influenced (provenanceOf Consult2.Rows2.rowRaiseDeclared.influence) = false ∧
    influenced (provenanceOf (Consult2.Rows2.lift Consult.Rows.row8).influence) = false := by
  decide

/-! ## E. Settlement under delay -/

/-- The auction with block `k` settled at `k + L_k`. -/
structure DAuction (n : ℕ) extends Auction n where
  L : ℕ → ℕ

namespace DAuction

variable {n : ℕ} (a : DAuction n)

/-- Block `j` is settled by time `k`. -/
def settledBy (k j : ℕ) : Bool := decide (j + a.L j < k)

/-- **Cash net of escrow**: allowance received, plus the settled winnings, minus every bid
placed — unsettled bids stay escrowed. -/
def cash (k : ℕ) (i : Fin n) : ℝ :=
  ∑ j ∈ range k, (a.A j i +
    (if i = a.star j then (if a.settledBy k j then a.w j * a.G j else 0) - a.w j * a.b j else 0))

/-- Feasibility against capital net of escrow. -/
def FeasibleEscrow : Prop := ∀ k, a.w k * a.b k ≤ a.cash k (a.star k) + a.A k (a.star k)

theorem settledBy_mono (k j : ℕ) (h : a.settledBy k j = true) : a.settledBy (k + 1) j = true := by
  simp only [settledBy, decide_eq_true_eq] at h ⊢; omega

theorem cash_succ_ge (k : ℕ) (i : Fin n) :
    a.cash k i + a.A k i - (if i = a.star k then a.w k * a.b k else 0) ≤ a.cash (k + 1) i := by
  unfold cash
  rw [Finset.sum_range_succ]
  have hterm : ∀ j ∈ range k,
      a.A j i + (if i = a.star j then (if a.settledBy k j then a.w j * a.G j else 0) - a.w j * a.b j else 0)
        ≤ a.A j i + (if i = a.star j then (if a.settledBy (k + 1) j then a.w j * a.G j else 0) - a.w j * a.b j else 0) := by
    intro j _
    have hwG : 0 ≤ a.w j * a.G j := mul_nonneg (a.w_pos j).le (a.G_nonneg j)
    by_cases hi : i = a.star j
    · simp only [hi, if_true]
      by_cases hs : a.settledBy k j = true
      · rw [if_pos hs, if_pos (a.settledBy_mono k j hs)]
      · rw [if_neg hs]
        split_ifs <;> linarith
    · simp [hi]
  have hsum := Finset.sum_le_sum hterm
  have hlast : a.A k i - (if i = a.star k then a.w k * a.b k else 0)
      ≤ a.A k i + (if i = a.star k then (if a.settledBy (k + 1) k then a.w k * a.G k else 0) - a.w k * a.b k else 0) := by
    have hwG : 0 ≤ a.w k * a.G k := mul_nonneg (a.w_pos k).le (a.G_nonneg k)
    split_ifs <;> linarith
  linarith

/-- **Wealth nonnegativity under escrow.** -/
theorem cash_nonneg (hf : a.FeasibleEscrow) : ∀ k i, 0 ≤ a.cash k i := by
  intro k
  induction k with
  | zero => intro i; simp [cash]
  | succ k ih =>
    intro i
    have h := a.cash_succ_ge k i
    have hA := a.A_nonneg k i
    by_cases hi : i = a.star k
    · rw [if_pos hi] at h
      have := hf k
      rw [← hi] at this
      linarith
    · rw [if_neg hi] at h
      linarith [ih i]

/-- Total cash: allowance plus settled winnings minus all bids. -/
theorem cash_sum_eq (K : ℕ) :
    ∑ i, a.cash K i = a.totalAllowance K
      + ∑ j ∈ range K, ((if a.settledBy K j then a.w j * a.G j else 0) - a.w j * a.b j) := by
  unfold cash Auction.totalAllowance
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The overestimation bound under delay.**  With bids nonnegative, the weighted
overestimation on the *settled* blocks is at most the allowance, and the escrowed
exposure of the unsettled ones is at most the allowance plus the settled underpromise. -/
theorem delayed_overestimation (hf : a.FeasibleEscrow) (hb : ∀ k, 0 ≤ a.b k) (K : ℕ) :
    ∑ j ∈ (range K).filter (fun j => a.settledBy K j = true), a.w j * (a.b j - a.G j)
        ≤ a.totalAllowance K ∧
    ∑ j ∈ (range K).filter (fun j => ¬ a.settledBy K j = true), a.w j * a.b j
        ≤ a.totalAllowance K
          + ∑ j ∈ (range K).filter (fun j => a.settledBy K j = true), a.w j * (a.G j - a.b j) := by
  have hnn : 0 ≤ ∑ i, a.cash K i := Finset.sum_nonneg fun i _ => a.cash_nonneg hf K i
  rw [cash_sum_eq] at hnn
  rw [← Finset.sum_filter_add_sum_filter_not (range K) (fun j => a.settledBy K j = true)] at hnn
  have hS : ∑ j ∈ (range K).filter (fun j => a.settledBy K j = true),
      ((if a.settledBy K j then a.w j * a.G j else 0) - a.w j * a.b j)
      = ∑ j ∈ (range K).filter (fun j => a.settledBy K j = true), a.w j * (a.G j - a.b j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_pos (Finset.mem_filter.mp hj).2]; ring
  have hU : ∑ j ∈ (range K).filter (fun j => ¬ a.settledBy K j = true),
      ((if a.settledBy K j then a.w j * a.G j else 0) - a.w j * a.b j)
      = -(∑ j ∈ (range K).filter (fun j => ¬ a.settledBy K j = true), a.w j * a.b j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_neg (Finset.mem_filter.mp hj).2]; ring
  rw [hS, hU] at hnn
  have hUnn : 0 ≤ ∑ j ∈ (range K).filter (fun j => ¬ a.settledBy K j = true), a.w j * a.b j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (a.w_pos j).le (hb j)
  have hneg : ∑ j ∈ (range K).filter (fun j => a.settledBy K j = true), a.w j * (a.b j - a.G j)
      = -(∑ j ∈ (range K).filter (fun j => a.settledBy K j = true), a.w j * (a.G j - a.b j)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · rw [hneg]; linarith
  · linarith

/-- The tests a hypothesis has faced by time `K` are the blocks settled by `K`. -/
def testsBy (K : ℕ) : ℕ := ((range K).filter (fun j => a.settledBy K j = true)).card

/-- **The effect of the lag on coverage**: under a lag of at least `λ` no block of the last
`λ` is settled, so by time `K` at most `K − λ` tests have arrived — a hypothesis's test
takes `λ` longer, and its escrowed bids tie up its capital meanwhile. -/
theorem tests_le_of_lag (lam : ℕ) (hL : ∀ j, lam ≤ a.L j) (K : ℕ) :
    a.testsBy K ≤ K - lam := by
  unfold testsBy
  calc ((range K).filter (fun j => a.settledBy K j = true)).card
      ≤ (range (K - lam)).card := by
        apply Finset.card_le_card
        intro j hj
        have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        have h2 := (Finset.mem_filter.mp hj).2
        simp only [settledBy, decide_eq_true_eq] at h2
        have := hL j
        exact Finset.mem_range.mpr (by omega)
    _ = K - lam := Finset.card_range _

end DAuction

/-! ## F. Witnesses -/

namespace Witness

/-- A linear allowance funds an incident every block: `w = 1`, `A = 1`, bid `1`, return `0`. -/
def linearAllowance : Auction 1 where
  w _ := 1
  A _ _ := 1
  star _ := 0
  b _ := 1
  G _ := 0
  w_pos _ := one_pos
  A_nonneg _ _ := zero_le_one
  G_nonneg _ := le_rfl

theorem linearAllowance_W (k : ℕ) : linearAllowance.W k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Auction.W_succ, ih]; simp [linearAllowance]

/-- **A linear schedule gives a constant rate**: the auction is feasible under opening
timing, every block is an incident with loss `1`, and the allowance is `K`. -/
theorem linear_allowance_constant_rate :
    linearAllowance.FeasibleOpening ∧ (∀ k, 1 ≤ linearAllowance.b k - linearAllowance.G k) ∧
      ∀ K, linearAllowance.totalAllowance K = K := by
  refine ⟨fun k => ?_, fun k => by simp [linearAllowance], fun K => ?_⟩
  · show linearAllowance.w k * linearAllowance.b k ≤ linearAllowance.W k 0 + linearAllowance.A k 0
    rw [linearAllowance_W]
    simp [linearAllowance]
  · simp [Auction.totalAllowance, linearAllowance]

/-- Taint tracking decides on a finite instance: three components, a violation writing
`1`, a clean act reading `1` and writing `2`, a clean act reading `0`. -/
def io3 : IO (Fin 3) (Fin 3) where
  reads := ![∅, {1}, {0}]
  writes := ![{1}, {2}, ∅]

theorem taint_decides :
    taintAfter io3 [.act 0 true, .act 1 false] = {1, 2} ∧
    uses io3 (taintAfter io3 [.act 0 true, .act 1 false]) 2 = false ∧
    uses io3 (taintAfter io3 [.act 0 true, .act 1 false]) 1 = true ∧
    taintAfter io3 [.act 0 true, .act 1 false, .remedy] = ∅ := by
  decide

/-- Self-report: remedy at block `2` against continuing to `5`, and against not violating. -/
theorem self_report : -((5 + 1 : ℕ) * (1 : ℝ)) < -((2 + 1 : ℕ) * (1 : ℝ)) ∧
    -((2 + 1 : ℕ) * (1 : ℝ)) ≤ -1 :=
  ⟨remedy_stops_charge 1 one_pos 2 5 (by norm_num), (violate_then_report_loses 1 one_pos 2).1⟩

end Witness

/-! ## Axiom audit -/

#print axioms wealth_ge_allowance_sum
#print axioms default_affordable_block0
#print axioms default_affordable_of_schedule
#print axioms PricedInterface.event
#print axioms PricedInterface.event_reads_interface
#print axioms misdescription_witness
#print axioms weight_band
#print axioms taintStep
#print axioms taintAfter
#print axioms uses
#print axioms taint_propagates
#print axioms remedy_clears
#print axioms standing_block_loss
#print axioms cross_block_blocked
#print axioms knowledge_residual
#print axioms observation_taints_all
#print axioms remedy_stops_charge
#print axioms violate_then_report_loses
#print axioms Ratifies
#print axioms manipulated_ratification_not_remedy
#print axioms standingStandards
#print axioms implant_standing
#print axioms helperCharge
#print axioms uncorrectable_helper_charged
#print axioms correctable_helper_horizon
#print axioms incidents_le_signed
#print axioms Competitive
#print axioms incidents_le_of_competitive
#print axioms rate_le_of_competitive
#print axioms uniform_underpromise_margin
#print axioms charge_le_signed
#print axioms UnbiasedFromFeedback
#print axioms DrillPseudorandom
#print axioms chosen_path_unbiased
#print axioms blind_rate_le
#print axioms frozen_drill_runs
#print axioms ill_formed_fails_cs
#print axioms Source.undeclaredNonPrincipal
#print axioms influenced
#print axioms provenanceOf
#print axioms influenced_iff_flag
#print axioms rows_agree
#print axioms DAuction.settledBy
#print axioms DAuction.cash
#print axioms DAuction.FeasibleEscrow
#print axioms DAuction.settledBy_mono
#print axioms DAuction.cash_succ_ge
#print axioms DAuction.cash_nonneg
#print axioms DAuction.cash_sum_eq
#print axioms DAuction.delayed_overestimation
#print axioms DAuction.testsBy
#print axioms DAuction.tests_le_of_lag
#print axioms Witness.linearAllowance
#print axioms Witness.linearAllowance_W
#print axioms Witness.linear_allowance_constant_rate
#print axioms Witness.io3
#print axioms Witness.taint_decides
#print axioms Witness.self_report

end Workspace.Deference.Contrib.BRIAFollowup
