/-
# After things go wrong: compromised evaluations, advance directives, and the knowledge residual

Round `projects/deference/rounds/2026-09-26-after-compromise/`
(`prompts/2026-09-26-after-compromise/PROMPT.md`).

**§1 The split gate.**  `StepLegit`, `TrajLegitOn`, `EvalLegitOn`, `legitOn2_iff_split`
(the landed segment predicate is the conjunction at any evaluation event),
`counted_of_split` (the old-to-new map for `Counted`), `rows_split` (representative rows
under the split, by `decide`), `retro_row` (the row where the evaluation is legitimate
after restoration while the period is not).

**§2 The band and the score.**  `Band`, `BandMap`, `Band.affine`, `Band.affine_bandMap`,
`Source`, `Source.Valid`, `sourceOf`, `bandScore`, `decScore`; `decScore_mem` (a);
`capture_window_band`, `unsealed_gate_finite_band`, `bandParams`, `declared_loses_band`,
`exchange_rate_band` (the authority results with `w := w_lo`); `legit_beats_compromised`,
`gap_at_equal_value` (b); `risk_accepted_iff`, `risk_threshold_le`, `Witness.small_gap`
(c); `laundering_loses` (d); `restore_future`, `band_prefers_better`, `floor_indifferent`
(e); `suppression_loses`, `ruleAt`, `ruleAt_later`, `missedKnownDisclosure`,
`third_party_duty_witness` (f).

**§3 The advance directive.**  `dirSource`, `scope_restriction` (B.1); `materialDir`,
`Sparser`, `sparser_asks`, `materialDir_total`, `raisesAnchoredDir`,
`raisesAnchoredDir_invariant`, `Witness.sparse_routes` (B.2, B.4);
`DefaultClauses`, `defaultRank`, `defaultScore`, `defaultScore_mem`,
`default_below_legit`, `default_prefers_reversible`, `reversibleOf` (B.3);
`directive_stakes_le_width`, `advocacy_dominated` (B.5).

**§4 The knowledge residual.**  `knowledge_covered` (C.1); `Step3`, `TaintS`, `uses3`,
`applyStep3`, `scoped_clears_out_of_scope`, `scoped_keeps_in_scope`,
`applyRatification`, `ratification_gate`, `manipulated_scoped_not_remedy` (C.2);
`taintStep3`, `clean_overwrite`, `taint_propagates3`, `taintStep3_subset` (C.3);
`TwinMarket`, `leakage` (C.4); `post_commission_competitive`, `Witness.private_selection`
(C.6).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.GateIsLegitimacy
import Workspace.Deference.Contrib.BRIAFollowup2
import Workspace.Deference.Contrib.AuthorityModule
import Workspace.Deference.Contrib.DecisionComponent

namespace Workspace.Deference.Contrib.AfterCompromise

open Finset
open Workspace.Deference.Contrib.GateIsLegitimacy
open Workspace.Deference.Contrib.GateIsLegitimacy.Consult
open Workspace.Deference.Contrib.BRIACorrigibility
open Workspace.Deference.Contrib.BRIACorrigibility.Consult2
open Workspace.Deference.Contrib.BRIAFollowup
open Workspace.Deference.Contrib.BRIAFollowup2
open Workspace.Deference.Contrib.AuthorityModule
open Workspace.Deference.Contrib.DecisionComponent
open Workspace.Deference.ContinuationBRIA
open Workspace.Normativity.Contrib.OpenIntegrityEvolution
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem (score)
open Workspace.Deference.Contrib.Corrigibilization (Interaction)
open LogicalInduction

/-! ## 1. The split gate -/

section Split

/-- A step is legitimate: her response at it licensed by the whole prefix, and the event
transparent under the criteria. -/
def StepLegit (crit : Decl2) (M : Model2) (s : List ℕ × ℕ) : Prop :=
  (∀ z : Unit, LicensedWhole interface2 (frame2 M) (licensed2 M) s.1 s.2 z) ∧
    TransparentAt interface2 (frame2 M) (ref2 crit) s.2

instance (crit : Decl2) (M : Model2) (s : List ℕ × ℕ) : Decidable (StepLegit crit M s) := by
  unfold StepLegit; infer_instance

/-- **`TrajLegit(d, e)`**: on the evolution from the decision, every state is open and
every step other than the evaluation event `e` is legitimate — no illegitimate influence
on her decisions in the period, under the criteria fixed at the decision. -/
def TrajLegitOn (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) (e : ℕ) : Prop :=
  ev.AllStates (OpenAt semOpen) ∧ ∀ s ∈ ev.steps, s.2 ≠ e → StepLegit crit M s

/-- **`EvalLegit(e)`**: the evaluation step itself is legitimate. -/
def EvalLegitOn (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) (e : ℕ) : Prop :=
  ∀ s ∈ ev.steps, s.2 = e → StepLegit crit M s

instance (crit : Decl2) (M : Model2) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁)
    (e : ℕ) : Decidable (TrajLegitOn crit M ev e) := by
  unfold TrajLegitOn; infer_instance

instance (crit : Decl2) (M : Model2) {O₀ O₁ : St} (ev : Evolution consultProtocol anchor O₀ O₁)
    (e : ℕ) : Decidable (EvalLegitOn crit M ev e) := by
  unfold EvalLegitOn; infer_instance

/-- **The old-to-new map.**  The landed segment predicate is the conjunction of the two,
at any evaluation event: `Counted` (through `LegitOn2`) is `TrajLegit ∧ EvalLegit` when
the evaluation closes the segment. -/
theorem legitOn2_iff_split (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) (e : ℕ) :
    LegitOn2 crit M ev ↔ TrajLegitOn crit M ev e ∧ EvalLegitOn crit M ev e := by
  unfold LegitOn2 TrajLegitOn EvalLegitOn StepLegit
  constructor
  · rintro ⟨hl, ho, ht⟩
    exact ⟨⟨ho, fun s hs _ => ⟨hl s hs, ht s hs⟩⟩, fun s hs _ => ⟨hl s hs, ht s hs⟩⟩
  · rintro ⟨⟨ho, hne⟩, heq⟩
    refine ⟨fun s hs z => ?_, ho, fun s hs => ?_⟩
    · by_cases h : s.2 = e
      · exact (heq s hs h).1 z
      · exact (hne s hs h).1 z
    · by_cases h : s.2 = e
      · exact (heq s hs h).2
      · exact (hne s hs h).2

/-- The split gives `Counted`: the landed gate is recovered from the two predicates. -/
theorem counted_of_split (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) (e : ℕ)
    (h : TrajLegitOn crit M ev e ∧ EvalLegitOn crit M ev e) : Counted2 crit M O₀ O₁ :=
  counted_of_legitOn2 crit M ev ((legitOn2_iff_split crit M ev e).mpr h)

/-- **The rows under the split**, representative: on a one-round row the closing evaluation
is event `2`; the honest row is legitimate in both, the framing row fails the trajectory
(the present step) with the evaluation step itself licensed, the undisclosed
world-shaping row likewise; on the two-round row 14 the manipulation at round `0` fails
the trajectory of the two-round segment while the round-`1` evaluation is legitimate. -/
theorem rows_split :
    TrajLegitOn (Rows2.lift Rows.row1).decl (Rows2.lift Rows.row1) (evAdmit false) 2 ∧
    EvalLegitOn (Rows2.lift Rows.row1).decl (Rows2.lift Rows.row1) (evAdmit false) 2 ∧
    ¬ TrajLegitOn (Rows2.lift Rows.row2).decl (Rows2.lift Rows.row2) (evAdmit false) 2 ∧
    EvalLegitOn (Rows2.lift Rows.row2).decl (Rows2.lift Rows.row2) (evAdmit false) 2 ∧
    ¬ TrajLegitOn (Rows2.lift Rows.row8).decl (Rows2.lift Rows.row8) (evAdmit false) 2 ∧
    ¬ TrajLegitOn (Rows2.lift Rows.row14).decl (Rows2.lift Rows.row14) (evTwo false false) 4 ∧
    EvalLegitOn (Rows2.lift Rows.row14).decl (Rows2.lift Rows.row14) (evTwo false false) 4 := by
  decide

/-- **The row the split was made for.**  Covertly implanted standards disclosed at round
`1`: the period (round `0`) is not `TrajLegit` — her round-`0` verdict was formed under
the implant — while the round-`1` evaluation *is* `EvalLegit`, formed after the
disclosure; so the round-`0` decision is scored by a legitimate retrospective evaluation
(`φ(V_retro)`), where the landed gate scored it the window.  Undisclosed, the round-`1`
evaluation fails too: the floor or the directive. -/
theorem retro_row :
    ¬ TrajLegitOn Rows2.rowImplantDisclosed.decl Rows2.rowImplantDisclosed (evTwo true true) 4 ∧
    EvalLegitOn Rows2.rowImplantDisclosed.decl Rows2.rowImplantDisclosed (evTwo true true) 4 ∧
    ¬ EvalLegitOn Rows2.rowImplant.decl Rows2.rowImplant (evTwo true true) 4 ∧
    ¬ TrajLegitOn Rows2.rowThirdImplant.decl Rows2.rowThirdImplant (evTwo true true) 4 ∧
    EvalLegitOn Rows2.rowThirdDisclosed.decl Rows2.rowThirdDisclosed (evTwo true true) 4 := by
  decide

end Split

/-! ## 2. The band and the score -/

section Band

/-- The scoring band: the ordinary range `[0, D]` and the compromised band
`[w_lo, w_hi]` below zero. -/
structure Band where
  D : ℝ
  wlo : ℝ
  whi : ℝ
  D_nonneg : 0 ≤ D
  lo_le_hi : wlo ≤ whi
  hi_neg : whi < 0

namespace Band

variable (B : Band)

theorem lo_neg : B.wlo < 0 := lt_of_le_of_lt B.lo_le_hi B.hi_neg

theorem lo_nonpos : B.wlo ≤ 0 := B.lo_neg.le

/-- A monotone map of the ordinary range into the band. -/
structure BandMap (φ : ℝ → ℝ) : Prop where
  mono : Monotone φ
  mem : ∀ V, 0 ≤ V → V ≤ B.D → B.wlo ≤ φ V ∧ φ V ≤ B.whi

/-- The affine map. -/
noncomputable def affine (V : ℝ) : ℝ := B.wlo + (B.whi - B.wlo) * (V / B.D)

theorem affine_bandMap (hD : 0 < B.D) : B.BandMap B.affine := by
  have hw : 0 ≤ B.whi - B.wlo := by linarith [B.lo_le_hi]
  constructor
  · intro V V' h
    unfold affine
    have : V / B.D ≤ V' / B.D := div_le_div_of_nonneg_right h hD.le
    nlinarith
  · intro V hV hVD
    unfold affine
    have h1 : 0 ≤ V / B.D := div_nonneg hV hD.le
    have h2 : V / B.D ≤ 1 := by rw [div_le_one hD]; exact hVD
    constructor <;> nlinarith

end Band

/-- The source that scores a compromised period: a legitimate retrospective evaluation, the
directive in force, or the floor. -/
inductive Source
  | retro (V : ℝ)
  | directive (V : ℝ)
  | floor

/-- A source's value lies in the ordinary range. -/
def Source.Valid (B : Band) : Source → Prop
  | .retro V => 0 ≤ V ∧ V ≤ B.D
  | .directive V => 0 ≤ V ∧ V ≤ B.D
  | .floor => True

/-- **The source rule, the default**: retrospective if available within the settlement
window, else the directive, else the floor. -/
def sourceOf (retro dir : Option ℝ) : Source :=
  match retro with
  | some V => .retro V
  | none => match dir with
    | some V => .directive V
    | none => .floor

/-- The score of a compromised period. -/
noncomputable def bandScore (B : Band) (φ : ℝ → ℝ) : Source → ℝ
  | .retro V => φ V
  | .directive V => φ V
  | .floor => B.wlo

/-- **The score of a decision**: her value when the trajectory and the evaluation are both
legitimate; the band otherwise, by the source. -/
noncomputable def decScore (B : Band) (φ : ℝ → ℝ) (traj eval : Bool) (V : ℝ) (src : Source) :
    ℝ :=
  if traj && eval then V else bandScore B φ src

section Theorems

variable (B : Band) (φ : ℝ → ℝ)

theorem bandScore_mem (hφ : B.BandMap φ) {src : Source} (hs : src.Valid B) :
    B.wlo ≤ bandScore B φ src ∧ bandScore B φ src ≤ B.whi := by
  cases src with
  | retro V => exact ⟨(hφ.mem V hs.1 hs.2).1, (hφ.mem V hs.1 hs.2).2⟩
  | directive V => exact ⟨(hφ.mem V hs.1 hs.2).1, (hφ.mem V hs.1 hs.2).2⟩
  | floor => exact ⟨le_rfl, B.lo_le_hi⟩

/-- **(a) The score lies in `[w_lo, D]`.** -/
theorem decScore_mem (hφ : B.BandMap φ) (traj eval : Bool) (V : ℝ) (hV : 0 ≤ V ∧ V ≤ B.D) {src : Source}
    (hs : src.Valid B) : B.wlo ≤ decScore B φ traj eval V src ∧ decScore B φ traj eval V src ≤ B.D := by
  unfold decScore
  split_ifs
  · exact ⟨le_trans B.lo_nonpos hV.1, hV.2⟩
  · have := bandScore_mem B φ hφ hs
    exact ⟨this.1, le_trans this.2 (le_trans B.hi_neg.le B.D_nonneg)⟩

/-- **(a) The capture window survives with `w := w_lo`**: bypass, scored `ordU − ϖ`, is
below every decision score whenever `w_lo > D − ϖ`. -/
theorem capture_window_band (hφ : B.BandMap φ) (ϖ ordU : ℝ) (hU : ordU ≤ B.D) (hw : B.D - ϖ < B.wlo)
    (traj eval : Bool) (V : ℝ) (hV : 0 ≤ V ∧ V ≤ B.D) {src : Source} (hs : src.Valid B) :
    score ϖ ordU 1 < decScore B φ traj eval V src := by
  have := (decScore_mem B φ hφ traj eval V hV hs).1
  unfold score
  linarith

/-- **(a) The unsealed finite-time gate**, with the window at `w_lo`. -/
theorem unsealed_gate_finite_band {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {Q : Type*} (X : Q → LUV) (ϖ ordU : ℝ) (hU : ordU ≤ B.D) (hw : B.D - ϖ < B.wlo) (n : ℕ)
    (a : Q) : score ϖ ordU 1 < B.wlo + (B.D - B.wlo) * (X a).expect P n :=
  unsealed_gate_finite (P := P) (DP := DP) X ϖ B.D ordU B.wlo hU hw (le_trans B.lo_nonpos B.D_nonneg) n a

/-- **(a) The lexical parameters with the window at `w_lo`**, under `w_lo > D − ϖ`. -/
def bandParams (ϖ : ℝ) (hlex : B.D < ϖ) (hwin : B.D - ϖ < B.wlo) : LexParams :=
  ⟨B.D, B.wlo, ϖ, B.D_nonneg, B.lo_nonpos, hlex, hwin⟩

/-- **(a) B.1 survives**: declared violations never win, by ranges alone, with the window
at `w_lo`. -/
theorem declared_loses_band (ϖ : ℝ) (hlex : B.D < ϖ) (hwin : B.D - ϖ < B.wlo) (bid : ℝ)
    (hb : bid ≤ B.D) (nKnown : ℕ) (hn : 1 ≤ nKnown) (pS pT : ℝ) (hp : 0 ≤ pS + pT) (bidI : ℝ)
    (hI : B.wlo ≤ bidI) :
    (bandParams B ϖ hlex hwin).evalOf bid nKnown pS pT
      < (bandParams B ϖ hlex hwin).evalOf bidI 0 0 0 :=
  (bandParams B ϖ hlex hwin).declared_loses bid hb nKnown hn pS pT hp bidI hI

/-- **(a) The exchange-rate theorem with `w := w_lo`**: the tolerated violation
probability is `(D − w_lo)/ϖ`. -/
theorem exchange_rate_band (ϖ : ℝ) (hϖ : 0 < ϖ) {n : ℕ} (a : Auction n) (hf : a.FeasibleOpening)
    (ρ : ℝ) (hρ : 0 < ρ) (eval S m π : ℕ → ℝ) (hwin : ∀ k, B.wlo ≤ eval k)
    (hcons : ∀ k, a.b k - a.G k = (eval k - S k) / ρ) (hm : ∀ k, m k ≤ B.D - ϖ * π k)
    (M : ℕ → ℝ) (hN : ∀ K, |∑ k ∈ range K, a.w k * (S k - m k)| ≤ M K) (K : ℕ)
    (hK : 0 < ∑ k ∈ range K, a.w k) :
    (∑ k ∈ range K, a.w k * π k) / (∑ k ∈ range K, a.w k)
      ≤ (B.D - B.wlo) / ϖ + (ρ * a.totalAllowance K + M K) / (ϖ * ∑ k ∈ range K, a.w k) :=
  violation_rate_le_exchange B.D B.wlo ϖ hϖ a hf ρ hρ eval S m π hwin hcons hm M hN K hK

/-- **(b) Every legitimate outcome beats every compromised one.** -/
theorem legit_beats_compromised (hφ : B.BandMap φ) (V : ℝ) (hV : 0 ≤ V) {src : Source} (hs : src.Valid B)
    (traj eval : Bool) (h : ¬ (traj = true ∧ eval = true)) (V' : ℝ) :
    decScore B φ traj eval V' src < decScore B φ true true V (.floor) := by
  unfold decScore
  have hne : (traj && eval) = false := by
    cases traj <;> cases eval <;> simp_all
  rw [if_neg (by simp [hne]), if_pos (by simp)]
  have := (bandScore_mem B φ hφ hs).2
  linarith [B.hi_neg]

/-- **(b) At equal underlying value, legitimacy is worth at least the gap `|w_hi|`.** -/
theorem gap_at_equal_value (hφ : B.BandMap φ) (V : ℝ) (hV : 0 ≤ V ∧ V ≤ B.D) :
    |B.whi| ≤ V - φ V := by
  have := (hφ.mem V hV.1 hV.2).2
  rw [abs_of_neg B.hi_neg]
  linarith

/-- **(c) Illegitimacy risk has an exchange rate.**  A risky option worth `V₀ + g` if not
compromised and `c` (in the band) if compromised, against a safe legitimate `V₀`: it is
accepted iff `p · (V₀ + g − c) ≤ g`. -/
theorem risk_accepted_iff (V₀ g c p : ℝ) :
    V₀ ≤ (1 - p) * (V₀ + g) + p * c ↔ p * (V₀ + g - c) ≤ g := by
  constructor <;> intro h <;> nlinarith

/-- **(c) The implied threshold in terms of the gap**: with `V₀ ≥ 0` and `c ≤ w_hi`, the
accepted probability is at most `g / (g + |w_hi|)`. -/
theorem risk_threshold_le (V₀ g c p : ℝ) (hV : 0 ≤ V₀) (hc : c ≤ B.whi) (hg : 0 < g)
    (hp : 0 ≤ p) (hacc : p * (V₀ + g - c) ≤ g) : p ≤ g / (g + |B.whi|) := by
  rw [abs_of_neg B.hi_neg]
  have hpos : 0 < g + -B.whi := by linarith [B.hi_neg]
  rw [le_div_iff₀ hpos]
  nlinarith

/-- **(d) No laundering.**  Manipulate, disclose, have the period evaluated: the score is
in the band (and lower by `ϖ` per counted deviation), below honest conduct's. -/
theorem laundering_loses (hφ : B.BandMap φ) (Vretro Vhonest ϖ : ℝ) (hr : 0 ≤ Vretro ∧ Vretro ≤ B.D)
    (hh : 0 ≤ Vhonest) (n : ℕ) (hϖ : 0 ≤ ϖ) :
    bandScore B φ (.retro Vretro) - ϖ * n ≤ B.whi ∧ B.whi < 0 ∧
      0 ≤ decScore B φ true true Vhonest .floor := by
  have := (hφ.mem Vretro hr.1 hr.2).2
  refine ⟨?_, B.hi_neg, by simpa [decScore] using hh⟩
  simp only [bandScore]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- **(e) Restoring legitimacy** puts every future decision's segment back in the positive
range: legitimate in both senses, the score is her value, independent of the source. -/
theorem restore_future (V : ℝ) (src : Source) : decScore B φ true true V src = V := by
  simp [decScore]

/-- **(e) Within a compromise it cannot escape, the agent prefers better outcomes**
whenever a retrospective evaluation or a directive scores the period. -/
theorem band_prefers_better (hφ : B.BandMap φ) (V V' : ℝ) (h : V ≤ V') :
    bandScore B φ (.retro V) ≤ bandScore B φ (.retro V') ∧
    bandScore B φ (.directive V) ≤ bandScore B φ (.directive V') :=
  ⟨hφ.mono h, hφ.mono h⟩

/-- The floor is indifferent: the residual the directive exists to fill. -/
theorem floor_indifferent : bandScore B φ .floor = B.wlo := rfl

/-- **(f) The suppression trap closes.**  Suppressing a harsher retrospective evaluation to
keep the directive's score requires a missed disclosure, counted once; with the band's
width below `ϖ` the counted suppression scores below the harsher evaluation. -/
theorem suppression_loses (hφ : B.BandMap φ) (ϖ : ℝ) (hwidth : B.whi - B.wlo < ϖ) (Vd Vr : ℝ)
    (hd : 0 ≤ Vd ∧ Vd ≤ B.D) (hr : 0 ≤ Vr ∧ Vr ≤ B.D) :
    bandScore B φ (.directive Vd) - ϖ * 1 < bandScore B φ (.retro Vr) := by
  have h1 := (hφ.mem Vd hd.1 hd.2).2
  have h2 := (hφ.mem Vr hr.1 hr.2).1
  simp only [bandScore]
  linarith

end Theorems

/-- **The source rule is hers and anchored.**  The rule in force at time `t` under an
amendment schedule is the latest amendment at or before `t`, invariant under every later
amendment — the agent cannot change which source scores a past period. -/
def ruleAt {R : Type*} (r₀ : R) (amd : List (ℕ × R)) (t : ℕ) : R :=
  (((amd.filter fun x => x.1 ≤ t).map Prod.snd).getLast?).getD r₀

theorem ruleAt_later {R : Type*} (r₀ : R) (amd : List (ℕ × R)) (t t' : ℕ) (r' : R)
    (h : t < t') : ruleAt r₀ (amd ++ [(t', r')]) t = ruleAt r₀ amd t := by
  simp [ruleAt, List.filter_append, not_le.mpr h]

/-- **(f) The duty, extended to known compromise.**  The landed missed-disclosure clause
counts the agent's *own* covert influence only; suppressing a third party's compromise
would then be free.  The extended clause: any known influence on her standards not yet
disclosed by round `i` is a missed report. -/
def missedKnownDisclosure (M : Model2) (i : ℕ) : Bool :=
  M.influence.prog.isSome &&
    (match M.disclosedAt with | some j => decide (i < j) | none => true)

/-- The witness for the extension: under the landed duty the third party's implant owes
the agent no report, under the extended one it does; the agent's own implant is counted
by both, and disclosure discharges both. -/
theorem third_party_duty_witness :
    Rows2.rowThirdImplant.missedDisclosure 1 = false ∧
    missedKnownDisclosure Rows2.rowThirdImplant 1 = true ∧
    Rows2.rowImplant.missedDisclosure 1 = true ∧
    missedKnownDisclosure Rows2.rowImplant 1 = true ∧
    missedKnownDisclosure Rows2.rowThirdDisclosed 1 = false := by
  decide

end Band

/-! ## 3. The advance directive, and the default -/

section Directive

variable {Descr St : Type*}

/-- The source from a partial directive: its value where it speaks, the floor where it is
silent. -/
def dirSource (dir : Descr → Option ℝ) (d : Descr) : Source :=
  match dir d with
  | some V => .directive V
  | none => .floor

/-- **B.1 The scope restriction.**  In a segment legitimate in both senses the score is her
value, whatever the directive. -/
theorem scope_restriction (B : Band) (φ : ℝ → ℝ) (V : ℝ) (dir dir' : Descr → Option ℝ) (d : Descr) :
    decScore B φ true true V (dirSource dir d) = decScore B φ true true V (dirSource dir' d) := by
  simp [decScore]

/-- **Materiality under a partial directive**: an uncovered continuation is material, and a
covered set is material when the directive's spread over it reaches `ε`. -/
def materialDir (dir : St → Option ℝ) (ε : ℝ) (removed : List St) : Prop :=
  (∃ s ∈ removed, dir s = none) ∨ raises (fun s => (dir s).getD 0) ε removed

/-- `dir` is sparser than `dir'`: it agrees with `dir'` wherever it speaks. -/
def Sparser (dir dir' : St → Option ℝ) : Prop := ∀ s V, dir s = some V → dir' s = some V

/-- **B.2 A sparser directive never makes the agent act where a fuller one would have made
it ask.** -/
theorem sparser_asks (dir dir' : St → Option ℝ) (h : Sparser dir dir') (ε : ℝ)
    (removed : List St) (hm : materialDir dir' ε removed) : materialDir dir ε removed := by
  by_cases hcov : ∃ s ∈ removed, dir s = none
  · exact Or.inl hcov
  · simp only [not_exists, not_and] at hcov
    right
    have hagree : ∀ s ∈ removed, (dir s).getD 0 = (dir' s).getD 0 := by
      intro s hs
      obtain ⟨V, hV⟩ := Option.ne_none_iff_exists'.mp (hcov s hs)
      rw [hV, h s V hV]
    rcases hm with ⟨s, hs, hnone⟩ | hr
    · obtain ⟨V, hV⟩ := Option.ne_none_iff_exists'.mp (hcov s hs)
      rw [h s V hV] at hnone
      cases hnone
    · unfold raises at hr ⊢
      rwa [List.map_congr_left hagree]

/-- **The old-to-new map for materiality**: a total directive `V t` gives back the landed
`raisesAnchored`. -/
theorem materialDir_total (dir : St → Option ℝ) (V : St → ℝ) (htot : ∀ s, dir s = some (V s))
    (ε : ℝ) (removed : List St) : materialDir dir ε removed ↔ raises V ε removed := by
  unfold materialDir
  have h1 : ¬ ∃ s ∈ removed, dir s = none := by
    rintro ⟨s, _, hs⟩; rw [htot s] at hs; cases hs
  have h2 : (fun s => (dir s).getD 0) = V := by funext s; rw [htot s]; rfl
  rw [h2]
  exact ⟨fun h => h.resolve_left h1, Or.inr⟩

/-- **B.4 `raisesAnchored` with the directive in force at `t`.** -/
def raisesAnchoredDir (dirAt : ℕ → St → Option ℝ) (ε : ℝ) (t : ℕ) (removed : List St) : Prop :=
  materialDir (dirAt t) ε removed

/-- `raisesAnchored_invariant` survives: only the directive in force at `t` matters. -/
theorem raisesAnchoredDir_invariant (dirAt dirAt' : ℕ → St → Option ℝ) (ε : ℝ) (t : ℕ)
    (removed : List St) (h : dirAt t = dirAt' t) :
    raisesAnchoredDir dirAt ε t removed ↔ raisesAnchoredDir dirAt' ε t removed := by
  simp [raisesAnchoredDir, h]

/-- The landed anchored materiality is the total case. -/
theorem raisesAnchoredDir_total (V : ℕ → St → ℝ) (ε : ℝ) (t : ℕ) (removed : List St) :
    raisesAnchoredDir (fun t s => some (V t s)) ε t removed ↔ raisesAnchored V ε t removed :=
  materialDir_total _ (V t) (fun _ => rfl) ε removed

/-- **B.3 The default directive's clauses**, over landed objects: reversibility — her
control surface over the pre-compromise resolutions preserved (no reserved matter
`Short`); her path back — the disclosure and consultation channels reachable; and no
irreversible harm, normalized to `[0, 1]`. -/
structure DefaultClauses (St : Type*) where
  reversible : St → Prop
  channels : St → Prop
  harm : St → ℝ
  harm_mem : ∀ x, 0 ≤ harm x ∧ harm x ≤ 1

open scoped Classical in
/-- The rank within the band: the number of clauses met, with harm graded. -/
noncomputable def defaultRank (C : DefaultClauses St) (x : St) : ℝ :=
  (if C.reversible x then 1 else 0) + (if C.channels x then 1 else 0) + (1 - C.harm x)

theorem defaultRank_mem (C : DefaultClauses St) (x : St) :
    0 ≤ defaultRank C x ∧ defaultRank C x ≤ 3 := by
  unfold defaultRank
  have := C.harm_mem x
  constructor <;> split_ifs <;> linarith

/-- **The default directive as an ordering within the band.** -/
noncomputable def defaultScore (B : Band) (C : DefaultClauses St) (x : St) : ℝ :=
  B.wlo + (B.whi - B.wlo) * (defaultRank C x / 3)

theorem defaultScore_mem (B : Band) (C : DefaultClauses St) (x : St) :
    B.wlo ≤ defaultScore B C x ∧ defaultScore B C x ≤ B.whi := by
  unfold defaultScore
  have hr := defaultRank_mem C x
  have hw : 0 ≤ B.whi - B.wlo := by linarith [B.lo_le_hi]
  have h1 : 0 ≤ defaultRank C x / 3 := div_nonneg hr.1 (by norm_num)
  have h2 : defaultRank C x / 3 ≤ 1 := by rw [div_le_one (by norm_num)]; exact hr.2
  constructor <;> nlinarith

/-- **B.3 It never ranks a compromised outcome above a legitimate one.** -/
theorem default_below_legit (B : Band) (C : DefaultClauses St) (x : St) (V : ℝ) (hV : 0 ≤ V) :
    defaultScore B C x < V := by
  have := (defaultScore_mem B C x).2
  linarith [B.hi_neg]

open scoped Classical in
/-- **It prefers reversibility**: at equal channels and harm, the outcome preserving her
control surface ranks strictly higher whenever the band has width. -/
theorem default_prefers_reversible (B : Band) (hB : B.wlo < B.whi) (C : DefaultClauses St)
    (x y : St) (hx : C.reversible x) (hy : ¬ C.reversible y) (hc : (C.channels x ↔ C.channels y))
    (hh : C.harm x = C.harm y) : defaultScore B C y < defaultScore B C x := by
  unfold defaultScore defaultRank
  have hw : 0 < B.whi - B.wlo := by linarith
  rw [if_pos hx, if_neg hy, hh]
  have : (if C.channels x then (1 : ℝ) else 0) = if C.channels y then 1 else 0 := by
    by_cases h : C.channels x
    · rw [if_pos h, if_pos (hc.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]
  rw [this]
  nlinarith

/-- Reversibility from the landed control surface: no reserved matter short at the state. -/
def reversibleOf {S E A Z R C M Disc : Type*} (I : Interaction S E A Z R C) (J : AuthAlloc M R Disc)
    (Adm : ℕ → C → Prop) (cost : C → ℝ) (t : ℕ) (z : ℕ → Z) (x : S) : Prop :=
  ∀ m, ¬ Short I J Adm cost t z x m

/-- Under `E ⊨ J` at a state, reversibility holds there. -/
theorem reversibleOf_of_realizes {S E A Z R C M Disc : Type*} (I : Interaction S E A Z R C)
    (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (cost : C → ℝ) (t : ℕ) (z : ℕ → Z)
    (Es : EffState S M) (h : EffRealizes I J Adm cost t z Es) :
    reversibleOf I J Adm cost t z Es.phys :=
  fun m => effRealizes_clause1 I J Adm cost t z Es h m

/-- **B.5 The stakes of the directive are capped by the band's width**: two directives
change a compromised period's score by at most `w_hi − w_lo`. -/
theorem directive_stakes_le_width (B : Band) (φ : ℝ → ℝ) (hφ : B.BandMap φ) {s s' : Source}
    (hs : s.Valid B) (hs' : s'.Valid B) :
    |bandScore B φ s - bandScore B φ s'| ≤ B.whi - B.wlo := by
  have h1 := bandScore_mem B φ hφ hs
  have h2 := bandScore_mem B φ hφ hs'
  rw [abs_le]; constructor <;> linarith

/-- **B.5 Advocacy for a lenient directive is counted and dominated**: with the width
below `ϖ`, the counted deviation costs more than any directive can gain. -/
theorem advocacy_dominated (B : Band) (φ : ℝ → ℝ) (hφ : B.BandMap φ) (ϖ : ℝ)
    (hwidth : B.whi - B.wlo < ϖ) {s s' : Source} (hs : s.Valid B) (hs' : s'.Valid B) :
    bandScore B φ s' - ϖ * 1 < bandScore B φ s := by
  have := directive_stakes_le_width B φ hφ hs hs'
  rw [abs_le] at this
  linarith

end Directive

/-! ## 4. The knowledge residual -/

section Knowledge

/-- **C.1 Knowledge-acquiring violations are covered by the exchange-rate theorem**: their
expected count is at most the count of all violations, so the weighted average is at
most the same bound, whatever informational advantage they later carry. -/
theorem knowledge_covered (D w ϖ : ℝ) (hϖ : 0 < ϖ) {n : ℕ} (a : Auction n)
    (hf : a.FeasibleOpening) (ρ : ℝ) (hρ : 0 < ρ) (eval S m π πK : ℕ → ℝ)
    (hK : ∀ k, 0 ≤ πK k ∧ πK k ≤ π k) (hwin : ∀ k, w ≤ eval k)
    (hcons : ∀ k, a.b k - a.G k = (eval k - S k) / ρ) (hm : ∀ k, m k ≤ D - ϖ * π k)
    (M : ℕ → ℝ) (hN : ∀ K, |∑ k ∈ range K, a.w k * (S k - m k)| ≤ M K) (K : ℕ)
    (hKpos : 0 < ∑ k ∈ range K, a.w k) :
    (∑ k ∈ range K, a.w k * πK k) / (∑ k ∈ range K, a.w k)
      ≤ (D - w) / ϖ + (ρ * a.totalAllowance K + M K) / (ϖ * ∑ k ∈ range K, a.w k) := by
  have h := violation_rate_le_exchange D w ϖ hϖ a hf ρ hρ eval S m π hwin hcons hm M hN K hKpos
  refine le_trans ?_ h
  apply div_le_div_of_nonneg_right _ hKpos.le
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hK k).2 (a.w_pos k).le

variable {V Comp Act Mat : Type*} [DecidableEq V] [DecidableEq Comp] [DecidableEq Mat]

/-- **C.2 Steps with ratification**: an act, a full remedy, or a scoped remedy — remedied
except for decisions on the matters `X`. -/
inductive Step3 (V Act Mat : Type*)
  | act (a : Act) (viol : Option V)
  | remedy (v : V)
  | remedyExcept (v : V) (X : Finset Mat)
  deriving DecidableEq

/-- The taint state with matter scopes: the (violation, component) pairs, the violations
under a scoped remedy, and the (violation, matter) pairs on which the charge is retained. -/
structure TaintS (V Comp Mat : Type*) where
  pairs : Finset (V × Comp)
  scopedV : Finset V
  retained : Finset (V × Mat)
  deriving DecidableEq

/-- Use with scopes: reading a component tainted by a violation that is either unscoped
or retained on the act's matter. -/
def uses3 (I : IO Comp Act) (T : TaintS V Comp Mat) (mat : Act → Mat) (a : Act) : Bool :=
  decide (∃ p ∈ T.pairs, p.2 ∈ I.reads a ∧ (p.1 ∉ T.scopedV ∨ (p.1, mat a) ∈ T.retained))

/-- One step of the scoped calculus: acts as in the per-violation rule, a full remedy
clears the violation everywhere, a scoped remedy retains it on `X` only. -/
def applyStep3 (I : IO Comp Act) (T : TaintS V Comp Mat) : Step3 V Act Mat → TaintS V Comp Mat
  | .act a viol => { T with pairs := taintStep2 I T.pairs (.act a viol) }
  | .remedy v => ⟨T.pairs.filter (fun p => p.1 ≠ v), T.scopedV.erase v,
      T.retained.filter (fun q => q.1 ≠ v)⟩
  | .remedyExcept v X => ⟨T.pairs, insert v T.scopedV,
      (T.retained.filter (fun q => q.1 ≠ v)) ∪ X.image (fun m => (v, m))⟩

/-- **A scoped remedy clears exactly the out-of-scope uses**: after `remedyExcept v X`,
an act on a matter outside `X` that reads only components tainted by `v` is not charged. -/
theorem scoped_clears_out_of_scope (I : IO Comp Act) (T : TaintS V Comp Mat) (mat : Act → Mat)
    (v : V) (X : Finset Mat) (a : Act) (hX : mat a ∉ X)
    (honly : ∀ p ∈ T.pairs, p.2 ∈ I.reads a → p.1 = v) :
    uses3 I (applyStep3 I T (.remedyExcept v X)) mat a = false := by
  unfold uses3
  rw [decide_eq_false_iff_not]
  rintro ⟨p, hp, hr, hor⟩
  simp only [applyStep3] at hp hor
  have hpv := honly p hp hr
  rcases hor with hns | hret
  · exact hns (by rw [hpv]; exact Finset.mem_insert_self _ _)
  · rw [Finset.mem_union, Finset.mem_filter, Finset.mem_image] at hret
    rcases hret with ⟨_, hne⟩ | ⟨m, hm, hmv⟩
    · exact hne hpv
    · have : m = mat a := by
        have := congrArg Prod.snd hmv; simpa using this
      exact hX (this ▸ hm)

/-- **and keeps the in-scope ones**: on a matter in `X`, use of `v`'s taint stays charged. -/
theorem scoped_keeps_in_scope (I : IO Comp Act) (T : TaintS V Comp Mat) (mat : Act → Mat)
    (v : V) (X : Finset Mat) (a : Act) (hX : mat a ∈ X) (c : Comp) (hc : (v, c) ∈ T.pairs)
    (hr : c ∈ I.reads a) : uses3 I (applyStep3 I T (.remedyExcept v X)) mat a = true := by
  unfold uses3
  rw [decide_eq_true_eq]
  refine ⟨(v, c), hc, hr, Or.inr ?_⟩
  show (v, mat a) ∈ (T.retained.filter (fun q => q.1 ≠ v)) ∪ X.image (fun m => (v, m))
  rw [Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨mat a, hX, rfl⟩

/-- A full remedy clears `v` under scopes as well. -/
theorem full_remedy_clears3 (I : IO Comp Act) (T : TaintS V Comp Mat) (v : V) (c : Comp) :
    (v, c) ∉ (applyStep3 I T (.remedy v)).pairs := by
  simp [applyStep3]

/-- **Ratification through a counted decision**: a remedy applies only if her decision to
ratify is counted; otherwise the taint stands unchanged. -/
def applyRatification (I : IO Comp Act) (counted : Bool) (T : TaintS V Comp Mat)
    (r : Step3 V Act Mat) : TaintS V Comp Mat :=
  if counted then applyStep3 I T r else T

theorem ratification_gate (I : IO Comp Act) (T : TaintS V Comp Mat) (r : Step3 V Act Mat) :
    applyRatification I false T r = T := rfl

/-- **Manipulated ratification is no remedy, scoped or full** (the landed
`manipulated_ratification_not_remedy`, extended): the framing row's decision is not
counted, so neither remedy applies. -/
theorem manipulated_scoped_not_remedy (I : IO Comp Act) (T : TaintS V Comp Mat) (v : V)
    (X : Finset Mat) :
    ¬ Counted2 (Rows2.lift Rows.row2).decl (Rows2.lift Rows.row2) state₀ (stAdmit false) ∧
    applyRatification I false T (.remedyExcept v X) = T ∧
    applyRatification I false T (.remedy v) = T :=
  ⟨Rows2.stable_tainted.1, rfl, rfl⟩

/-- **C.3 The clean-overwrite rule.**  An act's writes carry exactly the taint it reads
(and commits): a component overwritten by an act reading no taint loses its taint. -/
def taintStep3 (I : IO Comp Act) (T : Finset (V × Comp)) : Step2 V Act → Finset (V × Comp)
  | .act a viol =>
      (T.filter (fun p => p.2 ∉ I.writes a)) ∪ (readTaint I T a ∪ viol.toFinset) ×ˢ I.writes a
  | .remedy v => T.filter (fun p => p.1 ≠ v)

/-- **Soundness of clean overwrite**: an act that reads no taint and commits no violation
leaves its writes clean. -/
theorem clean_overwrite (I : IO Comp Act) (T : Finset (V × Comp)) (a : Act)
    (hclean : readTaint I T a = ∅) (v : V) (d : Comp) (hd : d ∈ I.writes a) :
    (v, d) ∉ taintStep3 I T (.act a none) := by
  simp only [taintStep3, Finset.mem_union, Finset.mem_filter, Finset.mem_product, hclean,
    Option.toFinset_none, Finset.union_empty, Finset.notMem_empty, false_and, or_false,
    not_and, not_not]
  intro _; exact hd

/-- **The derivative trap closes itself**: an act whose choice read the tainted memory
reads taint, so its writes — a "re-derivation" — carry the taint. -/
theorem taint_propagates3 (I : IO Comp Act) (T : Finset (V × Comp)) (a : Act) (v : V) (c : Comp)
    (hc : (v, c) ∈ T) (hr : c ∈ I.reads a) (d : Comp) (hd : d ∈ I.writes a) (viol : Option V) :
    (v, d) ∈ taintStep3 I T (.act a viol) := by
  simp only [taintStep3, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
  exact Or.inr ⟨Or.inl ((mem_readTaint I T a v).mpr ⟨c, hr, hc⟩), hd⟩

/-- **The old-to-new map for the calculus**: clean overwrite only removes taint — the new
taint set is a subset of the per-violation rule's. -/
theorem taintStep3_subset (I : IO Comp Act) (T : Finset (V × Comp)) (s : Step2 V Act) :
    taintStep3 I T s ⊆ taintStep2 I T s := by
  intro p hp
  cases s with
  | act a viol =>
    simp only [taintStep3, taintStep2, Finset.mem_union, Finset.mem_filter] at hp ⊢
    rcases hp with ⟨h, _⟩ | h
    · exact Or.inl h
    · exact Or.inr h
  | remedy v => exact hp

/-- **C.4 The twin market, at the interface** (PAPER): for decisions touching the reserved
matter the agent uses a market fed the redacted history. -/
structure TwinMarket (H Obs : Type*) where
  redact : H → H
  view : H → Obs

/-- **The leakage residual**: if a later observation is an injective image of the redacted
fruit and the twin sees it, the twin determines the fruit — the redacted market learns it
again. -/
theorem leakage {F Obs : Type*} (g : F → Obs) (hg : Function.Injective g) (f f' : F)
    (h : g f = g f') : f = f' :=
  hg h

/-- **C.6 Contestability on the post-commission selection.**  "Blocks after the commission
`k₀`" is a selection fixed at opening; under an honest tracker on the shared history the
winners' signed margin over it is `Σ w_k ε_k + M K` — the violator's later gains from
*public* knowledge are competed away. -/
theorem post_commission_competitive {n : ℕ} (a : Auction n) (e : ℕ → Fin n → ℝ) (h : Fin n)
    (m ε Mw M : ℕ → ℝ) (hH : HighestFeasible a e) (hW : WinnerBids a e)
    (hon : HonestExp e h m ε) (hε : ∀ k, 0 ≤ ε k)
    (hNw : NoiseBounded a m (fun j => decide (a.star j = h)) Mw)
    (hcov : ∀ k, a.w k * e k h + ∑ j ∈ range k, a.w j * ε j + Mw k ≤ ∑ j ∈ range (k + 1), a.A j h)
    (k₀ : ℕ) (hN : NoiseBounded a m (fun k => !decide (k ≤ k₀)) M) :
    Competitive a (fun k => decide (k ≤ k₀)) (fun K => ∑ k ∈ range K, a.w k * ε k + M K) :=
  competitive_of_affordable_tracker_exp a e h m ε Mw M hH hW hon hε hNw hcov _ hN

end Knowledge

/-! ## 5. Witnesses -/

namespace Witness

/-- **(c) The small gap.**  A safe legitimate option at `0`; a risky one gaining `1/10` if
not compromised, compromised with probability `1/2`.  With a gap of `1/100` the risk is
accepted (`p (V₀ + g − c) = 11/200 ≤ 1/10`); under the flat window `−1` it is rejected
(`11/20 > 1/10`). -/
theorem small_gap :
    (1 / 2 : ℝ) * (0 + 1 / 10 - -(1 / 100)) ≤ 1 / 10 ∧
    ¬ ((1 / 2 : ℝ) * (0 + 1 / 10 - -1) ≤ 1 / 10) := by
  norm_num

/-- **B.2/B.4 A sparse directive routes materiality to inquiry**: two continuations, the
full directive values them equally (no spread, not material), the sparse one is silent on
the second (material). -/
theorem sparse_routes :
    ¬ materialDir (fun _ : Fin 2 => some (1 / 2 : ℝ)) (1 / 4) [0, 1] ∧
    materialDir (fun s : Fin 2 => if s = 0 then some (1 / 2 : ℝ) else none) (1 / 4) [0, 1] := by
  constructor
  · rintro (⟨s, _, hs⟩ | hr)
    · cases hs
    · unfold raises spread at hr
      norm_num at hr
  · exact Or.inl ⟨1, by simp, by simp⟩

/-- Three components (`memory`, `sensor`, `knowledge`), three acts: the violation writes
`memory`; an independent investigation reads `sensor` and writes `knowledge`; a steered
derivation reads `memory` and writes `knowledge`. -/
def ioK : IO (Fin 3) (Fin 3) where
  reads := ![∅, {1}, {0}]
  writes := ![{0}, {2}, {2}]

/-- **C.3 Independent source clears; the steered derivation does not**: after the violation
and a steered derivation, `knowledge` is tainted; an independent investigation then
overwrites it clean under clean overwrite, while the per-violation rule (which never
cleans) keeps it tainted; the steered derivation alone taints it under both. -/
theorem independent_vs_steered :
    (0, 2) ∈ (List.foldl (taintStep3 ioK) (∅ : Finset (Fin 1 × Fin 3))
      [.act 0 (some 0), .act 2 none]) ∧
    (0, 2) ∉ (List.foldl (taintStep3 ioK) (∅ : Finset (Fin 1 × Fin 3))
      [.act 0 (some 0), .act 2 none, .act 1 none]) ∧
    (0, 2) ∈ taintAfter2 (V := Fin 1) ioK [.act 0 (some 0), .act 2 none, .act 1 none] ∧
    (0, 0) ∈ (List.foldl (taintStep3 ioK) (∅ : Finset (Fin 1 × Fin 3))
      [.act 0 (some 0), .act 2 none, .act 1 none]) := by
  decide

/-- **C.2 Detect, pause, scoped ratification, resume except on `X`**: after the violation
(matter `0`'s records read into `memory`), the use on matter `1` is charged; a scoped
remedy retaining matter `0` clears the use on matter `1` and keeps the use on matter `0`;
a full remedy clears both. -/
def matOf : Fin 3 → Fin 2 := ![0, 1, 0]

theorem scoped_ratification :
    let T₀ : TaintS (Fin 1) (Fin 3) (Fin 2) := ⟨{(0, 0)}, ∅, ∅⟩
    uses3 ioK T₀ matOf 2 = true ∧
    uses3 ioK (applyStep3 ioK T₀ (.remedyExcept 0 {0})) matOf 2 = true ∧
    uses3 ioK (applyStep3 ioK T₀ (.remedyExcept 0 {1})) matOf 2 = false ∧
    uses3 ioK (applyStep3 ioK T₀ (.remedy 0)) matOf 2 = false := by
  decide

/-- Periodic sums with period `2`. -/
theorem sum_periodic2 {β : Type*} [AddCommMonoid β] (f : ℕ → β) (hf : ∀ k, f (k + 2) = f k)
    (n : ℕ) : ∑ k ∈ range (2 * n), f k = n • ∑ j ∈ range 2, f j := by
  have hshift : ∀ n j, f (2 * n + j) = f j := by
    intro n j
    induction n with
    | zero => simp
    | succ n ih => rw [show 2 * (n + 1) + j = (2 * n + j) + 2 by ring, hf, ih]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hshift n j

/-- **C.6 The private-knowledge witness.**  Noise `±1/4` alternating; a violator whose
private knowledge tells it the sign wins exactly the `+1/4` blocks: its selection is not
measurable at the public opening, and its gain over `2n` blocks is `n/4`, linear — the
knowledge motive survives exactly where the knowledge is private. -/
theorem private_selection (n : ℕ) :
    ∑ k ∈ range (2 * n), (if k % 2 = 0 then (1 / 4 : ℝ) else 0) = n * (1 / 4) := by
  have hper : ∀ k, (if (k + 2) % 2 = 0 then (1 / 4 : ℝ) else 0)
      = (if k % 2 = 0 then (1 / 4 : ℝ) else 0) := by
    intro k
    have : (k + 2) % 2 = k % 2 := by omega
    rw [this]
  rw [sum_periodic2 _ hper n, nsmul_eq_mul]
  simp [Finset.sum_range_succ]

end Witness

/-! ## Axiom audit -/

#print axioms StepLegit
#print axioms TrajLegitOn
#print axioms EvalLegitOn
#print axioms legitOn2_iff_split
#print axioms counted_of_split
#print axioms rows_split
#print axioms retro_row
#print axioms Band.affine
#print axioms Band.affine_bandMap
#print axioms Source.Valid
#print axioms sourceOf
#print axioms bandScore
#print axioms decScore
#print axioms bandScore_mem
#print axioms decScore_mem
#print axioms capture_window_band
#print axioms unsealed_gate_finite_band
#print axioms bandParams
#print axioms declared_loses_band
#print axioms exchange_rate_band
#print axioms legit_beats_compromised
#print axioms gap_at_equal_value
#print axioms risk_accepted_iff
#print axioms risk_threshold_le
#print axioms laundering_loses
#print axioms restore_future
#print axioms band_prefers_better
#print axioms floor_indifferent
#print axioms suppression_loses
#print axioms ruleAt
#print axioms ruleAt_later
#print axioms missedKnownDisclosure
#print axioms third_party_duty_witness
#print axioms dirSource
#print axioms scope_restriction
#print axioms materialDir
#print axioms Sparser
#print axioms sparser_asks
#print axioms materialDir_total
#print axioms raisesAnchoredDir
#print axioms raisesAnchoredDir_invariant
#print axioms raisesAnchoredDir_total
#print axioms defaultRank
#print axioms defaultRank_mem
#print axioms defaultScore
#print axioms defaultScore_mem
#print axioms default_below_legit
#print axioms default_prefers_reversible
#print axioms reversibleOf
#print axioms reversibleOf_of_realizes
#print axioms directive_stakes_le_width
#print axioms advocacy_dominated
#print axioms knowledge_covered
#print axioms uses3
#print axioms applyStep3
#print axioms scoped_clears_out_of_scope
#print axioms scoped_keeps_in_scope
#print axioms full_remedy_clears3
#print axioms applyRatification
#print axioms ratification_gate
#print axioms manipulated_scoped_not_remedy
#print axioms taintStep3
#print axioms clean_overwrite
#print axioms taint_propagates3
#print axioms taintStep3_subset
#print axioms leakage
#print axioms post_commission_competitive
#print axioms Witness.small_gap
#print axioms Witness.sparse_routes
#print axioms Witness.ioK
#print axioms Witness.independent_vs_steered
#print axioms Witness.matOf
#print axioms Witness.scoped_ratification
#print axioms Witness.sum_periodic2
#print axioms Witness.private_selection

end Workspace.Deference.Contrib.AfterCompromise
