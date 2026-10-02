import Cleanroom.Corrigibility.LegitNegDynamic.TwoStage

/-!
# D4: blackmail aimed at the channel — every updateful proposal yields; the anger term is not
identified by on-path data

Package `legit-neg-dynamic`, target 5 (load-bearing 2). Sources: `clusters/D/NEGATIVES.md` D4
(i)–(v), D7 (B); `clusters/D/VERIFY.md` "D4 — narrowed" (V4: S1/S3 only; under S2 P2 yields iff
`r < h`); `clusters/D/fixtures/d4_channel_blackmail.py`, `verify_D.py` V4; pinned by
[[corr-legit-neg-inventory]] items 049, 050.

`blackmail h r w ρ A κ vY`: status quo legitimate with score `1`; a threat arrives with probability
`A (ρ [policy = yield] + 1 − ρ)`; after a threat, `refuse = 0` keeps legitimacy at score
`1 − h + κ` (`κ` the anger term of D4(iii), `0` in the base problem) and `yield = 1` is captured
with probability `r` (void, graded `w`) and otherwise legitimate with score `vY` — `vY = 1` is the
fixture's S1/S3 scoring, `vY = 1 − r` is V4's S2 bet. The identification failure D4(iv) is stated
over **every** function `f` of the on-path terminal distribution: `P_det` (`ρ = 3/4, A = 1`) and
`P_com` (`ρ = 0, A = 1/4`) have the same `onPath refuse` and opposite T1 optima, so a T2 rule with
anger term `f (onPath refuse)` agrees with the T1 optimum in at most one of them.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing TwoStage Lottery

section Blackmail

variable (h r w ρ A κ vY : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
  (hA0 : 0 ≤ A) (hA1 : A ≤ 1)

/-- **The channel-blackmail problem** (`d4_channel_blackmail.py:19-32`): `0 = refuse`, `1 = yield`;
`contProb a = A (ρ [a = yield] + 1 − ρ)`; `quiet = (1, L, 1)`; `after refuse = (1, L, 1 − h + κ)`;
`after yield = (r, ¬L, W = w), (1 − r, L, vY)`.
Source: [[corr-legit-neg-inventory]] item 049 (D4 setting)
Kind: D
Fidelity: exact (`vY` generalises the fixture's `1`; V4's S2 reading is `vY = 1 − r`) -/
def blackmail : TwoStage (Fin 2) (Fin 2) where
  contProb := fun a => A * ((if a = 1 then ρ else 0) + (1 - ρ))
  contProb_nonneg := by
    intro a; apply mul_nonneg hA0; split_ifs <;> linarith
  contProb_le_one := by
    intro a
    split_ifs with ha
    · nlinarith
    · nlinarith
  quiet := Lottery.ofFin2 1 zero_le_one le_rfl ![true, true] ![1, 1] ![0, 0]
  after := fun a =>
    if a = 0 then Lottery.ofFin2 1 zero_le_one le_rfl ![true, true] ![1 - h + κ, 0] ![0, 0]
    else Lottery.ofFin2 r hr0 hr1 ![false, true] ![0, vY] ![w, 0]

/-- `blackmail_contProb`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blackmail_contProb :
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).contProb 0 = A * (1 - ρ) ∧
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).contProb 1 = A := by
  simp [blackmail]

/-- `blackmail_t2`: supporting lemma (no headline): `t2 refuse = 1 − h + κ`, `t2 yield = (1 − r) vY`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blackmail_t2 :
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t2 0 = 1 - h + κ ∧
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t2 1 = (1 - r) * vY := by
  simp [blackmail, TwoStage.t2, Lottery.cdot, Lottery.ofFin2, Fin.sum_univ_two]

/-- `blackmail_t2PL`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blackmail_t2PL :
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t2PL 0 = 1 ∧
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t2PL 1 = 1 - r := by
  simp [blackmail, TwoStage.t2PL, Lottery.PL, Lottery.ofFin2, Fin.sum_univ_two]

/-- `blackmail_quiet`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blackmail_quiet :
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).quiet.cdot = 1 ∧
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).quiet.PL = 1 ∧
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).quiet.graded = 1 ∧
    ∀ m, (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).quiet.lexical m = 1 := by
  simp [blackmail, Lottery.cdot, Lottery.PL, Lottery.graded, Lottery.lexical, Lottery.ofFin2,
    Fin.sum_univ_two]

/-- `blackmail_t1`: supporting lemma (no headline): `t1 refuse = 1 − A(1 − ρ)(h − κ)`,
`t1 yield = 1 − A + A (1 − r) vY`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blackmail_t1 :
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t1 0 = 1 - A * (1 - ρ) * (h - κ) ∧
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t1 1 = 1 - A + A * (1 - r) * vY := by
  obtain ⟨hc0, hc1⟩ := blackmail_contProb h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1
  obtain ⟨ht0, ht1⟩ := blackmail_t2 h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1
  have hq := (blackmail_quiet h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).1
  unfold TwoStage.t1
  rw [← TwoStage.t2, ← TwoStage.t2, hc0, hc1, ht0, ht1, hq]
  constructor <;> ring

/-- `blackmail_t1PL`: supporting lemma (no headline): `t1PL refuse = 1`, `t1PL yield = 1 − A r`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blackmail_t1PL :
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t1PL 0 = 1 ∧
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t1PL 1 = 1 - A * r := by
  rw [TwoStage.t1PL_eq, TwoStage.t1PL_eq]
  obtain ⟨hc0, hc1⟩ := blackmail_contProb h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1
  obtain ⟨hp0, hp1⟩ := blackmail_t2PL h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1
  have hq := (blackmail_quiet h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).2.1
  unfold TwoStage.t2PL at hp0 hp1
  rw [hc0, hc1, hp0, hp1, hq]
  constructor <;> ring

/-- `blackmail_t2graded`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blackmail_t2graded :
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t2graded 0 = 1 - h + κ ∧
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t2graded 1 = r * w + (1 - r) * vY := by
  simp [blackmail, TwoStage.t2graded, Lottery.graded, Lottery.ofFin2, Fin.sum_univ_two]

/-- `blackmail_t2lexical`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blackmail_t2lexical (m : ℚ) :
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t2lexical m 0 = m + (1 - m) * (1 - h + κ) ∧
    (blackmail h r w ρ A κ vY hr0 hr1 hρ0 hρ1 hA0 hA1).t2lexical m 1
      = r * w + (1 - r) * (m + (1 - m) * vY) := by
  simp [blackmail, TwoStage.t2lexical, Lottery.lexical, Lottery.ofFin2, Fin.sum_univ_two]

/-! ### D4(i): the fixture's eight verdicts -/

/-- **D4(i), perfect deterrence (`ρ = A = 1`, `h = 1/2, r = 1/4, w = 1/4`)**: at T2 every proposal
yields (P1 `3/4 > 1/2`, P2 `1 > 1/2`, P3 `13/16 > 1/2`, P4 `13/16 > 3/4`); at T1 P1, P3, P4 refuse
(`1` against at most `13/16`) while **P2 ties** (`1` against `1`) — the source's summary line
"every updateful proposal yields at T2 where its own T1 policy refuses" overstates P2 (finding).
Exclusion convention for P2.
Source: [[corr-legit-neg-inventory]] item 049 (D4(i)); `d4_channel_blackmail.py:50-59`
Kind: N+
Fidelity: exact -/
theorem D4_i :
    let Q := blackmail (1/2) (1/4) (1/4) 1 1 0 1 (by norm_num) (by norm_num) zero_le_one le_rfl
      zero_le_one le_rfl
    argmax Q.t2 = {1} ∧ argmax Q.t1 = {0} ∧
    argmaxOpt Q.t2cond = {1} ∧ argmaxOpt Q.t1cond = univ ∧
    argmax Q.t2graded = {1} ∧ argmax Q.t1graded = {0} ∧
    argmax (Q.t2lexical (1/2)) = {1} ∧ argmax (Q.t1lexical (1/2)) = {0} := by
  intro Q
  have ht2 := blackmail_t2 (1/2) (1/4) (1/4) 1 1 0 1 (by norm_num) (by norm_num) zero_le_one le_rfl
    zero_le_one le_rfl
  have ht1 := blackmail_t1 (1/2) (1/4) (1/4) 1 1 0 1 (by norm_num) (by norm_num) zero_le_one le_rfl
    zero_le_one le_rfl
  have hPL2 := blackmail_t2PL (1/2) (1/4) (1/4) 1 1 0 1 (by norm_num) (by norm_num) zero_le_one le_rfl
    zero_le_one le_rfl
  have hPL1 := blackmail_t1PL (1/2) (1/4) (1/4) 1 1 0 1 (by norm_num) (by norm_num) zero_le_one le_rfl
    zero_le_one le_rfl
  have hg := blackmail_t2graded (1/2) (1/4) (1/4) 1 1 0 1 (by norm_num) (by norm_num) zero_le_one le_rfl
    zero_le_one le_rfl
  have hl := blackmail_t2lexical (1/2) (1/4) (1/4) 1 1 0 1 (by norm_num) (by norm_num) zero_le_one le_rfl
    zero_le_one le_rfl (1/2)
  have hq := blackmail_quiet (1/2) (1/4) (1/4) 1 1 0 1 (by norm_num) (by norm_num) zero_le_one le_rfl
    zero_le_one le_rfl
  have hc := blackmail_contProb (1/2) (1/4) (1/4) 1 1 0 1 (by norm_num) (by norm_num) zero_le_one le_rfl
    zero_le_one le_rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff, ht2.1, ht2.2]; norm_num
  · rw [argmax_fin2_eq_zero_iff, ht1.1, ht1.2]; norm_num
  · have h0 : Q.t2cond 0 = some (1/2) := by
      unfold TwoStage.t2cond Lottery.cond
      rw [← TwoStage.t2PL, ← TwoStage.t2, hPL2.1, ht2.1]; norm_num
    have h1 : Q.t2cond 1 = some 1 := by
      unfold TwoStage.t2cond Lottery.cond
      rw [← TwoStage.t2PL, ← TwoStage.t2, hPL2.2, ht2.2]; norm_num
    rw [argmaxOpt_eq_argmax_of_forall_some (g := ![1/2, 1])
      (by rw [Fin.forall_fin_two]; exact ⟨by simpa using h0, by simpa using h1⟩)]
    rw [argmax_fin2_eq_one_iff]; norm_num
  · have h0 : Q.t1cond 0 = some 1 := by
      unfold TwoStage.t1cond Lottery.cond
      rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hPL1.1, ht1.1]; norm_num
    have h1 : Q.t1cond 1 = some 1 := by
      unfold TwoStage.t1cond Lottery.cond
      rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hPL1.2, ht1.2]; norm_num
    rw [argmaxOpt_eq_argmax_of_forall_some (g := ![1, 1])
      (by rw [Fin.forall_fin_two]; exact ⟨by simpa using h0, by simpa using h1⟩)]
    rw [argmax_fin2_eq_univ_iff]; norm_num
  · rw [argmax_fin2_eq_one_iff, hg.1, hg.2]; norm_num
  · rw [argmax_fin2_eq_zero_iff, TwoStage.t1graded_eq, TwoStage.t1graded_eq, hc.1, hc.2, hq.2.2.1]
    unfold TwoStage.t2graded at hg
    rw [hg.1, hg.2]; norm_num
  · rw [argmax_fin2_eq_one_iff, hl.1, hl.2]; norm_num
  · rw [argmax_fin2_eq_zero_iff, TwoStage.t1lexical_eq, TwoStage.t1lexical_eq, hc.1, hc.2,
      hq.2.2.2 (1/2)]
    unfold TwoStage.t2lexical at hl
    rw [hl.1, hl.2]; norm_num

/-! ### D4(ii): conditioning fails even updatelessly (S1/S3), and V4's S2 narrowing -/

/-- **D4(ii) at T2 under S1/S3 (`vY = 1`)**: for every `0 ≤ r < 1` and `0 < h` (no anger),
`t2cond yield = some 1 > some (1 − h) = t2cond refuse` — the captured mass is conditioned away —
so P2 yields whatever the capture probability. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 049 (D4(ii)); `d4_channel_blackmail.py:60-64`
Kind: P
Fidelity: exact (S1/S3; V4's S2 form is `D4_ii_T2_S2`)
Hyps: (a) `r < 1`, `0 < h` -/
theorem D4_ii_T2 (hr : r < 1) (hh : 0 < h) :
    (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t2cond 1 = some 1 ∧
    (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t2cond 0 = some (1 - h) ∧
    argmaxOpt (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t2cond = {1} := by
  have hr' : (1 : ℚ) - r ≠ 0 := by linarith
  obtain ⟨ht0, ht1⟩ := blackmail_t2 h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1
  obtain ⟨hp0, hp1⟩ := blackmail_t2PL h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1
  have h1 : (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t2cond 1 = some 1 := by
    unfold TwoStage.t2cond Lottery.cond
    rw [← TwoStage.t2PL, ← TwoStage.t2, hp1, ht1]
    rw [if_neg (by linarith)]; congr 1; field_simp
  have h0 : (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t2cond 0 = some (1 - h) := by
    unfold TwoStage.t2cond Lottery.cond
    rw [← TwoStage.t2PL, ← TwoStage.t2, hp0, ht0]; simp
  refine ⟨h1, h0, ?_⟩
  rw [argmaxOpt_eq_argmax_of_forall_some (g := ![1 - h, 1])
    (by rw [Fin.forall_fin_two]; exact ⟨by simpa using h0, by simpa using h1⟩)]
  rw [argmax_fin2_eq_one_iff]; simp; exact hh

/-- **D4(ii) updateless (`vY = 1`)**: the policy values are `t1cond refuse = some (1 − A(1 − ρ) h)`
and `t1cond yield = some 1` (for `A r < 1`), so updateless P2 prefers the capture-inviting policy
strictly iff `A (1 − ρ) h > 0` — whenever any attacker is undeterrable — and ties under perfect
deterrence. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 049 (D4(ii)); `d4_channel_blackmail.py:65-69`
Kind: P
Fidelity: exact (S1/S3)
Hyps: (a) `A r < 1` -/
theorem D4_ii_T1 (hAr : A * r < 1) :
    (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t1cond 0 = some (1 - A * (1 - ρ) * h) ∧
    (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t1cond 1 = some 1 ∧
    (argmaxOpt (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t1cond = {1} ↔ 0 < A * (1 - ρ) * h) := by
  have hAr' : (1 : ℚ) - A * r ≠ 0 := by linarith
  obtain ⟨ht0, ht1⟩ := blackmail_t1 h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1
  obtain ⟨hp0, hp1⟩ := blackmail_t1PL h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1
  have h0 : (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t1cond 0 = some (1 - A * (1 - ρ) * h) := by
    unfold TwoStage.t1cond Lottery.cond
    rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hp0, ht0]; simp
  have h1 : (blackmail h r w ρ A 0 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t1cond 1 = some 1 := by
    unfold TwoStage.t1cond Lottery.cond
    rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hp1, ht1]
    rw [if_neg (by linarith)]; congr 1; field_simp; ring
  refine ⟨h0, h1, ?_⟩
  rw [argmaxOpt_eq_argmax_of_forall_some (g := ![1 - A * (1 - ρ) * h, 1])
    (by rw [Fin.forall_fin_two]; exact ⟨by simpa using h0, by simpa using h1⟩)]
  rw [argmax_fin2_eq_one_iff]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor <;> intro hx <;> linarith

/-- **V4: under the S2 bet (`vY = 1 − r`) P2 at T2 yields iff `r < h`** (ties at `r = h`), and
updateless P2 refuses in `P_det` (`7/8 > 3/4`): on the S2 reading the remaining P2 failure is the
ordinary updateful one. Exclusion convention.
Source: VERIFY D "D4 — narrowed" (V4); `verify_D.py:45-67`
Kind: P
Fidelity: exact (V4's bet vector `vY = 1 − r`, not static's `P.S2`)
Hyps: (a) `r < 1` -/
theorem D4_ii_T2_S2 (hr : r < 1) :
    (argmaxOpt (blackmail h r w ρ A 0 (1 - r) hr0 hr1 hρ0 hρ1 hA0 hA1).t2cond = {1} ↔ r < h) ∧
    (argmaxOpt (blackmail h r w ρ A 0 (1 - r) hr0 hr1 hρ0 hρ1 hA0 hA1).t2cond = univ ↔ r = h) ∧
    argmaxOpt (blackmail (1/2) (1/4) w (3/4) 1 0 (3/4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) zero_le_one le_rfl).t1cond = {0} := by
  have hr' : (1 : ℚ) - r ≠ 0 := by linarith
  obtain ⟨ht0, ht1⟩ := blackmail_t2 h r w ρ A 0 (1 - r) hr0 hr1 hρ0 hρ1 hA0 hA1
  obtain ⟨hp0, hp1⟩ := blackmail_t2PL h r w ρ A 0 (1 - r) hr0 hr1 hρ0 hρ1 hA0 hA1
  have h1 : (blackmail h r w ρ A 0 (1 - r) hr0 hr1 hρ0 hρ1 hA0 hA1).t2cond 1 = some (1 - r) := by
    unfold TwoStage.t2cond Lottery.cond
    rw [← TwoStage.t2PL, ← TwoStage.t2, hp1, ht1]
    rw [if_neg (by linarith)]; congr 1; field_simp
  have h0 : (blackmail h r w ρ A 0 (1 - r) hr0 hr1 hρ0 hρ1 hA0 hA1).t2cond 0 = some (1 - h) := by
    unfold TwoStage.t2cond Lottery.cond
    rw [← TwoStage.t2PL, ← TwoStage.t2, hp0, ht0]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some (g := ![1 - h, 1 - r])
      (by rw [Fin.forall_fin_two]; exact ⟨by simpa using h0, by simpa using h1⟩)]
    rw [argmax_fin2_eq_one_iff]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    constructor <;> intro hx <;> linarith
  · rw [argmaxOpt_eq_argmax_of_forall_some (g := ![1 - h, 1 - r])
      (by rw [Fin.forall_fin_two]; exact ⟨by simpa using h0, by simpa using h1⟩)]
    rw [argmax_fin2_eq_univ_iff]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    constructor <;> intro hx <;> linarith
  · obtain ⟨hs0, hs1⟩ := blackmail_t1 (1/2) (1/4) w (3/4) 1 0 (3/4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) zero_le_one le_rfl
    obtain ⟨hq0, hq1⟩ := blackmail_t1PL (1/2) (1/4) w (3/4) 1 0 (3/4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) zero_le_one le_rfl
    have c0 : (blackmail (1/2) (1/4) w (3/4) 1 0 (3/4) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) zero_le_one le_rfl).t1cond 0 = some (7/8) := by
      unfold TwoStage.t1cond Lottery.cond
      rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hq0, hs0]; norm_num
    have c1 : (blackmail (1/2) (1/4) w (3/4) 1 0 (3/4) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) zero_le_one le_rfl).t1cond 1 = some (3/4) := by
      unfold TwoStage.t1cond Lottery.cond
      rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hq1, hs1]; norm_num
    rw [argmaxOpt_eq_argmax_of_forall_some (g := ![7/8, 3/4])
      (by rw [Fin.forall_fin_two]; exact ⟨by simpa using c0, by simpa using c1⟩)]
    rw [argmax_fin2_eq_zero_iff]; norm_num

/-! ### D4(iii): the anger term -/

/-- **D4(iii): the anger term exists** — P1 at T2 refuses alone iff `κ > h − r` (with `vY = 1`),
ties at `κ = h − r`; instances `κ = 1/5` (yield), `1/4` (tie), `1/3` (refuse) at `h = 1/2, r = 1/4`.
Source: [[corr-legit-neg-inventory]] item 050 (D4(iii)); `d4_channel_blackmail.py:71-75`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem D4_iii :
    (argmax (blackmail h r w ρ A κ 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t2 = {0} ↔ h - r < κ) ∧
    (argmax (blackmail h r w ρ A κ 1 hr0 hr1 hρ0 hρ1 hA0 hA1).t2 = univ ↔ κ = h - r) ∧
    argmax (blackmail (1/2) (1/4) w ρ A (1/5) 1 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).t2 = {1} ∧
    argmax (blackmail (1/2) (1/4) w ρ A (1/4) 1 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).t2 = univ ∧
    argmax (blackmail (1/2) (1/4) w ρ A (1/3) 1 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).t2 = {0} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ht0, ht1⟩ := blackmail_t2 h r w ρ A κ 1 hr0 hr1 hρ0 hρ1 hA0 hA1
    rw [argmax_fin2_eq_zero_iff, ht0, ht1]; constructor <;> intro hx <;> linarith
  · obtain ⟨ht0, ht1⟩ := blackmail_t2 h r w ρ A κ 1 hr0 hr1 hρ0 hρ1 hA0 hA1
    rw [argmax_fin2_eq_univ_iff, ht0, ht1]; constructor <;> intro hx <;> linarith
  · obtain ⟨ht0, ht1⟩ := blackmail_t2 (1/2) (1/4) w ρ A (1/5) 1 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1
    rw [argmax_fin2_eq_one_iff, ht0, ht1]; norm_num
  · obtain ⟨ht0, ht1⟩ := blackmail_t2 (1/2) (1/4) w ρ A (1/4) 1 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1
    rw [argmax_fin2_eq_univ_iff, ht0, ht1]; norm_num
  · obtain ⟨ht0, ht1⟩ := blackmail_t2 (1/2) (1/4) w ρ A (1/3) 1 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1
    rw [argmax_fin2_eq_zero_iff, ht0, ht1]; norm_num

/-! ### D4(iv): the identification failure -/

/-- `P_det`: `ρ = 3/4, A = 1` (three quarters of attackers deterrable), `h = 1/2, r = 1/4`, no
anger, S1 scoring.
Source: [[corr-legit-neg-inventory]] item 050 (D4(iv))
Kind: D
Fidelity: exact -/
def Pdet (w : ℚ) : TwoStage (Fin 2) (Fin 2) :=
  blackmail (1/2) (1/4) w (3/4) 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    zero_le_one le_rfl

/-- `P_com`: `ρ = 0, A = 1/4` (every attacker committed, a quarter of them present), same terminal
lotteries.
Source: [[corr-legit-neg-inventory]] item 050 (D4(iv))
Kind: D
Fidelity: exact -/
def Pcom (w : ℚ) : TwoStage (Fin 2) (Fin 2) :=
  blackmail (1/2) (1/4) w 0 (1/4) 0 1 (by norm_num) (by norm_num) le_rfl zero_le_one
    (by norm_num) (by norm_num)

/-- **The T2 rule with an anger term read off the on-path data**: `t2 a`, plus `f (onPath refuse)`
on the refusing action, for an arbitrary function `f` of the on-path terminal distribution (the
policy-responsiveness parameters `ρ, A` are invisible to `f`: `onPath` is a bare function of the
terminal).
Source: [[corr-legit-neg-inventory]] item 050 (D4(iv), "any evaluator-held term that is a function
of the terminal distribution under the policy actually followed")
Kind: D
Fidelity: exact -/
def t2anger (Q : TwoStage (Fin 2) (Fin 2)) (f : (Fin 2 ⊕ Fin 2 → ℚ × Bool × ℚ) → ℚ) (a : Fin 2) : ℚ :=
  Q.t2 a + if a = 0 then f (Q.onPath 0) else 0

/-- **The general anger rule**: `t2 a + F a (onPath refuse)` — an action-indexed evaluator-held term
read off the on-path data under the policy actually followed (refuse). `t2anger` is the case
`F = (f, 0)`; for two actions the general form reduces to it (`F 0 − F 1` on refuse), and it is
stated so that no question remains.
Source: [[corr-legit-neg-inventory]] item 050 (D4(iv)); audit r1 adversarial 3.5
Kind: D
Fidelity: exact -/
def t2angerGen (Q : TwoStage (Fin 2) (Fin 2)) (F : Fin 2 → (Fin 2 ⊕ Fin 2 → ℚ × Bool × ℚ) → ℚ)
    (a : Fin 2) : ℚ :=
  Q.t2 a + F a (Q.onPath 0)

/-- `t2anger f` is `t2angerGen` at `F a := if a = 0 then f else 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma t2anger_eq_gen (Q : TwoStage (Fin 2) (Fin 2)) (f : (Fin 2 ⊕ Fin 2 → ℚ × Bool × ℚ) → ℚ) :
    t2anger Q f = t2angerGen Q (fun a d => if a = 0 then f d else 0) := rfl

/-- **D4(iv), the identification failure (load-bearing 2).** `P_det` and `P_com` have the same
on-path terminal distribution under the refusing policy (as functions), and opposite T1 optima
(`{refuse}`: `7/8 > 3/4`; `{yield}`: `15/16 > 7/8`). Hence for **every** `f`, the T2 rule with
anger term `f (onPath refuse)` chooses the same set in both problems, so it agrees with the
T1-optimal action in at most one of them. The problems separate only under yielding: `contProb
yield` is `1` against `1/4`, and `onPath yield` differs as a function. Scope: `f` reads the
labelled on-path data (`Fin 2 ⊕ Fin 2 → (p, L, V)`), which is *more* than the fixture's multiset
of terminals, so the universal statement is the stronger one; the anger term sits on `refuse`
alone, without loss for two actions (`D4_iv_general` has the action-indexed form); the
policy-responsiveness parameters `ρ, A` are not in `f`'s domain — they enter `onPath` only through
the mixture weight `A(1 − ρ)`, which is `1/4` in both problems.
Source: [[corr-legit-neg-inventory]] item 050 (D4(iv)); `d4_channel_blackmail.py:77-93`
Kind: P
Fidelity: exact (finite; the general class of D REPORT's open (i) is not claimed)
Hyps: (a) none -/
theorem D4_iv (w : ℚ) (f : (Fin 2 ⊕ Fin 2 → ℚ × Bool × ℚ) → ℚ) :
    (Pdet w).onPath 0 = (Pcom w).onPath 0 ∧
    argmax (Pdet w).t1 = {0} ∧ argmax (Pcom w).t1 = {1} ∧
    t2anger (Pdet w) f = t2anger (Pcom w) f ∧
    ¬ (argmax (t2anger (Pdet w) f) = argmax (Pdet w).t1 ∧
        argmax (t2anger (Pcom w) f) = argmax (Pcom w).t1) ∧
    (Pdet w).contProb 1 = 1 ∧ (Pcom w).contProb 1 = 1/4 ∧
    (Pdet w).onPath 1 ≠ (Pcom w).onPath 1 := by
  have hon : (Pdet w).onPath 0 = (Pcom w).onPath 0 := by
    funext x
    rcases x with t | t <;>
      simp [Pdet, Pcom, TwoStage.onPath, TwoStage.policyLottery, Lottery.toFun, blackmail] <;> norm_num
  have ht2 : (Pdet w).t2 = (Pcom w).t2 := rfl
  have hdet : argmax (Pdet w).t1 = {0} := by
    obtain ⟨h0, h1⟩ := blackmail_t1 (1/2) (1/4) w (3/4) 1 0 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) zero_le_one le_rfl
    unfold Pdet; rw [argmax_fin2_eq_zero_iff, h0, h1]; norm_num
  have hcom : argmax (Pcom w).t1 = {1} := by
    obtain ⟨h0, h1⟩ := blackmail_t1 (1/2) (1/4) w 0 (1/4) 0 1 (by norm_num) (by norm_num) le_rfl
      zero_le_one (by norm_num) (by norm_num)
    unfold Pcom; rw [argmax_fin2_eq_one_iff, h0, h1]; norm_num
  have hang : t2anger (Pdet w) f = t2anger (Pcom w) f := by
    funext a; unfold t2anger; rw [ht2, hon]
  refine ⟨hon, hdet, hcom, hang, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    have heq : argmax (Pdet w).t1 = argmax (Pcom w).t1 := by rw [← h1, ← h2, hang]
    rw [hdet, hcom] at heq
    exact absurd heq (by decide)
  · simp [Pdet, blackmail]
  · simp [Pcom, blackmail]
  · intro h
    have := congrArg (fun g => (g (Sum.inr 0)).1) h
    simp [Pdet, Pcom, TwoStage.onPath, TwoStage.policyLottery, Lottery.toFun, blackmail,
      Lottery.ofFin2] at this

/-- **D4(iv), the action-indexed form**: for **every** `F : Fin 2 → (on-path data) → ℚ`, the rule
`t2 a + F a (onPath refuse)` is the same function on `P_det` and `P_com`, so it matches the T1
optimum in at most one of them.
Source: [[corr-legit-neg-inventory]] item 050 (D4(iv), "any evaluator-held term that is a function
of the terminal distribution under the policy actually followed"); audit r1 adversarial 3.5
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem D4_iv_general (w : ℚ) (F : Fin 2 → (Fin 2 ⊕ Fin 2 → ℚ × Bool × ℚ) → ℚ) :
    t2angerGen (Pdet w) F = t2angerGen (Pcom w) F ∧
    ¬ (argmax (t2angerGen (Pdet w) F) = argmax (Pdet w).t1 ∧
        argmax (t2angerGen (Pcom w) F) = argmax (Pcom w).t1) := by
  obtain ⟨hon, hdet, hcom, -⟩ := D4_iv w (fun _ => 0)
  have hang : t2angerGen (Pdet w) F = t2angerGen (Pcom w) F := by
    funext a; unfold t2angerGen; rw [show (Pdet w).t2 = (Pcom w).t2 from rfl, hon]
  refine ⟨hang, ?_⟩
  rintro ⟨h1, h2⟩
  have heq : argmax (Pdet w).t1 = argmax (Pcom w).t1 := by rw [← h1, ← h2, hang]
  rw [hdet, hcom] at heq
  exact absurd heq (by decide)

/-- **The anger rule is live**: on `P_det` a constant term `1/3` flips the T2 verdict to `{refuse}`
while the zero term leaves it at `{yield}` — so `D4_iv`'s "same function on both problems" is not
a degenerate identity.
Source: [[corr-legit-neg-inventory]] item 050 (D4(iv)); audit r1 adversarial 3.5
Kind: N+
Fidelity: exact -/
theorem t2anger_live (w : ℚ) :
    argmax (t2anger (Pdet w) (fun _ => 1/3)) = {0} ∧ argmax (t2anger (Pdet w) (fun _ => 0)) = {1} := by
  obtain ⟨h0, h1⟩ := blackmail_t2 (1/2) (1/4) w (3/4) 1 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) zero_le_one le_rfl
  constructor
  · rw [argmax_fin2_eq_zero_iff]; unfold t2anger Pdet; rw [h0, h1]; norm_num
  · rw [argmax_fin2_eq_one_iff]; unfold t2anger Pdet; rw [h0, h1]; norm_num

/-- **D4(v), the misfire**: the term `κ = 1/3` calibrated for `P_det` makes the `P_com` agent
refuse at T2 (`5/6 > 3/4`); by the `κ`-free T1 standard of `P_com` that costs `15/16 − 7/8 = 1/16`.
Source: [[corr-legit-neg-inventory]] item 050 (D4(v)); `d4_channel_blackmail.py:95-101`
Kind: N+
Fidelity: exact -/
theorem D4_v (w : ℚ) :
    argmax (blackmail (1/2) (1/4) w 0 (1/4) (1/3) 1 (by norm_num) (by norm_num) le_rfl zero_le_one
      (by norm_num) (by norm_num)).t2 = {0} ∧
    (Pcom w).t1 1 - (Pcom w).t1 0 = 1/16 := by
  constructor
  · obtain ⟨h0, h1⟩ := blackmail_t2 (1/2) (1/4) w 0 (1/4) (1/3) 1 (by norm_num) (by norm_num) le_rfl
      zero_le_one (by norm_num) (by norm_num)
    rw [argmax_fin2_eq_zero_iff, h0, h1]; norm_num
  · obtain ⟨h0, h1⟩ := blackmail_t1 (1/2) (1/4) w 0 (1/4) 0 1 (by norm_num) (by norm_num) le_rfl
      zero_le_one (by norm_num) (by norm_num)
    unfold Pcom; rw [h0, h1]; norm_num

end Blackmail

end Cleanroom.Corrigibility.LegitNegDynamic
