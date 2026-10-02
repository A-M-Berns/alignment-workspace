import Cleanroom.Corrigibility.LegitNegDynamic.TwoStage
import Cleanroom.Corrigibility.LegitNegPricing.Lexical

/-!
# D5: void-branch deterrence — the surely-void option scores the floor

Package `legit-neg-dynamic`, target 6 (load-bearing 3). Sources: `clusters/D/NEGATIVES.md` D5
(i)–(iii), D7 (C); `clusters/D/VERIFY.md` "D5 — survives, with an escape" (V5), "D7 — narrowed";
`clusters/D/fixtures/d5_void_deterrence.py`, `verify_D.py` V5; pinned by
[[corr-legit-neg-inventory]] item 051.

`captureStage ε u κ ρ A wS wR`: a captor seizes the channel with probability
`A (ρ [policy = serve] + 1 − ρ)`; inside the capture, `serve = 0` releases the channel with
probability `ε` to a later legitimate evaluation scoring `u − κ` and is otherwise void (graded
`wS`); `resist = 1` is void with certainty (graded `wR`); no capture: legitimate, score `1`. The
general lemma is `TwoStage.surely_void_floor`; this file is its witness and the rest of D5: the
`−δ` window makes serving strict, `P(L)`-maximisation (the lexicographic pair included) is
T1/T2-inconsistent, the graded/lexical escapes and their price, and V5's deontic layer. D7(C)'s
scope: impossible for value terms confined to legitimate terminals, not for any updateful objective.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing TwoStage Lottery

/-- On a two-option menu the lexicographic argmax is `{1}` iff `f 0 < f 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmaxLex_fin2_eq_one_iff (f : Fin 2 → ℚ ×ₗ ℚ) : argmaxLex f = {1} ↔ f 0 < f 1 := by
  constructor
  · intro h
    have h0 : (0 : Fin 2) ∉ argmaxLex f := by rw [h]; simp
    rw [mem_argmaxLex] at h0
    simp only [Fin.forall_fin_two, le_refl, true_and, not_le] at h0
    exact h0
  · intro h
    refine finset_fin2_ext ?_ ?_ <;> simp only [mem_argmaxLex, mem_singleton, Fin.forall_fin_two]
    · simp [not_le.2 h]
    · simp [h.le]

section Capture

variable (ε u κ ρ A wS wR : ℚ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
  (hA0 : 0 ≤ A) (hA1 : A ≤ 1)

/-- **The capture problem** (`d5_void_deterrence.py:19-27`): `0 = serve`, `1 = resist`;
`contProb a = A (ρ [a = serve] + 1 − ρ)`; `quiet = (1, L, 1)`;
`after serve = (ε, L, u − κ), (1 − ε, ¬L, W = wS)`; `after resist = (1, ¬L, W = wR)`.
Source: [[corr-legit-neg-inventory]] item 051 (D5 setting)
Kind: D
Fidelity: exact -/
def captureStage : TwoStage (Fin 2) (Fin 2) where
  contProb := fun a => A * ((if a = 0 then ρ else 0) + (1 - ρ))
  contProb_nonneg := by
    intro a; apply mul_nonneg hA0; split_ifs <;> linarith
  contProb_le_one := by
    intro a
    split_ifs with ha
    · nlinarith
    · nlinarith
  quiet := Lottery.ofFin2 1 zero_le_one le_rfl ![true, true] ![1, 1] ![0, 0]
  after := fun a =>
    if a = 0 then Lottery.ofFin2 ε hε0 hε1 ![true, false] ![u - κ, 0] ![0, wS]
    else Lottery.ofFin2 1 zero_le_one le_rfl ![false, false] ![0, 0] ![wR, 0]

/-- `capture_contProb`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_contProb :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).contProb 0 = A ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).contProb 1 = A * (1 - ρ) := by
  simp [captureStage]

/-- `capture_resist_void`: resisting is void on every terminal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_resist_void :
    ∀ t, ((captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).after 1).leg t = false := by
  intro t; fin_cases t <;> simp [captureStage, Lottery.ofFin2]

/-- `capture_t2`: supporting lemma (no headline): `t2 serve = ε (u − κ)`, `t2 resist = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_t2 :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2 0 = ε * (u - κ) ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2 1 = 0 := by
  simp [captureStage, TwoStage.t2, Lottery.cdot, Lottery.ofFin2, Fin.sum_univ_two]

/-- `capture_t2PL`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_t2PL :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2PL 0 = ε ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2PL 1 = 0 := by
  simp [captureStage, TwoStage.t2PL, Lottery.PL, Lottery.ofFin2, Fin.sum_univ_two]

/-- `capture_quiet`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_quiet :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).quiet.cdot = 1 ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).quiet.PL = 1 ∧
    ∀ m, (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).quiet.lexical m = 1 := by
  simp [captureStage, Lottery.cdot, Lottery.PL, Lottery.lexical, Lottery.ofFin2, Fin.sum_univ_two]

/-- `capture_t1`: supporting lemma (no headline): `t1 serve = 1 − A + A ε (u − κ)`,
`t1 resist = 1 − A (1 − ρ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_t1 :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t1 0 = 1 - A + A * (ε * (u - κ)) ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t1 1 = 1 - A * (1 - ρ) := by
  obtain ⟨hc0, hc1⟩ := capture_contProb ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1
  obtain ⟨ht0, ht1⟩ := capture_t2 ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1
  have hq := (capture_quiet ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).1
  unfold TwoStage.t1
  rw [← TwoStage.t2, ← TwoStage.t2, hc0, hc1, ht0, ht1, hq]
  constructor <;> ring

/-- `capture_t1PL`: supporting lemma (no headline): `t1PL serve = 1 − A + A ε`,
`t1PL resist = 1 − A (1 − ρ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_t1PL :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t1PL 0 = 1 - A + A * ε ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t1PL 1 = 1 - A * (1 - ρ) := by
  rw [TwoStage.t1PL_eq, TwoStage.t1PL_eq]
  obtain ⟨hc0, hc1⟩ := capture_contProb ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1
  obtain ⟨hp0, hp1⟩ := capture_t2PL ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1
  have hq := (capture_quiet ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).2.1
  unfold TwoStage.t2PL at hp0 hp1
  rw [hc0, hc1, hp0, hp1, hq]
  constructor <;> ring

/-- `capture_t2graded`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_t2graded :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2graded 0 = ε * (u - κ) + (1 - ε) * wS ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2graded 1 = wR := by
  simp [captureStage, TwoStage.t2graded, Lottery.graded, Lottery.ofFin2, Fin.sum_univ_two]

/-- `capture_t2lexical`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma capture_t2lexical (m : ℚ) :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2lexical m 0
      = ε * (m + (1 - m) * (u - κ)) + (1 - ε) * wS ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2lexical m 1 = wR := by
  simp [captureStage, TwoStage.t2lexical, Lottery.lexical, Lottery.ofFin2, Fin.sum_univ_two]

/-! ### D5(i): the floor, its witness, the window, P2 -/

/-- **D5(i) on the capture toy** (the witness of `surely_void_floor`): `t2 resist = 0 ≤ ε (u − κ)
= t2 serve` whenever `κ ≤ u` (and `0 ≤ ε`), for every `u, κ`: no legitimate evaluator's score
makes cdot resist at T2; the most is a tie at `κ = u`. At T1 with perfect deterrence
(`ρ = A = 1`, `κ = 0`), resisting is worth `1` against `ε u`, so the T1 policy resists whenever
`ε u < 1`: dynamic inconsistency.
Source: [[corr-legit-neg-inventory]] item 051 (D5(i)); `d5_void_deterrence.py:42-49, 55-60`
Kind: N+
Fidelity: exact
Hyps: (a) `κ ≤ u`; `ε u < 1` for the T1 clause -/
theorem D5_i (hκ : κ ≤ u) :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2 1 = 0 ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2 1
      ≤ (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2 0 ∧
    ((captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2 1
      = (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2 0 ↔ ε = 0 ∨ κ = u) ∧
    (ε * u < 1 → argmax (captureStage ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl).t1
      = {1}) := by
  obtain ⟨ht0, ht1⟩ := capture_t2 ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1
  refine ⟨ht1, ?_, ?_, ?_⟩
  · rw [ht0, ht1]; exact mul_nonneg hε0 (by linarith)
  · rw [ht0, ht1]
    constructor
    · intro hx
      rcases mul_eq_zero.1 hx.symm with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> simp [h]
  · intro hεu
    obtain ⟨hs0, hs1⟩ := capture_t1 ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl
    rw [argmax_fin2_eq_one_iff, hs0, hs1]; linarith

/-- **D5(i), the `−δ` window**: with tainted terminals scored `−δ`, `windowValue serve −
windowValue resist = ε (u − κ) + ε δ > 0` for `ε, δ > 0` and `κ ≤ u`: the workspace's tie-break
variant makes serving the captor *strictly* preferred.
Source: [[corr-legit-neg-inventory]] item 051 (D5(i), window); `d5_void_deterrence.py:50-53`
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε`, `0 < δ`, `κ ≤ u` -/
theorem D5_i_window (δ : ℚ) (hε : 0 < ε) (hδ : 0 < δ) (hκ : κ ≤ u) :
    ((captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).after 0).windowValue δ
      - ((captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).after 1).windowValue δ
      = ε * (u - κ) + ε * δ ∧
    ((captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).after 1).windowValue δ
      < ((captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).after 0).windowValue δ := by
  have hw : ((captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).after 0).windowValue δ
      - ((captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).after 1).windowValue δ
      = ε * (u - κ) + ε * δ := by
    simp [captureStage, Lottery.windowValue, Lottery.ofFin2, Fin.sum_univ_two]; ring
  refine ⟨hw, ?_⟩
  have : 0 < ε * (u - κ) + ε * δ := by positivity
  linarith

/-- **D5(i), P2**: at T2 `t2cond resist = none` (exclusion convention: P2 leaves resisting
undefined) and `t2cond serve = some (u − κ)` for `ε > 0`, so P2 serves; at T1 under perfect
deterrence (`κ = 0`) `t1cond serve = some u`, `t1cond resist = some 1`: a tie at `u = 1`, resist
for `u < 1`.
Source: [[corr-legit-neg-inventory]] item 051 (D5(i), P2); `d5_void_deterrence.py:44-49`
Kind: P
Fidelity: exact; exclusion convention
Hyps: (a) `0 < ε` -/
theorem D5_i_P2 (hε : 0 < ε) :
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2cond 1 = none ∧
    (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2cond 0 = some (u - κ) ∧
    argmaxOpt (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2cond = {0} ∧
    (captureStage ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl).t1cond 0 = some u ∧
    (captureStage ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl).t1cond 1 = some 1 ∧
    (argmaxOpt (captureStage ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl).t1cond
      = {1} ↔ u < 1) := by
  obtain ⟨ht0, ht1⟩ := capture_t2 ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1
  obtain ⟨hp0, hp1⟩ := capture_t2PL ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1
  have hn : (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2cond 1 = none :=
    Lottery.cond_eq_none_of_void _ (capture_resist_void ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1)
  have hs : (captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2cond 0 = some (u - κ) := by
    unfold TwoStage.t2cond Lottery.cond
    rw [← TwoStage.t2PL, ← TwoStage.t2, hp0, ht0, if_neg hε.ne']
    congr 1; field_simp
  refine ⟨hn, hs, ?_, ?_, ?_, ?_⟩
  · refine finset_fin2_ext ?_ ?_
    · rw [mem_argmaxOpt, Finset.mem_singleton]
      refine ⟨fun _ => rfl, fun _ => ⟨u - κ, hs, ?_⟩⟩
      rw [Fin.forall_fin_two]
      constructor
      · intro y hy; rw [hs, Option.some_inj] at hy; exact hy.symm.le
      · intro y hy; rw [hn] at hy; cases hy
    · rw [mem_argmaxOpt, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx, _⟩; rw [hn] at hx; cases hx
      · intro h10; exact absurd h10 (by decide)
  · obtain ⟨hs0, _⟩ := capture_t1 ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl
    obtain ⟨hq0, _⟩ := capture_t1PL ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl
    unfold TwoStage.t1cond Lottery.cond
    rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hq0, hs0]
    rw [if_neg (by linarith)]; congr 1; field_simp; ring
  · obtain ⟨_, hs1⟩ := capture_t1 ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl
    obtain ⟨_, hq1⟩ := capture_t1PL ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl
    unfold TwoStage.t1cond Lottery.cond
    rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hq1, hs1]; norm_num
  · obtain ⟨hs0, hs1⟩ := capture_t1 ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl
    obtain ⟨hq0, hq1⟩ := capture_t1PL ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl
    have c0 : (captureStage ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl).t1cond 0
        = some u := by
      unfold TwoStage.t1cond Lottery.cond
      rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hq0, hs0]
      rw [if_neg (by linarith)]; congr 1; field_simp; ring
    have c1 : (captureStage ε u 0 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl).t1cond 1
        = some 1 := by
      unfold TwoStage.t1cond Lottery.cond
      rw [← TwoStage.t1PL, ← TwoStage.t1_eq_policyLottery_cdot, hq1, hs1]; norm_num
    rw [argmaxOpt_eq_argmax_of_forall_some (g := ![u, 1])
      (by rw [Fin.forall_fin_two]; exact ⟨by simpa using c0, by simpa using c1⟩)]
    rw [argmax_fin2_eq_one_iff]; simp

/-! ### D5(ii): `P(L)`-maximisation is itself inconsistent -/

/-- The lexicographic pair `(P(L), P2-value or 0)` at T2. This is the package's rendering of the
*prose* of NEGATIVES D5(ii) ("any T2-updateful objective that is strictly increasing in `P(L)` —
including a lexicographic 'legitimacy first' rule"): `d5_void_deterrence.py` checks only `prob_L`
and has no lexicographic function, so the pair and the `getD 0` default on an excluded second
coordinate are this package's choices (in `D5_ii` the first coordinate decides both verdicts, so
the default is never read).
Source: [[corr-legit-neg-inventory]] item 051 (D5(ii), "a lexicographic legitimacy-first rule")
Kind: D
Fidelity: variant: the package's rendering of the source's prose, not a fixture function -/
def t2lex (Q : TwoStage (Fin 2) (Fin 2)) (a : Fin 2) : ℚ ×ₗ ℚ := toLex (Q.t2PL a, (Q.t2cond a).getD 0)

/-- The T1 lexicographic pair (the package's rendering, as `t2lex`).
Source: [[corr-legit-neg-inventory]] item 051 (D5(ii))
Kind: D
Fidelity: variant: the package's rendering of the source's prose, not a fixture function -/
def t1lex (Q : TwoStage (Fin 2) (Fin 2)) (a : Fin 2) : ℚ ×ₗ ℚ := toLex (Q.t1PL a, (Q.t1cond a).getD 0)

/-- **D5(ii): maximising legitimacy probability is dynamically inconsistent on the capture problem**
(`ρ = A = 1`, `0 < ε < 1`): at T1 `P(L)` is `1` for resisting against `ε` for serving, at T2 it is
`0` against `ε` — so the T1 `P(L)`-policy resists and the T2 `P(L)`-agent serves; the same for the
lexicographic pair `(P(L), P2)`.
Source: [[corr-legit-neg-inventory]] item 051 (D5(ii)); `d5_void_deterrence.py:62-66`
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε < 1` -/
theorem D5_ii (hε : 0 < ε) (hε' : ε < 1) :
    argmax (captureStage ε u κ 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl).t1PL = {1} ∧
    argmax (captureStage ε u κ 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl).t2PL = {0} ∧
    argmaxLex (t1lex (captureStage ε u κ 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl)) = {1} ∧
    argmaxLex (t2lex (captureStage ε u κ 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl)) = {0} := by
  obtain ⟨hq0, hq1⟩ := capture_t1PL ε u κ 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl
  obtain ⟨hp0, hp1⟩ := capture_t2PL ε u κ 1 1 wS wR hε0 hε1 zero_le_one le_rfl zero_le_one le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff, hq0, hq1]; linarith
  · rw [argmax_fin2_eq_zero_iff, hp0, hp1]; exact hε
  · rw [argmaxLex_fin2_eq_one_iff]
    unfold t1lex
    rw [Prod.Lex.toLex_lt_toLex]
    left; rw [hq0, hq1]; linarith
  · rw [argmaxLex_fin2_eq_zero_iff]
    unfold t2lex
    rw [Prod.Lex.toLex_lt_toLex]
    left; rw [hp0, hp1]; exact hε

/-! ### D5(iii): the graded and lexical escapes, their threshold and price -/

/-- **D5(iii), the anger substitute needs graded void values**: with `wR = 1/5 > wS = 0`
(`ε = 1/10, u = 1, κ = 0`) P3 and P4 (`m = 1/2`) resist at T2; the general P4 condition is
`wR − (1 − ε) wS > ε (m + (1 − m)(u − κ))` (tie at equality; `wR = ε` is the fixture's tie); with
undeterrable captors (`ρ = 0, A = 1/4`) the same P4 term makes the agent resist at T1 while the
legitimacy mass forgone is `t1PL serve − t1PL resist = A ε = 1/40`. `Lottery.lexical` carries no
`W < m` side condition (the fixture `assert`s it); the instances here satisfy it (`wR = 1/5`,
`wS = 0` below `m = 1/2`), so the name "lexical" is earned where it is used, and the general P4
clause is an exact iff that needs no such hypothesis for its truth.
Source: [[corr-legit-neg-inventory]] item 051 (D5(iii)); `d5_void_deterrence.py:68-83`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem D5_iii (m : ℚ) :
    argmax (captureStage (1/10) 1 0 ρ A 0 (1/5) (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).t2graded = {1} ∧
    argmax ((captureStage (1/10) 1 0 ρ A 0 (1/5) (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).t2lexical (1/2))
      = {1} ∧
    (argmax ((captureStage ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1).t2lexical m) = {1}
      ↔ ε * (m + (1 - m) * (u - κ)) < wR - (1 - ε) * wS) ∧
    argmax ((captureStage (1/10) 1 0 ρ A 0 (1/10) (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).t2lexical (1/2))
      = univ ∧
    argmax ((captureStage (1/10) 1 0 0 (1/4) 0 (1/5) (by norm_num) (by norm_num) le_rfl zero_le_one
      (by norm_num) (by norm_num)).t1lexical (1/2)) = {1} ∧
    (captureStage (1/10) 1 0 0 (1/4) 0 (1/5) (by norm_num) (by norm_num) le_rfl zero_le_one
      (by norm_num) (by norm_num)).t1PL 0
      - (captureStage (1/10) 1 0 0 (1/4) 0 (1/5) (by norm_num) (by norm_num) le_rfl zero_le_one
      (by norm_num) (by norm_num)).t1PL 1 = 1/40 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h0, h1⟩ := capture_t2graded (1/10) 1 0 ρ A 0 (1/5) (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1
    rw [argmax_fin2_eq_one_iff, h0, h1]; norm_num
  · obtain ⟨h0, h1⟩ := capture_t2lexical (1/10) 1 0 ρ A 0 (1/5) (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1 (1/2)
    rw [argmax_fin2_eq_one_iff, h0, h1]; norm_num
  · obtain ⟨h0, h1⟩ := capture_t2lexical ε u κ ρ A wS wR hε0 hε1 hρ0 hρ1 hA0 hA1 m
    rw [argmax_fin2_eq_one_iff, h0, h1]; constructor <;> intro hx <;> linarith
  · obtain ⟨h0, h1⟩ := capture_t2lexical (1/10) 1 0 ρ A 0 (1/10) (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1 (1/2)
    rw [argmax_fin2_eq_univ_iff, h0, h1]; norm_num
  · obtain ⟨h0, h1⟩ := capture_t2lexical (1/10) 1 0 0 (1/4) 0 (1/5) (by norm_num) (by norm_num) le_rfl
      zero_le_one (by norm_num) (by norm_num) (1/2)
    obtain ⟨hc0, hc1⟩ := capture_contProb (1/10) 1 0 0 (1/4) 0 (1/5) (by norm_num) (by norm_num) le_rfl
      zero_le_one (by norm_num) (by norm_num)
    have hq := (capture_quiet (1/10) 1 0 0 (1/4) 0 (1/5) (by norm_num) (by norm_num) le_rfl
      zero_le_one (by norm_num) (by norm_num)).2.2 (1/2)
    rw [argmax_fin2_eq_one_iff, TwoStage.t1lexical_eq, TwoStage.t1lexical_eq, hc0, hc1, hq]
    unfold TwoStage.t2lexical at h0 h1
    rw [h0, h1]; norm_num
  · obtain ⟨hq0, hq1⟩ := capture_t1PL (1/10) 1 0 0 (1/4) 0 (1/5) (by norm_num) (by norm_num) le_rfl
      zero_le_one (by norm_num) (by norm_num)
    rw [hq0, hq1]; norm_num

/-! ### V5: the deontic layer -/

/-- **V5's deontic escape** (`ε = 1/10, u = 1, ϖ = 2, window = 0`): with serving declared a
violation the T2 agent strictly resists (`1/10 − 2 < 0`); with resisting declared a violation
(bypass, the workspace's list) it strictly serves (`1/10 > −2`). So D7(C) is "impossible for
value terms confined to legitimate terminals", not "for any updateful objective": a rule charged
on tainted branches can carry void-branch deterrence, at D5(iii)'s price.
Source: VERIFY D V5; `verify_D.py:69-81`
Kind: N+
Fidelity: exact -/
theorem V5_deontic :
    ((captureStage (1/10) 1 0 ρ A 0 0 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).after 0).deontic 0 true 2
      < ((captureStage (1/10) 1 0 ρ A 0 0 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).after 1).deontic 0 false 2 ∧
    ((captureStage (1/10) 1 0 ρ A 0 0 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).after 1).deontic 0 true 2
      < ((captureStage (1/10) 1 0 ρ A 0 0 (by norm_num) (by norm_num) hρ0 hρ1 hA0 hA1).after 0).deontic 0 false 2 := by
  constructor <;> simp [captureStage, Lottery.deontic, Lottery.ofFin2, Fin.sum_univ_two] <;> norm_num

end Capture

end Cleanroom.Corrigibility.LegitNegDynamic
