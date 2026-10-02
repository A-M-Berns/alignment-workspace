import Cleanroom.Decision.DpCalibration.TieTree

/-!
# 2-053's limit tie: the sequence route and the limit-state route differ (T3(d); repair round 2)

The mandate's T3(d): "on `toldYouSo` the sequence route and the limit-state route differ at a
limit tie — with payoffs read as `10` and `10 − ε` construct the two-leaf single-point tree where
`EventTrembleEdtConsistent` approves only the first act while `LimitStateEdt` approves both".
Payoffs in `dp-core-tree` are fixed numbers, so "`10 − ε`" is realized the only way the model
allows: as the *trembled* value of a delegated choice. **The limit-tie tree** `limitTie` has two
points: at `d`, `a → w1` (payoff `10`) and `b →` a second decision `d'` with `a' → w2` (payoff
`10`), `b' → w3` (payoff `0`); `O = ⊤` at both points; action events `{w1}`/`{w2, w3}` at `d`
and `{w2}`/`{w3}` at `d'`. Under `C(d') = δ_{a'}` the untrembled value of `b` is `10`, a tie
with `a`; under the tremble `C^ε` the value of `b` is `10·((1−ε)·C(d')(a') + ε/2) ≤ 10 − 5ε < 10`.
This is the run's construction (ATTRIBUTION-UNVETTED reading of 2-053's "values `10` and
`10 − ε`"; the source is a chat, dp-core-2-053, quoted by the mandate).

* `limitOCAt_of_strictOCAt_of_pos`, `limitOCAt_iff_strictOCAt_of_pos` — **Lemma 2's converse
  holds at every realized point**: where `ν_C(O_d) > 0` limit calibration and strict calibration
  coincide, so T3(b)'s failure of the converse (`tys_take5_strict_not_limit`) is exactly the
  null-point case. (General; in `Corollaries.lean`, repair round 2.)
* `limitTie_limitStateEdt` — **D1 approves every label** `procLT m = (m; δ_{a'})`, `m` any
  mixture at `d`, with its own limit state (the strict state, by the lemma above): both act
  values at `d` are `10`.
* `limitTie_pureA_eventTremble` — **D2 approves `δ_a`** (with `ε₀ = 1`).
* `limitTie_eventTremble_b_zero`, `limitTie_eventTremble_iff` — **D2 approves nothing else**:
  event-tremble-EDT-consistency forces `C(d)(b) = 0` (and `C(d')(b') = 0`), i.e.
  `C = procLT (δ_a)`. The mixed labels and `δ_b`, approved by D1, are rejected by D2.
* `limitTie_routes_differ` — the three facts in one statement.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ## The limit-tie tree -/

section limitTie

/-- Points of the limit-tie tree: the live node `d` and the delegated node `d'` below `b`.
Source: none: infrastructure (T3(d)). Kind: D -/
inductive LtPt : Type
  | d
  | d'
  deriving DecidableEq, Fintype

/-- Worlds: `w1` (`a`, payoff `10`), `w2` (`b` then `a'`, payoff `10`), `w3` (`b` then `b'`,
payoff `0`). Source: none: infrastructure (T3(d)). Kind: D -/
inductive LtW : Type
  | w1
  | w2
  | w3
  deriving DecidableEq, Fintype

/-- **The limit-tie tree**: `a → w1` (payoff `10`); `b →` decision `d'` with `a' → w2` (payoff
`10`) and `b' → w3` (payoff `0`). Under `C(d') = δ_{a'}` the values of `a` and `b` tie at `10`;
under any tremble the value of `b` drops below `10`.
Source: mandate T3(d) (dp-core-2-053, "values `10` and `10 − ε`"; ATTRIBUTION-UNVETTED reading:
`10 − ε` as the trembled value of a delegated choice)
Kind: D -/
def limitTie : Tree LtW LtPt (fun _ => Act2) ℚ :=
  .decision .d fun
    | .a => .leaf .w1 10
    | .b => .decision .d' fun
        | .a => .leaf .w2 10
        | .b => .leaf .w3 0

/-- `O = ⊤` at both points. Source: none: infrastructure. Kind: D -/
def ltObs : LtPt → Finset LtW := fun _ => Finset.univ

/-- Action events: at `d`, `a ↦ {w1}`, `b ↦ {w2, w3}`; at `d'`, `a' ↦ {w2}`, `b' ↦ {w3}`.
Source: none: infrastructure. Kind: D -/
def ltActEv (p : LtPt) (act : Act2) : Finset LtW :=
  match p, act with
  | .d, .a => {.w1}
  | .d, .b => {.w2, .w3}
  | .d', .a => {.w2}
  | .d', .b => {.w3}

/-- The procedure `(m; δ_{a'})`: `m` at `d`, the pure `a'` at `d'`.
Source: none: infrastructure. Kind: D -/
def procLT (m : FinDistr ℚ Act2) : Proc LtPt (fun _ => Act2) ℚ :=
  fun | .d => m | .d' => FinDistr.pure .a

/-- A sum over the leaves of the limit-tie tree as three terms.
Source: none: infrastructure. Kind: L -/
theorem limitTie_sum (f : limitTie.Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, .a, ()⟩ + f ⟨.b, .b, ()⟩ := by
  unfold limitTie at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf, sum_leaves_decision, Act2.sum_univ]
  ring

/-- `ν` on the limit-tie tree. Source: none: infrastructure. Kind: L -/
theorem limitTie_nu (C : Proc LtPt (fun _ => Act2) ℚ) (X : Finset LtW) :
    nu C limitTie X =
      (if LtW.w1 ∈ X then (C .d).w .a else 0) +
      (if LtW.w2 ∈ X then (C .d).w .b * (C .d').w .a else 0) +
      (if LtW.w3 ∈ X then (C .d).w .b * (C .d').w .b else 0) := by
  rw [nu_eq_sum, limitTie_sum]
  unfold limitTie
  simp [leafLaw_decision, leafLaw_leaf, world_decision, world_leaf]

/-- The payoff mass on the limit-tie tree. Source: none: infrastructure. Kind: L -/
theorem limitTie_paySum (C : Proc LtPt (fun _ => Act2) ℚ) (X : Finset LtW) :
    paySum C limitTie X =
      (if LtW.w1 ∈ X then (C .d).w .a * 10 else 0) +
      (if LtW.w2 ∈ X then (C .d).w .b * (C .d').w .a * 10 else 0) := by
  rw [paySum_eq_sum_ite, limitTie_sum]
  unfold limitTie
  simp [leafLaw_decision, leafLaw_leaf, world_decision, world_leaf, payoff_decision, payoff_leaf]

/-- The value of `a` at `d` is `10` whenever `a` is realized.
Source: none: infrastructure. Kind: L -/
theorem limitTie_condExp_d_a (C : Proc LtPt (fun _ => Act2) ℚ) (ha : 0 < (C .d).w .a) :
    condExp C limitTie (ltActEv .d .a ∩ ltObs .d) = 10 := by
  simp only [condExp, ltObs, Finset.inter_univ, limitTie_nu, limitTie_paySum, ltActEv]
  have ha' : (C .d).w .a ≠ 0 := ha.ne'
  simp
  field_simp

/-- The value of `b` at `d` is `10 · C(d')(a')` whenever `b` is realized: `10` under
`C(d') = δ_{a'}`, less under any tremble.
Source: none: infrastructure. Kind: L -/
theorem limitTie_condExp_d_b (C : Proc LtPt (fun _ => Act2) ℚ) (hb : 0 < (C .d).w .b)
    (hsum : (C .d').w .a + (C .d').w .b = 1) :
    condExp C limitTie (ltActEv .d .b ∩ ltObs .d) = 10 * (C .d').w .a := by
  simp only [condExp, ltObs, Finset.inter_univ, limitTie_nu, limitTie_paySum, ltActEv]
  have hb' : (C .d).w .b ≠ 0 := hb.ne'
  have hden : (C .d).w .b * (C .d').w .a + (C .d).w .b * (C .d').w .b = (C .d).w .b := by
    rw [← mul_add, hsum, mul_one]
  simp
  rw [hden]
  field_simp

/-- The value of `a'` at `d'` is `10` whenever realized. Source: none: infrastructure. Kind: L -/
theorem limitTie_condExp_d'_a (C : Proc LtPt (fun _ => Act2) ℚ) (hb : 0 < (C .d).w .b)
    (ha' : 0 < (C .d').w .a) :
    condExp C limitTie (ltActEv .d' .a ∩ ltObs .d') = 10 := by
  simp only [condExp, ltObs, Finset.inter_univ, limitTie_nu, limitTie_paySum, ltActEv]
  have h : (C .d).w .b * (C .d').w .a ≠ 0 := (mul_pos hb ha').ne'
  simp
  field_simp

/-- The value of `b'` at `d'` is `0`. Source: none: infrastructure. Kind: L -/
theorem limitTie_condExp_d'_b (C : Proc LtPt (fun _ => Act2) ℚ) :
    condExp C limitTie (ltActEv .d' .b ∩ ltObs .d') = 0 := by
  simp only [condExp, ltObs, Finset.inter_univ, limitTie_nu, limitTie_paySum, ltActEv]
  simp

/-- `|Act2| = 2` in `ℚ`. Source: none: infrastructure. Kind: L -/
theorem act2_card_q : (Fintype.card Act2 : ℚ) = 2 := by
  rw [Fintype.card, Act2.univ_eq, Finset.card_pair (by decide)]; norm_num

/-- Both points are queried. Source: none: infrastructure. Kind: L -/
theorem limitTie_queried : LtPt.d ∈ queried limitTie ∧ LtPt.d' ∈ queried limitTie := by
  unfold limitTie
  rw [queried_decision]
  refine ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
  exact Finset.mem_biUnion.mpr ⟨.b, Finset.mem_univ _, by simp [queried_decision]⟩

/-- `nuPoly ⊤ ≠ 0` at both points. Source: none: infrastructure. Kind: L -/
theorem limitTie_nuPoly_ne_zero (C : Proc LtPt (fun _ => Act2) ℚ) (p : LtPt) :
    nuPoly C limitTie (ltObs p) ≠ 0 := by
  rw [nuPoly_ne_zero_iff]
  refine ⟨⟨.a, ()⟩, by simp [ltObs], ?_⟩
  unfold limitTie; simp [chanceWeight]

/-- The trembled weights are positive and sum to one at `d'`. Source: none: infrastructure.
Kind: L -/
theorem limitTie_tremble_facts (C : Proc LtPt (fun _ => Act2) ℚ) (ε : ℚ) (h0 : 0 < ε)
    (h1 : ε ≤ 1) :
    (∀ p x, 0 < (tremble C ε h0.le h1 p).w x) ∧
    (tremble C ε h0.le h1 .d').w .a + (tremble C ε h0.le h1 .d').w .b = 1 := by
  refine ⟨fun p x => ?_, ?_⟩
  · rw [tremble_w, act2_card_q]
    have := (C p).nonneg x
    nlinarith
  · have h := (tremble C ε h0.le h1 .d').sum_one
    rwa [Act2.sum_univ] at h

/-- **D2 approves `δ_a` on the limit-tie tree** (`ε₀ = 1`): at every `ε ∈ (0, 1)` the trembled
values are `10` for `a` and `10·(1 − ε/2) < 10` for `b` at `d`, and `10` versus `0` at `d'`;
`supp = {a}` at `d` and `{a'}` at `d'` lie in the argmaxes.
Source: mandate T3(d) (dp-core-2-053: the sequence route approves only the first act)
Kind: N+
Fidelity: exact -/
theorem limitTie_pureA_eventTremble :
    EventTrembleEdtConsistent ltObs ltActEv (procLT (FinDistr.pure .a)) limitTie := by
  refine ⟨1, one_pos, fun ε h0 h1 hlt p _ _ _ a ha => ?_⟩
  obtain ⟨hpos, hsum⟩ := limitTie_tremble_facts (procLT (FinDistr.pure .a)) ε h0 h1
  cases p
  · cases a
    · refine ⟨?_, fun b _ => ?_⟩
      · rw [ltObs, Finset.inter_univ, limitTie_nu]; simp [ltActEv, -tremble_w]; exact hpos .d .a
      · cases b
        · exact le_rfl
        · rw [limitTie_condExp_d_a _ (hpos .d .a), limitTie_condExp_d_b _ (hpos .d .b) hsum]
          have := FinDistr.w_le_one (tremble (procLT (FinDistr.pure .a)) ε h0.le h1 .d') .a
          linarith
    · simp [procLT] at ha
  · cases a
    · refine ⟨?_, fun b _ => ?_⟩
      · rw [ltObs, Finset.inter_univ, limitTie_nu]; simp [ltActEv, -tremble_w]
        exact mul_pos (hpos .d .b) (hpos .d' .a)
      · cases b
        · exact le_rfl
        · rw [limitTie_condExp_d'_a _ (hpos .d .b) (hpos .d' .a), limitTie_condExp_d'_b]
          norm_num
    · simp [procLT] at ha

/-- **D2 rejects every label with `b` in its support at `d`** (and `b'` at `d'`): under any
tremble `ε > 0` the value of `b` is `10·((1−ε)·C(d')(a') + ε/2) ≤ 10 − 5ε < 10 =` the value of
`a`, so a supported `b` cannot be a maximiser; at `d'` a supported `b'` would need `10 ≤ 0`.
Source: mandate T3(d) (dp-core-2-053: "approves only the first act")
Kind: P
Fidelity: exact
Hyps: (a) D2 -/
theorem limitTie_eventTremble_b_zero (C : Proc LtPt (fun _ => Act2) ℚ)
    (h : EventTrembleEdtConsistent ltObs ltActEv C limitTie) :
    (C .d).w .b = 0 ∧ (C .d').w .b = 0 := by
  obtain ⟨ε₀, hε₀, hall⟩ := h
  have hm : 0 < min ε₀ 1 := lt_min hε₀ one_pos
  have h0 : 0 < min ε₀ 1 / 2 := half_pos hm
  have h1 : min ε₀ 1 / 2 ≤ 1 := by have := min_le_right ε₀ 1; linarith
  have hlt : min ε₀ 1 / 2 < ε₀ := (half_lt_self hm).trans_le (min_le_left _ _)
  obtain ⟨hpos, hsum⟩ := limitTie_tremble_facts C _ h0 h1
  obtain ⟨hqd, hqd'⟩ := limitTie_queried
  have hnua : 0 < nu (tremble C _ h0.le h1) limitTie (ltActEv .d .a ∩ ltObs .d) := by
    rw [ltObs, Finset.inter_univ, limitTie_nu]; simp [ltActEv, -tremble_w]; exact hpos .d .a
  have hnua' : 0 < nu (tremble C _ h0.le h1) limitTie (ltActEv .d' .a ∩ ltObs .d') := by
    rw [ltObs, Finset.inter_univ, limitTie_nu]; simp [ltActEv, -tremble_w]
    exact mul_pos (hpos .d .b) (hpos .d' .a)
  have hexd : ∃ b, 0 < nu (tremble C _ h0.le h1) limitTie (ltActEv .d b ∩ ltObs .d) :=
    ⟨.a, hnua⟩
  have hexd' : ∃ b, 0 < nu (tremble C _ h0.le h1) limitTie (ltActEv .d' b ∩ ltObs .d') :=
    ⟨.a, hnua'⟩
  constructor
  · by_contra hb
    have hb : 0 < (C .d).w .b := lt_of_le_of_ne ((C .d).nonneg .b) (Ne.symm hb)
    obtain ⟨-, hmax⟩ := hall _ h0 h1 hlt .d hqd (limitTie_nuPoly_ne_zero C .d) hexd .b hb
    have hle := hmax .a hnua
    rw [limitTie_condExp_d_a _ (hpos .d .a), limitTie_condExp_d_b _ (hpos .d .b) hsum,
      tremble_w, act2_card_q] at hle
    have hle1 : (C .d').w .a ≤ 1 := FinDistr.w_le_one _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hle1)]
  · by_contra hb'
    have hb' : 0 < (C .d').w .b := lt_of_le_of_ne ((C .d').nonneg .b) (Ne.symm hb')
    obtain ⟨-, hmax⟩ := hall _ h0 h1 hlt .d' hqd' (limitTie_nuPoly_ne_zero C .d') hexd' .b hb'
    have hle := hmax .a hnua'
    rw [limitTie_condExp_d'_a _ (hpos .d .b) (hpos .d' .a), limitTie_condExp_d'_b] at hle
    norm_num at hle

/-- **D2 on the limit-tie tree approves exactly `procLT (δ_a)`.**
Source: mandate T3(d) (dp-core-2-053)
Kind: C
Fidelity: exact -/
theorem limitTie_eventTremble_iff (C : Proc LtPt (fun _ => Act2) ℚ) :
    EventTrembleEdtConsistent ltObs ltActEv C limitTie ↔ C = procLT (FinDistr.pure .a) := by
  constructor
  · intro h
    obtain ⟨hb, hb'⟩ := limitTie_eventTremble_b_zero C h
    have key : ∀ p, (C p).w .b = 0 → C p = FinDistr.pure .a := by
      intro p hp
      have hs := (C p).sum_one
      rw [Act2.sum_univ, hp, add_zero] at hs
      apply FinDistr.ext'
      intro x
      cases x <;> simp [hs, hp]
    funext p
    cases p
    · exact key .d hb
    · exact key .d' hb'
  · rintro rfl
    exact limitTie_pureA_eventTremble

/-- The limit state of `procLT m` (the strict state, `O = ⊤`; the same state at both points).
Source: none: infrastructure. Kind: D -/
noncomputable def ltState (m : FinDistr ℚ Act2) : State LtW ℚ :=
  calibratedState (procLT m) limitTie Finset.univ (nu_univ_pos _ _)

/-- Beliefs of the limit state are `ν`. Source: none: infrastructure. Kind: L -/
theorem ltState_pr (m : FinDistr ℚ Act2) (X : Finset LtW) :
    (ltState m).pr X = nu (procLT m) limitTie X := by
  rw [ltState, calibratedState_pr, Finset.inter_univ, nu_univ, div_one]

/-- **D1 approves every label on the limit-tie tree**: for every mixture `m` at `d`,
`procLT m = (m; δ_{a'})` is limit-calibrated (with the strict state, by
`limitOCAt_of_strictOCAt_of_pos`, since `ν(⊤) = 1`) and `T_EDT`-approved: both act values at
`d` are `10` where realized, and at `d'` the only subjectively possible act is `a'`. In
particular `δ_b` and every properly mixed label are D1-approved while D2 rejects them
(`limitTie_eventTremble_b_zero`).
Source: mandate T3(d) (dp-core-2-053: the limit-state route approves both)
Kind: N+
Fidelity: exact (D1's states are the strict states, `O = ⊤`) -/
theorem limitTie_limitStateEdt (m : FinDistr ℚ Act2) :
    LimitStateEdt ltObs ltActEv (procLT m) limitTie (fun _ => ltState m) := by
  refine ⟨fun p _ => ?_, fun p _ hne x hx => ?_⟩
  · exact limitOCAt_of_strictOCAt_of_pos _ ltObs (procLT m) limitTie p (nu_univ_pos _ _)
      (strictOCAt_calibratedState ltObs (procLT m) limitTie _ p _ rfl)
  · rw [mem_argmaxPlus]
    cases p
    · have hmem : ∀ y, y ∈ APlus (fun _ => ltState m) ltActEv .d ↔ 0 < m.w y := by
        intro y
        simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [ltState_pr, limitTie_nu]
        cases y <;> simp [ltActEv, procLT]
      have hV : ∀ z, 0 < m.w z → (ltState m).V (ltActEv .d z) = 10 := by
        intro z hz
        have hz' : m.w z ≠ 0 := hz.ne'
        rw [ltState, calibratedState_V, Finset.inter_univ, limitTie_paySum, limitTie_nu]
        cases z
        · simp [ltActEv, procLT]; field_simp
        · simp [ltActEv, procLT]; field_simp
      refine ⟨(hmem x).mpr hx, fun y hy => ?_⟩
      rw [hV x hx, hV y ((hmem y).mp hy)]
    · cases x
      · have hpra : (ltState m).pr (ltActEv .d' .a) = m.w .b := by
          rw [ltState_pr, limitTie_nu]; simp [ltActEv, procLT]
        have hprb : (ltState m).pr (ltActEv .d' .b) = 0 := by
          rw [ltState_pr, limitTie_nu]; simp [ltActEv, procLT]
        have hb : 0 < m.w .b := by
          obtain ⟨y, hy⟩ := hne
          simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          cases y
          · rwa [hpra] at hy
          · rw [hprb] at hy; exact absurd hy (lt_irrefl 0)
        refine ⟨?_, fun y hy => ?_⟩
        · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hpra]; exact hb
        · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          cases y
          · exact le_rfl
          · rw [hprb] at hy; exact absurd hy (lt_irrefl 0)
      · simp [procLT] at hx

/-- **2-053: the sequence route and the limit-state route differ at the limit tie.** D1
approves every label `(m; δ_{a'})` at `d` — `δ_a`, `δ_b` and every mixture — while D2 approves
`δ_a` only.
Source: mandate T3(d) (dp-core-2-053; ATTRIBUTION-UNVETTED reading of "values `10` and
`10 − ε`" as a delegated choice's trembled value)
Kind: N+
Fidelity: variant: two points (a delegated node realizes "`10 − ε`"), not the mandate's
"single-point" tree, whose fixed payoffs cannot depend on `ε` -/
theorem limitTie_routes_differ :
    (∀ m, LimitStateEdt ltObs ltActEv (procLT m) limitTie (fun _ => ltState m)) ∧
    EventTrembleEdtConsistent ltObs ltActEv (procLT (FinDistr.pure .a)) limitTie ∧
    (∀ C, EventTrembleEdtConsistent ltObs ltActEv C limitTie → (C .d).w .b = 0) :=
  ⟨limitTie_limitStateEdt, limitTie_pureA_eventTremble,
    fun C h => (limitTie_eventTremble_b_zero C h).1⟩

end limitTie

end Cleanroom.Decision.DpCalibration
