import Cleanroom.Decision.DpSmokingLesion.Steelman
import Cleanroom.Decision.DpSmokingLesion.Tickle12

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# T15: pooled points — no observation-calibration sense gives the agent its label alone

[[dp-smoking-lesion-mandate]] T15, source dp-sl-2-008 (reading fixed there): on the two-type
tree with both type points at `O = ⊤` (the worlds carry the type), at any state satisfying
Definition 8's clause 1 under a procedure `C'` (the strict state for `C' = C`, a masked state's
self-model, the limit state at the realized point):

* **(a)** the state carries no type information beyond the prior: `P_s(type = S) = n`
  (`pooled_pr_type`) — never `1` for `n < 1`;
* **(b)** `P_s(m = a) = n C'(d_S)(a) + (1 − n) C'(d_N)(a)` (`pooled_pr_act`), which equals the
  point's own label `C'(d_t)(a)` for both acts iff the two labels agree
  (`pooled_selfTransparent_iff`);
* **(c)** hence "label known, type inferred" — self-transparency together with certainty of
  the type — is realized by no clause-1 state at a pooled point for any procedure
  (`pooled_no_label_alone`); at the strict/limit grades with `C' = C`, at the masked grade with
  `C'` the self-model;
* **non-vacuity of the impossibility**: the **per-run SSC** state at `d_t` *does* carry the
  type, `P_s(type = t) = 1` (`pooled_perRun_type_certain`: `occ(d_t)` is the `t`-branch) — the
  epistemic state is realizable, just not by an OC sense.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

section pooled

variable (n : ℚ) (n0 : 0 ≤ n) (n1 : n ≤ 1) (U : Bool → Bool → Bool → ℚ) (κ : Bool → ℚ)
  (κ0 : ∀ t, 0 ≤ κ t) (κ1 : ∀ t, κ t ≤ 1)

local notation "TT" => twoType n n0 n1 U κ κ0 κ1

variable (C : Proc Bool (fun _ => Bool) ℚ) (s : Bool → State TickleW ℚ)

/-- The type event at the pooled point: `{type = t}` (`tickleObs t`, the world's first
coordinate).
Source: dp-sl-2-008 ("`P_s(t ∣ m = a)`")
Kind: D -/
abbrev typeEv (t : Bool) : Finset TickleW := tickleObs t

/-- `ν(type = t) = n_t` on the two-type tree for every procedure. Source: none: infrastructure. Kind: L -/
theorem twoType_nu_type (t : Bool) : nu C TT (typeEv t) = typeRate n t := by
  have hnu : ∀ X, nu C TT X = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
      if (decide (i = 0), m, decide (j = 0)) ∈ X then leafLaw C TT ⟨i, m, j, ()⟩ else 0 := by
    intro X; rw [nu_eq_sum, twoType_sum]; rfl
  have hw : ∀ t : Bool, (C t).w false = 1 - (C t).w true := by
    intro t; have := (C t).sum_one; rw [Fintype.sum_bool] at this; linarith
  rw [hnu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, twoType_leafLaw, typeEv, mem_tickleObs, typeRate]
  cases t <;> simp [hw] <;> ring

/-- **(a) A clause-1 state at a pooled point carries the population type rate**:
`P_{s_d}(type = S) = n` for every procedure and both points.
Source: dp-sl-2-008 ("OC states carry the population mixture (no type)"); mandate T15(a)
Kind: P
Fidelity: exact
Hyps: (a) clause 1 of Definition 8 at `d` under `C` at `O = ⊤` -/
theorem pooled_pr_type (d : Bool) (h1 : StrictClause1At s slObs C TT d) (t : Bool) :
    (s d).pr (typeEv t) = typeRate n t := by
  rw [pr_eq_nu_of_strictClause1At_univ s C TT d h1, twoType_nu_type]

/-- **(b) A clause-1 state's act probabilities are the population's**:
`P_{s_d}(m = a) = n C(d_S)(a) + (1 − n) C(d_N)(a)`.
Source: dp-sl-2-008; mandate T15(b)
Kind: L -/
theorem pooled_pr_act (d : Bool) (h1 : StrictClause1At s slObs C TT d) (a : Bool) :
    (s d).pr (evM a) = n * (C true).w a + (1 - n) * (C false).w a := by
  rw [pr_eq_nu_of_strictClause1At_univ s C TT d h1, (twoType_nu_act n n0 n1 U κ κ0 κ1 C a).1]

/-- **(b) Self-transparency at a pooled point iff the two labels agree**: for `n ∈ (0, 1)`,
`P_{s_d}(m = a) = C(d)(a)` for both acts iff `C(d_S) = C(d_N)` (as weights on `smoke`).
Source: dp-sl-2-008 ("`P_s(m = a) = C(d)(a)` … iff `C(d_L)(a) = C(d_N)(a)`"); mandate T15(b)
Kind: C
Fidelity: exact
Hyps: (a) clause 1 at `d`; (a) `0 < n < 1` -/
theorem pooled_selfTransparent_iff (hn0 : 0 < n) (hn1 : n < 1) (d : Bool)
    (h1 : StrictClause1At s slObs C TT d) :
    (∀ a, (s d).pr (evM a) = (C d).w a) ↔ (C true).w true = (C false).w true := by
  have hw : ∀ t : Bool, (C t).w false = 1 - (C t).w true := by
    intro t; have := (C t).sum_one; rw [Fintype.sum_bool] at this; linarith
  have hact := pooled_pr_act n n0 n1 U κ κ0 κ1 C s d h1
  constructor
  · intro h
    have := h true
    rw [hact] at this
    cases d
    · -- `n q_S + (1 − n) q_N = q_N` ⟹ `q_S = q_N`
      have : n * ((C true).w true - (C false).w true) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hn0.ne'
      · linarith
    · have : (1 - n) * ((C false).w true - (C true).w true) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' (by linarith)
      · linarith
  · intro h a
    rw [hact]
    cases d <;> cases a <;> simp only [hw] <;> rw [h] <;> ring

/-- **(c) "Label known, type inferred" is realized by no clause-1 state at a pooled point**:
for `n ∈ (0, 1)`, no state satisfying Definition 8's clause 1 at `d_t` under any procedure
`C'` (the strict and limit states for `C' = C`; a masked state under its self-model) is both
self-transparent for its point's label and certain of its type. The type probability is the
population rate `n_t`, never `1`.
Source: dp-sl-2-008 ("no calibration sense `κ` among Definitions 8–13 and no `C` such that the
`κ`-calibrated state at the pooled point has `P_s(m=a) = C(d)(a)` and `P_s(t ∣ m=a)` equal to
the Bayes posterior of the type given the label"; OC half); mandate T15(c)
Kind: L
Fidelity: variant: the second clause read as "certain of its type" (`P_s(type = t) = 1`), the
strongest form of "type inferred from the label". This **changes the mandate's reading**
("`P_s(type ∣ m=a)` equal to the Bayes posterior of the type given the label"): under that
reading the conjunction is *satisfiable* whenever the two labels agree
(`pooled_bayes_reading_of_eq_labels`: self-transparent by `pooled_selfTransparent_iff`, and the
posterior of the type given an uninformative label is the prior `n_t`, which the pooled state
carries), so the mandate's "(c) the conjunction fails for every `C`" is false as written and
the certainty reading is the one that fails. The content is `pooled_pr_type` plus `n_t ≠ 1`;
the second conjunct is the propositional consequence of the first, kept as the literal form of
(c)
Hyps: (a) clause 1 at `d` under `C'`; (a) `0 < n < 1` -/
theorem pooled_no_label_alone (hn0 : 0 < n) (hn1 : n < 1) (C' : Proc Bool (fun _ => Bool) ℚ)
    (d : Bool) (h1 : StrictClause1At s slObs C' TT d) :
    (s d).pr (typeEv d) ≠ 1 ∧ ¬ ((∀ a, (s d).pr (evM a) = (C' d).w a) ∧ (s d).pr (typeEv d) = 1) := by
  have hT := pooled_pr_type n n0 n1 U κ κ0 κ1 C' s d h1 d
  have hne : (s d).pr (typeEv d) ≠ 1 := by
    rw [hT]; unfold typeRate; cases d <;> simp <;> linarith
  exact ⟨hne, fun h => hne h.2⟩

/-- **The mandate's Bayes-posterior reading of dp-sl-2-008 is satisfiable at a pooled point**:
when the two labels agree, every clause-1 state at either point is self-transparent
(`P_s(m = a) = C(d)(a)`) *and* has `P_s(type = t ∧ m = a) = n_t · P_s(m = a)` for both types
and both acts — the posterior of the type given the (uninformative) label is the prior `n_t`,
which is the Bayes posterior. So "(c) the conjunction fails for every `C`" holds only under the
certainty reading (`pooled_no_label_alone`), not under the mandate's own reading.
Source: dp-sl-2-008 (the mandate's reading of "`P_s(t ∣ m=a)` equal to the Bayes posterior");
mandate T15(c), refuted as written; audit r1 fidelity §3.5, adversarial N4
Kind: N+
Fidelity: exact for the Bayes-posterior reading (cross-multiplied joint form)
Hyps: (a) clause 1 at `d` under `C`; (a) `0 < n < 1`; (a) the labels agree -/
theorem pooled_bayes_reading_of_eq_labels (hn0 : 0 < n) (hn1 : n < 1) (d : Bool)
    (h1 : StrictClause1At s slObs C TT d) (heq : (C true).w true = (C false).w true) :
    (∀ a, (s d).pr (evM a) = (C d).w a) ∧
    ∀ t a, (s d).pr (typeEv t ∩ evM a) = typeRate n t * (s d).pr (evM a) := by
  refine ⟨(pooled_selfTransparent_iff n n0 n1 U κ κ0 κ1 C s hn0 hn1 d h1).mpr heq, fun t a => ?_⟩
  rw [pr_eq_nu_of_strictClause1At_univ s C TT d h1, pr_eq_nu_of_strictClause1At_univ s C TT d h1]
  have hnu : ∀ X, nu C TT X = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
      if (decide (i = 0), m, decide (j = 0)) ∈ X then leafLaw C TT ⟨i, m, j, ()⟩ else 0 := by
    intro X; rw [nu_eq_sum, twoType_sum]; rfl
  have hw : ∀ t : Bool, (C t).w false = 1 - (C t).w true := by
    intro t; have := (C t).sum_one; rw [Fintype.sum_bool] at this; linarith
  rw [hnu, hnu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, twoType_leafLaw, typeEv, mem_tickleObs, mem_evM,
    Finset.mem_inter, typeRate]
  cases t <;> cases a <;> simp [hw, heq] <;> ring

/-- The strict, limit and masked states at a pooled point are clause-1 states (for `C`, `C`
and the self-model respectively), so `pooled_no_label_alone` applies at all three OC grades.
Source: dp-sl-2-008; mandate T15(c) ("at strict/limit, and at masked for every self-model")
Kind: C
Fidelity: exact (masked = first disjunct; the vacuity disjunct cannot fire at `⊤`)
Hyps: (a) `0 < n < 1` -/
theorem pooled_no_label_alone_grades (hn0 : 0 < n) (hn1 : n < 1) (d : Bool) :
    (StrictOCAt s slObs C TT d → (s d).pr (typeEv d) ≠ 1) ∧
    (LimitOCAt s slObs C TT d → (s d).pr (typeEv d) ≠ 1) ∧
    (MaskedOCAt s slObs C TT d → (s d).pr (typeEv d) ≠ 1) := by
  have hpos : 0 < nu C TT (slObs d) := by rw [slObs_apply]; exact nu_univ_pos C _
  refine ⟨fun hs => (pooled_no_label_alone n n0 n1 U κ κ0 κ1 s hn0 hn1 C d (hs hpos).1).1,
    fun hs => (pooled_no_label_alone n n0 n1 U κ κ0 κ1 s hn0 hn1 C d
      (limitOCAt_imp_strictOCAt s slObs C TT d hs hpos).1).1, ?_⟩
  rintro (⟨C', -, -, hcl⟩ | ⟨-, hnull⟩)
  · exact (pooled_no_label_alone n n0 n1 U κ κ0 κ1 s hn0 hn1 C' d hcl.1).1
  · exfalso
    have := hnull (C.deviate d FinDistr.uniform) ⟨FinDistr.uniform, fun a => FinDistr.uniform_w_pos a, rfl⟩
    rw [slObs_apply, nu_univ] at this
    exact one_ne_zero this

/-- Every leaf of the two-type tree is `⟨i, m, j, ()⟩`. Source: none: infrastructure. Kind: L -/
theorem twoType_leaves (ℓ : (TT).Leaves) :
    ∃ (i : Fin 2) (m : Bool) (j : Fin 2), ℓ = ⟨i, m, j, ()⟩ := by
  unfold twoType at ℓ
  rcases ℓ with ⟨i, m, j, ⟨⟩⟩
  exact ⟨i, m, j, rfl⟩

/-- `occ(d_t)` on the two-type tree is the `t`-branch: the runs whose world has type `t`.
Source: none: infrastructure. Kind: L -/
theorem twoType_occ_eq (t : Bool) : occ t TT = worldEv TT (typeEv t) := by
  ext ℓ
  obtain ⟨i, m, j, rfl⟩ := twoType_leaves n n0 n1 U κ κ0 κ1 ℓ
  rw [mem_occ, twoType_count]
  simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and, typeEv, mem_tickleObs,
    (twoType_world_payoff n n0 n1 U κ κ0 κ1 i m j).1]
  by_cases h : decide (i = 0) = t <;> simp [h]

/-- **Non-vacuity of the impossibility: the per-run SSC state knows its type.** At `d_t` with
`n_t > 0`, a per-run calibrated state has `P_{s}(type = t) = 1`: `occ(d_t)` is the `t`-branch, on
which the type is constant. The epistemic state "type known" is realizable — by
occurrence-conditioning, not by any observation-calibration sense.
Source: dp-sl-2-008 ("SSC states carry the type (Proposition 12)"); mandate T15 ("show the
*SSC* state at `d_t` does carry the type")
Kind: P
Fidelity: exact
Hyps: (a) `PerRunSSCAt` at `d_t`; (a) `0 < n_t` -/
theorem pooled_perRun_type_certain (t : Bool) (hpos : 0 < typeRate n t)
    (hs : PerRunSSCAt s C TT t) : (s t).pr (typeEv t) = 1 := by
  have hocc : mass C TT (occ t TT) = typeRate n t := by
    rw [twoType_occ_eq]; exact twoType_nu_type n n0 n1 U κ κ0 κ1 C t
  have h1 := (hs (by rw [hocc]; exact hpos)).1 (typeEv t)
  rw [twoType_occ_eq, Finset.inter_self, ← twoType_occ_eq, hocc] at h1
  exact mul_right_cancel₀ hpos.ne' (by rw [h1, one_mul])

end pooled

/-- **T15 on the robots at `n = ½`** (N+): at the pooled strict state for any label the type
probability is `½`, self-transparency holds iff the labels agree, and the per-run state at
`d_S` is certain of the type.
Source: dp-sl-2-008 (witness: the steelman's pooled points); mandate T15
Kind: N+ -/
theorem pooled_robots_instance (C : Proc Bool (fun _ => Bool) ℚ) :
    let s₀ : Bool → State TickleW ℚ :=
      fun _ => calibratedState C (twoType (1/2) (by norm_num) (by norm_num) uRobot κRobot
        κRobot_nonneg κRobot_le_one) Finset.univ (nu_univ_pos _ _)
    (s₀ true).pr (typeEv true) = 1/2 ∧ (s₀ false).pr (typeEv true) = 1/2 ∧
      ((∀ a, (s₀ true).pr (evM a) = (C true).w a) ↔ (C true).w true = (C false).w true) := by
  intro s₀
  have h1 : ∀ d, StrictClause1At s₀ slObs C (twoType (1/2) (by norm_num) (by norm_num) uRobot
      κRobot κRobot_nonneg κRobot_le_one) d := fun d =>
    (strictClausesAt_calibratedState slObs C _ s₀ d _ rfl).1
  refine ⟨?_, ?_, ?_⟩
  · rw [pooled_pr_type _ _ _ _ _ _ _ C s₀ true (h1 true)]; simp [typeRate]
  · rw [pooled_pr_type _ _ _ _ _ _ _ C s₀ false (h1 false)]; simp [typeRate]
  · exact pooled_selfTransparent_iff _ _ _ _ _ _ _ C s₀ (by norm_num) (by norm_num) true (h1 true)

end Cleanroom.Decision.DpSmokingLesion
