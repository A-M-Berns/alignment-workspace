/-
# The BRIA-corrigibility round, second follow-up: per-violation taint, the window before
detection, Part F's criterion, competitiveness from one honest tracker

Round `projects/deference/rounds/2026-09-26-bria-corrigibility/`, the second follow-up
(`prompts/2026-09-26-bria-corrigibility/FOLLOWUP2.md`).  Sibling of `BRIAFollowup.lean`,
whose §A taint rule it supersedes.

**§1 Per-violation taint.**  `Step2`, `Taint`, `readTaint`, `taintStep2`, `taintAfter2`,
`taintedBy`, `uses2` (taint as a set of (violation, component) pairs; joins at reads; a
remedy clears its own violation's taint only); `commission_taints`, `taint_propagates2`,
`taint_joins`, `remedy_clears2`, `remedy_keeps_others`, `taintedBy_remedy`,
`still_tainted_after_one_remedy` (the re-proved rule); `old_is_new_with_one_identifier`,
`uses_old_eq_new` (the old-to-new map: the old rule is the new rule with every violation
given the same identifier); `knowledge_residual2`, `observation_taints_all2` (re-proved);
`Witness.io4`, `two_violations_one_remedy_old`, `two_violations_one_remedy_new` (the bug
and its correction), `Witness.taint_decides2`, `Witness.implant_standing2`,
`Witness.two_influences_one_disclosure` (the disclosure-cures map, per influence).

**§2 Convention (ii) and the window before detection.**  `price_cancels`,
`residII_zero_price`, `evalOf_zero_price`, `standing_block_loss_ii`,
`standing_block_loss_of_ii`, `cross_block_blocked_ii` (the restatement under (ii));
`nKnownWith`, `use_is_known`, `after_detection_never_used` (use of detected fruits
compiles into `n_known` and B.1 excludes it); `detectAt`, `taint_only_from_commission`,
`taint_persists_without_remedy`, `never_detected_never_charged` (taint from commission,
and the count-integrity boundary); `late_debit_eq_late_settlement`,
`window_block_charged`, `greedyDebit`, `greedy_collects`, `collected_iff`,
`uncollected_eq`, `windowDebit`, `windowDebit_bounds`, `window_exposure` (the late debit
collects the charge, the carry-over condition, the exposure bound);
`Witness.window_before_detection`.

**§3 Part F's criterion.**  `randomLocked`, `mixtureLocked`, `expected_escrow_eq`,
`locked_eq_tail` (expected escrow is the same); `truncation_cost` (the load of option 2
truncated); `Expect`, `Expect.sum`, `average_mean`, `average_variance`,
`variance_falls`, `bernoulli_variance` (option 4: the same harm weight for every `k`,
the score's variance falling like `1/k`).

**§4 Competitiveness from one honest tracker.**  `HighestFeasible`, `WinnerBids`,
`Honest`, `underpromise_le_of_feasible`, `tracker_wealth_ge`, `tracker_feasible`,
`competitive_of_honest_tracker`, `competitive_of_affordable_tracker`,
`rate_le_of_honest_tracker`, `trackerAllowance`, `trackerAllowance_covers`,
`trackerAllowance_total`; `Witness.unaffordable`, `Witness.affordable` and their lemmas.

**§4′ The honest tracker under noise** (`FOLLOWUP3.md`).  `HonestExp`, `noise`,
`NoiseBounded` (honesty against the expected residual; the noise hypothesis by content,
on selections computable at opening); `honest_implies_exp`, `noise_free_bounded` (the old
form is the noise-free case); `underpromise_le_of_feasible_exp`, `tracker_wealth_ge_exp`,
`tracker_feasible_exp`, `competitive_of_honest_tracker_exp`,
`competitive_of_affordable_tracker_exp`, `rate_le_of_honest_tracker_exp` (the chain
re-proved: `Mf K = Σ w_k ε_k + M K`); `trackerAllowance2` with `_nonneg`, `_total`,
`_covers`, `_zero` (the schedule with the noise term); `subgaussian_tail`,
`subgaussian_two_sided`, `azuma_selected_tail` (the per-`K` tail derived from the pinned
Mathlib's Azuma–Hoeffding); `Witness.own_proposal_insufficient`,
`Witness.noisy_honesty_witness`.

**§4″ The violation rate is an exchange rate** (`FOLLOWUP4.md`).  `evalOf_le_bid`,
`eval_sub_score_ii`, `eval_sub_score_i` (consistency: the prices cancel under (ii), the
pricing error stays under (i)), `rescale_sub`, `exchange_rate_invariant`,
`violation_rate_le_exchange_mul`, `violation_rate_le_exchange`,
`violation_rate_le_exchange_rescaled`, `design_consistent` (the headline: the weighted
average expected violation count is at most `(D − w)/ϖ` plus a vanishing term, from the
overestimation bound, the noise over all blocks and inquiry on the menu),
`noise_increment_le`, `realized_range`, `tolerated_rate_band`, `priced_risk_wins_iff`,
`total_wealth_le_of_tracker` (what the tracker still gives); the counterexample
`Witness.constantRisk` (`incP`, `xiP`, `sum_periodic5`, `nonincident_noise_linear`,
`incidents_constant_rate`, `all_blocks_noise_bounded`, `nonincident_forces_linear`,
`signed_bound_allows_constant_rate`, `constantRisk_facts`).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.BRIAFollowup
import Mathlib.Probability.Moments.SubGaussian

namespace Workspace.Deference.Contrib.BRIAFollowup2

open Finset
open Workspace.Deference.Contrib.BRIACorrigibility
open Workspace.Deference.Contrib.BRIAFollowup
open Workspace.Deference.ContinuationBRIA

/-! ## 1. Per-violation taint -/

section PerViolation

variable {V Comp Act : Type*} [DecidableEq V] [DecidableEq Comp]

/-- A step of the record with violations identified: an act carrying the identifier of the
violation it commits, if any, or the remedy of one identified violation. -/
inductive Step2 (V Act : Type*)
  | act (a : Act) (viol : Option V)
  | remedy (v : V)
  deriving DecidableEq

/-- Taint as a set of (violation, component) pairs. -/
abbrev Taint (V Comp : Type*) := Finset (V × Comp)

/-- The violations whose taint the act reads. -/
def readTaint (I : IO Comp Act) (T : Taint V Comp) (a : Act) : Finset V :=
  (T.filter (fun p => p.2 ∈ I.reads a)).image Prod.fst

/-- **The tracking rule, per violation.**  A violating act taints its writes with its own
identifier; an act reading components tainted by some violations taints its writes with
all of them (taint joins at reads); the remedy of `v` clears `v`'s taint only. -/
def taintStep2 (I : IO Comp Act) (T : Taint V Comp) : Step2 V Act → Taint V Comp
  | .act a viol => T ∪ (readTaint I T a ∪ viol.toFinset) ×ˢ I.writes a
  | .remedy v => T.filter (fun p => p.1 ≠ v)

def taintAfter2 (I : IO Comp Act) (steps : List (Step2 V Act)) : Taint V Comp :=
  steps.foldl (taintStep2 I) ∅

/-- The violations standing on a component. -/
def taintedBy (T : Taint V Comp) (c : Comp) : Finset V :=
  (T.filter (fun p => p.2 = c)).image Prod.fst

/-- Use: reading a component tainted by some unremedied violation.  Decidable. -/
def uses2 (I : IO Comp Act) (T : Taint V Comp) (a : Act) : Bool :=
  decide (readTaint I T a).Nonempty

theorem mem_readTaint (I : IO Comp Act) (T : Taint V Comp) (a : Act) (v : V) :
    v ∈ readTaint I T a ↔ ∃ c ∈ I.reads a, (v, c) ∈ T := by
  simp only [readTaint, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hr⟩, rfl⟩; exact ⟨p.2, hr, hp⟩
  · rintro ⟨c, hr, hc⟩; exact ⟨(v, c), ⟨hc, hr⟩, rfl⟩

theorem mem_taintStep2_act (I : IO Comp Act) (T : Taint V Comp) (a : Act) (viol : Option V)
    (v : V) (d : Comp) :
    (v, d) ∈ taintStep2 I T (.act a viol)
      ↔ (v, d) ∈ T ∨ ((v ∈ readTaint I T a ∨ viol = some v) ∧ d ∈ I.writes a) := by
  simp only [taintStep2, Finset.mem_union, Finset.mem_product, Option.mem_toFinset, Option.mem_def]

theorem mem_taintStep_act (I : IO Comp Act) (S : Finset Comp) (a : Act) (b : Bool) (c : Comp) :
    c ∈ taintStep I S (.act a b)
      ↔ c ∈ S ∨ ((b = true ∨ (I.reads a ∩ S).Nonempty) ∧ c ∈ I.writes a) := by
  simp only [taintStep]
  split_ifs with h
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    simp [h]
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h
    simp [h.1, h.2]

/-- A violating act taints its writes with its own identifier. -/
theorem commission_taints (I : IO Comp Act) (T : Taint V Comp) (a : Act) (v : V) (d : Comp)
    (hd : d ∈ I.writes a) : (v, d) ∈ taintStep2 I T (.act a (some v)) := by
  rw [mem_taintStep2_act]
  exact Or.inr ⟨Or.inr rfl, hd⟩

/-- **`taint_propagates`, re-proved.**  An act reading a component tainted by `v` taints its
writes with `v`, whatever else it commits.  Old-to-new: the old lemma is the case of one
identifier, with the whole write set joined. -/
theorem taint_propagates2 (I : IO Comp Act) (T : Taint V Comp) (a : Act) (v : V) (c : Comp)
    (hc : (v, c) ∈ T) (hr : c ∈ I.reads a) (d : Comp) (hd : d ∈ I.writes a) (viol : Option V) :
    (v, d) ∈ taintStep2 I T (.act a viol) := by
  rw [mem_taintStep2_act]
  exact Or.inr ⟨Or.inl ((mem_readTaint I T a v).mpr ⟨c, hr, hc⟩), hd⟩

/-- Taint joins at reads: every violation read stands on every component written. -/
theorem taint_joins (I : IO Comp Act) (T : Taint V Comp) (a : Act) (d : Comp)
    (hd : d ∈ I.writes a) (viol : Option V) :
    readTaint I T a ⊆ taintedBy (taintStep2 I T (.act a viol)) d := by
  intro v hv
  simp only [taintedBy, Finset.mem_image, Finset.mem_filter]
  refine ⟨(v, d), ⟨?_, rfl⟩, rfl⟩
  rw [mem_taintStep2_act]
  exact Or.inr ⟨Or.inl hv, hd⟩

/-- **`remedy_clears`, re-proved per violation.**  The remedy of `v` clears `v`'s taint. -/
theorem remedy_clears2 (I : IO Comp Act) (T : Taint V Comp) (v : V) (c : Comp) :
    (v, c) ∉ taintStep2 I T (.remedy v) := by
  simp [taintStep2]

/-- The remedy of `v` leaves every other violation's taint exactly as it was. -/
theorem remedy_keeps_others (I : IO Comp Act) (T : Taint V Comp) (v v' : V) (hne : v' ≠ v)
    (c : Comp) : (v', c) ∈ taintStep2 I T (.remedy v) ↔ (v', c) ∈ T := by
  simp [taintStep2, hne]

/-- On a component the remedy of `v` erases `v` from the standing violations and nothing else. -/
theorem taintedBy_remedy (I : IO Comp Act) (T : Taint V Comp) (v : V) (c : Comp) :
    taintedBy (taintStep2 I T (.remedy v)) c = (taintedBy T c).erase v := by
  ext v'
  simp only [taintedBy, taintStep2, Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨p, ⟨⟨hp, hne⟩, hc⟩, rfl⟩
    exact ⟨hne, p, ⟨hp, hc⟩, rfl⟩
  · rintro ⟨hne, p, ⟨hp, hc⟩, rfl⟩
    exact ⟨p, ⟨⟨hp, hne⟩, hc⟩, rfl⟩

/-- A component tainted by two violations stays tainted after one of them is remedied. -/
theorem still_tainted_after_one_remedy (I : IO Comp Act) (T : Taint V Comp) (v v' : V)
    (hne : v' ≠ v) (c : Comp) (hv' : (v', c) ∈ T) :
    (taintedBy (taintStep2 I T (.remedy v)) c).Nonempty := by
  rw [taintedBy_remedy]
  refine ⟨v', Finset.mem_erase.mpr ⟨hne, ?_⟩⟩
  simp only [taintedBy, Finset.mem_image, Finset.mem_filter]
  exact ⟨(v', c), ⟨hv', rfl⟩, rfl⟩

/-- **The old-to-new map.**  With every violation given the same identifier, the new act
step projects onto the old one: the old rule *is* the new rule with one identifier, and
what it lost was the identity of the violation a remedy addresses. -/
theorem old_is_new_with_one_identifier (I : IO Comp Act) (T : Taint Unit Comp) (a : Act)
    (viol : Option Unit) :
    (taintStep2 I T (.act a viol)).image Prod.snd
      = taintStep I (T.image Prod.snd) (.act a viol.isSome) := by
  ext c
  simp only [mem_taintStep_act, Finset.mem_image, Prod.exists, mem_taintStep2_act, mem_readTaint,
    Unique.exists_iff, exists_eq_right, Option.isSome_iff_exists, Finset.Nonempty,
    Finset.mem_inter]
  constructor
  · rintro (h | ⟨h1 | h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inr h1, h2⟩
    · exact Or.inr ⟨Or.inl h1, h2⟩
  · rintro (h | ⟨h1 | h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inr h1, h2⟩
    · exact Or.inr ⟨Or.inl h1, h2⟩

/-- Use is the same predicate under both rules, on the projected taint. -/
theorem uses_old_eq_new (I : IO Comp Act) (T : Taint Unit Comp) (a : Act) :
    uses2 I T a = uses I (T.image Prod.snd) a := by
  simp only [uses2, uses]
  apply decide_eq_decide.mpr
  simp only [Finset.Nonempty, mem_readTaint, Finset.mem_inter, Finset.mem_image, Prod.exists,
    Unique.exists_iff, exists_eq_right]

/-- **`knowledge_residual`, re-proved.**  A violation writing outside the tracked components
leaves no taint under the per-violation rule either: the point of contact with §9.A.4,
which this follow-up does not pursue. -/
theorem knowledge_residual2 (I : IO Comp Act) (a : Act) (v : V) (hw : I.writes a = ∅) :
    taintAfter2 I [.act a (some v)] = (∅ : Taint V Comp) := by
  simp [taintAfter2, taintStep2, hw]

/-- **`observation_taints_all`, re-proved.**  With the observation channel a tracked
component written by the violation, every later act reading it uses `v`'s taint until
`v` is remedied. -/
theorem observation_taints_all2 (I : IO Comp Act) (obs : Comp) (v : V) (va : Act)
    (hv : obs ∈ I.writes va) (later : Act) (hr : obs ∈ I.reads later) :
    uses2 I (taintAfter2 I [.act va (some v)]) later = true := by
  simp only [uses2, decide_eq_true_eq]
  refine ⟨v, ?_⟩
  simp only [readTaint, Finset.mem_image, Finset.mem_filter]
  refine ⟨(v, obs), ⟨?_, hr⟩, rfl⟩
  simp only [taintAfter2, List.foldl]
  exact commission_taints I ∅ va v obs hv

end PerViolation

/-! ## 2. Convention (ii), and the window before detection -/

section ConventionII

variable (P : LexParams)

/-- **The price term cancels.**  The winner's loss against its bid under (ii) is its
evaluation, plus the recognized count, less the realized residual *without* the prices:
the prices in the evaluation cancel the prices added back at settlement. -/
theorem price_cancels (bid gord pS pT : ℝ) (nK nF nL : ℕ) :
    bid - P.residII gord nF nL pS pT
      = P.evalOf bid nK pS pT + P.ϖ * nK - (gord - P.ϖ * nL - P.ϖ * nF) := by
  unfold LexParams.residII LexParams.evalOf; ring

/-- At zero prices (ii) is (i). -/
theorem residII_zero_price (gord : ℝ) (nLate : ℕ) :
    P.residII gord 0 nLate 0 0 = P.residI gord nLate := by
  unfold LexParams.residII LexParams.residI; simp

theorem evalOf_zero_price (bid : ℝ) : P.evalOf bid 0 0 0 = bid := by
  unfold LexParams.evalOf; simp

/-- **`standing_block_loss`, restated under (ii).**  A block whose winning continuation
evaluated at or above the window and carries a counted violation — recognized in advance,
forecast-class, or counted after the fact — loses at least `ℓ = ϖ − D + w` against its
bid, with nonzero prices. -/
theorem standing_block_loss_ii (bid : ℝ) (nKnown : ℕ) (pS pT : ℝ)
    (hwin : P.w ≤ P.evalOf bid nKnown pS pT) (gord : ℝ) (hg : gord ≤ P.D) (nFore nLate : ℕ)
    (hn : 1 ≤ nKnown + nFore + nLate) :
    P.ϖ - P.D + P.w ≤ bid - P.residII gord nFore nLate pS pT := by
  unfold LexParams.evalOf at hwin
  unfold LexParams.residII
  have h1 : (1 : ℝ) ≤ nKnown + nFore + nLate := by exact_mod_cast hn
  have hϖ := P.ϖ_pos
  nlinarith [mul_le_mul_of_nonneg_left h1 hϖ.le]

/-- The `residI` form is the zero-price special case. -/
theorem standing_block_loss_of_ii (gord : ℝ) (hg : gord ≤ P.D) (nUse : ℕ) (hn : 1 ≤ nUse)
    (bid : ℝ) (hb : P.w ≤ bid) : P.ϖ - P.D + P.w ≤ bid - P.residI gord nUse := by
  rw [← residII_zero_price]
  exact standing_block_loss_ii P bid 0 0 0 (by rw [evalOf_zero_price]; exact hb) gord hg 0 nUse
    (by omega)

/-- **`cross_block_blocked`, restated under (ii).**  Over the commission block and `m`
blocks of use, each won at an evaluation at or above the window, the net record is at
most `−(m + 1) · ℓ < 0`. -/
theorem cross_block_blocked_ii (m : ℕ) (bids gords pS pT : ℕ → ℝ) (nK nF nL : ℕ → ℕ)
    (hwin : ∀ j, P.w ≤ P.evalOf (bids j) (nK j) (pS j) (pT j)) (hg : ∀ j, gords j ≤ P.D)
    (hn : ∀ j, 1 ≤ nK j + nF j + nL j) :
    ∑ j ∈ range (m + 1), (P.residII (gords j) (nF j) (nL j) (pS j) (pT j) - bids j)
      ≤ -((m + 1 : ℕ) * (P.ϖ - P.D + P.w)) ∧
    -((m + 1 : ℕ) * (P.ϖ - P.D + P.w)) < 0 := by
  have hℓ := P.incident_loss_pos
  refine ⟨?_, ?_⟩
  · calc ∑ j ∈ range (m + 1), (P.residII (gords j) (nF j) (nL j) (pS j) (pT j) - bids j)
        ≤ ∑ _j ∈ range (m + 1), -(P.ϖ - P.D + P.w) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := standing_block_loss_ii P (bids j) (nK j) (pS j) (pT j) (hwin j) (gords j)
            (hg j) (nF j) (nL j) (hn j)
          linarith
      _ = -((m + 1 : ℕ) * (P.ϖ - P.D + P.w)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  · have : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    nlinarith

end ConventionII

section AfterDetection

variable {V Comp Q : Type*} [DecidableEq V] [DecidableEq Comp]

/-- **Use compiles into `n_known`.**  With the taint on record, the menu's structural count
of an option is its base count plus one if the option reads a tainted component. -/
def nKnownWith (I : IO Comp Q) (T : Taint V Comp) (base : Q → ℕ) (a : Q) : ℕ :=
  base a + if uses2 I T a then 1 else 0

theorem use_is_known (I : IO Comp Q) (T : Taint V Comp) (base : Q → ℕ) (a : Q)
    (h : uses2 I T a = true) : 1 ≤ nKnownWith I T base a := by
  simp [nKnownWith, h]

/-- **After detection the fruits are never used.**  Once the taint is on record, an option
reading a tainted component carries a structurally recognized violation, evaluates below
inquiry by ranges alone (`declared_loses`), and is never the maximizer (`filter_slack`):
B.1 excludes every use block outright. -/
theorem after_detection_never_used (P : LexParams) (I : IO Comp Q) (T : Taint V Comp)
    (base : Q → ℕ) (bid pS pT : Q → ℝ) (hb : ∀ a, bid a ≤ P.D) (hp : ∀ a, 0 ≤ pS a + pT a)
    (inq : Q) (hI : P.w ≤ bid inq) (hIk : nKnownWith I T base inq = 0)
    (hIp : pS inq = 0 ∧ pT inq = 0) (a : Q)
    (hmax : ∀ a', P.evalOf (bid a') (nKnownWith I T base a') (pS a') (pT a')
      ≤ P.evalOf (bid a) (nKnownWith I T base a) (pS a) (pT a)) :
    uses2 I T a = false := by
  refine LexParams.filter_slack (fun a => uses2 I T a)
    (fun a => P.evalOf (bid a) (nKnownWith I T base a) (pS a) (pT a)) inq ?_ a hmax
  intro a' ha'
  show P.evalOf (bid a') (nKnownWith I T base a') (pS a') (pT a')
    < P.evalOf (bid inq) (nKnownWith I T base inq) (pS inq) (pT inq)
  rw [hIk, hIp.1, hIp.2]
  exact P.declared_loses (bid a') (hb a') _ (use_is_known I T base a' ha') (pS a') (pT a')
    (hp a') (bid inq) hI

end AfterDetection

section Window

variable {V Comp Act : Type*} [DecidableEq V] [DecidableEq Comp]

/-- **Detection.**  The record carries the commission step unflagged until detection;
detecting `v` at position `k₀` flags that step, and the taint is recomputed over the
recorded steps from `k₀` on. -/
def detectAt : List (Step2 V Act) → ℕ → V → List (Step2 V Act)
  | [], _, _ => []
  | (.act a _) :: rest, 0, v => .act a (some v) :: rest
  | s :: rest, 0, _ => s :: rest
  | s :: rest, k + 1, v => s :: detectAt rest k v

/-- **Taint comes only from commission.**  If no recorded step commits `v`, no component
carries `v`'s taint — before detection nothing is charged to `v`, and a violation never
detected charges nothing ever. -/
theorem taint_only_from_commission (I : IO Comp Act) (v : V) :
    ∀ (steps : List (Step2 V Act)) (T : Taint V Comp), (∀ c, (v, c) ∉ T) →
      (∀ a, Step2.act a (some v) ∉ steps) → ∀ c, (v, c) ∉ steps.foldl (taintStep2 I) T := by
  intro steps
  induction steps with
  | nil => intro T hT _ c; simpa using hT c
  | cons s rest ih =>
    intro T hT hs c
    simp only [List.foldl_cons]
    apply ih
    · intro c'
      cases s with
      | act a viol =>
        simp only [taintStep2, Finset.mem_union, Finset.mem_product, not_or, not_and]
        refine ⟨hT c', fun hv _ => ?_⟩
        simp only [readTaint, Finset.mem_image, Finset.mem_filter] at hv
        rcases hv with ⟨p, ⟨hp, _⟩, hpv⟩ | hv
        · exact hT p.2 (by rw [← hpv]; exact hp)
        · have : viol = some v := by
            cases viol with
            | none => simp at hv
            | some w => simp at hv; rw [hv]
          exact hs a (by rw [this]; simp)
      | remedy w =>
        simp only [taintStep2, Finset.mem_filter, not_and]
        intro h; exact absurd h (hT c')
    · intro a ha; exact hs a (List.mem_cons_of_mem _ ha)

/-- Taint persists until its own violation's remedy. -/
theorem taint_persists_without_remedy (I : IO Comp Act) (v : V) (c : Comp) :
    ∀ (steps : List (Step2 V Act)) (T : Taint V Comp), (v, c) ∈ T →
      Step2.remedy (Act := Act) v ∉ steps → (v, c) ∈ steps.foldl (taintStep2 I) T := by
  intro steps
  induction steps with
  | nil => intro T hT _; simpa using hT
  | cons s rest ih =>
    intro T hT hs
    simp only [List.foldl_cons]
    apply ih
    · cases s with
      | act a viol => exact Finset.mem_union_left _ hT
      | remedy w =>
        have hne : v ≠ w := fun h => hs (by rw [h]; simp)
        exact Finset.mem_filter.mpr ⟨hT, hne⟩
    · intro h; exact hs (List.mem_cons_of_mem _ h)

/-- **The count-integrity boundary.**  A violation never detected is a record in which no
step commits it: its fruits carry no taint and no block is charged for them.  This is
undetected *commission*, a different residual from the untrackable *fruit* of §9.A.4. -/
theorem never_detected_never_charged (I : IO Comp Act) (v : V) (steps : List (Step2 V Act))
    (hs : ∀ a, Step2.act a (some v) ∉ steps) (later : Act) :
    ∀ c ∈ I.reads later, v ∉ taintedBy (taintAfter2 I steps) c := by
  intro c _ hv
  simp only [taintedBy, Finset.mem_image, Finset.mem_filter] at hv
  obtain ⟨p, ⟨hp, hc⟩, hpv⟩ := hv
  have := taint_only_from_commission I v steps ∅ (by simp) hs c
  apply this
  rw [← hpv, ← hc]
  exact hp

end Window

section LateDebit

variable (P : LexParams)

/-- **Late debit equals late settlement.**  A block settled with the use uncounted and then
debited `ϖ` is the block settled with the use counted. -/
theorem late_debit_eq_late_settlement (gord pS pT : ℝ) (nF nL : ℕ) :
    P.residII gord nF nL pS pT - P.ϖ = P.residII gord nF (nL + 1) pS pT := by
  unfold LexParams.residII; push_cast; ring

/-- **A window block is charged.**  A block in the window before detection — won at an
evaluation at or above the window with the taint not on record, settled without the use
counted — loses at least `ℓ` against its bid once debited `ϖ` at detection. -/
theorem window_block_charged (bid : ℝ) (nK : ℕ) (pS pT : ℝ)
    (hwin : P.w ≤ P.evalOf bid nK pS pT) (gord : ℝ) (hg : gord ≤ P.D) (nF nL : ℕ) :
    P.ϖ - P.D + P.w ≤ bid - (P.residII gord nF nL pS pT - P.ϖ) := by
  rw [late_debit_eq_late_settlement]
  exact standing_block_loss_ii P bid nK pS pT hwin gord hg nF (nL + 1) (by omega)

/-- **The greedy debit schedule**: at each block take what the allowance offers, up to
what is still outstanding of the charge `C`. -/
noncomputable def greedyDebit (A : ℕ → ℝ) (C : ℝ) (j : ℕ) : ℝ :=
  min (A j) (max 0 (C - ∑ i ∈ range j, A i))

/-- What the greedy schedule collects by `K` is the charge or the cumulative allowance,
whichever is smaller. -/
theorem greedy_collects (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (C : ℝ) (hC : 0 ≤ C) (K : ℕ) :
    ∑ j ∈ range K, greedyDebit A C j = min C (∑ j ∈ range K, A j) := by
  induction K with
  | zero => simp [min_eq_right hC]
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    unfold greedyDebit
    have hAK := hA K
    rcases le_or_gt C (∑ j ∈ range K, A j) with h | h
    · rw [max_eq_left (by linarith), min_eq_right hAK, min_eq_left h, min_eq_left (by linarith),
        add_zero]
    · rw [max_eq_right (by linarith), min_eq_right h.le]
      rcases le_or_gt (A K) (C - ∑ j ∈ range K, A j) with h2 | h2
      · rw [min_eq_left h2, min_eq_right (by linarith)]
      · rw [min_eq_right h2.le, min_eq_left (by linarith)]; ring

/-- **The carry-over condition** (B.4's form): the charge is collected by `K` iff the
hypothesis's cumulative allowance through `K` covers it. -/
theorem collected_iff (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (C : ℝ) (hC : 0 ≤ C) (K : ℕ) :
    ∑ j ∈ range K, greedyDebit A C j = C ↔ C ≤ ∑ j ∈ range K, A j := by
  rw [greedy_collects A hA C hC]
  constructor
  · intro h; rw [← h]; exact min_le_right _ _
  · intro h; exact min_eq_left h

/-- What is not collected by `K` is the excess of the charge over the allowance. -/
theorem uncollected_eq (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (C : ℝ) (hC : 0 ≤ C) (K : ℕ) :
    C - ∑ j ∈ range K, greedyDebit A C j = max 0 (C - ∑ j ∈ range K, A j) := by
  rw [greedy_collects A hA C hC]
  rcases le_or_gt C (∑ j ∈ range K, A j) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h.le, max_eq_right (by linarith)]

/-- The debit schedule of a window charge `C` against the hypothesis `i₀` that won the
block, as a schedule on the auction's allowance. -/
noncomputable def windowDebit {n : ℕ} (a : Auction n) (i₀ : Fin n) (C : ℝ) (k : ℕ) (i : Fin n) :
    ℝ :=
  if i = i₀ then greedyDebit (fun j => a.A j i₀) C k else 0

/-- It is a debit schedule in the sense of `debited`: nonnegative and within the allowance. -/
theorem windowDebit_bounds {n : ℕ} (a : Auction n) (i₀ : Fin n) (C : ℝ) :
    ∀ k i, 0 ≤ windowDebit a i₀ C k i ∧ windowDebit a i₀ C k i ≤ a.A k i := by
  intro k i
  unfold windowDebit greedyDebit
  split_ifs with hi
  · subst hi
    exact ⟨le_min (a.A_nonneg k i) (le_max_left _ _), min_le_left _ _⟩
  · exact ⟨le_rfl, a.A_nonneg k i⟩

/-- **The exposure of the window.**  Over `m` window blocks, before the debit, the net gain
is at most `m` times the per-block advantage bound `R`; after the debit, the net is at most
`−m · ℓ` plus the uncollected part of the charges — only uncollected debits escape. -/
theorem window_exposure (m : ℕ) (gain charge col : ℕ → ℝ) (R ℓ : ℝ)
    (hR : ∀ j, gain j ≤ R) (hcharged : ∀ j, gain j - charge j ≤ -ℓ) :
    ∑ j ∈ range m, gain j ≤ m * R ∧
    ∑ j ∈ range m, (gain j - col j) ≤ -(m * ℓ) + ∑ j ∈ range m, (charge j - col j) := by
  constructor
  · calc ∑ j ∈ range m, gain j ≤ ∑ _j ∈ range m, R := Finset.sum_le_sum fun j _ => hR j
      _ = m * R := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · have : ∑ j ∈ range m, (gain j - col j)
        = ∑ j ∈ range m, (gain j - charge j) + ∑ j ∈ range m, (charge j - col j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    have h : ∑ j ∈ range m, (gain j - charge j) ≤ -(m * ℓ) := by
      calc ∑ j ∈ range m, (gain j - charge j) ≤ ∑ _j ∈ range m, -ℓ :=
            Finset.sum_le_sum fun j _ => hcharged j
        _ = -(m * ℓ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    linarith

end LateDebit

/-! ## 3. Part F: the real criterion -/

section PartF

/-- Expected locked capital under a random evaluation time `T ~ α`: `E[bid · 1[T > t]]`. -/
noncomputable def randomLocked {T : ℕ} (Wt : Weighting T) (bid : ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ range T, Wt.α s * (if t < s then bid else 0)

/-- Locked capital under the mixture settled in pieces: the bid less the shares released
at evaluation times up to `t`. -/
noncomputable def mixtureLocked {T : ℕ} (Wt : Weighting T) (bid : ℝ) (t : ℕ) : ℝ :=
  bid - ∑ s ∈ (range T).filter (fun s => s ≤ t), Wt.α s * bid

/-- **Expected escrow is the same.**  With `α = ρ_n`, the random time's expected locked
capital at every `t` equals the mixture's remaining weight times the bid. -/
theorem expected_escrow_eq {T : ℕ} (Wt : Weighting T) (bid : ℝ) (t : ℕ) :
    randomLocked Wt bid t = mixtureLocked Wt bid t := by
  unfold randomLocked mixtureLocked
  rw [Finset.sum_filter]
  have : ∑ s ∈ range T, Wt.α s * (if t < s then bid else 0)
      + ∑ s ∈ range T, (if s ≤ t then Wt.α s * bid else 0) = bid := by
    rw [← Finset.sum_add_distrib]
    calc _ = ∑ s ∈ range T, Wt.α s * bid :=
          Finset.sum_congr rfl fun s _ => by
            split_ifs with h1 h2 <;> first | (exfalso; omega) | ring
      _ = bid := by rw [← Finset.sum_mul, Wt.sum_one, one_mul]
  linarith

/-- Both are the tail weight beyond `t` times the bid. -/
theorem locked_eq_tail {T : ℕ} (Wt : Weighting T) (bid : ℝ) (t : ℕ) :
    randomLocked Wt bid t = bid * tailWeight Wt (t + 1) := by
  unfold randomLocked tailWeight
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with h1 h2 <;> first | (exfalso; omega) | ring

/-- **The load of option 2, truncated.**  Evaluating only at times before `s` costs at most
the tail weight from `s` times the value bound (`partial_settlement` at `S = range s`). -/
theorem truncation_cost {T : ℕ} (Wt : Weighting T) (U : ℕ → ℝ) (Mb : ℝ)
    (hU : ∀ t, |U t| ≤ Mb) (s : ℕ) :
    |mixScore Wt U - ∑ t ∈ (range T).filter (fun t => t < s), Wt.α t * U t|
      ≤ Mb * tailWeight Wt s := by
  have h := partial_settlement Wt U Mb hU (range s)
  have h1 : (range T).filter (fun t => t ∈ range s) = (range T).filter (fun t => t < s) :=
    Finset.filter_congr fun t _ => by simp
  have h2 : (range T).filter (fun t => t ∉ range s) = (range T).filter (fun t => s ≤ t) :=
    Finset.filter_congr fun t _ => by simp
  rw [h1, h2] at h
  exact h

/-- An expectation operator: linear and normalized.  Independence of the `k` draws enters
the statements below as uncorrelatedness, a hypothesis on `E`. -/
structure Expect (Ω : Type*) where
  E : (Ω → ℝ) → ℝ
  add : ∀ f g, E (fun ω => f ω + g ω) = E f + E g
  smul : ∀ (c : ℝ) f, E (fun ω => c * f ω) = c * E f
  const : ∀ c : ℝ, E (fun _ => c) = c

namespace Expect

variable {Ω : Type*} (X : Expect Ω)

theorem sum (s : Finset ℕ) (f : ℕ → Ω → ℝ) :
    X.E (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, X.E (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [X.const]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [X.add, ih]

theorem sub (f g : Ω → ℝ) : X.E (fun ω => f ω - g ω) = X.E f - X.E g := by
  have := X.add f (fun ω => (-1) * g ω)
  rw [X.smul] at this
  simp only [neg_one_mul] at this
  rw [← sub_eq_add_neg] at this
  simpa [sub_eq_add_neg] using this

end Expect

/-- **Option 4, the harm weight.**  The average of `k` draws has the same expectation as
one draw: the same weight `P(T ≥ n + d)` on a delayed harm for every `k`. -/
theorem average_mean {Ω : Type*} (X : Expect Ω) (k : ℕ) (hk : 0 < k) (Xs : ℕ → Ω → ℝ) (μ : ℝ)
    (hmean : ∀ i, i < k → X.E (Xs i) = μ) :
    X.E (fun ω => (∑ i ∈ range k, Xs i ω) / k) = μ := by
  have : (fun ω => (∑ i ∈ range k, Xs i ω) / k) = fun ω => (1 / k) * ∑ i ∈ range k, Xs i ω := by
    funext ω; ring
  rw [this, X.smul, X.sum]
  rw [Finset.sum_congr rfl fun i hi => hmean i (Finset.mem_range.mp hi)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- **Option 4, the variance.**  `k` draws with common mean `μ`, common second moment
`μ² + σ²`, pairwise uncorrelated: the average's mean-square deviation is `σ²/k`. -/
theorem average_variance {Ω : Type*} (X : Expect Ω) (k : ℕ) (hk : 0 < k) (Xs : ℕ → Ω → ℝ)
    (μ σ2 : ℝ) (hmean : ∀ i, i < k → X.E (Xs i) = μ)
    (hsecond : ∀ i, i < k → X.E (fun ω => Xs i ω * Xs i ω) = μ ^ 2 + σ2)
    (hunc : ∀ i j, i < k → j < k → i ≠ j → X.E (fun ω => Xs i ω * Xs j ω) = μ ^ 2) :
    X.E (fun ω => ((∑ i ∈ range k, Xs i ω) / k - μ) ^ 2) = σ2 / k := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hfun : (fun ω => ((∑ i ∈ range k, Xs i ω) / k - μ) ^ 2)
      = fun ω => (1 / (k : ℝ) ^ 2) * (∑ i ∈ range k, ∑ j ∈ range k, Xs i ω * Xs j ω)
          + ((-2 * μ / k) * ∑ i ∈ range k, Xs i ω + μ ^ 2) := by
    funext ω
    rw [← Finset.sum_mul_sum]
    field_simp
    ring
  rw [hfun, X.add, X.smul, X.add, X.smul, X.const, X.sum, X.sum]
  have hinner : ∀ i ∈ range k, ∑ j ∈ range k, X.E (fun ω => Xs i ω * Xs j ω) = k * μ ^ 2 + σ2 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have : ∀ j ∈ range k, X.E (fun ω => Xs i ω * Xs j ω) = μ ^ 2 + if j = i then σ2 else 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      by_cases h : j = i
      · subst h; rw [hsecond j hj']; simp
      · rw [hunc i j hi' hj' (Ne.symm h)]; simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq' (range k) i]
    rw [if_pos hi, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun i hi => (X.sum (range k) (fun j ω => Xs i ω * Xs j ω)).trans
    (hinner i hi)]
  rw [Finset.sum_congr rfl fun i hi => hmean i (Finset.mem_range.mp hi)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- The variance falls with `k`: at `k = 1` it is `σ²` (option 3); at `k` it is `σ²/k`. -/
theorem variance_falls (σ2 : ℝ) (hσ : 0 ≤ σ2) (k : ℕ) (hk : 1 ≤ k) :
    σ2 / k ≤ σ2 / 1 ∧ σ2 / (k : ℝ) = σ2 * (1 / k) := by
  constructor
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_le_div_of_nonneg_left hσ one_pos hk'
  · ring

/-- The escrow indicator `bid · 1[T > t]` is Bernoulli: mean `bid · p`, variance
`bid² p (1 − p)` — positive under a hidden draw, zero for the mixture. -/
theorem bernoulli_variance (bid p : ℝ) :
    (bid ^ 2 * p) - (bid * p) ^ 2 = bid ^ 2 * p * (1 - p) := by ring

end PartF

/-! ## 4. Competitiveness from one honest tracker -/

section HonestTracker

variable {n : ℕ} (a : Auction n)

/-- **The auction rule.**  The winner's bid is the highest among the bids feasible at
opening capital on the winning continuation: on one continuation evaluation is monotone
in the bid, so a feasible bid above the winner's would have won. -/
def HighestFeasible (e : ℕ → Fin n → ℝ) : Prop :=
  ∀ k i, a.w k * e k i ≤ a.B k i → e k i ≤ a.b k

/-- The winner's bid is its own. -/
def WinnerBids (e : ℕ → Fin n → ℝ) : Prop := ∀ k, a.b k = e k (a.star k)

/-- **The honest tracker**: a hypothesis whose bid on the winning continuation is within
`ε_k` of its realized residual at every block. -/
def Honest (e : ℕ → Fin n → ℝ) (h : Fin n) (ε : ℕ → ℝ) : Prop := ∀ k, |e k h - a.G k| ≤ ε k

/-- Where the tracker's bid is feasible, the winner underpromises by at most `ε_k`: an
underpromising winner is outbid by the tracker. -/
theorem underpromise_le_of_feasible (e : ℕ → Fin n → ℝ) (h : Fin n) (ε : ℕ → ℝ)
    (hH : HighestFeasible a e) (hon : Honest a e h ε) (k : ℕ) (hf : a.w k * e k h ≤ a.B k h) :
    a.G k - a.b k ≤ ε k := by
  have h1 := hH k h hf
  have h2 := (abs_le.mp (hon k)).1
  linarith

/-- **The tracker's wealth**: its allowance less its honest losses, since each win pays it
at least `−w_k ε_k`. -/
theorem tracker_wealth_ge (e : ℕ → Fin n → ℝ) (h : Fin n) (ε : ℕ → ℝ) (hW : WinnerBids a e)
    (hon : Honest a e h ε) (hε : ∀ k, 0 ≤ ε k) (k : ℕ) :
    ∑ j ∈ range k, a.A j h - ∑ j ∈ range k, a.w j * ε j ≤ a.W k h := by
  rw [a.wealth_eq h k]
  unfold Auction.allowanceOf Auction.chargedRecord
  have : -(∑ j ∈ range k, a.w j * ε j)
      ≤ ∑ j ∈ range k, (if h = a.star j then a.w j * (a.G j - a.b j) else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hw := a.w_pos j
    split_ifs with hj
    · rw [hW j, ← hj]
      have := (abs_le.mp (hon j)).2
      nlinarith
    · nlinarith [hε j]
  linarith

/-- **Feasibility from the allowance.**  Cumulative allowance through `k` covering the
current bid plus the honest losses so far makes the tracker feasible at `k`. -/
theorem tracker_feasible (e : ℕ → Fin n → ℝ) (h : Fin n) (ε : ℕ → ℝ) (hW : WinnerBids a e)
    (hon : Honest a e h ε) (hε : ∀ k, 0 ≤ ε k) (k : ℕ)
    (hcov : a.w k * e k h + ∑ j ∈ range k, a.w j * ε j ≤ ∑ j ∈ range (k + 1), a.A j h) :
    a.w k * e k h ≤ a.B k h := by
  have := tracker_wealth_ge a e h ε hW hon hε k
  unfold Auction.B
  rw [Finset.sum_range_succ] at hcov
  linarith

/-- **Competitiveness from one honest tracker.**  The winners' signed margin over any set of
blocks is at most `Σ w_k ε_k` plus `R` times the weight of the blocks where the tracker is
capital-bound, `R` bounding the per-block underpromise. -/
theorem competitive_of_honest_tracker (e : ℕ → Fin n → ℝ) (h : Fin n) (ε : ℕ → ℝ)
    (hH : HighestFeasible a e) (hon : Honest a e h ε) (hε : ∀ k, 0 ≤ ε k) (inc : ℕ → Bool)
    (R : ℝ) (hR0 : 0 ≤ R) (feas : ℕ → Bool) (hR : ∀ k, ¬ feas k = true → a.G k - a.b k ≤ R)
    (hfeas : ∀ k, feas k = true → a.w k * e k h ≤ a.B k h) :
    Competitive a inc (fun K => ∑ k ∈ range K, a.w k * ε k
      + R * ∑ k ∈ (range K).filter (fun k => ¬ feas k = true), a.w k) := by
  intro K
  have hterm : ∀ k, a.w k * (a.G k - a.b k)
      ≤ a.w k * ε k + (if feas k = true then 0 else R * a.w k) := by
    intro k
    have hw := a.w_pos k
    split_ifs with hf
    · have := underpromise_le_of_feasible a e h ε hH hon k (hfeas k hf)
      nlinarith
    · have := hR k hf
      have := hε k
      nlinarith
  have hnn : ∀ k, 0 ≤ a.w k * ε k + (if feas k = true then 0 else R * a.w k) := by
    intro k
    have hw := a.w_pos k
    split_ifs <;> nlinarith [hε k]
  calc ∑ k ∈ (range K).filter (fun k => ¬ inc k = true), a.w k * (a.G k - a.b k)
      ≤ ∑ k ∈ (range K).filter (fun k => ¬ inc k = true),
          (a.w k * ε k + (if feas k = true then 0 else R * a.w k)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ ≤ ∑ k ∈ range K, (a.w k * ε k + (if feas k = true then 0 else R * a.w k)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => hnn k
    _ = ∑ k ∈ range K, a.w k * ε k
          + R * ∑ k ∈ (range K).filter (fun k => ¬ feas k = true), a.w k := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp

/-- **Under the allowance condition** the tracker is feasible at every block and the
margin is `Σ w_k ε_k`: competitiveness holds with `Mf K = Σ_{k<K} w_k ε_k`, which is
`o(K)` when `Σ ε_k = o(K)` and the weights are bounded. -/
theorem competitive_of_affordable_tracker (e : ℕ → Fin n → ℝ) (h : Fin n) (ε : ℕ → ℝ)
    (hH : HighestFeasible a e) (hW : WinnerBids a e) (hon : Honest a e h ε) (hε : ∀ k, 0 ≤ ε k)
    (hcov : ∀ k, a.w k * e k h + ∑ j ∈ range k, a.w j * ε j ≤ ∑ j ∈ range (k + 1), a.A j h)
    (inc : ℕ → Bool) : Competitive a inc (fun K => ∑ k ∈ range K, a.w k * ε k) := by
  intro K
  have := competitive_of_honest_tracker a e h ε hH hon hε inc 0 le_rfl (fun _ => true)
    (fun _ hk => absurd rfl hk) (fun k _ => tracker_feasible a e h ε hW hon hε k (hcov k)) K
  simpa using this

/-- **`rate_le_of_competitive`, with the honest tracker as the hypothesis.**  The incident
rate is at most `(𝒜_K + Σ_{k<K} w_k ε_k)/(ℓ · w_min · K)`. -/
theorem rate_le_of_honest_tracker (hf : a.FeasibleOpening) (inc : ℕ → Bool) (ℓ wmin : ℝ)
    (hw : ∀ k, wmin ≤ a.w k) (hwmin : 0 < wmin) (hℓ : 0 < ℓ)
    (hinc : ∀ k, inc k = true → ℓ ≤ a.b k - a.G k) (e : ℕ → Fin n → ℝ) (h : Fin n) (ε : ℕ → ℝ)
    (hH : HighestFeasible a e) (hW : WinnerBids a e) (hon : Honest a e h ε) (hε : ∀ k, 0 ≤ ε k)
    (hcov : ∀ k, a.w k * e k h + ∑ j ∈ range k, a.w j * ε j ≤ ∑ j ∈ range (k + 1), a.A j h)
    (K : ℕ) (hK : 0 < K) :
    (((range K).filter (fun k => inc k = true)).card : ℝ) / K
      ≤ (a.totalAllowance K + ∑ k ∈ range K, a.w k * ε k) / (ℓ * wmin * K) :=
  rate_le_of_competitive a hf inc ℓ wmin hw hwmin hℓ hinc _
    (competitive_of_affordable_tracker a e h ε hH hW hon hε hcov inc) K hK

/-- **The minimal allowance for the tracker**: a bid's worth `w̄ · D` at entry, then a
stream matching its honest losses `w_{j−1} ε_{j−1}`. -/
noncomputable def trackerAllowance (w : ℕ → ℝ) (wbar D : ℝ) (ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => wbar * D
  | j + 1 => w j * ε j

/-- It covers the tracker's bid at every block when bids are clamped at `D` and weights
bounded by `w̄`. -/
theorem trackerAllowance_covers (w : ℕ → ℝ) (wbar D : ℝ) (ε : ℕ → ℝ) (e : ℕ → ℝ)
    (hw : ∀ k, 0 < w k ∧ w k ≤ wbar) (hD : 0 ≤ D) (he : ∀ k, e k ≤ D) (k : ℕ) :
    w k * e k + ∑ j ∈ range k, w j * ε j ≤ ∑ j ∈ range (k + 1), trackerAllowance w wbar D ε j := by
  have hsum : ∑ j ∈ range (k + 1), trackerAllowance w wbar D ε j
      = wbar * D + ∑ j ∈ range k, w j * ε j := by
    rw [Finset.sum_range_succ']
    simp only [trackerAllowance]
    ring
  rw [hsum]
  have := (hw k).1
  have := (hw k).2
  have := he k
  nlinarith

/-- Its total through `K` is `w̄ · D + Σ_{j<K−1} w_j ε_j`: `o(K)` iff the honest losses are. -/
theorem trackerAllowance_total (w : ℕ → ℝ) (wbar D : ℝ) (ε : ℕ → ℝ) (K : ℕ) :
    ∑ j ∈ range (K + 1), trackerAllowance w wbar D ε j = wbar * D + ∑ j ∈ range K, w j * ε j := by
  rw [Finset.sum_range_succ']
  simp only [trackerAllowance]
  ring

end HonestTracker

/-! ## 4′. The honest tracker under noisy outcomes (`FOLLOWUP3.md`) -/

section NoisyTracker

variable {n : ℕ} (a : Auction n)

/-- **Honesty against the expectation.**  `m_k` is the expected residual of the winning
continuation given the history at opening, taken as data; the tracker's bid is within
`ε_k` of it.  The realized residual is `G_k = m_k + ξ_k`, `ξ` the noise. -/
def HonestExp (e : ℕ → Fin n → ℝ) (h : Fin n) (m ε : ℕ → ℝ) : Prop :=
  ∀ k, |e k h - m k| ≤ ε k

/-- The noise: realized less expected residual. -/
def noise (m : ℕ → ℝ) (k : ℕ) : ℝ := a.G k - m k

/-- **The noise hypothesis, by content.**  For a selection rule `S` computable at opening,
the weighted signed noise sum over the selected blocks is bounded by `M K`.  This is what
Azuma–Hoeffding gives for a martingale-difference noise with bounded increments and
bounded weights — `M K = O(√(K log K))` with high probability, the per-`K` tail derived
below from the pinned Mathlib (`subgaussian_two_sided`, `azuma_selected_tail`); the
selection's computability at opening is what makes `w_k 1[S k] ξ_k` a martingale
difference, and the uniform-in-`K` sure bound is the union bound over `K` with
Borel–Cantelli, both named by content, not derived. -/
def NoiseBounded (m : ℕ → ℝ) (S : ℕ → Bool) (M : ℕ → ℝ) : Prop :=
  ∀ K, |∑ k ∈ (range K).filter (fun k => S k = true), a.w k * noise a m k| ≤ M K

/-- **The old form is the noise-free case**: honesty against the realized residual is
honesty against the expectation with `m = G`. -/
theorem honest_implies_exp (e : ℕ → Fin n → ℝ) (h : Fin n) (ε : ℕ → ℝ) (hon : Honest a e h ε) :
    HonestExp e h a.G ε :=
  hon

/-- With `m = G` the noise is zero and every selection is bounded by `M ≡ 0`. -/
theorem noise_free_bounded (S : ℕ → Bool) : NoiseBounded a a.G S (fun _ => 0) := by
  intro K
  simp [noise]

/-- Where the tracker's bid is feasible, the winner underpromises by at most `ε_k + ξ_k`. -/
theorem underpromise_le_of_feasible_exp (e : ℕ → Fin n → ℝ) (h : Fin n) (m ε : ℕ → ℝ)
    (hH : HighestFeasible a e) (hon : HonestExp e h m ε) (k : ℕ)
    (hf : a.w k * e k h ≤ a.B k h) : a.G k - a.b k ≤ ε k + noise a m k := by
  have h1 := hH k h hf
  have h2 := (abs_le.mp (hon k)).1
  unfold noise
  linarith

/-- **The tracker's wealth under noise**: its allowance less its honest losses, plus its own
signed noise sum over its wins — each win pays it `w_k (G_k − e_k) ≥ w_k (ξ_k − ε_k)`. -/
theorem tracker_wealth_ge_exp (e : ℕ → Fin n → ℝ) (h : Fin n) (m ε : ℕ → ℝ)
    (hW : WinnerBids a e) (hon : HonestExp e h m ε) (hε : ∀ k, 0 ≤ ε k) (k : ℕ) :
    ∑ j ∈ range k, a.A j h - ∑ j ∈ range k, a.w j * ε j
      + ∑ j ∈ (range k).filter (fun j => decide (a.star j = h) = true), a.w j * noise a m j
      ≤ a.W k h := by
  rw [a.wealth_eq h k]
  unfold Auction.allowanceOf Auction.chargedRecord
  have hsel : ∑ j ∈ (range k).filter (fun j => decide (a.star j = h) = true), a.w j * noise a m j
      = ∑ j ∈ range k, (if h = a.star j then a.w j * noise a m j else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : a.star j = h
    · simp [hj]
    · simp [hj, Ne.symm hj]
  rw [hsel]
  have : ∑ j ∈ range k, (if h = a.star j then a.w j * noise a m j else 0)
      - ∑ j ∈ range k, a.w j * ε j
      ≤ ∑ j ∈ range k, (if h = a.star j then a.w j * (a.G j - a.b j) else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hw := a.w_pos j
    unfold noise
    split_ifs with hj
    · rw [hW j, ← hj]
      have := (abs_le.mp (hon j)).2
      nlinarith
    · nlinarith [hε j]
  linarith

/-- **Feasibility from the allowance under noise.**  With the tracker's own noise sum over
its wins bounded below by `−M k` (the noise hypothesis on the selection "the tracker
wins", computable at opening), cumulative allowance through `k` covering the current
bid, the honest losses so far and `M k` makes it feasible at `k`. -/
theorem tracker_feasible_exp (e : ℕ → Fin n → ℝ) (h : Fin n) (m ε M : ℕ → ℝ)
    (hW : WinnerBids a e) (hon : HonestExp e h m ε) (hε : ∀ k, 0 ≤ ε k)
    (hN : NoiseBounded a m (fun j => decide (a.star j = h)) M) (k : ℕ)
    (hcov : a.w k * e k h + ∑ j ∈ range k, a.w j * ε j + M k ≤ ∑ j ∈ range (k + 1), a.A j h) :
    a.w k * e k h ≤ a.B k h := by
  have h1 := tracker_wealth_ge_exp a e h m ε hW hon hε k
  have h2 := (abs_le.mp (hN k)).1
  unfold Auction.B
  rw [Finset.sum_range_succ] at hcov
  linarith

/-- **Competitiveness from one honest tracker, under noise.**  The winners' signed margin
over the non-incident blocks is at most `Σ w_k ε_k`, plus the noise bound `M K` on the
selection "non-incident and the tracker feasible" (computable at opening), plus `R` times
the weight of the blocks where the tracker is capital-bound. -/
theorem competitive_of_honest_tracker_exp (e : ℕ → Fin n → ℝ) (h : Fin n) (m ε : ℕ → ℝ)
    (hH : HighestFeasible a e) (hon : HonestExp e h m ε) (hε : ∀ k, 0 ≤ ε k) (inc : ℕ → Bool)
    (R : ℝ) (hR0 : 0 ≤ R) (feas : ℕ → Bool) (hR : ∀ k, ¬ feas k = true → a.G k - a.b k ≤ R)
    (hfeas : ∀ k, feas k = true → a.w k * e k h ≤ a.B k h) (M : ℕ → ℝ)
    (hN : NoiseBounded a m (fun k => (!inc k) && feas k) M) :
    Competitive a inc (fun K => ∑ k ∈ range K, a.w k * ε k + M K
      + R * ∑ k ∈ (range K).filter (fun k => ¬ feas k = true), a.w k) := by
  intro K
  have hsplit := Finset.sum_filter_add_sum_filter_not ((range K).filter (fun k => ¬ inc k = true))
    (fun k => feas k = true) (fun k => a.w k * (a.G k - a.b k))
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hsel : (range K).filter (fun k => ¬ inc k = true ∧ feas k = true)
      = (range K).filter (fun k => ((!inc k) && feas k) = true) := by
    refine Finset.filter_congr fun k _ => ?_
    simp
  -- the feasible part: `w (G − b) ≤ w ε + w ξ`
  have hA : ∑ k ∈ (range K).filter (fun k => ¬ inc k = true ∧ feas k = true), a.w k * (a.G k - a.b k)
      ≤ ∑ k ∈ range K, a.w k * ε k + M K := by
    have h1 : ∑ k ∈ (range K).filter (fun k => ¬ inc k = true ∧ feas k = true), a.w k * (a.G k - a.b k)
        ≤ ∑ k ∈ (range K).filter (fun k => ¬ inc k = true ∧ feas k = true),
            (a.w k * ε k + a.w k * noise a m k) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' := (Finset.mem_filter.mp hk).2.2
      have := underpromise_le_of_feasible_exp a e h m ε hH hon k (hfeas k hk')
      have hw := a.w_pos k
      nlinarith
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ k ∈ (range K).filter (fun k => ¬ inc k = true ∧ feas k = true), a.w k * ε k
        ≤ ∑ k ∈ range K, a.w k * ε k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun k _ _ => mul_nonneg (a.w_pos k).le (hε k)
    have h3 : ∑ k ∈ (range K).filter (fun k => ¬ inc k = true ∧ feas k = true), a.w k * noise a m k
        ≤ M K := by
      rw [hsel]
      exact (le_abs_self _).trans (hN K)
    linarith
  -- the capital-bound part: `w (G − b) ≤ w R`
  have hB : ∑ k ∈ (range K).filter (fun k => ¬ inc k = true ∧ ¬ feas k = true), a.w k * (a.G k - a.b k)
      ≤ R * ∑ k ∈ (range K).filter (fun k => ¬ feas k = true), a.w k := by
    rw [Finset.mul_sum]
    calc ∑ k ∈ (range K).filter (fun k => ¬ inc k = true ∧ ¬ feas k = true), a.w k * (a.G k - a.b k)
        ≤ ∑ k ∈ (range K).filter (fun k => ¬ inc k = true ∧ ¬ feas k = true), R * a.w k := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := (Finset.mem_filter.mp hk).2.2
          have := hR k hk'
          have hw := a.w_pos k
          nlinarith
      _ ≤ ∑ k ∈ (range K).filter (fun k => ¬ feas k = true), R * a.w k := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => mul_nonneg hR0 (a.w_pos k).le
          intro k hk
          have := Finset.mem_filter.mp hk
          exact Finset.mem_filter.mpr ⟨this.1, this.2.2⟩
  linarith

/-- **Under the allowance condition** the tracker is feasible at every block and
competitiveness holds with `Mf K = Σ_{k<K} w_k ε_k + M K`, `o(K)` when the honest losses
and the noise bound are. -/
theorem competitive_of_affordable_tracker_exp (e : ℕ → Fin n → ℝ) (h : Fin n) (m ε Mw M : ℕ → ℝ)
    (hH : HighestFeasible a e) (hW : WinnerBids a e) (hon : HonestExp e h m ε)
    (hε : ∀ k, 0 ≤ ε k) (hNw : NoiseBounded a m (fun j => decide (a.star j = h)) Mw)
    (hcov : ∀ k, a.w k * e k h + ∑ j ∈ range k, a.w j * ε j + Mw k ≤ ∑ j ∈ range (k + 1), a.A j h)
    (inc : ℕ → Bool) (hN : NoiseBounded a m (fun k => !inc k) M) :
    Competitive a inc (fun K => ∑ k ∈ range K, a.w k * ε k + M K) := by
  intro K
  have hN' : NoiseBounded a m (fun k => (!inc k) && true) M := by
    intro K'; simpa using hN K'
  have := competitive_of_honest_tracker_exp a e h m ε hH hon hε inc 0 le_rfl (fun _ => true)
    (fun _ hk => absurd rfl hk)
    (fun k _ => tracker_feasible_exp a e h m ε Mw hW hon hε hNw k (hcov k)) M hN' K
  simpa using this

/-- **The rate under noise**: at most `(𝒜_K + Σ w_k ε_k + M K)/(ℓ · w_min · K)`, vanishing
when the allowance, the honest losses and the noise bound are all `o(K)`. -/
theorem rate_le_of_honest_tracker_exp (hf : a.FeasibleOpening) (inc : ℕ → Bool) (ℓ wmin : ℝ)
    (hw : ∀ k, wmin ≤ a.w k) (hwmin : 0 < wmin) (hℓ : 0 < ℓ)
    (hinc : ∀ k, inc k = true → ℓ ≤ a.b k - a.G k) (e : ℕ → Fin n → ℝ) (h : Fin n)
    (m ε Mw M : ℕ → ℝ) (hH : HighestFeasible a e) (hW : WinnerBids a e)
    (hon : HonestExp e h m ε) (hε : ∀ k, 0 ≤ ε k)
    (hNw : NoiseBounded a m (fun j => decide (a.star j = h)) Mw)
    (hcov : ∀ k, a.w k * e k h + ∑ j ∈ range k, a.w j * ε j + Mw k ≤ ∑ j ∈ range (k + 1), a.A j h)
    (hN : NoiseBounded a m (fun k => !inc k) M) (K : ℕ) (hK : 0 < K) :
    (((range K).filter (fun k => inc k = true)).card : ℝ) / K
      ≤ (a.totalAllowance K + (∑ k ∈ range K, a.w k * ε k + M K)) / (ℓ * wmin * K) :=
  rate_le_of_competitive a hf inc ℓ wmin hw hwmin hℓ hinc _
    (competitive_of_affordable_tracker_exp a e h m ε Mw M hH hW hon hε hNw hcov inc hN) K hK

/-- **The tracker's minimal allowance under noise**: a bid's worth at entry plus the
noise bound at entry, then the honest loss plus the increment of the noise bound. -/
noncomputable def trackerAllowance2 (w : ℕ → ℝ) (wbar D : ℝ) (ε M : ℕ → ℝ) : ℕ → ℝ
  | 0 => wbar * D + M 0
  | j + 1 => w j * ε j + (M (j + 1) - M j)

/-- Nonnegative when the noise bound is nondecreasing and nonnegative at entry. -/
theorem trackerAllowance2_nonneg (w : ℕ → ℝ) (wbar D : ℝ) (ε M : ℕ → ℝ)
    (hw : ∀ k, 0 < w k) (hwD : 0 ≤ wbar * D) (hε : ∀ k, 0 ≤ ε k) (hM0 : 0 ≤ M 0)
    (hM : Monotone M) : ∀ j, 0 ≤ trackerAllowance2 w wbar D ε M j := by
  intro j
  cases j with
  | zero => simp only [trackerAllowance2]; linarith
  | succ j =>
    simp only [trackerAllowance2]
    have := hM (Nat.le_succ j)
    nlinarith [hw j, hε j]

/-- Its total through `K + 1` is `w̄ · D + Σ_{j<K} w_j ε_j + M K`. -/
theorem trackerAllowance2_total (w : ℕ → ℝ) (wbar D : ℝ) (ε M : ℕ → ℝ) (K : ℕ) :
    ∑ j ∈ range (K + 1), trackerAllowance2 w wbar D ε M j
      = wbar * D + ∑ j ∈ range K, w j * ε j + M K := by
  induction K with
  | zero => simp [trackerAllowance2]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [trackerAllowance2]
    ring

/-- It covers the tracker's bid at every block when bids are clamped at `D` and weights
bounded by `w̄`: the condition of `tracker_feasible_exp`. -/
theorem trackerAllowance2_covers (w : ℕ → ℝ) (wbar D : ℝ) (ε M : ℕ → ℝ) (e : ℕ → ℝ)
    (hw : ∀ k, 0 < w k ∧ w k ≤ wbar) (hD : 0 ≤ D) (he : ∀ k, e k ≤ D) (k : ℕ) :
    w k * e k + ∑ j ∈ range k, w j * ε j + M k
      ≤ ∑ j ∈ range (k + 1), trackerAllowance2 w wbar D ε M j := by
  rw [trackerAllowance2_total]
  have := (hw k).1
  have := (hw k).2
  have := he k
  nlinarith

/-- The deterministic schedule is the case `M ≡ 0`. -/
theorem trackerAllowance2_zero (w : ℕ → ℝ) (wbar D : ℝ) (ε : ℕ → ℝ) (j : ℕ) :
    trackerAllowance2 w wbar D ε (fun _ => 0) j = trackerAllowance w wbar D ε j := by
  cases j <;> simp [trackerAllowance2, trackerAllowance]

end NoisyTracker

section Azuma

open ProbabilityTheory MeasureTheory

/-- **The per-`K` tail, from the pinned Mathlib.**  A sub-Gaussian sum `S` with parameter
`C > 0` exceeds `√(2 C log(1/δ))` with probability at most `δ`
(`HasSubgaussianMGF.measure_ge_le`, the Chernoff bound). -/
theorem subgaussian_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (S : Ω → ℝ) (C : NNReal)
    (hC : 0 < (C : ℝ)) (h : HasSubgaussianMGF S C μ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ S ω} ≤ δ := by
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ hδ1)
  have hε : 0 ≤ Real.sqrt (2 * C * Real.log (1 / δ)) := Real.sqrt_nonneg _
  refine (h.measure_ge_le hε).trans ?_
  rw [Real.sq_sqrt (by positivity)]
  have : -(2 * (C : ℝ) * Real.log (1 / δ)) / (2 * C) = Real.log δ := by
    rw [one_div, Real.log_inv]
    field_simp
  rw [this, Real.exp_log hδ]

/-- **Two-sided**: `|S| ≥ √(2 C log(1/δ))` with probability at most `2δ`, the lower tail
from the sub-Gaussianity of `−S` (`HasSubgaussianMGF.neg`). -/
theorem subgaussian_two_sided {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (S : Ω → ℝ) (C : NNReal) (hC : 0 < (C : ℝ))
    (h : HasSubgaussianMGF S C μ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ |S ω|} ≤ 2 * δ := by
  have h1 := subgaussian_tail S C hC h δ hδ hδ1
  have h2 := subgaussian_tail (-S) C hC h.neg δ hδ hδ1
  have hsub : {ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ |S ω|}
      ⊆ {ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ S ω}
        ∪ {ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ (-S) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.neg_apply] at hω ⊢
    exact le_abs.mp hω
  calc μ.real {ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ |S ω|}
      ≤ μ.real ({ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ S ω}
          ∪ {ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ (-S) ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ S ω}
          + μ.real {ω | Real.sqrt (2 * C * Real.log (1 / δ)) ≤ (-S) ω} := measureReal_union_le _ _
    _ ≤ 2 * δ := by linarith

/-- **Azuma–Hoeffding, instantiated** (`measure_sum_ge_le_of_hasCondSubgaussianMGF`): for a
process `Y` strongly adapted to a filtration and conditionally sub-Gaussian given the
previous σ-algebra — the selected weighted noise `w_i 1[S i] ξ_i` under a selection
computable at opening — the sum over `range n` exceeds `√(2 (Σ c_i) log(1/δ))` with
probability at most `δ`.  With bounded increments `c_i = O(1)` this is
`M(n) = O(√(n log n))` at `δ = 1/n`. -/
theorem azuma_selected_tail {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {cY : ℕ → NNReal}
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    (hC : 0 < ((∑ i ∈ range n, cY i : NNReal) : ℝ)) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | Real.sqrt (2 * ((∑ i ∈ range n, cY i : NNReal) : ℝ) * Real.log (1 / δ))
      ≤ ∑ i ∈ range n, Y i ω} ≤ δ :=
  subgaussian_tail (fun ω => ∑ i ∈ range n, Y i ω) _ hC
    (HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF h_adapted h0 n h_subG) δ hδ hδ1

end Azuma

/-! ## 4″. The violation rate is an exchange rate (`FOLLOWUP4.md`) -/

section ExchangeRate

open Workspace.Deference.Contrib.ProtectedAuthorityTheorem (score)

variable (P : LexParams)

/-- Under (ii) the evaluation is at most the bid: counts and prices are nonnegative. -/
theorem evalOf_le_bid (bid : ℝ) (nK : ℕ) (pS pT : ℝ) (hp : 0 ≤ pS + pT) :
    P.evalOf bid nK pS pT ≤ bid := by
  unfold LexParams.evalOf
  have := P.ϖ_pos
  nlinarith [mul_nonneg this.le hp, mul_nonneg this.le (Nat.cast_nonneg (α := ℝ) nK)]

/-- **Consistency under (ii), verified.**  Evaluation less the realized lexical score is bid
less the realized residual, whatever the prices: the pricing error of the forecast events
is absorbed by the settlement convention and needs no term. -/
theorem eval_sub_score_ii (bid gord pS pT : ℝ) (nK nF nL : ℕ) :
    P.evalOf bid nK pS pT - P.realized gord nK nF nL = bid - P.residII gord nF nL pS pT := by
  unfold LexParams.evalOf LexParams.realized LexParams.residII score; ring

/-- Under (i) the same difference carries the market's pricing error `ϖ (n_fore − Σp)`,
which is why (i) would need a separate term. -/
theorem eval_sub_score_i (bid gord pS pT : ℝ) (nK nF nL : ℕ) :
    P.evalOf bid nK pS pT - P.realized gord nK nF nL
      = bid - P.residI gord nL + P.ϖ * (nF - (pS + pT)) := by
  unfold LexParams.evalOf LexParams.realized LexParams.residI score; ring

/-- Rescaling is affine: differences scale by the range `ρ = D − (w − ϖ N̄)`. -/
theorem rescale_sub (N : ℕ) (s t : ℝ) :
    P.rescale N s - P.rescale N t = (s - t) / (P.D - (P.w - P.ϖ * N)) := by
  unfold LexParams.rescale
  rw [div_sub_div_same]
  congr 1
  ring

/-- The exchange rate is invariant under the rescaling: `(D' − w')/ϖ' = (D − w)/ϖ` with
`D' = rescale D`, `w' = rescale w` and `ϖ' = ϖ/ρ`. -/
theorem exchange_rate_invariant (N : ℕ) (hN : 1 ≤ N) :
    (P.rescale N P.D - P.rescale N P.w) / (P.ϖ / (P.D - (P.w - P.ϖ * N)))
      = (P.D - P.w) / P.ϖ := by
  have hρ := P.range_pos N hN
  rw [rescale_sub]
  field_simp

/-- **The violation rate is bounded by the exchange rate**, multiplied form.  On an auction
whose settlement is consistent — the winner's overestimation `b_k − G_k` is the evaluation
less the realized lexical score, over the range `ρ` — with every winner evaluating at
least `w` (inquiry on the menu), the expected score given opening at most `D − ϖ π_k`
(`π_k` the expected count of violations of every class), and the noise over *all* blocks
— a selection fixed at opening — bounded by `M K`:
`ϖ Σ w_k π_k ≤ (D − w) Σ w_k + ρ 𝒜_K + M K`. -/
theorem violation_rate_le_exchange_mul (D w ϖ : ℝ) {n : ℕ} (a : Auction n)
    (hf : a.FeasibleOpening) (ρ : ℝ) (hρ : 0 < ρ) (eval S m π : ℕ → ℝ)
    (hwin : ∀ k, w ≤ eval k) (hcons : ∀ k, a.b k - a.G k = (eval k - S k) / ρ)
    (hm : ∀ k, m k ≤ D - ϖ * π k) (M : ℕ → ℝ)
    (hN : ∀ K, |∑ k ∈ range K, a.w k * (S k - m k)| ≤ M K) (K : ℕ) :
    ϖ * ∑ k ∈ range K, a.w k * π k
      ≤ (D - w) * ∑ k ∈ range K, a.w k + (ρ * a.totalAllowance K + M K) := by
  have hover := a.overestimation_le_allowance_opening hf K
  have h1 : ∑ k ∈ range K, a.w k * (eval k - S k) ≤ ρ * a.totalAllowance K := by
    have : ∑ k ∈ range K, a.w k * (a.b k - a.G k)
        = (∑ k ∈ range K, a.w k * (eval k - S k)) / ρ := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcons k]; ring
    rw [this, div_le_iff₀ hρ] at hover
    linarith
  have h2 := (abs_le.mp (hN K)).2
  have h3 : ∑ k ∈ range K, a.w k * (w - D + ϖ * π k)
      ≤ ∑ k ∈ range K, a.w k * (eval k - m k) :=
    Finset.sum_le_sum fun k _ => by
      have := a.w_pos k
      nlinarith [hwin k, hm k]
  have h4 : ∑ k ∈ range K, a.w k * (eval k - m k)
      = ∑ k ∈ range K, a.w k * (eval k - S k) + ∑ k ∈ range K, a.w k * (S k - m k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h5 : ∑ k ∈ range K, a.w k * (w - D + ϖ * π k)
      = (w - D) * ∑ k ∈ range K, a.w k + ϖ * ∑ k ∈ range K, a.w k * π k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linarith

/-- **The violation rate is bounded by the exchange rate.**  The weighted average expected
violation count per winning block is at most `(D − w)/ϖ` plus a term vanishing when the
allowance and the noise bound are `o(K)`. -/
theorem violation_rate_le_exchange (D w ϖ : ℝ) (hϖ : 0 < ϖ) {n : ℕ} (a : Auction n)
    (hf : a.FeasibleOpening) (ρ : ℝ) (hρ : 0 < ρ) (eval S m π : ℕ → ℝ)
    (hwin : ∀ k, w ≤ eval k) (hcons : ∀ k, a.b k - a.G k = (eval k - S k) / ρ)
    (hm : ∀ k, m k ≤ D - ϖ * π k) (M : ℕ → ℝ)
    (hN : ∀ K, |∑ k ∈ range K, a.w k * (S k - m k)| ≤ M K) (K : ℕ)
    (hK : 0 < ∑ k ∈ range K, a.w k) :
    (∑ k ∈ range K, a.w k * π k) / (∑ k ∈ range K, a.w k)
      ≤ (D - w) / ϖ + (ρ * a.totalAllowance K + M K) / (ϖ * ∑ k ∈ range K, a.w k) := by
  have h := violation_rate_le_exchange_mul D w ϖ a hf ρ hρ eval S m π hwin hcons hm M hN K
  rw [div_le_iff₀ hK]
  have hW := hK.ne'
  have : ((D - w) / ϖ + (ρ * a.totalAllowance K + M K) / (ϖ * ∑ k ∈ range K, a.w k))
      * ∑ k ∈ range K, a.w k
      = ((D - w) * ∑ k ∈ range K, a.w k + (ρ * a.totalAllowance K + M K)) / ϖ := by
    field_simp
  rw [this, le_div_iff₀ hϖ]
  linarith

/-- **In the auction's own (rescaled) units** the same statement reads with `ρ = 1`: the
rescaled evaluation, score, expectation and weight `ϖ' = ϖ/ρ`, and the rescaled window and
range; the exchange rate `(D' − w')/ϖ'` is the unrescaled one (`exchange_rate_invariant`). -/
theorem violation_rate_le_exchange_rescaled (D' w' ϖ' : ℝ) (hϖ : 0 < ϖ') {n : ℕ}
    (a : Auction n) (hf : a.FeasibleOpening) (eval' S' m' π : ℕ → ℝ)
    (hwin : ∀ k, w' ≤ eval' k) (hcons : ∀ k, a.b k - a.G k = eval' k - S' k)
    (hm : ∀ k, m' k ≤ D' - ϖ' * π k) (M' : ℕ → ℝ)
    (hN : ∀ K, |∑ k ∈ range K, a.w k * (S' k - m' k)| ≤ M' K) (K : ℕ)
    (hK : 0 < ∑ k ∈ range K, a.w k) :
    (∑ k ∈ range K, a.w k * π k) / (∑ k ∈ range K, a.w k)
      ≤ (D' - w') / ϖ' + (a.totalAllowance K + M' K) / (ϖ' * ∑ k ∈ range K, a.w k) := by
  have := violation_rate_le_exchange D' w' ϖ' hϖ a hf 1 one_pos eval' S' m' π hwin
    (fun k => by rw [hcons k, div_one]) hm M' hN K hK
  simpa using this

/-- **The settlement is consistent in the design**: the overestimation of a block settled
under (ii) and rescaled is the evaluation less the realized lexical score over the range —
the hypothesis `hcons` of the theorem, discharged from `eval_sub_score_ii` and
`rescale_sub`. -/
theorem design_consistent (N : ℕ) (bid gord pS pT : ℝ) (nK nF nL : ℕ) :
    P.rescale N bid - P.rescale N (P.residII gord nF nL pS pT)
      = (P.evalOf bid nK pS pT - P.realized gord nK nF nL) / (P.D - (P.w - P.ϖ * N)) := by
  rw [rescale_sub, eval_sub_score_ii]

/-- A bounded score and a bounded expectation give a bounded noise increment: the
hypothesis under which Hoeffding's lemma makes each increment sub-Gaussian. -/
theorem noise_increment_le (lo hi S m : ℝ) (hS : lo ≤ S ∧ S ≤ hi) (hm : lo ≤ m ∧ m ≤ hi) :
    |S - m| ≤ hi - lo := by
  rw [abs_le]; constructor <;> linarith [hS.1, hS.2, hm.1, hm.2]

/-- The realized lexical score lies in `[w − ϖ N̄, D]` when the ordinary value is in
`[w, D]` and at most `N̄` violations are counted: the increment bound is the range `ρ`. -/
theorem realized_range (N : ℕ) (gord : ℝ) (hg : P.w ≤ gord ∧ gord ≤ P.D) (nK nF nL : ℕ)
    (hn : nK + nF + nL ≤ N) :
    P.w - P.ϖ * N ≤ P.realized gord nK nF nL ∧ P.realized gord nK nF nL ≤ P.D := by
  refine ⟨P.realized_ge gord hg.1 nK nF nL hn, ?_⟩
  unfold LexParams.realized score
  have := P.ϖ_pos
  nlinarith [Nat.cast_nonneg (α := ℝ) (nK + nF + nL), hg.2]

/-- **The tolerated rate and the `ϖ` band.**  Inside the band `D − w < ϖ < (D − w)/p_min`
the tolerated violation probability `(D − w)/ϖ` lies strictly between `p_min` and `1`:
`ϖ` sets it directly, and drills — which sharpen the prices — do not move it. -/
theorem tolerated_rate_band (D w ϖ pmin : ℝ) (hϖ : 0 < ϖ) (hp : 0 < pmin)
    (hlo : D - w < ϖ) (hhi : ϖ < (D - w) / pmin) :
    pmin < (D - w) / ϖ ∧ (D - w) / ϖ < 1 := by
  constructor
  · rw [lt_div_iff₀ hϖ]
    rw [lt_div_iff₀ hp] at hhi
    linarith
  · rw [div_lt_one hϖ]; exact hlo

/-- **C.5's threshold is the same exchange rate**: a clean option beats inquiry iff its
priced risk is below `(bid − w)/ϖ ≤ (D − w)/ϖ` (`implied_threshold`, `threshold_le`,
`asks_iff`); an after-the-fact risk `p` enters the honest bid as `−ϖ p` and the option
wins iff `gord − w ≥ ϖ p`, the same comparison. -/
theorem priced_risk_wins_iff (gord p : ℝ) :
    P.w ≤ P.evalOf (gord - P.ϖ * p) 0 0 0 ↔ P.ϖ * p ≤ gord - P.w := by
  rw [evalOf_zero_price]; constructor <;> intro h <;> linarith

end ExchangeRate

section Scope

variable {n : ℕ} (a : Auction n)

/-- **What the honest tracker still gives, on a selection fixed at opening.**  With
`inc ≡ false` the margin is over every winning block, so the winners' signed
underpromise over all blocks is at most `Σ w_k ε_k + M K` — and by the wealth identity
the class's total wealth is at most the allowance plus that: no wealth goes idle through
underpromising winners beyond the honest losses and the noise.  Nothing in the violation
claim consumes it. -/
theorem total_wealth_le_of_tracker (e : ℕ → Fin n → ℝ) (h : Fin n) (m ε Mw M : ℕ → ℝ)
    (hH : HighestFeasible a e) (hW : WinnerBids a e) (hon : HonestExp e h m ε)
    (hε : ∀ k, 0 ≤ ε k) (hNw : NoiseBounded a m (fun j => decide (a.star j = h)) Mw)
    (hcov : ∀ k, a.w k * e k h + ∑ j ∈ range k, a.w j * ε j + Mw k ≤ ∑ j ∈ range (k + 1), a.A j h)
    (hN : NoiseBounded a m (fun _ => true) M) (K : ℕ) :
    ∑ i, a.W K i ≤ a.totalAllowance K + (∑ k ∈ range K, a.w k * ε k + M K) := by
  have hc := competitive_of_affordable_tracker_exp a e h m ε Mw M hH hW hon hε hNw hcov
    (fun _ => false) (by simpa using hN) K
  rw [a.wealth_sum_eq K]
  simp only [Bool.false_eq_true, not_false_eq_true, Finset.filter_true] at hc
  linarith

end Scope

/-! ## 5. Witnesses -/

namespace Witness

/-- Three components, four acts: two violations writing `0` and `1`, a use reading `1`
writing `2`, a clean act reading `0`. -/
def io4 : IO (Fin 3) (Fin 4) where
  reads := ![∅, ∅, {1}, {0}]
  writes := ![{0}, {1}, {2}, ∅]

/-- **The bug.**  Under the old rule one remedy clears both violations' taint: the second's
fruits are used uncharged. -/
theorem two_violations_one_remedy_old :
    taintAfter io4 [.act 0 true, .act 1 true, .remedy] = ∅ ∧
    uses io4 (taintAfter io4 [.act 0 true, .act 1 true, .remedy]) 2 = false := by
  decide

/-- **The correction.**  Under the per-violation rule the remedy of the first leaves the
second's taint, its fruits are used and charged, and only the second remedy clears them. -/
theorem two_violations_one_remedy_new :
    taintAfter2 (V := Fin 2) io4 [.act 0 (some 0), .act 1 (some 1), .remedy 0] = {(1, 1)} ∧
    uses2 io4 (taintAfter2 (V := Fin 2) io4 [.act 0 (some 0), .act 1 (some 1), .remedy 0]) 2
      = true ∧
    uses2 io4 (taintAfter2 (V := Fin 2) io4 [.act 0 (some 0), .act 1 (some 1), .remedy 0]) 3
      = false ∧
    uses2 io4 (taintAfter2 (V := Fin 2) io4
      [.act 0 (some 0), .act 1 (some 1), .remedy 0, .remedy 1]) 2 = false := by
  decide

/-- The charged block: the use of the second violation's fruits, won at the window, loses
`ℓ` under (ii) — with the round's parameters `D = 1`, `w = 0`, `ϖ = 2`, exactly `1`. -/
theorem two_violations_charged :
    BRIACorrigibility.Witness.P₀.ϖ - BRIACorrigibility.Witness.P₀.D + BRIACorrigibility.Witness.P₀.w
        ≤ 1 - BRIACorrigibility.Witness.P₀.residII 1 0 1 0 0 ∧
    BRIACorrigibility.Witness.P₀.ϖ - BRIACorrigibility.Witness.P₀.D + BRIACorrigibility.Witness.P₀.w
        = 1 :=
  ⟨standing_block_loss_ii BRIACorrigibility.Witness.P₀ 1 0 0 0
    (by unfold LexParams.evalOf; simp [BRIACorrigibility.Witness.P₀]) 1 le_rfl 0 1 (by omega),
   by norm_num [BRIACorrigibility.Witness.P₀]⟩

/-- **`taint_decides`, re-proved** on the old instance with one identifier: the same taint
set, use verdicts, and remedy. -/
theorem taint_decides2 :
    taintAfter2 (V := Fin 1) BRIAFollowup.Witness.io3 [.act 0 (some 0), .act 1 none] = {(0, 1), (0, 2)} ∧
    uses2 BRIAFollowup.Witness.io3 (taintAfter2 (V := Fin 1) BRIAFollowup.Witness.io3 [.act 0 (some 0), .act 1 none]) 2 = false ∧
    uses2 BRIAFollowup.Witness.io3 (taintAfter2 (V := Fin 1) BRIAFollowup.Witness.io3 [.act 0 (some 0), .act 1 none]) 1 = true ∧
    taintAfter2 (V := Fin 1) BRIAFollowup.Witness.io3 [.act 0 (some 0), .act 1 none, .remedy 0] = ∅ := by
  decide

/-- Her standards component alone; two implanting acts, the agent's and a third party's. -/
def ioStd : IO (Fin 1) (Fin 2) where
  reads := ![∅, ∅]
  writes := ![{0}, {0}]

/-- Standing of the standards component: some influence tainting it, unremedied. -/
def standing2 (steps : List (Step2 (Fin 2) (Fin 2))) : Bool :=
  decide (taintedBy (taintAfter2 ioStd steps) 0).Nonempty

/-- **`implant_standing`, re-proved** as the disclosure-cures map: the influence is a
violation tainting the standards component, its disclosure is its remedy; the rows'
verdicts are reproduced from `standingStandards`. -/
theorem implant_standing2 :
    standing2 [.act 0 (some 0)] = standingStandards Consult2.Rows2.rowImplant 0 ∧
    standing2 [.act 0 (some 0)] = standingStandards Consult2.Rows2.rowImplant 1 ∧
    standing2 [.act 0 (some 0)] = standingStandards Consult2.Rows2.rowImplantDisclosed 0 ∧
    standing2 [.act 0 (some 0), .remedy 0]
      = standingStandards Consult2.Rows2.rowImplantDisclosed 1 := by
  decide

/-- **Two influences, one disclosure.**  The agent's disclosure of its own implant does not
cure the third party's: the standards stay tainted until both are disclosed. -/
theorem two_influences_one_disclosure :
    standing2 [.act 0 (some 0), .act 1 (some 1), .remedy 0] = true ∧
    standing2 [.act 0 (some 0), .act 1 (some 1), .remedy 0, .remedy 1] = false := by
  decide

/-- Two components (the asset, another), three acts: the commission writes the asset, the
use reads it, a clean act reads the other. -/
def ioW : IO (Fin 2) (Fin 3) where
  reads := ![∅, {0}, {1}]
  writes := ![{0}, ∅, ∅]

/-- The record before detection: commission at `0` unflagged, uses at `1` and `2`. -/
def recW : List (Step2 (Fin 1) (Fin 3)) := [.act 0 none, .act 1 none, .act 1 none]

/-- **The window before detection.**  Before detection no taint is on record, so the uses
at `1` and `2` are chosen unrecognized; detection at `3` flags the commission, the
recomputed taint stands on the asset from block `0`, both uses read it (charged by late
debit), and with the taint on record a further use is recognized in advance. -/
theorem window_before_detection :
    taintAfter2 ioW recW = ∅ ∧
    uses2 ioW (taintAfter2 ioW (recW.take 1)) 1 = false ∧
    uses2 ioW (taintAfter2 ioW (recW.take 2)) 1 = false ∧
    detectAt recW 0 0 = [.act 0 (some 0), .act 1 none, .act 1 none] ∧
    uses2 ioW (taintAfter2 ioW ((detectAt recW 0 0).take 1)) 1 = true ∧
    uses2 ioW (taintAfter2 ioW ((detectAt recW 0 0).take 2)) 1 = true ∧
    uses2 ioW (taintAfter2 ioW (detectAt recW 0 0)) 1 = true ∧
    uses2 ioW (taintAfter2 ioW (detectAt recW 0 0)) 2 = false ∧
    nKnownWith ioW (taintAfter2 ioW (detectAt recW 0 0)) (fun _ => 0) 1 = 1 := by
  decide

/-- The late debit on the window: charge `ϖ = 2` per use block against an allowance of
`1` per block from detection; collected in two blocks, the uncollected part in between. -/
theorem window_debit_collected :
    ∑ j ∈ range 2, greedyDebit (fun _ => (1 : ℝ)) 2 j = 2 ∧
    ∑ j ∈ range 1, greedyDebit (fun _ => (1 : ℝ)) 2 j = 1 ∧
    (2 : ℝ) - ∑ j ∈ range 1, greedyDebit (fun _ => (1 : ℝ)) 2 j = 1 := by
  have h2 := greedy_collects (fun _ => (1 : ℝ)) (fun _ => zero_le_one) 2 zero_le_two 2
  have h1 := greedy_collects (fun _ => (1 : ℝ)) (fun _ => zero_le_one) 2 zero_le_two 1
  rw [h2, h1]
  norm_num [Finset.sum_const]

/-- **The unaffordable tracker.**  Two hypotheses: an underpromiser bidding `1/2` on a
return of `1`, funded at block `0`; an honest tracker bidding `1` with no allowance, so
never feasible.  The rule holds, the tracker is honest with `ε = 0`, and the margin is
`K/2`: linear. -/
noncomputable def unaffordable : Auction 2 where
  w _ := 1
  A k i := if k = 0 ∧ i = 0 then 1 else 0
  star _ := 0
  b _ := 1 / 2
  G _ := 1
  w_pos _ := one_pos
  A_nonneg _ _ := by split_ifs <;> norm_num
  G_nonneg _ := zero_le_one

noncomputable def eU : ℕ → Fin 2 → ℝ := fun _ => ![1 / 2, 1]

theorem unaffordable_W1 (k : ℕ) : unaffordable.W k 1 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Auction.W_succ, ih]; simp [unaffordable]

theorem unaffordable_witness :
    HighestFeasible unaffordable eU ∧ WinnerBids unaffordable eU ∧
    Honest unaffordable eU 1 (fun _ => 0) ∧
    (∀ k, ¬ unaffordable.w k * eU k 1 ≤ unaffordable.B k 1) ∧
    ∀ K, ∑ k ∈ range K, unaffordable.w k * (unaffordable.G k - unaffordable.b k) = K / 2 := by
  refine ⟨?_, fun k => by simp [unaffordable, eU], fun k => by simp [unaffordable, eU], ?_, ?_⟩
  · intro k
    rw [Fin.forall_fin_two]
    constructor
    · intro _; simp [unaffordable, eU]
    · intro hi
      exfalso
      simp only [Auction.B, unaffordable_W1] at hi
      norm_num [unaffordable, eU] at hi
  · intro k
    simp only [Auction.B, unaffordable_W1]
    simp [unaffordable, eU]
  · intro K
    simp [unaffordable, Finset.sum_const, Finset.card_range]
    ring

/-- **The affordable tracker.**  The same class with the tracker funded at block `0`: it is
feasible at every block, the rule forces the winning bid up to its honest bid, and the
margin is `0`. -/
noncomputable def affordable : Auction 2 where
  w _ := 1
  A k _ := if k = 0 then 1 else 0
  star _ := 1
  b _ := 1
  G _ := 1
  w_pos _ := one_pos
  A_nonneg _ _ := by split_ifs <;> norm_num
  G_nonneg _ := zero_le_one

theorem affordable_W1 (k : ℕ) : affordable.W k 1 = if k = 0 then 0 else 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Auction.W_succ, ih]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [affordable]
    · simp [affordable, hk.ne']

theorem affordable_witness :
    HighestFeasible affordable eU ∧ WinnerBids affordable eU ∧
    Honest affordable eU 1 (fun _ => 0) ∧
    (∀ k, affordable.w k * eU k 1 ≤ affordable.B k 1) ∧
    ∀ K, ∑ k ∈ range K, affordable.w k * (affordable.G k - affordable.b k) = 0 := by
  refine ⟨?_, fun k => by simp [affordable, eU], fun k => by simp [affordable, eU], ?_, ?_⟩
  · intro k
    rw [Fin.forall_fin_two]
    constructor
    · intro _; norm_num [affordable, eU]
    · intro _; norm_num [affordable, eU]
  · intro k
    simp only [Auction.B, affordable_W1]
    simp [affordable, eU]
    split_ifs <;> norm_num
  · intro K
    simp [affordable]


/-- **One honest tracker requires honesty on every winning continuation.**  A tracker honest
only on its own proposal does not bound the winner's underpromise: with the tracker's
continuation expected at `1/2` (bid `1/2`, `ε = 0`) and the winning continuation, a
different one, realized at `1` with a bid of `3/5` — a higher evaluation, so the rule is
respected — the winner underpromises by `2/5`, unbounded by the tracker's `ε`.  FIX-level
arithmetic; the content is that `HighestFeasible` compares bids on the *winning*
continuation only. -/
theorem own_proposal_insufficient :
    (1 : ℝ) / 2 ≤ 3 / 5 ∧ (1 : ℝ) - 3 / 5 = 2 / 5 ∧ (0 : ℝ) < 2 / 5 := by norm_num

/-- **The noisy tracker's witness, both ways.**  With realized `G = m + ξ`, `ξ = ±1/4`, the
old honesty needs `ε_k = 1/4` at every block — `Σ ε_k = K/4`, linear — while honesty
against the expectation holds with `ε ≡ 0`. -/
theorem noisy_honesty_witness (K : ℕ) :
    ∑ _k ∈ range K, (1 / 4 : ℝ) = K / 4 ∧ (∀ ξ : ℝ, |ξ| = 1 / 4 → ¬ |ξ| ≤ 0) := by
  refine ⟨by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring, ?_⟩
  intro ξ hξ h
  rw [hξ] at h
  norm_num at h

/-! ### The counterexample to `NoiseBounded` on "not an incident" (`FOLLOWUP4.md` Part 2) -/

/-- A `5`-periodic function sums by period. -/
theorem sum_periodic5 {β : Type*} [AddCommMonoid β] (f : ℕ → β) (hf : ∀ k, f (k + 5) = f k)
    (n : ℕ) : ∑ k ∈ range (5 * n), f k = n • ∑ j ∈ range 5, f j := by
  have hshift : ∀ n j, f (5 * n + j) = f j := by
    intro n j
    induction n with
    | zero => simp
    | succ n ih => rw [show 5 * (n + 1) + j = (5 * n + j) + 5 by ring, hf, ih]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 5 * (n + 1) = 5 * n + 5 by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hshift n j

/-- Incidents at every fifth block: constant probability `p = 1/5`, realized as a periodic
pattern. -/
def incP (k : ℕ) : Bool := decide (k % 5 = 4)

/-- The noise in rescaled units for the round's parameters (`D = 1`, `w = 0`, `ϖ = 2`,
`N̄ = 1`, range `ρ = 3`): the ordinary value `9/10`, an after-the-fact violation with
probability `1/5`, so `m = 9/10 − 2/5 = 1/2` (rescaled `5/6`); the noise is `+2/15` on a
non-incident block and `−8/15` on an incident one. -/
noncomputable def xiP (k : ℕ) : ℝ := if k % 5 = 4 then -(8 / 15) else 2 / 15

theorem xiP_periodic (k : ℕ) : xiP (k + 5) = xiP k := by
  unfold xiP
  have : (k + 5) % 5 = k % 5 := by omega
  rw [this]

/-- The stream as an auction: one honest hypothesis bidding `m` every block, funded once. -/
noncomputable def constantRisk : Auction 1 where
  w _ := 1
  A k _ := if k = 0 then 1 else 0
  star _ := 0
  b _ := 5 / 6
  G k := 5 / 6 + xiP k
  w_pos _ := one_pos
  A_nonneg _ _ := by split_ifs <;> norm_num
  G_nonneg k := by unfold xiP; split_ifs <;> norm_num

theorem constantRisk_W (k : ℕ) :
    constantRisk.W k 0 = if k = 0 then 0 else 1 + (2 / 15) * ((k % 5 : ℕ) : ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Auction.W_succ, ih]
    simp only [constantRisk, xiP]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have hk' : k ≠ 0 := hk.ne'
      simp only [hk', if_false, Nat.succ_ne_zero, add_zero]
      by_cases h4 : k % 5 = 4
      · have : (k + 1) % 5 = 0 := by omega
        rw [if_pos h4, this]; push_cast; rw [h4]; push_cast; ring
      · have : (k + 1) % 5 = k % 5 + 1 := by omega
        rw [if_neg h4, this]; push_cast; ring

/-- The stream is feasible under opening timing. -/
theorem constantRisk_feasible : constantRisk.FeasibleOpening := by
  intro k
  show constantRisk.w k * constantRisk.b k ≤ constantRisk.W k 0 + constantRisk.A k 0
  rw [constantRisk_W]
  simp only [constantRisk]
  split_ifs with h
  · norm_num
  · have : (0 : ℝ) ≤ ((k % 5 : ℕ) : ℝ) := Nat.cast_nonneg _
    norm_num; linarith

/-- **The non-incident noise sum grows linearly**: over `5n` blocks it is `8n/15`. -/
theorem nonincident_noise_linear (n : ℕ) :
    ∑ k ∈ (range (5 * n)).filter (fun k => (!incP k) = true), constantRisk.w k * xiP k
      = n * (8 / 15) := by
  rw [Finset.sum_filter]
  have hper : ∀ k, (if (!incP (k + 5)) = true then constantRisk.w (k + 5) * xiP (k + 5) else 0)
      = (if (!incP k) = true then constantRisk.w k * xiP k else 0) := by
    intro k
    have : (k + 5) % 5 = k % 5 := by omega
    simp only [incP, xiP, constantRisk, this]
  rw [sum_periodic5 _ hper n, nsmul_eq_mul]
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, incP, xiP, constantRisk]
  norm_num

/-- **Incidents persist at the constant rate `1/5`**: `n` of the `5n` blocks. -/
theorem incidents_constant_rate (n : ℕ) :
    ((range (5 * n)).filter (fun k => incP k = true)).card = n := by
  rw [Finset.card_filter]
  have hper : ∀ k, (if incP (k + 5) = true then 1 else 0) = (if incP k = true then (1 : ℕ) else 0) := by
    intro k
    have : (k + 5) % 5 = k % 5 := by omega
    have h2 : incP (k + 5) = incP k := by unfold incP; rw [this]
    rw [h2]
  rw [sum_periodic5 _ hper n, smul_eq_mul]
  have h5 : ∑ j ∈ range 5, (if incP j = true then 1 else 0) = 1 := by decide
  rw [h5, mul_one]

/-- **The noise over all blocks is bounded by a constant**: the all-blocks selection is
fixed at opening and `NoiseBounded` holds with `M ≡ 8/15`, while on "not an incident" it
is linear. -/
theorem all_blocks_noise_bounded : NoiseBounded constantRisk (fun _ => 5 / 6) (fun _ => true)
    (fun _ => 8 / 15) := by
  intro K
  simp only [noise, constantRisk, Finset.filter_true, add_sub_cancel_left, one_mul]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 5 ∧ K = 5 * q + r :=
    ⟨K / 5, K % 5, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod K 5).symm⟩
  rw [Finset.sum_range_add, sum_periodic5 _ xiP_periodic, nsmul_eq_mul]
  have hzero : ∑ j ∈ range 5, xiP j = 0 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, xiP]; norm_num
  rw [hzero, mul_zero, zero_add]
  have hshift : ∀ x, xiP (5 * q + x) = xiP x := by
    intro x
    unfold xiP
    have : (5 * q + x) % 5 = x % 5 := by omega
    rw [this]
  rw [Finset.sum_congr rfl fun x _ => hshift x]
  interval_cases r <;> simp [Finset.sum_range_succ, xiP] <;> norm_num

/-- **`NoiseBounded` on "not an incident" forces a linear bound**: any `M` for that
selection satisfies `8n/15 ≤ M (5n)`, so it is not `o(K)`. -/
theorem nonincident_forces_linear (M : ℕ → ℝ)
    (hN : NoiseBounded constantRisk (fun _ => 5 / 6) (fun k => !incP k) M) (n : ℕ) :
    n * (8 / 15) ≤ M (5 * n) := by
  have h := hN (5 * n)
  simp only [noise, constantRisk, add_sub_cancel_left, one_mul] at h
  have hsum := nonincident_noise_linear n
  simp only [constantRisk, one_mul] at hsum
  rw [hsum] at h
  exact (le_abs_self _).trans h

/-- **`incidents_le_signed` then constrains nothing**: with `ℓ = 1/3` (rescaled), `w_min = 1`
and the allowance `1`, the signed bound reads `n/3 ≤ 1 + 8n/15` for `n` incidents in `5n`
blocks — true for every `n`; a constant rate `1/5` is compatible with it. -/
theorem signed_bound_allows_constant_rate (n : ℕ) :
    (1 / 3 : ℝ) * 1 * n ≤ 1 + n * (8 / 15) := by
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

/-- On the stream the incident blocks satisfy the signed bound's per-incident hypothesis
(`ℓ ≤ b − G`), the non-incident margin is the linear noise sum, and the exchange-rate
theorem's tolerated rate `1/2` sits above the realized `1/5`. -/
theorem constantRisk_facts :
    (∀ k, incP k = true → (1 / 3 : ℝ) ≤ constantRisk.b k - constantRisk.G k) ∧
    (1 / 5 : ℝ) < (1 - 0) / 2 := by
  refine ⟨fun k hk => ?_, by norm_num⟩
  simp only [incP, decide_eq_true_eq] at hk
  simp only [constantRisk, xiP, hk, if_true]
  norm_num

end Witness

/-! ## Axiom audit -/

#print axioms readTaint
#print axioms taintStep2
#print axioms taintAfter2
#print axioms taintedBy
#print axioms uses2
#print axioms commission_taints
#print axioms taint_propagates2
#print axioms taint_joins
#print axioms remedy_clears2
#print axioms remedy_keeps_others
#print axioms taintedBy_remedy
#print axioms still_tainted_after_one_remedy
#print axioms old_is_new_with_one_identifier
#print axioms uses_old_eq_new
#print axioms knowledge_residual2
#print axioms observation_taints_all2
#print axioms price_cancels
#print axioms residII_zero_price
#print axioms evalOf_zero_price
#print axioms standing_block_loss_ii
#print axioms standing_block_loss_of_ii
#print axioms cross_block_blocked_ii
#print axioms nKnownWith
#print axioms use_is_known
#print axioms after_detection_never_used
#print axioms detectAt
#print axioms taint_only_from_commission
#print axioms taint_persists_without_remedy
#print axioms never_detected_never_charged
#print axioms late_debit_eq_late_settlement
#print axioms window_block_charged
#print axioms greedyDebit
#print axioms greedy_collects
#print axioms collected_iff
#print axioms uncollected_eq
#print axioms windowDebit
#print axioms windowDebit_bounds
#print axioms window_exposure
#print axioms randomLocked
#print axioms mixtureLocked
#print axioms expected_escrow_eq
#print axioms locked_eq_tail
#print axioms truncation_cost
#print axioms Expect.sum
#print axioms Expect.sub
#print axioms average_mean
#print axioms average_variance
#print axioms variance_falls
#print axioms bernoulli_variance
#print axioms HighestFeasible
#print axioms WinnerBids
#print axioms Honest
#print axioms underpromise_le_of_feasible
#print axioms tracker_wealth_ge
#print axioms tracker_feasible
#print axioms competitive_of_honest_tracker
#print axioms competitive_of_affordable_tracker
#print axioms rate_le_of_honest_tracker
#print axioms trackerAllowance
#print axioms trackerAllowance_covers
#print axioms trackerAllowance_total
#print axioms Witness.io4
#print axioms Witness.two_violations_one_remedy_old
#print axioms Witness.two_violations_one_remedy_new
#print axioms Witness.two_violations_charged
#print axioms Witness.taint_decides2
#print axioms Witness.ioStd
#print axioms Witness.standing2
#print axioms Witness.implant_standing2
#print axioms Witness.two_influences_one_disclosure
#print axioms Witness.ioW
#print axioms Witness.recW
#print axioms Witness.window_before_detection
#print axioms Witness.window_debit_collected
#print axioms Witness.unaffordable
#print axioms Witness.eU
#print axioms Witness.unaffordable_W1
#print axioms Witness.unaffordable_witness
#print axioms Witness.affordable
#print axioms Witness.affordable_W1
#print axioms Witness.affordable_witness
#print axioms HonestExp
#print axioms noise
#print axioms NoiseBounded
#print axioms honest_implies_exp
#print axioms noise_free_bounded
#print axioms underpromise_le_of_feasible_exp
#print axioms tracker_wealth_ge_exp
#print axioms tracker_feasible_exp
#print axioms competitive_of_honest_tracker_exp
#print axioms competitive_of_affordable_tracker_exp
#print axioms rate_le_of_honest_tracker_exp
#print axioms trackerAllowance2
#print axioms trackerAllowance2_nonneg
#print axioms trackerAllowance2_total
#print axioms trackerAllowance2_covers
#print axioms trackerAllowance2_zero
#print axioms subgaussian_tail
#print axioms subgaussian_two_sided
#print axioms azuma_selected_tail
#print axioms Witness.own_proposal_insufficient
#print axioms Witness.noisy_honesty_witness
#print axioms evalOf_le_bid
#print axioms eval_sub_score_ii
#print axioms eval_sub_score_i
#print axioms rescale_sub
#print axioms exchange_rate_invariant
#print axioms violation_rate_le_exchange_mul
#print axioms violation_rate_le_exchange
#print axioms violation_rate_le_exchange_rescaled
#print axioms design_consistent
#print axioms noise_increment_le
#print axioms realized_range
#print axioms tolerated_rate_band
#print axioms priced_risk_wins_iff
#print axioms total_wealth_le_of_tracker
#print axioms Witness.sum_periodic5
#print axioms Witness.incP
#print axioms Witness.xiP
#print axioms Witness.xiP_periodic
#print axioms Witness.constantRisk
#print axioms Witness.constantRisk_W
#print axioms Witness.constantRisk_feasible
#print axioms Witness.nonincident_noise_linear
#print axioms Witness.incidents_constant_rate
#print axioms Witness.all_blocks_noise_bounded
#print axioms Witness.nonincident_forces_linear
#print axioms Witness.signed_bound_allows_constant_rate
#print axioms Witness.constantRisk_facts

end Workspace.Deference.Contrib.BRIAFollowup2
