import Cleanroom.Decision.DpEdtUdtFair.Theorem3
import Cleanroom.Decision.DpEdtUdtFair.Trees
import Cleanroom.Decision.DpCalibration.MiniDevices

/-!
# Inhabitants of `𝔉` and the witnesses of Theorem 3, FR-12 and the threat tree's D2 verdict

* `twoPoint r₀ r₁ r₂ ∈ 𝔉` for every payoff triple (T1(b)): recording at `p1` and `p2` for every
  procedure, pruned, both observations realized; `Q` on `twoPoint` in closed form; the tremble of
  `proc2` is a `proc2`.
* `dupPay ra rb ∈ 𝔉` with a **two-member fiber** (T1(b), the witness Claim B says must be
  un-evented — and it is: `dupPay_not_eventedChance`).
* T4's witnesses: `inX` on `fantasy241` is D2-consistent and optimal (N+); `ofFun a` on
  `dupPay 1 0` is D2-consistent and optimal on a two-member fiber (N+); on `twoPoint 4 4 4` every
  procedure is D2-consistent and optimal (N−).
* T6(a), FR-12: on `fr12 = (0; 0, −1)`, `IsOptimal (proc2 p q) ↔ p = 1 ∨ q = 1` and
  `D2 (proc2 p q) ↔ p = 1 ∧ q = 1`: `∅ ≠ {D2} = {(out, x)} ⊊ {optimal}` on one tree; the
  **refuted** row for "optimal ⟹ D2" (`outY` is optimal and D2-rejected).
* T8's D2 clause: `(a, y)` on `threat` is D2-rejected (`x → 2 > 0 ← y`) and not optimal
  (`1 < 2`).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

/-! ### `twoPoint` is in `𝔉` -/

section twoPoint

variable (r₀ r₁ r₂ : ℚ)

/-- `twoPoint` records at `p1` for every procedure: every path passes the root once, `O_{p1} = ⊤`,
and the world (`out` / `inX` / `inY`) satisfies exactly the act event of the edge taken.
Source: `fair-repair.md` §3.2 (the two-point shape, "evented and recorded"); mandate T1(b)
Kind: N+ -/
theorem twoPoint_recordsForAll_p1 :
    RecordsForAll twoObs twoActEv (twoPoint r₀ r₁ r₂) .p1 := by
  intro C ℓ _ _
  unfold twoPoint at ℓ ⊢
  refine ⟨?_, ?_⟩
  · rcases ℓ with ⟨a, ℓ⟩
    cases a
    · simp [count_decision, count_leaf]
    · rcases ℓ with ⟨b, _⟩
      cases b <;> simp [count_decision, count_leaf]
  · rintro (_ | ⟨b, q⟩) hq a ha
    · rcases ℓ with ⟨a', ℓ⟩
      simp only [edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨fun _ _ => by simp [twoObs], ?_, ?_⟩
      · cases a'
        · simp [twoActEv, world_decision, world_leaf]
        · rcases ℓ with ⟨b, _⟩
          cases b <;> simp [twoActEv, world_decision, world_leaf]
      · intro a'' ha''
        cases a'
        · cases a'' <;> simp [twoActEv, world_decision, world_leaf] at ha'' ⊢
        · rcases ℓ with ⟨b, _⟩
          cases b <;> cases a'' <;> simp [twoActEv, world_decision, world_leaf] at ha'' ⊢
    · cases b
      · exact q.elim
      · rcases q with _ | ⟨c, q'⟩
        · simp [pt] at hq
        · cases c <;> exact q'.elim

/-- `twoPoint` records at `p2` for every procedure: the `O_{p2}`-leaves are the two leaves below
the `p2`-node, which is subtree-veridical and action-veridical.
Source: `fair-repair.md` §3.2 ("`O_2 =` the act-event 'in', evented and recorded"); mandate T1(b)
Kind: N+ -/
theorem twoPoint_recordsForAll_p2 :
    RecordsForAll twoObs twoActEv (twoPoint r₀ r₁ r₂) .p2 := by
  intro C ℓ _ hobs
  unfold twoPoint at ℓ hobs ⊢
  rcases ℓ with ⟨a, ℓ⟩
  cases a
  · simp [twoObs, world_decision, world_leaf] at hobs
  · rcases ℓ with ⟨b, _⟩
    refine ⟨by cases b <;> simp [count_decision, count_leaf], ?_⟩
    rintro (_ | ⟨c, q⟩) hq a ha
    · simp [pt] at hq
    · cases c
      · exact q.elim
      · rcases q with _ | ⟨c', q'⟩
        · simp only [edgeOf_decision_some, dite_true, edgeOf_decision_none,
            Option.some.injEq] at ha
          subst ha
          refine ⟨?_, ?_, ?_⟩
          · rintro ⟨a', ℓ'⟩ hℓ'
            rw [mem_leavesBelow] at hℓ'
            cases a'
            · simp [edgeOf_decision_some] at hℓ'
            · rcases ℓ' with ⟨b', _⟩
              cases b' <;> simp [twoObs, pt, world_decision, world_leaf]
          · cases b <;> simp [twoActEv, pt, world_decision, world_leaf]
          · intro a'' ha''
            cases b <;> cases a'' <;> simp [twoActEv, pt, world_decision, world_leaf] at ha'' ⊢
        · cases c' <;> exact q'.elim

/-- `twoPoint` is pruned (no chance nodes).
Source: none: infrastructure
Kind: L -/
theorem twoPoint_pruned : Pruned (twoPoint r₀ r₁ r₂) := by
  rintro ⟨a, ℓ⟩
  unfold Positive
  cases a
  · simp [twoPoint, chanceWeight_decision, chanceWeight_leaf]
  · rcases ℓ with ⟨b, _⟩
    cases b <;> simp [twoPoint, chanceWeight_decision, chanceWeight_leaf]

/-- Both observations of `twoPoint` are realized.
Source: `adversary-repair.md` Claim A (the added hypothesis, checked on the two-point shape)
Kind: L -/
theorem twoPoint_realized : ∀ d ∈ queried (twoPoint r₀ r₁ r₂), Realized twoObs (twoPoint r₀ r₁ r₂) d := by
  intro d _
  cases d
  · exact ⟨⟨.a, ()⟩, by simp [Positive, twoPoint, chanceWeight_decision, chanceWeight_leaf],
      by simp [twoObs]⟩
  · exact ⟨⟨.b, .a, ()⟩, by simp [Positive, twoPoint, chanceWeight_decision, chanceWeight_leaf],
      by simp [twoObs, twoPoint, world_decision, world_leaf]⟩

/-- **Every `twoPoint` tree is in `𝔉`** (with `twoObs`, `twoActEv`).
Source: `fair-repair.md` §3.2; `calibration.md` l. 9; mandate T1(b)
Kind: N+ -/
theorem twoPoint_fairClass : FairClass twoObs twoActEv (twoPoint r₀ r₁ r₂) where
  stronglyFair := twoPoint_stronglyFair r₀ r₁ r₂
  frec := fun d _ => by
    cases d
    · exact twoPoint_recordsForAll_p1 r₀ r₁ r₂
    · exact twoPoint_recordsForAll_p2 r₀ r₁ r₂
  pruned := twoPoint_pruned r₀ r₁ r₂
  realized := twoPoint_realized r₀ r₁ r₂

/-- `Q` at `p1`: `Q(p1, out) = r₀`.
Source: mandate T4 (the two-point numbers)
Kind: L -/
theorem twoPoint_Q_p1_a (C : Proc Pt2 (fun _ => Act2) ℚ) :
    Q C (twoPoint r₀ r₁ r₂) .p1 .a = r₀ := by
  rw [← stronglyFair_value_eq_Q (twoPoint_stronglyFair r₀ r₁ r₂) C (q := none) (d := .p1)
    (c := fun x => match x with
      | .a => .leaf .out r₀
      | .b => .decision .p2 fun y => match y with | .a => .leaf .inX r₁ | .b => .leaf .inY r₂) rfl]
  simp [DpLocalOpt.value_leaf]

/-- `Q` at `p1`: `Q_C(p1, in) = C(p2)(x) r₁ + C(p2)(y) r₂`.
Source: mandate T4
Kind: L -/
theorem twoPoint_Q_p1_b (C : Proc Pt2 (fun _ => Act2) ℚ) :
    Q C (twoPoint r₀ r₁ r₂) .p1 .b = (C .p2).w .a * r₁ + (C .p2).w .b * r₂ := by
  rw [← stronglyFair_value_eq_Q (twoPoint_stronglyFair r₀ r₁ r₂) C (q := none) (d := .p1)
    (c := fun x => match x with
      | .a => .leaf .out r₀
      | .b => .decision .p2 fun y => match y with | .a => .leaf .inX r₁ | .b => .leaf .inY r₂) rfl]
  simp [DpLocalOpt.value_decision, DpLocalOpt.value_leaf, Act2.sum_univ]

/-- `Q` at `p2`: `Q(p2, x) = r₁`. Source: mandate T4. Kind: L -/
theorem twoPoint_Q_p2_a (C : Proc Pt2 (fun _ => Act2) ℚ) :
    Q C (twoPoint r₀ r₁ r₂) .p2 .a = r₁ := by
  rw [← stronglyFair_value_eq_Q (twoPoint_stronglyFair r₀ r₁ r₂) C (q := some ⟨.b, none⟩)
    (d := .p2) (c := fun y => match y with | .a => .leaf .inX r₁ | .b => .leaf .inY r₂) rfl]
  simp [DpLocalOpt.value_leaf]

/-- `Q` at `p2`: `Q(p2, y) = r₂`. Source: mandate T4. Kind: L -/
theorem twoPoint_Q_p2_b (C : Proc Pt2 (fun _ => Act2) ℚ) :
    Q C (twoPoint r₀ r₁ r₂) .p2 .b = r₂ := by
  rw [← stronglyFair_value_eq_Q (twoPoint_stronglyFair r₀ r₁ r₂) C (q := some ⟨.b, none⟩)
    (d := .p2) (c := fun y => match y with | .a => .leaf .inX r₁ | .b => .leaf .inY r₂) rfl]
  simp [DpLocalOpt.value_leaf]

end twoPoint

/-- **The tremble of `proc2 p q` is `proc2 p_ε q_ε`**, `p_ε = (1−ε)p + ε/2` (`|A_d| = 2`).
Source: `calibration.md` CA-14′ (`q_ε = (1−ε)q + ε/2`); `dp-calibration`'s `tremble_procQ`
Kind: L -/
theorem tremble_proc2 (p q ε : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    tremble (proc2 p q hp0 hp1 hq0 hq1) ε h0 h1 =
      proc2 ((1 - ε) * p + ε / 2) ((1 - ε) * q + ε / 2)
        (qeps_mem p ε hp0 hp1 h0 h1).1 (qeps_mem p ε hp0 hp1 h0 h1).2
        (qeps_mem q ε hq0 hq1 h0 h1).1 (qeps_mem q ε hq0 hq1 h0 h1).2 := by
  funext d
  cases d <;> apply FinDistr.ext' <;> intro a <;> cases a <;>
    simp [tremble_w, proc2, FinDistr.act2, Act2.univ_eq, Fintype.card] <;> ring

/-! ### T4's witnesses on `twoPoint` -/

section fantasy

/-- **`(in, x)` on `fantasy241` is event-tremble-EDT-consistent** (D2), in `Q`-form: at `p1`,
`2 ≤ 4 − 3ε/2` for `ε ≤ 1`; at `p2`, `1 ≤ 4`.
Source: mandate T4 ("`inX` on `fantasy241`: D2 holds at both points: `out → 2 < 4 − 3ε/2`;
`x → 4 > 1`")
Kind: N+ -/
theorem fantasy_inX_eventTremble : EventTrembleEdtConsistent twoObs twoActEv inX fantasy241 := by
  unfold fantasy241
  rw [(twoPoint_fairClass 2 4 1).eventTremble_iff_Q]
  refine ⟨1, one_pos, fun ε h0 h1 _ d _ a ha b => ?_⟩
  unfold inX
  rw [tremble_proc2]
  cases d <;> cases a <;> cases b <;>
    simp [twoPoint_Q_p1_a, twoPoint_Q_p1_b, twoPoint_Q_p2_a, twoPoint_Q_p2_b, proc2,
      FinDistr.act2] at ha ⊢ <;> nlinarith

/-- **T4's N+ witness**: `(in, x)` on `fantasy241 ∈ 𝔉` is D2-consistent and (by Theorem 3, and
by direct computation) optimal, with `V = 4`; the hypothesis package of Theorem 3 is inhabited
non-degenerately (the optimum beats `(out, y)`'s `2`).
Source: mandate T4 (witness); A32 (the fantasy tree's optimum `(in, x)`)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem fantasy_inX_theorem3_witness :
    FairClass twoObs twoActEv fantasy241 ∧ EventTrembleEdtConsistent twoObs twoActEv inX fantasy241 ∧
    IsOptimal inX fantasy241 ∧ value inX fantasy241 = 4 ∧ value outY fantasy241 = 2 := by
  refine ⟨twoPoint_fairClass 2 4 1, fantasy_inX_eventTremble,
    eventTrembleEdt_isOptimal_of_fairClass (twoPoint_fairClass 2 4 1) fantasy_inX_eventTremble,
    ?_, ?_⟩
  · unfold inX fantasy241; rw [twoPoint_value]; norm_num
  · unfold outY fantasy241; rw [twoPoint_value]; norm_num

/-- **T4's N− check**: on `twoPoint 4 4 4` every procedure is D2-consistent and optimal (constant
payoffs) — the degenerate case the `dupPay` witness must avoid (`ra ≠ rb`).
Source: mandate T4 ("N−: on `twoPoint 4 4 4` every procedure is D2-consistent and optimal")
Kind: N−
Fidelity: exact -/
theorem twoPoint444_all (C : Proc Pt2 (fun _ => Act2) ℚ) :
    EventTrembleEdtConsistent twoObs twoActEv C (twoPoint 4 4 4) ∧ IsOptimal C (twoPoint 4 4 4) := by
  have hD2 : EventTrembleEdtConsistent twoObs twoActEv C (twoPoint 4 4 4) := by
    rw [(twoPoint_fairClass 4 4 4).eventTremble_iff_Q]
    refine ⟨1, one_pos, fun ε h0 h1 _ d _ a _ b => ?_⟩
    have hs : (tremble C ε h0.le h1 .p2).w .a + (tremble C ε h0.le h1 .p2).w .b = 1 := by
      rw [← Act2.sum_univ]; exact (tremble C ε h0.le h1 .p2).sum_one
    cases d <;> cases a <;> cases b <;>
      simp only [twoPoint_Q_p1_a, twoPoint_Q_p1_b, twoPoint_Q_p2_a, twoPoint_Q_p2_b] <;> linarith
  exact ⟨hD2, eventTrembleEdt_isOptimal_of_fairClass (twoPoint_fairClass 4 4 4) hD2⟩

end fantasy

/-! ### FR-12: the strict converse on `fr12` (T6(a)) -/

section fr12

variable (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)

/-- `V_{fr12}(p, q) = −(1 − p)(1 − q)`. Source: `fair-repair.md` FR-12. Kind: L -/
theorem fr12_value : value (proc2 p q hp0 hp1 hq0 hq1) fr12 = -((1 - p) * (1 - q)) := by
  unfold fr12; rw [twoPoint_value]; ring

/-- **The optimal set on `fr12`**: `proc2 p q` is optimal iff `p = 1 ∨ q = 1` (value `0`).
Source: `fair-repair.md` FR-12 ("`(out, y)` is `V`-optimal (`V = 0 = max`)"); mandate T6(a)
Kind: P -/
theorem fr12_isOptimal_iff :
    IsOptimal (proc2 p q hp0 hp1 hq0 hq1) fr12 ↔ p = 1 ∨ q = 1 := by
  rw [isOptimal_proc2_iff]
  constructor
  · intro h
    have := h 1 1 zero_le_one le_rfl zero_le_one le_rfl
    rw [fr12_value, fr12_value] at this
    by_contra hne
    push Not at hne
    have h1 : 0 < 1 - p := by rcases lt_or_eq_of_le hp1 with h | h <;> [linarith; exact absurd h hne.1]
    have h2 : 0 < 1 - q := by rcases lt_or_eq_of_le hq1 with h | h <;> [linarith; exact absurd h hne.2]
    nlinarith [mul_pos h1 h2]
  · intro h r s r0 r1 s0 s1
    rw [fr12_value, fr12_value]
    rcases h with h | h <;> subst h <;> nlinarith [mul_nonneg (sub_nonneg.mpr r1) (sub_nonneg.mpr s1)]

/-- **The D2-consistent set on `fr12`**: `proc2 p q` is event-tremble-EDT-consistent iff
`p = 1 ∧ q = 1` — i.e. `{D2} = {(out, x)}`. At `p2`, `x` (`0`) beats `y` (`−1`) at every `ε`, so
`supp C(p2) = {x}`; then at `p1`, `out` (`0`) beats `in` (`−(1 − q_ε) < 0`).
Source: `fair-repair.md` FR-12 ("`T_EDT` rejects `y` at every `ε`"); `adversary-repair.md` A.3;
mandate T6(a) ("the exact sets: `{D2} = {(out, x)}`")
Kind: P -/
theorem fr12_eventTremble_iff :
    EventTrembleEdtConsistent twoObs twoActEv (proc2 p q hp0 hp1 hq0 hq1) fr12 ↔ p = 1 ∧ q = 1 := by
  unfold fr12
  rw [(twoPoint_fairClass 0 0 (-1)).eventTremble_iff_Q]
  constructor
  · rintro ⟨ε₀, hε₀, hQ⟩
    set ε := min (ε₀ / 2) 1 with hε
    have h0 : 0 < ε := lt_min (by linarith) one_pos
    have h1 : ε ≤ 1 := min_le_right _ _
    have hlt : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith)
    have hq : q = 1 := by
      by_contra hne
      have hqpos : 0 < (proc2 p q hp0 hp1 hq0 hq1 .p2).w .b := by
        simp [proc2, FinDistr.act2]; rcases lt_or_eq_of_le hq1 with h | h <;> [linarith; exact absurd h hne]
      have := hQ ε h0 h1 hlt .p2 (twoPoint_queried 0 0 (-1)).2 .b hqpos .a
      rw [twoPoint_Q_p2_a, twoPoint_Q_p2_b] at this
      norm_num at this
    subst hq
    refine ⟨?_, rfl⟩
    by_contra hne
    have hppos : 0 < (proc2 p 1 hp0 hp1 hq0 hq1 .p1).w .b := by
      simp [proc2, FinDistr.act2]; rcases lt_or_eq_of_le hp1 with h | h <;> [linarith; exact absurd h hne]
    have := hQ ε h0 h1 hlt .p1 (twoPoint_queried 0 0 (-1)).1 .b hppos .a
    rw [tremble_proc2, twoPoint_Q_p1_a, twoPoint_Q_p1_b] at this
    simp [proc2, FinDistr.act2] at this
    nlinarith
  · rintro ⟨rfl, rfl⟩
    refine ⟨1, one_pos, fun ε h0 h1 _ d _ a ha b => ?_⟩
    rw [tremble_proc2]
    cases d <;> cases a <;> cases b <;>
      simp [twoPoint_Q_p1_a, twoPoint_Q_p1_b, twoPoint_Q_p2_a, twoPoint_Q_p2_b, proc2,
        FinDistr.act2] at ha ⊢ <;> nlinarith

/-- **FR-12 (refuted row for "optimal ⟹ D2")**: on `fr12 ∈ 𝔉`, `(out, y)` is optimal (`V = 0`)
and not event-tremble-EDT-consistent; hence `∅ ≠ {D2} = {(out, x)} ⊊ {optimal} ∋ (out, y), (in, x)`
on one tree — the inclusion of Theorem 3 is strict. Quoted claim refuted: the converse "optimal ⟹
tremble-EDT-consistent", which no source asserts and FR-12 denies; reading: the two sets coincide
on `𝔉`; surviving neighbour: Theorem 3's inclusion.
Source: `fair-repair.md` FR-12 ("optimal but not tremble-EDT-consistent"); `adversary-repair.md`
A.3 ("FR-12 SURVIVES"); A36 (i)(ii); mandate T6(a)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem fr12_outY_isOptimal_not_eventTremble :
    FairClass twoObs twoActEv fr12 ∧ IsOptimal outY fr12 ∧
    ¬ EventTrembleEdtConsistent twoObs twoActEv outY fr12 ∧
    EventTrembleEdtConsistent twoObs twoActEv (proc2 1 1 zero_le_one le_rfl zero_le_one le_rfl) fr12 ∧
    IsOptimal (proc2 1 1 zero_le_one le_rfl zero_le_one le_rfl) fr12 ∧
    IsOptimal inX fr12 ∧ value outY fr12 = 0 := by
  refine ⟨twoPoint_fairClass 0 0 (-1), (fr12_isOptimal_iff 1 0 _ _ _ _).mpr (Or.inl rfl),
    fun h => ?_, (fr12_eventTremble_iff 1 1 _ _ _ _).mpr ⟨rfl, rfl⟩,
    (fr12_isOptimal_iff 1 1 _ _ _ _).mpr (Or.inl rfl),
    (fr12_isOptimal_iff 0 1 _ _ _ _).mpr (Or.inr rfl), by unfold outY; rw [fr12_value]; ring⟩
  have := (fr12_eventTremble_iff 1 0 zero_le_one le_rfl le_rfl zero_le_one).mp h
  norm_num at this

end fr12

/-! ### The threat tree's D2 verdict (T8, the tremble clause) -/

/-- **D2 rejects `(a, y)` on the threat tree**: at `p2`, `Q(x) = 2 > 0 = Q(y)` at every `ε`; and
`(a, y)` is not optimal (`V = 1 < 2 = V(in, x)`).
Source: `identity.md` ID-22 (M0) ("dissolved by trembles alone (FR-11)"); ID-23 rider (a′);
mandate T8
Kind: N+ -/
theorem threat_outY_not_eventTremble :
    ¬ EventTrembleEdtConsistent twoObs twoActEv outY threat ∧ ¬ IsOptimal outY threat ∧
    value outY threat = 1 ∧ value inX threat = 2 := by
  refine ⟨fun h => ?_, fun h => ?_, ?_, ?_⟩
  · unfold threat at h
    rw [(twoPoint_fairClass 1 2 0).eventTremble_iff_Q] at h
    obtain ⟨ε₀, hε₀, hQ⟩ := h
    have := hQ (min (ε₀ / 2) 1) (lt_min (by linarith) one_pos) (min_le_right _ _)
      ((min_le_left _ _).trans_lt (by linarith)) .p2 (twoPoint_queried 1 2 0).2 .b
      (by simp [outY, proc2, FinDistr.act2]) .a
    rw [twoPoint_Q_p2_a, twoPoint_Q_p2_b] at this
    norm_num at this
  · have := h inX
    unfold inX outY threat at this
    rw [twoPoint_value, twoPoint_value] at this
    norm_num at this
  · unfold outY threat; rw [twoPoint_value]; norm_num
  · unfold inX threat; rw [twoPoint_value]; norm_num

/-! ### `dupPay` is in `𝔉` with a two-member fiber -/

section dupPay

variable (ra rb : ℚ)

/-- Every decision node of `dupPay` has subtree `dupNode ra rb`.
Source: none: infrastructure
Kind: L -/
theorem dupPay_subtree (q : (dupPay ra rb).DecNode) : subtreeAt (dupPay ra rb) q = dupNode ra rb := by
  obtain ⟨i, q⟩ := q
  rcases q with _ | ⟨x, q'⟩
  · rfl
  · cases x <;> exact q'.elim

/-- `dupPay` is strongly fair (both members have the same subtree).
Source: mandate T1(b)
Kind: L -/
theorem dupPay_stronglyFair : StronglyFair (dupPay ra rb) := by
  intro d q _ q' _
  rw [dupPay_subtree, dupPay_subtree]
  exact LabIso.refl _

/-- `dupPay` records at its point for every procedure (`O = ⊤`; the world is the drawn act).
Source: mandate T1(b)
Kind: N+ -/
theorem dupPay_recordsForAll : RecordsForAll dupPayObs dupPayActEv (dupPay ra rb) () := by
  intro C ℓ _ _
  unfold dupPay dupNode at ℓ ⊢
  rcases ℓ with ⟨i, x, _⟩
  refine ⟨by simp [count_chance, count_decision, count_leaf], ?_⟩
  rintro ⟨i', (_ | ⟨y, q⟩)⟩ hq a ha
  · by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨fun _ _ => by simp [dupPayObs], ?_, ?_⟩
      · simp [dupPayActEv, world_chance, world_decision, world_leaf]
      · intro a' ha'
        simp [dupPayActEv, world_chance, world_decision, world_leaf] at ha'
        exact ha'.symm
    · simp [edgeOf_chance, hi] at ha
  · cases y <;> exact q.elim

/-- `dupPay` is pruned (a fair coin).
Source: none: infrastructure
Kind: L -/
theorem dupPay_pruned : Pruned (dupPay ra rb) := by
  rintro ⟨i, x, _⟩
  unfold Positive dupPay dupNode
  simp only [chanceWeight_chance, chanceWeight_decision, chanceWeight_leaf, mul_one]
  fin_cases i <;> simp [FinDistr.fair, FinDistr.coin] <;> norm_num

/-- **`dupPay ra rb ∈ 𝔉`**.
Source: mandate T1(b) ("`dupPay ra rb ∈ 𝔉` with a two-member fiber")
Kind: N+ -/
theorem dupPay_fairClass : FairClass dupPayObs dupPayActEv (dupPay ra rb) where
  stronglyFair := dupPay_stronglyFair ra rb
  frec := fun d _ => by cases d; exact dupPay_recordsForAll ra rb
  pruned := dupPay_pruned ra rb
  realized := fun d _ => by
    cases d
    exact ⟨⟨0, .a, ()⟩, dupPay_pruned ra rb _, by simp [dupPayObs]⟩

/-- **The fiber of `dupPay` has two members**: `⟨0, none⟩ ≠ ⟨1, none⟩`, both carrying `d`.
Source: mandate T1(b), T4 ("two-member fiber")
Kind: N+ -/
theorem dupPay_two_member_fiber :
    (⟨0, none⟩ : (dupPay ra rb).DecNode) ∈ fiber (dupPay ra rb) () ∧
    (⟨1, none⟩ : (dupPay ra rb).DecNode) ∈ fiber (dupPay ra rb) () ∧
    (⟨0, none⟩ : (dupPay ra rb).DecNode) ≠ ⟨1, none⟩ := by
  refine ⟨(mem_fiber _ _ _).mpr rfl, (mem_fiber _ _ _).mpr rfl, fun h => ?_⟩
  have h01 : (0 : Fin 2) = 1 := congrArg Sigma.fst h
  exact absurd h01 (by decide)

/-- **`dupPay` is not evented** (Claim B's price for a two-member fiber): the two coin branches
carry the same worlds.
Source: `adversary-repair.md` Claim B; mandate known issue 10
Kind: N+ -/
theorem dupPay_not_eventedChance : ¬ EventedChance (dupPay ra rb) := by
  intro h
  unfold dupPay at h
  have := h.1 0 1 (by decide) ⟨.a, ()⟩ ⟨.a, ()⟩
  exact this rfl

/-- `Q` on `dupPay`: `Q(d, a) = ra`, `Q(d, b) = rb`.
Source: mandate T4
Kind: L -/
theorem dupPay_Q (C : Proc Unit (fun _ => Act2) ℚ) :
    Q C (dupPay ra rb) () .a = ra ∧ Q C (dupPay ra rb) () .b = rb := by
  constructor <;>
  · rw [← stronglyFair_value_eq_Q (dupPay_stronglyFair ra rb) C (q := ⟨0, none⟩) (d := ())
      (c := fun x => .leaf x (if x = .a then ra else rb)) rfl]
    simp [DpLocalOpt.value_leaf]

/-- **T4's two-member-fiber witness**: on `dupPay 1 0 ∈ 𝔉` (fiber of size two), `δ_a` is
D2-consistent and optimal (`V = 1`), while `δ_b` (`V = 0`) is not — non-degenerate.
Source: mandate T4 ("`ofFun (fun _ => a)` on `dupPay 1 0` (two-member fiber)")
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem dupPay_theorem3_witness :
    EventTrembleEdtConsistent dupPayObs dupPayActEv (Proc.ofFun fun _ => Act2.a) (dupPay 1 0) ∧
    IsOptimal (Proc.ofFun fun _ => Act2.a) (dupPay 1 0) ∧
    value (Proc.ofFun fun _ => Act2.a) (dupPay 1 0) = 1 ∧
    ¬ IsOptimal (Proc.ofFun fun _ => Act2.b) (dupPay 1 0) := by
  have hD2 : EventTrembleEdtConsistent dupPayObs dupPayActEv (Proc.ofFun fun _ => Act2.a)
      (dupPay 1 0) := by
    rw [(dupPay_fairClass 1 0).eventTremble_iff_Q]
    refine ⟨1, one_pos, fun ε h0 h1 _ d _ a ha b => ?_⟩
    cases d
    cases a <;> cases b <;> simp [(dupPay_Q 1 0 _).1, (dupPay_Q 1 0 _).2, Proc.ofFun_w] at ha ⊢
  have hpa : (Proc.ofFun fun _ => Act2.a : Proc Unit (fun _ => Act2) ℚ) = procQ 1 zero_le_one le_rfl := by
    funext d; apply FinDistr.ext'; intro x; cases x <;> simp [Proc.ofFun, procQ, FinDistr.act2]
  have hpb : (Proc.ofFun fun _ => Act2.b : Proc Unit (fun _ => Act2) ℚ) = procQ 0 le_rfl zero_le_one := by
    funext d; apply FinDistr.ext'; intro x; cases x <;> simp [Proc.ofFun, procQ, FinDistr.act2]
  refine ⟨hD2, eventTrembleEdt_isOptimal_of_fairClass (dupPay_fairClass 1 0) hD2, ?_, fun h => ?_⟩
  · rw [hpa, dupPay_value]; norm_num
  · have := h (Proc.ofFun fun _ => Act2.a)
    rw [hpa, hpb, dupPay_value, dupPay_value] at this
    norm_num at this

end dupPay

end Cleanroom.Decision.DpEdtUdtFair
