/-
# Warrant entitlement: the licence chain, the grounded survivors, the settlement fork, and the record

Rounds `projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/` (Parts A–C),
`2026-10-21-rebuttal-and-end-to-end/` (rebuttal by settlement) and
`2026-10-22-normative-inductor-integration/` (the grounded survivors and the canonical bundle).

1. **The typed warrant and the survivors.**  A warrant occurrence (`Occurrence`) is a
   `Form` with an identity, the applicability claim it cites, a source and a defeat set.
   `settleOutcome` applies the rulings on settlement: a form whose consequent is pinned
   false is *rebutted*, whose antecedent is pinned false is *vacuous*, a premise on a
   pinned-false sentence is *retired*.  **The survivors** (`Grounds.survivors`) are the
   occurrences that are not undercut by the docket, kept by the settlement, and cite a
   survivor — the least fixed point of `activeStep` (`activeIds_fixed`, `mem_survivors`),
   antitone in the settlement and in the docket (`survivors_anti`,
   `survivors_anti_docket`).  Their specialized rows together with the settlement's pins
   are **the settled bundle** (`Grounds.settledBundle`), whose region is
   `Grounds.settledRegion`; the licence, the elimination, the enforcer and the record all
   read it.  `Grounds.region` is the region of every undefeated-port row regardless of
   settlement outcome, the comparison object of the countermodels
   (`Fixture.orphan_region_nonempty`, `Fixture2.old_rule_empty`, `EndToEndWitness.Run.old_rule_pins`).

2. **The licence chain (Part A).**  A verdict is a value for a coordinate.  `Admissible`:
   the settled region contains a point with that value.  `Supported`: a `VerdictCert` — two
   `BoundCert`s whose positive-multiplier rows are cited **by occurrence** into the settled
   bundle, plus the two attained endpoints — brackets the verdict.  `Licensed`: `Supported`
   on the record's grounds, and the issuing event is one the record authorizes.
   `licensed_supported`, `supported_admissible` (through rational convexity of
   `Bundle.Region`, `region_convex`).  The two converses fail:
   `Countermodel.admissible_not_supported` (a stale citation after defeat of one of two
   duplicating occurrences; the region is unchanged) and
   `Countermodel.supported_not_licensed` (an unauthorized selection inside a forced
   interval of positive width, an instance of `GateIsLegitimacy.tiebreak_transparency`:
   `Countermodel.selection_not_transparent`).

3. **The settlement fork (Part B).**  The enforcer is the force layer's compiled position
   on a date-indexed presentation (`warrantEnforcer`).  **The odds bankroll**
   (`netWorth_ge_neg_odds`): if at date `n` some live world clears every enforced row of
   every date `t ≤ n` with a surplus dominating every live world's deficit on that row by
   the factor `ρ`, then the enforcer's assessed net worth at every live world is at least
   `−3ρ` — the market maker's constant `1` plus the trading firm's floor `2`, times the
   odds.  Across one reopening, `−3ρ(2 + ρ)` (`netWorth_ge_neg_odds_reopened`).  Composed
   with the conditional Normative Inductor theorem as `warrant_normative_inductor`.  The
   fixture `Fixture`: four sentences `X, X∧A, X∧A∧Y, Y`, one warrant with strengths
   `c_P, c_A, c_S ∈ (0,1)`, `X` settled at `n₁`, the applicability port defeated at `n₀`,
   `Y` settled by a declared evaluation at `n_E`.  Under `Grounds.region` the refutation
   leaves an orphan pin in a nonempty region with no slack world
   (`Fixture.orphan_region_nonempty`, `Fixture.orphan_no_slack`); under the survivors the
   strength row leaves with the applicability it cites (`Fixture.survivors_eq`) and the
   bankroll holds across the rebuttal (`Fixture.liability_rebutted`).

4. **The record (Part C).**  `MarketRun`, `Record`, `trace`.  Prices are not in the
   record; the enforcer's position on the settled bundle is.  `trace_not_injOn` and
   `trace_not_const` on the fixture, and `Licensed` is decidable from the record
   (`instance : Decidable`).

Every structure has a nonvacuity witness in `Witness`.  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.NormativeInductionInterface
import Workspace.Normativity.Contrib.SeedStatics
import Workspace.Deference.Contrib.GateIsLegitimacy
import Workspace.Deference.Contrib.ReasonMediatedAuthorship

namespace Workspace.Normativity.Contrib.WarrantEntitlement

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Finset

variable {d : ℕ}

/-! ## Rational convexity of a bundle's region

The one fact about regions the licence chain needs beyond the port: a region is convex
over `ℚ`, so a value bracketed by two attained values is itself attained. -/

/-- The rational segment between two points. -/
def seg (x y : Fin d → ℚ) (t : ℚ) : Fin d → ℚ := fun i => (1 - t) * x i + t * y i

lemma Row.sat_seg {r : Row d} {x y : Fin d → ℚ} (hx : r.Sat x) (hy : r.Sat y) {t : ℚ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : r.Sat (seg x y t) := by
  unfold Row.Sat seg at *
  have : ∑ i, r.a i * ((1 - t) * x i + t * y i) =
      (1 - t) * ∑ i, r.a i * x i + t * ∑ i, r.a i * y i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  nlinarith

/-- **`Bundle.Region` is convex over `ℚ`.** -/
theorem region_convex {Q : Type*} {B : Bundle Q d} {x y : Fin d → ℚ} (hx : B.Region x)
    (hy : B.Region y) {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : B.Region (seg x y t) := by
  refine ⟨fun i => ?_, fun c hc => Row.sat_seg (hx.2 c hc) (hy.2 c hc) h0 h1⟩
  obtain ⟨hx0, hx1⟩ := hx.1 i
  obtain ⟨hy0, hy1⟩ := hy.1 i
  unfold seg
  constructor <;> nlinarith

/-- A value between two attained values of a coordinate is attained. -/
theorem region_attains_between {Q : Type*} {B : Bundle Q d} {φ : Fin d} {x y : Fin d → ℚ}
    (hx : B.Region x) (hy : B.Region y) {v : ℚ} (hxv : x φ ≤ v) (hvy : v ≤ y φ) :
    ∃ z, B.Region z ∧ z φ = v := by
  rcases eq_or_lt_of_le (hxv.trans hvy) with heq | hlt
  · exact ⟨x, hx, by linarith⟩
  · set t : ℚ := (v - x φ) / (y φ - x φ) with ht
    have hden : 0 < y φ - x φ := by linarith
    have h0 : 0 ≤ t := div_nonneg (by linarith) hden.le
    have h1 : t ≤ 1 := by
      rw [ht, div_le_one hden]; linarith
    refine ⟨seg x y t, region_convex hx hy h0 h1, ?_⟩
    unfold seg
    rw [ht]
    field_simp
    ring

/-! ## Part A — the typed warrant and the licence chain -/

/-- Where an occurrence's applicability claim comes from: another occurrence, a settled
coordinate, or nothing (a premise). -/
inductive Applicability (d : ℕ) where
  | occurrence (id : ℕ)
  | settled (i : Fin d)
  | none
  deriving DecidableEq

/-- Who entered the occurrence: a party, or a settlement event. -/
inductive Source where
  | party (p : ℕ)
  | settlement (event : ℕ)
  deriving DecidableEq

/-- **A warrant occurrence** (A1): a leverage form with an identity, the applicability
claim it cites, its source, and its defeat set — the ports whose defeat on the docket also
undercuts it, so that one warrant's forms share one defeat condition.  Its own docket port
is its identity. -/
structure Occurrence (d : ℕ) where
  id : ℕ
  form : Form d
  cites : Applicability d
  source : Source
  defeaters : Finset ℕ
  deriving DecidableEq

/-- The substantive item an occurrence contributes: its form on its own port. -/
def Occurrence.toSub (o : Occurrence d) : SubItem d := ⟨o.form, o.id⟩

/-- **Grounds**: the occurrences admitted to the record. -/
abbrev Grounds (d : ℕ) := List (Occurrence d)

/-- The seed a set of grounds presents: its substantive items, no structural layer. -/
def Grounds.seed (G : Grounds d) : Seed d Unit := ⟨G.map Occurrence.toSub, [], ⟨∅, ∅⟩⟩

/-- The live bundle of grounds under a docket and a settlement. -/
def Grounds.bundle (G : Grounds d) (st : DocketState) (F : Settlement d) : Bundle (Cite d) d :=
  forcedBundle G.seed [] st F

/-- The region the live grounds force. -/
def Grounds.region (G : Grounds d) (st : DocketState) (F : Settlement d) (x : Fin d → ℚ) :
    Prop := forcedRegion G.seed [] st F x

instance (G : Grounds d) (st : DocketState) (F : Settlement d) (x : Fin d → ℚ) :
    Decidable (G.region st F x) := by unfold Grounds.region; infer_instance

/-- **The region of grounds, by occurrence**: the cube, the settlement's pins, and the row
of every occurrence whose port the docket has not defeated. -/
theorem Grounds.region_iff (G : Grounds d) (st : DocketState) (F : Settlement d)
    (x : Fin d → ℚ) :
    G.region st F x ↔
      InCube x ∧ F.Pinned x ∧ ∀ o ∈ G, o.id ∉ st.defeated → o.form.row.Sat x := by
  unfold Grounds.region
  rw [forcedRegion_iff]
  have hstr : G.seed.liveStr st = [] := rfl
  rw [hstr]
  simp only [List.not_mem_nil, false_implies, implies_true, and_true, List.append_nil,
    Grounds.seed, Seed.liveSub, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hp, h⟩
    exact ⟨hc, hp, fun o ho hid => h o.toSub ⟨⟨o, ho, rfl⟩, hid⟩⟩
  · rintro ⟨hc, hp, h⟩
    refine ⟨hc, hp, ?_⟩
    rintro it ⟨⟨o, ho, rfl⟩, hport⟩
    exact h o ho hport

/-- **Membership in the live bundle, by occurrence**: a cited row is a live occurrence's
specialized row under that occurrence's citation, or a pin row under its coordinate. -/
theorem Grounds.mem_bundle_iff (G : Grounds d) (st : DocketState) (F : Settlement d)
    (c : CitedRow (Cite d) d) :
    c ∈ G.bundle st F ↔
      (∃ o ∈ G, o.id ∉ st.defeated ∧ c = ⟨Cite.sub o.id, specialize F o.form.row⟩) ∨
      (∃ i, ∃ r ∈ F.pinRowsAt i, c = ⟨Cite.settled i, r⟩) := by
  have hstr : G.seed.liveStr st = [] := rfl
  unfold Grounds.bundle forcedBundle
  rw [hstr]
  simp only [List.map_nil, List.append_nil, List.mem_append, List.mem_map, Grounds.seed,
    Seed.liveSub, List.mem_filter, decide_eq_true_eq, pinCited, List.mem_flatMap,
    List.mem_finRange, true_and]
  constructor
  · rintro (⟨it, ⟨⟨o, ho, rfl⟩, hport⟩, rfl⟩ | ⟨i, r, hr, rfl⟩)
    · exact Or.inl ⟨o, ho, hport, rfl⟩
    · exact Or.inr ⟨i, r, hr, rfl⟩
  · rintro (⟨o, ho, hport, rfl⟩ | ⟨i, r, hr, rfl⟩)
    · exact Or.inl ⟨o.toSub, ⟨⟨o, ho, rfl⟩, hport⟩, rfl⟩
    · exact Or.inr ⟨i, r, hr, rfl⟩

/-! ## Part A — revision: settlement outcomes and the grounded survivors

The rulings M1–M3 of `prompts/2026-10-21-rebuttal-and-end-to-end/PROMPT.md` as a function on
the typed occurrence: a form whose consequent coordinate is pinned false is **rebutted**,
whose antecedent coordinate is pinned false is **vacuous**, a premise whose sentence is
pinned false is **retired**; in every case the row leaves.  The occurrences that stay are
the **survivors**: not undercut by the docket, kept by the settlement, and citing a
survivor — the grounded rule.  The settled region is the region of the survivors'
specialized rows; monotonicity under settlement is restated for it. -/

section Rebuttal

/-- The outcome of settling a form. -/
inductive Outcome where
  | kept
  | rebutted
  | vacuous
  | retired
  deriving DecidableEq

/-- The settlement pins coordinate `i` false. -/
def pinsFalse (F : Settlement d) (i : Fin d) : Bool := F.val i == some false

lemma pinsFalse_iff (F : Settlement d) (i : Fin d) : pinsFalse F i = true ↔ F.val i = some false := by
  simp [pinsFalse]

/-- **`settleOutcome`** (M1, M2): vacuity is checked before rebuttal — a form that never
applied is not rebutted. -/
def settleOutcome (F : Settlement d) : Form d → Outcome
  | .premise X _ => if pinsFalse F X then .retired else .kept
  | .applicability X XA _ =>
      if pinsFalse F X then .vacuous else if pinsFalse F XA then .rebutted else .kept
  | .strength XA XAY _ =>
      if pinsFalse F XA then .vacuous else if pinsFalse F XAY then .rebutted else .kept

/-- **`settleForm`** (P1): the rows an occurrence contributes under a settlement — its
specialized row when kept, nothing otherwise. -/
def settleForm (F : Settlement d) (o : Occurrence d) : Option (List (Row d)) :=
  if settleOutcome F o.form = .kept then some [specialize F o.form.row] else none

/-- The degenerate shapes: a premise on a false sentence, or a conditional form with a
false antecedent or a false consequent. -/
def Degenerate (F : Settlement d) : Form d → Prop
  | .premise X _ => pinsFalse F X = true
  | .applicability X XA _ => pinsFalse F X = true ∨ pinsFalse F XA = true
  | .strength XA XAY _ => pinsFalse F XA = true ∨ pinsFalse F XAY = true

instance (F : Settlement d) (f : Form d) : Decidable (Degenerate F f) := by
  cases f <;> unfold Degenerate <;> infer_instance

lemma settleOutcome_eq_kept_iff (F : Settlement d) (f : Form d) :
    settleOutcome F f = .kept ↔ ¬ Degenerate F f := by
  cases f <;> simp [settleOutcome, Degenerate] <;> split_ifs <;> simp_all

/-- **`settleForm` keeps exactly the specialized rows of non-degenerate forms** (P1). -/
theorem settleForm_eq_some_iff (F : Settlement d) (o : Occurrence d) (rows : List (Row d)) :
    settleForm F o = some rows ↔ rows = [specialize F o.form.row] ∧ ¬ Degenerate F o.form := by
  unfold settleForm
  rw [← settleOutcome_eq_kept_iff]
  split_ifs with h <;> simp [h, eq_comm]

theorem settleForm_eq_none_iff (F : Settlement d) (o : Occurrence d) :
    settleForm F o = none ↔ Degenerate F o.form := by
  unfold settleForm
  by_cases h : settleOutcome F o.form = .kept
  · simp [h, (settleOutcome_eq_kept_iff F o.form).1 h]
  · simp only [h, if_false, true_iff]
    by_contra hd
    exact h ((settleOutcome_eq_kept_iff F o.form).2 hd)

/-- **M3, no discount.**  A kept form's row is the specialization of the form with its own
strength; `settleForm` never rewrites a strength. -/
theorem settleForm_strength (F : Settlement d) (o : Occurrence d) (rows : List (Row d))
    (h : settleForm F o = some rows) : rows = [specialize F o.form.row] :=
  ((settleForm_eq_some_iff F o rows).1 h).1

/-- **The contraposing shape.**  A strength row whose consequent is pinned false forces the
antecedent to zero at every pinned point: the row says "¬Y, so not X∧A". -/
theorem strength_contraposes (F : Settlement d) (XA XAY : Fin d) (c : ℚ) (hc : 0 < c)
    (hpin : F.val XAY = some false) (x : Fin d → ℚ) (hx : F.Pinned x)
    (hsat : (specialize F (Form.strength XA XAY c).row).Sat x) : x XA ≤ 0 := by
  rw [specialize_sat_iff F _ hx, Form.strength_sat_iff] at hsat
  have h0 : x XAY = 0 := by simpa [truth] using hx XAY false hpin
  rw [h0] at hsat
  nlinarith

/-- The same for an applicability row whose consequent is pinned false. -/
theorem applicability_contraposes (F : Settlement d) (X XA : Fin d) (c : ℚ) (hc : 0 < c)
    (hpin : F.val XA = some false) (x : Fin d → ℚ) (hx : F.Pinned x)
    (hsat : (specialize F (Form.applicability X XA c).row).Sat x) : x X ≤ 0 := by
  rw [specialize_sat_iff F _ hx, Form.applicability_sat_iff] at hsat
  have h0 : x XA = 0 := by simpa [truth] using hx XA false hpin
  rw [h0] at hsat
  nlinarith

/-- **Rebuttal removes exactly the contraposing rows**: a strength form is rebutted (and
not vacuous) iff its consequent is pinned false while its antecedent is not. -/
theorem settleOutcome_rebutted_iff (F : Settlement d) (XA XAY : Fin d) (c : ℚ) :
    settleOutcome F (.strength XA XAY c) = .rebutted ↔
      F.val XAY = some false ∧ ¬ F.val XA = some false := by
  simp only [settleOutcome]
  have h1 := pinsFalse_iff F XA
  have h2 := pinsFalse_iff F XAY
  split_ifs with ha hb <;> simp_all

/-! ### The survivors: the grounded rule

An occurrence is **active** when the docket does not undercut it — neither its own port nor
a port of its defeat set is defeated — its form is kept by `settleOutcome`, and the
applicability occurrence it cites is itself active.  The active identities are the least
fixed point of the step operator `activeStep`, reached from `∅` in `G.length` steps
(`activeIds_fixed`).  Retirement, vacuity, rebuttal and undercut propagate along citation
chains of every length with no closure requirement on the settlement; an occurrence whose
citation resolves to nothing, or whose citations run in a cycle, is inactive. -/

/-- The docket **undercuts** `o`: its own port, or a port of its defeat set, is defeated. -/
def undercut (st : DocketState) (o : Occurrence d) : Prop :=
  o.id ∈ st.defeated ∨ ∃ j ∈ o.defeaters, j ∈ st.defeated

instance (st : DocketState) (o : Occurrence d) : Decidable (undercut st o) := by
  unfold undercut; infer_instance

/-- The applicability claim `a` is grounded in the identity set `S`. -/
def citesIn (S : Finset ℕ) : Applicability d → Prop
  | .occurrence j => j ∈ S
  | .settled _ => True
  | .none => True

instance (S : Finset ℕ) (a : Applicability d) : Decidable (citesIn S a) := by
  cases a <;> unfold citesIn <;> infer_instance

lemma citesIn_iff (S : Finset ℕ) (a : Applicability d) :
    citesIn S a ↔ ∀ j, a = .occurrence j → j ∈ S := by
  cases a <;> simp [citesIn]

lemma citesIn_mono {S S' : Finset ℕ} (h : S ⊆ S') {a : Applicability d} (ha : citesIn S a) :
    citesIn S' a := by
  cases a <;> simp only [citesIn] at ha ⊢
  exact h ha

/-- `o` is **live given** the identity set `S`: not undercut, kept, and citing into `S`. -/
def liveGiven (st : DocketState) (F : Settlement d) (S : Finset ℕ) (o : Occurrence d) : Prop :=
  ¬ undercut st o ∧ settleOutcome F o.form = .kept ∧ citesIn S o.cites

instance (st : DocketState) (F : Settlement d) (S : Finset ℕ) (o : Occurrence d) :
    Decidable (liveGiven st F S o) := by
  unfold liveGiven; infer_instance

lemma liveGiven_mono {st : DocketState} {F : Settlement d} {S S' : Finset ℕ} (h : S ⊆ S')
    {o : Occurrence d} (ho : liveGiven st F S o) : liveGiven st F S' o :=
  ⟨ho.1, ho.2.1, citesIn_mono h ho.2.2⟩

/-- One step of the grounded operator: the identities of the occurrences live given `S`. -/
def activeStep (G : Grounds d) (st : DocketState) (F : Settlement d) (S : Finset ℕ) : Finset ℕ :=
  ((G.filter fun o => liveGiven st F S o).map Occurrence.id).toFinset

/-- **The active identities**: the least fixed point of `activeStep`, reached in `G.length`
steps from `∅`. -/
def Grounds.activeIds (G : Grounds d) (st : DocketState) (F : Settlement d) : Finset ℕ :=
  (activeStep G st F)^[G.length] ∅

/-- **The survivors**: the occurrences live given the active identities. -/
def Grounds.survivors (G : Grounds d) (st : DocketState) (F : Settlement d) : Grounds d :=
  G.filter fun o => liveGiven st F (G.activeIds st F) o

section Grounded

variable (G : Grounds d) (st : DocketState) (F : Settlement d)

lemma mem_activeStep {S : Finset ℕ} {j : ℕ} :
    j ∈ activeStep G st F S ↔ ∃ o ∈ G, liveGiven st F S o ∧ o.id = j := by
  simp [activeStep, List.mem_filter, and_assoc]

lemma activeStep_mono {S S' : Finset ℕ} (h : S ⊆ S') :
    activeStep G st F S ⊆ activeStep G st F S' := by
  intro j hj
  rw [mem_activeStep] at hj ⊢
  obtain ⟨o, ho, hl, rfl⟩ := hj
  exact ⟨o, ho, liveGiven_mono h hl, rfl⟩

lemma activeStep_subset (S : Finset ℕ) :
    activeStep G st F S ⊆ (G.map Occurrence.id).toFinset := by
  intro j hj
  rw [mem_activeStep] at hj
  obtain ⟨o, ho, -, rfl⟩ := hj
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨o, ho, rfl⟩

lemma iter_chain : ∀ k, (activeStep G st F)^[k] ∅ ⊆ (activeStep G st F)^[k + 1] ∅
  | 0 => Finset.empty_subset _
  | k + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact activeStep_mono G st F (iter_chain k)

lemma iter_fixed_of_eq {k : ℕ}
    (h : (activeStep G st F)^[k + 1] ∅ = (activeStep G st F)^[k] ∅) :
    ∀ i, (activeStep G st F)^[k + i] ∅ = (activeStep G st F)^[k] ∅ := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      show (activeStep G st F)^[(k + i) + 1] ∅ = _
      rw [Function.iterate_succ_apply', ih]
      exact (Function.iterate_succ_apply' _ _ _).symm.trans h

lemma card_iter : ∀ k, (∀ i < k, (activeStep G st F)^[i + 1] ∅ ≠ (activeStep G st F)^[i] ∅) →
    k ≤ ((activeStep G st F)^[k] ∅).card
  | 0, _ => Nat.zero_le _
  | k + 1, h => by
      have ih := card_iter k fun i hi => h i (Nat.lt_succ_of_lt hi)
      have hne := h k (Nat.lt_succ_self k)
      have hlt : ((activeStep G st F)^[k] ∅).card < ((activeStep G st F)^[k + 1] ∅).card :=
        Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨iter_chain G st F k, fun e => hne e.symm⟩)
      omega

/-- **The active identities are a fixed point of the step.** -/
theorem activeIds_fixed : activeStep G st F (G.activeIds st F) = G.activeIds st F := by
  unfold Grounds.activeIds
  rw [show activeStep G st F ((activeStep G st F)^[G.length] ∅) =
      (activeStep G st F)^[G.length + 1] ∅ from (Function.iterate_succ_apply' _ _ _).symm]
  by_cases h : ∃ i < G.length, (activeStep G st F)^[i + 1] ∅ = (activeStep G st F)^[i] ∅
  · obtain ⟨i, hi, he⟩ := h
    have h1 := iter_fixed_of_eq G st F he (G.length - i)
    have h2 := iter_fixed_of_eq G st F he (G.length + 1 - i)
    rw [show i + (G.length - i) = G.length by omega] at h1
    rw [show i + (G.length + 1 - i) = G.length + 1 by omega] at h2
    rw [h1, h2]
  · push Not at h
    have hcard := card_iter G st F G.length h
    refine (Finset.eq_of_subset_of_card_le (iter_chain G st F G.length) ?_).symm
    calc ((activeStep G st F)^[G.length + 1] ∅).card
        ≤ (G.map Occurrence.id).toFinset.card := by
          rw [Function.iterate_succ_apply']
          exact Finset.card_le_card (activeStep_subset G st F _)
      _ ≤ G.length := by
          refine (List.toFinset_card_le _).trans ?_
          rw [List.length_map]
      _ ≤ _ := hcard

theorem mem_activeIds {j : ℕ} :
    j ∈ G.activeIds st F ↔ ∃ o ∈ G.survivors st F, o.id = j := by
  conv_lhs => rw [← activeIds_fixed G st F]
  rw [mem_activeStep]
  simp [Grounds.survivors, List.mem_filter, and_assoc]

/-- **Membership in the survivors**: in the grounds, not undercut, kept, and citing a
survivor. -/
theorem mem_survivors {o : Occurrence d} :
    o ∈ G.survivors st F ↔
      o ∈ G ∧ ¬ undercut st o ∧ settleOutcome F o.form = .kept ∧
        ∀ j, o.cites = .occurrence j → ∃ o' ∈ G.survivors st F, o'.id = j := by
  constructor
  · intro h
    have h' := h
    simp only [Grounds.survivors, List.mem_filter, decide_eq_true_eq, liveGiven,
      citesIn_iff] at h'
    obtain ⟨hG, hu, hk, hc⟩ := h'
    exact ⟨hG, hu, hk, fun j hj => (mem_activeIds G st F).1 (hc j hj)⟩
  · rintro ⟨hG, hu, hk, hc⟩
    simp only [Grounds.survivors, List.mem_filter, decide_eq_true_eq, liveGiven, citesIn_iff]
    exact ⟨hG, hu, hk, fun j hj => (mem_activeIds G st F).2 (hc j hj)⟩

lemma survivors_subset {o : Occurrence d} (ho : o ∈ G.survivors st F) : o ∈ G :=
  ((mem_survivors G st F).1 ho).1

lemma survivors_not_defeated {o : Occurrence d} (ho : o ∈ G.survivors st F) :
    o.id ∉ st.defeated :=
  fun h => ((mem_survivors G st F).1 ho).2.1 (Or.inl h)

lemma survivors_kept {o : Occurrence d} (ho : o ∈ G.survivors st F) :
    settleOutcome F o.form = .kept :=
  ((mem_survivors G st F).1 ho).2.2.1

/-- Unfolding the iterate at a known length, for computing the active identities of a
concrete list of grounds. -/
lemma activeIds_of_length (k : ℕ) (hk : G.length = k) :
    G.activeIds st F = (activeStep G st F)^[k] ∅ := by
  rw [Grounds.activeIds, hk]

end Grounded

lemma iterate_two {α : Type*} (f : α → α) (x : α) : f^[2] x = f (f x) := rfl
lemma iterate_three {α : Type*} (f : α → α) (x : α) : f^[3] x = f (f (f x)) := rfl
lemma iterate_four {α : Type*} (f : α → α) (x : α) : f^[4] x = f (f (f (f x))) := rfl

/-- The settled bundle: the survivors' specialized rows, cited by occurrence, and the pins. -/
def Grounds.settledBundle (G : Grounds d) (st : DocketState) (F : Settlement d) :
    Bundle (Cite d) d :=
  ((G.survivors st F).map fun o => ⟨Cite.sub o.id, specialize F o.form.row⟩) ++ pinCited F

/-- **The settled region**: the region the surviving rows force. -/
def Grounds.settledRegion (G : Grounds d) (st : DocketState) (F : Settlement d)
    (x : Fin d → ℚ) : Prop :=
  (G.settledBundle st F).Region x

instance (G : Grounds d) (st : DocketState) (F : Settlement d) (x : Fin d → ℚ) :
    Decidable (G.settledRegion st F x) := by unfold Grounds.settledRegion; infer_instance

/-- The region of an explicit occurrence list under a settlement, on the unspecialized rows. -/
def regionOn (L : Grounds d) (F : Settlement d) (x : Fin d → ℚ) : Prop :=
  InCube x ∧ F.Pinned x ∧ ∀ o ∈ L, o.form.row.Sat x

/-- **The settled region, by occurrence.** -/
theorem Grounds.settledRegion_iff (G : Grounds d) (st : DocketState) (F : Settlement d)
    (x : Fin d → ℚ) :
    G.settledRegion st F x ↔ regionOn (G.survivors st F) F x := by
  unfold Grounds.settledRegion Grounds.settledBundle Bundle.Region regionOn
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro ⟨hc, hrows⟩
    have hpin : F.Pinned x := (pinCited_sat_iff F x).1 fun c hc => hrows c (Or.inr hc)
    refine ⟨hc, hpin, fun o ho => ?_⟩
    exact (specialize_sat_iff F _ hpin).1 (hrows _ (Or.inl ⟨o, ho, rfl⟩))
  · rintro ⟨hc, hpin, h⟩
    refine ⟨hc, ?_⟩
    rintro c (⟨o, ho, rfl⟩ | hc')
    · exact (specialize_sat_iff F _ hpin).2 (h o ho)
    · exact (pinCited_sat_iff F x).2 hpin c hc'

/-- **Membership in the settled bundle**: a survivor's specialized row under its citation,
or a pin row under its coordinate. -/
theorem mem_settledBundle_iff (G : Grounds d) (st : DocketState) (F : Settlement d)
    (c : CitedRow (Cite d) d) :
    c ∈ G.settledBundle st F ↔
      (∃ o ∈ G.survivors st F, c = ⟨Cite.sub o.id, specialize F o.form.row⟩) ∨
      (∃ i, ∃ r ∈ F.pinRowsAt i, c = ⟨Cite.settled i, r⟩) := by
  unfold Grounds.settledBundle
  simp only [List.mem_append, List.mem_map, pinCited, List.mem_flatMap, List.mem_finRange,
    true_and]
  constructor
  · rintro (⟨o, ho, rfl⟩ | ⟨i, r, hr, rfl⟩)
    · exact Or.inl ⟨o, ho, rfl⟩
    · exact Or.inr ⟨i, r, hr, rfl⟩
  · rintro (⟨o, ho, rfl⟩ | ⟨i, r, hr, rfl⟩)
    · exact Or.inl ⟨o, ho, rfl⟩
    · exact Or.inr ⟨i, r, hr, rfl⟩

/-- **The settled region contains the port-only region**: the survivors are among the
undefeated-port occurrences. -/
theorem region_subset_settledRegion (G : Grounds d) (st : DocketState) (F : Settlement d)
    (x : Fin d → ℚ) (hx : G.region st F x) : G.settledRegion st F x := by
  rw [Grounds.region_iff] at hx
  rw [Grounds.settledRegion_iff]
  obtain ⟨hc, hp, h⟩ := hx
  exact ⟨hc, hp, fun o ho => h o (survivors_subset G st F ho) (survivors_not_defeated G st F ho)⟩

/-! ### Monotonicity restated (A4) -/

lemma pinsFalse_mono {F F' : Settlement d} (h : F.le F') {i : Fin d}
    (hi : pinsFalse F i = true) : pinsFalse F' i = true := by
  rw [pinsFalse_iff] at hi ⊢
  exact h i false hi

/-- A kept form stays kept backwards: what is kept under more settlement was kept under less. -/
lemma kept_of_le {F F' : Settlement d} (h : F.le F') {f : Form d}
    (hk : settleOutcome F' f = .kept) : settleOutcome F f = .kept := by
  rw [settleOutcome_eq_kept_iff] at hk ⊢
  intro hd
  apply hk
  cases f <;> simp only [Degenerate] at hd ⊢
  · exact pinsFalse_mono h hd
  · rcases hd with hd | hd
    · exact Or.inl (pinsFalse_mono h hd)
    · exact Or.inr (pinsFalse_mono h hd)
  · rcases hd with hd | hd
    · exact Or.inl (pinsFalse_mono h hd)
    · exact Or.inr (pinsFalse_mono h hd)

lemma activeStep_anti_settlement (G : Grounds d) (st : DocketState) {F F' : Settlement d}
    (h : F.le F') {S S' : Finset ℕ} (hS : S' ⊆ S) :
    activeStep G st F' S' ⊆ activeStep G st F S := by
  intro j hj
  rw [mem_activeStep] at hj ⊢
  obtain ⟨o, ho, ⟨hu, hk, hc⟩, rfl⟩ := hj
  exact ⟨o, ho, ⟨hu, kept_of_le h hk, citesIn_mono hS hc⟩, rfl⟩

lemma activeIds_anti_settlement (G : Grounds d) (st : DocketState) {F F' : Settlement d}
    (h : F.le F') : G.activeIds st F' ⊆ G.activeIds st F := by
  unfold Grounds.activeIds
  generalize G.length = k
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact activeStep_anti_settlement G st h ih

/-- **Survivors only leave under more settlement.** -/
theorem survivors_anti (G : Grounds d) (st : DocketState) {F F' : Settlement d} (h : F.le F')
    {o : Occurrence d} (ho : o ∈ G.survivors st F') : o ∈ G.survivors st F := by
  simp only [Grounds.survivors, List.mem_filter, decide_eq_true_eq, liveGiven] at ho ⊢
  obtain ⟨hG, hu, hk, hc⟩ := ho
  exact ⟨hG, hu, kept_of_le h hk, citesIn_mono (activeIds_anti_settlement G st h) hc⟩

lemma undercut_mono {st st' : DocketState} (h : st.defeated ⊆ st'.defeated) {o : Occurrence d}
    (hu : undercut st o) : undercut st' o := by
  rcases hu with hu | ⟨j, hj, hd⟩
  · exact Or.inl (h hu)
  · exact Or.inr ⟨j, hj, h hd⟩

lemma activeStep_anti_docket (G : Grounds d) (F : Settlement d) {st st' : DocketState}
    (h : st.defeated ⊆ st'.defeated) {S S' : Finset ℕ} (hS : S' ⊆ S) :
    activeStep G st' F S' ⊆ activeStep G st F S := by
  intro j hj
  rw [mem_activeStep] at hj ⊢
  obtain ⟨o, ho, ⟨hu, hk, hc⟩, rfl⟩ := hj
  exact ⟨o, ho, ⟨fun hu' => hu (undercut_mono h hu'), hk, citesIn_mono hS hc⟩, rfl⟩

lemma activeIds_anti_docket (G : Grounds d) (F : Settlement d) {st st' : DocketState}
    (h : st.defeated ⊆ st'.defeated) : G.activeIds st' F ⊆ G.activeIds st F := by
  unfold Grounds.activeIds
  generalize G.length = k
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact activeStep_anti_docket G F h ih

/-- **Survivors only leave under more defeat.** -/
theorem survivors_anti_docket (G : Grounds d) (F : Settlement d) {st st' : DocketState}
    (h : st.defeated ⊆ st'.defeated) {o : Occurrence d} (ho : o ∈ G.survivors st' F) :
    o ∈ G.survivors st F := by
  simp only [Grounds.survivors, List.mem_filter, decide_eq_true_eq, liveGiven] at ho ⊢
  obtain ⟨hG, hu, hk, hc⟩ := ho
  exact ⟨hG, fun hu' => hu (undercut_mono h hu'), hk,
    citesIn_mono (activeIds_anti_docket G F h) hc⟩

/-- **A4(a): no reopening, nested as before.**  When the survivors are unchanged by a
settlement step, the settled region shrinks. -/
theorem settledRegion_anti_of_survivors_eq (G : Grounds d) (st : DocketState)
    {F F' : Settlement d} (h : F.le F') (hs : G.survivors st F' = G.survivors st F)
    {x : Fin d → ℚ} (hx : G.settledRegion st F' x) : G.settledRegion st F x := by
  rw [Grounds.settledRegion_iff] at hx ⊢
  obtain ⟨hc, hp, hr⟩ := hx
  exact ⟨hc, hp.mono h, by rw [← hs]; exact hr⟩

/-- **A4(b): a reopening step is bounded by the kept rows' pre-step region.**  The settled
region after the step, and the settled region before it, both lie inside the region the
*surviving* rows forced at the pre-step settlement. -/
theorem settledRegion_subset_kept (G : Grounds d) (st : DocketState) {F F' : Settlement d}
    (h : F.le F') (x : Fin d → ℚ) :
    (G.settledRegion st F' x → regionOn (G.survivors st F') F x) ∧
    (G.settledRegion st F x → regionOn (G.survivors st F') F x) := by
  constructor
  · intro hx
    rw [Grounds.settledRegion_iff] at hx
    exact ⟨hx.1, hx.2.1.mono h, hx.2.2⟩
  · intro hx
    rw [Grounds.settledRegion_iff] at hx
    exact ⟨hx.1, hx.2.1, fun o ho => hx.2.2 o (survivors_anti G st h ho)⟩

/-- **The exact widening bound.**  Any bounds valid on the kept rows' pre-step region are
valid on the settled region before and after the step: the interval can widen by at most
what the removed rows had been forcing. -/
theorem reopening_bound (G : Grounds d) (st : DocketState) {F F' : Settlement d} (h : F.le F')
    (φ : Fin d) (lo hi : ℚ)
    (hK : ∀ x, regionOn (G.survivors st F') F x → lo ≤ x φ ∧ x φ ≤ hi) :
    (∀ x, G.settledRegion st F' x → lo ≤ x φ ∧ x φ ≤ hi) ∧
    (∀ x, G.settledRegion st F x → lo ≤ x φ ∧ x φ ≤ hi) :=
  ⟨fun x hx => hK x ((settledRegion_subset_kept G st h x).1 hx),
    fun x hx => hK x ((settledRegion_subset_kept G st h x).2 hx)⟩

end Rebuttal
/-- **Admissible** (P1): the settled region of the grounds contains the verdict — some
region point gives `φ` the value `v`. -/
def Admissible (G : Grounds d) (st : DocketState) (F : Settlement d) (φ : Fin d) (v : ℚ) :
    Prop := ∃ x, G.settledRegion st F x ∧ x φ = v

/-- **A verdict certificate**: a lower and an upper bound certificate, each row cited by
occurrence (or a pin, or a cube face), and the two endpoints with the region points that
attain them. -/
structure VerdictCert (d m m' : ℕ) (φ : Fin d) where
  lo : BoundCert d m φ (-1)
  hi : BoundCert d m' φ 1
  loCite : Fin m → Cite d
  hiCite : Fin m' → Cite d
  loPoint : Fin d → ℚ
  hiPoint : Fin d → ℚ

namespace VerdictCert

variable {m m' : ℕ} {φ : Fin d}

/-- Rows are determined by their data; equality is decidable coordinatewise. -/
instance rowDecEq : DecidableEq (Row d) := fun r s =>
  if h : r.a = s.a ∧ r.b = s.b then
    isTrue (by obtain ⟨a, b⟩ := r; obtain ⟨a', b'⟩ := s; simp only at h; rw [h.1, h.2])
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

instance citedRowDecEq {Q : Type*} [DecidableEq Q] : DecidableEq (CitedRow Q d) := fun r s =>
  if h : r.cites = s.cites ∧ r.row = s.row then
    isTrue (by obtain ⟨q, a⟩ := r; obtain ⟨q', a'⟩ := s; simp only at h; rw [h.1, h.2])
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

/-- A certificate row is admitted against a bundle under its citation: the cited row is in
the bundle, or the row is a cube face (which cites nothing). -/
def RowAdmitted {Q : Type*} (B : Bundle Q d) (q : Q) (r : Row d) : Prop :=
  (⟨q, r⟩ : CitedRow Q d) ∈ B ∨ (∃ i, r = cubeUpper i) ∨ (∃ i, r = cubeLower i)

instance {Q : Type*} [DecidableEq Q] (B : Bundle Q d) (q : Q) (r : Row d) :
    Decidable (RowAdmitted B q r) := by unfold RowAdmitted; infer_instance

theorem RowAdmitted.allowed {Q : Type*} {B : Bundle Q d} {q : Q} {r : Row d}
    (h : RowAdmitted B q r) : B.Allowed r := by
  rcases h with h | h | h
  · exact Or.inl ⟨_, h, rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **Every positively weighted row names a survivor** (or a pin or a face). -/
def CitesLive (c : VerdictCert d m m' φ) (B : Bundle (Cite d) d) : Prop :=
  (∀ i, 0 < c.lo.mult i → RowAdmitted B (c.loCite i) (c.lo.row i)) ∧
  (∀ i, 0 < c.hi.mult i → RowAdmitted B (c.hiCite i) (c.hi.row i))

instance (c : VerdictCert d m m' φ) (B : Bundle (Cite d) d) : Decidable (c.CitesLive B) := by
  unfold CitesLive; infer_instance

end VerdictCert

/-- **Supported** (P1): the certificate's positively weighted rows are cited into the settled
bundle — a survivor's row under that occurrence's citation, a pin, or a cube face — its
endpoints bracket the verdict, and both endpoints are attained in the settled region. -/
def Supported {m m' : ℕ} (G : Grounds d) (st : DocketState) (F : Settlement d) (φ : Fin d)
    (v : ℚ) (c : VerdictCert d m m' φ) : Prop :=
  c.CitesLive (G.settledBundle st F) ∧
  -c.lo.value ≤ v ∧ v ≤ c.hi.value ∧
  (G.settledRegion st F c.loPoint ∧ c.loPoint φ = -c.lo.value) ∧
  (G.settledRegion st F c.hiPoint ∧ c.hiPoint φ = c.hi.value)

instance {m m' : ℕ} (G : Grounds d) (st : DocketState) (F : Settlement d) (φ : Fin d) (v : ℚ)
    (c : VerdictCert d m m' φ) : Decidable (Supported G st F φ v c) := by
  unfold Supported; infer_instance

/-- **The record at a step** (Part A's view of it): the admitted grounds, the docket, the
settlement, and the set of record events the record authorizes. -/
structure RecordState (d : ℕ) where
  grounds : Grounds d
  docket : DocketState
  settlement : Settlement d
  authorized : Finset ℕ

/-- **Licensed** (P1): supported on the record's survivors, and the event that issued and
selected the certificate is one the record authorizes. -/
def Licensed {m m' : ℕ} (R : RecordState d) (φ : Fin d) (v : ℚ) (c : VerdictCert d m m' φ)
    (event : ℕ) : Prop :=
  Supported R.grounds R.docket R.settlement φ v c ∧ event ∈ R.authorized

instance {m m' : ℕ} (R : RecordState d) (φ : Fin d) (v : ℚ) (c : VerdictCert d m m' φ)
    (event : ℕ) : Decidable (Licensed R φ v c event) := by
  unfold Licensed; infer_instance

/-- **Licensed → Supported.** -/
theorem licensed_supported {m m' : ℕ} {R : RecordState d} {φ : Fin d} {v : ℚ}
    {c : VerdictCert d m m' φ} {event : ℕ} (h : Licensed R φ v c event) :
    Supported R.grounds R.docket R.settlement φ v c := h.1

/-- **Supported → Admissible**, by rational convexity. -/
theorem supported_admissible {m m' : ℕ} {G : Grounds d} {st : DocketState} {F : Settlement d}
    {φ : Fin d} {v : ℚ} {c : VerdictCert d m m' φ} (h : Supported G st F φ v c) :
    Admissible G st F φ v := by
  obtain ⟨_, hlo, hhi, ⟨hloR, hloφ⟩, ⟨hhiR, hhiφ⟩⟩ := h
  exact region_attains_between (B := G.settledBundle st F) hloR hhiR (by rw [hloφ]; exact hlo)
    (by rw [hhiφ]; exact hhi)

/-- **The chain.** -/
theorem licence_chain {m m' : ℕ} {R : RecordState d} {φ : Fin d} {v : ℚ}
    {c : VerdictCert d m m' φ} {event : ℕ} (h : Licensed R φ v c event) :
    Supported R.grounds R.docket R.settlement φ v c ∧
      Admissible R.grounds R.docket R.settlement φ v :=
  ⟨licensed_supported h, supported_admissible (licensed_supported h)⟩

/-- A supported verdict's certified endpoints are valid bounds on the settled region: the
certificate is not only cited but sound. -/
theorem Supported.valid {m m' : ℕ} {G : Grounds d} {st : DocketState} {F : Settlement d}
    {φ : Fin d} {v : ℚ} {c : VerdictCert d m m' φ} (h : Supported G st F φ v c) :
    (∀ x, G.settledRegion st F x → -c.lo.value ≤ x φ) ∧
    (∀ x, G.settledRegion st F x → x φ ≤ c.hi.value) := by
  obtain ⟨⟨hlo, hhi⟩, _⟩ := h
  constructor
  · intro x hx
    have := c.lo.sound_of_pos x fun i hi => allowed_sat (hlo i hi).allowed hx
    linarith
  · intro x hx
    have := c.hi.sound_of_pos x fun i hi => allowed_sat (hhi i hi).allowed hx
    linarith

/-! ## Part A — the two countermodels -/

namespace Countermodel

/-- The one coordinate `φ = 0`. -/
abbrev φ : Fin 1 := 0

/-- Two distinct occurrences, each `P(φ) ≥ 1/2`, from two parties, citing nothing. -/
def r₁ : Occurrence 1 := ⟨1, Form.premise 0 (1/2), .none, .party 1, ∅⟩
def r₂ : Occurrence 1 := ⟨2, Form.premise 0 (1/2), .none, .party 2, ∅⟩

/-- The grounds: both occurrences. -/
def G : Grounds 1 := [r₁, r₂]

/-- The empty settlement on one coordinate. -/
def F : Settlement 1 := Settlement.empty 1

/-- The docket after defeat of `r₁`. -/
def stDefeat : DocketState := ⟨{1}, ∅⟩

/-- The common row both occurrences compile to, specialized by the empty settlement. -/
def premRow : Row 1 := specialize F (Form.premise 0 (1/2 : ℚ)).row

lemma premRow_sat_iff (x : Fin 1 → ℚ) : premRow.Sat x ↔ (1/2 : ℚ) ≤ x 0 := by
  rw [premRow, specialize_sat_iff F _ (Settlement.empty_pinned x)]
  exact Form.premise_sat_iff 0 (1/2) x

/-- The survivors on the quiet docket: both occurrences. -/
lemma survivors_quiet : G.survivors DocketState.quiet F = [r₁, r₂] := by
  unfold Grounds.survivors
  rw [activeIds_of_length G _ _ 2 rfl, iterate_two]
  simp [activeStep, liveGiven, undercut, citesIn, settleOutcome, pinsFalse, G, r₁, r₂, F,
    Settlement.empty, DocketState.quiet]

/-- The survivors after the defeat of `r₁`: `r₂` alone. -/
lemma survivors_defeat : G.survivors stDefeat F = [r₂] := by
  unfold Grounds.survivors
  rw [activeIds_of_length G _ _ 2 rfl, iterate_two]
  simp [activeStep, liveGiven, undercut, citesIn, settleOutcome, pinsFalse, G, r₁, r₂, F,
    Settlement.empty, stDefeat]

/-- **The settled region is unchanged by the defeat**: `r₂` supplies the same row. -/
theorem region_unchanged (x : Fin 1 → ℚ) :
    G.settledRegion DocketState.quiet F x ↔ G.settledRegion stDefeat F x := by
  rw [Grounds.settledRegion_iff, Grounds.settledRegion_iff, survivors_quiet, survivors_defeat]
  simp [regionOn, r₁, r₂]

/-- Both settled regions are the interval `[1/2, 1]` on `φ`. -/
theorem region_iff (x : Fin 1 → ℚ) :
    G.settledRegion DocketState.quiet F x ↔ (1/2 : ℚ) ≤ x 0 ∧ x 0 ≤ 1 := by
  rw [Grounds.settledRegion_iff, survivors_quiet]
  have hr₁ : r₁.form.row.Sat x ↔ (1/2 : ℚ) ≤ x 0 := Form.premise_sat_iff 0 (1/2) x
  have hr₂ : r₂.form.row.Sat x ↔ (1/2 : ℚ) ≤ x 0 := Form.premise_sat_iff 0 (1/2) x
  constructor
  · rintro ⟨hc, -, h⟩
    exact ⟨hr₁.1 (h r₁ (by simp)), (hc 0).2⟩
  · rintro ⟨hlo, hhi⟩
    refine ⟨fun i => ?_, Settlement.empty_pinned x, ?_⟩
    · have : i = 0 := Subsingleton.elim i 0
      subst this; constructor <;> linarith
    · intro o ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · exact hr₁.2 hlo
      · exact hr₂.2 hlo

/-- A point of the interval is in the port-only region of the quiet docket. -/
lemma mem_region_port (x : Fin 1 → ℚ) (hlo : (1/2 : ℚ) ≤ x 0) (hhi : x 0 ≤ 1) :
    G.region DocketState.quiet F x := by
  rw [Grounds.region_iff]
  refine ⟨fun i => ?_, Settlement.empty_pinned x, ?_⟩
  · have : i = 0 := Subsingleton.elim i 0
    subst this; exact ⟨by linarith, hhi⟩
  · intro o ho _
    simp only [G, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> exact (Form.premise_sat_iff 0 (1/2) x).2 hlo

/-- The lower-bound certificate: multiplier `1` on the premise row. -/
def loCert : BoundCert 1 1 φ (-1) where
  mult := fun _ => 1
  row := fun _ => premRow
  mult_nonneg := fun _ => by norm_num
  coeff_sum := fun j => by
    have : j = 0 := Subsingleton.elim j 0
    subst this
    simp [premRow, specialize, F, Settlement.empty, Form.row]

/-- The upper-bound certificate: multiplier `1` on the cube face `x 0 ≤ 1`. -/
def hiCert : BoundCert 1 1 φ 1 where
  mult := fun _ => 1
  row := fun _ => cubeUpper 0
  mult_nonneg := fun _ => by norm_num
  coeff_sum := fun j => by
    have : j = 0 := Subsingleton.elim j 0
    subst this
    simp [cubeUpper]

lemma loCert_value : loCert.value = -(1/2 : ℚ) := by
  simp [BoundCert.value, loCert, premRow, specialize, F, Settlement.empty, Form.row,
    settledTerm]

lemma hiCert_value : hiCert.value = 1 := by
  simp [BoundCert.value, hiCert, cubeUpper]

/-- A verdict certificate citing occurrence `k` for its lower row. -/
def cert (k : ℕ) : VerdictCert 1 1 1 φ where
  lo := loCert
  hi := hiCert
  loCite := fun _ => Cite.sub k
  hiCite := fun _ => Cite.settled 0
  loPoint := fun _ => 1/2
  hiPoint := fun _ => 1

lemma loPoint_mem : G.settledRegion DocketState.quiet F (fun _ => 1/2) := by
  rw [region_iff]; norm_num

lemma hiPoint_mem : G.settledRegion DocketState.quiet F (fun _ => 1) := by
  rw [region_iff]; norm_num

lemma premRow_b : premRow.b = -(1/2 : ℚ) := by
  simp [premRow, specialize, F, Settlement.empty, Form.row, settledTerm]

lemma premRow_a : premRow.a = fun _ => -1 := by
  funext i
  have : i = 0 := Subsingleton.elim i 0
  subst this
  simp [premRow, specialize, F, Settlement.empty, Form.row]

lemma premRow_ne_cubeUpper (i : Fin 1) : premRow ≠ cubeUpper i := by
  intro h
  have := congrArg Row.b h
  rw [premRow_b] at this
  norm_num [cubeUpper] at this

lemma premRow_ne_cubeLower (i : Fin 1) : premRow ≠ cubeLower i := by
  intro h
  have := congrArg Row.b h
  rw [premRow_b] at this
  norm_num [cubeLower] at this

/-- The settled bundle on the quiet docket: both citations of the premise row, no pins. -/
lemma settledBundle_quiet :
    G.settledBundle DocketState.quiet F = [⟨Cite.sub 1, premRow⟩, ⟨Cite.sub 2, premRow⟩] := by
  rw [Grounds.settledBundle, survivors_quiet]
  simp [r₁, r₂, pinCited, F, Settlement.empty, Settlement.pinRowsAt, premRow]

/-- The settled bundle after the defeat: only `r₂`'s citation survives. -/
lemma settledBundle_defeat : G.settledBundle stDefeat F = [⟨Cite.sub 2, premRow⟩] := by
  rw [Grounds.settledBundle, survivors_defeat]
  simp [r₂, pinCited, F, Settlement.empty, Settlement.pinRowsAt, premRow]

lemma cited_quiet (k : ℕ) (hk : k = 1 ∨ k = 2) :
    (cert k).CitesLive (G.settledBundle DocketState.quiet F) := by
  refine ⟨fun _ _ => Or.inl ?_, fun _ _ => Or.inr (Or.inl ⟨0, rfl⟩)⟩
  rw [settledBundle_quiet]
  rcases hk with rfl | rfl <;> simp [cert, loCert]

/-- **Supported on the quiet docket**, citing either occurrence, for any verdict in the
interval. -/
theorem supported_quiet (k : ℕ) (hk : k = 1 ∨ k = 2) (v : ℚ) (hlo : (1/2 : ℚ) ≤ v)
    (hhi : v ≤ 1) : Supported G DocketState.quiet F φ v (cert k) := by
  refine ⟨cited_quiet k hk, ?_, ?_, ⟨loPoint_mem, ?_⟩, ⟨hiPoint_mem, ?_⟩⟩
  · simp [cert, loCert_value]; linarith
  · simpa [cert, hiCert_value] using hhi
  · simp [cert, loCert_value]
  · simp [cert, hiCert_value]

/-- **After the defeat of `r₁`**, the certificate citing `r₁` is no longer supported: its
one positively weighted lower row is cited into a bundle that no longer carries that
citation, and the row is no cube face. -/
theorem stale_not_supported (v : ℚ) : ¬ Supported G stDefeat F φ v (cert 1) := by
  rintro ⟨⟨hlo, -⟩, -⟩
  have h := hlo 0 (by simp [cert, loCert])
  rw [settledBundle_defeat] at h
  rcases h with h | ⟨i, hi⟩ | ⟨i, hi⟩
  · simp [cert, loCert] at h
  · exact premRow_ne_cubeUpper i (by simpa [cert, loCert] using hi)
  · exact premRow_ne_cubeLower i (by simpa [cert, loCert] using hi)

/-- A fresh certificate citing the surviving `r₂` is supported after the defeat. -/
theorem fresh_supported (v : ℚ) (hlo : (1/2 : ℚ) ≤ v) (hhi : v ≤ 1) :
    Supported G stDefeat F φ v (cert 2) := by
  refine ⟨⟨fun _ _ => Or.inl ?_, fun _ _ => Or.inr (Or.inl ⟨0, rfl⟩)⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [settledBundle_defeat]; simp [cert, loCert]
  · simp [cert, loCert_value]; linarith
  · simpa [cert, hiCert_value] using hhi
  · exact (region_unchanged _).1 loPoint_mem
  · simp [cert, loCert_value]
  · exact (region_unchanged _).1 hiPoint_mem
  · simp [cert, hiCert_value]

/-- **A3.  Admissible does not imply Supported**: after the defeat the verdict is still
admissible (the region did not move) while the certificate that cited the defeated
occurrence is not supported — and a certificate citing the survivor is. -/
theorem admissible_not_supported :
    Admissible G stDefeat F φ (1/2) ∧ ¬ Supported G stDefeat F φ (1/2) (cert 1) ∧
      Supported G stDefeat F φ (1/2) (cert 2) :=
  ⟨⟨fun _ => 1/2, (region_unchanged _).1 loPoint_mem, rfl⟩, stale_not_supported _,
    fresh_supported _ le_rfl (by norm_num)⟩

/-- The forced interval of the countermodel is `[1/2, 1]`, with positive width. -/
theorem forcedInterval : IsForcedInterval G.seed [] DocketState.quiet F φ (1/2) 1 :=
  ⟨fun x hx => ((region_iff x).1 (region_subset_settledRegion G _ F x hx)).1,
    fun x hx => ((region_iff x).1 (region_subset_settledRegion G _ F x hx)).2,
    ⟨fun _ => 1/2, mem_region_port _ le_rfl (by norm_num), rfl⟩,
    ⟨fun _ => 1, mem_region_port _ (by norm_num) le_rfl, rfl⟩⟩

/-! ### A4: two supported verdicts, one unauthorized selection -/

/-- The record whose event `7` is authorized. -/
def recordAuth : RecordState 1 := ⟨G, DocketState.quiet, F, {7}⟩

/-- The same record with no authorized event at that step. -/
def recordNoAuth : RecordState 1 := ⟨G, DocketState.quiet, F, ∅⟩

/-- **A4.  Supported does not imply Licensed.**  Two verdicts inside the forced interval,
both supported by the same cited certificate; the selection event is licensed on the
record that authorizes it and not on the record that does not. -/
theorem supported_not_licensed :
    Supported G DocketState.quiet F φ (2/3) (cert 1) ∧
    Supported G DocketState.quiet F φ (3/4) (cert 1) ∧
    Licensed recordAuth φ (2/3) (cert 1) 7 ∧
    ¬ Licensed recordNoAuth φ (3/4) (cert 1) 7 := by
  refine ⟨supported_quiet 1 (Or.inl rfl) _ (by norm_num) (by norm_num),
    supported_quiet 1 (Or.inl rfl) _ (by norm_num) (by norm_num),
    ⟨supported_quiet 1 (Or.inl rfl) _ (by norm_num) (by norm_num), by simp [recordAuth]⟩, ?_⟩
  rintro ⟨-, h⟩
  simp [recordNoAuth] at h

/-! The selection as a transparency failure, an instance of `tiebreak_transparency`:
two audited continuations enter the same declared inputs at the selection event, and the
advisor's contribution at that event differs — the verdict it pushed. -/

section Transparency

open Workspace.Deference.Contrib.GateIsLegitimacy

/-- The two parties. -/
inductive Party where
  | principal
  | advisor
  deriving DecidableEq

/-- The trace interface: the advisor enters the selected verdict at event `0`. -/
def interface : TraceInterface Bool Party ℚ where
  entriesAt r e := if e = 0 then [(Party.advisor, if r then 3/4 else 2/3)] else []
  agent := Party.advisor
  principal := Party.principal

/-- The frame: the audited class is both continuations; declared inputs are the same. -/
def frame : TFrame Bool Unit Bool Unit Bool ℚ where
  β q _ := q
  x _ _ := ()
  R ω := ω
  V ω _ := if ω then 3/4 else 2/3
  D := Set.univ

/-- **The selection is not transparent** at the selection event, whatever reference `κ`
is declared: `tiebreak_transparency` applied to the two continuations. -/
theorem selection_not_transparent (κ : Party → Unit → Unit → List ℚ) :
    ¬ TransparentAt interface frame κ 0 :=
  tiebreak_transparency (I := interface) (F := frame) Party.advisor (by decide) false true
    (Set.mem_univ _) (Set.mem_univ _) () rfl (by
      simp [interface, frame, sourced]
      norm_num)

end Transparency

end Countermodel

/-! ## Part B — the settlement fork: the odds bankroll -/

section Fork

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementPreservation
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-- **The warrant enforcer**: the force layer's compiled position on the date's
presentation.  It reads no price history beyond what its features read, so prefix
invariance is by definition. -/
def warrantEnforcer (sched : ℕ → Presentation) : AdaptiveTrader where
  action n _ := enforcementStrategy (sched n) n

/-- The realized enforcer plays exactly the compiled strategy. -/
lemma realizedEnforcer_strat (L : Assessment) (sched : ℕ → Presentation) (n : ℕ) :
    (realizedEnforcer L (warrantEnforcer sched)).strat n = enforcementStrategy (sched n) n :=
  rfl

/-- **The signed row gap** at a world: positive is a surplus (the world clears the row),
negative is a deficit (the row excludes the world). -/
noncomputable def rowGap (coords : Finset Sentence) (r : Row) (v : PCWorld) : ℚ :=
  pair coords r.coeff (ratPayout v) - r.rhs

/-- The units the enforcer holds on a row at a price: intensity times violation. -/
def rowUnits (pres : Presentation) (i : Fin pres.rows.length) (p : Sentence → ℚ) : ℚ :=
  pres.intensities i * pres.rowViolation i p

lemma rowUnits_nonneg (pres : Presentation) (i : Fin pres.rows.length) (p : Sentence → ℚ) :
    0 ≤ rowUnits pres i p :=
  mul_nonneg (pres.rowAt i).intensity_nonneg (violation_nonneg _ _ _ _)

/-- **The day's value, resolved**: the units-weighted signed gaps plus the
intensity-weighted squared violations. -/
theorem day_value_eq (L : Assessment) (sched : ℕ → Presentation) (n : ℕ) (v : PCWorld) :
    ((realizedEnforcer L (warrantEnforcer sched)).strat n).value
        (history L (warrantEnforcer sched)) v.payout =
      (((∑ i, rowUnits (sched n) i (quote L (warrantEnforcer sched) n) *
            rowGap (sched n).coords ((sched n).rowAt i) v) +
          ∑ i, (sched n).intensities i *
            (sched n).rowViolation i (quote L (warrantEnforcer sched) n) ^ 2 : ℚ) : ℝ) := by
  rw [realizedEnforcer_strat]
  have hpay : (fun φ => ((ratPayout v φ : ℚ) : ℝ)) = v.payout := by
    funext φ; exact (payout_eq_ratPayout v φ).symm
  have hval := value_enforcementStrategy (sched n) n (history L (warrantEnforcer sched))
    (quote L (warrantEnforcer sched)) (history_eq_quote_cast L _) (ratPayout v)
  rw [hpay] at hval
  rw [hval]
  congr 1
  rw [Presentation.compiledPosition, pair_position, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pair_sub]
  have hgap := violation_mul_gap (sched n).coords ((sched n).normals i) ((sched n).rhss i)
    (quote L (warrantEnforcer sched) n)
  simp only [rowUnits, rowGap, Presentation.rowViolation, Presentation.normals,
    Presentation.rhss] at hgap ⊢
  linear_combination ((sched n).intensities i) * hgap

/-- At a world, the day's value is at least the units-weighted signed gap. -/
theorem day_value_ge (L : Assessment) (sched : ℕ → Presentation) (n : ℕ) (v : PCWorld) :
    ((∑ i, rowUnits (sched n) i (quote L (warrantEnforcer sched) n) *
        rowGap (sched n).coords ((sched n).rowAt i) v : ℚ) : ℝ) ≤
      ((realizedEnforcer L (warrantEnforcer sched)).strat n).value
        (history L (warrantEnforcer sched)) v.payout := by
  rw [day_value_eq]
  have : 0 ≤ ∑ i, (sched n).intensities i *
      (sched n).rowViolation i (quote L (warrantEnforcer sched) n) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg ((sched n).rowAt i).intensity_nonneg (sq_nonneg _)
  exact_mod_cast le_add_of_nonneg_right this

/-- The units-weighted signed gap of one date at a world. -/
noncomputable def dayGap (L : Assessment) (sched : ℕ → Presentation) (v : PCWorld) (t : ℕ) : ℚ :=
  ∑ i, rowUnits (sched t) i (quote L (warrantEnforcer sched) t) *
    rowGap (sched t).coords ((sched t).rowAt i) v

/-- The slack mass through date `n`: the units-weighted surplus at the witness world. -/
noncomputable def slackMass (L : Assessment) (sched : ℕ → Presentation) (v' : PCWorld) (n : ℕ) :
    ℚ :=
  ∑ t ∈ Finset.range (n + 1), dayGap L sched v' t

/-- The witness world's net worth dominates the slack mass. -/
theorem slackMass_le_netWorth (L : Assessment) (sched : ℕ → Presentation) (v' : PCWorld)
    (n : ℕ) :
    ((slackMass L sched v' n : ℚ) : ℝ) ≤
      (realizedEnforcer L (warrantEnforcer sched)).netWorth (history L (warrantEnforcer sched))
        v' n := by
  unfold slackMass Trader.netWorth
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun t _ => day_value_ge L sched t v'

/-- **The market's capital bounds the enforcer's assessed gain**: the market maker's
constant `1` plus the trading firm's floor `2`, at every live world. -/
theorem enforcer_netWorth_lt_three (L : Assessment) (E : AdaptiveTrader) (n : ℕ)
    (v : PCWorld) (hv : L.Live n v) :
    (realizedEnforcer L E).netWorth (history L E) v n < 3 := by
  have hmm : (realizedAggregate L E).netWorth (history L E) v n < 1 := by
    rw [history_eq_marketMakerHistory]
    exact marketMaker_netWorth_lt_one (realizedAggregate L E) v n
  have hfirm : -2 ≤ (realizedFirm L E).netWorth (history L E) v n := by
    rw [← tradingFirmTrader_quote_eq_realizedFirm]
    exact AssessmentFirm.tradingFirmTrader_netWorth_floor L (history L E) (history_range L E)
      (quote L E) (history_eq_quote_cast L E) n v hv
  have hsplit := realizedAggregate_netWorth L E n (history L E) v
  linarith

/-- **The odds bankroll.**  If at date `n` a live world `v'` clears every enforced row of
every date `t ≤ n` with a surplus dominating, by the factor `ρ`, the deficit of the live
world `w` on that row, then the enforcer's assessed net worth at `w` is at least `−3ρ`.
Intensity, tolerance, the number of rows and the number of dates do not appear. -/
theorem netWorth_ge_neg_odds (L : Assessment) (sched : ℕ → Presentation) (ρ : ℚ)
    (hρ : 0 ≤ ρ) (n : ℕ) (v' : PCWorld) (hv' : L.Live n v') (w : PCWorld)
    (hgap : ∀ t ≤ n, ∀ r ∈ (sched t).rows,
      -(rowGap (sched t).coords r w) ≤ ρ * rowGap (sched t).coords r v') :
    -(3 * (ρ : ℝ)) ≤
      (realizedEnforcer L (warrantEnforcer sched)).netWorth (history L (warrantEnforcer sched))
        w n := by
  have hS : ((slackMass L sched v' n : ℚ) : ℝ) < 3 :=
    lt_of_le_of_lt (slackMass_le_netWorth L sched v' n)
      (enforcer_netWorth_lt_three L (warrantEnforcer sched) n v' hv')
  -- each date: the deficit side is dominated by `ρ` times the surplus side
  have hday : ∀ t ≤ n, -((ρ : ℝ) * ((dayGap L sched v' t : ℚ) : ℝ)) ≤
      ((realizedEnforcer L (warrantEnforcer sched)).strat t).value
        (history L (warrantEnforcer sched)) w.payout := by
    intro t htn
    refine le_trans ?_ (day_value_ge L sched t w)
    have hq : -(ρ * dayGap L sched v' t) ≤ dayGap L sched w t := by
      unfold dayGap
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hu := rowUnits_nonneg (sched t) i (quote L (warrantEnforcer sched) t)
      have hg := hgap t htn ((sched t).rowAt i) (List.get_mem _ _)
      nlinarith
    have hq' : ((-(ρ * dayGap L sched v' t) : ℚ) : ℝ) ≤ ((dayGap L sched w t : ℚ) : ℝ) := by
      exact_mod_cast hq
    push_cast at hq'
    exact hq'
  have hsum : ∑ t ∈ Finset.range (n + 1), -((ρ : ℝ) * ((dayGap L sched v' t : ℚ) : ℝ)) =
      -((ρ : ℝ) * ((slackMass L sched v' n : ℚ) : ℝ)) := by
    unfold slackMass
    rw [Rat.cast_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  have hw : -((ρ : ℝ) * ((slackMass L sched v' n : ℚ) : ℝ)) ≤
      (realizedEnforcer L (warrantEnforcer sched)).netWorth
        (history L (warrantEnforcer sched)) w n := by
    unfold Trader.netWorth
    rw [← hsum]
    exact Finset.sum_le_sum fun t ht => hday t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
  have hρS : (ρ : ℝ) * ((slackMass L sched v' n : ℚ) : ℝ) ≤ (ρ : ℝ) * 3 :=
    mul_le_mul_of_nonneg_left hS.le (by exact_mod_cast hρ)
  linarith

/-- **Liability discharged by the odds bankroll**: a slack witness at every date gives the
`liability` hypothesis of `conditional_normative_inductor` with `B = 3ρ`. -/
theorem liability_of_odds (L : Assessment) (sched : ℕ → Presentation) (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hslack : ∀ n, ∃ v' : PCWorld, L.Live n v' ∧ ∀ w : PCWorld, L.Live n w →
      ∀ t ≤ n, ∀ r ∈ (sched t).rows,
        -(rowGap (sched t).coords r w) ≤ ρ * rowGap (sched t).coords r v') :
    ∀ n (v : PCWorld), L.Live n v →
      -(3 * (ρ : ℝ)) ≤
        (realizedEnforcer L (warrantEnforcer sched)).netWorth
          (history L (warrantEnforcer sched)) v n := by
  intro n v hv
  obtain ⟨v', hv', hgap⟩ := hslack n
  exact netWorth_ge_neg_odds L sched ρ hρ n v' hv' v (hgap v hv)

open Workspace.Normativity.Contrib.NormativeInductionInterface in
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Protocol) in
open Workspace.Normativity.Contrib.OpenIntegrityEvolution (ObligationState) in
/-- **The warrant Normative Inductor.**  `conditional_normative_inductor` at the warrant
enforcer, its `liability` hypothesis discharged by the odds bankroll; the computable-market
and uptake hypotheses are the theorem's own. -/
theorem warrant_normative_inductor {Occ Req Service : Type*} {S : Protocol Occ Req}
    {anchor : Occ → Req} {O : ObligationState S anchor} (E : Evaluation O Service)
    (L : Assessment) (sched : ℕ → Presentation) (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hslack : ∀ n, ∃ v' : PCWorld, L.Live n v' ∧ ∀ w : PCWorld, L.Live n w →
      ∀ t ≤ n, ∀ r ∈ (sched t).rows,
        -(rowGap (sched t).coords r w) ≤ ρ * rowGap (sched t).coords r v')
    (computableMarket : ComputableMarket (history L (warrantEnforcer sched)))
    (cert : E.PracticalUptake (history L (warrantEnforcer sched))) :
    L.IsLogicalInductor (history L (warrantEnforcer sched)) ∧
    (0 ≤ E.residual ∧ E.residual ≤ 1) ∧
    E.progress (history L (warrantEnforcer sched)) ≤ E.modulus + E.error + E.D * E.residual :=
  E.conditional_normative_inductor L (warrantEnforcer sched) (3 * (ρ : ℝ))
    (liability_of_odds L sched ρ hρ hslack) computableMarket cert

/-- **World-inclusive rows cost nothing**: when every row's gap at a world is nonnegative
at every date through `n`, the enforcer's net worth there is nonnegative — the deductive
case's `B = 0`, recovered as `ρ = 0`. -/
theorem netWorth_nonneg_of_inclusive (L : Assessment) (sched : ℕ → Presentation) (n : ℕ)
    (w : PCWorld) (hw : ∀ t ≤ n, ∀ r ∈ (sched t).rows, 0 ≤ rowGap (sched t).coords r w) :
    0 ≤ (realizedEnforcer L (warrantEnforcer sched)).netWorth
      (history L (warrantEnforcer sched)) w n := by
  unfold Trader.netWorth
  refine Finset.sum_nonneg fun t ht => ?_
  have htn : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  refine le_trans ?_ (day_value_ge L sched t w)
  have : 0 ≤ ∑ i, rowUnits (sched t) i (quote L (warrantEnforcer sched) t) *
      rowGap (sched t).coords ((sched t).rowAt i) w :=
    Finset.sum_nonneg fun i _ => mul_nonneg (rowUnits_nonneg _ _ _)
      (hw t htn _ (List.get_mem _ _))
  exact_mod_cast this

/-- A date with no rows trades nothing. -/
theorem day_value_eq_zero_of_rows_nil (L : Assessment) (sched : ℕ → Presentation) (t : ℕ)
    (h : (sched t).rows = []) (v : PCWorld) :
    ((realizedEnforcer L (warrantEnforcer sched)).strat t).value
      (history L (warrantEnforcer sched)) v.payout = 0 := by
  rw [day_value_eq]
  have hempty : IsEmpty (Fin (sched t).rows.length) := by
    rw [h]; exact Fin.isEmpty'
  simp

/-- **Frozen tail**: a trader that trades nothing after date `m` has at every later date the
net worth it had at `m`. -/
theorem netWorth_eq_of_tail_zero (Tr : Trader) (P : History) (v : PCWorld) {m n : ℕ}
    (hmn : m ≤ n) (hz : ∀ t, m < t → (Tr.strat t).value P v.payout = 0) :
    Tr.netWorth P v n = Tr.netWorth P v m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, Trader.netWorth, Finset.sum_range_succ, ← Trader.netWorth,
        ih (by omega), hz _ (by omega), add_zero]

/-- `ofDeductiveProcess` is globally nested. -/
theorem ofDeductiveProcess_nested (DP : DeductiveProcess) {m n : ℕ} (h : m ≤ n) (v : PCWorld)
    (hv : (ofDeductiveProcess DP).Live n v) : (ofDeductiveProcess DP).Live m v := by
  intro φ hφ
  have hmono : ∀ k, DP.D m ⊆ DP.D (m + k) := by
    intro k
    induction k with
    | zero => exact fun _ h => h
    | succ k ih => exact fun x hx => DP.mono (m + k) (ih hx)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact hv φ (hmono k hφ)

end Fork

/-! ## Part B — the fixture -/

namespace Fixture

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementPreservation
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-- The three atoms. -/
def X : Sentence := .atom 0
def A : Sentence := .atom 1
def Y : Sentence := .atom 2
/-- `X ∧ A`. -/
def XA : Sentence := X ⋏ A
/-- `X ∧ A ∧ Y`, associated `(X ∧ A) ∧ Y`. -/
def XAY : Sentence := XA ⋏ Y
/-- `¬Y`. -/
def negY : Sentence := ∼Y

@[simp] lemma X_ne_XA : X ≠ XA := by simp [X, XA]
@[simp] lemma X_ne_XAY : X ≠ XAY := by simp [X, XAY, XA]
@[simp] lemma X_ne_Y : X ≠ Y := by simp [X, Y]
@[simp] lemma XA_ne_X : XA ≠ X := by simp [X, XA]
@[simp] lemma XA_ne_XAY : XA ≠ XAY := by intro h; cases h
@[simp] lemma XA_ne_Y : XA ≠ Y := by simp [XA, Y]
@[simp] lemma XAY_ne_X : XAY ≠ X := by simp [X, XAY, XA]
@[simp] lemma XAY_ne_XA : XAY ≠ XA := by intro h; cases h
@[simp] lemma XAY_ne_Y : XAY ≠ Y := by simp [XAY, Y]
@[simp] lemma Y_ne_X : Y ≠ X := by simp [X, Y]
@[simp] lemma Y_ne_XA : Y ≠ XA := by simp [XA, Y]
@[simp] lemma Y_ne_XAY : Y ≠ XAY := by simp [XAY, Y]

lemma holds_XA (v : PCWorld) : v.Holds XA ↔ v.Holds X ∧ v.Holds A := Iff.rfl
lemma holds_XAY (v : PCWorld) : v.Holds XAY ↔ v.Holds XA ∧ v.Holds Y := Iff.rfl
lemma holds_negY (v : PCWorld) : v.Holds negY ↔ ¬ v.Holds Y := by
  show LO.Propositional.Formula.Boolean.val v (∼Y) ↔ ¬ _
  simp [LO.Propositional.Formula.Boolean.val, PCWorld.Holds]

/-- The priced fragment. -/
def coordList : List Sentence := [X, XA, XAY, Y]

lemma coordList_nodup : coordList.Nodup := by simp [coordList]

/-- The coordinate map from the seed's four coordinates to the fragment. -/
def ι : Fin 4 → Sentence := ![X, XA, XAY, Y]

@[simp] lemma ι_zero : ι 0 = X := rfl
@[simp] lemma ι_one : ι 1 = XA := rfl
@[simp] lemma ι_two : ι 2 = XAY := rfl
@[simp] lemma ι_three : ι 3 = Y := rfl

/-- **The bridge from a seed row to a force row.**  A seed row `a · x ≤ b` on `Fin d`
coordinates becomes the force row `⟨coeff, P⟩ ≥ −b` with `coeff φ = −Σ_{j : ι j = φ} a j`,
at a declared intensity. -/
def toForceRow {d : ℕ} (ι : Fin d → Sentence) (β : ℚ) (hβ : 0 ≤ β) (r : Row d) : Row where
  coeff φ := ∑ j, if ι j = φ then -r.a j else 0
  rhs := -r.b
  intensity := β
  intensity_nonneg := hβ

/-- The bridge's pairing: on a coordinate set containing the image, the force row's pairing
is the negated seed row's left-hand side. -/
theorem toForceRow_pair {d : ℕ} (ι : Fin d → Sentence) (β : ℚ) (hβ : 0 ≤ β) (r : Row d)
    (coords : Finset Sentence) (hι : ∀ j, ι j ∈ coords) (w : Sentence → ℚ) :
    pair coords (toForceRow ι β hβ r).coeff w = -∑ j, r.a j * w (ι j) := by
  unfold pair toForceRow
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq coords (ι j), if_pos (hι j)]
  ring

/-- The bridge's gap at a world: how far the world clears the seed row. -/
theorem toForceRow_gap {d : ℕ} (ι : Fin d → Sentence) (β : ℚ) (hβ : 0 ≤ β) (r : Row d)
    (coords : Finset Sentence) (hι : ∀ j, ι j ∈ coords) (v : PCWorld) :
    rowGap coords (toForceRow ι β hβ r) v = r.b - ∑ j, r.a j * ratPayout v (ι j) := by
  unfold rowGap
  rw [toForceRow_pair ι β hβ r coords hι]
  simp [toForceRow]
  ring

/-- The strengths. -/
structure Strengths where
  P : ℚ
  A : ℚ
  S : ℚ
  P_pos : 0 < P
  P_lt : P < 1
  A_pos : 0 < A
  A_lt : A < 1
  S_pos : 0 < S
  S_lt : S < 1

/-- The three rows of the warrant, through the bridge. -/
def premiseRow (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) : Row :=
  toForceRow ι β hβ (Form.premise 0 c.P).row
def applRow (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) : Row :=
  toForceRow ι β hβ (Form.applicability 0 1 c.A).row
def strengthRow (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) : Row :=
  toForceRow ι β hβ (Form.strength 1 2 c.S).row

/-- The live rows at date `n` when the applicability port is defeated from `n₀`. -/
def rowsAt (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ n : ℕ) : List Row :=
  premiseRow c β hβ :: ((if n < n₀ then [applRow c β hβ] else []) ++ [strengthRow c β hβ])

/-- A presentation on the fragment with the given rows. -/
def pres (rows : List Row) : Presentation := ⟨coordList, coordList_nodup, rows⟩

@[simp] lemma pres_rows (rows : List Row) : (pres rows).rows = rows := rfl

lemma ι_mem_coords (j : Fin 4) : ι j ∈ (pres []).coords := by
  fin_cases j <;> simp [Presentation.coords, pres, coordList, ι]

/-- The schedule with every row live (no withholding). -/
def schedLive (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ : ℕ) : ℕ → Presentation :=
  fun n => pres (rowsAt c β hβ n₀ n)

/-- The schedule withholding force from `nE` on. -/
def schedWithheld (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ nE : ℕ) : ℕ → Presentation :=
  fun n => pres (if n < nE then rowsAt c β hβ n₀ n else [])

/-- **The settlement process**: `X` from `n₁`, and from `nE` the declared evaluation of
`Y` — `Y` itself if `e`, `¬Y` otherwise.  Deductive settlement and evaluation settlement
enter here in the same way: as members of the stage. -/
def stage (n₁ nE : ℕ) (e : Bool) (n : ℕ) : Finset Sentence :=
  (if n₁ ≤ n then {X} else ∅) ∪ (if nE ≤ n then {if e then Y else negY} else ∅)

lemma mem_stage (n₁ nE : ℕ) (e : Bool) (n : ℕ) (φ : Sentence) :
    φ ∈ stage n₁ nE e n ↔ (n₁ ≤ n ∧ φ = X) ∨ (nE ≤ n ∧ φ = (if e then Y else negY)) := by
  unfold stage
  by_cases h₁ : n₁ ≤ n <;> by_cases h₂ : nE ≤ n <;> simp [h₁, h₂]

lemma stage_mono (n₁ nE : ℕ) (e : Bool) (n : ℕ) : stage n₁ nE e n ⊆ stage n₁ nE e (n + 1) := by
  intro φ hφ
  rw [mem_stage] at hφ ⊢
  rcases hφ with ⟨h, hφ⟩ | ⟨h, hφ⟩
  · exact Or.inl ⟨by omega, hφ⟩
  · exact Or.inr ⟨by omega, hφ⟩

/-- The deductive process of the fixture. -/
def dp (n₁ nE : ℕ) (e : Bool) : DeductiveProcess where
  D := stage n₁ nE e
  mono := stage_mono n₁ nE e

/-- The fixture's assessment process. -/
def L (n₁ nE : ℕ) (e : Bool) : Assessment := ofDeductiveProcess (dp n₁ nE e)

lemma live_iff (n₁ nE : ℕ) (e : Bool) (n : ℕ) (v : PCWorld) :
    (L n₁ nE e).Live n v ↔
      (n₁ ≤ n → v.Holds X) ∧ (nE ≤ n → v.Holds (if e then Y else negY)) := by
  show v.ConsistentWith (stage n₁ nE e n) ↔ _
  unfold PCWorld.ConsistentWith
  constructor
  · intro h
    exact ⟨fun h₁ => h X ((mem_stage _ _ _ _ _).2 (Or.inl ⟨h₁, rfl⟩)),
      fun h₂ => h _ ((mem_stage _ _ _ _ _).2 (Or.inr ⟨h₂, rfl⟩))⟩
  · rintro ⟨h₁, h₂⟩ φ hφ
    rcases (mem_stage _ _ _ _ _).1 hφ with ⟨hn, rfl⟩ | ⟨hn, rfl⟩
    · exact h₁ hn
    · exact h₂ hn

/-- The all-true world is live whenever the evaluation affirms `Y`. -/
lemma allTrue_live (n₁ nE : ℕ) (n : ℕ) : (L n₁ nE true).Live n allTrue := by
  rw [live_iff]
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- The all-true world is live before the evaluation, whatever it says. -/
lemma allTrue_live_before (n₁ nE : ℕ) (e : Bool) (n : ℕ) (hn : n < nE) :
    (L n₁ nE e).Live n allTrue := by
  rw [live_iff]
  exact ⟨fun _ => trivial, fun h => absurd h (by omega)⟩

/-! ### The gaps -/

open Classical in
lemma ratPayout_X (v : PCWorld) : ratPayout v X = if v.Holds X then 1 else 0 := rfl
open Classical in
lemma ratPayout_XA (v : PCWorld) :
    ratPayout v XA = if v.Holds X ∧ v.Holds A then 1 else 0 := by
  by_cases h : v.Holds X ∧ v.Holds A
  · have h' : v.Holds XA := (holds_XA v).2 h
    simp [ratPayout, h, h']
  · have h' : ¬ v.Holds XA := fun hx => h ((holds_XA v).1 hx)
    simp [ratPayout, h, h']
open Classical in
lemma ratPayout_XAY (v : PCWorld) :
    ratPayout v XAY = if (v.Holds X ∧ v.Holds A) ∧ v.Holds Y then 1 else 0 := by
  by_cases h : (v.Holds X ∧ v.Holds A) ∧ v.Holds Y
  · have h' : v.Holds XAY := (holds_XAY v).2 ⟨(holds_XA v).2 h.1, h.2⟩
    simp [ratPayout, h, h']
  · have h' : ¬ v.Holds XAY := fun hx => h ⟨(holds_XA v).1 ((holds_XAY v).1 hx).1,
      ((holds_XAY v).1 hx).2⟩
    simp [ratPayout, h, h']

lemma gap_premise (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (v : PCWorld) :
    rowGap (pres []).coords (premiseRow c β hβ) v = ratPayout v X - c.P := by
  rw [premiseRow, toForceRow_gap ι β hβ _ _ ι_mem_coords]
  simp [Form.row]
  ring

lemma gap_appl (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (v : PCWorld) :
    rowGap (pres []).coords (applRow c β hβ) v = ratPayout v XA - c.A * ratPayout v X := by
  rw [applRow, toForceRow_gap ι β hβ _ _ ι_mem_coords]
  simp [Form.row, Fin.sum_univ_four]
  ring

lemma gap_strength (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (v : PCWorld) :
    rowGap (pres []).coords (strengthRow c β hβ) v = ratPayout v XAY - c.S * ratPayout v XA := by
  rw [strengthRow, toForceRow_gap ι β hβ _ _ ι_mem_coords]
  simp [Form.row, Fin.sum_univ_four]
  ring

/-- The odds of a strength. -/
def odds (c : ℚ) : ℚ := c / (1 - c)

lemma odds_spec {c : ℚ} (h1 : c < 1) : c = odds c * (1 - c) := by
  unfold odds
  have : (1 - c) ≠ 0 := by linarith
  field_simp

lemma odds_nonneg {c : ℚ} (h0 : 0 < c) (h1 : c < 1) : 0 ≤ odds c :=
  div_nonneg h0.le (by linarith)

/-- The fixture's odds: the largest of the three. -/
def ρ (c : Strengths) : ℚ := max (odds c.P) (max (odds c.A) (odds c.S))

lemma ρ_nonneg (c : Strengths) : 0 ≤ ρ c :=
  le_max_of_le_left (odds_nonneg c.P_pos c.P_lt)

lemma le_of_odds_le {a ρ' : ℚ} (h1 : a < 1) (h : odds a ≤ ρ') : a ≤ ρ' * (1 - a) := by
  have h3 : 0 ≤ 1 - a := by linarith
  calc a = odds a * (1 - a) := odds_spec h1
    _ ≤ ρ' * (1 - a) := mul_le_mul_of_nonneg_right h h3

lemma P_le (c : Strengths) : c.P ≤ ρ c * (1 - c.P) :=
  le_of_odds_le c.P_lt (le_max_left _ _)
lemma A_le (c : Strengths) : c.A ≤ ρ c * (1 - c.A) :=
  le_of_odds_le c.A_lt (le_max_of_le_right (le_max_left _ _))
lemma S_le (c : Strengths) : c.S ≤ ρ c * (1 - c.S) :=
  le_of_odds_le c.S_lt (le_max_of_le_right (le_max_right _ _))

lemma allTrue_holds (φ : Sentence) (h : φ = X ∨ φ = A ∨ φ = Y) : allTrue.Holds φ := by
  rcases h with rfl | rfl | rfl <;> trivial

/-- **Every world's deficit on every row is dominated by the all-true world's surplus at
the odds.**  No liveness hypothesis: the domination holds at every propositionally
consistent world. -/
theorem gap_dominated (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (r : Row)
    (hr : r = premiseRow c β hβ ∨ r = applRow c β hβ ∨ r = strengthRow c β hβ)
    (w : PCWorld) :
    -(rowGap (pres []).coords r w) ≤ ρ c * rowGap (pres []).coords r allTrue := by
  have hρ := ρ_nonneg c
  have hP := P_le c
  have hA := A_le c
  have hS := S_le c
  have hallX : allTrue.Holds X := allTrue_holds X (Or.inl rfl)
  have hallA : allTrue.Holds A := allTrue_holds A (Or.inr (Or.inl rfl))
  have hallY : allTrue.Holds Y := allTrue_holds Y (Or.inr (Or.inr rfl))
  rcases hr with rfl | rfl | rfl
  · rw [gap_premise, gap_premise, ratPayout_X, ratPayout_X]
    by_cases hX : w.Holds X <;> simp [hX, hallX] <;> nlinarith [c.P_pos, c.P_lt]
  · rw [gap_appl, gap_appl, ratPayout_XA, ratPayout_X, ratPayout_XA, ratPayout_X]
    by_cases hX : w.Holds X <;> by_cases hA' : w.Holds A <;>
      simp [hX, hA', hallX, hallA] <;> nlinarith [c.A_pos, c.A_lt]
  · rw [gap_strength, gap_strength, ratPayout_XAY, ratPayout_XA, ratPayout_XAY, ratPayout_XA]
    by_cases hX : w.Holds X <;> by_cases hA' : w.Holds A <;> by_cases hY : w.Holds Y <;>
      simp [hX, hA', hY, hallX, hallA, hallY] <;> nlinarith [c.S_pos, c.S_lt]

lemma mem_rowsAt {c : Strengths} {β : ℚ} {hβ : 0 ≤ β} {n₀ n : ℕ} {r : Row}
    (h : r ∈ rowsAt c β hβ n₀ n) :
    r = premiseRow c β hβ ∨ r = applRow c β hβ ∨ r = strengthRow c β hβ := by
  unfold rowsAt at h
  by_cases hn : n < n₀ <;> simp [hn] at h <;> tauto

/-- **B(i)/(ii)/(iii), the affirming case.**  With `Y` affirmed by the evaluation (or never
settled: take `nE` beyond every date of interest), the all-true world is live at every
date and the enforcer's assessed net worth is at least `−3ρ` at every live world at every
date, under every settlement date `n₁` of `X` and every defeat date `n₀`. -/
theorem liability (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ n₁ nE : ℕ) :
    ∀ n (v : PCWorld), (L n₁ nE true).Live n v →
      -(3 * (ρ c : ℝ)) ≤
        (realizedEnforcer (L n₁ nE true) (warrantEnforcer (schedLive c β hβ n₀))).netWorth
          (history (L n₁ nE true) (warrantEnforcer (schedLive c β hβ n₀))) v n :=
  liability_of_odds (L n₁ nE true) (schedLive c β hβ n₀) (ρ c) (ρ_nonneg c) fun n =>
    ⟨allTrue, allTrue_live n₁ nE n, fun w _ _ _ r hr =>
      gap_dominated c β hβ r (mem_rowsAt hr) w⟩

/-- **B(ii), the disagreeing case.**  `Y` is evaluated false at `nE`; force is withheld
from `nE` on (the region is empty, `disagree_region_empty` below).  The bankroll is the
same `3ρ`: before `nE` the all-true world is live and dominates; from `nE` on the
enforcer's account is frozen at its value at `nE − 1`, where every world then live was
live. -/
theorem liability_disagree (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ n₁ nE : ℕ)
    (hnE : 0 < nE) :
    ∀ n (v : PCWorld), (L n₁ nE false).Live n v →
      -(3 * (ρ c : ℝ)) ≤
        (realizedEnforcer (L n₁ nE false)
          (warrantEnforcer (schedWithheld c β hβ n₀ nE))).netWorth
          (history (L n₁ nE false) (warrantEnforcer (schedWithheld c β hβ n₀ nE))) v n := by
  intro n v hv
  have hgap : ∀ (w : PCWorld) (t : ℕ), ∀ r ∈ (schedWithheld c β hβ n₀ nE t).rows,
      -(rowGap (schedWithheld c β hβ n₀ nE t).coords r w) ≤
        ρ c * rowGap (schedWithheld c β hβ n₀ nE t).coords r allTrue := by
    intro w t r hr
    simp only [schedWithheld, pres_rows] at hr
    split_ifs at hr with ht
    · exact gap_dominated c β hβ r (mem_rowsAt hr) w
    · simp at hr
  by_cases hn : n < nE
  · exact netWorth_ge_neg_odds (L n₁ nE false) (schedWithheld c β hβ n₀ nE) (ρ c) (ρ_nonneg c)
      n allTrue (allTrue_live_before n₁ nE false n hn) v (fun t _ r hr => hgap v t r hr)
  · have hle : nE - 1 ≤ n := by omega
    rw [netWorth_eq_of_tail_zero _ _ v hle (fun t ht =>
      day_value_eq_zero_of_rows_nil (L n₁ nE false) (schedWithheld c β hβ n₀ nE) t (by
        simp only [schedWithheld, pres_rows]
        rw [if_neg (by omega)]) v)]
    have hv' : (L n₁ nE false).Live (nE - 1) v := ofDeductiveProcess_nested _ hle v hv
    exact netWorth_ge_neg_odds (L n₁ nE false) (schedWithheld c β hβ n₀ nE) (ρ c) (ρ_nonneg c)
      (nE - 1) allTrue (allTrue_live_before n₁ nE false (nE - 1) (by omega)) v
      (fun t _ r hr => hgap v t r hr)

/-! ### The seed side: emptiness on disagreement, and the orphan pin -/

/-- The warrant as three occurrences on the seed's four coordinates. -/
def occP (c : Strengths) : Occurrence 4 := ⟨1, Form.premise 0 c.P, .none, .party 1, ∅⟩
def occA (c : Strengths) : Occurrence 4 :=
  ⟨2, Form.applicability 0 1 c.A, .occurrence 1, .party 1, ∅⟩
def occS (c : Strengths) : Occurrence 4 :=
  ⟨3, Form.strength 1 2 c.S, .occurrence 2, .party 1, {2}⟩

/-- The grounds: the warrant's three occurrences. -/
def grounds (c : Strengths) : Grounds 4 := [occP c, occA c, occS c]

/-- The settlement after `X` true and `Y` false, with the closure `X∧A∧Y` false. -/
def settledDisagree : Settlement 4 :=
  ⟨![some true, none, some false, some false]⟩

lemma settledDisagree_pinned_iff (x : Fin 4 → ℚ) :
    settledDisagree.Pinned x ↔ x 0 = 1 ∧ x 2 = 0 ∧ x 3 = 0 := by
  unfold Settlement.Pinned settledDisagree truth
  constructor
  · intro h
    exact ⟨by simpa using h 0 true rfl, by simpa using h 2 false rfl,
      by simpa using h 3 false rfl⟩
  · rintro ⟨h0, h2, h3⟩ i b hi
    fin_cases i <;> simp_all

/-- **The region empties on disagreement** while the applicability row is live: the chain
`P(X) ≥ c_P`, `P(X∧A) ≥ c_A P(X)`, `P(X∧A∧Y) ≥ c_S P(X∧A)` with `X∧A∧Y` pinned to `0`
forces `P(X∧A) = 0`, then `c_A ≤ 0`. -/
theorem disagree_region_empty (c : Strengths) :
    ¬ ∃ x, (grounds c).region DocketState.quiet settledDisagree x := by
  rintro ⟨x, hx⟩
  rw [Grounds.region_iff] at hx
  obtain ⟨-, hpin, h⟩ := hx
  obtain ⟨h0, h2, -⟩ := (settledDisagree_pinned_iff x).1 hpin
  have hA := h (occA c) (by simp [grounds]) (by simp [DocketState.quiet])
  have hS := h (occS c) (by simp [grounds]) (by simp [DocketState.quiet])
  simp only [occA, occS] at hA hS
  rw [Form.applicability_sat_iff] at hA
  rw [Form.strength_sat_iff] at hS
  rw [h0] at hA
  rw [h2] at hS
  nlinarith [c.A_pos, c.S_pos, hA, hS]

/-- The docket after the applicability port is defeated. -/
def docketDefeatA : DocketState := ⟨{2}, ∅⟩

/-- **The orphan pin.**  After the applicability port is defeated, the same disagreement
leaves the region **nonempty**: the point `(1, 0, 0, 0)` lies in it. -/
theorem orphan_region_nonempty (c : Strengths) :
    (grounds c).region docketDefeatA settledDisagree ![1, 0, 0, 0] := by
  rw [Grounds.region_iff]
  refine ⟨fun i => by fin_cases i <;> norm_num,
    (settledDisagree_pinned_iff _).2 ⟨rfl, rfl, rfl⟩, ?_⟩
  intro o ho hid
  simp only [grounds, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · simp only [occP]
    rw [Form.premise_sat_iff]
    simpa using c.P_lt.le
  · exact absurd (by simp [occA, docketDefeatA]) hid
  · simp only [occS]
    rw [Form.strength_sat_iff]
    simp

/-- The world with `A` true and `Y` false. -/
def wAY : PCWorld := fun a => a ≠ 2

lemma wAY_X : wAY.Holds X := by show (0 : ℕ) ≠ 2; decide
lemma wAY_A : wAY.Holds A := by show (1 : ℕ) ≠ 2; decide
lemma wAY_notY : ¬ wAY.Holds Y := by show ¬ ((2 : ℕ) ≠ 2); decide

/-- **No slack world for the orphaned strength row.**  Every world live after the
disagreement (`Y` false) has nonpositive gap on the strength row, and the live world with
`X`, `A` true and `Y` false has a strictly negative one: the hypothesis of the odds
bankroll fails on the orphaned row. -/
theorem orphan_no_slack (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₁ nE : ℕ) (n : ℕ) (hn : nE ≤ n) :
    (∀ v : PCWorld, (L n₁ nE false).Live n v →
      rowGap (pres []).coords (strengthRow c β hβ) v ≤ 0) ∧
    ((L n₁ nE false).Live n wAY ∧ rowGap (pres []).coords (strengthRow c β hβ) wAY < 0) := by
  constructor
  · intro v hv
    have hY : ¬ v.Holds Y := by
      have := ((live_iff _ _ _ _ _).1 hv).2 hn
      simpa [holds_negY] using this
    rw [gap_strength, ratPayout_XAY, ratPayout_XA]
    by_cases hX : v.Holds X <;> by_cases hA' : v.Holds A <;> simp [hX, hA', hY]
    linarith [c.S_pos]
  · refine ⟨?_, ?_⟩
    · rw [live_iff]
      exact ⟨fun _ => wAY_X, fun _ => by simpa [holds_negY] using wAY_notY⟩
    · rw [gap_strength, ratPayout_XAY, ratPayout_XA]
      simp [wAY_X, wAY_A, wAY_notY]
      exact c.S_pos

end Fixture

/-! ## Part C — the record of a market run -/

section RecordPart

open LogicalInduction
open Workspace.Normativity.Contrib.TraderizedEnforcement
open Workspace.Deference.Contrib.ReasonMediatedAuthorship

/-- **A market run**: per date, the admitted grounds, the docket, the settlement, the
certificate events (event id, selected?), the authorized events — and the prices. -/
structure MarketRun (d : ℕ) where
  grounds : ℕ → Grounds d
  docket : ℕ → DocketState
  settlement : ℕ → Settlement d
  certs : ℕ → List (ℕ × Bool)
  authorized : ℕ → Finset ℕ
  prices : ℕ → Fin d → ℚ

/-- **A record entry**: the record state at the date, the certificate events, and the
enforcer's position.  No prices. -/
structure RecordEntry (d : ℕ) where
  state : RecordState d
  certs : List (ℕ × Bool)
  position : Fin d → ℚ

/-- **The record**: one entry per date. -/
abbrev Record (d : ℕ) := ℕ → RecordEntry d

/-- The enforcer's position on the settled bundle at a price, at a uniform intensity: the
force algebra's position formula `Σ_rows β · violation · normal` on the bundle's rows read
as `⟨−a, ·⟩ ≥ −b`, summed along the bundle. -/
def positionOf (B : Bundle (Cite d) d) (β : ℚ) (p : Fin d → ℚ) : Fin d → ℚ := fun k =>
  (B.map fun c =>
    β * violation Finset.univ (fun j => -c.row.a j) (-c.row.b) p * (-c.row.a k)).sum

/-- The list form agrees with the force algebra's `position` over the bundle's indices. -/
theorem positionOf_eq_position (B : Bundle (Cite d) d) (β : ℚ) (p : Fin d → ℚ) (k : Fin d) :
    positionOf B β p k =
      position (Finset.univ : Finset (Fin B.length)) Finset.univ
        (fun i j => -(B.get i).row.a j) (fun i => -(B.get i).row.b) (fun _ => β) p k := by
  unfold positionOf position
  rw [← List.sum_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get B]
  rw [List.map_ofFn]
  rfl

/-- **The trace**: the record of a market run.  Prices enter only through the position. -/
def trace (run : MarketRun d) (β : ℚ) : Record d := fun n =>
  { state := ⟨run.grounds n, run.docket n, run.settlement n, run.authorized n⟩
    certs := run.certs n
    position := positionOf ((run.grounds n).settledBundle (run.docket n) (run.settlement n)) β
      (run.prices n) }

/-- **`Licensed` is decidable from the record alone.** -/
def decideLicensed {m m' : ℕ} (rec : Record d) (n : ℕ) (φ : Fin d) (v : ℚ)
    (c : VerdictCert d m m' φ) (event : ℕ) : Bool :=
  decide (Licensed (rec n).state φ v c event)

theorem decideLicensed_iff {m m' : ℕ} (rec : Record d) (n : ℕ) (φ : Fin d) (v : ℚ)
    (c : VerdictCert d m m' φ) (event : ℕ) :
    decideLicensed rec n φ v c event = true ↔ Licensed (rec n).state φ v c event :=
  decide_eq_true_iff

namespace RecordFixture

/-- The one-coordinate base run: the countermodel's grounds, quiet docket, no events, a
constant price. -/
def baseRun (p : ℚ) : MarketRun 1 where
  grounds _ := Countermodel.G
  docket _ := DocketState.quiet
  settlement _ := Countermodel.F
  certs _ := []
  authorized _ := ∅
  prices _ _ := p

/-- A run whose docket defeats `r₁`. -/
def defeatRun : MarketRun 1 where
  grounds _ := Countermodel.G
  docket _ := Countermodel.stDefeat
  settlement _ := Countermodel.F
  certs _ := []
  authorized _ := ∅
  prices _ _ := 1/2

/-- A price at or above the row leaves the position at zero. -/
lemma positionOf_base_eq_zero (β : ℚ) (p : ℚ) (hp : (1/2 : ℚ) ≤ p) :
    positionOf (Countermodel.G.settledBundle DocketState.quiet Countermodel.F) β (fun _ => p) = 0 := by
  rw [Countermodel.settledBundle_quiet]
  funext k
  have hviol : violation Finset.univ (fun j => -Countermodel.premRow.a j)
      (-Countermodel.premRow.b) (fun _ => p) = 0 := by
    unfold violation pair
    rw [Countermodel.premRow_b, Countermodel.premRow_a]
    simp
    linarith
  simp only [positionOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hviol,
    Pi.zero_apply]
  ring

/-- **The record is not injective in the run**: two runs with different prices, both
clearing the row, have the same record. -/
theorem trace_not_injective (β : ℚ) :
    baseRun (1/2) ≠ baseRun 1 ∧ trace (baseRun (1/2)) β = trace (baseRun 1) β := by
  constructor
  · intro h
    have := congrArg (fun r : MarketRun 1 => r.prices 0 0) h
    norm_num [baseRun] at this
  · funext n
    simp only [trace, baseRun]
    rw [positionOf_base_eq_zero β _ le_rfl, positionOf_base_eq_zero β _ (by norm_num)]

/-- **The record is not constant in the run**: a defeat shows in it. -/
theorem trace_not_const (β : ℚ) : trace (baseRun (1/2)) β ≠ trace defeatRun β := by
  intro h
  have := congrArg (fun r : Record 1 => (r 0).state.docket) h
  simp [trace, baseRun, defeatRun, DocketState.quiet, Countermodel.stDefeat] at this

/-- The audited class of runs. -/
def runs : Set (MarketRun 1) := {baseRun (1/2), baseRun 1, defeatRun}

/-- The frame: a run is its own world. -/
def β' : MarketRun 1 → Unit → MarketRun 1 := fun q _ => q

lemma mem_runs₁ : baseRun (1/2) ∈ runs := Set.mem_insert _ _
lemma mem_runs₂ : baseRun 1 ∈ runs := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
lemma mem_runs₃ : defeatRun ∈ runs :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- **Not over-rich**: the trace is not injective on the audited class, so
`reasonMediated_of_injOn` does not make mediation by the record vacuous. -/
theorem trace_not_injOn (β : ℚ) : ¬ Set.InjOn (fun q => trace (β' q ()) β) runs := by
  intro h
  exact (trace_not_injective β).1 (h mem_runs₁ mem_runs₂ (trace_not_injective β).2)

/-- **Not under-rich**: the trace is not constant on the audited class, so
`reasonMediated_const_iff`'s isolated-principal reading does not apply. -/
theorem trace_not_constant (β : ℚ) : ¬ ∃ r₀, ∀ q ∈ runs, trace (β' q ()) β = r₀ := by
  rintro ⟨r₀, h⟩
  exact trace_not_const β ((h _ mem_runs₁).trans (h _ mem_runs₃).symm)

/-- **Prices are not mediated by the record**: the payload "the price of `φ`" is not
reason-mediated by the trace on the audited class — the record is strictly coarser than
the run. -/
theorem price_not_mediated (β : ℚ) :
    ¬ ReasonMediated β' (fun q => trace q β) (fun q => q.prices 0 0) runs () := by
  intro h
  have := h (baseRun (1/2)) mem_runs₁ (baseRun 1) mem_runs₂ (trace_not_injective β).2
  norm_num [β', baseRun] at this

/-- **The docket is mediated by the record**: the payload "the docket" factors through the
trace. -/
theorem docket_mediated (β : ℚ) :
    ReasonMediated β' (fun q => trace q β) (fun q => q.docket) runs () := by
  intro q _ q' _ h
  funext n
  have := congrArg (fun r : Record 1 => (r n).state.docket) h
  simpa [trace, β'] using this

end RecordFixture

end RecordPart

/-! ## Nonvacuity witnesses -/

namespace Witness

open LogicalInduction
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-- `Settlement`, `Seed`, `DocketState`, `SubItem`, `StrItem`, `Constitutive`. -/
def settlement : Settlement 2 := ⟨![some true, none]⟩
def subItem : SubItem 2 := ⟨Form.premise 0 (1/3), 0⟩
def strItem : StrItem 2 := ⟨cubeUpper 1, .coherence, 5⟩
def constitutive : Constitutive 2 Unit := ⟨{()}, {1}⟩
def seed : Seed 2 Unit := ⟨[subItem], [strItem], constitutive⟩
def docket : DocketState := ⟨{0}, {5}⟩

/-- The seed's forced region on the settlement is inhabited. -/
theorem seed_region_inhabited :
    forcedRegion seed [] DocketState.quiet settlement ![1, 1/2] := by
  rw [forcedRegion_iff]
  refine ⟨fun i => by fin_cases i <;> norm_num, ?_, ?_, ?_⟩
  · intro i b hi
    fin_cases i <;> simp_all [settlement, truth]
  · intro it hit
    simp [seed, Seed.liveSub, DocketState.quiet, subItem] at hit
    subst hit
    rw [Form.premise_sat_iff]; norm_num
  · intro it hit
    simp [seed, Seed.liveStr, DocketState.quiet, strItem] at hit
    subst hit
    exact cubeUpper_sat (fun i => by fin_cases i <;> norm_num) 1

/-- `IsForcedInterval`: the countermodel's interval. -/
theorem forcedInterval : IsForcedInterval Countermodel.G.seed [] DocketState.quiet
    Countermodel.F Countermodel.φ (1/2) 1 := Countermodel.forcedInterval

/-- `BoundCert`, `VerdictCert`, `Occurrence`, `Grounds`, `RecordState`: the countermodel's. -/
def verdictCert : VerdictCert 1 1 1 Countermodel.φ := Countermodel.cert 1
def recordState : RecordState 1 := Countermodel.recordAuth

/-- `Supported` and `Licensed` are inhabited. -/
theorem licensed_inhabited : Licensed Countermodel.recordAuth Countermodel.φ (2/3)
    (Countermodel.cert 1) 7 := Countermodel.supported_not_licensed.2.2.1

/-- `Strengths`: `4/5, 3/4, 2/3`. -/
def strengths : Fixture.Strengths :=
  ⟨4/5, 3/4, 2/3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The fixture's odds: `max(4, max(3, 2)) = 4`, so the bankroll is `12`. -/
theorem strengths_odds : Fixture.ρ strengths = 4 := by
  simp [Fixture.ρ, Fixture.odds, strengths]
  norm_num

/-- The fixture's presentation at date `0`, defeat at `5`: three rows. -/
theorem sched_rows_length :
    (Fixture.schedLive strengths 10 (by norm_num) 5 0).rows.length = 3 := by
  simp [Fixture.schedLive, Fixture.pres, Fixture.rowsAt]

/-- **The fixture's bankroll is `12`**: `X` settled at `3`, the applicability port defeated
at `5`, `Y` affirmed at `8`, intensity `10`. -/
theorem fixture_liability :
    ∀ n (v : PCWorld), (Fixture.L 3 8 true).Live n v →
      -(12 : ℝ) ≤
        (Workspace.Normativity.Contrib.EnforcementPreservation.realizedEnforcer
          (Fixture.L 3 8 true)
          (warrantEnforcer (Fixture.schedLive strengths 10 (by norm_num) 5))).netWorth
          (Workspace.Normativity.Contrib.EnforcementPreservation.history
            (Fixture.L 3 8 true)
            (warrantEnforcer (Fixture.schedLive strengths 10 (by norm_num) 5))) v n := by
  have h := Fixture.liability strengths 10 (by norm_num) 5 3 8
  rw [strengths_odds] at h
  intro n v hv
  have := h n v hv
  norm_num at this ⊢
  exact this

/-- `MarketRun`, `Record`, `RecordEntry`: the Part C fixture, with a nonzero position when
the price violates the row — the record does carry the position. -/
theorem position_nonzero :
    positionOf (Countermodel.G.settledBundle DocketState.quiet Countermodel.F) 1 (fun _ => 0) 0 =
      1 := by
  rw [Countermodel.settledBundle_quiet]
  simp only [positionOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  unfold violation pair
  rw [Countermodel.premRow_b, Countermodel.premRow_a]
  norm_num

end Witness


/-! ### The countermodel to settlement-antitonicity of the settled region -/

namespace Countermodel

/-- One applicability form `P(1) ≥ (1/2) P(0)` on two coordinates. -/
def applOcc : Occurrence 2 := ⟨1, Form.applicability 0 1 (1/2), .none, .party 1, ∅⟩

/-- The settlement pinning the consequent false. -/
def pinConsequent : Settlement 2 := ⟨![none, some false]⟩

lemma empty_le_pinConsequent : (Settlement.empty 2).le pinConsequent := by
  intro i b h; simp [Settlement.empty] at h

/-- **`IsForcedInterval.mono`'s shape fails for the settled region.**  The point `(1, 0)`
is in the settled region after the consequent is pinned false (the row was rebutted) and
not before (the row `x₁ ≥ x₀/2` excludes it): more settlement, larger region. -/
theorem settled_not_anti :
    Grounds.settledRegion [applOcc] DocketState.quiet pinConsequent ![1, 0] ∧
    ¬ Grounds.settledRegion [applOcc] DocketState.quiet (Settlement.empty 2) ![1, 0] := by
  constructor
  · rw [Grounds.settledRegion_iff]
    refine ⟨fun i => by fin_cases i <;> norm_num, ?_, ?_⟩
    · intro i b hi
      fin_cases i <;> simp_all [pinConsequent, truth]
    · intro o ho
      rw [mem_survivors] at ho
      obtain ⟨hoG, -, hk, -⟩ := ho
      simp only [List.mem_singleton] at hoG
      subst hoG
      simp [settleOutcome, pinsFalse, applOcc, pinConsequent] at hk
  · intro hx
    rw [Grounds.settledRegion_iff] at hx
    obtain ⟨-, -, h⟩ := hx
    have hmem : applOcc ∈ Grounds.survivors [applOcc] DocketState.quiet (Settlement.empty 2) := by
      rw [mem_survivors]
      refine ⟨by simp, by simp [undercut, DocketState.quiet], ?_, ?_⟩
      · simp [settleOutcome, pinsFalse, applOcc, Settlement.empty]
      · simp [applOcc]
    have := h applOcc hmem
    simp only [applOcc] at this
    rw [Form.applicability_sat_iff] at this
    norm_num at this

end Countermodel

/-! ## Part A — the bankroll across a reopening -/

section ReopenedBankroll

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementPreservation
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-- One date's domination: deficits at `w` dominated by `ρ` times the surpluses at `v'`. -/
theorem dayGap_dominated (L : Assessment) (sched : ℕ → Presentation) (ρ : ℚ) (t : ℕ)
    (w v' : PCWorld)
    (hgap : ∀ r ∈ (sched t).rows, -(rowGap (sched t).coords r w) ≤ ρ * rowGap (sched t).coords r v') :
    -(ρ * dayGap L sched v' t) ≤ dayGap L sched w t := by
  unfold dayGap
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hu := rowUnits_nonneg (sched t) i (quote L (warrantEnforcer sched) t)
  have hg := hgap ((sched t).rowAt i) (List.get_mem _ _)
  nlinarith

/-- The slack mass through `n` is the sum of the day gaps over `range (n + 1)`. -/
lemma slackMass_eq (L : Assessment) (sched : ℕ → Presentation) (v : PCWorld) (n : ℕ) :
    slackMass L sched v n = ∑ t ∈ Finset.range (n + 1), dayGap L sched v t := rfl

/-- **The odds bankroll across one reopening.**  Before date `m` a live world `v₀` dominates
every enforced row at the odds (for the bounded world `w` and for the later witness `v'`);
from `m` on a live world `v'` dominates the rows then enforced.  The enforcer's assessed
net worth at `w` is at least `−3ρ(2 + ρ)`: the pre-reopening bankroll `3ρ`, plus `ρ`
times the post-reopening slack mass, which the market's capital bounds by `3` plus the
reopened mass `3ρ`.  The "same `3ρ`" is **not** recovered; the reopened mass is paid for. -/
theorem netWorth_ge_neg_odds_reopened (L : Assessment) (sched : ℕ → Presentation) (ρ : ℚ)
    (hρ : 0 ≤ ρ) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (v₀ : PCWorld) (hv₀ : L.Live (m - 1) v₀) (v' : PCWorld) (hv' : L.Live n v') (w : PCWorld)
    (hdom₀w : ∀ t < m, ∀ r ∈ (sched t).rows,
      -(rowGap (sched t).coords r w) ≤ ρ * rowGap (sched t).coords r v₀)
    (hdom₀v' : ∀ t < m, ∀ r ∈ (sched t).rows,
      -(rowGap (sched t).coords r v') ≤ ρ * rowGap (sched t).coords r v₀)
    (hdom' : ∀ t, m ≤ t → t ≤ n → ∀ r ∈ (sched t).rows,
      -(rowGap (sched t).coords r w) ≤ ρ * rowGap (sched t).coords r v') :
    -(3 * (ρ : ℝ) * (2 + ρ)) ≤
      (realizedEnforcer L (warrantEnforcer sched)).netWorth (history L (warrantEnforcer sched))
        w n := by
  set E := warrantEnforcer sched
  set P := history L E
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  -- the prefix through `m − 1`, bounded by the pre-reopening bankroll
  have hpre : -(3 * (ρ : ℝ)) ≤ (realizedEnforcer L E).netWorth P w (m - 1) :=
    netWorth_ge_neg_odds L sched ρ hρ (m - 1) v₀ hv₀ w
      (fun t ht r hr => hdom₀w t (by omega) r hr)
  -- the slack mass of `v₀` through `m − 1` is under the capital
  have hS₀ : ((slackMass L sched v₀ (m - 1) : ℚ) : ℝ) < 3 :=
    lt_of_le_of_lt (slackMass_le_netWorth L sched v₀ (m - 1))
      (enforcer_netWorth_lt_three L E (m - 1) v₀ hv₀)
  -- the slack mass of `v'` through `m − 1` is bounded below by the reopened mass
  have hSv'pre : -(ρ * slackMass L sched v₀ (m - 1)) ≤ slackMass L sched v' (m - 1) := by
    rw [slackMass_eq, slackMass_eq, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun t ht => ?_
    have htm : t < m := by have := Finset.mem_range.mp ht; omega
    exact dayGap_dominated L sched ρ t v' v₀ (hdom₀v' t htm)
  -- the slack mass of `v'` through `n` is under the capital
  have hSv' : ((slackMass L sched v' n : ℚ) : ℝ) < 3 :=
    lt_of_le_of_lt (slackMass_le_netWorth L sched v' n) (enforcer_netWorth_lt_three L E n v' hv')
  -- the tail of the slack mass of `v'`
  have htail_eq : ∑ t ∈ Finset.Ico m (n + 1), dayGap L sched v' t =
      slackMass L sched v' n - slackMass L sched v' (m - 1) := by
    rw [slackMass_eq, slackMass_eq, hm1]
    exact Finset.sum_Ico_eq_sub _ (by omega)
  -- the tail of the net worth at `w`
  have hworth : (realizedEnforcer L E).netWorth P w n =
      (realizedEnforcer L E).netWorth P w (m - 1) +
        ∑ t ∈ Finset.Ico m (n + 1), ((realizedEnforcer L E).strat t).value P w.payout := by
    unfold Trader.netWorth
    rw [hm1, Finset.sum_range_add_sum_Ico _ (by omega)]
  have htailw : ((-(ρ * ∑ t ∈ Finset.Ico m (n + 1), dayGap L sched v' t) : ℚ) : ℝ) ≤
      ∑ t ∈ Finset.Ico m (n + 1), ((realizedEnforcer L E).strat t).value P w.payout := by
    have hq : ∀ t ∈ Finset.Ico m (n + 1),
        ((-(ρ * dayGap L sched v' t) : ℚ) : ℝ) ≤
          ((realizedEnforcer L E).strat t).value P w.payout := by
      intro t ht
      have hbd := Finset.mem_Ico.mp ht
      refine le_trans ?_ (day_value_ge L sched t w)
      exact_mod_cast dayGap_dominated L sched ρ t w v' (hdom' t hbd.1 (by omega))
    calc ((-(ρ * ∑ t ∈ Finset.Ico m (n + 1), dayGap L sched v' t) : ℚ) : ℝ)
        = ∑ t ∈ Finset.Ico m (n + 1), ((-(ρ * dayGap L sched v' t) : ℚ) : ℝ) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          push_cast
          rfl
      _ ≤ _ := Finset.sum_le_sum hq
  -- assemble in ℚ then cast
  have hbound : -(ρ * ∑ t ∈ Finset.Ico m (n + 1), dayGap L sched v' t) ≥ -(ρ * (3 + 3 * ρ)) := by
    rw [htail_eq]
    have h1 : slackMass L sched v' n - slackMass L sched v' (m - 1) ≤ 3 + 3 * ρ := by
      have a : (slackMass L sched v' n : ℚ) < 3 := by exact_mod_cast hSv'
      have b : (slackMass L sched v₀ (m - 1) : ℚ) < 3 := by exact_mod_cast hS₀
      nlinarith
    nlinarith
  have hcast : ((-(ρ * (3 + 3 * ρ)) : ℚ) : ℝ) ≤
      ((-(ρ * ∑ t ∈ Finset.Ico m (n + 1), dayGap L sched v' t) : ℚ) : ℝ) := by
    exact_mod_cast hbound
  rw [hworth]
  have : ((-(ρ * (3 + 3 * ρ)) : ℚ) : ℝ) = -((ρ : ℝ) * (3 + 3 * ρ)) := by push_cast; ring
  rw [this] at hcast
  nlinarith [hpre, hcast, htailw]

end ReopenedBankroll

/-! ## Part A — the fixture under the rule -/

namespace Fixture

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementPreservation
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-- The settlement at date `n`: `X` from `n₁`, and from `nE` the refutation of `Y` with its
closure `X∧A∧Y` false. -/
def settlementAt (n₁ nE n : ℕ) : Settlement 4 :=
  ⟨![if n₁ ≤ n then some true else none, none,
     if nE ≤ n then some false else none, if nE ≤ n then some false else none]⟩

/-- The docket at date `n`: the applicability port `2` defeated from `n₀`. -/
def docketAt (n₀ n : ℕ) : DocketState := ⟨if n₀ ≤ n then {2} else ∅, ∅⟩

/-- **The strength occurrence is rebutted at `nE`**, and before it every form is kept. -/
theorem settleOutcome_strength (c : Strengths) (n₁ nE n : ℕ) :
    settleOutcome (settlementAt n₁ nE n) (occS c).form =
      (if nE ≤ n then Outcome.rebutted else Outcome.kept) := by
  simp [settleOutcome, pinsFalse, settlementAt, occS]

theorem settleOutcome_premise (c : Strengths) (n₁ nE n : ℕ) :
    settleOutcome (settlementAt n₁ nE n) (occP c).form = .kept := by
  simp [settleOutcome, pinsFalse, settlementAt, occP]

theorem settleOutcome_appl (c : Strengths) (n₁ nE n : ℕ) :
    settleOutcome (settlementAt n₁ nE n) (occA c).form = .kept := by
  simp [settleOutcome, pinsFalse, settlementAt, occA]

@[simp] lemma occP_id (c : Strengths) : (occP c).id = 1 := rfl
@[simp] lemma occA_id (c : Strengths) : (occA c).id = 2 := rfl
@[simp] lemma occS_id (c : Strengths) : (occS c).id = 3 := rfl
@[simp] lemma occP_cites (c : Strengths) : (occP c).cites = .none := rfl
@[simp] lemma occA_cites (c : Strengths) : (occA c).cites = .occurrence 1 := rfl
@[simp] lemma occS_cites (c : Strengths) : (occS c).cites = .occurrence 2 := rfl
@[simp] lemma occP_defeaters (c : Strengths) : (occP c).defeaters = ∅ := rfl
@[simp] lemma occA_defeaters (c : Strengths) : (occA c).defeaters = ∅ := rfl
@[simp] lemma occS_defeaters (c : Strengths) : (occS c).defeaters = {2} := rfl

lemma mem_docketAt_iff (n₀ n j : ℕ) : j ∈ (docketAt n₀ n).defeated ↔ n₀ ≤ n ∧ j = 2 := by
  simp only [docketAt]
  split_ifs with h <;> simp [h]

/-- **The survivors, date by date**: the premise always, the applicability before `n₀`, the
strength while the applicability it cites is live and `Y` is not refuted — by the grounded
rule, not by declaration. -/
theorem survivors_eq (c : Strengths) (n₀ n₁ nE n : ℕ) :
    (grounds c).survivors (docketAt n₀ n) (settlementAt n₁ nE n) =
      occP c :: ((if n < n₀ then [occA c] else []) ++
        (if n < n₀ ∧ n < nE then [occS c] else [])) := by
  have hP := settleOutcome_premise c n₁ nE n
  have hA := settleOutcome_appl c n₁ nE n
  have hS := settleOutcome_strength c n₁ nE n
  unfold Grounds.survivors
  rw [activeIds_of_length _ _ _ 3 rfl, iterate_three]
  by_cases h0 : n < n₀ <;> by_cases hE : n < nE <;>
    simp [activeStep, liveGiven, undercut, citesIn, grounds, hP, hA, hS, mem_docketAt_iff,
      h0, hE, show ¬ n₀ ≤ n ↔ n < n₀ from not_le, show ¬ nE ≤ n ↔ n < nE from not_le]

/-- The force rows at date `n` under the rule. -/
def rowsRebutted (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ nE n : ℕ) : List Row :=
  premiseRow c β hβ ::
    ((if n < n₀ then [applRow c β hβ] else []) ++
      (if n < n₀ ∧ n < nE then [strengthRow c β hβ] else []))

/-- The force schedule under the rule. -/
def schedRebutted (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ nE : ℕ) : ℕ → Presentation :=
  fun n => pres (rowsRebutted c β hβ n₀ nE n)

/-- **The force schedule is the survivors through the bridge**: the enforcer holds exactly the
rows `settleForm` keeps. -/
theorem schedRebutted_eq_survivors (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ n₁ nE n : ℕ) :
    (schedRebutted c β hβ n₀ nE n).rows =
      ((grounds c).survivors (docketAt n₀ n) (settlementAt n₁ nE n)).map
        fun o => toForceRow ι β hβ o.form.row := by
  rw [survivors_eq]
  simp only [schedRebutted, pres_rows, rowsRebutted, List.map_cons, List.map_append]
  by_cases h0 : n < n₀ <;> by_cases hE : n < nE <;>
    simp [h0, hE, premiseRow, applRow, strengthRow, occP, occA, occS]

/-- **No strength row after `nE`**, and no row on `X∧A` at all once the applicability port is
defeated — the harmonic buyer has nothing to buy against. -/
theorem no_strength_after (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ nE n : ℕ) (hn : nE ≤ n) :
    strengthRow c β hβ ∉ (schedRebutted c β hβ n₀ nE n).rows ∧
    (n₀ ≤ n → (schedRebutted c β hβ n₀ nE n).rows = [premiseRow c β hβ]) := by
  have hE : ¬ n < nE := not_lt.mpr hn
  constructor
  · simp only [schedRebutted, pres_rows, rowsRebutted, hE, and_false, if_false, List.append_nil,
      List.mem_cons, List.mem_ite_nil_right, List.mem_singleton, List.not_mem_nil, or_false]
    rintro (h | ⟨-, h⟩)
    · have := congrArg Row.rhs h
      simp [strengthRow, premiseRow, toForceRow, Form.row] at this
      linarith [c.P_pos]
    · have := congrArg (fun r : Row => r.coeff XAY) h
      simp [strengthRow, applRow, toForceRow, Form.row, Fin.sum_univ_four] at this
  · intro h0
    simp [schedRebutted, rowsRebutted, hE, not_lt.mpr h0]

/-- **The region after the rebuttal is nonempty**: `(1, c_A, 0, 0)` with every row live but
the strength row, which is gone. -/
theorem rebutted_region_nonempty (c : Strengths) (n₀ n₁ nE n : ℕ) (hn₁ : n₁ ≤ n)
    (hnE : nE ≤ n) :
    (grounds c).settledRegion (docketAt n₀ n) (settlementAt n₁ nE n) ![1, c.A, 0, 0] := by
  rw [Grounds.settledRegion_iff, survivors_eq]
  have hE : ¬ n < nE := not_lt.mpr hnE
  refine ⟨fun i => by fin_cases i <;> simp <;> constructor <;> linarith [c.A_pos, c.A_lt], ?_, ?_⟩
  · intro i b hi
    fin_cases i <;> simp_all [settlementAt, truth, hn₁, hnE]
  · intro o ho
    simp only [hE, and_false, if_false, List.append_nil, List.mem_cons, List.mem_ite_nil_right,
      List.mem_singleton, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | ⟨-, rfl⟩
    · simp only [occP]; rw [Form.premise_sat_iff]; simp; exact c.P_lt.le
    · simp only [occA]; rw [Form.applicability_sat_iff]; simp

/-- Domination at the slack world `X, A` true, `Y` false, on the rows live after the
rebuttal. -/
theorem gap_dominated_wAY (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (r : Row)
    (hr : r = premiseRow c β hβ ∨ r = applRow c β hβ) (w : PCWorld) :
    -(rowGap (pres []).coords r w) ≤ ρ c * rowGap (pres []).coords r wAY := by
  have hρ := ρ_nonneg c
  have hP := P_le c
  have hA := A_le c
  have hX := wAY_X
  have hA' := wAY_A
  rcases hr with rfl | rfl
  · rw [gap_premise, gap_premise, ratPayout_X, ratPayout_X]
    by_cases hwX : w.Holds X <;> simp [hwX, hX] <;> nlinarith [c.P_pos, c.P_lt]
  · rw [gap_appl, gap_appl, ratPayout_XA, ratPayout_X, ratPayout_XA, ratPayout_X]
    by_cases hwX : w.Holds X <;> by_cases hwA : w.Holds A <;>
      simp [hwX, hwA, hX, hA'] <;> nlinarith [c.A_pos, c.A_lt]

lemma mem_rowsRebutted {c : Strengths} {β : ℚ} {hβ : 0 ≤ β} {n₀ nE n : ℕ} {r : Row}
    (h : r ∈ rowsRebutted c β hβ n₀ nE n) :
    r = premiseRow c β hβ ∨ r = applRow c β hβ ∨ (n < nE ∧ r = strengthRow c β hβ) := by
  unfold rowsRebutted at h
  by_cases h0 : n < n₀ <;> by_cases hE : n < nE <;> simp [h0, hE] at h <;> tauto

/-- `wAY` is live once `Y` is refuted (and `X` settled true or not). -/
lemma wAY_live (n₁ nE n : ℕ) : (L n₁ nE false).Live n wAY := by
  rw [live_iff]
  exact ⟨fun _ => wAY_X, fun _ => by simpa [holds_negY] using wAY_notY⟩

/-- **A2, `Fixture.liability_rebutted`.**  Under the rule, with `Y` refuted at `nE` and the
applicability port defeated at `n₀`, the enforcer's assessed net worth is at least
`−3ρ(2 + ρ)` at every live world at every date: `3ρ` before the rebuttal (the all-true world
is the slack world), and across it the reopened bankroll with the slack world `X, A` true,
`Y` false.  The dispatch's "the same `3ρ`" is not what the construction gives; see the
round's `REBUTTAL.md` for the exhibit that it cannot. -/
theorem liability_rebutted (c : Strengths) (β : ℚ) (hβ : 0 ≤ β) (n₀ n₁ nE : ℕ)
    (hnE : 0 < nE) :
    ∀ n (v : PCWorld), (L n₁ nE false).Live n v →
      -(3 * (ρ c : ℝ) * (2 + ρ c)) ≤
        (realizedEnforcer (L n₁ nE false) (warrantEnforcer (schedRebutted c β hβ n₀ nE))).netWorth
          (history (L n₁ nE false) (warrantEnforcer (schedRebutted c β hβ n₀ nE))) v n := by
  intro n v hv
  have hρ := ρ_nonneg c
  have hrows : ∀ t, ∀ r ∈ (schedRebutted c β hβ n₀ nE t).rows,
      r = premiseRow c β hβ ∨ r = applRow c β hβ ∨ (t < nE ∧ r = strengthRow c β hβ) :=
    fun t r hr => mem_rowsRebutted hr
  -- all rows at dates `< nE` are dominated at the all-true world
  have hpre : ∀ (w : PCWorld) t, t < nE → ∀ r ∈ (schedRebutted c β hβ n₀ nE t).rows,
      -(rowGap (schedRebutted c β hβ n₀ nE t).coords r w) ≤
        ρ c * rowGap (schedRebutted c β hβ n₀ nE t).coords r allTrue := by
    intro w t _ r hr
    rcases hrows t r hr with h | h | ⟨-, h⟩
    · exact gap_dominated c β hβ r (Or.inl h) w
    · exact gap_dominated c β hβ r (Or.inr (Or.inl h)) w
    · exact gap_dominated c β hβ r (Or.inr (Or.inr h)) w
  -- rows at dates `≥ nE` are dominated at `wAY`
  have hpost : ∀ (w : PCWorld) t, nE ≤ t → ∀ r ∈ (schedRebutted c β hβ n₀ nE t).rows,
      -(rowGap (schedRebutted c β hβ n₀ nE t).coords r w) ≤
        ρ c * rowGap (schedRebutted c β hβ n₀ nE t).coords r wAY := by
    intro w t ht r hr
    rcases hrows t r hr with h | h | ⟨hlt, -⟩
    · exact gap_dominated_wAY c β hβ r (Or.inl h) w
    · exact gap_dominated_wAY c β hβ r (Or.inr h) w
    · omega
  by_cases hn : n < nE
  · have h3 := netWorth_ge_neg_odds (L n₁ nE false) (schedRebutted c β hβ n₀ nE) (ρ c) hρ n allTrue
      (allTrue_live_before n₁ nE false n hn) v (fun t ht r hr => hpre v t (by omega) r hr)
    have : -(3 * (ρ c : ℝ) * (2 + ρ c)) ≤ -(3 * (ρ c : ℝ)) := by
      have hρr : (0 : ℝ) ≤ ρ c := by exact_mod_cast hρ
      nlinarith
    linarith
  · exact netWorth_ge_neg_odds_reopened (L n₁ nE false) (schedRebutted c β hβ n₀ nE) (ρ c) hρ hnE
      (not_lt.mp hn) allTrue (allTrue_live_before n₁ nE false (nE - 1) (by omega)) wAY
      (wAY_live n₁ nE n) v (fun t ht r hr => hpre v t ht r hr)
      (fun t ht r hr => hpre wAY t ht r hr) (fun t ht _ r hr => hpost v t ht r hr)

end Fixture

/-! ## Part A — A3: the premise guard retired -/

namespace Fixture2

/-- Five coordinates: `X, X∧A, X∧A∧Y, Y, Z`. -/
abbrev X : Fin 5 := 0
abbrev XA : Fin 5 := 1
abbrev XAY : Fin 5 := 2
abbrev Y : Fin 5 := 3
abbrev Z : Fin 5 := 4

/-- The first warrant's three occurrences and the second warrant on `Z`. -/
def occP (cP : ℚ) : Occurrence 5 := ⟨1, Form.premise X cP, .none, .party 1, ∅⟩
def occA (cA : ℚ) : Occurrence 5 := ⟨2, Form.applicability X XA cA, .occurrence 1, .party 1, ∅⟩
def occS (cS : ℚ) : Occurrence 5 := ⟨3, Form.strength XA XAY cS, .occurrence 2, .party 1, {2}⟩
def occZ (cZ : ℚ) : Occurrence 5 := ⟨4, Form.premise Z cZ, .none, .party 2, ∅⟩

def grounds (cP cA cS cZ : ℚ) : Grounds 5 := [occP cP, occA cA, occS cS, occZ cZ]

/-- The settlement refuting `X`, with the closure `X∧A`, `X∧A∧Y` false. -/
def refuteX : Settlement 5 := ⟨![some false, some false, some false, none, none]⟩

/-- **Under the port-only rule, refuting the premise empties the joint region**: the premise
row `P(X) ≥ c_P > 0` meets the pin `P(X) = 0`, and the warrant on `Z` is withheld with it. -/
theorem old_rule_empty (cP cA cS cZ : ℚ) (hP : 0 < cP) :
    ¬ ∃ x, (grounds cP cA cS cZ).region DocketState.quiet refuteX x := by
  rintro ⟨x, hx⟩
  rw [Grounds.region_iff] at hx
  obtain ⟨-, hpin, h⟩ := hx
  have h0 : x X = 0 := by simpa [truth] using hpin X false rfl
  have hp := h (occP cP) (by simp [grounds]) (by simp [DocketState.quiet])
  simp only [occP] at hp
  rw [Form.premise_sat_iff, h0] at hp
  linarith

@[simp] lemma occP_id (cP : ℚ) : (occP cP).id = 1 := rfl
@[simp] lemma occA_id (cA : ℚ) : (occA cA).id = 2 := rfl
@[simp] lemma occS_id (cS : ℚ) : (occS cS).id = 3 := rfl
@[simp] lemma occZ_id (cZ : ℚ) : (occZ cZ).id = 4 := rfl
@[simp] lemma occP_cites (cP : ℚ) : (occP cP).cites = .none := rfl
@[simp] lemma occA_cites (cA : ℚ) : (occA cA).cites = .occurrence 1 := rfl
@[simp] lemma occS_cites (cS : ℚ) : (occS cS).cites = .occurrence 2 := rfl
@[simp] lemma occZ_cites (cZ : ℚ) : (occZ cZ).cites = .none := rfl
@[simp] lemma occP_defeaters (cP : ℚ) : (occP cP).defeaters = ∅ := rfl
@[simp] lemma occA_defeaters (cA : ℚ) : (occA cA).defeaters = ∅ := rfl
@[simp] lemma occS_defeaters (cS : ℚ) : (occS cS).defeaters = {2} := rfl
@[simp] lemma occZ_defeaters (cZ : ℚ) : (occZ cZ).defeaters = ∅ := rfl

/-- The survivors of the refutation: only the warrant on `Z` — the premise retires, and the
applicability and strength that cite into it leave with it. -/
theorem survivors_refuteX (cP cA cS cZ : ℚ) :
    (grounds cP cA cS cZ).survivors DocketState.quiet refuteX = [occZ cZ] := by
  unfold Grounds.survivors
  rw [activeIds_of_length _ _ _ 4 rfl, iterate_four]
  simp [activeStep, liveGiven, undercut, citesIn, grounds, settleOutcome, pinsFalse, occP,
    occA, occS, occZ, refuteX, DocketState.quiet]

/-- **Under the rule, the region is the one the other warrant forces**: nonempty, and `Z`
still bounded below by `c_Z`. -/
theorem retired_region (cP cA cS cZ : ℚ) (hZ0 : 0 ≤ cZ) (hZ1 : cZ ≤ 1) :
    (grounds cP cA cS cZ).settledRegion DocketState.quiet refuteX ![0, 0, 0, 0, cZ] ∧
    ∀ x, (grounds cP cA cS cZ).settledRegion DocketState.quiet refuteX x → cZ ≤ x Z := by
  constructor
  · rw [Grounds.settledRegion_iff, survivors_refuteX]
    refine ⟨fun i => by fin_cases i <;> simp [hZ0, hZ1], ?_, ?_⟩
    · intro i b hi; fin_cases i <;> simp_all [refuteX, truth]
    · intro o ho
      simp only [List.mem_singleton] at ho
      subst ho
      simp only [occZ]; rw [Form.premise_sat_iff]; simp
  · intro x hx
    rw [Grounds.settledRegion_iff, survivors_refuteX] at hx
    have := hx.2.2 (occZ cZ) (by simp)
    simp only [occZ] at this
    exact (Form.premise_sat_iff _ _ _).1 this

end Fixture2

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.seg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Row.sat_seg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.region_convex
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.region_attains_between
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Applicability
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Source
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Occurrence
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Occurrence.toSub
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.seed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.bundle
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.region
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.region_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.mem_bundle_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Outcome
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.pinsFalse
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.pinsFalse_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settleOutcome
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settleForm
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Degenerate
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settleOutcome_eq_kept_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settleForm_eq_some_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settleForm_eq_none_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settleForm_strength
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.strength_contraposes
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.applicability_contraposes
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settleOutcome_rebutted_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.undercut
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.citesIn
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.citesIn_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.citesIn_mono
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.liveGiven
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.liveGiven_mono
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.activeStep
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.activeIds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.survivors
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.mem_activeStep
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.activeStep_mono
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.activeStep_subset
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.iter_chain
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.iter_fixed_of_eq
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.card_iter
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.activeIds_fixed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.mem_activeIds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.mem_survivors
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.survivors_subset
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.survivors_not_defeated
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.survivors_kept
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.activeIds_of_length
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.iterate_two
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.iterate_three
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.iterate_four
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.settledBundle
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.settledRegion
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.regionOn
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Grounds.settledRegion_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.mem_settledBundle_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.region_subset_settledRegion
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.pinsFalse_mono
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.kept_of_le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.activeStep_anti_settlement
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.activeIds_anti_settlement
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.survivors_anti
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.undercut_mono
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.activeStep_anti_docket
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.activeIds_anti_docket
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.survivors_anti_docket
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settledRegion_anti_of_survivors_eq
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.settledRegion_subset_kept
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.reopening_bound
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Admissible
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.VerdictCert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.VerdictCert.RowAdmitted
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.VerdictCert.RowAdmitted.allowed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.VerdictCert.CitesLive
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordState
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Licensed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.licensed_supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.supported_admissible
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.licence_chain
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Supported.valid
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.φ
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.r₁
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.r₂
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.G
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.F
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.stDefeat
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_sat_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.survivors_quiet
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.survivors_defeat
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.region_unchanged
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.region_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.mem_region_port
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.loCert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.hiCert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.loCert_value
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.hiCert_value
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.cert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.loPoint_mem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.hiPoint_mem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_b
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_a
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_ne_cubeUpper
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.premRow_ne_cubeLower
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.settledBundle_quiet
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.settledBundle_defeat
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.cited_quiet
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.supported_quiet
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.stale_not_supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.fresh_supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.admissible_not_supported
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.forcedInterval
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.recordAuth
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.recordNoAuth
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.supported_not_licensed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.Party
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.interface
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.frame
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.selection_not_transparent
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.warrantEnforcer
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.realizedEnforcer_strat
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.rowGap
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.rowUnits
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.rowUnits_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.day_value_eq
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.day_value_ge
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.dayGap
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.slackMass
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.slackMass_le_netWorth
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.enforcer_netWorth_lt_three
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.netWorth_ge_neg_odds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.liability_of_odds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.warrant_normative_inductor
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.netWorth_nonneg_of_inclusive
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.day_value_eq_zero_of_rows_nil
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.netWorth_eq_of_tail_zero
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.ofDeductiveProcess_nested
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.A
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Y
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.negY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.X_ne_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.X_ne_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.X_ne_Y
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XA_ne_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XA_ne_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XA_ne_Y
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XAY_ne_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XAY_ne_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.XAY_ne_Y
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Y_ne_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Y_ne_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Y_ne_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.holds_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.holds_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.holds_negY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.coordList
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.coordList_nodup
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_zero
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_one
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_two
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_three
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.toForceRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.toForceRow_pair
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.toForceRow_gap
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.Strengths
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.premiseRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.applRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.strengthRow
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.rowsAt
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.pres
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.pres_rows
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ι_mem_coords
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.schedLive
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.schedWithheld
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.stage
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.mem_stage
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.stage_mono
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.dp
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.L
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.live_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.allTrue_live
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.allTrue_live_before
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ratPayout_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ratPayout_XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ratPayout_XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.gap_premise
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.gap_appl
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.gap_strength
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.odds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.odds_spec
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.odds_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ρ
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.ρ_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.le_of_odds_le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.P_le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.A_le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.S_le
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.allTrue_holds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.gap_dominated
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.mem_rowsAt
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.liability
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.liability_disagree
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occP
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occS
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.grounds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.settledDisagree
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.settledDisagree_pinned_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.disagree_region_empty
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.docketDefeatA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.orphan_region_nonempty
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.wAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.wAY_X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.wAY_A
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.wAY_notY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.orphan_no_slack
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.MarketRun
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordEntry
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Record
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.positionOf
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.positionOf_eq_position
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.trace
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.decideLicensed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.decideLicensed_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.baseRun
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.defeatRun
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.positionOf_base_eq_zero
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.trace_not_injective
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.trace_not_const
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.runs
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.β'
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.mem_runs₁
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.mem_runs₂
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.mem_runs₃
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.trace_not_injOn
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.trace_not_constant
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.price_not_mediated
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.RecordFixture.docket_mediated
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.settlement
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.subItem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.strItem
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.constitutive
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.seed
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.docket
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.seed_region_inhabited
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.forcedInterval
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.verdictCert
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.recordState
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.licensed_inhabited
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.strengths
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.strengths_odds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.sched_rows_length
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.fixture_liability
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Witness.position_nonzero
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.applOcc
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.pinConsequent
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.empty_le_pinConsequent
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Countermodel.settled_not_anti
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.dayGap_dominated
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.slackMass_eq
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.netWorth_ge_neg_odds_reopened
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.settlementAt
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.docketAt
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.settleOutcome_strength
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.settleOutcome_premise
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.settleOutcome_appl
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occP_id
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occA_id
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occS_id
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occP_cites
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occA_cites
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occS_cites
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occP_defeaters
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occA_defeaters
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.occS_defeaters
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.mem_docketAt_iff
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.survivors_eq
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.rowsRebutted
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.schedRebutted
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.schedRebutted_eq_survivors
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.no_strength_after
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.rebutted_region_nonempty
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.gap_dominated_wAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.mem_rowsRebutted
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.wAY_live
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture.liability_rebutted
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.X
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.XA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.XAY
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.Y
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.Z
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occP
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occA
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occS
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occZ
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.grounds
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.refuteX
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.old_rule_empty
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occP_id
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occA_id
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occS_id
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occZ_id
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occP_cites
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occA_cites
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occS_cites
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occZ_cites
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occP_defeaters
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occA_defeaters
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occS_defeaters
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.occZ_defeaters
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.survivors_refuteX
#print axioms Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2.retired_region

end Workspace.Normativity.Contrib.WarrantEntitlement
