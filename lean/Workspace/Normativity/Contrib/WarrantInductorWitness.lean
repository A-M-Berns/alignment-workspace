/-
# The warrant Normative Inductor, run

Round `projects/normativity/rounds/2026-10-22-normative-inductor-integration/`.

One fixture through the whole construction, the adapter included.  The fragment is the five
sentences `X, X∧A, X∧A∧Y, Y, Z`; the grounds are the first warrant's three forms
(strengths `4/5, 3/4, 2/3`) and a second warrant `P(Z) ≥ 3/4`; the structural rows are the
three coherence relations `X∧A ≤ X`, `X∧A∧Y ≤ X∧A`, `X∧A∧Y ≤ Y`.  `X` settles true at `n₁ = 3`,
the first warrant's applicability is undercut at `n₀ = 5`, `Y` is refuted at `n_E = 8`.  The
deductive process is the warrant round's (`Fixture.dp`), the market is the augmented
deductive market of the compiled schedule at tolerance `1/400`.

* **The state process** `N n`: grounds, docket and settlement of the date, the three coherence
  rows.  Its survivors (`survivors_eq`): the strength occurrence leaves at the undercut with the
  applicability it cites; the premise and the `Z` warrant stay throughout.  Its region
  (`region_iff`) and the checked witnesses (`check`).
* **Computability, discharged.**  The deductive process is a step function of the date
  (`process`); the compiled bundle runs through four phases (`bundle_step`), so the enforcer is
  effective data (`computation`).  The run's theorem has no computability hypothesis.
* **Affordability, discharged.**  The odds are `4`; the all-true world is the slack world before
  the refutation and the world `X, A, Z` true, `Y` false after it; the bankroll across the
  reopening is `−72` (`liability`).
* **Two decision problems.**  At date `4` (the warrant live, `X` settled): act on the warrant's
  conclusion or refrain, scored by `P(X∧A∧Y)` and `P(X∧A) − P(X∧A∧Y)`; the strength row and the
  cube certify the refraining score at most `1/3` (`excludes₁`), the strength and applicability
  rows certify the acting score at least `1/2` (`margins₁`).  At date `9` (after the
  refutation): act on `Z` or refrain, scored by `P(Z)` and `1 − P(Z)`, certified by the `Z` row
  (`excludes₂`, `margins₂`).  The gate puts mass at most `1/25` on refraining at date `4` and
  at most `1/100` at date `9` (`gate_bounds`), it is not constant in the prices
  (`gate_nonconstant`), and after the revision the region no longer excludes refraining
  (`exclusion_lapses`).
* **Entitlement** (`entitlement`): the first warrant's occurrences realize the first exposed
  obligation of the accounted state `state₀`, the `Z` warrant the second; both accounts are live
  (`account_live`).  In `state₁`, where the first obligation is answered, no entitlement traces
  an occurrence to it (`answered_not_entitled`).  The protocol's admission predicate and the
  `Expresses` relation are the trivial ones: the fixture does not exercise them.
* **The theorem** (`inductor`): `warrant_inductor` at the fixture — Logical Induction over the
  deductive process, rowwise conformance at every date (every date is enforced: `enforced`),
  provenance of every enforced row to an entitled survivor, a structural row or a pin, the
  adapter's inadequate-mass bound, and the Progress bound at the declared protocol — `≤ 37/100`
  in numbers (`progress_le`), against the trivial `1`.
* **Scenario A, the undercut** (`undercut_summary`): the applicability and the strength leave;
  the region loses `P(X∧A) ≥ 3/4` and `P(X∧A∧Y) ≥ 1/2` and keeps `P(Z) ≥ 3/4`; the certified
  guidance on the principal matter is lost and nothing replaces it.  The companion scenario —
  the strength rebutted while still active — is `WarrantInductorRebuttal`.
* **The licence at the market** (`bracket`): the supported verdict `P(X∧A∧Y) = 1/2` at date `4`
  brackets the displayed price within `5/3 · 1/400` below and `1/400` above.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.WarrantInductor
import Workspace.Normativity.Contrib.EndToEndWitness

namespace Workspace.Normativity.Contrib.WarrantInductorWitness

open LogicalInduction
open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement
open Workspace.Normativity.Contrib.WarrantEntitlement.Fixture (wAY wAY_X wAY_A wAY_notY
  holds_XA holds_XAY holds_negY ratPayout_X ratPayout_XA ratPayout_XAY live_iff
  allTrue_live_before dp negY)
open Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2 (X XA XAY Y Z)
open Workspace.Normativity.Contrib.WarrantForce
open Workspace.Normativity.Contrib.WarrantInductor
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation
open Workspace.Normativity.Contrib.GatedChoice
open Workspace.Normativity.Contrib.NormativeInductionInterface
open Workspace.Normativity.Contrib.OpenIntegrityEvolution (ObligationState)
open Workspace.Normativity.Contrib.OpenIntegrityEvolution.Witness (state₀ state₁ wAnchor)
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Initial)
open Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness (start finish initial protocol
  first_answered)
open Workspace.Normativity.Contrib.AssessmentProcess (ratPayout allTrue)
open Workspace.Normativity.Contrib.EndToEndWitness.Run (n₁ n₀ nE cP cA cS settlementAt docketAt
  occP occA occS outcome_occP outcome_occA outcome_occS mem_docketAt_iff Zs ι5 coordList5
  coordList5_nodup wAY_Zs allTrue_holds_Zs)
open Finset

/-! ## 1. The fixture -/

lemma n₁_val : n₁ = 3 := rfl
lemma n₀_val : n₀ = 5 := rfl
lemma nE_val : nE = 8 := rfl

/-- The second warrant's strength. -/
def cZ : ℚ := 3/4

/-- The second warrant, `P(Z) ≥ 3/4`. -/
def occZ : Occurrence 5 := Fixture2.occZ cZ

/-- The grounds. -/
def grounds : Grounds 5 := [occP, occA, occS, occZ]

/-- The coherence rows `X∧A ≤ X`, `X∧A∧Y ≤ X∧A`, `X∧A∧Y ≤ Y`. -/
def coh₁ : StrItem 5 := ⟨⟨![-1, 1, 0, 0, 0], 0⟩, .coherence, 10⟩
def coh₂ : StrItem 5 := ⟨⟨![0, -1, 1, 0, 0], 0⟩, .coherence, 11⟩
def coh₃ : StrItem 5 := ⟨⟨![0, 0, 1, -1, 0], 0⟩, .coherence, 12⟩

def structural : List (StrItem 5) := [coh₁, coh₂, coh₃]

/-- **The normative state at date `n`.** -/
def N (n : ℕ) : NormState 5 := ⟨⟨grounds, docketAt n, settlementAt n, {7, 8}⟩, structural⟩

@[simp] lemma N_grounds (n : ℕ) : (N n).grounds = grounds := rfl
@[simp] lemma N_docket (n : ℕ) : (N n).docket = docketAt n := rfl
@[simp] lemma N_settlement (n : ℕ) : (N n).settlement = settlementAt n := rfl
@[simp] lemma N_structural (n : ℕ) : (N n).structural = structural := rfl

@[simp] lemma occZ_id : occZ.id = 4 := rfl
@[simp] lemma occZ_cites : occZ.cites = .none := rfl
@[simp] lemma occZ_defeaters : occZ.defeaters = ∅ := rfl

theorem outcome_occZ (n : ℕ) : settleOutcome (settlementAt n) occZ.form = .kept := by
  simp [settleOutcome, pinsFalse, settlementAt, occZ, Fixture2.occZ]

/-- **The survivors, date by date**: the strength occurrence leaves at the undercut with the
applicability it cites. -/
theorem survivors_eq (n : ℕ) :
    (N n).survivors = occP :: ((if n < n₀ then [occA, occS] else []) ++ [occZ]) := by
  have hP := outcome_occP n; have hA := outcome_occA n; have hS := outcome_occS n
  have hZ := outcome_occZ n
  show grounds.survivors (docketAt n) (settlementAt n) = _
  unfold Grounds.survivors
  rw [activeIds_of_length _ _ _ 4 rfl, iterate_four]
  by_cases h0 : n < n₀
  · have hE : n < nE := by have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl; omega
    simp [activeStep, liveGiven, undercut, citesIn, grounds, hP, hA, hS, hZ, mem_docketAt_iff,
      h0, hE, show ¬ n₀ ≤ n from not_le.mpr h0, show ¬ nE ≤ n from not_le.mpr hE]
  · simp [activeStep, liveGiven, undercut, citesIn, grounds, hP, hA, hS, hZ, mem_docketAt_iff,
      h0, show n₀ ≤ n from not_lt.mp h0]

/-- No structural row is withdrawn. -/
theorem liveStr_eq (n : ℕ) : (N n).seed.liveStr (N n).docket = structural := by
  simp [NormState.seed, Seed.liveStr, docketAt, structural]

/-- The settlement at date `n`, read as pins. -/
theorem pinned_iff (n : ℕ) (x : Fin 5 → ℚ) :
    (settlementAt n).Pinned x ↔ (n₁ ≤ n → x X = 1) ∧ (nE ≤ n → x XAY = 0 ∧ x Y = 0) := by
  unfold Settlement.Pinned settlementAt
  constructor
  · intro h
    refine ⟨fun h₁ => ?_, fun hE => ⟨?_, ?_⟩⟩
    · simpa [truth, h₁] using h X true (by simp [h₁])
    · simpa [truth, hE] using h XAY false (by simp [hE])
    · simpa [truth, hE] using h Y false (by simp [hE])
  · rintro ⟨h₁, hE⟩ i b hi
    fin_cases i <;> simp_all [truth] <;> split_ifs at hi <;> simp_all

/-- **The region at date `n`, read as inequalities.** -/
theorem region_iff (n : ℕ) (x : Fin 5 → ℚ) :
    (N n).region x ↔
      InCube x ∧ (n₁ ≤ n → x X = 1) ∧ (nE ≤ n → x XAY = 0 ∧ x Y = 0) ∧
      cP ≤ x X ∧ (n < n₀ → cA * x X ≤ x XA) ∧ (n < n₀ → cS * x XA ≤ x XAY) ∧ cZ ≤ x Z ∧
      x XA ≤ x X ∧ x XAY ≤ x XA ∧ x XAY ≤ x Y := by
  rw [NormState.region_iff, survivors_eq, liveStr_eq, N_settlement, pinned_iff]
  have hrows : (∀ o ∈ occP :: ((if n < n₀ then [occA, occS] else []) ++ [occZ]),
      o.form.row.Sat x) ↔
      (cP ≤ x X ∧ (n < n₀ → cA * x X ≤ x XA) ∧ (n < n₀ → cS * x XA ≤ x XAY) ∧ cZ ≤ x Z) := by
    by_cases h0 : n < n₀ <;>
      simp [h0, occP, occA, occS, occZ, Fixture2.occP, Fixture2.occA, Fixture2.occS,
        Fixture2.occZ, Form.premise_sat_iff, Form.applicability_sat_iff, Form.strength_sat_iff]
  have hstr : (∀ it ∈ structural, it.row.Sat x) ↔ (x XA ≤ x X ∧ x XAY ≤ x XA ∧ x XAY ≤ x Y) := by
    simp only [structural, coh₁, coh₂, coh₃, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Row.Sat, Fin.sum_univ_five]
    simp [Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y]
  rw [hrows, hstr]
  tauto

/-- The feasibility witness: the all-true point before the refutation, `(1, 1, 0, 0, 1)` after. -/
def wit (n : ℕ) : Fin 5 → ℚ := if n < nE then ![1, 1, 1, 1, 1] else ![1, 1, 0, 0, 1]

theorem wit_mem (n : ℕ) : (N n).region (wit n) := by
  rw [region_iff]
  by_cases hE : n < nE
  · simp [wit, hE, InCube, Fin.forall_fin_succ, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
  · have h0 : ¬ n < n₀ := by have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl; omega
    simp [wit, hE, h0, InCube, Fin.forall_fin_succ, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num

/-- **Every date's witness checks.** -/
theorem check (n : ℕ) : checkCompiled (N n).bundle (wit n) = true :=
  (checkCompiled_iff _ _).2 (wit_mem n)

/-! ## 2. The schedule and its market -/

lemma ι5_inj : Function.Injective ι5 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [ι5] at h ⊢ <;>
    exact absurd h (by simp only [Fixture.X, Fixture.XA, Fixture.XAY, Fixture.Y, Fixture.A, Zs]; decide)

/-- The fragment map of the five coordinates. -/
def F5 : FragmentMap 5 :=
  ⟨ι5, ι5_inj, coordList5, coordList5_nodup, fun j => by fin_cases j <;> simp [ι5, coordList5]⟩

/-- The tolerance: `1/400` at every date. -/
def tol : ℕ → ℚ := fun _ => 1/400

lemma tol_pos (n : ℕ) : 0 < tol n := by norm_num [tol]

/-- The compiler's result at every date: the witness. -/
def res (n : ℕ) : CompileResult (Cite 5) 5 := .compiled (wit n)

/-- **The schedule**: the compiled bundle of every date at tolerance `1/400`. -/
def W : WarrantSchedule 5 := schedule N F5 res tol tol_pos

/-- The deductive process: `X` at `n₁`, `¬Y` at `n_E`. -/
def DP : DeductiveProcess := dp n₁ nE false

/-- **Every date is enforced**: the outcome is never idle or withheld. -/
theorem enforced (n : ℕ) : Enforced (N n) (res n) := enforced_of_check (check n)

theorem bundle_eq (n : ℕ) : W.bundle n = (N n).bundle := enforced n

/-- Two dates in one phase have one state. -/
lemma N_eq_of_phase {n k : ℕ} (h1 : n₁ ≤ n ↔ n₁ ≤ k) (h0 : n₀ ≤ n ↔ n₀ ≤ k)
    (hE : nE ≤ n ↔ nE ≤ k) : N n = N k := by
  simp only [N, docketAt, settlementAt, h1, h0, hE]

/-- **The compiled bundle runs through four phases.** -/
theorem bundle_step (n : ℕ) :
    W.bundle n = stepBundle (N nE).bundle
      [(n₁, (N 0).bundle), (n₀, (N n₁).bundle), (nE, (N n₀).bundle)] n := by
  rw [bundle_eq]
  have h3 : n₁ = 3 := rfl; have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl
  simp only [stepBundle]
  split_ifs with a b c
  · rw [N_eq_of_phase (k := 0)] <;> constructor <;> intro h <;> omega
  · rw [N_eq_of_phase (k := n₁)] <;> constructor <;> intro h <;> omega
  · rw [N_eq_of_phase (k := n₀)] <;> constructor <;> intro h <;> omega
  · rw [N_eq_of_phase (k := nE)] <;> constructor <;> intro h <;> omega

/-- **The enforcer is effective data.** -/
theorem computation : EnforcedCompiler.EffectiveEnforcerComputation W.enforcer :=
  W.computation _ _ bundle_step (Primrec.const _)

/-- The deductive stage, as a step function of the date. -/
theorem stage_eq (n : ℕ) :
    DP.D n = if n < n₁ then ∅ else if n < nE then {Fixture.X} else {Fixture.X, negY} := by
  show Fixture.stage n₁ nE false n = _
  unfold Fixture.stage
  have h3 : n₁ = 3 := rfl; have h8 : nE = 8 := rfl
  by_cases a : n < n₁ <;> by_cases b : n < nE <;>
    simp [a, b, show n₁ ≤ n ↔ ¬ n < n₁ from not_lt.symm,
      show nE ≤ n ↔ ¬ n < nE from not_lt.symm] <;>
    first | omega | (ext φ; simp)

theorem stage_primrec : Primrec fun n => DP.D n := by
  have h : Primrec fun n : ℕ =>
      if n < n₁ then (∅ : Finset Sentence) else if n < nE then {Fixture.X} else {Fixture.X, negY} :=
    Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const _)) (Primrec.const _)
      (Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const _)) (Primrec.const _)
        (Primrec.const _))
  exact h.of_eq fun n => (stage_eq n).symm

/-- **The deductive process is computable.** -/
noncomputable def process : DeductiveProcessComputation DP := by
  have hc : Computable fun n : ℕ => Encodable.encode (DP.D n) :=
    Computable.encode.comp stage_primrec.to_comp
  have hp : Nat.Partrec fun n => Part.some (Encodable.encode (DP.D n)) :=
    Partrec.nat_iff.mp hc.partrec
  refine ⟨(Nat.Partrec.Code.exists_code.mp hp).choose, fun n => ?_⟩
  rw [(Nat.Partrec.Code.exists_code.mp hp).choose_spec]
  exact Part.mem_some _

/-! ## 3. Affordability: the bankroll across the reopening -/

/-- A world's payouts on the fragment. -/
noncomputable def payoutVec (v : PCWorld) : Fin 5 → ℚ := fun j => ratPayout v (ι5 j)

open Classical in
lemma ratPayout_Y (v : PCWorld) : ratPayout v Fixture.Y = if v.Holds Fixture.Y then 1 else 0 := rfl
open Classical in
lemma ratPayout_Zs (v : PCWorld) : ratPayout v Zs = if v.Holds Zs then 1 else 0 := rfl

theorem live_iff' (n : ℕ) (v : PCWorld) :
    v.ConsistentWith (DP.D n) ↔ (n₁ ≤ n → v.Holds Fixture.X) ∧ (nE ≤ n → ¬ v.Holds Fixture.Y) := by
  have := live_iff n₁ nE false n v
  simp only [Bool.false_eq_true, if_false, holds_negY] at this
  exact this

theorem live_mono {t n : ℕ} (h : t ≤ n) {v : PCWorld} (hv : v.ConsistentWith (DP.D n)) :
    v.ConsistentWith (DP.D t) :=
  ofDeductiveProcess_nested DP h v hv

/-- A plausible world is pinned by the date's settlement. -/
theorem live_pinned {n : ℕ} {v : PCWorld} (hv : v.ConsistentWith (DP.D n)) :
    (settlementAt n).Pinned (payoutVec v) := by
  rw [live_iff'] at hv
  obtain ⟨hX, hY⟩ := hv
  rw [pinned_iff]
  refine ⟨fun h₁ => ?_, fun hE => ⟨?_, ?_⟩⟩
  · simp [payoutVec, ι5, ratPayout_X, hX h₁]
  · simp [payoutVec, ι5, ratPayout_XAY, hY hE]
  · simp [payoutVec, ι5, ratPayout_Y, hY hE]

theorem allTrue_live {n : ℕ} (hn : n < nE) : allTrue.ConsistentWith (DP.D n) :=
  allTrue_live_before n₁ nE false n hn

theorem wAY_live (n : ℕ) : wAY.ConsistentWith (DP.D n) := by
  rw [live_iff']
  exact ⟨fun _ => wAY_X, fun _ => wAY_notY⟩

/-- The seed gaps of the raw rows. -/
lemma gap_P (v : PCWorld) : seedGap ι5 occP.form.row v = ratPayout v Fixture.X - cP := by
  simp [seedGap, occP, Fixture2.occP, Form.row, Fin.sum_univ_five, ι5, Fixture2.X, Fixture2.XA,
    Fixture2.XAY, Fixture2.Y, Fixture2.Z]
  ring

lemma gap_A (v : PCWorld) :
    seedGap ι5 occA.form.row v = ratPayout v Fixture.XA - cA * ratPayout v Fixture.X := by
  simp [seedGap, occA, Fixture2.occA, Form.row, Fin.sum_univ_five, ι5, Fixture2.X, Fixture2.XA,
    Fixture2.XAY, Fixture2.Y, Fixture2.Z]
  ring

lemma gap_S (v : PCWorld) :
    seedGap ι5 occS.form.row v = ratPayout v Fixture.XAY - cS * ratPayout v Fixture.XA := by
  simp [seedGap, occS, Fixture2.occS, Form.row, Fin.sum_univ_five, ι5, Fixture2.X, Fixture2.XA,
    Fixture2.XAY, Fixture2.Y, Fixture2.Z]
  ring

lemma gap_Z (v : PCWorld) : seedGap ι5 occZ.form.row v = ratPayout v Zs - cZ := by
  simp [seedGap, occZ, Fixture2.occZ, Form.row, Fin.sum_univ_five, ι5, Fixture2.X, Fixture2.XA,
    Fixture2.XAY, Fixture2.Y, Fixture2.Z]
  ring

/-- Coherence rows have nonnegative gap at every world. -/
lemma gap_coh_nonneg {it : StrItem 5} (hit : it ∈ structural) (v : PCWorld) :
    0 ≤ seedGap ι5 it.row v := by
  simp only [structural, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl <;>
    simp [seedGap, coh₁, coh₂, coh₃, Fin.sum_univ_five, ι5, ratPayout_X, ratPayout_XA,
      ratPayout_XAY, ratPayout_Y] <;>
    by_cases hX : v.Holds Fixture.X <;> by_cases hA : v.Holds Fixture.A <;>
      by_cases hY : v.Holds Fixture.Y <;> simp [hX, hA, hY]

/-- Every raw warrant row is dominated at the odds `4` by the all-true world. -/
theorem dom_allTrue (o : Occurrence 5) (ho : o ∈ grounds) (w : PCWorld) :
    -(seedGap ι5 o.form.row w) ≤ 4 * seedGap ι5 o.form.row allTrue := by
  have hX : allTrue.Holds Fixture.X := trivial
  have hA : allTrue.Holds Fixture.A := trivial
  have hY : allTrue.Holds Fixture.Y := trivial
  have hZ := allTrue_holds_Zs
  simp only [grounds, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · rw [gap_P, gap_P, ratPayout_X, ratPayout_X]
    by_cases h : w.Holds Fixture.X <;> simp [h, hX, cP] <;> norm_num
  · rw [gap_A, gap_A, ratPayout_XA, ratPayout_X, ratPayout_XA, ratPayout_X]
    by_cases h : w.Holds Fixture.X <;> by_cases h' : w.Holds Fixture.A <;>
      simp [h, h', hX, hA, cA] <;> norm_num
  · rw [gap_S, gap_S, ratPayout_XAY, ratPayout_XA, ratPayout_XAY, ratPayout_XA]
    by_cases h : w.Holds Fixture.X <;> by_cases h' : w.Holds Fixture.A <;>
      by_cases h'' : w.Holds Fixture.Y <;> simp [h, h', h'', hX, hA, hY, cS] <;> norm_num
  · rw [gap_Z, gap_Z, ratPayout_Zs, ratPayout_Zs]
    by_cases h : w.Holds Zs <;> simp [h, hZ, cZ] <;> norm_num

/-- The premise and the `Z` warrant are dominated at the odds `4` by the world `X, A, Z` true,
`Y` false. -/
theorem dom_wAY (o : Occurrence 5) (ho : o = occP ∨ o = occZ) (w : PCWorld) :
    -(seedGap ι5 o.form.row w) ≤ 4 * seedGap ι5 o.form.row wAY := by
  have hX := wAY_X; have hZ := wAY_Zs
  rcases ho with rfl | rfl
  · rw [gap_P, gap_P, ratPayout_X, ratPayout_X]
    by_cases h : w.Holds Fixture.X <;> simp [h, hX, cP] <;> norm_num
  · rw [gap_Z, gap_Z, ratPayout_Zs, ratPayout_Zs]
    by_cases h : w.Holds Zs <;> simp [h, hZ, cZ] <;> norm_num

/-- **Domination of the compiled bundle**: at two worlds the date's settlement pins, every
bundle row is dominated once every survivor's raw row is. -/
theorem dom_bundle {t : ℕ} {w v' : PCWorld} (hw : (settlementAt t).Pinned (payoutVec w))
    (hv' : (settlementAt t).Pinned (payoutVec v'))
    (hsub : ∀ o ∈ (N t).survivors, -(seedGap ι5 o.form.row w) ≤ 4 * seedGap ι5 o.form.row v')
    {c : CitedRow (Cite 5) 5} (hc : c ∈ W.bundle t) :
    -(seedGap ι5 c.row w) ≤ 4 * seedGap ι5 c.row v' := by
  rw [bundle_eq] at hc
  rcases ((N t).mem_bundle_iff c).1 hc with ⟨o, ho, rfl⟩ | ⟨it, hit, rfl⟩ | ⟨i, r, hr, rfl⟩
  · simp only [N_settlement]
    rw [seedGap_specialize _ _ _ _ hw, seedGap_specialize _ _ _ _ hv']
    exact hsub o ho
  · simp only [N_settlement]
    rw [seedGap_specialize _ _ _ _ hw, seedGap_specialize _ _ _ _ hv']
    rw [liveStr_eq] at hit
    have h1 := gap_coh_nonneg hit w
    have h2 := gap_coh_nonneg hit v'
    linarith
  · simp only [N_settlement] at hr ⊢
    rw [seedGap_pinRow _ _ hr _ hw, seedGap_pinRow _ _ hr _ hv']
    norm_num

/-- **The bankroll of the run**: `−72 = −3·4·(2 + 4)` at every plausible world at every date. -/
theorem liability : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
    -(72 : ℝ) ≤ (realizedEnforcer DP (W.enforcer.adaptive DP)).netWorth (W.market DP) v n := by
  intro n v hv
  have hρ : (0 : ℚ) ≤ 4 := by norm_num
  have hsubAll : ∀ t, ∀ o ∈ (N t).survivors, ∀ w : PCWorld,
      -(seedGap ι5 o.form.row w) ≤ 4 * seedGap ι5 o.form.row allTrue := fun t o ho w =>
    dom_allTrue o (survivors_subset _ _ _ ho) w
  have hsubPost : ∀ t, nE ≤ t → ∀ o ∈ (N t).survivors, ∀ w : PCWorld,
      -(seedGap ι5 o.form.row w) ≤ 4 * seedGap ι5 o.form.row wAY := by
    intro t ht o ho w
    rw [survivors_eq] at ho
    have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl
    have h0 : ¬ t < n₀ := by omega
    simp only [h0, if_false, List.nil_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at ho
    exact dom_wAY o ho w
  by_cases hn : n < nE
  · have h := (W.account DP).netWorth_ge_neg_odds 4 hρ n allTrue (allTrue_live hn) v
      (fun t ht r hr => W.dom_of_seed DP (fun c hc =>
        dom_bundle (live_pinned (live_mono ht hv)) (live_pinned (allTrue_live (by omega)))
          (fun o ho => hsubAll t o ho v) hc) r hr)
    have : (-(72 : ℝ)) ≤ -((W.account DP).cap * ((4 : ℚ) : ℝ)) := by
      show (-(72 : ℝ)) ≤ -(3 * ((4 : ℚ) : ℝ)); norm_num
    exact this.trans h
  · have hm : 0 < nE := by decide
    have hmn : nE ≤ n := not_lt.mp hn
    have h := W.liability_reopened DP 4 hρ hm hmn allTrue (allTrue_live (by omega)) wAY
      (wAY_live n) v
      (fun t ht c hc => dom_bundle (live_pinned (live_mono (by omega) hv))
        (live_pinned (allTrue_live ht)) (fun o ho => hsubAll t o ho v) hc)
      (fun t ht c hc => dom_bundle (live_pinned (wAY_live t)) (live_pinned (allTrue_live ht))
        (fun o ho => hsubAll t o ho wAY) hc)
      (fun t ht₁ ht₂ c hc => dom_bundle (live_pinned (live_mono ht₂ hv))
        (live_pinned (wAY_live t)) (fun o ho => hsubPost t ht₁ o ho v) hc)
    have : (-(72 : ℝ)) ≤ -(3 * ((4 : ℚ) : ℝ) * (2 + ((4 : ℚ) : ℝ))) := by norm_num
    exact this.trans h

/-! ## 4. Entitlement and well-formedness -/

/-- In the accounted state `state₀` — two obligations exposed on their own ports, nothing yet
answered — every account is live. -/
theorem account_live (e : Fin 2) (h : e ∈ state₀.boundary.exposed) :
    OccurrenceIntegrity.Fate.live ∈ (state₀.account e h).fates := by
  simp [state₀, Initial.state, Initial.accounted, initial, OccurrenceIntegrity.Program.fates]

/-- **The entitlement**: the first warrant's occurrences realize the first exposed obligation,
the `Z` warrant the second; the trivial protocol admits everything and the `Expresses` relation
is total — the two inputs the fixture does not exercise — and both accounts are live. -/
def entitlement (n : ℕ) : Entitlement state₀ (N n).grounds (fun _ _ => True) where
  origin o := if o.id = 4 then 1 else 0
  origin_exposed _ _ := by simp [state₀, Initial.state, start]
  admitted _ _ := trivial
  live _ _ := account_live _ _
  faithful _ _ := trivial

/-- **An answered obligation entitles nothing.**  In `state₁` the first obligation is answered;
no entitlement of these grounds, under any `Expresses` relation, may trace an occurrence to it. -/
theorem answered_not_entitled (Expresses : Unit → Form 5 → Prop)
    (E : Entitlement state₁ grounds Expresses) (o : Occurrence 5) (ho : o ∈ grounds) :
    E.origin o ≠ 0 := by
  intro h
  have hlive := E.live o ho
  have hf : ∀ (e : Fin 2) (he : e ∈ state₁.boundary.exposed), e = 0 →
      (state₁.account e he).fates = {OccurrenceIntegrity.Fate.answered} := by
    rintro e he rfl
    exact first_answered
  rw [hf _ _ h] at hlive
  simp at hlive

theorem wellFormed (n : ℕ) : (N n).grounds.WellFormed := by
  refine ⟨by simp [grounds] <;> decide, ?_⟩
  intro o ho j hj
  simp only [N_grounds, grounds, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · simp at hj
  · simp at hj; subst hj; exact ⟨occP, by simp [grounds], rfl⟩
  · simp at hj; subst hj; exact ⟨occA, by simp [grounds], rfl⟩
  · simp at hj

/-! ## 5. The two decision problems -/

/-- The functionals: `P(X∧A∧Y)`, `P(X∧A) − P(X∧A∧Y)`, `P(Z)`. -/
def eXAY : Fin 5 → ℚ := ![0, 0, 1, 0, 0]
def eXA_XAY : Fin 5 → ℚ := ![0, 1, -1, 0, 0]
def eZ : Fin 5 → ℚ := ![0, 0, 0, 0, 1]

/-- The specialized rows of the two service dates. -/
def rowS4 : Row 5 := specialize (settlementAt 4) occS.form.row
def rowA4 : Row 5 := specialize (settlementAt 4) occA.form.row
def rowZ9 : Row 5 := specialize (settlementAt 9) occZ.form.row

lemma rowS4_a : rowS4.a = ![0, 2/3, -1, 0, 0] := by
  funext j
  fin_cases j <;> simp [rowS4, specialize, settlementAt, occS, Fixture2.occS, Form.row, cS,
    n₁_val, nE_val, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]

lemma rowS4_b : rowS4.b = 0 := by
  simp [rowS4, specialize, settledTerm, settlementAt, occS, Fixture2.occS, Form.row, cS,
    n₁_val, nE_val, Fin.sum_univ_five, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
    Fixture2.Z]

lemma rowA4_a : rowA4.a = ![0, -1, 0, 0, 0] := by
  funext j
  fin_cases j <;> simp [rowA4, specialize, settlementAt, occA, Fixture2.occA, Form.row, cA,
    n₁_val, nE_val, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]

lemma rowA4_b : rowA4.b = -3/4 := by
  norm_num [rowA4, specialize, settledTerm, settlementAt, occA, Fixture2.occA, Form.row, cA,
    n₁_val, nE_val, Fin.sum_univ_five, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
    Fixture2.Z, truth]

lemma rowZ9_a : rowZ9.a = ![0, 0, 0, 0, -1] := by
  funext j
  fin_cases j <;> simp [rowZ9, specialize, settlementAt, occZ, Fixture2.occZ, Form.row, cZ,
    n₁_val, nE_val, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]

lemma rowZ9_b : rowZ9.b = -3/4 := by
  norm_num [rowZ9, specialize, settledTerm, settlementAt, occZ, Fixture2.occZ, Form.row, cZ,
    n₁_val, nE_val, Fin.sum_univ_five, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
    Fixture2.Z, truth] <;> decide

/-- Upper certificate on the refraining score at date `4`: the strength row and the cube face
on `X∧A`, value `1/3`, mass `4/3`. -/
def upS : FunctionalCert 5 2 eXA_XAY where
  mult := ![1, 1/3]
  row := ![rowS4, cubeUpper XA]
  mult_nonneg := fun i => by fin_cases i <;> norm_num
  coeff_sum := fun j => by
    fin_cases j <;> simp [Fin.sum_univ_two, rowS4_a, cubeUpper, eXA_XAY, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num

/-- Lower certificate on the acting score at date `4`: the strength row and the specialized
applicability row, value `−1/2`, mass `5/3`. -/
def loS : FunctionalCert 5 2 (fun j => -(eXAY j)) where
  mult := ![1, 2/3]
  row := ![rowS4, rowA4]
  mult_nonneg := fun i => by fin_cases i <;> norm_num
  coeff_sum := fun j => by
    fin_cases j <;> simp [Fin.sum_univ_two, rowS4_a, rowA4_a, eXAY, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num

/-- The unused certificates of the adequate response (upper) and the inadequate one (lower):
cube faces. -/
def upR1 : FunctionalCert 5 1 eXAY where
  mult := fun _ => 1
  row := fun _ => cubeUpper XAY
  mult_nonneg := fun _ => zero_le_one
  coeff_sum := fun j => by
    fin_cases j <;> simp [cubeUpper, eXAY, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
      Fixture2.Z]

def loR0 : FunctionalCert 5 2 (fun j => -(eXA_XAY j)) where
  mult := ![1, 1]
  row := ![cubeLower XA, cubeUpper XAY]
  mult_nonneg := fun i => by fin_cases i <;> norm_num
  coeff_sum := fun j => by
    fin_cases j <;> simp [Fin.sum_univ_two, cubeLower, cubeUpper, eXA_XAY, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z]

lemma upS_value : upS.value = 1/3 := by
  norm_num [upS, FunctionalCert.value, Fin.sum_univ_two, rowS4_b, cubeUpper]
lemma upS_mass : upS.mass = 4/3 := by
  norm_num [upS, FunctionalCert.mass, Fin.sum_univ_two]
lemma loS_value : loS.value = -1/2 := by
  norm_num [loS, FunctionalCert.value, Fin.sum_univ_two, rowS4_b, rowA4_b]
lemma loS_mass : loS.mass = 5/3 := by
  norm_num [loS, FunctionalCert.mass, Fin.sum_univ_two]

/-- **The principal problem at date `4`**: act on the conclusion (`0`) or refrain (`1`). -/
noncomputable def P₁ : Problem 5 (Fin 2) where
  offset := fun _ => 0
  ℓ := ![eXAY, eXA_XAY]
  A := {0}
  A₁ := {0}
  A₁_sub := Finset.Subset.refl _
  pref := fun _ => 1
  pref_nonneg := fun _ => zero_le_one
  τ := 1/3
  δ := 1/12
  δ_pos := by norm_num
  W := 1
  W_pos := one_pos
  W_le := by simp
  upper := fun q => match q with
    | 0 => ⟨1, upR1, fun _ => Cite.settled XAY⟩
    | 1 => ⟨2, upS, ![Cite.sub 3, Cite.settled XA]⟩
  lower := fun q => match q with
    | 0 => ⟨2, loS, ![Cite.sub 3, Cite.sub 2]⟩
    | 1 => ⟨2, loR0, ![Cite.settled XA, Cite.settled XAY]⟩

/-- The `Z` row's certificates at date `9`. -/
def certZ : FunctionalCert 5 1 (fun j => -(eZ j)) where
  mult := fun _ => 1
  row := fun _ => rowZ9
  mult_nonneg := fun _ => zero_le_one
  coeff_sum := fun j => by
    fin_cases j <;> simp [rowZ9_a, eZ, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
      Fixture2.Z]

def upZ1 : FunctionalCert 5 1 eZ where
  mult := fun _ => 1
  row := fun _ => cubeUpper Z
  mult_nonneg := fun _ => zero_le_one
  coeff_sum := fun j => by
    fin_cases j <;> simp [cubeUpper, eZ, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
      Fixture2.Z]

def loZ0 : FunctionalCert 5 1 (fun j => -(-(eZ j))) where
  mult := fun _ => 1
  row := fun _ => cubeUpper Z
  mult_nonneg := fun _ => zero_le_one
  coeff_sum := fun j => by
    fin_cases j <;> simp [cubeUpper, eZ, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
      Fixture2.Z]

lemma certZ_value : certZ.value = -3/4 := by
  norm_num [certZ, FunctionalCert.value, rowZ9_b]
lemma certZ_mass : certZ.mass = 1 := by
  norm_num [certZ, FunctionalCert.mass]

/-- **The `Z` problem at date `9`**: act on `Z` (`0`) or refrain (`1`). -/
noncomputable def P₂ : Problem 5 (Fin 2) where
  offset := ![0, 1]
  ℓ := ![eZ, fun j => -(eZ j)]
  A := {0}
  A₁ := {0}
  A₁_sub := Finset.Subset.refl _
  pref := fun _ => 1
  pref_nonneg := fun _ => zero_le_one
  τ := 1/4
  δ := 1/4
  δ_pos := by norm_num
  W := 1
  W_pos := one_pos
  W_le := by simp
  upper := fun q => match q with
    | 0 => ⟨1, upZ1, fun _ => Cite.settled Z⟩
    | 1 => ⟨1, certZ, fun _ => Cite.sub 4⟩
  lower := fun q => match q with
    | 0 => ⟨1, certZ, fun _ => Cite.sub 4⟩
    | 1 => ⟨1, loZ0, fun _ => Cite.settled Z⟩

/-- A survivor's specialized row is in the date's bundle. -/
lemma mem_bundle_sub (n : ℕ) (o : Occurrence 5) (ho : o ∈ (N n).survivors) :
    (⟨Cite.sub o.id, specialize (settlementAt n) o.form.row⟩ : CitedRow (Cite 5) 5) ∈ (N n).bundle :=
  ((N n).mem_bundle_iff _).2 (Or.inl ⟨o, ho, rfl⟩)

lemma occS_mem_4 : occS ∈ (N 4).survivors := by rw [survivors_eq]; simp [n₀]
lemma occA_mem_4 : occA ∈ (N 4).survivors := by rw [survivors_eq]; simp [n₀]
lemma occZ_mem_9 : occZ ∈ (N 9).survivors := by rw [survivors_eq]; simp

/-- **Exclusion certified at date `4`**: refraining is priced at most `1/3` on the bundle. -/
theorem excludes₁ : P₁.Excludes (N 4).bundle := by
  intro q hq
  fin_cases q
  · simp [P₁] at hq
  · refine ⟨fun i _ => ?_, ?_⟩
    · fin_cases i
      · exact Or.inl (mem_bundle_sub 4 occS occS_mem_4)
      · exact Or.inr (Or.inl ⟨XA, rfl⟩)
    · show ((P₁.offset 1 + upS.value : ℚ) : ℝ) ≤ P₁.τ
      rw [upS_value]; norm_num [P₁]

/-- **Margin certified at date `4`**: acting is priced at least `1/2 − 5/3 · tol ≥ 5/12`. -/
theorem margins₁ : P₁.Margins (N 4).bundle (tol 4) := by
  intro q hq
  fin_cases q
  · refine ⟨fun i _ => ?_, ?_⟩
    · fin_cases i
      · exact Or.inl (mem_bundle_sub 4 occS occS_mem_4)
      · exact Or.inl (mem_bundle_sub 4 occA occA_mem_4)
    · show P₁.τ + P₁.δ ≤ ((P₁.offset 0 - loS.value - loS.mass * tol 4 : ℚ) : ℝ)
      rw [loS_value, loS_mass]; norm_num [P₁, tol]
  · simp [P₁] at hq

theorem excludes₂ : P₂.Excludes (N 9).bundle := by
  intro q hq
  fin_cases q
  · simp [P₂] at hq
  · refine ⟨fun i _ => Or.inl (mem_bundle_sub 9 occZ occZ_mem_9), ?_⟩
    show ((P₂.offset 1 + certZ.value : ℚ) : ℝ) ≤ P₂.τ
    rw [certZ_value]; norm_num [P₂]

theorem margins₂ : P₂.Margins (N 9).bundle (tol 9) := by
  intro q hq
  fin_cases q
  · refine ⟨fun i _ => Or.inl (mem_bundle_sub 9 occZ occZ_mem_9), ?_⟩
    show P₂.τ + P₂.δ ≤ ((P₂.offset 0 - certZ.value - certZ.mass * tol 9 : ℚ) : ℝ)
    rw [certZ_value, certZ_mass]; norm_num [P₂, tol]
  · simp [P₂] at hq

lemma univ_sdiff_zero : (univ \ ({0} : Finset (Fin 2))) = {1} := by decide

theorem massCap₁ : P₁.massCap = 4/3 := by
  unfold Problem.massCap
  rw [show P₁.A = {0} from rfl, univ_sdiff_zero, Finset.sum_singleton]
  show upS.mass = 4/3
  exact upS_mass

theorem massCap₂ : P₂.massCap = 1 := by
  unfold Problem.massCap
  rw [show P₂.A = {0} from rfl, univ_sdiff_zero, Finset.sum_singleton]
  show certZ.mass = 1
  exact certZ_mass

theorem κ₁ : P₁.κ = 12 := by
  unfold Problem.κ
  rw [show P₁.A = {0} from rfl, univ_sdiff_zero, Finset.sum_singleton]
  norm_num [P₁]

theorem κ₂ : P₂.κ = 4 := by
  unfold Problem.κ
  rw [show P₂.A = {0} from rfl, univ_sdiff_zero, Finset.sum_singleton]
  norm_num [P₂]

/-! ## 6. The adapter protocol -/

/-- **The adapter protocol**: two services at dates `4` and `9`, the first exposed obligation
transported to the first with mass `1/2`, the second to the second with mass `1/4`; losses
`1/10` on the adequate response and `1` on the other; intensities `1`, budgets at the
certificates' masses, amplification `12`. -/
noncomputable def protocol : AdapterProtocol state₀ 5 (Fin 2) where
  services := {4, 9}
  μ := fun _ => 1/2
  μ_prob := by
    show ∑ e ∈ (Finset.univ : Finset (Fin 2)), (1/2 : ℝ) = 1
    simp <;> norm_num
  T := fun e s => if e = 0 ∧ s = 4 then 1/2 else if e = 1 ∧ s = 9 then 1/4 else 0
  T_nonneg := by intros; split_ifs <;> norm_num
  T_row := by
    intro e _
    fin_cases e <;> simp <;> norm_num
  prob := fun s => if s = 4 then P₁ else P₂
  lam := fun _ _ q => if q = 0 then 1/10 else 1
  εad := fun _ => 1/10
  D := 1
  lamS := fun _ => 1
  ρ := fun s => if s = 4 then 1/90000 else 1/160000
  Γ := 12

/-! ## 7. The theorem, run -/

/-- **The warrant Normative Inductor at the fixture.**  No computability hypothesis and no
liability hypothesis remain: both are discharged above. -/
theorem inductor :
    IsLogicalInductor (W.market DP) DP ∧
    (∀ n, Enforced (N n) (res n) →
      ∀ c ∈ (N n).bundle, excess c.row (W.priceVec DP n) ≤ tol n) ∧
    (∀ n, ∀ c ∈ W.bundle n,
      (∃ o ∈ (N n).survivors, c.cites = Cite.sub o.id ∧ (entitlement n).Entitled o ∧
        ∀ j, o.cites = .occurrence j → ∃! o', o' ∈ (N n).survivors ∧ o'.id = j) ∨
      (∃ it ∈ (N n).seed.liveStr (N n).docket, c.cites = Cite.str it.id) ∨
      ∃ i, c.cites = Cite.settled i) ∧
    (∀ s ∈ protocol.services,
      massOff ((protocol.prob s).gate fun j => W.market DP s (F5.ι j)) (protocol.prob s).A ≤
        (protocol.prob s).κ * (protocol.evaluation F5.ι).defect s (W.market DP) ∧
      (protocol.evaluation F5.ι).defect s (W.market DP) ≤
        (((protocol.prob s).massCap * tol s : ℚ) : ℝ)) ∧
    (protocol.evaluation F5.ι).progress (W.market DP) ≤
      (protocol.evaluation F5.ι).modulus + (protocol.evaluation F5.ι).error +
        protocol.D * (protocol.evaluation F5.ι).residual := by
  refine warrant_inductor N F5 res tol tol_pos entitlement wellFormed DP process computation 72
    liability protocol ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s _; exact enforced s
  · intro s hs
    simp only [protocol, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · simpa [protocol] using excludes₁
    · simpa [protocol] using excludes₂
  · intro s hs
    simp only [protocol, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · simpa [protocol] using margins₁
    · simpa [protocol] using margins₂
  · intros; norm_num [protocol]
  · norm_num [protocol]
  · intro r s hs q hq
    simp only [protocol] at hq ⊢
    split_ifs at hq with h <;> simp [P₁, P₂] at hq <;> simp [hq]
  · intro r s q; simp only [protocol]; split_ifs <;> norm_num
  · intros; norm_num [protocol]
  · simp [protocol]
  · intro s hs
    simp only [protocol, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · simp [protocol, massCap₁, tol]; norm_num
    · simp [protocol, massCap₂, tol]; norm_num
  · norm_num [protocol]
  · intro s hs
    simp only [protocol, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · simp [protocol, κ₁, state₀, Initial.state, start, Fin.sum_univ_two]; norm_num
    · simp [protocol, κ₂, state₀, Initial.state, start, Fin.sum_univ_two]; norm_num

/-! ## 8. The run, in numbers -/

/-- The enforcement intensity is positive at every date. -/
theorem intensity_pos (n : ℕ) : 0 < W.realizedκ DP n := W.realizedκ_pos DP n

/-- **The gate at the market**: mass at most `1/25` on refraining at date `4`, at most `1/100`
on refraining at date `9`. -/
theorem gate_bounds :
    massOff (P₁.gate fun j => W.market DP 4 (ι5 j)) {0} ≤ 1/25 ∧
    massOff (P₂.gate fun j => W.market DP 9 (ι5 j)) {0} ≤ 1/100 := by
  obtain ⟨-, -, -, h, -⟩ := inductor
  have h4 := h 4 (by simp [protocol])
  have h9 := h 9 (by simp [protocol])
  have e4 : protocol.prob 4 = P₁ := rfl
  have e9 : protocol.prob 9 = P₂ := rfl
  rw [e4] at h4
  rw [e9] at h9
  constructor
  · calc massOff (P₁.gate fun j => W.market DP 4 (ι5 j)) {0}
        ≤ P₁.κ * (protocol.evaluation F5.ι).defect 4 (W.market DP) := h4.1
      _ ≤ P₁.κ * ((P₁.massCap * tol 4 : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left h4.2 (by rw [κ₁]; norm_num)
      _ = 1/25 := by rw [κ₁, massCap₁]; norm_num [tol]
  · calc massOff (P₂.gate fun j => W.market DP 9 (ι5 j)) {0}
        ≤ P₂.κ * (protocol.evaluation F5.ι).defect 9 (W.market DP) := h9.1
      _ ≤ P₂.κ * ((P₂.massCap * tol 9 : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left h9.2 (by rw [κ₂]; norm_num)
      _ = 1/100 := by rw [κ₂, massCap₂]; norm_num [tol]

/-- **The gate reads the prices**: at a price vector in the date-`4` region it acts with
certainty; at the point `(1, 1, 0, 0, 3/4)` it refrains with certainty. -/
theorem gate_nonconstant :
    P₁.gate (fun j => ((![1, 3/4, 1/2, 1/2, 3/4] : Fin 5 → ℚ) j : ℝ)) 1 = 0 ∧
    P₁.gate (fun j => ((![1, 1, 0, 0, 3/4] : Fin 5 → ℚ) j : ℝ)) 1 = 1 := by
  constructor
  · simp [Problem.gate, Problem.scoreR, softGate, weight, ramp, P₁, eXAY, eXA_XAY,
      Fin.sum_univ_five, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]
    norm_num
  · simp [Problem.gate, Problem.scoreR, softGate, weight, total, ramp, P₁, eXAY, eXA_XAY,
      Fin.sum_univ_five, Fin.sum_univ_two, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
      Fixture2.Z]
    norm_num

/-- **The exclusion lapses after the revision**: at date `4` every region point prices
refraining at most `1/3`; at date `9` the region contains a point pricing it at `1`. -/
theorem exclusion_lapses :
    (∀ x, (N 4).region x → x XA - x XAY ≤ 1/3) ∧
    ((N 9).region ![1, 1, 0, 0, 1] ∧ (![1, 1, 0, 0, 1] : Fin 5 → ℚ) XA - ![1, 1, 0, 0, 1] XAY = 1) := by
  refine ⟨fun x hx => ?_, ?_, by simp⟩
  · rw [region_iff] at hx
    obtain ⟨hc, -, -, -, -, hS, -, -, -, -⟩ := hx
    have := hS (by decide)
    have := (hc XA).2
    unfold cS at *
    linarith
  · rw [region_iff]
    simp [InCube, Fin.forall_fin_succ, cP, cA, cS, cZ, n₁, n₀, nE, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z]
    norm_num

/-! ## 8′. Scenario A, summarized: what the undercut loses and what survives -/

/-- **The undercut at date `n₀`.**  The applicability and the strength leave the survivors; the
premise and the `Z` warrant stay.  The region loses the lower bounds `P(X∧A) ≥ 3/4` and
`P(X∧A∧Y) ≥ 1/2` it carried at date `4` — at date `5` it admits the point pricing both at `0` —
and keeps `P(Z) ≥ 3/4` at every date.  With `exclusion_lapses`: the certified guidance on the
principal matter is lost, nothing replaces it, and the independent warrant's guidance is
untouched. -/
theorem undercut_summary :
    (N 4).survivors = [occP, occA, occS, occZ] ∧ (N 5).survivors = [occP, occZ] ∧
    (∀ x, (N 4).region x → 3/4 ≤ x XA ∧ 1/2 ≤ x XAY) ∧
    (N 5).region ![1, 0, 0, 0, 3/4] ∧
    (∀ n x, (N n).region x → 3/4 ≤ x Z) := by
  have h3 : n₁ = 3 := rfl; have h5 : n₀ = 5 := rfl
  refine ⟨by rw [survivors_eq]; simp [h5], by rw [survivors_eq]; simp [h5], fun x hx => ?_, ?_,
    fun n x hx => ?_⟩
  · rw [region_iff] at hx
    obtain ⟨-, h1, -, -, hA, hS, -, -, -, -⟩ := hx
    have h1' := h1 (by omega)
    have hA' := hA (by omega)
    have hS' := hS (by omega)
    rw [h1'] at hA'
    unfold cA at hA'; unfold cS at hS'
    constructor <;> linarith
  · rw [region_iff]
    simp [InCube, Fin.forall_fin_succ, cP, cA, cS, cZ, n₁, n₀, nE, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z]
    norm_num
  · rw [region_iff] at hx
    exact hx.2.2.2.2.2.2.1

/-! ## 8″. The Progress bound, in numbers -/

/-- At the fixture the three terms are `Γ √(Σρ/Σλ) ≤ 12/339`, `Σ T ε = 3/40` and
`D · residual = 1/4`, so `progress ≤ 37/100` against the trivial bound `D = 1`.  The adequate
response costs `1/10` and the gate realizes it with mass at least `24/25` at date `4` and
`99/100` at date `9` (`gate_bounds`); the unserved quarter of the evaluation mass is the
largest term. -/
theorem progress_le : (protocol.evaluation F5.ι).progress (W.market DP) ≤ 37/100 := by
  obtain ⟨-, -, -, -, h⟩ := inductor
  have hρ : ∑ s ∈ protocol.services, protocol.ρ s = 1/90000 + 1/160000 := by
    simp [protocol]
  have hl : ∑ s ∈ protocol.services, protocol.lamS s = 2 := by
    norm_num [protocol]
  have hmod : (protocol.evaluation F5.ι).modulus ≤ 12/339 := by
    show protocol.Γ * Real.sqrt ((∑ s ∈ protocol.services, protocol.ρ s) /
      ∑ s ∈ protocol.services, protocol.lamS s) ≤ 12/339
    rw [hρ, hl]
    have hs : Real.sqrt ((1/90000 + 1/160000) / 2) ≤ 1/339 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hΓ : protocol.Γ = 12 := rfl
    rw [hΓ]; linarith
  have herr : (protocol.evaluation F5.ι).error = 3/40 := by
    simp [Evaluation.error, AdapterProtocol.evaluation, protocol, state₀, Initial.state, start,
      Fin.sum_univ_two]
    norm_num
  have hres : (protocol.evaluation F5.ι).residual = 1/4 := by
    simp [Evaluation.residual, AdapterProtocol.evaluation, protocol, state₀, Initial.state, start,
      Fin.sum_univ_two]
    norm_num
  have hD : protocol.D = 1 := rfl
  rw [herr, hres, hD] at h
  linarith

/-! ## 9. The licence at the market -/

/-- The verdict certificate `P(X∧A∧Y) = 1/2` at date `4`: the lower rows of `loS`, the cube
face above. -/
def loCert4 : BoundCert 5 2 XAY (-1) where
  mult := ![1, 2/3]
  row := ![rowS4, rowA4]
  mult_nonneg := fun i => by fin_cases i <;> norm_num
  coeff_sum := fun j => by
    fin_cases j <;> simp [Fin.sum_univ_two, rowS4_a, rowA4_a, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num

def hiCert4 : BoundCert 5 1 XAY 1 where
  mult := fun _ => 1
  row := fun _ => cubeUpper XAY
  mult_nonneg := fun _ => zero_le_one
  coeff_sum := fun j => by simp [cubeUpper]

def cert4 : VerdictCert 5 2 1 XAY where
  lo := loCert4
  hi := hiCert4
  loCite := ![Cite.sub 3, Cite.sub 2]
  hiCite := fun _ => Cite.settled XAY
  loPoint := ![1, 3/4, 1/2, 1/2, 3/4]
  hiPoint := ![1, 1, 1, 1, 1]

lemma loCert4_value : loCert4.value = -1/2 := by
  simp [BoundCert.value, loCert4, Fin.sum_univ_two, rowS4_b, rowA4_b]; norm_num

lemma loCert4_mass : loCert4.mass = 5/3 := by
  simp [BoundCert.mass, loCert4, Fin.sum_univ_two]; norm_num

/-- **The verdict is supported on the canonical bundle at date `4`.** -/
theorem supported4 : (N 4).Supported XAY (1/2) cert4 := by
  refine ⟨⟨fun i _ => ?_, fun _ _ => Or.inr (Or.inl ⟨XAY, rfl⟩)⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · fin_cases i
    · exact Or.inl (mem_bundle_sub 4 occS occS_mem_4)
    · exact Or.inl (mem_bundle_sub 4 occA occA_mem_4)
  · rw [show cert4.lo = loCert4 from rfl, loCert4_value]; norm_num
  · simp [cert4, hiCert4, BoundCert.value, cubeUpper] <;> norm_num
  · show (N 4).region _
    rw [region_iff]
    simp [cert4, InCube, Fin.forall_fin_succ, cP, cA, cS, cZ, n₁, n₀, nE, Fixture2.X,
      Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]
    norm_num
  · rw [show cert4.lo = loCert4 from rfl, loCert4_value]; simp [cert4]; norm_num
  · show (N 4).region _
    rw [region_iff]
    simp [cert4, InCube, Fin.forall_fin_succ, cP, cA, cS, cZ, n₁, n₀, nE, Fixture2.X,
      Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]
    norm_num
  · simp [cert4, hiCert4, BoundCert.value, cubeUpper]

/-- **The licensed bracket holds at the market**: the displayed price of `X∧A∧Y` at date `4`
lies in `[1/2 − 5/3 · 1/400, 1 + 1/400]`. -/
theorem bracket :
    (1/2 : ℚ) - 5/3 * (1/400) ≤ W.priceVec DP 4 XAY ∧ W.priceVec DP 4 XAY ≤ 1 + 1/400 := by
  have hB : W.bundle 4 = (N 4).bundle := bundle_eq 4
  have hsupp : SupportedOn (W.bundle 4) XAY (1/2) cert4 := by rw [hB]; exact supported4
  have h := W.bracket_at_market DP 4 (wit 4) (by rw [hB]; exact wit_mem 4) hsupp
  have ht : W.tol 4 = 1/400 := rfl
  have hlo : cert4.lo = loCert4 := rfl
  have hhiv : cert4.hi.value = 1 := by simp [cert4, hiCert4, BoundCert.value, cubeUpper]
  have hhim : cert4.hi.mass = 1 := by simp [cert4, hiCert4, BoundCert.mass]
  rw [ht, hlo, loCert4_value, loCert4_mass, hhiv, hhim] at h
  constructor
  · have := h.1; linarith
  · have := h.2; linarith

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.n₁_val
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.n₀_val
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.nE_val
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.cZ
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.occZ
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.grounds
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.coh₁
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.coh₂
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.coh₃
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.structural
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.N
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.N_grounds
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.N_docket
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.N_settlement
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.N_structural
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.occZ_id
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.occZ_cites
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.occZ_defeaters
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.outcome_occZ
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.survivors_eq
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.liveStr_eq
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.pinned_iff
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.region_iff
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.wit
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.wit_mem
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.check
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.ι5_inj
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.F5
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.tol
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.tol_pos
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.W
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.DP
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.bundle_eq
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.N_eq_of_phase
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.bundle_step
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.computation
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.stage_eq
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.stage_primrec
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.process
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.payoutVec
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.ratPayout_Y
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.ratPayout_Zs
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.live_iff'
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.live_mono
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.live_pinned
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.allTrue_live
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.wAY_live
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.gap_P
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.gap_A
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.gap_S
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.gap_Z
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.gap_coh_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.dom_allTrue
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.dom_wAY
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.dom_bundle
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.liability
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.res
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.enforced
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.account_live
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.entitlement
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.answered_not_entitled
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.undercut_summary
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.progress_le
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.wellFormed
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.eXAY
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.eXA_XAY
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.eZ
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.rowS4
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.rowA4
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.rowZ9
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.rowS4_a
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.rowS4_b
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.rowA4_a
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.rowA4_b
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.rowZ9_a
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.rowZ9_b
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.upS
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.loS
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.upR1
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.loR0
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.upS_value
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.upS_mass
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.loS_value
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.loS_mass
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.P₁
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.certZ
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.upZ1
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.loZ0
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.certZ_value
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.certZ_mass
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.P₂
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.mem_bundle_sub
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.occS_mem_4
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.occA_mem_4
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.occZ_mem_9
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.excludes₁
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.margins₁
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.excludes₂
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.margins₂
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.univ_sdiff_zero
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.massCap₁
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.massCap₂
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.κ₁
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.κ₂
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.protocol
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.inductor
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.intensity_pos
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.gate_bounds
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.gate_nonconstant
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.exclusion_lapses
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.loCert4
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.hiCert4
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.cert4
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.loCert4_value
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.loCert4_mass
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.supported4
#print axioms Workspace.Normativity.Contrib.WarrantInductorWitness.bracket

end Workspace.Normativity.Contrib.WarrantInductorWitness