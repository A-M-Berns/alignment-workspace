/-
# Scenario B — the strength rebutted while active

Round `projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/`.

The companion to `WarrantInductorWitness` (Scenario A, the undercut).  Same five sentences,
same grounds, same settlement — `X` true at `n₁ = 3`, `Y` and `X∧A∧Y` refuted at `n_E = 8` —
same coherence rows, tolerance and deductive process; the docket is quiet throughout, so the
applicability is never undercut and the strength `P(X∧A∧Y) ≥ 2/3 · P(X∧A)` is **active until
its consequent is refuted**, and leaves by rebuttal.

1. **Operative before**: the strength survives and its row is enforced at every date before
   `n_E` (`operative_before`).
2. **The consequent settles false while the antecedent can remain true**: at `n_E` the
   settlement pins `Y` and `X∧A∧Y` false and leaves `X∧A` open; the region at date `9`
   contains a point with `P(X∧A) = 1` and forces `P(X∧A) ≥ 3/4` (`antecedent_open`).
3. **Withdrawn by rebuttal**: from `n_E` the strength's outcome is `rebutted` and it is not a
   survivor (`withdrawn`).
4. **Contraposition blocked**: had the specialized strength row stayed, the system would have
   been infeasible — `2/3 · P(X∧A) ≤ 0` against `P(X∧A) ≥ 3/4` (`contraposition_blocked`).
   Withdrawal is what leaves the antecedent's credence where the applicability puts it.
5. **Feasible and enforced**: every date is enforced and every enforced row conforms within
   `1/400` at the displayed price (`enforced`, `inductor`).
6. **Liability survives**: the bankroll across the reopening is `−72` with the same two slack
   worlds as Scenario A — the all-true world before `n_E`, the world `X, A, Z` true and `Y`
   false after it — the applicability row now among the rows the second world must dominate
   (`liability`).

**The same decision question, before and after.**  The problem `P₁` — act on the warrant's
conclusion or refrain, scored by `P(X∧A∧Y)` and `P(X∧A) − P(X∧A∧Y)`, adequate set *act* — is
posed at date `4` and again at date `9`.  Four things are kept apart.

* *The constraints change*: the strength row leaves (`withdrawn`).
* *The region changes*: at date `4` every admissible price vector prices refraining at most
  `1/3`; at date `9` every one prices it at least `3/4` (`region_flips`).
* *The guarantees change*: the date-4 certificates have no counterpart at date `9` — no
  `Excludes` and no `Margins` certificate for `P₁` exists on the date-9 bundle
  (`no_certificate_after`) — so the adapter theorem cannot be applied to this question there.
* *The adapter's behavior changes*: at the realized market the gate acts with mass at least
  `24/25` at date `4` and refrains with certainty at date `9` (`same_question`).  The reversal
  follows the pinned price of the refuted conclusion, not a revised adequacy judgment: the
  declared adequate set is unchanged, and whether refraining is *adequate* after the refutation
  is not a question the mathematics answers.

**Accounting.**  The protocol declares both services; the theorem runs on its restriction to
date `4`, and the dropped service's transport mass `1/4` reappears in the residual
(`residual_restricted`, by `AdapterProtocol.residual_restrict`), charged at `D`.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.WarrantInductorWitness

namespace Workspace.Normativity.Contrib.WarrantInductorRebuttal

open LogicalInduction
open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement
open Workspace.Normativity.Contrib.WarrantEntitlement.Fixture (wAY wAY_X wAY_A ratPayout_X
  ratPayout_XA)
open Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2 (X XA XAY Y Z)
open Workspace.Normativity.Contrib.WarrantForce
open Workspace.Normativity.Contrib.WarrantInductor
open Workspace.Normativity.Contrib.WarrantInductorWitness (cZ occZ grounds coh₁ coh₂ coh₃ structural
  N outcome_occZ pinned_iff wit F5 tol tol_pos DP process payoutVec live_mono live_pinned
  allTrue_live wAY_live gap_A gap_coh_nonneg dom_allTrue dom_wAY entitlement wellFormed eXAY
  eXA_XAY P₁ excludes₁ margins₁ massCap₁ κ₁ univ_sdiff_zero)
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation
open Workspace.Normativity.Contrib.GatedChoice
open Workspace.Normativity.Contrib.NormativeInductionInterface
open Workspace.Normativity.Contrib.OpenIntegrityEvolution.Witness (state₀)
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Initial)
open Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness (start)
open Workspace.Normativity.Contrib.AssessmentProcess (allTrue)
open Workspace.Normativity.Contrib.EndToEndWitness.Run (n₁ n₀ nE cP cA cS settlementAt docketAt
  occP occA occS outcome_occP outcome_occA outcome_occS ι5)
open Finset

/-! ## 1. The state process: a quiet docket -/

/-- The quiet docket at every date: no port is ever defeated. -/
def docketB (_ : ℕ) : DocketState := DocketState.quiet

/-- **The normative state at date `n`.** -/
def NB (n : ℕ) : NormState 5 := ⟨⟨grounds, docketB n, settlementAt n, {7, 8}⟩, structural⟩

@[simp] lemma NB_grounds (n : ℕ) : (NB n).grounds = grounds := rfl
@[simp] lemma NB_docket (n : ℕ) : (NB n).docket = docketB n := rfl
@[simp] lemma NB_settlement (n : ℕ) : (NB n).settlement = settlementAt n := rfl
@[simp] lemma NB_structural (n : ℕ) : (NB n).structural = structural := rfl

/-- Before Scenario A's undercut the two scenarios have one state. -/
theorem NB_eq_N (n : ℕ) (hn : n < n₀) : NB n = N n := by
  simp [NB, N, docketB, DocketState.quiet, docketAt, show ¬ n₀ ≤ n from not_le.mpr hn]

/-- **The survivors**: the strength leaves at the refutation, by rebuttal; the premise, the
applicability and the `Z` warrant stay throughout. -/
theorem survivors_eq (n : ℕ) :
    (NB n).survivors = occP :: occA :: ((if n < nE then [occS] else []) ++ [occZ]) := by
  have hP := outcome_occP n; have hA := outcome_occA n; have hS := outcome_occS n
  have hZ := outcome_occZ n
  show grounds.survivors (docketB n) (settlementAt n) = _
  unfold Grounds.survivors
  rw [activeIds_of_length _ _ _ 4 rfl, iterate_four]
  by_cases hE : n < nE
  · simp [activeStep, liveGiven, undercut, citesIn, grounds, docketB, DocketState.quiet, hP, hA,
      hS, hZ, hE, show ¬ nE ≤ n from not_le.mpr hE]
  · simp [activeStep, liveGiven, undercut, citesIn, grounds, docketB, DocketState.quiet, hP, hA,
      hS, hZ, hE, show nE ≤ n from not_lt.mp hE]

theorem liveStr_eq (n : ℕ) : (NB n).seed.liveStr (NB n).docket = structural := by
  simp [NormState.seed, Seed.liveStr, docketB, DocketState.quiet, structural]

/-- **The region at date `n`**: the applicability row at every date, the strength row before
`n_E`. -/
theorem region_iff (n : ℕ) (x : Fin 5 → ℚ) :
    (NB n).region x ↔
      InCube x ∧ (n₁ ≤ n → x X = 1) ∧ (nE ≤ n → x XAY = 0 ∧ x Y = 0) ∧
      cP ≤ x X ∧ cA * x X ≤ x XA ∧ (n < nE → cS * x XA ≤ x XAY) ∧ cZ ≤ x Z ∧
      x XA ≤ x X ∧ x XAY ≤ x XA ∧ x XAY ≤ x Y := by
  rw [NormState.region_iff, survivors_eq, liveStr_eq, NB_settlement, pinned_iff]
  have hrows : (∀ o ∈ occP :: occA :: ((if n < nE then [occS] else []) ++ [occZ]),
      o.form.row.Sat x) ↔
      (cP ≤ x X ∧ cA * x X ≤ x XA ∧ (n < nE → cS * x XA ≤ x XAY) ∧ cZ ≤ x Z) := by
    by_cases hE : n < nE <;>
      simp [hE, occP, occA, occS, occZ, Fixture2.occP, Fixture2.occA, Fixture2.occS,
        Fixture2.occZ, Form.premise_sat_iff, Form.applicability_sat_iff, Form.strength_sat_iff]
  have hstr : (∀ it ∈ structural, it.row.Sat x) ↔ (x XA ≤ x X ∧ x XAY ≤ x XA ∧ x XAY ≤ x Y) := by
    simp only [structural, coh₁, coh₂, coh₃, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Row.Sat, Fin.sum_univ_five]
    simp [Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y]
  rw [hrows, hstr]
  tauto

/-- Scenario A's witnesses are in the region here too. -/
theorem wit_mem (n : ℕ) : (NB n).region (wit n) := by
  rw [region_iff]
  by_cases hE : n < nE
  · simp [wit, hE, InCube, Fin.forall_fin_succ, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
  · simp [wit, hE, InCube, Fin.forall_fin_succ, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num

theorem check (n : ℕ) : checkCompiled (NB n).bundle (wit n) = true :=
  (checkCompiled_iff _ _).2 (wit_mem n)

/-! ## 2. The schedule, its market, computability -/

/-- The compiler's result at every date: the witness. -/
def res (n : ℕ) : CompileResult (Cite 5) 5 := .compiled (wit n)

/-- **The schedule.** -/
def WB : WarrantSchedule 5 := schedule NB F5 res tol tol_pos

/-- **(5) Every date is enforced.** -/
theorem enforced (n : ℕ) : Enforced (NB n) (res n) := enforced_of_check (check n)

theorem bundle_eq (n : ℕ) : WB.bundle n = (NB n).bundle := enforced n

lemma NB_eq_of_phase {n k : ℕ} (h1 : n₁ ≤ n ↔ n₁ ≤ k) (hE : nE ≤ n ↔ nE ≤ k) : NB n = NB k := by
  simp only [NB, docketB, settlementAt, h1, hE]

/-- The compiled bundle runs through three phases. -/
theorem bundle_step (n : ℕ) :
    WB.bundle n = stepBundle (NB nE).bundle [(n₁, (NB 0).bundle), (nE, (NB n₁).bundle)] n := by
  rw [bundle_eq]
  have h3 : n₁ = 3 := rfl; have h8 : nE = 8 := rfl
  simp only [stepBundle]
  split_ifs with a b
  · rw [NB_eq_of_phase (k := 0)] <;> constructor <;> intro h <;> omega
  · rw [NB_eq_of_phase (k := n₁)] <;> constructor <;> intro h <;> omega
  · rw [NB_eq_of_phase (k := nE)] <;> constructor <;> intro h <;> omega

theorem computation : EnforcedCompiler.EffectiveEnforcerComputation WB.enforcer :=
  WB.computation _ _ bundle_step (Primrec.const _)

/-! ## 3. Affordability across the reopening -/

/-- The premise, the applicability and the `Z` warrant are dominated at the odds `4` by the
world `X, A, Z` true, `Y` false. -/
theorem dom_wAY' (o : Occurrence 5) (ho : o = occP ∨ o = occA ∨ o = occZ) (w : PCWorld) :
    -(seedGap ι5 o.form.row w) ≤ 4 * seedGap ι5 o.form.row wAY := by
  rcases ho with rfl | rfl | rfl
  · exact dom_wAY occP (Or.inl rfl) w
  · have hX := wAY_X; have hA := wAY_A
    rw [gap_A, gap_A, ratPayout_XA, ratPayout_X, ratPayout_XA, ratPayout_X]
    by_cases h : w.Holds Fixture.X <;> by_cases h' : w.Holds Fixture.A <;>
      simp [h, h', hX, hA, cA] <;> norm_num
  · exact dom_wAY occZ (Or.inr rfl) w

theorem dom_bundle {t : ℕ} {w v' : PCWorld} (hw : (settlementAt t).Pinned (payoutVec w))
    (hv' : (settlementAt t).Pinned (payoutVec v'))
    (hsub : ∀ o ∈ (NB t).survivors, -(seedGap ι5 o.form.row w) ≤ 4 * seedGap ι5 o.form.row v')
    {c : CitedRow (Cite 5) 5} (hc : c ∈ WB.bundle t) :
    -(seedGap ι5 c.row w) ≤ 4 * seedGap ι5 c.row v' := by
  rw [bundle_eq] at hc
  rcases ((NB t).mem_bundle_iff c).1 hc with ⟨o, ho, rfl⟩ | ⟨it, hit, rfl⟩ | ⟨i, r, hr, rfl⟩
  · simp only [NB_settlement]
    rw [seedGap_specialize _ _ _ _ hw, seedGap_specialize _ _ _ _ hv']
    exact hsub o ho
  · simp only [NB_settlement]
    rw [seedGap_specialize _ _ _ _ hw, seedGap_specialize _ _ _ _ hv']
    rw [liveStr_eq] at hit
    have h1 := gap_coh_nonneg hit w
    have h2 := gap_coh_nonneg hit v'
    linarith
  · simp only [NB_settlement] at hr ⊢
    rw [seedGap_pinRow _ _ hr _ hw, seedGap_pinRow _ _ hr _ hv']
    norm_num

/-- **(6) The bankroll of the run**: `−72` at every plausible world at every date, the all-true
world slack before the refutation and the world `X, A, Z` true, `Y` false after it. -/
theorem liability : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
    -(72 : ℝ) ≤ (realizedEnforcer DP (WB.enforcer.adaptive DP)).netWorth (WB.market DP) v n := by
  intro n v hv
  have hρ : (0 : ℚ) ≤ 4 := by norm_num
  have hsubAll : ∀ t, ∀ o ∈ (NB t).survivors, ∀ w : PCWorld,
      -(seedGap ι5 o.form.row w) ≤ 4 * seedGap ι5 o.form.row allTrue := fun t o ho w =>
    dom_allTrue o (survivors_subset _ _ _ ho) w
  have hsubPost : ∀ t, nE ≤ t → ∀ o ∈ (NB t).survivors, ∀ w : PCWorld,
      -(seedGap ι5 o.form.row w) ≤ 4 * seedGap ι5 o.form.row wAY := by
    intro t ht o ho w
    rw [survivors_eq] at ho
    have hE : ¬ t < nE := by omega
    simp only [hE, if_false, List.nil_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at ho
    exact dom_wAY' o ho w
  by_cases hn : n < nE
  · have h := (WB.account DP).netWorth_ge_neg_odds 4 hρ n allTrue (allTrue_live hn) v
      (fun t ht r hr => WB.dom_of_seed DP (fun c hc =>
        dom_bundle (live_pinned (live_mono ht hv)) (live_pinned (allTrue_live (by omega)))
          (fun o ho => hsubAll t o ho v) hc) r hr)
    have : (-(72 : ℝ)) ≤ -((WB.account DP).cap * ((4 : ℚ) : ℝ)) := by
      show (-(72 : ℝ)) ≤ -(3 * ((4 : ℚ) : ℝ)); norm_num
    exact this.trans h
  · have hm : 0 < nE := by decide
    have hmn : nE ≤ n := not_lt.mp hn
    have h := WB.liability_reopened DP 4 hρ hm hmn allTrue (allTrue_live (by omega)) wAY
      (wAY_live n) v
      (fun t ht c hc => dom_bundle (live_pinned (live_mono (by omega) hv))
        (live_pinned (allTrue_live ht)) (fun o ho => hsubAll t o ho v) hc)
      (fun t ht c hc => dom_bundle (live_pinned (wAY_live t)) (live_pinned (allTrue_live ht))
        (fun o ho => hsubAll t o ho wAY) hc)
      (fun t ht₁ ht₂ c hc => dom_bundle (live_pinned (live_mono ht₂ hv))
        (live_pinned (wAY_live t)) (fun o ho => hsubPost t ht₁ o ho v) hc)
    have : (-(72 : ℝ)) ≤ -(3 * ((4 : ℚ) : ℝ) * (2 + ((4 : ℚ) : ℝ))) := by norm_num
    exact this.trans h

/-! ## 4. Entitlement, well-formedness, the protocol -/

/-- The grounds are Scenario A's, so the entitlement and the well-formedness are too. -/
def entitlementB (n : ℕ) : Entitlement state₀ (NB n).grounds (fun _ _ => True) := entitlement n

theorem wellFormedB (n : ℕ) : (NB n).grounds.WellFormed := wellFormed n

theorem excludesB₁ : P₁.Excludes (NB 4).bundle := by
  rw [NB_eq_N 4 (by have : n₀ = 5 := rfl; omega)]; exact excludes₁

theorem marginsB₁ : P₁.Margins (NB 4).bundle (tol 4) := by
  rw [NB_eq_N 4 (by have : n₀ = 5 := rfl; omega)]; exact margins₁

/-- **The protocol**: the same question `P₁` at dates `4` and `9`, the first obligation
transported to date `4` with mass `1/2`, the second to date `9` with mass `1/4`. -/
noncomputable def protocolB : AdapterProtocol state₀ 5 (Fin 2) where
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
  prob := fun _ => P₁
  lam := fun _ _ q => if q = 0 then 1/10 else 1
  εad := fun _ => 1/10
  D := 1
  lamS := fun _ => 1
  ρ := fun _ => 1/90000
  Γ := 12

/-- **The served protocol**: the date-9 service dropped — its certificates fail
(`no_certificate_after`). -/
noncomputable def served : AdapterProtocol state₀ 5 (Fin 2) := protocolB.restrict {4}

lemma served_services : served.services = {4} := by
  show ({4, 9} : Finset ℕ) ∩ {4} = {4}
  decide

/-! ## 5. The theorem, run -/

/-- **The warrant Normative Inductor at Scenario B**, on the served protocol. -/
theorem inductor :
    IsLogicalInductor (WB.market DP) DP ∧
    (∀ n, Enforced (NB n) (res n) →
      ∀ c ∈ (NB n).bundle, excess c.row (WB.priceVec DP n) ≤ tol n) ∧
    (∀ n, ∀ c ∈ WB.bundle n,
      (∃ o ∈ (NB n).survivors, c.cites = Cite.sub o.id ∧ (entitlementB n).Entitled o ∧
        ∀ j, o.cites = .occurrence j → ∃! o', o' ∈ (NB n).survivors ∧ o'.id = j) ∨
      (∃ it ∈ (NB n).seed.liveStr (NB n).docket, c.cites = Cite.str it.id) ∨
      ∃ i, c.cites = Cite.settled i) ∧
    (∀ s ∈ served.services,
      massOff ((served.prob s).gate fun j => WB.market DP s (F5.ι j)) (served.prob s).A ≤
        (served.prob s).κ * (served.evaluation F5.ι).defect s (WB.market DP) ∧
      (served.evaluation F5.ι).defect s (WB.market DP) ≤
        (((served.prob s).massCap * tol s : ℚ) : ℝ)) ∧
    (served.evaluation F5.ι).progress (WB.market DP) ≤
      (served.evaluation F5.ι).modulus + (served.evaluation F5.ι).error +
        served.D * (served.evaluation F5.ι).residual := by
  refine warrant_inductor NB F5 res tol tol_pos entitlementB wellFormedB DP process computation
    72 liability served ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s _; exact enforced s
  · intro s hs
    rw [served_services, Finset.mem_singleton] at hs
    subst hs
    exact excludesB₁
  · intro s hs
    rw [served_services, Finset.mem_singleton] at hs
    subst hs
    exact marginsB₁
  · intros; norm_num [served, AdapterProtocol.restrict, protocolB]
  · norm_num [served, AdapterProtocol.restrict, protocolB]
  · intro r s _ q hq
    simp only [served, AdapterProtocol.restrict, protocolB] at hq ⊢
    simp [P₁] at hq
    simp [hq]
  · intro r s q; simp only [served, AdapterProtocol.restrict, protocolB]; split_ifs <;> norm_num
  · intros; norm_num [served, AdapterProtocol.restrict, protocolB]
  · rw [served_services]; simp [served, AdapterProtocol.restrict, protocolB]
  · intro s hs
    rw [served_services, Finset.mem_singleton] at hs
    subst hs
    simp [served, AdapterProtocol.restrict, protocolB, massCap₁, tol]; norm_num
  · norm_num [served, AdapterProtocol.restrict, protocolB]
  · intro s hs
    rw [served_services, Finset.mem_singleton] at hs
    subst hs
    simp [served, AdapterProtocol.restrict, protocolB, κ₁, state₀, Initial.state, start,
      Fin.sum_univ_two]
    norm_num

/-! ## 6. The rebuttal, step by step -/

/-- **(1) Operative before the refutation**: the strength survives and its specialized row is
enforced. -/
theorem operative_before (n : ℕ) (hn : n < nE) :
    occS ∈ (NB n).survivors ∧
    (⟨Cite.sub 3, specialize (settlementAt n) occS.form.row⟩ : CitedRow (Cite 5) 5) ∈
      WB.bundle n := by
  have hS : occS ∈ (NB n).survivors := by rw [survivors_eq]; simp [hn]
  refine ⟨hS, ?_⟩
  rw [bundle_eq]
  exact ((NB n).mem_bundle_iff _).2 (Or.inl ⟨occS, hS, rfl⟩)

/-- **(2) The consequent settles false while the antecedent stays open**: at `n_E` the
settlement pins `Y` and `X∧A∧Y` false and `X∧A` not at all; the date-9 region contains the point
with `P(X∧A) = 1` and forces `P(X∧A) ≥ 3/4`. -/
theorem antecedent_open :
    (settlementAt nE).val Y = some false ∧ (settlementAt nE).val XAY = some false ∧
    (settlementAt nE).val XA = none ∧
    (NB 9).region ![1, 1, 0, 0, 1] ∧ (∀ x, (NB 9).region x → 3/4 ≤ x XA) := by
  refine ⟨by decide, by decide, by decide, ?_, fun x hx => ?_⟩
  · rw [region_iff]
    simp [InCube, Fin.forall_fin_succ, cP, cA, cS, cZ, n₁, nE, Fixture2.X, Fixture2.XA,
      Fixture2.XAY, Fixture2.Y, Fixture2.Z]
    norm_num
  · rw [region_iff] at hx
    obtain ⟨-, h1, -, -, hA, -, -, -, -, -⟩ := hx
    have h1' := h1 (by decide)
    rw [h1'] at hA
    unfold cA at hA
    linarith

/-- **(3) Withdrawn by rebuttal**: from `n_E` the strength's outcome is `rebutted` and it is not
a survivor. -/
theorem withdrawn (n : ℕ) (hn : nE ≤ n) :
    settleOutcome (settlementAt n) occS.form = .rebutted ∧ occS ∉ (NB n).survivors := by
  refine ⟨by rw [outcome_occS]; simp [hn], ?_⟩
  rw [survivors_eq]
  have hE : ¬ n < nE := by omega
  simp [hE, occS, occP, occA, occZ, Fixture2.occS, Fixture2.occP, Fixture2.occA, Fixture2.occZ]

/-- **(4) Contraposition blocked.**  Had the specialized strength row stayed at date `9` — where
it reads `2/3 · P(X∧A) ≤ 0` — the system would have been infeasible, because the applicability
row with `X` settled true forces `P(X∧A) ≥ 3/4`.  Withdrawal keeps the antecedent where the
applicability puts it rather than suppressing it. -/
theorem contraposition_blocked :
    ¬ ∃ x, ((NB 9).bundle ++
      [(⟨Cite.sub 3, specialize (settlementAt 9) occS.form.row⟩ : CitedRow (Cite 5) 5)]).Region x := by
  rintro ⟨x, hx⟩
  have hreg : (NB 9).region x := ⟨hx.1, fun c hc => hx.2 c (List.mem_append_left _ hc)⟩
  have hrow : (specialize (settlementAt 9) occS.form.row).Sat x :=
    hx.2 _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hXA : 3/4 ≤ x XA := antecedent_open.2.2.2.2 x hreg
  have hpin : (settlementAt 9).Pinned x := ((NormState.region_iff (NB 9) x).1 hreg).2.1
  rw [specialize_sat_iff _ _ hpin] at hrow
  have hS : cS * x XA ≤ x XAY := (Form.strength_sat_iff XA XAY cS x).1 hrow
  have hXAY : x XAY = 0 := (((region_iff 9 x).1 hreg).2.2.1 (by decide)).1
  unfold cS at hS
  linarith

/-! ## 7. The same question, before and after -/

/-- **The region flips on the refraining score**: at most `1/3` at date `4`, at least `3/4` at
date `9`. -/
theorem region_flips :
    (∀ x, (NB 4).region x → x XA - x XAY ≤ 1/3) ∧
    (∀ x, (NB 9).region x → 3/4 ≤ x XA - x XAY) := by
  constructor
  · intro x hx
    rw [region_iff] at hx
    obtain ⟨hc, -, -, -, -, hS, -, -, -, -⟩ := hx
    have := hS (by decide)
    have := (hc XA).2
    unfold cS at *
    linarith
  · intro x hx
    have hXA := antecedent_open.2.2.2.2 x hx
    rw [region_iff] at hx
    obtain ⟨-, -, hE, -, -, -, -, -, -, -⟩ := hx
    have := (hE (by decide)).1
    linarith

/-- A row admitted into a bundle is satisfied at every point of the bundle's region. -/
theorem sat_of_admitted {B : Bundle (Cite 5) 5} {q : Cite 5} {r : Row 5}
    (h : VerdictCert.RowAdmitted B q r) {x : Fin 5 → ℚ} (hx : B.Region x) : r.Sat x := by
  rcases h with h | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact hx.2 _ h
  · exact cubeUpper_sat hx.1 i
  · exact cubeLower_sat hx.1 i

/-- **The guarantees change.**  No `Excludes` certificate and no `Margins` certificate for `P₁`
exists on the date-9 bundle: the point `(1, 1, 0, 0, 1)` of the region prices refraining at `1`
and acting at `0`, and a sound certificate cannot bound the first below `1/3` or the second
above `5/12`.  The adapter theorem's hypotheses for this question are unsatisfiable at date
`9`, whatever certificates are offered. -/
theorem no_certificate_after : ¬ P₁.Excludes (NB 9).bundle ∧ ¬ P₁.Margins (NB 9).bundle (tol 9) := by
  have hp : (NB 9).region ![1, 1, 0, 0, 1] := antecedent_open.2.2.2.1
  have hτ : P₁.τ = 1/3 := rfl
  have hδ : P₁.δ = 1/12 := rfl
  constructor
  · intro hex
    obtain ⟨hlive, hval⟩ := hex 1 (by simp [P₁])
    have hs := (P₁.upper 1).cert.sound ![1, 1, 0, 0, 1]
      (fun i hi => sat_of_admitted (hlive i hi) hp)
    have h1 : ∑ j, P₁.ℓ 1 j * (![1, 1, 0, 0, 1] : Fin 5 → ℚ) j = 1 := by
      simp [P₁, eXA_XAY, Fin.sum_univ_five, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
        Fixture2.Z]
    rw [h1] at hs
    have h0 : P₁.offset 1 = 0 := rfl
    rw [hτ, h0] at hval
    push_cast at hval
    have : (1 : ℝ) ≤ ((P₁.upper 1).cert.value : ℝ) := by exact_mod_cast hs
    linarith
  · intro hmar
    obtain ⟨hlive, hval⟩ := hmar 0 (by simp [P₁])
    have hs := (P₁.lower 0).cert.sound ![1, 1, 0, 0, 1]
      (fun i hi => sat_of_admitted (hlive i hi) hp)
    have h1 : ∑ j, -(P₁.ℓ 0 j) * (![1, 1, 0, 0, 1] : Fin 5 → ℚ) j = 0 := by
      simp [P₁, eXAY, Fin.sum_univ_five, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
        Fixture2.Z]
    rw [h1] at hs
    have h0 : P₁.offset 0 = 0 := rfl
    have ht : tol 9 = 1/400 := rfl
    rw [hτ, hδ, h0, ht] at hval
    push_cast at hval
    have hs' : (0 : ℝ) ≤ ((P₁.lower 0).cert.value : ℝ) := by exact_mod_cast hs
    have hm : (0 : ℝ) ≤ ((P₁.lower 0).cert.mass : ℝ) := by
      exact_mod_cast (P₁.lower 0).cert.mass_nonneg
    linarith

/-- The two rows of the date-9 bundle that pin the question: the pin `P(X∧A∧Y) ≤ 0` and the
applicability row with `X` settled, `3/4 ≤ P(X∧A)`. -/
def rowPinXAY : Row 5 := ⟨fun j => if j = XAY then 1 else 0, 0⟩
def rowA9 : Row 5 := specialize (settlementAt 9) occA.form.row

lemma rowPinXAY_mem : rowPinXAY ∈ (settlementAt 9).pinRowsAt XAY := by
  have h : (settlementAt 9).val XAY = some false := by decide
  simp [Settlement.pinRowsAt, h, rowPinXAY, truth]

lemma memPin9 :
    (⟨Cite.settled XAY, rowPinXAY⟩ : CitedRow (Cite 5) 5) ∈ (NB 9).bundle :=
  ((NB 9).mem_bundle_iff _).2 (Or.inr (Or.inr ⟨XAY, rowPinXAY, rowPinXAY_mem, rfl⟩))

lemma memA9 : (⟨Cite.sub 2, rowA9⟩ : CitedRow (Cite 5) 5) ∈ (NB 9).bundle :=
  ((NB 9).mem_bundle_iff _).2 (Or.inl ⟨occA, by rw [survivors_eq]; simp, rfl⟩)

lemma rowA9_a : rowA9.a = ![0, -1, 0, 0, 0] := by
  funext j
  fin_cases j <;> simp [rowA9, specialize, settlementAt, occA, Fixture2.occA, Form.row, cA,
    show n₁ = 3 from rfl, show nE = 8 from rfl, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
    Fixture2.Z]

lemma rowA9_b : rowA9.b = -3/4 := by
  norm_num [rowA9, specialize, settledTerm, settlementAt, occA, Fixture2.occA, Form.row, cA,
    show n₁ = 3 from rfl, show nE = 8 from rfl, Fin.sum_univ_five, Fixture2.X, Fixture2.XA,
    Fixture2.XAY, Fixture2.Y, Fixture2.Z, truth]

lemma excess_rowA9 (p : Fin 5 → ℚ) : excess rowA9 p = -(p XA) + 3/4 := by
  simp [excess, rowA9_a, rowA9_b, Fin.sum_univ_five, Fixture2.XA]
  ring

lemma excess_rowPinXAY (p : Fin 5 → ℚ) : excess rowPinXAY p = p XAY := by
  simp [excess, rowPinXAY, Fin.sum_univ_five, Fixture2.XAY]

/-- **The adapter's behavior changes.**  At the realized market the gate acts with mass at
least `24/25` at date `4`; at date `9` it puts mass `0` on acting and `1` on refraining, because
the enforced pin holds `P(X∧A∧Y) ≤ 1/400 < τ` and the enforced applicability row holds
`P(X∧A) ≥ 3/4 − 1/400`, so the refraining score clears `τ + δ`. -/
theorem same_question :
    (24/25 : ℝ) ≤ P₁.gate (fun j => WB.market DP 4 (F5.ι j)) 0 ∧
    P₁.gate (fun j => WB.market DP 9 (F5.ι j)) 0 = 0 ∧
    P₁.gate (fun j => WB.market DP 9 (F5.ι j)) 1 = 1 := by
  have hτ : P₁.τ = 1/3 := rfl
  have hδ : P₁.δ = 1/12 := rfl
  obtain ⟨-, hconf, -, h, -⟩ := inductor
  refine ⟨?_, ?_⟩
  · -- before: the theorem's bound and the gate's normalization
    have hB4 : WB.bundle 4 = (NB 4).bundle := bundle_eq 4
    have hy4 : (WB.bundle 4).Region (wit 4) := by rw [hB4]; exact wit_mem 4
    have hmar4 : P₁.Margins (WB.bundle 4) (WB.tol 4) := by rw [hB4]; exact marginsB₁
    have hsum := P₁.gate_sum_one WB DP 4 (wit 4) hy4 hmar4
    rw [Fin.sum_univ_two] at hsum
    have h4 := h 4 (by rw [served_services]; simp)
    have e4 : served.prob 4 = P₁ := rfl
    rw [e4] at h4
    have hmass : massOff (P₁.gate fun j => WB.market DP 4 (F5.ι j)) {0} ≤ 1/25 := by
      calc massOff (P₁.gate fun j => WB.market DP 4 (F5.ι j)) {0}
          ≤ P₁.κ * (served.evaluation F5.ι).defect 4 (WB.market DP) := h4.1
        _ ≤ P₁.κ * ((P₁.massCap * tol 4 : ℚ) : ℝ) :=
            mul_le_mul_of_nonneg_left h4.2 (by rw [κ₁]; norm_num)
        _ = 1/25 := by rw [κ₁, massCap₁]; norm_num [tol]
    unfold massOff at hmass
    rw [univ_sdiff_zero, Finset.sum_singleton] at hmass
    have hsum' : P₁.gate (fun j => WB.market DP 4 (F5.ι j)) 0 +
        P₁.gate (fun j => WB.market DP 4 (F5.ι j)) 1 = 1 := hsum
    linarith
  · -- after: the two enforced rows pin the scores
    have hex := hconf 9 (enforced 9)
    have hA9 := hex _ memA9
    have hP9 := hex _ memPin9
    simp only at hA9 hP9
    rw [excess_rowA9] at hA9
    rw [excess_rowPinXAY] at hP9
    have ht : tol 9 = 1/400 := rfl
    rw [ht] at hA9 hP9
    set p := WB.priceVec DP 9 with hp
    have hXA : (3/4 - 1/400 : ℝ) ≤ (p XA : ℝ) := by
      have hq : (3/4 - 1/400 : ℚ) ≤ p XA := by linarith
      have := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at this
      exact this
    have hXAY : ((p XAY : ℚ) : ℝ) ≤ 1/400 := by
      have := (Rat.cast_le (K := ℝ)).mpr hP9
      push_cast at this
      exact this
    have hb : (fun j => WB.market DP 9 (F5.ι j)) = fun j => ((p j : ℚ) : ℝ) := rfl
    have hs0 : P₁.scoreR (fun j => ((p j : ℚ) : ℝ)) 0 = (p XAY : ℝ) := by
      simp [Problem.scoreR, P₁, eXAY, Fin.sum_univ_five, Fixture2.X, Fixture2.XA, Fixture2.XAY,
        Fixture2.Y, Fixture2.Z]
    have hs1 : P₁.scoreR (fun j => ((p j : ℚ) : ℝ)) 1 = (p XA : ℝ) - (p XAY : ℝ) := by
      simp [Problem.scoreR, P₁, eXA_XAY, Fin.sum_univ_five, Fixture2.X, Fixture2.XA,
        Fixture2.XAY, Fixture2.Y, Fixture2.Z]
      ring
    have hw0 : weight (P₁.scoreR fun j => ((p j : ℚ) : ℝ)) P₁.pref P₁.τ P₁.δ 0 = 0 := by
      unfold weight
      rw [hs0, hτ, hδ]
      have hneg : ((p XAY : ℝ) - 1/3) / (1/12) < 0 :=
        div_neg_of_neg_of_pos (by linarith) (by norm_num)
      have : ramp (((p XAY : ℝ) - 1/3) / (1/12)) = 0 := by
        unfold ramp
        exact max_eq_left ((min_le_right _ _).trans hneg.le)
      rw [this, zero_mul]
    have hw1 : weight (P₁.scoreR fun j => ((p j : ℚ) : ℝ)) P₁.pref P₁.τ P₁.δ 1 = 1 := by
      unfold weight
      rw [hs1, hτ, hδ, ramp_eq_one]
      · simp [P₁]
      · rw [le_div_iff₀ (by norm_num)]; linarith
    have htot : total (P₁.scoreR fun j => ((p j : ℚ) : ℝ)) P₁.pref P₁.τ P₁.δ = 1 := by
      unfold total
      rw [Fin.sum_univ_two, hw0, hw1, zero_add]
    rw [hb]
    constructor
    · show weight (P₁.scoreR fun j => ((p j : ℚ) : ℝ)) P₁.pref P₁.τ P₁.δ 0 /
        total (P₁.scoreR fun j => ((p j : ℚ) : ℝ)) P₁.pref P₁.τ P₁.δ = 0
      rw [hw0, zero_div]
    · show weight (P₁.scoreR fun j => ((p j : ℚ) : ℝ)) P₁.pref P₁.τ P₁.δ 1 /
        total (P₁.scoreR fun j => ((p j : ℚ) : ℝ)) P₁.pref P₁.τ P₁.δ = 1
      rw [hw1, htot, div_one]

/-! ## 8. Accounting for the dropped service -/

/-- **The residual carries the unserved question.**  The declared protocol's residual is `1/4`;
the served protocol's is `1/2`: the date-9 transport mass `1/4` moves into the residual, where
the Progress bound of `inductor` charges it at `D = 1`. -/
theorem residual_restricted :
    (protocolB.evaluation F5.ι).residual = 1/4 ∧ (served.evaluation F5.ι).residual = 1/2 := by
  constructor
  · simp [Evaluation.residual, AdapterProtocol.evaluation, protocolB, state₀, Initial.state,
      start, Fin.sum_univ_two]
    norm_num
  · have h := protocolB.residual_restrict {4} F5.ι
    have h' : (protocolB.evaluation F5.ι).residual = 1/4 := by
      simp [Evaluation.residual, AdapterProtocol.evaluation, protocolB, state₀, Initial.state,
        start, Fin.sum_univ_two]
      norm_num
    rw [show served = protocolB.restrict {4} from rfl, h, h']
    have hd : ({4, 9} : Finset ℕ) \ {4} = {9} := by decide
    simp [protocolB, hd, state₀, Initial.state, start, Fin.sum_univ_two]
    norm_num

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.docketB
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.NB
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.NB_eq_N
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.survivors_eq
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.liveStr_eq
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.region_iff
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.wit_mem
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.check
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.res
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.WB
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.enforced
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.bundle_eq
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.NB_eq_of_phase
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.bundle_step
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.computation
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.dom_wAY'
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.dom_bundle
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.liability
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.entitlementB
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.wellFormedB
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.excludesB₁
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.marginsB₁
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.protocolB
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.served
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.served_services
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.inductor
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.operative_before
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.antecedent_open
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.withdrawn
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.contraposition_blocked
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.region_flips
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.sat_of_admitted
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.no_certificate_after
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.rowPinXAY
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.rowA9
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.rowPinXAY_mem
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.memPin9
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.memA9
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.rowA9_a
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.rowA9_b
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.excess_rowA9
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.excess_rowPinXAY
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.same_question
#print axioms Workspace.Normativity.Contrib.WarrantInductorRebuttal.residual_restricted

end Workspace.Normativity.Contrib.WarrantInductorRebuttal
