import Cleanroom.Decision.DpCalibLimits.SscMasked
import Cleanroom.Decision.DpCalibLimits.AppendixB
import Cleanroom.Decision.DpCalibLimits.Cancellation
import Cleanroom.Decision.DpCalibLimits.Family
import Cleanroom.Decision.DpCalibLimits.TsMsr
import Cleanroom.Decision.DpCalibLimits.ChanceTwin
import Cleanroom.Decision.DpCalibLimits.PopperClass
import Cleanroom.Decision.DpCalibLimits.Sampler
import Cleanroom.Found.DpCoreTree.WitnessesR1

/-!
# Repair round 1 — hypothesis-package witnesses ([[STANDARDS]] §3)

Audit round 1 (adversarial B1, fidelity N2) found headlines whose hypothesis packages were
inhabited by no declaration. This module ships the inhabitants, lifted from the auditors'
probes (`run/wp/dp-calib-limits/audit-r1-probes/`) and extended:

* **T12 on `TB(θ)`** (`tbPerRunState`, `tb_perRun_witness`, `tb_perRun_instance`,
  `tb_perRunMasked_instance`): the strict state of `C[d ↦ m]` at the world event
  `tbTop = {topCross, topNot}` (which on `TB(θ)` *is* `occ(d)`) satisfies the per-run clauses for
  every self-model `m`; both headlines instantiated, with `A_d^+ = {not}` at `m = δ_not`
  (adversarial N8).
* **The cancellation family on `coinQuery`** (`coinQuery_cancellation_package`,
  `coinQuery_cancellation`, `coinQuery_no_zero_survives`, `coinQuery_condExp_deviate`) and the
  recording package (`coinQuery_nav`, `coinQuery_sv`, `coinQuery_recording_package`,
  `coinQuery_recordsFor_of_veridical`, `coinQuery_self_transparent`), plus the bridge from
  node-level to leaf-level action veridicality (`hav_of_nodeActionVeridical`, adversarial N7).
* **T4(c),(d) on `coinQuery`** (`coinQuery_msr_realized_instance`, `coinQuery_msr17_instance`):
  N− as a separation (all payoffs tie), N+ as inhabitants (mixed label, chance node, every act
  realized); **T4(c) N+ on the miniature** (`miniature_msr_realized_instance`: the non-constant
  test sequence of `procQ ⅔`, both act events realized, `MSRAt` at `d`).
  **MSR¹⁷ ⊋ MSR in-domain** (`t1_msr17_not_msr`, adversarial N4): on the recorded
  `t1` with `δ_a`, `T_EDT` approves at the strict state and `MSRAt` fails (`limitVal b = 1 > 0`).
* **T16's invariance on `chanceTwin`** (`chanceTwin_twin_leaves_instance`): the two `a`-leaves
  inhabit `popperLimit_twin_leaves`'s package and the invariance returns the `½` that
  `chanceTwin_popperLimitRay` computes.
* **SE-18′(b)'s Open in the εFP form** (`tsTr_epsFP`, `tsTr_tendsTo`, adversarial N1): the
  reversal family is an ε-floored fixed-point family converging to `C₀`.
* **The Definition-15 encoding check** (`sigmaPi_half_consistent`, fidelity N2): `Σ_{½}` *is*
  strictly consistent (fill coin `p = ½`, every label), so `sigmaPi_not_consistent`'s
  impossibility is not an artifact of an unsatisfiable encoding.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-! ## T12: the per-run witness state on `TB(θ)` -/

section tb

/-- The top branch of `TB(θ)` as a world event — on `TB(θ)` this is the run event `occ(d)`.
Source: P11 §A4; audit r1 adversarial B1. Kind: D -/
def tbTop : Finset TbW := {.topCross, .topNot}

/-- `ν(tbTop) = (1 − θ)(m(a) + m(b))` under any procedure. Source: none: infrastructure. Kind: L -/
theorem tb_nu_top (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (C : Proc TbPt (fun _ => Act2) ℚ) :
    nu C (tbTheta θ h0 h1) tbTop = (1 - θ) * ((C .d).w .a + (C .d).w .b) := by
  rw [nu_eq_sum, tb_sum]
  simp [tbTheta, leafLaw, tbPt, tbW, tbTop, Fin.sum_univ_two, Act2.sum_univ, FinDistr.coin]
  ring

/-- `ν(tbTop) = 1 − θ`. Source: none: infrastructure. Kind: L -/
theorem tb_nu_top_eq (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (C : Proc TbPt (fun _ => Act2) ℚ) :
    nu C (tbTheta θ h0 h1) tbTop = 1 - θ := by
  rw [tb_nu_top]
  have := (C .d).sum_one
  rw [Act2.sum_univ] at this
  rw [this, mul_one]

/-- `ν(tbTop) > 0` for `θ < 1`. Source: none: infrastructure. Kind: L -/
theorem tb_nu_top_pos (θ : ℚ) (h0 : 0 < θ) (h1 : θ < 1) (C : Proc TbPt (fun _ => Act2) ℚ) :
    0 < nu C (tbTheta θ h0.le h1.le) tbTop := by
  rw [tb_nu_top_eq]; linarith

/-- On `TB(θ)`, `{λ ⊨ X} ∩ occ(d)` has the mass of the world event `X ∩ tbTop`.
Source: none: infrastructure. Kind: L -/
theorem tb_occ_mass_eq (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (C : Proc TbPt (fun _ => Act2) ℚ)
    (X : Finset TbW) :
    mass C (tbTheta θ h0 h1) (worldEv (tbTheta θ h0 h1) X ∩ occ .d (tbTheta θ h0 h1)) =
      nu C (tbTheta θ h0 h1) (X ∩ tbTop) := by
  rw [nu_eq_sum]
  simp only [mass, worldEv, occ, ← Finset.filter_and, Finset.sum_filter]
  rw [tb_sum, tb_sum]
  simp [tbTheta, leafLaw, tbPt, tbW, tbTop, count, Fin.sum_univ_two, Act2.sum_univ, FinDistr.coin]

/-- The payoff mass on `{λ ⊨ X} ∩ occ(d)` is `paySum (X ∩ tbTop)`.
Source: none: infrastructure. Kind: L -/
theorem tb_occ_pay_eq (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (C : Proc TbPt (fun _ => Act2) ℚ)
    (X : Finset TbW) :
    (∑ ℓ ∈ worldEv (tbTheta θ h0 h1) X ∩ occ .d (tbTheta θ h0 h1),
        leafLaw C (tbTheta θ h0 h1) ℓ * payoff (tbTheta θ h0 h1) ℓ) =
      paySum C (tbTheta θ h0 h1) (X ∩ tbTop) := by
  rw [paySum_eq_sum_ite]
  simp only [worldEv, occ, ← Finset.filter_and, Finset.sum_filter]
  rw [tb_sum, tb_sum]
  simp [tbTheta, leafLaw, tbPt, tbW, tbPay, tbTop, count, Fin.sum_univ_two, Act2.sum_univ,
    FinDistr.coin]

/-- **The per-run witness state of `C[d ↦ m]` on `TB(θ)`**: the strict state at the world event
`tbTop` (= `occ(d)` on this tree).
Source: P11 §A4; audit r1 adversarial B1
Kind: D -/
noncomputable def tbPerRunState (θ : ℚ) (h0 : 0 < θ) (h1 : θ < 1) (m : FinDistr ℚ Act2) :
    State TbW ℚ :=
  calibratedState (tbProc.deviate .d m) (tbTheta θ h0.le h1.le) tbTop (tb_nu_top_pos θ h0 h1 _)

/-- **The per-run clauses hold at the witness state** under `C[d ↦ m]`, for every self-model `m`.
Source: [[decision-problems-v2]] Definition 13 on `TB(θ)`; audit r1 adversarial B1
Kind: N+
Fidelity: exact
Hyps: (a) `0 < θ < 1` -/
theorem tb_perRun_witness (θ : ℚ) (h0 : 0 < θ) (h1 : θ < 1) (m : FinDistr ℚ Act2) :
    PerRunClausesAt (fun _ => tbPerRunState θ h0 h1 m) (tbProc.deviate .d m)
      (tbTheta θ h0.le h1.le) .d := by
  have hocc := (tb_occ_masses θ h0.le h1.le m).1
  have htop := tb_nu_top_eq θ h0.le h1.le (tbProc.deviate .d m)
  refine ⟨fun X => ?_, fun X hP hM => ?_⟩
  · simp only [tbPerRunState]
    rw [calibratedState_pr, hocc, tb_occ_mass_eq, htop]
    have : (1 - θ) ≠ 0 := by linarith
    field_simp
  · simp only [tbPerRunState] at hP ⊢
    rw [tb_occ_mass_eq] at hM ⊢
    rw [tb_occ_pay_eq, calibratedState_V]
    field_simp

/-- `P(not) = 1` at the witness state of `δ_not` itself. Source: none: infrastructure. Kind: L -/
theorem tbPerRunState_pure_pr_not (θ : ℚ) (h0 : 0 < θ) (h1 : θ < 1) :
    (tbPerRunState θ h0 h1 (tbProc .d)).pr (tbActEv .d .b) = 1 := by
  simp only [tbPerRunState]
  rw [calibratedState_pr, tb_nu_top_eq]
  have h1θ : (1 - θ) ≠ 0 := by linarith
  rw [div_eq_one_iff_eq h1θ, nu_eq_sum, tb_sum]
  simp [tbTheta, leafLaw, tbPt, tbW, tbTop, tbActEv, tbProc, Proc.deviate, Fin.sum_univ_two,
    Act2.sum_univ, FinDistr.coin]

/-- **T12(i)'s package is inhabited** (`m = δ_not`, i.e. `C = δ_not` itself): the per-run clauses
hold at the witness state, and there `P(cross) = 0`, `A_d^+ = {not}` (the mandate's and
P11-12′(e)'s equality, not only `⊆`) and `T_EDT` approves `not`.
Source: P11-12′(e); mandate T12(i); audit r1 adversarial B1, N8
Kind: N+
Fidelity: exact on `TB(θ)`
Hyps: (a) `0 < θ < 1` -/
theorem tb_perRun_instance (θ : ℚ) (h0 : 0 < θ) (h1 : θ < 1) :
    PerRunClausesAt (fun _ => tbPerRunState θ h0 h1 (tbProc .d)) tbProc (tbTheta θ h0.le h1.le) .d ∧
    (tbPerRunState θ h0 h1 (tbProc .d)).pr (tbActEv .d .a) = 0 ∧
    APlus (fun _ => tbPerRunState θ h0 h1 (tbProc .d)) tbActEv .d = {.b} ∧
    TEdtAt (fun _ => tbPerRunState θ h0 h1 (tbProc .d)) tbActEv tbProc .d := by
  have hself : tbProc.deviate .d (tbProc .d) = tbProc := Function.update_eq_self _ _
  have h := tb_perRun_witness θ h0 h1 (tbProc .d)
  rw [hself] at h
  obtain ⟨hP0, hT⟩ := tb_perRun_not_approved θ h0 h1 _ h
  have hP1 := tbPerRunState_pure_pr_not θ h0 h1
  refine ⟨h, hP0, ?_, hT⟩
  ext a
  cases a <;> simp [APlus, hP0, hP1]

/-- **T12(ii)'s package is inhabited** (`m = (½, ½)`): per-run SSC with a full-support self-model
holds at the witness state, and there `argmax = {cross}` and `T_EDT` rejects `δ_not`.
Source: P11 §A4; mandate T12(ii) ("at every full-support `m` (N+)"); audit r1 adversarial B1
Kind: N+
Fidelity: exact on `TB(θ)`
Hyps: (a) `0 < θ < 1` -/
theorem tb_perRunMasked_instance (θ : ℚ) (h0 : 0 < θ) (h1 : θ < 1) :
    PerRunSSCMaskedAt tbProc (tbTheta θ h0.le h1.le) (fun _ => tbPerRunState θ h0 h1 half) .d ∧
    argmaxPlus (fun _ => tbPerRunState θ h0 h1 half) tbActEv .d = {.a} ∧
    ¬ TEdtAt (fun _ => tbPerRunState θ h0 h1 half) tbActEv tbProc .d := by
  have hpkg : PerRunSSCMaskedAt tbProc (tbTheta θ h0.le h1.le)
      (fun _ => tbPerRunState θ h0 h1 half) .d :=
    ⟨half, half_pos, by rw [(tb_occ_masses θ h0.le h1.le half).1]; linarith,
      tb_perRun_witness θ h0 h1 half⟩
  exact ⟨hpkg, tb_perRunMasked_rejects θ h0 h1 _ hpkg⟩

end tb

/-! ## The veridicality bridge and the cancellation family on `coinQuery` -/

section bridge

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- **Node-level action veridicality implies the leaf-level form** the cancellation lemma uses:
if every `d`-node is node-action-veridical, a leaf whose path draws `(d, a)` has its world in
the `a`-event (through `mem_draws_iff_exists_edgeS`). So the mandate's `NodeActionVeridical`
hypothesis discharges `cancellation`'s `hav`.
Source: mandate T6(b) (the node-level hypothesis); audit r1 adversarial N7
Kind: L -/
theorem hav_of_nodeActionVeridical (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts K)
    (d : ι) (hnav : ∀ q, pt B q = d → NodeActionVeridical actEv B q) :
    ∀ (ℓ : B.Leaves) (a : acts d), (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ → world B ℓ ∈ actEv d a := by
  intro ℓ a ha
  obtain ⟨q, hq⟩ := (mem_draws_iff_exists_edgeS B ℓ ⟨d, a⟩).mp ha
  unfold edgeS at hq
  rw [Option.map_eq_some_iff] at hq
  obtain ⟨a', ha', hsig⟩ := hq
  obtain ⟨hpt, hheq⟩ := Sigma.mk.inj_iff.mp hsig
  subst hpt
  have := hnav q rfl ℓ a' ha'
  rwa [eq_of_heq hheq] at this

end bridge

section cq

/-- Every `d`-node of `coinQuery` is node-action-veridical: the leaf below its `a`-edge has act
coordinate `a`. Source: none: infrastructure. Kind: L -/
theorem coinQuery_nav (q : coinQuery.DecNode) (_ : pt coinQuery q = ()) :
    NodeActionVeridical cqActEv coinQuery q := by
  unfold coinQuery at q ⊢
  rcases q with ⟨i', (_ | ⟨b, q⟩)⟩
  · rintro ⟨i, act, _⟩ a ha
    by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      simp [cqActEv]
    · simp [edgeOf_chance, hi] at ha
  · exact q.elim

/-- Every `d`-node of `coinQuery` is subtree-veridical (`O = ⊤`). Source: none: infrastructure.
Kind: L -/
theorem coinQuery_sv (q : coinQuery.DecNode) (_ : pt coinQuery q = ()) :
    SubtreeVeridical cqObs coinQuery q := fun _ _ => by simp [cqObs]

/-- Leaf-level action veridicality on `coinQuery` (the bridge applied). Source: none:
infrastructure. Kind: L -/
theorem coinQuery_hav :
    ∀ (ℓ : coinQuery.Leaves) (a : Act2),
      (⟨(), a⟩ : Σ d : Unit, Act2) ∈ draws coinQuery ℓ → world coinQuery ℓ ∈ cqActEv () a :=
  hav_of_nodeActionVeridical cqActEv coinQuery () coinQuery_nav

/-- **The cancellation package on `coinQuery`**, every `procQ q`: `#_d ≤ 1`, coverage for the
uniform deviation, leaf-level action veridicality, disjoint action events.
Source: mandate T6(b); audit r1 adversarial B1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem coinQuery_cancellation_package (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (∀ ℓ, count () coinQuery ℓ ≤ 1) ∧
    Covers cqObs ((procQ q h0 h1).deviate () FinDistr.uniform) coinQuery () ∧
    (∀ (ℓ : coinQuery.Leaves) (a : Act2),
      (⟨(), a⟩ : Σ d : Unit, Act2) ∈ draws coinQuery ℓ → world coinQuery ℓ ∈ cqActEv () a) ∧
    (∀ a a' : Act2, a ≠ a' → Disjoint (cqActEv () a) (cqActEv () a')) :=
  ⟨fun ℓ => (coinQuery_count ℓ).le, coinQuery_covers _, coinQuery_hav, cqActEv_disjoint⟩

/-- `cancellation` instantiated on `coinQuery` (a chance node before the query, mixed `q`).
Source: mandate T6(b); audit r1 adversarial B1
Kind: N+ -/
theorem coinQuery_cancellation (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (m : FinDistr ℚ Act2) (a : Act2)
    (X : Finset CoinQueryW) :
    nu ((procQ q h0 h1).deviate () m) coinQuery (X ∩ cqActEv () a ∩ cqObs ()) *
        nu (procQ q h0 h1) coinQuery (cqActEv () a ∩ cqObs ()) =
      nu (procQ q h0 h1) coinQuery (X ∩ cqActEv () a ∩ cqObs ()) *
        nu ((procQ q h0 h1).deviate () m) coinQuery (cqActEv () a ∩ cqObs ()) :=
  cancellation cqObs cqActEv (procQ q h0 h1) coinQuery () m a X (fun ℓ => (coinQuery_count ℓ).le)
    (coinQuery_covers _) coinQuery_hav cqActEv_disjoint

/-- `zero_survives_iff` instantiated on `coinQuery`: no zero survives (`θ_a > 0`,
`coinQuery_theta_pos`), so some full-support self-model gives `a` positive mass.
Source: mandate T7(c); audit r1 adversarial B1
Kind: N+ -/
theorem coinQuery_no_zero_survives (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ¬ ∀ m : FinDistr ℚ Act2, (∀ a', 0 < m.w a') →
        nu ((procQ q h0 h1).deviate () m) coinQuery (cqActEv () .a ∩ cqObs ()) = 0 := by
  rw [zero_survives_iff cqObs cqActEv (procQ q h0 h1) coinQuery () .a
    (fun ℓ => (coinQuery_count ℓ).le) (coinQuery_covers _) coinQuery_hav cqActEv_disjoint]
  exact (coinQuery_theta_pos q h0 h1).ne'

/-- `condExp_deviate_eq` instantiated on `coinQuery` with `q = ½`, `m = Unif`: the masked act
value is the strict one. **N−**: every payoff on `coinQuery` is `0`, so both sides are `0` by
`coinQuery_condExp_zero` whatever `m` does — this instance says nothing about the cancellation.
The N+ is `cqPay_condExp_deviate_nontrivial` (`WitnessesR2.lean`: coin-dependent payoffs,
common value `½`). Source: mandate T6(b); audit r1 adversarial B1; regraded in repair round 2
(audit r2 adversarial B1). Kind: N− -/
theorem coinQuery_condExp_deviate :
    condExp ((procQ (1/2) (by norm_num) (by norm_num)).deviate () FinDistr.uniform) coinQuery
        (cqActEv () .a ∩ cqObs ()) =
      condExp (procQ (1/2) (by norm_num) (by norm_num)) coinQuery (cqActEv () .a ∩ cqObs ()) := by
  apply condExp_deviate_eq cqObs cqActEv _ coinQuery () FinDistr.uniform .a
    (fun ℓ => (coinQuery_count ℓ).le) (coinQuery_covers _) coinQuery_hav cqActEv_disjoint
  · rw [coinQuery_nu]
    simp [cqActEv, cqObs, FinDistr.uniform_w]
    try exact Fintype.card_pos_iff.mpr ⟨Act2.a⟩
  · rw [coinQuery_nu]
    simp [cqActEv, cqObs, procQ]
    try norm_num

/-- **The recording package of `recordsFor_of_veridical` on `coinQuery`** for every `C'`: `#_d ≤ 1`,
coverage, subtree- and node-action-veridicality of every `d`-node, disjoint action events —
and the conclusion `RecordsFor` (agreeing with `dp-core-tree`'s direct `coinQuery_recordsFor`).
Source: mandate T7(c); audit r1 adversarial B1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem coinQuery_recording_package (C' : Proc Unit (fun _ => Act2) ℚ) :
    ((∀ ℓ, count () coinQuery ℓ ≤ 1) ∧ Covers cqObs C' coinQuery () ∧
      (∀ q, pt coinQuery q = () → SubtreeVeridical cqObs coinQuery q) ∧
      (∀ q, pt coinQuery q = () → NodeActionVeridical cqActEv coinQuery q) ∧
      (∀ a a' : Act2, a ≠ a' → Disjoint (cqActEv () a) (cqActEv () a'))) ∧
    RecordsFor cqObs cqActEv C' coinQuery () :=
  ⟨⟨fun ℓ => (coinQuery_count ℓ).le, coinQuery_covers _, coinQuery_sv, coinQuery_nav,
      cqActEv_disjoint⟩,
    recordsFor_of_veridical cqObs cqActEv coinQuery C' () (fun ℓ => (coinQuery_count ℓ).le)
      (coinQuery_covers _) coinQuery_sv coinQuery_nav cqActEv_disjoint⟩

/-- **Self-transparency on the manifold, instantiated on `coinQuery`**:
`ν_{C[d↦m]}(a ∧ O) = m(a) · ν_{C[d↦m]}(O)` for every `q`, `m`, `a`.
Source: CA-8′(ii); audit r1 adversarial B1
Kind: N+ -/
theorem coinQuery_self_transparent (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (m : FinDistr ℚ Act2)
    (a : Act2) :
    nu ((procQ q h0 h1).deviate () m) coinQuery (cqActEv () a ∩ cqObs ()) =
      m.w a * nu ((procQ q h0 h1).deviate () m) coinQuery (cqObs ()) :=
  nu_deviate_actEv_eq_self cqObs cqActEv (procQ q h0 h1) coinQuery () m
    (fun ℓ => (coinQuery_count ℓ).le) (coinQuery_covers _) coinQuery_sv coinQuery_nav
    cqActEv_disjoint a

end cq

/-! ## T4(c),(d) on `coinQuery`; MSR¹⁷ ⊋ MSR on the recorded `t1` -/

section msr

/-- Every payoff mass on `coinQuery` is `0`. Source: none: infrastructure. Kind: L -/
theorem coinQuery_paySum_zero (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset CoinQueryW) :
    paySum C coinQuery X = 0 := by
  unfold paySum
  apply Finset.sum_eq_zero
  intro ℓ _
  rw [coinQuery_payoff, mul_zero]

/-- Every act value on `coinQuery` is `0`. Source: none: infrastructure. Kind: L -/
theorem coinQuery_condExp_zero (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset CoinQueryW) :
    condExp C coinQuery X = 0 := by
  unfold condExp; rw [coinQuery_paySum_zero, zero_div]

/-- `ν(a ∧ O) = C(d)(a)` on `coinQuery` (recording, `ν(O) = 1`). Source: none: infrastructure.
Kind: L -/
theorem coinQuery_nu_act (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    nu C coinQuery (cqActEv () a ∩ cqObs ()) = (C ()).w a := by
  rw [nu_actEv_inter_obs_of_recordsFor cqObs cqActEv C coinQuery (coinQuery_recordsFor C) a,
    coinQuery_nu_obs, mul_one]

/-- The query point is queried. Source: none: infrastructure. Kind: L -/
theorem coinQuery_queried : () ∈ queried coinQuery := by
  unfold coinQuery
  simp [queried_chance, queried_decision]

/-- FF on `coinQuery` for `procQ ½` (all payoffs `0`, every comparison `0 ≤ 0`).
Source: audit r1 adversarial B1. Kind: N− (as a separation; every act value ties) -/
theorem coinQuery_half_ff :
    FF cqObs cqActEv (procQ (1/2) (by norm_num) (by norm_num)) coinQuery := by
  refine ⟨1, one_pos, fun ε h0 h1 _ d _ _ _ a ha => ?_⟩
  cases d
  refine ⟨?_, fun b _ => ?_⟩
  · rw [coinQuery_nu_act]
    exact tremble_fullSupport (procQ (1/2) (by norm_num) (by norm_num)) ε h0 h1 () a
  · rw [coinQuery_condExp_zero, coinQuery_condExp_zero]

/-- **T4(c)'s package inhabited on `coinQuery`**: TS (via FF) and every act event realized
(`ν = ½`) for `procQ ½`; the conclusion `MSRAt` follows through `msrAt_of_ts_of_realized`.
N− as a separation (all payoffs tie), N+ as an inhabitant (mixed label, chance node, every act
realized).
Source: S10 / C2-9′ under SE-18′(b)'s positivity; audit r1 adversarial B1
Kind: N−
Fidelity: exact
Hyps: none -/
theorem coinQuery_msr_realized_instance :
    TS cqObs cqActEv (procQ (1/2) (by norm_num) (by norm_num)) coinQuery ∧
    (∀ a, 0 < nu (procQ (1/2) (by norm_num) (by norm_num)) coinQuery (cqActEv () a ∩ cqObs ())) ∧
    MSRAt cqObs cqActEv (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () := by
  have hts : TS cqObs cqActEv (procQ (1/2) (by norm_num) (by norm_num)) coinQuery :=
    ff_subset_ts _ _ _ _ coinQuery_half_ff
  have hreal : ∀ a, 0 < nu (procQ (1/2) (by norm_num) (by norm_num)) coinQuery
      (cqActEv () a ∩ cqObs ()) := fun a => by
    rw [coinQuery_nu_act]; cases a <;> simp [procQ] <;> norm_num
  exact ⟨hts, hreal, msrAt_of_ts_of_realized _ _ _ _ hts () coinQuery_queried hreal⟩

/-- **T4(c)'s package inhabited on the miniature, N+**: `procQ ⅔` is TS (`miniature_testSeq`,
the non-constant test sequence) with both act events realized (`ν(live = a) = ⅔`,
`ν(live = b) = ⅓`), so `MSRAt` holds at `d` — agreeing with D4's verdict
`miniature_adviceEdt_iff` at `q = ⅔`.
Source: S10 / C2-9′ under SE-18′(b)'s positivity; audit r1 fidelity N2
Kind: N+
Fidelity: exact
Hyps: none -/
theorem miniature_msr_realized_instance :
    TS miniObs miniActEv (procQ (2/3) (by norm_num) (by norm_num)) miniature ∧
    (∀ a, 0 < nu (procQ (2/3) (by norm_num) (by norm_num)) miniature
      (miniActEv () a ∩ miniObs ())) ∧
    MSRAt miniObs miniActEv (procQ (2/3) (by norm_num) (by norm_num)) miniature () := by
  have hreal : ∀ a, 0 < nu (procQ (2/3) (by norm_num) (by norm_num)) miniature
      (miniActEv () a ∩ miniObs ()) := fun a => by
    simp only [miniObs, Finset.inter_univ]
    rw [miniature_nu_live]; cases a <;> simp [procQ] <;> norm_num
  exact ⟨miniature_testSeq, hreal,
    msrAt_of_ts_of_realized _ _ _ _ miniature_testSeq () miniature_queried hreal⟩

/-- **T4(d)'s package inhabited on `coinQuery`**: the strict state of `procQ ½`, recording,
`ν(O) = 1 > 0`, `MSRAt`; the conclusion `MSR¹⁷` (`T_EDT` at the strict state) follows through
`msr17At_of_msrAt_recorded`.
Source: SL-21; C2-9′ ("MSR ⊆ MSR¹⁷"); audit r1 adversarial B1
Kind: N−
Fidelity: exact
Hyps: none -/
theorem coinQuery_msr17_instance :
    StrictOCAt (fun _ => cqStrictState (1/2) (by norm_num) (by norm_num)) cqObs
        (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () ∧
    RecordsFor cqObs cqActEv (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () ∧
    0 < nu (procQ (1/2) (by norm_num) (by norm_num)) coinQuery (cqObs ()) ∧
    MSRAt cqObs cqActEv (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () ∧
    MSR17At cqActEv (procQ (1/2) (by norm_num) (by norm_num))
      (fun _ => cqStrictState (1/2) (by norm_num) (by norm_num)) () := by
  have hs : StrictOCAt (fun _ => cqStrictState (1/2) (by norm_num) (by norm_num)) cqObs
      (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () :=
    fun h => strictClausesAt_calibratedState cqObs _ coinQuery _ () h rfl
  have hrec := coinQuery_recordsFor (procQ (1/2) (by norm_num) (by norm_num))
  have hpos : 0 < nu (procQ (1/2) (by norm_num) (by norm_num)) coinQuery (cqObs ()) := by
    rw [coinQuery_nu_obs]; exact one_pos
  have hmsr := coinQuery_msr_realized_instance.2.2
  exact ⟨hs, hrec, hpos, hmsr, msr17At_of_msrAt_recorded _ _ _ _ _ () hs hrec hpos hmsr⟩

/-- `t1` records at its point for every procedure (one decision node, worlds = acts).
Source: none: infrastructure. Kind: L -/
theorem t1_recordsFor (C : Proc Unit (fun _ => Act2) ℚ) : RecordsFor t1Obs t1ActEv C t1 () := by
  intro ℓ _ _
  unfold t1 at ℓ ⊢
  rcases ℓ with ⟨x, _⟩
  refine ⟨rfl, ?_⟩
  rintro (_ | ⟨b, q⟩) _ a ha
  · simp only [edgeOf_decision_none, Option.some.injEq] at ha
    subst ha
    refine ⟨fun _ _ => by simp [t1Obs], by simp [t1ActEv], fun a' ha' => ?_⟩
    simp [t1ActEv] at ha'
    exact ha'.symm
  · exact q.elim

/-- The strict state of `δ_a` on `t1`. Source: none: infrastructure. Kind: D -/
noncomputable def t1StrictState : State Act2 ℚ :=
  calibratedState procA1 t1 (t1Obs ()) (by show 0 < nu procA1 t1 Finset.univ; exact nu_univ_pos _ _)

/-- The uniform-ray coefficients of `δ_a` at `t1`: the `b`-event has order `1` with
`nuPoly.coeff 1 = ½` and `payPoly.coeff 1 = ½`. Source: none: infrastructure. Kind: L -/
theorem t1_b_coeffs :
    (nuPoly procA1 t1 (t1ActEv () .b ∩ t1Obs ())).coeff 0 = 0 ∧
    (nuPoly procA1 t1 (t1ActEv () .b ∩ t1Obs ())).coeff 1 = 1 / 2 ∧
    (payPoly procA1 t1 (t1ActEv () .b ∩ t1Obs ())).coeff 1 = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPoly_eq_sum, t1_sum]
    simp [t1, leafLawPoly, trembleW, t1ActEv, t1Obs, procA1, act2_card_rat]
  · rw [coeff_one_eq_eval_zero_derivative, nuPoly_eq_sum, t1_sum]
    simp [t1, leafLawPoly, trembleW, t1ActEv, t1Obs, procA1, act2_card_rat]
  · rw [coeff_one_eq_eval_zero_derivative, payPoly_eq_sum, t1_sum]
    simp [t1, leafLawPoly, trembleW, t1ActEv, t1Obs, procA1, act2_card_rat]

/-- **MSR¹⁷ ⊋ MSR on an in-domain (recorded) tree**: on `t1` with `δ_a`, the tree records at `d`
(so `msr17At_of_msrAt_recorded` applies there), `T_EDT` approves `δ_a` at its strict state
(`A_d^+ = {a}`, vacuously), and `MSRAt` fails: the tremble-pinned values are `limitVal b = 1 >
0 = limitVal a` while `supp C(d) = {a}`. The miniature's `miniature_msr17_not_msr` shows only
`MSR¹⁷ ⊄ MSR` there (the miniature is recorded by no procedure).
Source: SL-21 ("approves every deterministic label vacuously"); C2-9′; audit r1 adversarial N4
Kind: N+
Fidelity: exact
Hyps: none -/
theorem t1_msr17_not_msr :
    RecordsFor t1Obs t1ActEv procA1 t1 () ∧
    APlus (fun _ => t1StrictState) t1ActEv () = {.a} ∧
    MSR17At t1ActEv procA1 (fun _ => t1StrictState) () ∧
    ¬ MSRAt t1Obs t1ActEv procA1 t1 () := by
  have hpos : 0 < nu procA1 t1 (t1Obs ()) := by
    show 0 < nu procA1 t1 Finset.univ; exact nu_univ_pos _ _
  have hs : StrictOCAt (fun _ => t1StrictState) t1Obs procA1 t1 () :=
    strictOCAt_calibratedState t1Obs procA1 t1 (fun _ => t1StrictState) () hpos rfl
  obtain ⟨hA, hT⟩ := tEdtAt_of_deterministic_recorded (fun _ => t1StrictState) t1ActEv t1Obs
    procA1 t1 .a rfl (t1_recordsFor procA1) hpos hs
  refine ⟨t1_recordsFor procA1, hA, hT, fun h => ?_⟩
  obtain ⟨b0, b1, bp1⟩ := t1_b_coeffs
  have ha : 0 < (procA1 ()).w .a := by simp [procA1]
  have hbne : nuPoly procA1 t1 (t1ActEv () .b ∩ t1Obs ()) ≠ 0 := fun hz => by
    rw [hz, Polynomial.coeff_zero] at b1; norm_num at b1
  have hle := (h .a ha).2 .b hbne
  have hapos : 0 < nu procA1 t1 (t1ActEv () .a ∩ t1Obs ()) := by
    rw [t1_nu]; simp [t1ActEv, t1Obs, procA1]
  rw [limitVal_of_coeff_one _ _ _ b0 (by rw [b1]; norm_num), bp1, b1,
    limitVal_eq_of_pos _ _ _ hapos] at hle
  unfold condExp at hle
  rw [t1_paySum] at hle
  simp [t1ActEv, t1Obs] at hle
  linarith

end msr

/-! ## T16's invariance inhabited on `chanceTwin` -/

section twin

/-- The `(H, a)` leaf. Source: none: infrastructure. Kind: D -/
def twinHa : chanceTwin.Leaves := ⟨0, .a, ()⟩

/-- The `(T, a)` leaf. Source: none: infrastructure. Kind: D -/
def twinTa : chanceTwin.Leaves := ⟨1, .a, ()⟩

/-- `twinHa`'s world. Source: none: infrastructure. Kind: L -/
theorem twinHa_world : world chanceTwin twinHa = .ha := by simp [twinHa, chanceTwin, twinW]

/-- `twinTa`'s world. Source: none: infrastructure. Kind: L -/
theorem twinTa_world : world chanceTwin twinTa = .ta := by simp [twinTa, chanceTwin, twinW]

/-- `(H, a)` is carried by one leaf. Source: none: infrastructure. Kind: L -/
theorem twin_uniq_ha : ∀ ℓ'' : chanceTwin.Leaves, world chanceTwin ℓ'' = world chanceTwin twinHa →
    ℓ'' = twinHa := by
  rintro ⟨i, x, _⟩ hw
  rw [twinHa_world] at hw
  fin_cases i <;> cases x <;> simp [chanceTwin, twinW] at hw ⊢ <;> rfl

/-- `(T, a)` is carried by one leaf. Source: none: infrastructure. Kind: L -/
theorem twin_uniq_ta : ∀ ℓ'' : chanceTwin.Leaves, world chanceTwin ℓ'' = world chanceTwin twinTa →
    ℓ'' = twinTa := by
  rintro ⟨i, x, _⟩ hw
  rw [twinTa_world] at hw
  fin_cases i <;> cases x <;> simp [chanceTwin, twinW] at hw ⊢ <;> rfl

/-- **The invariance's package is inhabited on `chanceTwin`**: the two `a`-leaves have the same
draws `[(d, a)]`, distinct worlds each carried by one leaf, chance `½ + ½ > 0`, and
`popperLimit_twin_leaves` returns `½` for every `C` — the value `chanceTwin_popperLimitRay`
computes by hand.
Source: mandate T16; audit r1 adversarial B1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem chanceTwin_twin_leaves_instance (C : Proc Unit (fun _ => Act2) ℚ) :
    popperLimit C chanceTwin {TwinW.ha} {TwinW.ha, TwinW.ta} = 1 / 2 := by
  have h := popperLimit_twin_leaves C chanceTwin twinHa twinTa
    (by simp [twinHa, twinTa, chanceTwin, draws])
    (by rw [twinHa_world, twinTa_world]; decide)
    twin_uniq_ha twin_uniq_ta
    (by simp [twinHa, twinTa, chanceTwin, chanceWeight, FinDistr.fair, FinDistr.coin]; try norm_num)
  rw [twinHa_world, twinTa_world] at h
  rw [h]
  simp [twinHa, twinTa, chanceTwin, chanceWeight, FinDistr.fair, FinDistr.coin]
  try norm_num

end twin

/-! ## SE-18′(b)'s Open in the εFP form -/

section epsfp

/-- **The reversal family is ε-floored-fixed-point (εFP) at every `ε ∈ (0, ½]`**:
`tsTr ε := tremble (tsProc ε) ε` satisfies `EpsFP … ε`.
Source: SE-18′(b) Open ("whether a fixed-point family realizes the reversal"); audit r1
adversarial N1
Kind: N+
Fidelity: exact
Hyps: (a) `0 < ε ≤ ½` -/
theorem tsTr_epsFP (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    EpsFP tsObs tsActEv (tremble (tsProc ε h0.le h1) ε h0.le (by linarith)) tsTree ε :=
  (epsFP_tremble_iff_d2At tsObs tsActEv tsTree _ ε h0 (by linarith)).mpr (tsProc_d2At ε h0 h1)

/-- `tsProc ε_n → C₀` pointwise. Source: none: infrastructure. Kind: L -/
theorem tsProc_tendsTo :
    ProcTendsTo (fun n => tsProc (1 / ((n : ℚ) + 2)) (by positivity) (one_div_add_two_le_half n))
      tsC0 := by
  intro p a δ hδ
  obtain ⟨N, hN⟩ := one_div_add_two_tendsto (δ / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hlt := hN n hn
  have hpos : (0 : ℚ) < 1 / ((n : ℚ) + 2) := by positivity
  (cases p <;> cases a <;> simp [tsProc, tsC0, hδ]) <;>
    (rw [abs_of_pos (by positivity)]; rw [one_div] at hlt; linarith)

/-- **The εFP family converges to `C₀`**: `tremble (tsProc ε_n) ε_n → C₀` along `ε_n = 1/(n+2)`.
With `tsTr_epsFP` and `ts_not_msr`, SE-18′(b)'s Open is settled in the form it asks: an
ε-floored fixed-point family realizes the reversal.
Source: SE-18′(b) Open; audit r1 adversarial N1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem tsTr_tendsTo :
    ProcTendsTo (fun n => tremble (tsProc (1 / ((n : ℚ) + 2)) (by positivity)
      (one_div_add_two_le_half n)) (1 / ((n : ℚ) + 2)) (by positivity)
      (by linarith [one_div_add_two_le_half n])) tsC0 := by
  apply tremble_tendsTo _ _ (fun n => ⟨by positivity, by linarith [one_div_add_two_le_half n]⟩)
  · intro δ hδ
    obtain ⟨N, hN⟩ := one_div_add_two_tendsto δ hδ
    exact ⟨N, fun n hn => by rw [sub_zero, abs_of_pos (by positivity)]; exact hN n hn⟩
  · exact tsProc_tendsTo

end epsfp

/-! ## The Definition-15 encoding check: `Σ_{½}` is consistent -/

section sampler

/-- **`Σ_{½}` is strictly consistent** (the encoding check for `sigmaPi_not_consistent`): with
a fair fill coin (`p = ½`) every label `q` has `ν(fill ∧ one) = ½ ν(one)` and
`ν(¬fill ∧ two) = ½ ν(two)`, so the strict state of `procQ q` on `opaqueNewcomb ½` is an
instantiation of `Σ_{½}`. So the impossibility at `π > ½` is not an artifact of an
unsatisfiable encoding.
Source: S11; dp-sl-030; audit r1 fidelity N2
Kind: N+
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem sigmaPi_half_consistent (L S : ℚ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Consistent .strict opaqueObs (sigmaPi L S (1 / 2)) (procQ q hq0 hq1) := by
  have hpos : 0 < nu (procQ q hq0 hq1) (opaqueNewcomb (1/2) (by norm_num) (by norm_num) L S)
      (opaqueObs ()) := by
    show 0 < nu _ _ Finset.univ; exact nu_univ_pos _ _
  obtain ⟨hone, htwo, hfo, hnt⟩ :=
    opaque_masses (1/2) (by norm_num) (by norm_num) L S q hq0 hq1
  refine ⟨⟨opaqueNewcomb (1/2) (by norm_num) (by norm_num) L S,
    fun _ => calibratedState (procQ q hq0 hq1) _ (opaqueObs ()) hpos⟩,
    ⟨⟨1/2, by norm_num, by norm_num, rfl⟩, ?_, ?_⟩, fun d _ => ?_⟩
  · simp only [calibratedState_pr, opaqueObs, Finset.inter_univ, nu_univ, div_one]
    rw [hfo, hone]; ring
  · simp only [calibratedState_pr, opaqueObs, Finset.inter_univ, nu_univ, div_one]
    rw [hnt, htwo]; ring
  · cases d
    exact strictOCAt_calibratedState opaqueObs _ _ _ () hpos rfl

end sampler

end Cleanroom.Decision.DpCalibLimits
