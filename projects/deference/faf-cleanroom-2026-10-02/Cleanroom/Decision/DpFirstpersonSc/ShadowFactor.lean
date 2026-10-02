import Cleanroom.Decision.DpFirstpersonSc.License
import Cleanroom.Decision.DpFirstpersonSc.WitnessesLicense
import Cleanroom.Decision.DpCalibration.Shadow
import Cleanroom.Decision.DpCalibration.ToldYouSo

/-!
# The extension of record: which shadow the audit verdict factors through

The mandate's §5 strengthening of T1 ("the exact set of grades at which audit-pass is decidable
from the run law alone"), made precise as three claims (continuation 2):

* **Positive, strict grade** (`priorState_agree_of_shadow_eq`, `auditPassAt_of_shadow_eq`,
  `audit_stamped_shadow_functional`, `license_stamped_shadow_functional`,
  `perRunClausesAt_stamped_shadow_functional`): the strict-grade verdict — for every evidence
  event, every projection and every audited state — is a functional of the **shadow of the
  stamped problem** `shadow C (stamp U B)`, because the strict prior `priorState C (stamp U B)`
  is (`dp-calibration`'s `condPayoff_eq_of_shadow_eq` on the stamped tree); so are the license
  `License obs C B d` and, through T1(a), the per-run clauses at `d`. The masked-local grade is
  the same statement for `C.deviate d m` (the mask is a parameter of the grade, not of the tree),
  so it needs `m` in addition to the stamped shadow — no separate theorem.
* **Negative, base shadow** (`coverOk`, `coverOk_shadow_eq`, `coverOk_license`,
  `license_not_base_shadow_functional`, `stamped_verdict_not_base_shadow_functional`): `coverFail`
  (T2(b)) and `coverOk` (branch B's leaf moved under a `d`-node) have the **same base shadow**
  under `C = δ_a` (`δ_{((1,a),1)}`) and opposite verdicts: the license holds on `coverOk` and
  fails on `coverFail`; the stamped strict-OC state passes the stamped audit on `coverOk` and
  fails on `coverFail`. The base shadow cannot see which runs consult `d`.
* **Negative, limit grade** (`tys_take5_fiveTen_shadow_eq`, `limitOC_not_shadow_functional`,
  `tys_occ_ten_eq`): on Told-You-So, `procTake5` and `procFiveTen` have the **same strict
  shadow** (`δ_{((5,5),5)}` — neither reaches `d₁₀`), yet Definition 10's limit-grade
  calibration at `d₁₀` holds for `procFiveTen` and fails for `procTake5` (Lemma 2's separation,
  `dp-calibration`'s `tys_take5_strict_not_limit`); and on Told-You-So `occ(d₁₀) = λ⁻¹O₁₀`
  exactly, so the limit-grade *audit* referent at `d₁₀` (`LimitGrade.lean`) is Definition 10's
  limiting conditional on `O₁₀` — the limit grade factors through no strict shadow. The stamped
  shadows of the two procedures agree too (`tys_take5_fiveTen_stamp_shadow_eq`, repair round 2,
  audit r2 fidelity N4): neither reaches `d₁₀`, so their base leaf laws agree leaf by leaf
  (`tys_take5_fiveTen_leafLaw_eq`) and the stamped shadow reads only the base leaf law
  (`shadow_stamp_congr_leafLaw`) — both are `δ_{((5,5), pol = ⊥, 5)}`;
  `limitAudit_not_stamped_shadow_functional` (`LimitGrade.lean`) is the stamped form.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-! ## The positive clause: the strict prior, hence the verdict, is a functional of the shadow -/

section positive

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- **The strict prior is a functional of the shadow**: equal shadows give agreeing prior
states (`P = ν` and `V = 𝔼[r | ·]` are both read off `B̂(C)`, Remark 3.5).
Source: [[decision-problems-v2]] §3.1 Remark 3.5; mandate "Extension of record"
Kind: C
Fidelity: exact
Hyps: (a) `shadow C B = shadow C' B'` -/
theorem priorState_agree_of_shadow_eq {C C' : Proc ι acts K} {B B' : Tree Ω ι acts K}
    (h : shadow C B = shadow C' B') : State.Agree (priorState C B) (priorState C' B') := by
  have hnu : ∀ X, nu C B X = nu C' B' X := fun X => (condPayoff_eq_of_shadow_eq h X).1
  have hpay : ∀ X, paySum C B X = paySum C' B' X := fun X => (condPayoff_eq_of_shadow_eq h X).2
  refine ⟨?_, fun X _ => ?_⟩
  · ext ω
    have h1 := priorState_pr C B {ω}
    have h2 := priorState_pr C' B' {ω}
    simp only [State.pr, probOf_singleton] at h1 h2
    rw [h1, h2, hnu]
  · rw [priorState_V, priorState_V, hnu, hpay]

/-- The audit's guard is a functional of the shadow. Source: none: infrastructure. Kind: L -/
theorem priorState_pr_pos_iff_of_shadow_eq {C C' : Proc ι acts K} {B B' : Tree Ω ι acts K}
    (h : shadow C B = shadow C' B') (E : Finset Ω) :
    0 < (priorState C B).pr E ↔ 0 < (priorState C' B').pr E := by
  rw [priorState_pr, priorState_pr, (condPayoff_eq_of_shadow_eq h E).1]

/-- **The strict-grade verdict is a functional of the shadow of the problem it audits on**: for
equal shadows, every evidence event, every projection and every audited state, the verdicts
agree. Applied to the stamped problem below.
Source: mandate "Extension of record" ("the strict-grade audit verdict factors through the
shadow of the stamped problem")
Kind: C
Fidelity: exact
Hyps: (a) `shadow C B = shadow C' B'`, (a) the two guards -/
theorem auditPassAt_of_shadow_eq {W : Type} [Fintype W] [DecidableEq W]
    {C C' : Proc ι acts K} {B B' : Tree W ι acts K} (h : shadow C B = shadow C' B')
    (E : Finset W) (hE : 0 < (priorState C B).pr E) (hE' : 0 < (priorState C' B').pr E)
    (π : W → Ω) (s : State Ω K) :
    AuditPassAt (priorState C B) E hE π s ↔ AuditPassAt (priorState C' B') E hE' π s :=
  auditPassAt_congr_prior (priorState_agree_of_shadow_eq h) E hE hE' π s

variable (U : Finset ι) {d : ι} (hd : d ∈ U)

/-- **The strict-grade audit factors through the stamped shadow** (the extension of record,
positive clause): two problems with the same stamped shadow `shadow C (stamp U B)` — the joint
law of `(λ, pol, r)` — give the same verdict at `d` for every audited base state `s` (and every
projection `π`).
Source: mandate "Extension of record"
Kind: C
Fidelity: exact (stamped algebra; strict grade; the masked-local grade is the same statement
for `C.deviate d m`)
Hyps: (a) `shadow C (stamp U B) = shadow C' (stamp U B')`, (a) the two guards -/
theorem audit_stamped_shadow_functional {C C' : Proc ι acts K} {B B' : Tree Ω ι acts K}
    (h : shadow C (stamp U B) = shadow C' (stamp U B'))
    (hE : 0 < (priorState C (stamp U B)).pr (occW U hd))
    (hE' : 0 < (priorState C' (stamp U B')).pr (occW U hd)) (π : SW Ω acts U → Ω)
    (s : State Ω K) :
    AuditPassAt (priorState C (stamp U B)) (occW U hd) hE π s ↔
      AuditPassAt (priorState C' (stamp U B')) (occW U hd) hE' π s :=
  auditPassAt_of_shadow_eq h (occW U hd) hE hE' π s

include hd in
/-- **The license factors through the stamped shadow**: `μ(occ(d) ∖ λ⁻¹O_d)` and
`μ(λ⁻¹O_d ∖ occ(d))` are masses of world events of the stamped problem.
Source: mandate "Extension of record"; `firstperson.md` FP-22′
Kind: C
Fidelity: exact
Hyps: (a) `shadow C (stamp U B) = shadow C' (stamp U B')` -/
theorem license_stamped_shadow_functional {C C' : Proc ι acts K} {B B' : Tree Ω ι acts K}
    (h : shadow C (stamp U B) = shadow C' (stamp U B')) (obs : ι → Finset Ω) :
    License obs C B d ↔ License obs C' B' d := by
  unfold License VeridicalASAt CoversAS
  rw [← nu_stamp_occW_sdiff_obsW U C B hd, ← nu_stamp_obsW_sdiff_occW U C B hd,
    ← nu_stamp_occW_sdiff_obsW U C' B' hd, ← nu_stamp_obsW_sdiff_occW U C' B' hd,
    (condPayoff_eq_of_shadow_eq h _).1, (condPayoff_eq_of_shadow_eq h _).1]

/-- **The per-run clauses at `d` factor through the stamped shadow** (through T1(a)): per-run
SSC at `d` — unlike strict OC — is not a functional of the base shadow
(`dp-calibration`'s `perRunSSC_not_shadow_functional`) but is one of the stamped shadow.
Source: mandate "Extension of record"; [[decision-problems-v2]] §3.1 Remark 3.5 ("SSC … does
not")
Kind: C
Fidelity: exact
Hyps: (a) `shadow C (stamp U B) = shadow C' (stamp U B')`, (a) `0 < μ(occ(d))` on both -/
theorem perRunClausesAt_stamped_shadow_functional {C C' : Proc ι acts K} {B B' : Tree Ω ι acts K}
    (h : shadow C (stamp U B) = shadow C' (stamp U B'))
    (hE : 0 < (priorState C (stamp U B)).pr (occW U hd))
    (hE' : 0 < (priorState C' (stamp U B')).pr (occW U hd)) (s : ι → State Ω K) :
    PerRunClausesAt s C B d ↔ PerRunClausesAt s C' B' d := by
  rw [← audit_iff_perRunClausesAt C B U hd s hE, ← audit_iff_perRunClausesAt C' B' U hd s hE']
  exact audit_stamped_shadow_functional U hd h hE hE' Prod.fst (s d)

/-- **Equal leaf laws give equal shadows** on one tree: the shadow reads the leaf law only.
Source: none: infrastructure. Kind: L -/
theorem shadow_congr_leafLaw {C C' : Proc ι acts K} (B : Tree Ω ι acts K)
    (h : ∀ ℓ, leafLaw C B ℓ = leafLaw C' B ℓ) : shadow C B = shadow C' B := by
  funext x
  unfold shadow
  exact Finset.sum_congr rfl fun ℓ _ => by rw [h ℓ]

/-- **Equal base leaf laws give equal stamped shadows**: the stamped problem's leaf law is the
base leaf law at the relabelled leaf (`leafLaw_stamp`), so two procedures with the same leaf law
on `B` have the same shadow on `stamp U B` — the `shadow_stamp` transport the handoff asked for,
in the form the Told-You-So cell needs.
Source: none: infrastructure (repair round 2, audit r2 fidelity N4). Kind: L -/
theorem shadow_stamp_congr_leafLaw {C C' : Proc ι acts K} (U : Finset ι) (B : Tree Ω ι acts K)
    (h : ∀ ℓ, leafLaw C B ℓ = leafLaw C' B ℓ) :
    shadow C (stamp U B) = shadow C' (stamp U B) :=
  shadow_congr_leafLaw (stamp U B) fun ℓ' => by rw [leafLaw_stamp, leafLaw_stamp, h]

end positive

/-! ## Negative, base shadow: `coverFail` against `coverOk` -/

section coverOk

/-- **The coverage tree**: `coverFail` with branch B's leaf moved under a `d`-node — fair coin,
both branches query `d`, `a ↦ (1,a)` with `r = 1`, `b ↦ (1,b)` with `r = 0`. Under `C = δ_a` its
base shadow is `coverFail`'s (`δ_{((1,a),1)}`), and coverage holds.
Source: mandate "Extension of record" ("a tree with the same base shadow and coverage");
`dp-firstperson-sc-handoff` ("move branch B's leaf under a `d`-node")
Kind: D -/
def coverOk : Tree CfW CfPt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun _ => .decision .d fun act =>
    .leaf (true, act) (if act = .b then 0 else 1)

/-- Leaf sums on `coverOk`. Source: none: infrastructure. Kind: L -/
theorem coverOk_sum {M : Type} [AddCommMonoid M] (f : coverOk.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold coverOk at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The leaf law on `coverOk`. Source: none: infrastructure. Kind: L -/
theorem coverOk_leafLaw (C : Proc CfPt (fun _ => Act2) ℚ) (i : Fin 2) (act : Act2) :
    leafLaw C coverOk ⟨i, act, ()⟩ = FinDistr.fair.w i * ((C .d).w act * 1) := by
  unfold coverOk
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf]

/-- The world at a leaf of `coverOk`. Source: none: infrastructure. Kind: L -/
theorem coverOk_world (i : Fin 2) (act : Act2) :
    world coverOk ⟨i, act, ()⟩ = (true, act) := by
  unfold coverOk; simp [world_chance, world_decision, world_leaf]

/-- The payoff at a leaf of `coverOk`. Source: none: infrastructure. Kind: L -/
theorem coverOk_payoff (i : Fin 2) (act : Act2) :
    payoff coverOk ⟨i, act, ()⟩ = if act = .b then 0 else 1 := by
  unfold coverOk; simp [payoff_chance, payoff_decision, payoff_leaf]

/-- `#_d = 1` on every run of `coverOk`. Source: none: infrastructure. Kind: L -/
theorem coverOk_count_d (i : Fin 2) (act : Act2) : count .d coverOk ⟨i, act, ()⟩ = 1 := by
  unfold coverOk
  simp only [count_chance, count_decision, count_leaf]
  simp

/-- **Same base shadow**: under `δ_a`, `coverOk` and `coverFail` both have shadow
`δ_{((1,a),1)}`.
Source: mandate "Extension of record" ("same base shadow under two trees")
Kind: N+
Fidelity: exact -/
theorem coverOk_shadow_eq : shadow cfProcA coverOk = shadow cfProcA coverFail := by
  funext x
  unfold shadow
  rw [coverOk_sum, coverFail_sum]
  simp only [coverOk_world, coverOk_leafLaw, coverOk_payoff, coverFail_world, coverFail_leafLaw,
    coverFail_payoff, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin]

/-- **The license holds on `coverOk`**: every run consults `d` and every leaf-world is in
`O_d`.
Source: mandate "Extension of record" ("and coverage")
Kind: N+ -/
theorem coverOk_license : License cfObs cfProcA coverOk .d := by
  unfold License VeridicalASAt CoversAS
  constructor <;>
  · rw [mass_eq_zero_iff]
    intro ℓ hℓ
    exfalso
    rcases ℓ with ⟨i, act, ⟨⟩⟩
    simp only [Finset.mem_sdiff, mem_occ, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
      coverOk_world, coverOk_count_d, cfObs] at hℓ
    simp at hℓ

/-- **The license does not factor through the base shadow** (the extension of record, first
negative clause): `coverOk` and `coverFail` have the same base shadow under `δ_a`, the license
holds on the first and fails on the second. By `license_stamped_shadow_functional` their
stamped shadows must differ — and they do: the base shadow cannot see which runs consult `d`.
Source: mandate "Extension of record" ("not through the shadow of the base problem")
Kind: N+
Fidelity: exact -/
theorem license_not_base_shadow_functional :
    shadow cfProcA coverOk = shadow cfProcA coverFail ∧
      License cfObs cfProcA coverOk .d ∧ ¬ License cfObs cfProcA coverFail .d :=
  ⟨coverOk_shadow_eq, coverOk_license, coverFail_license_fails⟩

/-- **The stamped strict-OC state passes the stamped audit on `coverOk`** (T2(a) applied to
`coverOk_license`). Source: mandate "Extension of record". Kind: N+ -/
theorem coverOk_stamped_passes
    (hO : 0 < nu cfProcA (stamp {CfPt.d} coverOk) (obsW {CfPt.d} (cfObs .d)))
    (h : 0 < (priorState cfProcA (stamp {CfPt.d} coverOk)).pr
      (occW {CfPt.d} (Finset.mem_singleton_self _))) :
    AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverOk))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) h id
      (calibratedState cfProcA (stamp {CfPt.d} coverOk) (obsW {CfPt.d} (cfObs .d)) hO) := by
  rw [audit_license_iff_nullDiff]
  exact coverOk_license

/-- **The stamped strict-grade verdict on the strict-OC state does not factor through the base
shadow**: same base shadow, the stamped strict-OC state passes on `coverOk`
(`coverOk_stamped_passes`) and fails on `coverFail` (`coverFail_stamped_fails`).
Source: mandate "Extension of record" ("same base shadow under two trees, different verdicts")
Kind: N+
Fidelity: exact (strict grade) -/
theorem stamped_verdict_not_base_shadow_functional
    (hO : 0 < nu cfProcA (stamp {CfPt.d} coverOk) (obsW {CfPt.d} (cfObs .d)))
    (h : 0 < (priorState cfProcA (stamp {CfPt.d} coverOk)).pr
      (occW {CfPt.d} (Finset.mem_singleton_self _)))
    (hO' : 0 < nu cfProcA (stamp {CfPt.d} coverFail) (obsW {CfPt.d} (cfObs .d)))
    (h' : 0 < (priorState cfProcA (stamp {CfPt.d} coverFail)).pr
      (occW {CfPt.d} (Finset.mem_singleton_self _))) :
    shadow cfProcA coverOk = shadow cfProcA coverFail ∧
    AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverOk))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) h id
      (calibratedState cfProcA (stamp {CfPt.d} coverOk) (obsW {CfPt.d} (cfObs .d)) hO) ∧
    ¬ AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverFail))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) h' id
      (calibratedState cfProcA (stamp {CfPt.d} coverFail) (obsW {CfPt.d} (cfObs .d)) hO') :=
  ⟨coverOk_shadow_eq, coverOk_stamped_passes hO h, coverFail_stamped_fails hO' h'⟩

/-- `μ(occ(d)) = 1` on `coverOk` under `δ_a` (every run consults `d`).
Source: none: infrastructure. Kind: L -/
theorem coverOk_occ_pos : 0 < Tree.mass cfProcA coverOk (occ .d coverOk) := by
  rw [Cleanroom.Decision.DpFirstpersonSc.mass_eq_sum_ite', coverOk_sum]
  simp only [mem_occ, coverOk_count_d, coverOk_leafLaw]
  simp [Fin.sum_univ_two, Act2.sum_univ, cfProcA, FinDistr.fair, FinDistr.coin]

/-- The `coverOk` occurrence guard on the stamped prior. Source: none: infrastructure. Kind: L -/
theorem coverOk_stamp_occ_pos :
    0 < (priorState cfProcA (stamp {CfPt.d} coverOk)).pr
      (occW {CfPt.d} (Finset.mem_singleton_self _)) := by
  rw [priorState_stamp_pr_occW]; exact coverOk_occ_pos

/-- `ν(O_d) = 1` on `coverOk` under `δ_a`. Source: none: infrastructure. Kind: L -/
theorem coverOk_nu_obs_pos : 0 < nu cfProcA coverOk (cfObs .d) := by
  rw [nu_eq_sum, coverOk_sum]
  simp only [coverOk_world, coverOk_leafLaw]
  simp [Fin.sum_univ_two, cfProcA, FinDistr.fair, FinDistr.coin, cfObs]

/-- The `coverOk` observation guard on the stamped problem. Source: none: infrastructure.
Kind: L -/
theorem coverOk_stamp_nu_obs_pos :
    0 < nu cfProcA (stamp {CfPt.d} coverOk) (obsW {CfPt.d} (cfObs .d)) := by
  rw [nu_stamp_obsW {CfPt.d} cfProcA coverOk (cfObs .d)]; exact coverOk_nu_obs_pos

/-- **The stamped strict-OC state passes on `coverOk`, no guard left open.**
Source: mandate "Extension of record"; audit r1 adversarial N3. Kind: N+ -/
theorem coverOk_stamped_passes' :
    AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverOk))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) coverOk_stamp_occ_pos id
      (calibratedState cfProcA (stamp {CfPt.d} coverOk) (obsW {CfPt.d} (cfObs .d))
        coverOk_stamp_nu_obs_pos) :=
  coverOk_stamped_passes _ _

/-- **The base-shadow negative of the extension of record with every guard discharged**: same
base shadow, the stamped strict-OC state passes the stamped audit on `coverOk` and fails it on
`coverFail`.
Source: mandate "Extension of record"; audit r1 adversarial N3
Kind: N+
Fidelity: exact (strict grade) -/
theorem stamped_verdict_not_base_shadow_functional' :
    shadow cfProcA coverOk = shadow cfProcA coverFail ∧
    AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverOk))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) coverOk_stamp_occ_pos id
      (calibratedState cfProcA (stamp {CfPt.d} coverOk) (obsW {CfPt.d} (cfObs .d))
        coverOk_stamp_nu_obs_pos) ∧
    ¬ AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverFail))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) coverFail_stamp_occ_pos id
      (calibratedState cfProcA (stamp {CfPt.d} coverFail) (obsW {CfPt.d} (cfObs .d))
        coverFail_stamp_nu_obs_pos) :=
  stamped_verdict_not_base_shadow_functional coverOk_stamp_nu_obs_pos coverOk_stamp_occ_pos
    coverFail_stamp_nu_obs_pos coverFail_stamp_occ_pos

end coverOk

/-! ## Negative, limit grade: Told-You-So -/

section tys

/-- **Same strict shadow**: `procTake5` and `procFiveTen` never reach `d₁₀`, so both have shadow
`δ_{((5,5),5)}` on Told-You-So.
Source: mandate "Extension of record" ("two procedures with equal strict shadows")
Kind: N+
Fidelity: exact -/
theorem tys_take5_fiveTen_shadow_eq : shadow procTake5 toldYouSo = shadow procFiveTen toldYouSo := by
  funext x
  unfold shadow
  rw [tys_sum, tys_sum]
  simp [toldYouSo, leafLaw_decision, world_decision, payoff_decision, procTake5, procFiveTen]

/-- **`occ(d₁₀) = λ⁻¹O₁₀` on Told-You-So** (exactly, for every `C`): the limit-grade audit
referent at `d₁₀` is Definition 10's limiting conditional on `O₁₀`, so `LimitOCAt … .ten` is the
limit-grade audit verdict at `d₁₀`. Source: none: infrastructure. Kind: L -/
theorem tys_occ_ten_eq : occ .ten toldYouSo = worldEv toldYouSo (tysObs .ten) := by
  ext ℓ
  unfold toldYouSo at ℓ ⊢
  rcases ℓ with ⟨a, ℓ⟩
  cases a
  · simp [mem_occ, count_decision, worldEv, world_decision, tysObs]
  · rcases ℓ with ⟨b, ℓ⟩
    cases b <;> simp [mem_occ, count_decision, worldEv, world_decision, tysObs]

/-- **The limit grade factors through no strict shadow** (the extension of record, second
negative clause): `procTake5` and `procFiveTen` have the same strict shadow on Told-You-So, yet
Definition 10's limit calibration at `d₁₀` holds for `procFiveTen` (the limiting conditional is
`δ_{(10,10)} = P_{s₁₀}`) and fails for `procTake5` (it is `δ_{(10,5)}`) — Lemma 2's separation.
Since `occ(d₁₀) = λ⁻¹O₁₀` on Told-You-So (`tys_occ_ten_eq`), this is the limit-grade *audit*
verdict at `d₁₀` (`LimitGrade.lean`, `limitAudit_iff_limitOCAt_of_occ_eq`).
Source: mandate "Extension of record" ("neither limit grade factors through any shadow");
[[decision-problems-v2]] §3.1 Lemma 2
Kind: N+
Fidelity: exact -/
theorem limitOC_not_shadow_functional :
    shadow procTake5 toldYouSo = shadow procFiveTen toldYouSo ∧
    LimitOCAt tysState tysObs procFiveTen toldYouSo .ten ∧
    ¬ LimitOCAt tysState tysObs procTake5 toldYouSo .ten :=
  ⟨tys_take5_fiveTen_shadow_eq, tys_fiveTen_limitOC .ten (tys_queried .ten),
    tys_take5_strict_not_limit.2⟩

/-- **`procTake5` and `procFiveTen` have the same leaf law on Told-You-So**: both take `five` at
`d₅` with weight `1`, so the `(5,5)` leaf has law `1` and the two leaves under `d₁₀` have law `0`
under either (they differ only at `d₁₀`, which neither reaches).
Source: none: infrastructure (repair round 2). Kind: L -/
theorem tys_take5_fiveTen_leafLaw_eq (ℓ : toldYouSo.Leaves) :
    leafLaw procTake5 toldYouSo ℓ = leafLaw procFiveTen toldYouSo ℓ := by
  unfold toldYouSo at ℓ ⊢
  rcases ℓ with ⟨a, ℓ⟩
  cases a
  · simp [leafLaw_decision, procTake5, procFiveTen]
  · rcases ℓ with ⟨b, ℓ⟩
    cases b <;> simp [leafLaw_decision, procTake5, procFiveTen]

set_option maxHeartbeats 1000000 in
/-- **Same stamped strict shadow** (the half of the limit-grade negative that round 0 left to
prose; audit r2 fidelity N4): on the stamped Told-You-So `stamp {d₁₀} toldYouSo`, `procTake5`
and `procFiveTen` have the same shadow — both `δ_{((5,5), pol = ⊥, 5)}` — because their base
leaf laws agree leaf by leaf and the stamped shadow reads only the base leaf law. A structural
identity (the leaf laws agree), hence L; the N+ is `limitAudit_not_stamped_shadow_functional`
(`LimitGrade.lean`), which pairs it with the opposite limit-audit verdicts.
Source: mandate "Extension of record" ("neither limit grade factors through any shadow"); audit
r2 fidelity N4
Kind: L
Fidelity: exact -/
theorem tys_take5_fiveTen_stamp_shadow_eq :
    shadow procTake5 (stamp {Five10.ten} toldYouSo) =
      shadow procFiveTen (stamp {Five10.ten} toldYouSo) :=
  shadow_stamp_congr_leafLaw {Five10.ten} toldYouSo tys_take5_fiveTen_leafLaw_eq

end tys

end Cleanroom.Decision.DpFirstpersonSc
