import Cleanroom.Decision.DpFirstpersonSc.Audit
import Cleanroom.Decision.DpCalibration.ToldYouSo
import Cleanroom.Decision.DpCalibration.Mugging

/-!
# Witnesses for T1: the audit on `B₁` and Told-You-So (FP-21′)

* **`B₁` (Counterfactual Mugging), self-model `procQ q₀`, `0 < q₀ < 1`, strict grade
  `s₀ = priorState`** (`mug1_auditRef`, `mug1_tailsCertain_fails_audit`, `mug1SscState_passes`,
  `mug1_obsAudit_no_bite`): the referent is `ν = (q₀/2, (1−q₀)/2, q₀/2, (1−q₀)/2)` on
  `(T,pay), (T,refuse), (H,⊥,1), (H,⊥,0)` (`occ(d) = ⊤`); the tails-certain strict-OC state
  `mugState1` (Proposition 6's state, `P(T) = 1`) **fails** the audit (clause 1 at `O_T`: `1 ≠ ½`);
  the per-run SSC state `mug1SscState` passes; the observation-conditioned audit's referent is
  `mugState1` itself — no bite. N+: a non-constant chance, a mixed self-model, both actions
  live.
* **Told-You-So, FP-21′(iv)** (`tys_five_strictOCAt_of_pos`, `tys_five_fails_audit_uniform`,
  `tys_take10_not_zeroRespecting`): `s₅ = δ_{(5,5)}` is strictly observation-calibrated at `d₅`
  under every procedure with `C(d₅)(5) > 0` (every full-support `C`), yet fails the audit under
  the uniform self-model (`ŝ = (½, ¼, ¼)` on `(5,5), (10,10), (10,5)`); and the override
  (take 10 at `d₅`) is not zero-respecting for the stipulated states — the audit is deliberately
  not zero-respecting.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-! ## `B₁` -/

section mug

variable (x y q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1)

/-- On `B₁`, `{λ ⊨ X} ∩ occ(d) = {λ ⊨ X}` (`occ(d) = ⊤`). Source: none: infrastructure. Kind: L -/
theorem mug1_occEv (X : Finset MugW) : occEv (mug1 x y) () X = worldEv (mug1 x y) X := by
  unfold occEv; rw [mug1_occ, Finset.inter_univ]

/-- **The audit's referent on `B₁`** at the strict grade with self-model `procQ q₀`: `ν` itself —
`(q₀/2, (1−q₀)/2, q₀/2, (1−q₀)/2)` on `(T,pay), (T,refuse), (H,⊥,1), (H,⊥,0)`.
Source: `firstperson.md` FP-21′ ("`λ_*P_{s₀}(· | occ(d)) = (q₀/2, (1−q₀)/2, (1−q₀)/2, q₀/2)`")
Kind: N+
Fidelity: exact (the four atoms in `MugW`'s order; FP-21′ lists the two heads worlds in the
reverse order, `(H,⊥,0)` before `(H,⊥,1)`, which is why its tuple reads `(…, (1−q₀)/2, q₀/2)`
where this one reads `(…, q₀/2, (1−q₀)/2)`) -/
theorem mug1_auditRef :
    (occState (procQ q₀ h0.le h1.le) (mug1 x y) () (mug1_occ_pos x y q₀ h0 h1)).P.w .tPay = q₀ / 2 ∧
    (occState (procQ q₀ h0.le h1.le) (mug1 x y) () (mug1_occ_pos x y q₀ h0 h1)).P.w .tRefuse =
      (1 - q₀) / 2 ∧
    (occState (procQ q₀ h0.le h1.le) (mug1 x y) () (mug1_occ_pos x y q₀ h0 h1)).P.w .hOne = q₀ / 2 ∧
    (occState (procQ q₀ h0.le h1.le) (mug1 x y) () (mug1_occ_pos x y q₀ h0 h1)).P.w .hZero =
      (1 - q₀) / 2 := by
  have hw : ∀ ω, (occState (procQ q₀ h0.le h1.le) (mug1 x y) () (mug1_occ_pos x y q₀ h0 h1)).P.w ω =
      nu (procQ q₀ h0.le h1.le) (mug1 x y) {ω} := by
    intro ω
    show mass _ _ (occEv (mug1 x y) () {ω}) / mass _ _ (occ () (mug1 x y)) = _
    rw [mug1_occEv, mug1_occ, mass_univ, div_one]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hw, mug1_nu, procQ] <;> ring

/-- **The tails-certain strict-OC state fails the audit on `B₁`** (per-run clause 1 fails at
`X = O_T`: `P(T) = 1` against `ν(T) = ½`), for every self-model `procQ q₀`.
Source: `firstperson.md` FP-21′ ("the tails-certain OC state fails")
Kind: N+
Fidelity: exact -/
theorem mug1_tailsCertain_not_perRun :
    ¬ PerRunClausesAt (fun _ => mugState1 x y q₀ h0.le h1.le) (procQ q₀ h0.le h1.le) (mug1 x y) () := by
  rintro ⟨hc1, -⟩
  have := hc1 (mugObs ())
  rw [mug1_occ, mass_univ, mul_one, Finset.inter_univ] at this
  simp only at this
  rw [(mugState1_beliefs x y q₀ h0.le h1.le).1] at this
  have hν : nu (procQ q₀ h0.le h1.le) (mug1 x y) (mugObs ()) = 1 / 2 := mug1_nu_obs x y _
  unfold nu at hν
  rw [hν] at this
  norm_num at this

/-- The audit verdict on `B₁`: the tails-certain state **fails** (via T1(a)).
Source: `firstperson.md` FP-21′
Kind: N+ -/
theorem mug1_tailsCertain_fails_audit
    (h : 0 < (priorState (procQ q₀ h0.le h1.le) (stamp {()} (mug1 x y))).pr
      (occW {()} (Finset.mem_singleton_self ()))) :
    ¬ AuditPassAt (priorState (procQ q₀ h0.le h1.le) (stamp {()} (mug1 x y)))
      (occW {()} (Finset.mem_singleton_self ())) h Prod.fst (mugState1 x y q₀ h0.le h1.le) := by
  rw [audit_iff_perRunClausesAt (procQ q₀ h0.le h1.le) (mug1 x y) {()}
    (Finset.mem_singleton_self ()) (fun _ => mugState1 x y q₀ h0.le h1.le) h]
  exact mug1_tailsCertain_not_perRun x y q₀ h0 h1

/-- The `B₁` occurrence guard on the stamped prior (`occ = ⊤`, mass `1`).
Source: none: infrastructure. Kind: L -/
theorem mug1_stamp_occ_pos :
    0 < (priorState (procQ q₀ h0.le h1.le) (stamp {()} (mug1 x y))).pr
      (occW {()} (Finset.mem_singleton_self ())) := by
  rw [priorState_stamp_pr_occW]; exact mug1_occ_pos x y q₀ h0 h1

/-- **T1's N+ witness with no guard left open**: the tails-certain state fails the audit on `B₁`.
Source: `firstperson.md` FP-21′; audit r1 adversarial N3
Kind: N+
Fidelity: exact -/
theorem mug1_tailsCertain_fails_audit' :
    ¬ AuditPassAt (priorState (procQ q₀ h0.le h1.le) (stamp {()} (mug1 x y)))
      (occW {()} (Finset.mem_singleton_self ())) (mug1_stamp_occ_pos x y q₀ h0 h1) Prod.fst
      (mugState1 x y q₀ h0.le h1.le) :=
  mug1_tailsCertain_fails_audit x y q₀ h0 h1 _

/-- **The referent on `B₁` is the prior state** (`occ(d) = ⊤`): the per-run state agrees with
`priorState (procQ q₀) (mug1 x y)` as a state, so T8's three conditions, stated against the prior
state's `P` (`WitnessesLift.lean`), are literally about the audit's referent.
Source: `anticipation.md` AN-11; audit r1 fidelity N4
Kind: L -/
theorem mug1_occState_agree_priorState :
    State.Agree (occState (procQ q₀ h0.le h1.le) (mug1 x y) () (mug1_occ_pos x y q₀ h0 h1))
      (priorState (procQ q₀ h0.le h1.le) (mug1 x y)) :=
  occState_agree_priorState_of_occ_univ _ _ _ (mug1_occ x y) _

/-- **The per-run SSC state passes** (it is the referent: `mug1SscState` is `occState`; a sanity
cell — `State.Agree.refl` through T1(a), Kind T, not an N+).
Source: `firstperson.md` FP-21′ ("the per-run SSC state passes")
Kind: T -/
theorem mug1SscState_passes :
    PerRunClausesAt (fun _ => mug1SscState x y q₀ h0 h1) (procQ q₀ h0.le h1.le) (mug1 x y) () :=
  (agree_occState_iff_perRunClausesAt _ _ _ () (mug1_occ_pos x y q₀ h0 h1)).mp
    (State.Agree.refl _)

/-- `B₁` covers `d` (`occ(d) = ⊤`). Source: none: infrastructure. Kind: L -/
theorem mug1_covers (C : Proc Unit (fun _ => Act2) ℚ) : Covers mugObs C (mug1 x y) () := by
  intro ℓ _ _
  have := mug1_occ x y
  rw [Finset.ext_iff] at this
  exact (mem_occ () (mug1 x y) ℓ).mp ((this ℓ).mpr (Finset.mem_univ ℓ))

/-- **The observation-conditioned audit has no bite on `B₁`**: its referent (evidence
`occ(d) ∧ O_T`) is the tails-certain strict-OC state `mugState1` itself.
Source: `firstperson.md` FP-21′ ("`λ_*P_{s₀}(· | occ ∧ O_T)` equals the strict-OC state")
Kind: N+ -/
theorem mug1_obsAudit_no_bite (E : Finset (SW MugW (fun _ => Act2) {()}))
    (hE : E = obsW (acts := fun _ => Act2) {()} (mugObs ()) ∩ occW {()} (Finset.mem_singleton_self ()))
    (h : 0 < (priorState (procQ q₀ h0.le h1.le) (stamp {()} (mug1 x y))).pr E) :
    State.Agree
      (pushState Prod.fst (auditRef (priorState (procQ q₀ h0.le h1.le) (stamp {()} (mug1 x y))) E h))
      (mugState1 x y q₀ h0.le h1.le) := by
  subst hE
  exact obsAudit_ref_agree_calibratedState (procQ q₀ h0.le h1.le) (mug1 x y) {()}
    (Finset.mem_singleton_self ()) mugObs (mug1_covers x y _) (by rw [mug1_nu_obs]; norm_num) h

/-- The `B₁` evidence guard of the observation-conditioned audit: `ν'(O_T ∧ occ) = ν(O_T) = ½` —
so `mug1_obsAudit_no_bite`'s hypothesis package is inhabited. (Its closed form, with the event
written out in place of the variable `E`, does not elaborate at the concrete stamped carrier —
the package's `whnf` limit, report §Elaboration notes — which is why `mug1_obsAudit_no_bite`
takes `E` with `hE : E = …`.)
Source: none: infrastructure (audit r1 adversarial N3). Kind: L -/
theorem mug1_stamp_obs_occ_pos :
    0 < (priorState (procQ q₀ h0.le h1.le) (stamp {()} (mug1 x y))).pr
      (obsW (acts := fun _ => Act2) {()} (mugObs ()) ∩ occW {()} (Finset.mem_singleton_self ())) := by
  have key := nu_stamp_obsW_inter_occW {()} (procQ q₀ h0.le h1.le) (mug1 x y)
    (Finset.mem_singleton_self ()) (mugObs ())
  rw [priorState_pr]
  refine lt_of_lt_of_eq ?_ key.symm
  rw [mug1_occEv]
  show 0 < nu (procQ q₀ h0.le h1.le) (mug1 x y) (mugObs ())
  rw [mug1_nu_obs]; norm_num

end mug

/-! ## Told-You-So -/

section tys

/-- `occ(d₅)` is every run (the root carries `d₅`). Source: none: infrastructure. Kind: L -/
theorem tys_occ_five : occ .five toldYouSo = Finset.univ := by
  ext ℓ
  unfold toldYouSo at ℓ ⊢
  rcases ℓ with ⟨a, ℓ⟩
  simp [count_decision]

/-- **FP-21′(iv), the calibration half**: `s₅ = δ_{(5,5)}` (desirability `5`) is strictly
observation-calibrated at `d₅` under every procedure with `C(d₅)(5) > 0` — in particular every
full-support `C`: `ν(· | O₅) = δ_{(5,5)}` and `𝔼[r | (5,5)] = 5`.
Source: `firstperson.md` FP-21′(iv) ("`d₅`'s `δ_{(5,5)}` is strict-OC-calibrated under every
full-support `C`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < C(d₅)(5)` -/
theorem tys_five_strictOCAt_of_pos (C : Proc Five10 (fun _ => Five10) ℚ)
    (h : 0 < (C .five).w .five) : StrictOCAt tysState tysObs C toldYouSo .five := by
  intro _
  have hO : ∀ X : Finset TysW, nu C toldYouSo (X ∩ tysObs .five) =
      if (Five10.five, Five10.five) ∈ X then (C .five).w .five else 0 := by
    intro X
    rw [tys_nu]
    simp [tysObs]
  have hP : ∀ X : Finset TysW, paySum C toldYouSo (X ∩ tysObs .five) =
      if (Five10.five, Five10.five) ∈ X then (C .five).w .five * 5 else 0 := by
    intro X
    rw [tys_paySum]
    simp [tysObs]
  have hO5 : nu C toldYouSo (tysObs .five) = (C .five).w .five := by
    have := hO Finset.univ
    rwa [Finset.univ_inter, if_pos (Finset.mem_univ _)] at this
  refine ⟨fun X => ?_, fun X _ _ => ?_⟩
  · rw [hO5, hO]
    simp only [tysState, State.dirac_pr]
    split_ifs <;> simp
  · rw [hO, hP]
    simp only [tysState, State.dirac_V, Five10.val]
    split_ifs <;> ring

/-- The uniform self-model on Told-You-So. Source: `firstperson.md` FP-21′(iv) ("under the
uniform self-model"). Kind: D -/
def tysUniform : Proc Five10 (fun _ => Five10) ℚ := fun _ => FinDistr.uniform

/-- **FP-21′(iv), the audit half**: under the uniform self-model `s₅ = δ_{(5,5)}` fails per-run
clause 1 at `d₅` (`occ(d₅) = ⊤`, so the referent is `ν = (½, ¼, ¼)`; clause 1 at `{(5,5)}`:
`1 ≠ ½`) — hence fails the audit (T1(a)). With `tys_five_strictOCAt_of_pos`: strict OC does not
imply audit-pass; the audit is deliberately not zero-respecting.
Source: `firstperson.md` FP-21′(iv) ("yet fails the audit (`ŝ = (½, ¼, ¼)`)")
Kind: N+
Fidelity: exact -/
theorem tys_five_fails_audit_uniform :
    ¬ PerRunClause1At tysState tysUniform toldYouSo .five := by
  intro hc
  have := hc {(Five10.five, Five10.five)}
  rw [tys_occ_five, mass_univ, mul_one, Finset.inter_univ] at this
  change (tysState .five).pr _ = nu tysUniform toldYouSo _ at this
  rw [tys_nu] at this
  simp [tysState, State.dirac, State.ofConst, FinDistr.pure_w, tysUniform, FinDistr.uniform_w,
    five10_card] at this

/-- The Told-You-So occurrence guard at `d₅` on the stamped prior (`occ(d₅) = ⊤`).
Source: none: infrastructure. Kind: L -/
theorem tys_stamp_occ_five_pos (C : Proc Five10 (fun _ => Five10) ℚ) :
    0 < (priorState C (stamp {Five10.five} toldYouSo)).pr
      (occW {Five10.five} (Finset.mem_singleton_self _)) := by
  rw [priorState_stamp_pr_occW, tys_occ_five, mass_univ]; exact zero_lt_one

/-- **FP-21′(iv), the audit half as an audit verdict**: under the uniform self-model
`s₅ = δ_{(5,5)}` fails the audit at `d₅` (`¬ AuditPassAt`, through T1(a) and
`tys_five_fails_audit_uniform`).
Source: `firstperson.md` FP-21′(iv) ("yet fails the audit"); audit r1 fidelity N7
Kind: N+
Fidelity: exact -/
theorem tys_five_fails_audit_uniform' :
    ¬ AuditPassAt (priorState tysUniform (stamp {Five10.five} toldYouSo))
      (occW {Five10.five} (Finset.mem_singleton_self _)) (tys_stamp_occ_five_pos tysUniform)
      Prod.fst (tysState .five) := by
  rw [audit_iff_perRunClausesAt tysUniform toldYouSo {Five10.five} (Finset.mem_singleton_self _)
    tysState (tys_stamp_occ_five_pos tysUniform)]
  rintro ⟨hc1, -⟩
  exact tys_five_fails_audit_uniform hc1

/-- **The override is not zero-respecting**: taking 10 at `d₅` puts weight on an action
`P_{s₅}` rules out (`A⁺_{d₅} = {5}`).
Source: `firstperson.md` FP-21′(iv) ("Def 12: deliberately non-zero-respecting")
Kind: N+ -/
theorem tys_take10_not_zeroRespecting : ¬ ZeroRespecting tysState tysActEv procTake10 := by
  intro h
  have := h .five ⟨.five, by simp [APlus, tysState, State.dirac_pr, tysActEv]⟩ .ten
    (by simp [procTake10])
  simp [APlus, tysState, State.dirac_pr, tysActEv] at this

end tys

end Cleanroom.Decision.DpFirstpersonSc
