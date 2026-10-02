import Cleanroom.Udt.UdtHarmonyBargain.Defs
import Cleanroom.Udt.UdtHarmonyBargain.TreeWitnesses

/-!
# udt-harmony-bargain — audit round 1, lens `fidelity`: probes

Not imported by the library. Two checks behind non-blocking remarks in the audit:

1. `utilGame U` is WLOG for SC collections: every `U : N → Outcome A → ℝ` is the `U` of a
   collection of decision-points with one-point world-models, so the package's "every headline is
   stated over `utilGame U`, hence applies to every collection" is formally closable (the package
   states it in prose only).
2. `tnSigma_harmonious` is stated for membership-faithful selectors (`∀ S, S.Nonempty → sel S ∈ S`)
   while its docstring and the ledger say "singleton-faithful"; the weaker hypothesis suffices
   (the helper only ever consults `sel` on a nonempty subset of a singleton).
-/

namespace Cleanroom.Udt.UdtHarmonyBargain.AuditR1

open Finset SafeParetoImprovements StrategicGame
open Cleanroom.Found.DpCoreTree (FinDistr)
open Cleanroom.Found.DpCoreTree.Catalogue

variable {N : Type} [Fintype N] [DecidableEq N]
variable {A : N → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

/-- The one-point world-model collection realising an arbitrary `U`. -/
def pointCollection (Uf : N → Outcome A → ℝ) (i : N) : DecisionPoint A where
  X := Unit
  μ := { w := fun _ => 1, nonneg := fun _ => zero_le_one, sum_one := by simp }
  u O _ := Uf i O

/-- Probe 1: `utilGame U = collectionGame (pointCollection U)`. -/
theorem utilGame_eq_collectionGame (Uf : N → Outcome A → ℝ) :
    utilGame Uf = collectionGame (pointCollection Uf) := by
  unfold collectionGame utilGame
  congr 1
  funext O i
  simp [UdtHarmonyBargain.U, pointCollection]

/-- The singleton-faithful form of `TreeWitnesses.outcome_coord_of_singleton`. -/
theorem outcome_coord_of_singleton' {sel : Finset (Outcome A) → Outcome A}
    (hsel : ∀ O, sel {O} = O) (σ : ∀ i, Proposal A i) (j : N)
    {O₀ : Outcome A} (h : (σ j).2 = {O₀}) (hb : O₀ j = (σ j).1) :
    outcome sel σ j = (σ j).1 := by
  rcases outcome_eq_sel_or_batna sel σ with ⟨hne, hout⟩ | ⟨-, hout⟩
  · rw [hout]
    have hsub : inter σ ⊆ {O₀} := by
      intro O hO
      rw [mem_inter] at hO
      have := hO j
      rwa [h] at this
    have heq : inter σ = {O₀} := by
      obtain ⟨O, hO⟩ := hne
      have hO' := hsub hO
      rw [Finset.mem_singleton] at hO'
      subst hO'
      exact Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hO, fun O' hO' => Finset.mem_singleton.mp (hsub hO')⟩
    rw [heq, hsel, hb]
  · rw [hout]; rfl

/-- Probe 2: the TN-V2 witness under the weaker (singleton-faithful) hypothesis — the same proof
as `tnSigma_harmonious` with the helper above. -/
theorem tnSigma_harmonious_singletonFaithful (sel : Finset TnOut → TnOut)
    (hsel : ∀ O : TnOut, sel {O} = O) : HarmoniousPure tnUpd sel tnSigma := by
  apply thpe_of_dominant
  intro i s τ
  rw [bargain_payoff, bargain_payoff, ofStrategicProfile_update, ofStrategicProfile_update]
  cases i
  · rw [tnUpd_u_F, tnUpd_u_F]
    set σ' := Function.update ((bargain tnUpd sel).ofStrategicProfile τ) .F
      (toStrat tnUpd sel tnSigma .F : Proposal (fun _ => Box) .F) with hσ'
    have h5 : tnUF (outcome sel σ') = 5 :=
      tnUF_of_both _ (outcome_coord_of_singleton' hsel σ' .F (O₀ := tnO .both .both)
        (by simp [hσ', tnSigma]) (by simp [hσ', tnSigma]))
    rw [h5]
    exact_mod_cast tnUF_le _
  · rw [tnUpd_u_E, tnUpd_u_E]
    set σ' := Function.update ((bargain tnUpd sel).ofStrategicProfile τ) .E
      (toStrat tnUpd sel tnSigma .E : Proposal (fun _ => Box) .E) with hσ'
    have h1 : tnUE (outcome sel σ') = 1 :=
      tnUE_of_both _ (outcome_coord_of_singleton' hsel σ' .E (O₀ := tnO .both .both)
        (by simp [hσ', tnSigma]) (by simp [hσ', tnSigma]))
    rw [h1]
    exact_mod_cast tnUE_le _

end Cleanroom.Udt.UdtHarmonyBargain.AuditR1
