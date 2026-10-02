import Cleanroom.Bli.UdtBliCore.Wirehead

/-!
# Audit r3 (fidelity) probe: the wireheading identity needs only the `faith` field when the
next state settles the current action

Finding F-17 says the source's derivation of the wireheading identity (bli-soto-b-058,
"with constraint 2 in force") "silently uses more than constraint 2", because on `wfPrior` the
`faith` field holds and the identity fails (`wf_identity_fails`). On `wfPrior` the single table
cannot express the action (its small index is `{p, q}`), so the action cell `state = T ∧ act = a`
is a *proper* sub-event of `state = T` on which faith says nothing.

This probe checks the natural reading of the source, on which a written-out day-`(n+1)` state
settles the day-`n` action: if `act` is a function of `state` on the positive-mass worlds, the
`faith` field alone gives `FaithGivenAct`, hence the identity. So the strengthening
`wirehead_identity` takes is needed exactly when the next state does *not* settle the action —
which is what `wfPrior` exhibits. Not imported by the library.
-/

namespace AuditR3Fid

open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.BliFinite Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type}
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A) {A' : Type} [DecidableEq A'] (act : P.Ω → A')

/-- Two events that agree on every positive-mass world have the same integral. -/
lemma integralOf_congr_ae (g : P.Ω → ℚ) (E E' : P.Ω → Prop) [DecidablePred E]
    [DecidablePred E'] (h : ∀ ω, 0 < P.μ ω → (E ω ↔ E' ω)) :
    integralOf P.μ g E = integralOf P.μ g E' := by
  unfold integralOf
  apply Finset.sum_congr rfl
  intro ω _
  rcases (P.μ_nonneg ω).lt_or_eq with hpos | hzero
  · by_cases hE : E ω
    · have hE' : E' ω := (h ω hpos).mp hE
      rw [if_pos hE, if_pos hE']
    · have hE' : ¬ E' ω := fun h' => hE ((h ω hpos).mpr h')
      rw [if_neg hE, if_neg hE']
  · rw [← hzero]
    simp

/-- Two events that agree on every positive-mass world have the same mass. -/
lemma massOf_congr_ae (E E' : P.Ω → Prop) [DecidablePred E] [DecidablePred E']
    (h : ∀ ω, 0 < P.μ ω → (E ω ↔ E' ω)) : massOf P.μ E = massOf P.μ E' := by
  unfold massOf
  apply Finset.sum_congr rfl
  intro ω _
  rcases (P.μ_nonneg ω).lt_or_eq with hpos | hzero
  · by_cases hE : E ω
    · have hE' : E' ω := (h ω hpos).mp hE
      rw [if_pos hE, if_pos hE']
    · have hE' : ¬ E' ω := fun h' => hE ((h ω hpos).mpr h')
      rw [if_neg hE, if_neg hE']
  · rw [← hzero]
    simp

/-- **If the state settles the action (on positive-mass worlds), the `faith` field gives
action-conditional faith.** The cell `state = T ∧ act = f T` agrees with `state = T` off null
worlds, so faith's identity transfers; every other action cell at `T` is null. -/
theorem faithGivenAct_of_determined (f : ↥𝒟 → A')
    (hdet : ∀ ω, 0 < P.μ ω → act ω = f (P.state ω)) : P.FaithGivenAct act := by
  intro T φ a hpos
  by_cases ha : a = f T
  · subst ha
    have hE : ∀ ω, 0 < P.μ ω → ((P.state ω = T ∧ act ω = f T) ↔ P.state ω = T) := by
      intro ω hω
      constructor
      · exact fun h => h.1
      · intro hs
        refine ⟨hs, ?_⟩
        rw [hdet ω hω, hs]
    have h1 := integralOf_congr_ae P (fun ω => ind (P.small ω φ))
      (fun ω => P.state ω = T ∧ act ω = f T) (fun ω => P.state ω = T) hE
    have h2 := massOf_congr_ae P (fun ω => P.state ω = T ∧ act ω = f T)
      (fun ω => P.state ω = T) hE
    rw [h1, h2]
    unfold integralOf massOf
    exact P.faith T φ
  · exfalso
    have hnull : massOf P.μ (fun ω => P.state ω = T ∧ act ω = a) = 0 := by
      unfold massOf
      apply Finset.sum_eq_zero
      intro ω _
      by_cases hE : P.state ω = T ∧ act ω = a
      · rw [if_pos hE]
        rcases (P.μ_nonneg ω).lt_or_eq with hpos' | hzero
        · exfalso
          apply ha
          rw [← hE.2, hdet ω hpos', hE.1]
        · exact hzero.symm
      · exact if_neg hE
    rw [hnull] at hpos
    exact lt_irrefl _ hpos

/-- **Corollary: the wireheading identity under the `faith` field alone**, whenever the state
settles the action. This is the source's "with constraint 2 in force" on the reading where the
next state records the current action; `wfPrior` is the case where it cannot. -/
theorem wirehead_identity_of_faith (c : ↥(𝒮.S m) → ℚ) (hU : P.SmallCombination c)
    (f : ↥𝒟 → A') (hdet : ∀ ω, 0 < P.μ ω → act ω = f (P.state ω)) (a : A') :
    condExp P.μ P.U (fun ω => act ω = a) =
      ∑ T, massOf P.μ (fun ω => act ω = a ∧ P.state ω = T) / massOf P.μ (fun ω => act ω = a) *
        FiniteBLIPrior.believedValue c T :=
  P.wirehead_identity act c hU (faithGivenAct_of_determined P act f hdet) a

end AuditR3Fid
