import Cleanroom.Udt.UdtCommTrust.Advice

/-!
# Audit r2 (adversarial) probe: the pointwise package of `polE_follows_R` forces every chosen
policy to follow the recommendation

Not imported by the library. Claim checked: under `polE_follows_R`'s hypotheses *without* the
three transfer hypotheses (`hnosim`, `hlink`, `hR`), every world's chosen policy already plays the
recommended external action at every realized recommended input. So no model of the printed
clause's package has a chosen policy of positive mass deviating at a recommended input — the
general reason (for the guarded `InternallyDriven`) why the only witness is the constant `Det`,
and why the printed theorem's own content is the transfer `Π* → Π† → Π̈`. The ledger cites
`W2.not_udtRule` and the junk-form tie lemma for this; the junk-form lemma does not apply to the
guarded form, this does.
-/

namespace Cleanroom.Udt.UdtCommTrust.AuditR2

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]
  [DecidableEq AI] [Fintype DI] [DecidableEq DI] [Fintype DE] [DecidableEq DE] [Fintype DB]
  [DecidableEq DB]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-- Under the pointwise UDT rule, guarded internal drive, told-form stability of every realized
recommendation and `FactorsAsFam R`, the chosen policy of *every* world plays the recommended
external action at every realized input whose semantics recommend one. -/
theorem polS_follows_of_pointwise (hUdt : S.UdtRule) (hID : S.InternallyDriven)
    (hStab : ∀ r ∈ Set.range S.R, S.StableR r) (hRfac : FactorsAsFam S.R)
    (ω : Ω) {o : OI} (ho : o ∈ Set.range S.oI) {e : OE} {a₀ : AE}
    (hs : S.s e (S.projOH o) = some a₀) : (S.polS ω (o, e)).2 = a₀ := by
  by_contra hne
  obtain ⟨ω₂, rfl⟩ := ho
  have hRa : S.R ω₂ e = some a₀ := by
    show S.s e (S.oH ω₂) = some a₀
    rw [← S.projOH_oI]
    exact hs
  have hatt : (S.evS (S.oI ω₂) e ((S.polS ω (S.oI ω₂, e)).1, a₀)).Nonempty := by
    obtain ⟨ω'', hω''⟩ := S.stableR_nonempty (hStab (S.R ω₂) ⟨ω₂, rfl⟩) hRa hs
      (S.polS ω (S.oI ω₂, e)).1 _ hne
    exact ⟨ω'', (Finset.mem_inter.1 hω'').1⟩
  have hlt := S.adviceFollowing_R hID hStab hRfac ⟨ω₂, rfl⟩ hs (S.polS ω (S.oI ω₂, e)).1 hatt hne
  exact absurd (hUdt ω (S.oI ω₂) e ((S.polS ω (S.oI ω₂, e)).1, a₀)) (not_le.2 hlt)

/-- Consequence: under the same package, at a realized recommended input the *only* attained
actions are `(ȧ, a₀)`; a world choosing a different external action there would contradict the
previous theorem. So "a chosen policy of positive mass deviates at a recommended input" is
inconsistent with the package — the prior over chosen policies is degenerate in the external
component at every recommended input. -/
theorem no_deviating_world (hUdt : S.UdtRule) (hID : S.InternallyDriven)
    (hStab : ∀ r ∈ Set.range S.R, S.StableR r) (hRfac : FactorsAsFam S.R)
    {o : OI} (ho : o ∈ Set.range S.oI) {e : OE} {a₀ : AE}
    (hs : S.s e (S.projOH o) = some a₀) {ai : AI} {a : AE} (ha : a ≠ a₀) :
    S.evS o e (ai, a) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ω hω
  rw [AbstractDS.mem_evS] at hω
  have := polS_follows_of_pointwise S hUdt hID hStab hRfac ω ho hs
  rw [hω] at this
  exact ha this

end Cleanroom.Udt.UdtCommTrust.AuditR2
