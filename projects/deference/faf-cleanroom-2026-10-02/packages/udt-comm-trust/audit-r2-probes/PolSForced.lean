import Cleanroom.Udt.UdtCommTrust.Advice

/-!
# Audit r2 (fidelity) probe: what the pointwise UDT rule forces under AF-R's hypotheses

Not imported by the library. Claim checked: under the hypotheses of `polE_follows_R` that do
*not* mention `Π†`/`Π̈` (the pointwise rule, guarded internal drive, told-form stability of every
realized recommendation, `FactorsAsFam R`), **every** chosen policy in the support outputs the
recommended external action at every realized recommended input. So on that hypothesis package
the prior is supported on recommendation-following chosen policies wherever a recommendation is
non-silent; the only work left for `polE_follows_R` is the transfer `Π* → Π† → Π̈` through
`hnosim`, `hlink`, `hR` and the agent-dynamic factorization. This sharpens the ledger's "no
nondegenerate witness where advice-following has bite" (which cites the *junk*-form tie lemma)
to a statement about the guarded form the theorem actually takes.
-/

namespace Cleanroom.Udt.UdtCommTrust

namespace ConcreteDS

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]
  [DecidableEq AI]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-- Under the pointwise rule and AF-R's hypotheses (guarded internal drive), every support policy
follows the recommendation at every realized recommended input. -/
theorem polS_follows_of_udtRule (hUdt : S.UdtRule) (hID : S.InternallyDriven)
    (hStab : ∀ r ∈ Set.range S.R, S.StableR r) (hRfac : FactorsAsFam S.R)
    {o : OI} (ho : o ∈ Set.range S.oI) {e : OE} {a₀ : AE}
    (hs : S.s e (S.projOH o) = some a₀) (ω : Ω) : (S.polS ω (o, e)).2 = a₀ := by
  by_contra hne
  obtain ⟨ω₂, rfl⟩ := ho
  have hRa : S.R ω₂ e = some a₀ := by
    show S.s e (S.oH ω₂) = some a₀
    rw [← S.projOH_oI]
    exact hs
  -- told-form stability at ω₂'s own recommendation makes `(ȧ, a₀)` attained
  have hatt : (S.evS (S.oI ω₂) e ((S.polS ω (S.oI ω₂, e)).1, a₀)).Nonempty := by
    obtain ⟨ω'', hω''⟩ := S.stableR_nonempty (hStab (S.R ω₂) ⟨ω₂, rfl⟩) hRa hs
      (S.polS ω (S.oI ω₂, e)).1 _ hne
    exact ⟨ω'', (Finset.mem_inter.1 hω'').1⟩
  -- AF-R: the recommended action scores strictly above the chosen one
  have hlt := S.adviceFollowing_R hID hStab hRfac ⟨ω₂, rfl⟩ hs (S.polS ω (S.oI ω₂, e)).1 hatt hne
  -- the pointwise rule at ω says the chosen action is an argmax
  have hArg := hUdt ω (S.oI ω₂) e ((S.polS ω (S.oI ω₂, e)).1, a₀)
  exact absurd hArg (not_le.2 hlt)

/-- Consequence: on that package, two support policies can differ at a realized recommended input
only in their *internal* component. -/
theorem polS_snd_eq_of_udtRule (hUdt : S.UdtRule) (hID : S.InternallyDriven)
    (hStab : ∀ r ∈ Set.range S.R, S.StableR r) (hRfac : FactorsAsFam S.R)
    {o : OI} (ho : o ∈ Set.range S.oI) {e : OE} {a₀ : AE}
    (hs : S.s e (S.projOH o) = some a₀) (ω ω' : Ω) :
    (S.polS ω (o, e)).2 = (S.polS ω' (o, e)).2 := by
  rw [S.polS_follows_of_udtRule hUdt hID hStab hRfac ho hs ω,
    S.polS_follows_of_udtRule hUdt hID hStab hRfac ho hs ω']

end ConcreteDS

end Cleanroom.Udt.UdtCommTrust
