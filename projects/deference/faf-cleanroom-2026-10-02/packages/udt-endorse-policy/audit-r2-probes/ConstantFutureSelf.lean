import Cleanroom.Udt.UdtEndorsePolicy.Reflection

/-!
# Audit r2 (adversarial) probe: the degenerate end of `BeliefEndorsedAll`

The report (§Stretch and open, after audit r1 adversarial N10) states in prose that the
"no-learning" anticipation structure `κ_ā = P` for every atom is belief-endorsed on every event.
Checked here in general: for any `P : PMF Ω` on a finite `Ω` and any atom map `a`, the structure
whose every kernel is `P` itself satisfies `BeliefEndorsedAll`. Each future belief report is the
constant `P(X)`, its one positive class is `univ`, and `P(X ∩ univ) = P(X) · 1`. This is the
Reflection Principle's trivial case (a future self that learns nothing is endorsed), and the
reason `as3` — non-constant reports on the non-trivial events — is the witness that carries the
N+ grade. Not imported by the library.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy.AuditR2

open Cleanroom.Udt.UdtPolicyCalc Finset
open Cleanroom.Udt.UdtSupercondition (AnticipationStructure)
open scoped ENNReal

noncomputable section

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The structure that anticipates no change of belief: every atom's kernel is the prior. -/
def noLearning (P : PMF Ω) {A : Type} [Countable A] (a : Ω → A) : AnticipationStructure P Ω :=
  { A := A, a := a, κ := fun _ => P }

omit [DecidableEq Ω] in
/-- The real weights of a `PMF` on a finite carrier sum to `1`. -/
theorem mass_pw_univ (P : PMF Ω) : mass (pw P) univ = 1 := by
  unfold mass pw
  rw [← ENNReal.toReal_sum (fun ω _ => PMF.apply_ne_top P ω)]
  have := P.tsum_coe
  rw [tsum_fintype] at this
  rw [this, ENNReal.toReal_one]

/-- **The no-learning structure is belief-endorsed on every event** (the degenerate end of
`BeliefEndorsedAll`, confirming the report's prose). -/
theorem noLearning_beliefEndorsedAll (P : PMF Ω) {A : Type} [Countable A] (a : Ω → A) :
    BeliefEndorsedAll P (noLearning P a) := by
  intro X p hp
  -- the report is the constant `P(X)`
  have hconst : ∀ ω, futureBelief (noLearning P a) X ω = mass (pw P) X := fun ω => by
    unfold futureBelief noLearning
    exact toReal_mass_finset P X
  -- its positive class is `univ`, at the value `P(X)`
  obtain ⟨ω₀, hω₀, _⟩ := exists_pos_of_mass_pos (pw_nonneg P) hp
  have hpX : p = mass (pw P) X := by
    have : futureBelief (noLearning P a) X ω₀ = p := by simpa using hω₀
    rw [← this, hconst]
  have hcls : cls (futureBelief (noLearning P a) X) p = univ := by
    ext ω
    simp [cls, hconst, hpX]
  rw [hcls, Finset.inter_univ, mass_pw_univ, mul_one, hpX]

end

end Cleanroom.Udt.UdtEndorsePolicy.AuditR2

#print axioms Cleanroom.Udt.UdtEndorsePolicy.AuditR2.noLearning_beliefEndorsedAll
