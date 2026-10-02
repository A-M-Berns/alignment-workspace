import Cleanroom.Li.LiProjection.Church
import Cleanroom.Li.LiProjection.Open

/-!
# Audit r4 (adversarial) probe: axioms and statements of the repair-round-3 additions.

`#print axioms` on every declaration repair round 3 added or moved (the ledger says each is
sorry-free except the two T6.1 OPENs and the pinned `paperU1U2_half_sameDay`), and `#check` of the
two new headlines so their statements are on record as Lean prints them. Also: the binders of
`convergence_rate_not_computable` are inhabited at `𝗜𝚺₁` (the library has no `_ISigma1` instance
for it; T6.2 has one).
-/

open Cleanroom.Li.LiProjection LogicalInduction LO.FirstOrder LO.FirstOrder.Arithmetic

#check @convergence_rate_not_computable
#check @no_computable_modulus_market
#check @exists_computable_modulusFree_approximant
#check @conditioned_record_not_injective

#print axioms convergence_rate_not_computable
#print axioms convergence_rate_exists_classically
#print axioms rateSearch_re
#print axioms rateBit_iff
#print axioms paperPrimeDecomposeCode_encode
#print axioms no_computable_modulus_market
#print axioms exists_computable_modulusFree_approximant
#print axioms paper_modulusFree_approximant
#print axioms ledgerSeq_half_sameDay_literal
#print axioms paperU1U2_half_sameDay
#print axioms conditioned_record_not_injective
#print axioms conditioned_limitRecord_not_injective

/-- LI Proposition 5.5.1 at the mandate's `T := 𝗜𝚺₁` for FAF's paper LIA: the section binders
`[T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]` are inhabited (the same binders as
`limit_non_recoverable_ISigma1`). -/
theorem convergence_rate_not_computable_ISigma1 :
    ¬ ∃ f : ℕ → ℕ → ℕ, Computable (fun p : ℕ × ℕ => f p.1 p.2) ∧
      ∀ (σ : ArithmeticSentence) (k n : ℕ), 𝗜𝚺₁ ⊢ σ → f (Encodable.encode σ) k < n →
        1 - 1 / ((k : ℝ) + 1) < liaHistory (paperDP 𝗜𝚺₁) n (paperPrimeDecompose σ) :=
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
    LIA_is_logical_inductor _ (paperDP_computable _)
  convergence_rate_not_computable 𝗜𝚺₁ (liaHistory (paperDP 𝗜𝚺₁))

#print axioms convergence_rate_not_computable_ISigma1
