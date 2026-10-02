import Cleanroom.Li.LiProjection.Church
import Cleanroom.Li.LiProjection.Open

/-! Audit r4 (fidelity) probe: `#print axioms` on every declaration repair round 3 added or moved,
so the round's "proved outright" and "sorry-free" claims are checked by reading the axiom sets
rather than inferred from the gate. Expected: `[propext, Classical.choice, Quot.sound]` for the
LI Prop 5.5.1 chain (`paperPrimeDecomposeCode_encode`, `rateSearch_re`,
`convergence_rate_not_computable`, `convergence_rate_exists_classically`), the `ComputableMarket`
modulus corollary (`no_computable_modulus_market`), the modulus-free contrast
(`exists_computable_modulusFree_approximant`, `paper_modulusFree_approximant`) and the pinned
ledger literal (`ledgerSeq_half_sameDay_literal`); `sorryAx` for the controls
`paperU1U2_half_sameDay` (rests on (A) through `u1_u2_inductor`) and the two family-form T6.1 OPENs.
The `#check`s print the statements as elaborated, so the Fidelity reading in the audit is of the
real binders (`Rewriting.emb σ`, the real `1 / (↑k + 1)`, `ComputableMarket A`).
(File name carries the lens prefix: the adversarial auditor's `AxiomsR4.lean` overwrote an earlier
copy of this probe mid-round — the shared-directory hazard round 3's adversarial audit noted.) -/

namespace Cleanroom.Li.LiProjection.AuditR4Fidelity

-- round-3 additions, expected sorry-free
#print axioms Cleanroom.Li.LiProjection.paperPrimeDecomposeCode_encode
#print axioms Cleanroom.Li.LiProjection.rateSearch_re
#print axioms Cleanroom.Li.LiProjection.convergence_rate_not_computable
#print axioms Cleanroom.Li.LiProjection.convergence_rate_exists_classically
#print axioms Cleanroom.Li.LiProjection.no_computable_modulus_market
#print axioms Cleanroom.Li.LiProjection.exists_computable_modulusFree_approximant
#print axioms Cleanroom.Li.LiProjection.paper_modulusFree_approximant
#print axioms Cleanroom.Li.LiProjection.ledgerSeq_half_sameDay_literal
-- the T6.2 chain, re-checked this round
#print axioms Cleanroom.Li.LiProjection.limit_non_recoverable_of_inductor
#print axioms Cleanroom.Li.LiProjection.limit_non_recoverable_ISigma1
#print axioms Cleanroom.Li.LiProjection.no_computable_modulus
-- controls (expected to carry sorryAx)
#print axioms Cleanroom.Li.LiProjection.paperU1U2_half_sameDay
#print axioms Cleanroom.Li.LiProjection.conditioned_record_not_injective
#print axioms Cleanroom.Li.LiProjection.conditioned_limitRecord_not_injective

-- the statements as elaborated
#check @Cleanroom.Li.LiProjection.convergence_rate_not_computable
#check @Cleanroom.Li.LiProjection.no_computable_modulus_market
#check @Cleanroom.Li.LiProjection.exists_computable_modulusFree_approximant
#check @Cleanroom.Li.LiProjection.conditioned_record_not_injective

end Cleanroom.Li.LiProjection.AuditR4Fidelity
