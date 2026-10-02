import Cleanroom.Corrigibility.CorrExoTrader

/-!
# Audit r3 (adversarial) probe — per-declaration axioms of the repair-round-2 content and the five
load-bearing theorems

Expected: `propext`, `Classical.choice`, `Quot.sound` only, except where the open list says
`sorryAx` (`frontRun_witness`, `persistent_push_steers`, `constraint_lic_compatible`). Not imported
by the library.
-/

open Cleanroom.Corrigibility.CorrExoTrader

-- repair round 2
#print axioms netWorth_sub_netWorth_of_agree_on_traded
#print axioms joinBuyers_agree_on_traded
#print axioms constBuyer_agree_on_traded
#print axioms hcWitness_commitment
#print axioms hcWitness_stopWhenPressed_optimal
#print axioms hcIndep_not_commitment
#print axioms landing_increments_vanish_of_inductor
#print axioms frontRun_const_family_iff_of_inductor
#print axioms frontRun_fails_without_hworld
#print axioms frontRun_exo_witness_theorem
-- load-bearing five
#print axioms exo_day_value_le
#print axioms exo_finiteHorizon_bound
#print axioms noEcExploit_of_boundedLoss
#print axioms frontRun_asympEq
#print axioms occam_exhausted
-- listed OPENs reached through this package
#print axioms frontRun_witness
#print axioms persistent_push_steers
#print axioms constraint_lic_compatible
