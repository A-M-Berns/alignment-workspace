import Cleanroom.Li.LiPseudorandom.Defs
import Cleanroom.Li.LiPseudorandom.Locality
import Cleanroom.Li.LiPseudorandom.Diagonal
import Cleanroom.Li.LiPseudorandom.Countable
import Cleanroom.Li.LiPseudorandom.AtomDP
import Cleanroom.Li.LiPseudorandom.Fixed
import Cleanroom.Li.LiPseudorandom.Family
import Cleanroom.Li.LiPseudorandom.Union
import Cleanroom.Li.LiPseudorandom.Deferral
import Cleanroom.Li.LiPseudorandom.Lift
import Cleanroom.Li.LiPseudorandom.Joint
import Cleanroom.Li.LiPseudorandom.Witnesses
import Cleanroom.Li.LiPseudorandom.Market
import Cleanroom.Li.LiPseudorandom.Computable

/-!
# `li-pseudorandom`: a pseudorandom family FAF can inhabit

Root module. A dependent imports this one name (or `Cleanroom.Li.LiPseudorandom.Family`, which
brings the definitions module and everything below it except the T7 file) and gets:

* **Definitions of record** (`Defs`): `truthR`, `CausalRule`, `restrict`, `clamp`, the potential
  (`tilt`, `mass`, `factor`, `mart`, `pot`), the diagonal sequence `diag` (via `diagStep`,
  `diagPrefix`), `builderRule`, `CausalBuilder`, `diagBuilder`, `atomFamily`, `literalOf`,
  `atomDP`.
* **T1** (`Diagonal`): `diag_pseudorandom` (day-varying target), `diag_pseudorandom_const`,
  `diag_pseudorandom_of_surjective`.
* **T2** (`Countable`): `pgenerable_countable`; the enumeration of record `genWeighting` —
  explicit and primitive recursive since repair round 1 (`genWeighting_primrec`,
  `genWeighting_computable`) — with exact coverage `genWeighting_covers`.
* **T3** (`Locality`): `EF.denote_congr_of_rank_le`, `PGenerableWeighting.denote_congr`.
* **T4/T5** (`Fixed`): `diagBuilder_pseudorandom_of_causal`, `pseudorandomFrequency_of_causal`,
  `exists_pseudorandom_of_causal`, `variedPseudorandom_of_causal`;
  `diagBuilder_pseudorandom_of_history`, `pseudorandomFrequency_of_history`,
  `exists_pseudorandom_of_history`.
* **T6** (`AtomDP`, `Family`): `atom_mem_atomDP_iff`, `neg_atom_mem_atomDP_iff`, `atomDP_hworld`,
  `atomDP_theoryTruth`, `machineSentenceCodes_atomFamily_id`, `liaStates_congr`,
  `liaHistory_congr`, `liaHistory_atomDP_causal`; the family of record `truthStar` with
  `truthStar_pseudorandom_all`, `truthStar_pseudorandom`, `truthStar_theoryTruth`,
  `truthStar_hworld`, `truthStar_learned` (over the `IsLogicalInductor` instance),
  `truthStar_atom_mem_iff`.
* **The union shape** (`Union`): `liaHistory_union_atomDP_causal`, `unionStar` with
  `unionStar_pseudorandom_all`, `unionStar_pseudorandom`, `union_atomDP_theoryTruth`,
  `unionStar_theoryTruth` — the family inside `DP₀.union (atomDP …)`, the plan's `paperDP T`
  instance shape.
* **T7** (`Computable`, OPEN): `truthStar_computable`, `starDP_computable`;
  `truthStar_isLogicalInductor` and `truthStar_learned_of_computable` resting on them.
* **T8** (`Deferral`): `deferralPatient_succDeferral_of_divergent`,
  `pseudorandomFrequency_succDeferral_iff`, `pseudorandomFrequency_of_all`.
* **T9's machinery** (`Lift`, repair round 2): `Schedule` (`evenSched`, `oddSched`,
  `pairSched`), the lifted rule `lift`, `sum_lift`, `subfamily_of_lift`,
  `subfamily_pseudorandom_of_lift`, the disjoint union `unionRules`,
  `variedPseudorandom_of_builderRule_mem`, `pseudorandom_all_of_builderRule_mem`.
* **T9** (`Joint`): `pairTarget`, `twoFamilyRules`, `truthStar₂` (redefined in repair round 2
  over the disjoint union of the rule families), `truthStar₂_variedPseudorandom`,
  `truthStar₂_even_pseudorandom`, `truthStar₂_odd_pseudorandom` (and their `…_all` paper forms) —
  the cross-reading form, proved; countably many families: `omegaTarget`, `omegaRules`,
  `truthStarω`, `truthStarω_pseudorandom`, `truthStarω_pseudorandom_all`,
  `truthStarω_variedPseudorandom`.
* **Witnesses** (`Witnesses`): `constRule`, `evenRule`, `prevRule`, `not_eventuallyConst_of_average`,
  `diag_not_eventuallyConst`, `diag_even_density`, `diag_prev_density`, `diag_const_half_zero`,
  `diag_const_half_one`, `diagBuilder_history_not_eventuallyConst` (any `P`),
  `diagBuilder_liaHistory_not_eventuallyConst`, `toyBuilder`, `toyBuilder_causal`,
  `toyBuilder_pseudorandom`, `truthStar_not_eventuallyConst`, `atomDP_stage_ssubset`,
  `not_eventuallyConst_of_varied_average`, `truthStar₂_not_eventuallyConst`,
  `truthStar₂_even_not_eventuallyConst`, `truthStar₂_odd_not_eventuallyConst`,
  `truthStarω_family_not_eventuallyConst`, `unionStar_not_eventuallyConst`; the load-bearing
  hypotheses: `omniscient`, `omniscient_causalBuilder_id`, `omniscient_not_causalBuilder_succ`,
  `trivial_enumeration_does_not_cover`.
* **The market of record** (`Market`, repair round 2): `atomDP_succ_computable`,
  `atomDP_succ_isLogicalInductor` (certified inductors over primitive recursive fixed families),
  `liaHistory_atomDP_ne`, `builder_not_const` (the LIA over `atomDP` varies with the stream),
  `diagBuilder_liaHistory_certified` (T4's witness of record over a certified inductor).
-/
