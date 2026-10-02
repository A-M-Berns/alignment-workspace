import Cleanroom.Li.LiProjection.Subst
import Cleanroom.Li.LiProjection.Defs
import Cleanroom.Li.LiProjection.Mirror
import Cleanroom.Li.LiProjection.Certificate
import Cleanroom.Li.LiProjection.Market
import Cleanroom.Li.LiProjection.LemmaA
import Cleanroom.Li.LiProjection.Marginal
import Cleanroom.Li.LiProjection.Underdetermination
import Cleanroom.Li.LiProjection.Prescribe
import Cleanroom.Li.LiProjection.Fragments
import Cleanroom.Li.LiProjection.Witnesses
import Cleanroom.Li.LiProjection.Recover
import Cleanroom.Li.LiProjection.Open
import Cleanroom.Li.LiProjection.Church

/-!
# `li-projection` — Underdetermination: the Projection Lemma, prescribed prefixes and undecided limits

Root module of the package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]). Files, in
dependency order: `Subst` (substitution, Shannon split, freshness, the family-4 atoms), `Defs`
(definitions of record), `Mirror` (the value identities), `Certificate` (the e.c. certificate,
reduced to two OPEN `Complexity.FP` obligations), `Market` (the `ComputableMarket` of the
projection), `LemmaA` (the Projection Lemma), `Marginal` (restriction, marginal, limits; summable
convergence), `Underdetermination` (two inductors, one gap), `Prescribe` (prescribed prices split
three ways), `Fragments` (decided/undecided fragments), `Witnesses` (the N+ packages over FAF's
paper LIA), `Recover` (No-Forced-Trust), `Open` (the open statements of record, including — since
repair round 2 — the source's precise T6.1 target `conditioned_record_not_injective` /
`conditioned_limitRecord_not_injective`, over a stage-indexed family since repair round 3), `Church`
(added in repair round 1: Church's theorem along the halting family; since repair round 2 T6.2 is
**proved outright** there — the r.e. search pulls back along the halting family by the Σ₁ route
`rePred_comp_numeralSubst`, so `limit_non_recoverable`, `limit_non_recoverable_of_inductor`,
`limit_non_recoverable_ISigma1` and the corollary `no_computable_modulus` are sorry-free; since
repair round 3 also **LI Proposition 5.5.1**, `convergence_rate_not_computable`, proved outright
through FAF's `paperPrimeDecomposeCode_prim` as the market-side search, the `ComputableMarket`
corollary `no_computable_modulus_market`, and the contrast `exists_computable_modulusFree_approximant`
— without a modulus the market's own table approximates every limit; the coding fact
`numeralSubst_code_computable` remains only as an OPEN of record that nothing uses; `paperU1U2`
instantiates T6.1 at the paper LIA, pinned as `paperU1U2_half_sameDay`).
-/
