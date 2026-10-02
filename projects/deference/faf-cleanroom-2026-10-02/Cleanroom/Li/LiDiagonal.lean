import Cleanroom.Li.LiDiagonal.Defs
import Cleanroom.Li.LiDiagonal.Pinned
import Cleanroom.Li.LiDiagonal.Engine
import Cleanroom.Li.LiDiagonal.Deferred
import Cleanroom.Li.LiDiagonal.Family
import Cleanroom.Li.LiDiagonal.TwoFaces
import Cleanroom.Li.LiDiagonal.GatedForcing
import Cleanroom.Li.LiDiagonal.PastPrice
import Cleanroom.Li.LiDiagonal.Leak
import Cleanroom.Li.LiDiagonal.Forcing
import Cleanroom.Li.LiDiagonal.Legality
import Cleanroom.Li.LiDiagonal.Scope
import Cleanroom.Li.LiDiagonal.Agent
import Cleanroom.Li.LiDiagonal.Baseline
import Cleanroom.Li.LiDiagonal.Grade
import Cleanroom.Li.LiDiagonal.Schemata
import Cleanroom.Li.LiDiagonal.LemmaS
import Cleanroom.Li.LiDiagonal.Paper
import Cleanroom.Li.LiDiagonal.Open

/-!
# `li-diagonal`: quote-referencing diagonals and paradox resistance

Root module ([[li-diagonal-mandate]]). A dependent imports this one name and gets:

* **Definitions of record** (`Defs`): `defDiag` (the deferred liar as a reindexing), `diagTruth`,
  `gDiag` (the cross-process family over the ledger), `side`, `DiagonalPair` (the two-way object),
  `AgentCoupling`, `VariedParadoxResistanceQuote`.
* **T1** (`Pinned`): `paradox_pinned_within_width`, `paradox_pinned_every_rate` (pinning beats
  every e.c. rate, constant `1`), `paradox_resistance_of_pinned`, `ramp_silence_above/below`,
  `ramp_silence_every_rate`, `introspection_margin_fails`; at margin `0` (repair round 2)
  `ramp_margin_zero_le_width`, `ramp_margin_zero_tendsto_zero`, `ramp_margin_zero_eq_zero_iff`
  (exact silence there is E2).
* **T2a/b** (`Engine`): `pinning_engine` (vanishing-margin link), `pinning_engine_sharp`,
  `pinning_engine_diagonal` (N+), `paradox_resistance_via_engine`, `link_of_asympEq` (the link
  is the weaker side; repair round 2); infrastructure `expectFeature_pgenerable`, `ofLUVSyntax`,
  `ofLUV_boundedSequence`, `eventually_lt_one_of_not_divergent`.
* **T2c, T3.3(i), T4 cross-process** (`Forcing`, two-way, `partial: over the OPEN pair`):
  `forcingA`, `forcingA_table`, `theoremC_i`, `two_faces_pair`; `DiagonalPair.median`, `.median_payout`, `.median_price`,
  `patchPrefix`; **Lemma B's bridge** (repair round 2): `padG`, `padG_codes_succ`,
  `lemmaB_expect` (`|𝔼^H_{f(n)}(𝟙 g_n) − s_n| → 0` by `thm:ei` on the padded `g` family),
  `lemmaB_expect_quarter`, and `forcingA_of_lemmaB`, `two_faces_pair_of_lemmaB` with `htrack`
  discharged from the certificates `hR`, `hR'`, `hG`.
* **T3** (`Family`, one-way): `gDiag_codes`, `gDiag_decided`, `gDiag_decided_succ`,
  `gDiag_truth_iff`, `gDiag_theoryTruth`, `lemmaB`, `lemmaB_quarter` (over the cost-model
  certificates `hR`, `hR'`).
* **T4** (`TwoFaces`): `two_faces_diagonal`.
* **T5** (`Deferred`): `defDiag_reflected`, `defDiag_future_price`, `defDiag_present_price_of_ceu`
  / `_of_quote`, `defDiag_neg_price_of_quote`, `hard_endorsement_fails_of_half`,
  `hard_endorsement_fails_deferredDiagonal` (the note's no-go confirmed),
  `soft_self_trust_deferredDiagonal`, the
  grading lemmas `confidence_expect_tendsto_one/zero`, `product_expect_tendsto_zero`;
  infrastructure `expect_asympEq_of_determinedVia_tendsto`, `neg_coherence`, `neg_price_of_pos`,
  `kleeneDiag`, `harmonicDiagonalQuote`, `defDiag_codes_succ`.
* **T5f's N+ product side** (`Grade`): `expect_asympEq_of_eventually_values_close` (two LUV
  families valued alike eventually have asymptotically equal expectations; FAF API request),
  `product_expect_tendsto_p` (`𝔼_n(A_n) → p` at `p' + δ < p`), `soft_self_trust_nondegenerate`
  (both `thm:st` sides have positive limits `p`, `p'`); paper-market instances
  `paper_product_expect_tendsto`, `paper_soft_self_trust_nondegenerate` (`Paper`).
* **T5g** (`Schemata`): the 2×2 verdict table `schemata_two_by_two` — `hard_eq_schema_fails`,
  `hard_ge_schema_fails` (every `t > 0`), `soft_eq_schema_fails` (every `p' + δ < p`), soft-`≥`
  holds (FAF's `thm:st`); `conj_neg_price_tendsto_zero`, `defDiag_neg_price_tendsto`.
* **T6** (`GatedForcing`, `PastPrice`, `Leak`): Lemma F in both forms — `gated_forcing`,
  `gated_forcing_neg` (`→ 0`, completed-theory truth) and `gated_forcing_summable`,
  `gated_forcing_neg_summable` (the source's `∑ < ∞` under stage-decidedness, by the traders
  `gatedTrader`/`gatedTraderNeg`), with `price_summable_of_mem`/`_of_neg_mem` (summable
  provability induction, N−); `gated_forcing_diagonal` (N−: the gate dies by T1); the N+ witness
  `gated_forcing_pastPrice_const` / `gated_forcing_pastPrice_alternating` (`PastPrice`: the quote
  of the market's own yesterday price of the diagonal, `pastPriceQuote`, with the legal ramp
  `pastPriceRamp`; `pastPriceRamp_eventually`), and T7c(ii) `priceRampBelow_yesterday_pgenerable`;
  `revisiting_leak`, `evenIndicator_pgenerable`, `revisiting_leak_evens` (N+ for divergence
  and the zero average, N− for patience: `succPatient_of_le_one`, `const_one_succPatient`,
  repair round 2).
* **T6c** (`LemmaS`): `lemmaS` (a revisiting enumeration of proved and refuted sentences has
  diagonal-price liminf `0` and limsup `1`; `thm:provind` on the two constant families — no
  e.c. certificate of the enumeration), `lemmaS_supForm` (the source's sup/inf-form, same
  route; repair round 2), `lemmaS_alternating` (N+), `price_tendsto_one_of_mem`,
  `price_tendsto_zero_of_neg_mem`.
* **Witnesses** (`Paper`, the only file importing `Construction.Paper.Market`):
  `paper_pinned_every_rate`, `paper_pinned_harmonic`, `paper_pinned_two_pow`,
  `paper_engine_diagonal`, `paper_defDiag_present_price(_succ)`, `paper_defDiag_neg_price`,
  `paper_hard_endorsement_fails(_succ)`, `paper_soft_self_trust`, `paper_two_faces`,
  `paper_gated_forcing_pastPrice_const`, `paper_gated_forcing_pastPrice_alternating`.
* **T7c** (`Legality`): `hardGate_yesterday_not_ef`, `twoPowDeferral_f` (FAF's
  `doublingDeferral` is `2^n`), `doublingDeferral_strictlyIncreasing`,
  `const_one_not_doublingPatient`.
* **T7a/b/d** (`Scope`, real sequences against FAF's `ctsInd`/`weightedAverage`): the hovering
  quote `aHover` (`aHover_straddles`, `aHover_highRamp_sum_le`, `aHover_lowRamp_eq_zero`,
  `aHover_cesaro_tendsto_zero`, `aHover_uniform_bias_tendsto_zero`); the repaired dichotomy
  `hard_dichotomy`, `hard_dichotomy_not_hasLimitPoint`, `hard_dichotomy_deletion_test`; dithering
  `dither_high_kills`, `dither_low_kills`, `dither_one_sided_kills` under the side-density
  hypothesis, and K5's literal claim refuted by `sparseDither_highRamp_sum_le_one`.
* **T8a** (`Agent`): `agent_defects_io` over `AgentCoupling` (the sell trader `sellTrader`,
  `sellTrader_ec`).
* **T8b and T8a's corollary** (`Baseline`): `truthStar_cesaro` (the family of record's density),
  `blind_baseline` (the prediction-blind defector's average reward `→ 1`, over the inductor
  instance; `blind_baseline_of_computable` rests on li-pseudorandom's OPEN T7 and is listed open),
  `agent_reward_limit_point(_of_pos)` (the coupled agent's average reward exceeds `2` infinitely
  often).
* **Open** (`Open`): `diagonal_sides_pseudorandom` (T7e), `paper_kleene_exact_pinning` (E2).

Not reached: T5h, T8c, E3 — see `run/wp/li-diagonal/li-diagonal-report.md`.
-/
