import Cleanroom.Fa.FaDelayBsi.Locality
import Cleanroom.Fa.FaDelayBsi.Defs
import Cleanroom.Fa.FaDelayBsi.Split
import Cleanroom.Fa.FaDelayBsi.Deficit
import Cleanroom.Fa.FaDelayBsi.Pipeline
import Cleanroom.Fa.FaDelayBsi.DeckTT
import Cleanroom.Fa.FaDelayBsi.Anticipated
import Cleanroom.Fa.FaDelayBsi.SelfInstance
import Cleanroom.Fa.FaDelayBsi.Witnesses
import Cleanroom.Fa.FaDelayBsi.Open

/-!
# `fa-delay-bsi` — Delay: BSI Theorem B (price route closed, hardness half open), the deficit bound, anticipated deference

Root module of the package `Cleanroom.Fa.FaDelayBsi` ([[fa-delay-bsi-mandate]]; report
[[fa-delay-bsi-report]], findings [[fa-delay-bsi-findings]], ledger [[fa-delay-bsi-ledger]];
repair round 1 recorded in the report).

| file | content |
|---|---|
| `Locality` | **T1** `EF.denoteWith_eq_of_agree`, `EF.denote_eq_of_agree` (FAF API request), `pgenerable_price_local`, `generatedRat_price_local`: generators read prices through the day, not the deductive state — the **price-route half** of BSI Theorem B's refutation; `constantRoute_generable`, `constantRoute_locality_vacuous`: BSI's actual move (FAF's `ofMachineRatCodes`), untouched by the locality lemmas — its denial is the sources' hardness claim, not formalized |
| `Defs` | `violWeight`, `frozenWeight`, `FreezeSchedule`/`blockOf`, `ClosesWithinBlocks` (strict; BSI's horizon excluded, `not_closesWithinBlocks_of_horizon_T`), `ClosesByBoundary` (inclusive; `closesByBoundary_of_horizon_T`), `withinFreezeUpdate`, **T5** `DeckTrustQuote`/`DeckTT`/`DeckTTConst`, `accelerator` (+ `accelerator_eq`), `AnticipatedQuote` |
| `Split` | **T2** `violWeight_le_frozen_add_displacement` (ramp-value case split, no `δ`–`ε` relation), the refined live form, **W2** `bsi_split_wrong_threshold`, BSI Lemma 4's constants, **T3 (i)** finite sums |
| `Deficit` | **T4** `deficit_finite_sum` (+ quote and live forms) over `LUV.expect`; `liveCredence`, `frozenCredence`, `liveCredence_horizon` (strict clause), `realized_horizon_T` (BSI's horizon); the T1 instance `quoteRampAbove_price_local` |
| `Pipeline` | **T9** `pipeline_pigeonhole`, `pipeline_bound`, `pipeline_deficit` (sequence-level conservation law) |
| `DeckTT` | **T5** `deckTT_robust`, `deckTT_of_pair`; `expect_tendsto_of_determinedVia_tendsto`; **T7** `factoring_of_convergent_gate`, `deckTT_const_accelerator` |
| `Anticipated` | **T8** `anticipated_deference` (+ `_le`), `future_quote_pinned`, `forcingA_future`; **T10** `realized_violation_frequently_pair`; **E2** `gate_closes_of_realized_tendsto_zero` |
| `SelfInstance` | **T6** `selfTrustQuote_deckTrustQuote`, `paper_pair_deckTrustQuote`, `deckTT_self_paper`, `deckTT_self_paper_inhabited`, **W3** `deckTT_self_paper_nondegenerate`, **W4** `deckTTConst_accelerator_paper_self`, `accelGateCode`, `accelerator_pair_paper`, `deckTTConst_accelerator_paper_self_inhabited` (the only file importing `Construction.Paper.Market`) |
| `Witnesses` | **W1** `frozen_not_finite_witness`, **W5** `no_lower_bound` (sequence-level, N−: constant sequences) |
| `Open` | **T4** `deficit_bound_open` (schedule closing by the boundary), **T3 (ii)** `frozen_divergent_pair_open` (the inductor-level display), **T7** `factoring_of_determined_gate_open`, **T6** `deckTT_self_luv_open` |
-/
