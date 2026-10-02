import Cleanroom.Fa.FaEisenstatConj.Defs
import Cleanroom.Fa.FaEisenstatConj.Computable
import Cleanroom.Fa.FaEisenstatConj.GenRefuted
import Cleanroom.Fa.FaEisenstatConj.Companion
import Cleanroom.Fa.FaEisenstatConj.Transfer
import Cleanroom.Fa.FaEisenstatConj.SamStructure
import Cleanroom.Fa.FaEisenstatConj.Witnesses
import Cleanroom.Fa.FaEisenstatConj.Open

/-!
# `fa-eisenstat-conj` — Eisenstat's conjecture stated over FAF

Root module of the package `Cleanroom.Fa.FaEisenstatConj` ([[fa-eisenstat-conj-mandate]]; report
[[fa-eisenstat-conj-report]], findings [[fa-eisenstat-conj-findings]], ledger
[[fa-eisenstat-conj-ledger]], open list `fa-eisenstat-conj-open.txt`).

| file | content |
|---|---|
| `Defs` | **T1** `priceLuv` (the LUV whose expectation is the price), `mergeMarket` (`𝔼^∗` as a market), `MergeQuotes` (the good-feedback package of record, all sentences), `decodeSentence`, `samQuote` |
| `Computable` | **T2** `QuoteTable`, `mergeMarket_computableMarket` (the market half of the criterion, proved) |
| `GenRefuted` | **T4** `buyOneDaily` (+ certificate), `botQuotes`, `gen_refuted_of` / `gen_refuted_notInductor` ((Gen) refuted in the ∃-over-`Q` reading, at the substituted quote `⊥` — a disclosed (c); the note's own instance is OPEN); **S1** `mixedQuotes`, `gen_refuted_mixed_of` (honest on the even days, `⊥` off them: still not an inductor unrestricted, as the note says); **§ E** `TraderSupportedOn`, `InductorOn` (the criterion along a day-set — the note's "inductor on the subsequence" as an object), the certified parity traders `buyTopEven` / `buyTopOdd`, `gen_refuted_mixed_oddDays` (the fallback's odd-day complement, refuted) |
| `Companion` | **E1** `mergeMarket_asympEq` (Claim 2 on every sentence), `mergeMarket_dominates` (+ below), `mergeMarket_lemmaP`, `mergeMarket_provind` (+ neg, decided, even days — the surviving neighbour) |
| `Transfer` | **E2** `damped`, `damped_not_inductor` (per-sentence, even uniform, asymptotic equality to an inductor does not transfer the criterion) |
| `SamStructure` | **T5** `SamPair` (Sam's information structure, two-way), the regimes, `samPair_mergeQuotes` (yields the package of record), the transferred positives `samPair_asympEq` / `samPair_provind` / `samPair_beh_limitPoint` (fixed sentence) / `samPair_beh_limitPoint_seq` (varying sentence, given the uniform certificate), `samEst` (the merge estimate on LUV families) |
| `Witnesses` | W1 (the all-sentences mirror pair, N+ for the package), W2 `gen_refuted` (N+ markets/trader, N− quote data) / `gen_refuted_evenDays` / `gen_refuted_mixed_oddDays_w1` / `honestQuote_noFeedback_w1_computable`, W3 `decided_w3` (N+), E2 `asympEq_not_transfer` (N+); the only file importing the LIA compiler |
| `Open` | the OPEN rows: **T3** `inductor_half_noExploit`, `inductor_half`, `inductor_half_w1`; **T5** `samPair_beh_seq` (Prop A on a varying sentence), `samPair_beh` (its fixed-sentence case, derived), `samPair_trust_half`, `samPair_exists`; **T4 / S1** `gen_honestQuote_noFeedback_w1` (the note's own (Gen) instance), `fallback_evenDays_noExploit` / `fallback_evenDays_w1` (the note's fallback proper) — a leaf, imported only here |

Scope: one-way (corpus construal, Abram's version) everywhere except `SamStructure` and the T5
rows of `Open`, which are two-way (Sam's structure, ATTRIBUTION-UNVETTED, `partial: over the OPEN
pair`). Dependents should import `Defs` (light) or `Computable`; nothing in `Defs` imports a
`Construction.*` module or any `Cleanroom.Fa.FaTheoremA.*` module.
-/
