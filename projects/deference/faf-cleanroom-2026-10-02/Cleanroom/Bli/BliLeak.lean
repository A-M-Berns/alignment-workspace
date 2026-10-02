import Cleanroom.Bli.BliLeak.Leak
import Cleanroom.Bli.BliLeak.Trader
import Cleanroom.Bli.BliLeak.Transport
import Cleanroom.Bli.BliLeak.Exploit
import Cleanroom.Bli.BliLeak.Neighbour
import Cleanroom.Bli.BliLeak.Rate
import Cleanroom.Bli.BliLeak.Instance
import Cleanroom.Bli.BliLeak.Computable
import Cleanroom.Bli.BliLeak.Closed
import Cleanroom.Bli.BliLeak.Counterlogical
import Cleanroom.Bli.BliLeak.Witnesses

/-!
# `bli-leak`: post-hoc editing refuted; counterlogical conditioning is not an object

Root module of the package `bli-leak` (area `bli`, namespace `Cleanroom.Bli.BliLeak`). The BLI
construction (Appendix B of the Understanding Trust paper, both decks) prices the *large*
sentences by fiat and asserts the result is still a logical inductor "since it agrees with `ℚ` on
small prices". This package makes the failure of that argument a theorem, in two layers, and fixes
the vocabulary of "counterlogical conditioning" for the BLI area.

* **Leak** — definitions of record (families `8`/`9`, `member`/`memberAtom`, `leakAtom K n`,
  `leakCoef`, `leakTrader`, `leakHistory`, `pendingBound`) and **L3.1** `leakHistory_E1x`: the leak
  market agrees with the base on every day-small sentence.
* **Trader** — **L3.2** `leakTrader_ec`: the leak-reading trader is efficiently computable
  (`ofTradeBlocksBig` over `serialize_price`; K1), with the atom-family lemma
  `machineSentenceCodes_atom_of_machineDigits`.
* **Transport** — **L3.0** `posthoc_transfer_refuted`: the sources' transfer is false, by
  transport of FAF's PE1 witness through `E1x` (`cxPerturbed_E1x`,
  `cxPerturbed_not_logicalInductor`); grade (a), closed at `𝗜𝚺₁`.
* **Exploit** — **L3.3** `leakTrader_exploits`: over any inductor with a pseudorandom
  late-decided e.c. family, the leak trader exploits the leak market; the abstract finite-prefix
  refutation `posthoc_transfer_refuted_late_of`.
* **Neighbour** — **L3.7** `exploits_leakHistory_iff`: a trader that never reads a leak is
  unaffected (the surviving neighbour at this level).
* **Rate** — **E1** `no_early_read_large`: a sentence large on day `k` is unreadable before a day
  of order `2 ^ (k / E)` (singly exponential; the mandate's rate corrected).
* **Instance** — **L3.5** `leak_instance_exploits` over `paperDP T` with `li-pseudorandom`'s
  `unionStar` family; `hworld` for the union proved here; the two OPEN statements of record
  (`leakStream_computable`, `leakDP_computable`: `li-pseudorandom` T7).
* **Computable** — **L3.6** `leakHistory_computableMarket`: a computable market with a computable
  stream planted on computable edit days is a computable market (the recogniser read off
  Foundation's `Formula.toNat`).
* **Closed** — the closed forms resting on T7, including **L3.4** `posthoc_transfer_refuted_late`.
* **Counterlogical** — **L8**: `adjoinSentence_stage_unsatisfiable`,
  `counterlogical_criterion_vacuous`, `conditionedHistory_junk` (junk value `1`), the vanishing
  prices, and Ω's quote as a definition.
* **Witnesses** — the N+ rows.

Deliverables: `run/wp/bli-leak/` (report, findings, ledger, open list).
-/
