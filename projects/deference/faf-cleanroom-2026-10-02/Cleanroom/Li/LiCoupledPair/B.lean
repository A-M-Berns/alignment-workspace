import Cleanroom.Li.LiCoupledPair.B.Clocked
import Cleanroom.Li.LiCoupledPair.B.Conditioned
import Cleanroom.Li.LiCoupledPair.B.Scheduled
import Cleanroom.Li.LiCoupledPair.B.Counting
import Cleanroom.Li.LiCoupledPair.B.TieBreak
import Cleanroom.Li.LiCoupledPair.B.Sibling
import Cleanroom.Li.LiCoupledPair.B.ConditionedWitness

/-!
# `li-coupled-pair` · angle B: the conditioning route

Root of `Cleanroom.Li.LiCoupledPair.B` ([[li-coupled-pair-mandate]], "Attempt angles", B). Report:
`run/wp/li-coupled-pair/li-coupled-pair-report-B.md`.

* `Clocked`: the fuel-paid quote ledger `clockedSeq` and its `MachineSentenceCodes` certificate
  `clockedSeq_codes` — the conditioning route's one `(c)` (li-quote-lane F8), discharged for every
  table through FAF's one timeout-tolerant polynomial-time evaluation (`traderOutput_mem_FP`).
* `Conditioned`: `A = P | ψ_H` over `DPA0 ∪ prefixProcess ψ_H` is an inductor (`clocked_inductor`),
  the quote package is a theorem over that process (`crossQuotePackage_clocked`, timed, zero (c)),
  worlds, the timing lemma, the `ConditionedPair` carrier (not the two-way pair: `H` reads `P`).
* `Scheduled`: the *scheduled* sequence `ledgerSeq a e` has its certificate under fuel
  domination `FuelDominated` (anson-2-007's `e ≥ Λ` in FAF's cost model: the route's clock at
  the scheduled position) — a hypothesis with **no known instance** (`exists_fuelDominated`,
  OPEN; repair round 2 after audit r2 adversarial B1, which refuted the form first shipped:
  `not_fuelDominated_le`). Why the bound must exceed the payload (`not_perDay_dominated`,
  `not_fuelDominated_le`) and why the schedule cannot pay for the threshold comparison
  (`PayloadClocked`, `fuelDominated_of_payloadClocked`, `payloadClocked_of_fuelDominated_above`).
* `Counting`: T2.2, the quote stream costs at most `t(t−1) < t²`.
* `TieBreak`: T3.3, the ψ-tie-break counterexample, finite-exact and for a logical inductor.
* `Sibling`: T4.1 by conditioning — the frozen clocked record, the sibling inductor, determinacy
  below `N`, nothing injected at or above `N`, stage agreement below `N`.
* `ConditionedWitness`: the N+ instances at `paperDP 𝗜𝚺₁`, and T2.3's `theoremDP_is_steps_form`.
-/
