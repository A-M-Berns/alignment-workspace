# Evidence ledger

| ID | statement | status | evidence |
|---|---|---|---|
| PL-S1 | Blum--Mansour Theorem 18 uses source-action-conditioned learners, a transformation-weighted stochastic matrix, a stationary mixed action, and the stated row update. | SOURCE-THEOREM FACT | Blum and Mansour (2007), §7, Theorem 18 |
| PL-S2 | With the item-29 bridge, `N=8`, `M=1`, `K=9` gives horizon-tuned expected mixed charge regret `O(ell_max sqrt(8 T log 9))`. | SOURCE-DERIVED | Theorem 18 + bridge ledger PB-D1/PB-D2 |
| PL-E1 | The implementation contains eight rows, nine program weights per row, and the source transition/update objects. | EXACT-TEST-SUPPORTED implementation | state, dimensions, transition, update tests |
| PL-E2 | The stationary selector returns exact stationary vectors for the represented decimal weights, including reducible/non-unique cases. | EXACT-TEST-SUPPORTED | communicating-class, absorption, and `p=pQ` tests |
| PL-N1 | Changing Decimal precision from 50 to 90 alters the declared test outputs by less than `1e-40`. | NUMERICAL CONTROL | precision test; not exact-real proof |
| PL-X1 | Uniform play has linear lawful repair regret on the adverse fixtures; the Φ learner's measured max regret per round decreases over the declared horizons. | NUMERICAL EXPERIMENT | `EXPERIMENT_RESULTS.md` |
| PL-X2 | Zero regret against the nine programs need not minimize charge. | NUMERICAL WITNESS + EXACT TEST | persistent fixture at `T=96`: Φ charge 48 and regret 0; Hedge charge about 9.782 |
| PL-D1 | `o(T)` expected Φ-law regret retires positive asymptotic expected mass on represented uniformly saving admitted repairs. | LEAN-PROVED UPSTREAM + DERIVED | bridge PB-L3 + PL-S2 |
| PL-A1 | Sampled canonical actions produce well-formed, faithful, non-erasing, response-service-feasible repository histories on all `T=96` fixtures. | EXACT-TEST-SUPPORTED finite audit | integration tests and table |
| PL-A2 | Comparator legality remains independent of learner profitability for the exact nine-program class. | FINITE AUDIT | inherited item-29 non-capture audit + class test |
| PL-O1 | The learner computation fits a declared bounded service model and its state is historically answerable. | OPEN / BLOCKING INTEGRATION | current service schema has no computation coordinate or learner-state record |
| PL-O2 | The numerical executable trajectory equals the ideal real-arithmetic source learner. | OPEN / NOT CLAIMED | Decimal update is controlled approximation |
| PL-O3 | A sampled-path/high-probability regret bound. | OPEN | requires sampling theorem |
| PL-O4 | One anytime learner has the same asymptotic guarantee. | OPEN | current learner is horizon-tuned |
| PL-O5 | The nine programs cover normatively important correctable failures. | OPEN | PL-X2 demonstrates weakness |
