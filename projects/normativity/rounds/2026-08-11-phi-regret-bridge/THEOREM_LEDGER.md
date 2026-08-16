# Evidence ledger

| ID | statement | status | evidence |
|---|---|---|---|
| PB-L1 | The theorem-facing semantic action type has cardinality eight. | LEAN-PROVED, unregistered | `Workspace.Leverage.Contrib.PhiRegretBridge.semanticAction_card`; Python fixed-size tests |
| PB-L2 | Pointwise loss preservation and a commuting decoder preserve finite-horizon regret. | LEAN-PROVED, unregistered | `Workspace.Leverage.Contrib.PhiRegretBridge.regret_preserved` plus inhabited witness |
| PB-L3 | Mixed failure mass at least `rho*T` with saving `delta` implies expected regret at least `rho*delta*T-B`; deterministic counts are a special case. | LEAN-PROVED, unregistered | `Workspace.Leverage.Contrib.PhiRegretBridge.recurrentFailure_lowerBound` plus inhabited witness |
| PB-T1 | `decode_action` is a bijection from the eight labels to every frozen occasion's canonical response set. | TEST-SUPPORTED | exhaustive exact tests at all declared horizons; abnormal-ledger negative test |
| PB-T2 | All nine comparator maps factor through the labels and close on them. | TEST-SUPPORTED | all `9*8` map entries at every occasion for horizons 12, 24, 48, 96 |
| PB-T3 | Label actual loss, comparator loss, mixed loss, and regret equal their repository quantities. | TEST-SUPPORTED | exact rational equality for all programs and declared horizons |
| PB-A1 | The nine programs and default policy satisfy the finite non-capture condition. | AUDITED + TEST-SUPPORTED | data-only program schema; exact class check; adapter/policy closure audit; capture negative witness |
| PB-D1 | Blum--Mansour Theorem 18 instantiates with `N=8`, `M=1`, `K=9` under the frozen boundary. | DERIVED FROM CITED SOURCE + PB-L1/PB-L2/PB-T1–3/PB-A1 | `PHI_REGRET_BRIDGE.md`, hypothesis table |
| PB-D2 | For each horizon, a horizon-tuned learner has expected mixed-action charge regret `O(ell_max sqrt(8 T log 9))`. | DERIVED FROM CITED SOURCE, not locally reproved | Blum--Mansour (2007), Theorem 18, scaled from `[0,1]` |
| PB-O1 | A concrete item-30 learner meets the bound and remains answerable. | OPEN | item 30 |
| PB-O2 | A high-probability or pathwise sampled-trajectory bound. | OPEN | requires an additional sampling argument |
| PB-O3 | One anytime learner on an infinite run. | OPEN | requires dynamic tuning or a proved doubling construction |
