# Theorem map

All names are provisional. `SINGLE DERIVATION` means a paper proof given in
`MEMO.md`; `FINITE WITNESS` means an executable exact instance; `FALSE` has a
displayed counterexample; `INTERFACE` is a proposed type boundary. No item is
registered or Lean-checked.

| Item | Exact statement and hypotheses | Status | Smallest failure or repair | Registration |
|---|---|---|---|---|
| A. No New Normative Roots | In a finite accepted record, every post-seed authority act has at least one strictly earlier normative-license parent; only index-zero seed acts may lack one. Every maximal license path terminates at a seed. | `SINGLE DERIVATION`; `FINITE WITNESS` | Roots, self-license, same-index mutual license, and empirical-only license are rejected. Convergent DAG ancestry is accepted and repeated seed identities are deduplicated. Fixed checker semantics remain outside the graph. | not warranted; formal type not frozen |
| B. No Retroactive Evasion | Due tokens are append-only occurrences; removing a standing rule does not remove tokens already emitted by that rule. A token leaves the current docket only through a typed account. | `SINGLE DERIVATION`; `FINITE WITNESS` | Same-step ambiguity is repaired by receipt, accrual, then amendment micro-order. | not warranted |
| C. Docket Completeness | Atomically generating a token and coverage debt ensures every token has a linked liability, open coverage debt, or terminal coverage account. Eventual/bounded docketing additionally assumes processor fairness/capacity or a deadline. | safety form `SINGLE DERIVATION`; liveness conditional | Arrival rate two and capacity one produces linear backlog. | not warranted |
| D. No Forgotten Inquiry | Once docketed as `Do(task)`, an inquiry occurrence has a lineage-linked live/suspended frontier or typed terminal account under the existing No Forgotten Liability hypotheses. | inherited conditional derivation; finite identity witnesses | Equal task content does not contract occurrence identities. | formalization may reuse the existing target after types stabilize |
| E. Service-Specification Integrity | Each inquiry occurrence pins a service-specification version. Changing it requires a licensed, lineage-linked migration. | `INTERFACE`; `FINITE WITNESS` | Rebinding an old task to an empty new specification cannot discharge it. | not warranted |
| F. Certified Service | A terminal service disposition carries an input-scoped certificate whose evidence satisfies the occurrence's pinned specification. | `INTERFACE`; `FINITE WITNESS` | One shared investigation may supply evidence twice, but two old liabilities require two adequacy/account edges. | not warranted |
| G. SCD embedding | Finite elements are task kinds; buyable sets are deterministic inquiry actions; requests are due-token arrivals; buying an action serves exactly pending covered tokens; costs and accumulated delays are copied unchanged. | objective-preserving `SINGLE DERIVATION`; exact finite computation | Repeated purchases are allowed; future requests are not served by past purchases. Finite terminal delay permits permanent nonservice. | literature bridge only |
| H. Coverage from competitive service | Proposed form without a load bound is false. Repaired: if `Cost_A(T) <= alpha Cost_OPT(T)+beta`, one comparator has `Cost_OPT(T) <= B` for all `T`, and an unserved token's delay diverges, then it is eventually served. | original `FALSE`; repaired `SINGLE DERIVATION` | With background cost `T`, ignoring one token gives `Cost_A=2T <= 2(T+1)=2 Cost_OPT`. Under the repair, divergent delay contradicts `alpha B+beta`. | not warranted |
| I. Submodular-docket embedding | For a fixed finite docket, actions are MLSC vertices, context switching is a metric, and each pinned progress function is normalized monotone submodular on visited actions. The inquiry latency sum equals MLSC's sum of cover times. Unit metric gives submodular ranking. | objective-preserving `SINGLE DERIVATION`; exact unit-metric computation | Complementary actions with value only after both are selected violate submodularity. Repeated/mutable actions and changing specifications are outside the model. | literature bridge only |
| J. Afoundational provenance | The authority graph establishes membership in one seed-descended practice under the checker's grammar. It does not establish seed entailment, truth, moral legitimacy, or non-capture. | `SINGLE DERIVATION` boundary | Substantive grounds can be entirely post-seed empirical while authority ancestry remains seed-terminating. | not a theorem of substantive justification |

## Status map

| Component | Status |
|---|---|
| afoundational seed semantics | proposed initialization interface; bootstrapping beneath `S_0` remains open |
| no-new-root property | single derivation; finite adversarial witnesses; unregistered |
| empirical transcript `L_n` | append-only interface; normatively thin by construction |
| minimal `NormativeRecord` event type | current three-constructor typing is insufficient; implemented event family is a witness, not proven minimal |
| grounds/license/account separation | required interface; finite independence witnesses |
| commitment/liability narrow waist | partial unification under tested representation: `Hold`/`Do` contents share account identity; due tokens are operationally distinct; alternate compilations remain open |
| `May`/`Must` rule interface | useful typed interface; not a complete rule semantics |
| due-token semantics | repaired tested interface; immutable occurrence with rule, receipt, time, task, and service-spec versions; representation minimality open |
| event-time accrual | repaired by explicit micro-order; delayed recognition remains policy-relative |
| docket coverage | safety invariant available; bounded/eventual forms need processor assumptions |
| service coverage | conditional liveness only; unconditional bounded form false under overload |
| service certification | version-pinned, input-scoped interface; finite witnesses |
| versioned service specifications | necessary; finite rewrite attack |
| Set Cover with Delay bridge | objective-preserving paper derivation; independent finite computations agree; general scheduler fit conditional |
| submodular ranking / MLSC bridge | objective-preserving restricted paper derivation; independent unit-metric computations agree; complementarity counterexample |
| adaptive stochastic inquiry | tractable special class; fixed realization/prior/objective hypotheses |
| external evaluator role | meta-theoretic benchmark; finite disagreement witness |
| counterfactual non-capture | separate / out of scope |
| `R -> O` compiler | open |
| downstream `O -> C -> K -> E` | existing / unchanged |
