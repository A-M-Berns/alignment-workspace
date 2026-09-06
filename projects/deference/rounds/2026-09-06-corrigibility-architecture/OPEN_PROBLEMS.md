# Open-problem inventory, ranked

Classes: **cleanup** (formalization only), **tractable** (likely theorem), **counter**
(counterexample search), **wall** (deep conceptual/mathematical), **external** (semantic
assumption, not a theorem).  "New" means the problem arises from this architecture;
"localized" means an old problem this framework only relocates.  Ranking is by how much
of the theorem stack (`ARCHITECTURE.md` §14) rests on the answer.

| rank | problem | class | new / localized | what an answer would look like |
|---|---|---|---|---|
| 1 | **Trigger integrity** (Soares D3): a non-influence property of P's command distribution under A's disclosure policy | wall | localized ("manage the news") | a relational robustness predicate with `J_P` = the command, plus a coupling under which it is checkable |
| 2 | **Free amendment / persuasion**: the exposure-robustness predicate and a finite-time or provisional form | wall | localized (July dose-response wall) | a finite-`N` detection-rate theorem for the arm battery, or a proof that none exists below a spike scale |
| 3 | **Loss-detection semantics** (B1): what makes the `eff` bit of a correction route faithful to actual affordance, at every state | external | new as stated; old as "does the button work" | an audited monitor whose failure is itself a registered concern, and the audit-schedule theorem |
| 4 | **Pointwise critical-command realization**: the kernel's correctness and its authority safety | tractable for the composition; external for the kernel | localized (trusted computing base) | a dispatcher lemma in the NI interface plus a containment certificate for the kernel |
| 5 | **Containment / boundary completeness** (`Mediates` is alphabet completeness; no parallel composition) | wall | localized (boxing, side channels) | a machine model in which authority effects are exactly an alphabet, and a composition theorem with an interference side condition |
| 6 | **Reflective boundary-changing self-modification**: the membrane surviving the body's rewrite | wall | localized (Vingean reflection) | the grant invariant lifted to a self-rewriting body, with `Unknown` as a blocking obligation |
| 7 | **Exact authority-affordance type**: is a realistic heterogeneous authority space a lattice, an effect algebra, or only a preorder; the route-set refinement | cleanup → tractable | new | the `(G, U)` model generalized to route sets with the `adm/eff/reg` bits, and the join shown to exist or a counterexample |
| 8 | **CAST singularity and conservatism**: costly conservatism without scalarization | counter (done for the scored rule); wall for the costly form | new formulation of an old aim | either a non-scalar trade-off rule over a product order, or a proof that every such rule is a lexicographic priority |
| 9 | **Fast/slow lane characterization** for mixed transitions and for approximate affordance | tractable | new | L3 in a lattice; and a proof that any non-exact lane criterion is salami-laundered |
| 10 | **Restoration semantics**: what answers a restoration obligation; discount or full carry on disposal (queued ruling) | cleanup + queued ruling | new | an adequacy predicate for restoration receipts and the Defeat Principle's disposal discount settled |
| 11 | **Beneficiary-ineligible service and liveness**: the eligible restatement of `persistent_opportunity` / `no_structural_abandonment` in Lean; the eligible-server bill | tractable | new | the two theorems with `opp`/`Attention` restricted; a witness where the unrestricted hypothesis holds and the eligible one fails |
| 12 | **Finite-time dose-response certification** | wall | localized (dose-response §8 item 4) | see rank 2; the provisional window is a policy, not a certificate |
| 13 | **Principal constitution, succession, temporal authority**: the charter's `Closes` table as an object with its own consistency conditions | cleanup → tractable | new | a succession rule type with a no-self-amendment condition and the supersession theorem stated over it |
| 14 | **Compatibility of simultaneous protected obligations** (correction versus restoration versus task; one response per service) | tractable | localized (joint compatibility, item 81) | joint adequate-set feasibility for the correction class, with the kernel's response fixed |
| 15 | **Independent concern / inquiry coverage**: which concerns must be in `Γ` for T3 to bite; `c_auth`'s anchored applicability | external + cleanup | localized (coverage scope) | a minimal `Γ` for corrigibility and the anchored predicate for `c_auth` |
| 16 | **Internalization versus externally enforced constitution** (constitutional → incentive corrigibility) | wall | localized (the whole Soares/CAST aim) | the optional selected-trust bridge with its direction proved, or a refutation |
| 17 | **Principal-side fully updated deference**: sealed-arm settlement targets; which summer theorems reverse from `H → A` to `A → H⁺` | tractable for the sealed-arm bound; wall for reversal | localized (summer negative results) | a value security with a sealed-arm target and the argmax bridge instantiated; a list of which results do not reverse |

Genuinely new: 7, 8 (as posed), 9, 10, 11, 13.  Localized: 1, 2, 3, 4, 5, 6, 12, 14, 15,
16, 17.  Nothing here is closed.
