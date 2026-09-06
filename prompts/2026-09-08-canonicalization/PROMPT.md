Work in `A-M-Berns/alignment-workspace`.

Your task is to **finish the current legitimacy / normative-induction phase** by landing the mathematics from PRs #85–#87 cleanly, then canonicalizing the repository around the surviving PR87 theory.

This is not another architecture-discovery round.

Treat PR87 as the latest mathematical synthesis and pressure-pass result. PR85 and PR86 are historical inputs and supporting evidence. Where PR87 supersedes them, do not preserve obsolete formulations merely because they landed earlier in the stack.

## Primary goals

1. Land the cumulative mathematical content of PRs #85, #86, and #87 onto `main` in a clean way.
2. Avoid leaving `main` temporarily or permanently in a state known to have the PR85 axiom-audit failure.
3. Canonicalize the wiki/specification layer around the PR87 object graph and theorem spine.
4. Register the central Lean results at their correct evidence levels.
5. Demote/archive superseded intermediate theories and terminology.
6. Leave a short, exact research frontier containing only:

   * genuine open mathematics;
   * realization/integration obligations;
   * intentionally external application contracts.
7. End this phase with one coherent, navigable mathematical theory.

Do not start new speculative theory unless canonicalization reveals a direct contradiction.

---

# 0. Resolve the stack and landing strategy first

Current stack:

```text
main
  ↑
PR85  round/2026-09-05-integrity-synthesis
  ↑
PR86  round/2026-09-06-mathematical-consolidation
  ↑
PR87  round/2026-09-07-final-pressure-pass
```

Inspect the actual current refs and CI before acting.

Preferred landing strategy:

> land the **cumulative PR87 head** onto `main` after retarget/rebase/merge verification, and close PR85/PR86 as superseded if that is the cleanest way to preserve history without routing a known-bad intermediate state through `main`.

Do not blindly merge 85 → 86 → 87 if doing so temporarily lands the PR85 audit failure.

Acceptable alternatives include:

* retarget PR87 directly to `main`, verify the cumulative diff, merge it, then close 85/86 as superseded;
* create a maintainer integration branch from current `main`, merge/rebase the cumulative stack there, verify, open one landing PR, and close 85–87 appropriately after landing.

Choose the route that:

* preserves every intended commit/artifact;
* yields a reviewable cumulative diff;
* keeps provenance intact;
* gives green CI before merge;
* does not duplicate changes;
* does not accidentally drop PR85 worker-round evidence.

Record the exact landing strategy and final SHAs.

---

# 1. Treat PR87 as the mathematical source of truth for canonicalization

The surviving theory is:

## Accounted obligation state

The qualitative state is not merely a boundary.

Use the PR87 structure:

$$
\boxed{
O=(B,\operatorname{account})
}
$$

with:

* authenticated history prefix;
* exposed obligation occurrences;
* live docket/ports;
* immutable occurrence anchor;
* proof-relevant current account for every exposed occurrence.

Occurrence identity is distinct from semantic content.

`Initial` is only a constructor for an initial accounted state.

## Integrity evolution

The fundamental trajectory object is proof-relevant:

$$
\operatorname{Evolution}(O_0,O_1)
$$

with every intermediate state explicit and each target account equal to propagation of the source account through its transition.

Preserve composition at a literally shared state.

The derived conservation theorem is:

$$
\boxed{
\operatorname{Evolution}(O_0,O_1)
\Rightarrow
\operatorname{Conservation}(O_0,O_1).
}
$$

Conservation includes:

* no exposed occurrence disappears;
* terminal answer/closure receipts persist;
* live resolution structure is transported faithfully;
* anchoring remains occurrence-specific;
* equal-content occurrences do not collapse.

This is the canonical **Answerability Conservation** result.

## Resolution, not answer-evidence

Preserve the PR87 repair:

```text
Protocol.Resolution : Req → Type
```

means a witness that the anchored requirement has been legitimately accounted for.

An adequate answer may produce a resolution witness.

A valid closure may also produce one.

But:

```text
Fate.answered ≠ Fate.closed
```

and no theorem should say a closure is an answer.

## Settlement

Keep the layers distinct:

1. settlement item available through external boundary (`SetView`);
2. source trustworthiness, when an application needs truth/reliability;
3. internal `Closes` judgment under the warrant/rules at that prefix;
4. authority to use the closure;
5. immutable historical receipt;
6. counterfactual suppression/delay, where relevant, under Robust Openness.

Do not restore a monolithic "Settlement Integrity" hypothesis.

A later rejection of an old `Closes` rationale does not rewrite history. It may create a fresh reconsideration obligation.

## Robust Openness

Canonical per-prefix public predicate is the PR87 form:

```text
RobustOpenActual := ActualOpen ∧ RobustOpen
```

where:

* actual branch is checked explicitly;
* `J` indexes proper counterfactual interventions;
* actual standing is not recovered by a fictional null intervention.

The minimum external contract is:

> provide/certify `RobustOpenActual` under declared scope, intervention semantics, coupling, and protected relation.

Componentwise persistence is a sufficient plugin, not the definition and not a necessary certificate.

## Legitimate Evolution

The fundamental legitimacy object is a trajectory certificate:

$$
\boxed{
\operatorname{LegitimateSegment}(O_0,O_1)
}
$$

containing:

* an Integrity evolution;
* Robust Openness at every state of that evolution.

Endpoint-only openness is rejected by the exact PR87 counterexample.

The convenient consumer relation is:

$$
\operatorname{Legitimate}(O_0,O_1)
:=
\operatorname{Nonempty}(\operatorname{LegitimateSegment}(O_0,O_1)).
$$

Keep the distinction explicit:

* `LegitimateSegment` is fundamental/history-sensitive;
* `Legitimate` hides the witness for downstream consumers.

Composition/transitivity must remain canonical.

Initial-state neutrality must remain explicit: legitimate evolution does not certify that the starting commitments were substantively correct.

## Diachronic Answerability

Do not present it as an independent third top-level pillar.

Canonical decomposition:

$$
\boxed{
\text{Diachronic Answerability to }P
=
\text{Conservation from Integrity}
+
\text{standing/access from Robust Openness}.
}
$$

Use the strongest exact statement actually supported by PR87.

## Qualitative handoff

Canonical public handoff is the accounted obligation state itself, or a named wrapper around it:

$$
\boxed{\mathcal O_P}
$$

containing:

* exposure occurrences;
* immutable anchors/specifications;
* current live docket;
* proof-relevant account/status/lineage.

Do not include:

* evaluation weights;
* probabilities;
* service intensity;
* securities;
* market geometry;
* LI-specific data.

## Normative Induction / Progress

Preserve the edge-loss endpoint:

$$
\operatorname{Prog}
=
\sum_{e,s}
T(e,s)\,
\Lambda_{\operatorname{anchor}(e),s}(\Pi_s)
+
D\left(1-\sum_{e,s}T(e,s)\right).
$$

One service occurrence has one realized response \(\Pi_s\).

Every edge into that service must certify against that same response.

Public practical certificate:

$$
\boxed{
\Lambda_{e,s}(\Pi_s)
\le
M_{es}d_s+\epsilon_{es}.
}
$$

Value-correspondence machinery remains one sufficient plugin.

The exposure-headline Progress theorem is optional and noncanonical.

## NI realization

Retain the realization architecture:

```text
MarketMaker(
  TradingFirm^L
  +
  JointProjectionEnforcer[Compile(O_P)]
)
+
DecisionAdapter
```

Preserve:

* one joint region;
* `d_s = dist∞(b_s,K_s)`;
* `a_s = λ_s`;
* Euclidean projection only internally;
* padding invariance;
* admissibility ≠ value truth;
* joint price feasibility ≠ joint practical-response compatibility;
* accountable compiler failure;
* conditional LI preservation.

---

# 2. Resolve one small type-hygiene issue during canonicalization

PR87 currently has openness semantics indexed approximately by history:

```text
List Nat → Γ → Scenario J R
```

while prose says concern/carrier relations may depend on the docket/state.

Before freezing the canonical API, decide whether the public abstraction should instead be indexed by:

```text
ObligationState → Γ → Scenario J R
```

or:

```text
Boundary → Γ → Scenario J R
```

If changing this materially improves type correctness without changing the mathematics, make the cleanup now and re-prove the trivial structural lemmas.

Do not run another research round over it.

If history-indexing is deliberately retained, document exactly how the application supplies the history→state interpretation needed to recover docket/carrier information.

This should be treated as final interface hygiene, not a new conceptual blocker.

---

# 3. Canonicalize the wiki

Rewrite the core normativity/legitimacy wiki pages so they describe only the surviving theory.

At minimum update:

* `Legitimacy`
* `Integrity`
* `Diachronic Answerability`
* `Openness, Coverage, and Non-Capture`
* `Settlement Interface`
* `Normative Induction`
* `Normative Inductor`
* `Roadmap`
* glossary/naming surfaces as appropriate.

Use the PR87 readiness document plus the corrected canonical API after any small type-hygiene adjustment.

## Canonical presentation order

Prefer this explanatory sequence:

```text
1. Interactive/full history and trusted external interfaces
2. Accounted obligation state O
3. Integrity Evolution
4. Answerability Conservation
5. Robust Openness
6. Legitimate Evolution
7. Qualitative handoff O_P
8. Evaluation / PracticalCert / Progress
9. LI Normative Inductor realization
10. External contracts and research frontier
```

## What should disappear from the mainline explanation

Do not keep obsolete theories in the main narrative merely as historical layers.

Demote/archive:

* PR85 `IntegritySegment` + explicit `ContentLifecycle` as the canonical formulation;
* lattice `SliceLedger` / `LocalConservation` as the main Integrity theory;
* endpoint-only `Leg = Segment × RobustOpen(H_n)`;
* null-intervention convention;
* monolithic settlement-integrity language;
* `Evidence` terminology where `Resolution` is intended;
* general "merge" claims for unary `LocalLaw`;
* headline Progress as the canonical endpoint;
* `EndToEndHypotheses`;
* `(S,R+,P)` presented as an independent Non-Capture certificate;
* practical value vectors as public NI semantics.

Historical pages/artifacts may remain available and clearly marked as superseded/evidence.

---

# 4. Register the theorem spine

Promote only the results whose exact statements are now canonical.

Use the repository's claims/evidence conventions.

Candidate central registrations include the final equivalents of:

### Integrity / evolution

* `Evolution.propagate_toSegment`
* `Evolution.conservation`
* relevant receipt/faithful-carry theorem(s)
* multiplicity witness if the registry accepts witness results

### Legitimate Evolution

* `LegitimateSegment.trans`
* `Legitimate.trans`
* `LegitimateSegment.answerable`

### Robust Openness

* `RobustOpenActual`
* `robustOpenActual_of_persistence`
* exact witness separating counterfactual-only from actual openness

### Progress

* canonical edge Progress theorem;
* quadratic specialization if this is the public NI bound.

### NI realization

* final `Evaluation.progress_bound`;
* `conditional_normative_inductor`;
* `deductive_normative_inductor`.

Be precise about evidence:

* Lean-proved means only the exact theorem;
* conditional means conditional;
* nonvacuity status must be preserved;
* inherited theorem-status limitations must remain visible.

Do not register obsolete intermediary claims just because they were Lean-proved.

---

# 5. Clean the naming and decision surfaces

Review agent-decided/reversible entries from PRs 85–87.

For each:

* promote to maintainer/canonical wording if now settled;
* merge duplicate decisions;
* supersede obsolete decisions explicitly;
* leave still-open rulings queued.

In particular consolidate language around:

* `Resolution`;
* `ObligationState`;
* `Evolution`;
* `Conservation`;
* `LegitimateSegment`;
* `Legitimate`;
* `RobustOpenActual`;
* `PracticalCert`;
* Progress.

Do not leave the repository with three generations of competing names for the same object.

---

# 6. Separate the remaining frontier into three buckets

The canonical roadmap should make the phase transition obvious.

## A. Genuine research

Keep only real mathematical problems, currently including roughly:

* convex representability / compiler completeness for a nontrivial requirement class;
* adaptive affordable scheduling for closed-loop/adversarial dockets;
* quantitative semantic transport constants across ontology/representation change;
* jointly compatible practical-response ecologies;
* endogenous-contest liveness;
* many-parent aggregation only if it becomes mathematically useful.

## B. Realization / engineering connectors

Examples:

* concrete `Protocol` implementation from event history;
* constructing `Evolution` certificates from real history;
* compiler implementation;
* workload→enforcer liability connector;
* edge/response transport checker;
* effective representation plumbing.

Do not call these unresolved conceptual theory.

## C. External contracts by design

Examples:

* settlement/source trust assumptions;
* declared normative scope;
* intervention semantics/coupling;
* protected principal/relation;
* counterfactual/practical semantics;
* evaluator adequacy;
* evaluation measure/transport choice;
* market computability assumptions.

Do not list these as TODOs for the generic theory.

---

# 7. Preserve the historical research record

Do not delete PR85/PR86 round artifacts.

They are useful evidence showing:

* failed formulations;
* counterexamples;
* why the final type is what it is;
* provenance of the compression.

But mark them clearly as historical/superseded where appropriate.

The repository should support both:

* a clean canonical reader path;
* an auditable research-history path.

---

# 8. Verify the final integrated tree

Before merge:

Run all required repository checks, including at minimum:

```sh
python3 -m checkers.workspace_state --json
python3 -m checkers.run
python3 -m checkers.wiki_links
python3 -m checkers.wiki_state_bindings
python3 tests/run.py
```

From `lean/`:

```sh
lake build
python3 ../tests/audit_axioms.py
```

Also run any blanket/kernel gates required by the current `main` workflow.

Do not merge with a red required check.

If retargeting/rebasing changes the head SHA, rerun CI on the actual merge candidate.

---

# 9. Merge and close the stack cleanly

Once the cumulative tree is green and the canonicalization is complete:

1. Merge the final cumulative/canonicalization PR into `main`.
2. Close PR85/PR86/PR87 as merged/superseded according to the chosen landing strategy.
3. In each closed-but-not-directly-merged PR, leave enough metadata/body wording that a later reader can see which final merge incorporated it.
4. Confirm `main` contains every intended round and Lean module.
5. Confirm no duplicate or stale stack branch is accidentally presented as the active specification.

Do not merge unrelated stale PRs.

---

# 10. Final report

Return a compact maintainer report containing:

## Landing

* strategy used;
* final merged SHA on `main`;
* final status of PR85, PR86, PR87;
* any rebases/conflicts/corrections.

## Canonical mathematical spine

Give the final object graph and theorem graph in no more than one screen each.

The object graph should look roughly like:

```text
Protocol / external semantics
        ↓
ObligationState O
        ↓
Evolution
        ↓
Conservation
        +
Robust Openness at every state
        ↓
LegitimateSegment
        ↓
Legitimate endpoint relation
        ↓
Evaluation(O)
        ↓
PracticalCert / PracticalUptake
        ↓
Progress
        ↓
conditional LI Normative Inductor realization
```

## Canonical changes

List which concepts were:

* retained;
* redefined;
* merged;
* demoted;
* archived.

## Evidence

List the central registered Lean theorems and any important status caveats.

## Frontier

Give exactly three lists:

* genuine research;
* realization/integration;
* external by design.

## Final verdict

Use:

### `PHASE CANONICALIZED`

if the repository now has one stable theory and subsequent work no longer needs another generic-legitimacy architecture pass.

Otherwise:

### `CANONICALIZATION BLOCKED BY: ...`

and name only a concrete mathematical contradiction or unresolved type question.

The bar is high:

> After this merge, a new researcher should be able to read the canonical wiki, inspect the theorem registry, and understand what the theory of Legitimate Evolution and Normative Induction actually is without reconstructing PRs 80–87.

If that succeeds, this phase is finished.
