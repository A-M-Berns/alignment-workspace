# Report

**Attribution.** Prompt author: user, model not stated. Executor:
Claude Fable 5 (Anthropic). Dispatched and executed 2026-08-23. Branch
cut from live `origin/main` at `299fbd1` (transition-certificates
merge), in an isolated worktree; no concurrent branch consumed.

**Verdict.** `REQUIRES-REVISION`, surviving as revised. The candidate
`I = (A, Y, Gamma : H x A -> P+(Y*), Sigma, Check, cost)` with
optional hidden state loses five components under subtraction and
keeps the rest: `Y*` collapses to one response event; hidden world
state leaves the public interface (needed only to define semantic
success, which is excluded from the core; retained instance-side to
state `Check => Goal` soundness relations); `cost` demotes to
objective annotation; blanket prefix persistence of `Certified` is
refuted by a recency-bounded spec and replaced by citation-grounded
certificate persistence; external identity-bearing liabilities are
confirmed against internalization. Surviving object:
`I = (A, Y, Gamma : H x A -> P+(Y), Sigma)` with laws L1-L5 (finite
witness; citation persistence; observation locality; pinning;
interpretation separation) — typing and boundary disciplines that
prove no theorems. Mathematical content lives in the capability
lattice; the bare object is a waist, not a theory.

The round is at
`projects/normativity/legitimacy/rounds/2026-08-23-certified-interactive-service/`.
47 exact finite tests cover the ten mandatory microcases, all five
embeddings, the RR compilation correspondence, the serviceability
separations, and the boundary fixture. No claim is registered; no
Lean; no wiki edits.

## Findings

- All four submodular-family models embed exactly, with per-request /
  per-function objective preservation recomputed on both sides in
  `Fraction` arithmetic. GK Definition 7 coverage IS the generic
  certificate; GK Definition 8 (self-certifying) is the capability
  closing the semantic/certified gap. ISSC's stated termination
  references the true target and is repaired to the version-space-
  uniform certificate; the consistency-adversary = fixed-target
  coincidence (derived, tested) makes the hidden target analytic.
- Request-Response games are overlapping, not nested: RR embeds as
  instances (the paper's Example 2 value 56/10 is reproduced exactly
  from its Figure 1 arena); a finite-state coalescing recurrent
  fragment compiles to RR with play-level correspondence verified on
  every simple lasso of the compiled arena; identity-bearing same-type
  multiplicity breaks the compilation in both directions, matching the
  paper's own remark that open same-type requests are ignored.
- Serviceability is forced reachability for fixed dockets (solver
  implemented); generalized reachability collapses to reachability
  under absorbing acceptance; RR/Buechi enter only for recurrent
  generation. Individually servable does not imply jointly servable —
  a dynamical interference counterexample with no resource bound.
- Overload separates properties the dispatch listed: eventual service
  survives overload for deadline-free specs under FIFO (waiting time
  diverges); it fails by pigeonhole for perishable specs, checked
  exhaustively over schedules. This sharpens the predecessor round's
  overload deadline note into a spec-relative statement.
- The composition fixture runs both origin cases through an identical
  service path; a vocabulary scan enforces that service sources never
  mention upstream or downstream machinery.

## Deviations

- The prompt's Section V listed the RR paper as possibly available in
  the workspace; it was found locally as arXiv `1406.4648v1` and
  inspected there, with the other four papers' primary PDFs (three
  local, ISSC fetched from arXiv).
- SCD is modeled discrete-event where the paper is continuous, and
  unserved delay is accounted to a finite horizon; declared in
  `PRIOR_ART_EMBEDDINGS.md` with the reason (the translation depends
  only on arrival/purchase times).
- RR strategy synthesis was not implemented; the compilation claim is
  play-level finite-test-supported and labeled CONJECTURE at strategy
  level, per the evidence discipline.

## What was not shown

No general theorem is proved mechanically; DERIVED claims are paper
derivations with finite witnesses. Not established: strategy-level RR
transfer; any transfer of competitive/approximation guarantees outside
each model's exact capability conjunction; a sharp schedulability
condition under load; decidability between coalescing RR and unbounded
multiplicity; that the five laws are jointly minimal (only that each
attempted strengthening failed or collapsed into typing); adequacy of
the capability list beyond the tested models and microcases.

## Provisional names introduced

`certified interactive service`, `ServiceSpec`, `Certificate`,
`ServiceOutcome`, `Servable`, `JointlyServable`, `Schedulable`,
`MonotoneEvidence`, `CoalescingRequests`, and the other capability
names in the taxonomy table. All flagged provisional; the author
decides.

## Outstanding maintainer actions

None required for this research-round PR. Naming and any promotion
remain future decisions rather than merge blockers.

# Follow-up report: certification cleanup pass

**Attribution.** Prompt author: user, model not stated
(`PROMPT-cleanup.md`, verbatim). Executor: Claude Fable 5 (Anthropic).
Executed 2026-08-23 on the open PR #51 branch; no concurrent branch
consumed; the reason interface used for the compatibility audit is the
stipulated frozen summary in the prompt, not any live branch.

**Verdicts** (full statements in the round's
`CERTIFICATION_CLEANUP.md`): A. `SPLIT-VALIDITY-AND-CLOSURE`.
B. `CURRENT-TURN-MODEL-SUFFICIENT-WITH-CONVENTION`.
C. `CLEAN-COMPOSITION`. D. `REQUIRES-REVISION — SURVIVES`, with the
revision now including the validity/closure split.

## Findings

- The dispatch's central charge is confirmed: the original memo's
  "recency-bounded" counterexample to prefix persistence
  distinguished only an incomplete prover from the existential
  predicate. It is retracted. `Certifiable = exists c ValidCert` is
  extension-closed as a theorem of citation locality plus append-only
  receipts; `MonotoneEvidence` is deleted from the capability
  lattice; freshness lives in a new closure-admissibility component
  `Admit_sigma` (`MayClose`), which may lapse without falsifying
  history. Context-dependent acceptance ("the probe is the current
  last step") is INEXPRESSIBLE as a citation-local Check — the judge
  never sees the transcript length — and is typed as admissibility;
  citation locality is not weakened.
- The implementation separates semantics from procedure:
  `ServiceSpec = (C, Check, Admit)` constitutive; `prove` an attached
  prover; `certifiable(...)` a bounded exhaustive decision procedure;
  `prover_certified(...)` explicitly prover-relative; absorbing
  monitors justified by the theorem.
- Online timing: a finite counterexample shows the naive one-step SCD
  encoding changes the achievable online cost profiles; the tick
  convention (an observation action exposing arrivals before the
  decision) restores the source protocol's policy class exactly. No
  new step type added; the convention binds embeddings.
- `Gamma` is stated explicitly as the epistemic response relation;
  the ISSC consistency-adversary lesson is generalized:
  whole-history-consistency presentations preserve adversarial
  strategy semantics against fixed hidden configurations.
- Serviceability is retyped as a notion lattice (ever-certifiable /
  forceable / timely-closable / eventually-closed / bounded-latency),
  every retained distinction separated by a test. Overload defeats
  forceable certifiability under Check-windows, timely closability
  under Admit-windows, and only bounded latency with no windows.
- Reason-waist audit: on all five dispatch cases the frozen `V ⊔ L`
  source sorts suffice; a reason never cites the ServiceCertificate;
  protocol-compliance claims are ordinary contents supported by
  receipts. The three-provenance microhistory is the canonical
  composition fixture. No blocking interface issue.
- Prior-art deltas were conservative: SCD gains the tick convention;
  GK Definition 7 is worded as the existential learner-visible
  `Certifiable` with GK instances lapse-free; ISSC unchanged; RR is
  eventual historical service under coalescing, with waiting-time
  value a latency annotation, not admissibility.

The round suite grew from 47 to 60 tests, all green; the repo-level
runner is green.

## Deviations

None from the cleanup prompt's requirements. The reason-occurrence
stubs live in the round's test file rather than `src/`, because the
service sources are vocabulary-scanned against downstream terms; the
prompt's fixture is unaffected.

## What was not shown

The monotonicity theorem is a paper derivation with finite witnesses,
not kernel-checked. `certifiable(...)` is complete only on bounded
certificate spaces (sufficient for every spec in the round). The
tick-convention equivalence is proved by exhaustive policy
enumeration on one two-scenario instance and argued generally; a
general protocol-equivalence theorem is not stated. Timely
closability has no solver. The reason-waist sufficiency verdict
covers the five dispatched cases, not all possible assessment
structures.

## Provisional names introduced by this pass

`ValidCert`, `MayClose`, `Certifiable`, `Admit`, `LapseFree`, `tick
convention`, and the serviceability notion names (`ever-certifiable`,
`forceable`, `timely-closable`, `eventually-closed`). All
provisional; the author decides.

## Outstanding maintainer actions

None required; PR #51 is left open for the author's closeout review,
per the dispatch's do-not-merge instruction.
