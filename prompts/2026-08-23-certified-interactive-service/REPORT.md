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
