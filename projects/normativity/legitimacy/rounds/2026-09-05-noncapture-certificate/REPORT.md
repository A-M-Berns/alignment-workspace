# Report — Non-Capture certificate minimization

## Verdict

MINIMAL-NONCAPTURE-BILL-IS-ANCHORED-BRANCH-COVERAGE-PLUS-PRINCIPAL-STANDING — actual coverage composes with a silent-prefix clause, live-prefix route persistence-or-replacement, and principal-relative standing, while coupling authenticity, settlement delivery, and evaluator fidelity remain separately typed inputs.

## Result

Fix the application-supplied contract `sigma`, concern scope `Gamma`, intervention class
`J`, protected principal or relation `P`, and authenticated intervention semantics `I`.
For each concern, the proposed certificate has three clauses:

1. `(S)`: if the concern is not live on the actual prefix but is live after an
   intervention, the counterfactual has an adequate route.
2. `(R+)`: if it is live in both, every protected actually adequate route persists, or
   the counterfactual supplies an adequate replacement.
3. `(P)`: wherever the anchored concern remains applicable, `P` stands on its coverage
   carrier, including the successor carrying an authorized disposition's load.

`CoverageActual + (S) + (R+) + (P) -> RobustOpen` is proved in Lean. The proof splits on
actual liveness: `(S)` covers the silent actual prefix; otherwise actual Coverage yields
a route and `(R+)` carries it or replaces it. `(P)` supplies standing.

The component certificate `(Ra),(Rb),(Rc)` preserves route admissibility, target/receipt
efficacy, and registration capability. It implies direct route persistence. It is
strictly stronger away from actually adequate routes, so it is an implementation option,
not the minimal certificate.

Every minimal clause has an exact attack with actual Coverage and the other clauses.
Every component has an exact attack holding the other components fixed. The Lean file
contains the same attacks as closed `by decide` declarations and a nonvacuity witness
inhabiting every interface-theorem hypothesis.

## Coupling bill

Concern identity, target meaning, applicability meaning, agency boundary, and the
protected carrier must be fixed or authentically transported by `I`. They are types of
the comparison, not clauses inferred by the generic theory. `FORGET` shows that internal
recognition makes openness vacuous; `REANCHOR` shows that replacing a two-valued target by
a constant makes a dead route falsely efficacious.

The exterior response policy or strategy stays fixed, while its realized response may
change after a changed inquiry. The principal policy and settlement/evaluator engines
stay fixed unless the declared intervention varies them. Exact fixtures show that
varying the exterior can blame a null intervention for censorship or credit the assessed
process with a compensating route it did not preserve.

An ancestry-excision semantics, a do-style interaction coupling, and policy-class
quantification can each pay the same bill. Each must export coupled histories with the
fixed contract, adequate-route judgments, and principal standing. None is selected.

## Integrity and settlement boundary

Integrity governs faithful recording and use of what enters one history. Non-Capture
governs alternatives in which the process might control entry, challenge, or evaluation.
The settlement engine's independence in generation and delivery is an ambient interface
assumption; faithful recording after delivery is Integrity. Persistence of access under
interventions is Non-Capture only when an application includes settlement access in
`Adeq` or includes settlement-channel interventions in `J`.

The `SETTLEMENT` fixture delays a receipt from exact time `3` to `30`, or suppresses it,
while preserving every Non-Capture clause and Robust Openness. At horizon `10`, terminal
discharge differs. Thus “cannot be delayed or suppressed” is not a standalone clause for
this conclusion. If settlement is the only route, suppression is already visible as a
failure of route availability, efficacy, or registration.

`EVALUATOR` preserves Robust Openness while replacing an anchored closure protocol with
a captured one. Evaluator fidelity belongs to semantic authentication or the practical-
semantics bill, not to this certificate's conclusion.

## Evidence

- `Scenario.robustOpen_of_certPlus`: lean-proved interface theorem.
- `Scenario.robustOpen_of_cert`: lean-proved stronger persistence form.
- `Scenario.clauseR_of_components` and `components_of_clauseR`: lean-proved relation
  between component and direct persistence.
- `Witness.nonvacuity`: lean-proved inhabitation of the full hypothesis package.
- `Witness.attackS_activate`, `attackS_derepresent`, `attackRa`, `attackRb`, `attackRc`,
  `attackP`, and `offAdequate`: lean-proved finite structural witnesses.
- Python scenarios: exact-witness only. They instantiate tables and do not prove a
  general theorem.
- Comparisons with the three external semantics: paper-derived from landed artifacts.
- The certificate's intended interpretation: proposed definition/interface.

## Provisional names

`CovState`, `Scenario`, `RobustOpen`, `CoverageActual`, `ClauseS`, `ClauseComp`,
`ClauseRa`, `ClauseRb`, `ClauseRc`, `ClauseR`, `ClauseRPlus`, `ClauseP`,
`NonCaptureCert`, `StandsOnCarrier`, and the `NC-*` ledger identifiers.

## Deviations

1. The worktree base is `5ff9539`, exactly the dispatch's expected abbreviated head.
2. `python3 -m checkers.workspace_state --json` reported the pre-existing stale generated
   view `state/views/NAMING_AUDIT.md`. This round has no permission to repair `state/**`;
   the defect is unrelated to its additions. The single final repository-wide
   `python3 tests/run.py` invocation consequently failed when the
   `wiki_state_bindings` self-test called the invalid workspace-state emitter. The
   round runner, Lean build, name lint, and dead-pointer check pass.
3. The worktree contained untracked `src/`, tests, the Lean file, and the verbatim prompt
   at intake. Git supplied no generator provenance for them. The executor audited and
   adopted the code, corrected two statement mismatches, and records the inherited
   draft's original generator as `unrecorded` rather than guessing. The prompt's stated
   prompt-author attribution governs `PROMPT.md`.
4. The inherited Python route-persistence predicate preserved every component that held
   on every protected route. The Lean `ClauseR` preserved adequacy only for actually
   adequate routes. Python now matches Lean; the stronger component predicate remains
   separately named. The inherited global target-preservation check also let an
   unrelated inadmissible route spoil a candidate route; it is now checked per route, as
   the landed coverage contract requires.
5. The prompt requests a commit with no trailer other than `Model:` while `AGENTS.md`
   requires both `Prompt-author-model:` and `Model:` when authorship differs. The commit
   follows the binding repository rule; `git commit -s` controls sign-off ordering.
6. The resource guard repeatedly reported `LOADED` because swap-free memory was below
   its threshold and emitted sandboxed `sysctl` parse errors. Its required wait cleared
   after 120 seconds; the safe Lean build then completed successfully.

## What this does not establish

- No external counterfactual semantics is constructed or endorsed.
- The theorem does not authenticate `Gamma`, `J`, `W`, the agency decomposition, the
  exterior coupling, target transport, or applicability transport.
- `(S)` and `(R+)` together re-express counterfactual Coverage by an actual-liveness case
  split. The result does not claim a deeper causal reduction; its value is the exact bill
  and the identification of when actual Coverage contributes.
- The abstract Lean state does not encode the landed interaction patch, target transport,
  or successor issue identity. Those enter as named semantic inputs in the prose
  interface.
- Principal-relative standing is a proposed interface. The repository has not settled
  whether canonical legitimacy may name a protected participant.
- Route existence per concern does not prove joint resource feasibility across `Gamma`.
- Nothing proves that a settlement report is true of the world, that `Closes` is sound,
  that a later overturned closure generates a reopening obligation, or that practical
  evaluation tracks value.
- Settlement delay/suppression can be load-bearing for Answerability even though it is
  invisible to this Robust Openness conclusion.
- Exact Python fixtures pin finite instances only.

## Proposed filings

1. If integrated, add the round to `state/rounds.json` with dependencies on the
   cf-coverage continuity interface and the defeat/standing round; the orchestrator must
   choose the full dependency set for its synthesis.
2. If the Lean headline is judged worth registration under the dispatched program, add
   a `lean-proved` claim whose statement of record is
   `Workspace.Normativity.Contrib.NonCapture.Scenario.robustOpen_of_certPlus` and whose
   documentation is `THEOREMS.md`.
3. Retain as an open integration obligation the authentication of one external
   intervention semantics that instantiates concern transport, coupling, `(S)`, `(R+)`,
   and `(P)` without importing Robust Openness as an assumption.

## Attribution

- Prompt author: Claude Fable 5.1 (Anthropic), relaying a maintainer dispatch.
- Executor: GPT-5 (OpenAI).
- Date: 2026-09-05.

## Outstanding maintainer actions

None reserved by this round. The Proposed filings are integration recommendations for
the orchestrator, not low-confidence decisions reserved to the maintainer.
