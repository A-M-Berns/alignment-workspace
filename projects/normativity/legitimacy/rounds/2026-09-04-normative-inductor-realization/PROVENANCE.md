# Provenance

| Files | Generator | Review status | Date | Originating round |
|---|---|---|---|---|
| `*.md`, `src/*.py`, `tests/*.py`, `lean/Workspace/Normativity/Contrib/NormativeInductor.lean` | OpenAI Codex; prompt-author model unrecorded | `ci-only` | 2026-09-04 | `prompts/2026-09-04-normative-inductor-realization/` |

The maintainer's prompt explicitly granted workspace write scope.  The term
**Normative Inductor** and the internal names `CompilerInput`, `JointProjectionEnforcer`,
and `DecisionAdapter` are provisional.

## Governing sources

- `abstract_normative_induction_realization_contract.tex`, supplied by the maintainer
  outside the repository — exact notation and contract statement, read in full.
- `abstract_normative_induction_realization_contract.pdf`, the same document's render
  — intended exposition, read in full by layout-preserving extraction and page
  rendering.

Neither file is in the repository; the round's summary of the contract in
`NORMATIVE_INDUCTOR_REALIZATION.md` is the only in-repo record of it.

## Repository dependencies

The report consumed as hypotheses only results at the status each source itself claims:

- `projects/normativity/CLAIMS.md` and the linked generalized-LI theorem maps;
- `projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md` and
  `TRADERIZED_FORCE_INTERFACE.md`;
- `projects/normativity/legitimacy/checkpoint-2026-09-01/`;
- the landed `2026-09-02-unified-grounds-answerable-defeat` and
  `2026-09-03-defeat-landing-horty-standing` rounds;
- `2026-08-30-normative-continuity-settlement`, reason representation, transition
  certificates, anchored slices/authentication, coverage/continuity, progress witness,
  progress liability, and progress consolidation rounds;
- `2026-08-31-normative-affordability`, including service typing, joint actionability,
  service transfer, scheduling, and Sharp Timely Service;
- the deference notes on LI-native deference, action semantics, and the legitimacy to
  trust interface.

Historical papers/checkers were read as evidence, not upgraded.  Current state,
registered claims, priorities, decisions, and supersession documents controlled when
historical prose conflicted.

No web source was used.

## Refinement note

The in-place PR82 refinement re-audited the underlying projection-force,
bounded-liability preservation, effective-compiler, service-transfer, and scheduling
theorems rather than relying on the first-pass summaries. It added the focused
`PRESENTATION_AND_VALUE_SEMANTICS.md`, exact-rational counterexamples/tests, and Lean
bridge declarations. No historical consolidated artifact or claims registry was
modified, and no local result was promoted beyond its evidence class.
