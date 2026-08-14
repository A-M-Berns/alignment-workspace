# Wikification and normativity round report

Repo-piece verdict: `repo-consolidated / wiki-pending / machine-state-valid / 0 drift-risk files remaining`.

The final combined verdict replaces `wiki-pending` after the separate wiki
repository passes its link and citation checks.

## Attribution

- Prompt-author model: Claude Fable 5 (Anthropic)
- Executor model, repo piece: GPT-5 (OpenAI)
- Date: 2026-08-13

## Durable handoff

- Path map: `FINAL_PATH_MAP.md`, generated from `state/projects.json`.
- Vocabulary sheet: `VOCABULARY_SHEET.md`, generated from
  `state/vocabulary.json`.
- Verdict/status inventory: `VERDICT_STATUS_INVENTORY.md`, generated from
  `state/rounds.json` and the sole claims registry.
- Regeneration: `python3 -m checkers.workspace_state --write-handoff`.

The current verdict source for the φ-regret bridge is its post-refinement README,
not the earlier prompt report. The source string is lowercase and is preserved
verbatim in the inventory.

## Structured state

| file | authority |
|---|---|
| `state/projects.json` | stable project IDs, paths, parentage, status, entry points |
| `projects/normativity/CLAIMS.md` | the sole authoritative claim registry |
| `state/rounds.json` | completed/current round paths, verbatim verdicts where recorded, registered classes and claim relations |
| `state/vocabulary.json` | preferred labels, aliases, deprecations, identifier mappings |
| `PRIORITIES.md` | formally parsed priority IDs, titles and states |
| `state/theorem_interface.json` | theorem-facing objects, stable module IDs, write access and registered soundness references |

Stable IDs are semantic identifiers (`normativity`,
`normativity.legitimacy`, `deference`, claim IDs, round directory names, and
interface/module IDs); paths are mutable fields. `RESEARCH_STATE.md` is a pointer
to the query rather than a second state summary. The three handoff Markdown files
are generated views with freshness checks.

Commands:

```sh
python3 -m checkers.workspace_state --check
python3 -m checkers.workspace_state --json
python3 -m checkers.workspace_state --self-test
```

The query reports 4 project records (3 active, 1 deprecated), 3 registered
claims, 42 indexed rounds, 35 vocabulary terms, 45 priorities, and 7 theorem
interface objects. The self-test injects a stale registered path and fails it
loudly. A separate rename replay changed the active path to
`projects/leverage` in memory and produced
`project normativity: active path does not exist`.

One promotion path is
`prompts/2026-08-10-repo-scaffolding/REPORT.md` →
`Workspace.Smoke.chain_compiles` →
`smoke.chain-compiles` (`lean-proved`, `active`) → current query output.

Statements of record, experiment reports, exact model specifications, and local
scope caveats remain prose/code because they contain the evidence rather than an
inventory projection. Wiki exposition remains outside repo CI.

Machine-state inconsistencies: **0**.

## Rename and consolidation

- `projects/normativity/` is the active line; `Workspace.Normativity` is the Lean
  namespace.
- `projects/normativity/legitimacy/` is the named subproject. The relational
  scorekeeping bridge moved there cleanly on the first attempt.
- Deference remains a separate line and its README explicitly includes
  corrigibility.
- CI, protection payload, path-gate patterns, tests, namespace-shape fixture,
  claims paths, priorities, and live entry points use the post-rename paths.
- The deference roadmap, paper-arc ledger, prose term table, and dispatch queue
  are pointers; exact specifications and verification notes remain in the lab.
- `RESEARCH_STATE.md` is reduced to the canonical state query and wiki pointer.
- Item 35 names the end-to-end module pipeline round and is marked
  `maintainer-specified-later` without a specification.

## Vocabulary

The answerability collision is decided: answerability is relational;
auditability is the record property; efficacy is model-relative causal access.
Efficacy remains unanalyzed beyond the fixture and grant-invariant results. Lean
identifiers and test names using earlier vocabulary remain unchanged by explicit
scope and are deferred to a later naming round.

One other collision remains unresolved: “admission” names docket entry,
certificate permission, and membership in a state-indexed admissible set. It is
listed in `DECISIONS.md`'s author queue and is not adjudicated here.

## Human-register dispositions

| source | disposition |
|---|---|
| `projects/deference/notes/CARTESIAN_FRAMES_DEFERENCE_FOR_HUMANS.md` | mined to Deference; first-pass hidden-label and forward-target readings dropped after the adversarial correction |
| `projects/deference/notes/LI_NATIVE_DEFERENCE_FOR_HUMANS.md` | mined to Deference; philosophical thesis and proposed next target left to wiki exposition |
| `projects/deference/rounds/2026-08-12-corpus-reconciliation/FOR_HUMANS.md` | mined to Deference/Legitimacy; status paraphrases yield to the verification register |
| `projects/deference/rounds/2026-08-12-reachable-corrective-control/REACHABLE_CORRECTIVE_CONTROL_FOR_HUMANS.md` | mined to Deference/Legitimacy; protection-positive gloss dropped because the final verdict is protection-incomplete |
| `projects/normativity/notes/NORMATIVE_LEARNING_INTERFACE_FOR_HUMANS.md` | mined to Normativity/Architecture; aspirational theorem narrative moved out of the lab |
| `projects/normativity/rounds/2026-08-11-phi-regret-applicability/FOR_HUMANS.md` | mined to Normativity; any implication that the theorem already applies dropped in favor of `Near miss.` |
| `projects/normativity/rounds/2026-08-11-phi-regret-bridge/FOR_HUMANS.md` | mined to Normativity/Architecture; only the frozen-interface result retained |
| `projects/normativity/rounds/2026-08-11-phi-regret-learner/FOR_HUMANS.md` | mined to Normativity/Learning; learning-computation integration remains a gap |
| `projects/normativity/rounds/2026-08-11-phi-regret-prep/FOR_HUMANS.md` | mined to Normativity/Architecture; fencing-as-dividing-line gloss dropped after the horizon-sized witness |
| `projects/normativity/rounds/2026-08-13-local-regret-normative-learning/FOR_HUMANS.md` | mined to Normativity/Learning; “the learner has to stop” gloss dropped because the prosecution found transient-target vacuity |
| `projects/normativity/legitimacy/rounds/2026-08-13-relational-scorekeeping-bridge/FOR_HUMANS.md` | mined to Legitimacy; reset-environment and bounded-vindication readings dropped after P6 refinement |
| `projects/normativity/consolidation-aug9/FOR_HUMANS.md` | retained intact with a Normativity wiki `superseded-by` pointer |
| `projects/normativity/consolidation-aug9/INTERPRETATION.md` | retained intact with a Normativity wiki `superseded-by` pointer |

Every removed round-level file has a replacement pointer in its README or paired
verification note.

## Drift and grep audits

The drift sweep enumerated `*FOR_HUMANS*`, `INTERPRETATION.md`, roadmap/arc/
motivation/aspirational language in living READMEs and notes, and all live
references into retired narrative sections. Exact experiment interfaces and
local scope caveats remained; forward targets and broader positioning moved.
`rg` then checked old paths, the old namespace, and project-name uses.

`LEVERAGE_GREP_SURVIVORS.md` enumerates every file with a surviving case-insensitive
hit and assigns the required one-word class. Survivors are historical records or
mathematical uses naming the measure. Drift-risk files remaining: **0**.

## Verification

Passed:

- `python3 -m checkers.workspace_state --check`
- `python3 -m checkers.workspace_state --self-test`
- `python3 -m checkers.run` and `--self-test`
- `python3 tests/path_gate.py --self-test`
- `python3 tests/conservativity.py`
- `python3 tests/name_lint.py`
- `python3 tests/contrib_hygiene.py`
- `WORKSPACE_LEAN=1 python3 tests/run.py`: all eight discovered project runners
  pass, `lake build` completes 2,636 jobs, and the axiom audit accepts 322
  declarations across 15 files using only `Classical.choice`, `Quot.sound`, and
  `propext`.

## Acceptance conflict

The base prompt requests ten wiki Established spot-checks, but the machine-state
addendum permits Established only after claim registration. The sole registry has
three scaffolding/example claims and no substantive research result from the
indexed project rounds. No claim was promoted because new claims and epistemic
changes are out of scope. The wiki must therefore use Open/Aspirational or
unregistered lab-result wording for substantive material; it cannot supply ten
Established research labels without violating the controlling addendum.

## Predictions

- P1: **true** — CI and path-gate payloads named the old project path and changed
  in the same repo change.
- P2: **true** — more than two first-pass human glosses conflicted with later
  prosecution/refinement and were dropped.
- P3: **true** — “admission” remains an unresolved collision and is queued.
- P4: **clean relocation** — the bridge moved on the first attempt and its runner
  passed.

## What this does not establish

No theorem, experiment, registered research claim, epistemic class, or statement
of record changed. The structured interface ledger records only registered
soundness references; all are empty because the relevant research results are
unregistered. Efficacy is named, not analyzed. The wiki does not become an
instruction source.

## Wiki-piece completion

To be filled by the coordinated wiki piece: page tree, internal-link audit,
commit-pinned repo citations, cross-repo consistency counts, external sources,
and final `wiki-live` verdict.

## Outstanding maintainer actions

1. Decide the “admission” vocabulary collision recorded in `DECISIONS.md`.
