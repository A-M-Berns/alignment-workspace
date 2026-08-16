# Wikification and normativity round report

Verdict: `repo-consolidated / wiki-live / machine-state-valid / 0 drift-risk files remaining`.

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
- GitHub's live `main` protection was updated after the first repo commit was
  pushed. Read-back confirms the required context is
  `consolidation-verification — the normativity consolidation re-proves itself`,
  with all seven required checks and the remaining protection settings intact.
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

The wiki is live at commit
`4da6aa8d6aa774d980e2d24806af01fb6ee0e022`. Its 22-page tree comprises Home;
Architecture; Roadmap; Glossary; Sources; the Normativity overview, statics,
quantitative, learning, Legitimacy, answerability/auditability/efficacy, and
write-access/laundering pages; and the Deference overview plus focused pages on
Logical Induction, *Deference Done Better*, the corrigibility program,
delegation versus simulation, prediction versus authorization, corrective
reachability and foreclosure, competence and calibration, and current
boundaries/open questions.

All 26 repository citations are pinned to repo commit
`6d3bb2b49f0419bc90943f9cfad3be4a2c7bf147`. The local handshake reports:

```text
CROSS-REPO STATE: valid — 21 repo pointers, 65 internal wiki links, 26 pinned repo citations, 0 Established claims, 35 vocabulary terms, 7 interface objects
```

Unresolved repo-to-wiki pointers: **0**. Unresolved wiki
Established-claim-to-registry references: **0**. Total cross-repo
inconsistencies: **0**. The Established spot-check list is empty: no substantive
research claim is registered, so the wiki has zero Established claims rather
than manufacturing the requested ten. All substantive research interpretations
are `Open — unregistered`; Roadmap content is Aspirational.

The Sources page gives full entries for the external works actually used:
Brandom; Garrabrant et al.; Blum and Mansour; Williams; Walley; Lorenzen and
Lorenz; Prakken; Hunter, Polberg, and Thimm; Fischer and Ravizza; and Dorst,
Levinstein, Salow, Husic, and Fitelson.

## Outstanding maintainer actions

1. Decide the “admission” vocabulary collision recorded in `DECISIONS.md`.
2. Decide in a later naming round whether code identifiers and test names should
   be aligned with answerability/auditability/efficacy; this round deliberately
   left them unchanged.

## 2026-08-14/15 — PR #32 reconciliation and editorial pass

### Attribution

- Prompt-author model: GPT-5.6 Sol (OpenAI)
- Executor model: GPT-5 (OpenAI)
- This is a fixing pass on the existing round, not a new research round.

### Dependency repair

Live inspection confirmed the deadlock exactly. PR #31's head
`5772dd1f5dc857f77ad0663a49d9135775f7533f` had seven successful substantive
checks, including
`consolidation-verification — the leverage consolidation re-proves itself`.
Protection instead required
`consolidation-verification — the normativity consolidation re-proves itself`,
which that head could not emit.

The emitted context was added before the impossible one was removed; all other
protection settings were unchanged. The head was then re-read, remained exact,
and PR #31 was squash-merged by the repository's one-commit convention. Merge
SHA: `c49a7317be30d9c8ab2fd78b7c15d4e5722e0701`.

After reconciliation, PR #32 head `76b65e5cc327ca2f334e829a76548514813ab4b0`
emitted the stable context `consolidation-verification` successfully. Only then
was live protection migrated by adding the stable context before removing the
temporary one. Read-back confirms strict mode; the other six required contexts;
zero required approvals; code-owner review off; admin enforcement on; and force
pushes and deletions blocked.

### Crown-jewel reconciliation

The existing #32 commits were rebased over merged `main`. The only rebase
conflict was the new Lean contribution inside the renamed directory; it was
resolved as
`lean/Workspace/Normativity/Contrib/SurgicalRepairBound.lean` in namespace
`Workspace.Normativity.Contrib.SurgicalRepairBound`. The complete research tree
now has one current path:
`projects/normativity/rounds/2026-08-13-crown-jewel-learning-theorem/`.

The direct round runner exposed one stale sibling-path assumption after the
Legitimacy relocation. Its bridge import now resolves through
`projects/normativity/legitimacy/rounds/`; the 72-test suite then passed. The
round's `FOR_HUMANS.md` was mined into the wiki and removed, and its README and
provenance point to the maintained human register.

All three crown-jewel dispatches are indexed. Intermediate verdicts remain
verbatim and point forward to the final pass. The final pass governs the current
artifact with the separate verdicts
`NORMATIVE-RESPONSE-LEARNING-THEOREM-SETTLED` and
`BM-FEEDBACK-DYNAMICS-WITNESSED`. Its structured component statuses preserve:

- abstract theorem: settled at the stated conditional/interface level;
- dynamics: witness strength;
- `Due`: no satisfactory substantive instantiation;
- `Licensed`: interface discipline available, substantive soundness open;
- performance/loss: fixture success, general theory open;
- coverage: a hypothesis, not a delivered conclusion.

No crown-jewel result was registered or assigned an epistemic class.

### Machine state

Current query counts:

| object | count |
|---|---:|
| project records | 4 (3 active, 1 deprecated) |
| modern registered claims | 3 |
| foundation claim sources | 1 |
| foundation claims | 180, derived from the ledger ID column |
| indexed rounds | 45 |
| vocabulary terms | 35 |
| priorities | 45 |
| theorem-interface modules | 8 |
| theorem-interface objects | 10 |

`state/foundations.json` exposes `normativity.consolidation-aug9` as a legacy
claim source governed by its own ledger, verification document, and runner. It
is explicitly not the modern registry. `workspace_state --json` reports modern
claims and foundation claims separately and mechanically verifies the path,
ledger, verifier, and derived count.

`state/theorem_interface.json` now records `Due`, `Licensed`, performance/loss,
`A`, Due-to-selector compilation, compiled surgical repairs, the Blum–Mansour
engine, positive margin, coverage, and compiler loss-blindness. Coverage is
marked as a quantitative property of `Due`; compiled repair is a compiler
output; margin is not implied by licence. All soundness-claim lists remain empty
and all registered statuses remain null.

Priority project ownership and dispatchability now come from an explicit
`workspace-priority` annotation beside each item. The parser contains no numeric
range table and no special case for item 35. An in-memory item numbered 947
resolved to Normativity and dispatchable solely from its annotation.

The authoritative state remains `state/*.json`, the sole
`projects/normativity/CLAIMS.md`, and annotated `PRIORITIES.md`. The three
handoffs remain generated views. Research arguments, statements of record,
round reports, and wiki exposition remain prose because they are evidence or
interpretation rather than inventory state.

Machine-state inconsistencies: **0**.

### Wiki reader walks before editing

**New researcher.** Home named the three lines but led immediately to internal
terms such as relational scorekeeping and recommended an Architecture page whose
first substantive object was a seven-row ledger containing module IDs and file
paths. The central learning question and the reason Legitimacy bridges the lines
were recoverable, but not within one screen without prior vocabulary. The
22-file sidebar presented eight Deference facets as peer destinations, so there
was no obvious conceptual reading order.

**Returning collaborator.** The old Architecture page was one hop away but
described the pre-crown interface. Corrigibility required two hops and then
several false starts among prediction, simulation, reachability, competence, and
the staged-program pages. Roadmap was directly reachable. Evidence existed but
was distributed as long inline path-oriented citations.

### Wiki restructuring

The wiki moved from 21 substantive pages plus `_Sidebar.md` to 13 substantive
pages plus the sidebar.

Before:

```text
Home
Architecture / Current Boundaries / Roadmap / Glossary / Sources
Normativity
  Statics / Quantitative / Learning / Answerability-Auditability-Efficacy
  Legitimacy / Write Access and Laundering
Deference
  Logical Induction / Deference Done Better / Corrigibility Program
  Delegation vs Simulation / Prediction vs Authorization
  Corrective Reachability / Competence and Calibration
```

After:

```text
Home
The Research Program
  Architecture
Normativity
  Overview
  Reasons, Answerability, and the Score
  Normative Response Learning
Legitimacy
  The Bridge
Deference
  Overview
  Logical Induction and Deference
  What Deference Requires
  Corrigibility
Reference
  Roadmap / Glossary / Sources
```

Merges and replacements:

- Statics and Quantitative became **Reasons, Answerability, and the Score**.
- Answerability/Auditability/Efficacy and Write Access/Laundering became sections
  of **Legitimacy**.
- Learning Theorem Program became **Normative Response Learning** and absorbed
  the final crown-jewel boundary.
- Logical Induction Background and *Deference Done Better* became **Logical
  Induction and Deference**.
- Delegation/Simulation, Prediction/Authorization, and Competence/Calibration
  became **What Deference Requires**.
- Corrigibility Program and Corrective Reachability/Foreclosure became
  **Corrigibility**.
- Current Boundaries was removed; line-specific boundaries now sit beside each
  line's status, while aspirational direction remains on Roadmap.

There are no forwarding-only pages, duplicate overview pages, orphan pages,
broken internal links, or stale deleted-page titles.

### Readability spot checks

| section | old shape | new shape | reader-path effect |
|---|---|---|---|
| Home opening | program inventory and register policy | two ordinary-language research questions, then the three-line map | establishes the problem before vocabulary or repository machinery |
| Architecture | machine ledger first | two conceptual diagrams and the three primitive interfaces before the exact ledger | gives the table a purpose before asking the reader to parse it |
| Normative learning | aspirational pipeline followed by pre-crown local-regret boundaries | interface → compiler → conditional theorem → dynamics witness → missing substantive theory | separates what the theorem provides from the normative sockets it assumes |
| Legitimacy | three micro-pages split definitions, write access, and laundering | one bridge argument connecting answerability, auditability, efficacy, and write boundaries | lets a reader see why the bridge matters without reconstructing cross-page dependencies |
| Deference | eight peer pages, each restating status caveats | one overview and three question-driven pages | distinguishes epistemic deference, requirements, and corrigibility in a single reading order |

Status is now scoped by section-level blocks and compact component tables rather
than repeated before each paragraph. Evidence is collected in end-of-section
subsections with human-readable link text and immutable targets.

### Reader walks after editing

**New researcher.** The first Home screen now states the problem, distinguishes
Normativity from Deference, and explains Legitimacy as the process/trajectory
bridge. Architecture explains the conditional learning socket before notation
and states both the rough result and the missing `Due`, `Licensed`, performance,
and coverage theory. No repository knowledge is required.

**Returning collaborator.** The current learning interface is one sidebar choice
away at Architecture or two through Normativity; corrigibility is one nested
choice under Deference; Roadmap is top-level reference navigation; formal
evidence is the final section of each technical page. No route requires more
than two obvious conceptual choices. Remaining friction is substantive rather
than navigational: efficacy and the resource-separation account are still thin,
and the pages say so.

### Synchronization

- Wiki commit: `d86c9d79191d3e73d18be564866b1516dc525cc3`.
- Repository SHA pinned by the wiki:
  `76b65e5cc327ca2f334e829a76548514813ab4b0`.
- Repo-to-wiki pointers: 23.
- Internal wiki links: 34.
- Commit-pinned repository citations: 38.
- Established claims on the wiki: 0, because no substantive result is
  registered.
- Vocabulary records structurally compared: 35.
- Interface objects structurally compared: 10.
- Cross-repo inconsistencies: **0**.

The handshake now compares Architecture IDs, producers, consumers, write
access, loss exclusions, presentation requirements, status, and soundness claim
IDs field-by-field. The Glossary's machine-significant index is compared against
preferred labels and aliases. An Established label requires a structured claim
ID whose registered class exactly equals the displayed class.

### Negative controls

All twelve required controls fail loudly without leaving broken state:

1. stale registered project entry point;
2. duplicate stable project ID;
3. missing foundation ledger;
4. incorrect foundation inventory count;
5. arbitrary priority 947 resolved by explicit metadata;
6. Established label with the wrong epistemic class;
7. Architecture producer mismatch;
8. Architecture write-access mismatch;
9. stale repo-to-wiki page link;
10. active `projects/leverage` current-state path;
11. project display-name change with unchanged stable protection context;
12. successful `consolidation-verification` emission by exact PR #32 head before
    the live requirement changed.

### Verification

Passed:

- `python3 -m checkers.workspace_state --check`: 4 projects, 3 modern claims,
  1 foundation/180 foundation claims, 45 rounds, 35 terms, 45 priorities,
  10 interface objects.
- `python3 -m checkers.workspace_state --json` and `--self-test`.
- `python3 -m checkers.run` and `--self-test`: 3 modern claims, one adjudicated
  by the Python registry checker.
- `python3 tests/path_gate.py --self-test`.
- `python3 tests/conservativity.py`: 3 Lean specification files unchanged in
  shape and no axioms.
- `python3 tests/name_lint.py`: 114 in-scope Markdown files clean.
- `python3 tests/contrib_hygiene.py`: 0 contributed checkers.
- `WORKSPACE_LEAN=1 python3 tests/run.py`: 9 project runners green and full Lean
  build green.
- `python3 projects/normativity/consolidation-aug9/tests/run.py`: 107 tests,
  180 ledger claims, 26 frozen inputs.
- `python3 projects/normativity/rounds/2026-08-13-crown-jewel-learning-theorem/tests/run.py`:
  72 tests.
- `lake build Workspace.Normativity.Contrib.SurgicalRepairBound` and full
  `lake build`: 2,639 jobs.
- `python3 tests/audit_axioms.py`: 327 results across 16 files, all within
  `Classical.choice`, `Quot.sound`, and `propext`.
- Generated-handoff freshness check.
- `cross_repo_check.py --self-test` and the full local repo/wiki handshake.
- Live branch-protection and exact-head CI read-back.

The survivor audit contains 125 files: 123 historical and 2 mathematical-measure
uses. No live old project path or namespace remains.

Final verdict:
`crown-jewel-absorbed / machine-state-current / protection-stable / wiki-humanized / wiki-synchronized / 0 inconsistencies`.
