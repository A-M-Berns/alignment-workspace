# Prompt B — cleanup and compress

Round id: `2026-08-24-cleanup-and-compress`. Project: none (workspace).
Prompt-author-model: Claude Fable 5. Dispatched by the maintainer after #52
merged; cut from `main` at the #52 merge sha. This dispatch grants scope to
file priority items, to land agent-decided entries under §10, and to edit
spec-layer documents. `AGENTS.md` as amended by #52 binds you, including §10's
bar: adopt what you can; reserve only what turns on the maintainer.

## What this round is

The workspace's live documents have grown by accretion: `PRIORITIES.md` is
2,085 lines for 68 items; the wiki's status blocks lag the rounds they
describe; `README.md` and the wiki still describe a deference line as active
when it is paused on a decision; the deference line's kernel-checked results
have no registry; and the dependency view has eleven silent entries. None of
this is research. All of it makes the repository harder to read for the next
round and for the paper.

The governing constraint is **nothing is lost**: a sentence leaves a live
document only if its content is in a round record that a pointer still
reaches, or the item it belonged to is closed with a statement of record.
Compression is relocation and pointer-repair, never deletion of content that
exists nowhere else.

## Rulings

**R1 — Item numbers are permanent.** `answers_item`, `depends_on`, and wiki
bindings key on them. Compression never renumbers.

**R2 — Closed items collapse.** A closed priority item becomes: its title line,
one status line (what closed it, the statement of record or the round), and
pointers. The body moves nowhere because the round record already holds it;
confirm that before cutting, and if the round record does not hold it, the
body stays.

**R3 — Open items keep their body but lose their history.** Superseded
narrowings, "as of round N" paragraphs, and status updates that a later status
supersedes are cut; what remains is the current statement, the current
narrowing, and the consuming round if any.

**R4 — The wiki states current status only.** Status blocks bind to state
(`wiki/CONVENTIONS.md`) and say what is registered, what is open, what is a
living note, and — for deference — that the line is paused and on what.
History belongs on history pages or in round records.

**R5 — `depends_on` may be read from `PROMPT.md`.** A round's dispatch is part
of its record. Where a REPORT is silent and the PROMPT names what the round
builds on, the field records that, with `"depends_on_source": "prompt"` on the
record so the two sources stay distinguishable. Still no inference.

**R6 — The deference line gets a registry.** `projects/deference/CLAIMS.md`,
created under the same rule that governs normativity's: `kind: lean`, class
`lean-proved`, one entry per theorem a round's report presents as a result.
This retires friction F3 as a friction entry.

**R7 — Worktrees are ignored.** Add the `.gitignore` line for agent worktrees.
No gate; the friction entry records that the maintainer ruled a gate
unnecessary for an ignore rule, and closes.

**R8 — A dead-pointer check exists.** Friction F6 (a pointer into a
superseded tree still resolves and nothing says it is stale) is fixed here as
a contained gate: every repository-relative path in the live documents
(`README.md`, `AGENTS.md`, `CONTRIBUTING.md`, `PRIORITIES.md`, `DECISIONS.md`,
`PROVENANCE.md`, `wiki/`, each project's `CLAIMS.md` and `notes/`) resolves,
and any path under a tree whose `README` or `FORWARD.md` declares it
disposable or superseded is listed with that status. Null input: a document
citing a path that does not exist fails; a document citing a path under a
declared-superseded tree without saying so fails.

**R9 — The naming audit is prepared, not run.** Naming is the maintainer's by
batched audit (§6). This round produces the sheet the audit needs and does
not rule on any name.

## Work packages

### WP1 — `PRIORITIES.md`

Apply R1–R3 to all 68 items and the friction section. Expected result: under
800 lines. Report the before/after line count per section and, for every
item, the disposition (collapsed / trimmed / untouched) and the round record
that now holds the cut body. `workspace_state --check` must still count 68
priorities, and every `answers_item` in both registries must still resolve.

The *Where ingenuity is the bottleneck* section is not compressed; it is
reread for items that #52's queue triage moved or answered (Q3's queue entry
is the live one) and made consistent with the queue.

### WP2 — Wiki

- `wiki/Deference.md`: status block says the line is **paused** on the
  settlement decision (the trilemma — pointwise, classwise, or weakened
  target; see `projects/deference/` for the round that posed it), that the
  kernel-checked results are registered (after WP4), and that the impossibility
  results are the line's companion findings. Nothing about the line reads as
  in progress.
- `wiki/Legitimacy.md` and `wiki/Normative-Record-and-Inquiry.md`: cover the
  reason-state waist, transition certificates, and the certified interactive
  service at the level the page's existing sections cover earlier rounds — one
  paragraph per component, what it fixes, what it consumes (from `depends_on`),
  its status under §9's vocabulary. Apply the `𝓡_n` / `N_{≤n}` split #52
  adopted, which that entry left to the next round to touch the page.
- `wiki/Normativity.md`: check the status block against the registry after
  #52; trim the φ-regret arc to a history pointer if a history page exists,
  otherwise leave it.
- `wiki/Home.md`, `wiki/Architecture.md`, `wiki/Roadmap.md`: reconcile with
  the above; Roadmap lists open items only and each open item points at its
  priority item number.
- The relation-to-field page is **not** written. If the wiki lacks the
  placeholder, add a one-line stub saying it is the maintainer's to write.

### WP3 — `README.md` and `CONTRIBUTING.md`

Read both against the current tree. Fix what is false (layout section,
command list, gate count, any description of the deference line). Do not add
sections. Report each change as before/after.

### WP4 — Deference registry (R6)

Enumerate the theorems the deference rounds present as results (the Bridge,
Adjunction, TotalTrust, reachable-corrective-control, exposure-geometry,
envelope-dominance, faithful-acceleration, magnitude-prediction rounds and
whatever else `lean/Workspace/Deference/Contrib/` holds) from their REPORTs;
create `projects/deference/CLAIMS.md`; register each with `answers_item`
where a deference item exists and a new filed item where the report answers
a demand no item states. The registry checker and axiom audit pass. Confirm
each declaration appears in a `#print axioms` line. State in the REPORT the
count and which results were left out and why.

### WP5 — `depends_on` from prompts (R5)

Extend the round-record check to accept the optional `depends_on_source`
field. Fill the eleven silent entries from their `PROMPT.md` where it names
consumed rounds; leave `[]` where the prompt is silent too, and list those.
Re-emit `rests_on`.

### WP6 — Naming audit sheet (R9)

`state/views/NAMING_AUDIT.md`: every name marked provisional in live
documents and Lean identifiers, one row each — name, where it is introduced,
where it propagates (Lean / wiki / prose), the round that proposed it, and the
alternatives that round listed if any. Grouped by line. No recommendations.
This is the input to the maintainer's batched naming audit and nothing else.

### WP7 — Friction (R7, R8) and pointer repair

Land the ignore line and the dead-pointer gate with its null-input fixtures,
wire it into `ci.yml` and `tests/run.py`, and run it against the tree; repair
every pointer it finds, or annotate the superseded-tree ones. Update the
friction section: F6 and F9 close; F1/F2 stay merged-and-deferred; F4 stays
(its decision is in the queue).

## Non-goals

Research edits of any kind. The legitimacy pressure test (next round). The
relation-to-field page. Renumbering. Editing any round's PROMPT, REPORT,
README, or MEMO. Ruling on names.

## Acceptance

- Suite, all gates, `workspace_state --check`, both registry checkers, and the
  axiom audit green; Lean builds in CI.
- `PRIORITIES.md` under 800 lines; 68 items; every `answers_item` resolves.
- The dead-pointer gate is green on the tree and its null inputs fail.
- No wiki page says the deference line is active.
- `state/views/NAMING_AUDIT.md` exists and contains no recommendation.
- `git diff --stat` shows no file under `prompts/*/` or `*/rounds/*/` changed
  except `state/views/`.

## Report

`prompts/2026-08-24-cleanup-and-compress/REPORT.md` and the round record
(`depends_on: []`, this is a workspace round). Sections: per-item disposition
table for WP1 with the record holding each cut body; wiki changes as a list of
status-block befores and afters; README/CONTRIBUTING befores and afters; the
deference registry table; the `depends_on` fills with their source; the
naming-sheet row count by line; the dead-pointer gate's findings and repairs;
deviations with reasons; what was not shown — in particular that compression
moved content and established nothing, that the deference registry asserts
kernel checks and not that the paused line's theorems are the ones wanted, and
that `depends_on` from prompts is a reading of dispatches, not of what the
executor in fact used.

Attribution block on the PR; `Model:` trailer per commit. Auto-merge **on**:
this round is mechanical and every acceptance check is a gate. Reserve nothing
you can decide.
