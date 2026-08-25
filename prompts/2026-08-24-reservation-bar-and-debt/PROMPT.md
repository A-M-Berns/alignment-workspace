# Round: reservation bar and epistemic debt

Round id: `2026-08-24-reservation-bar-and-debt`
Project: none (workspace regulations). Prompt-author-model: Claude Fable 5.
Dispatched by the maintainer; this dispatch grants scope to file priority items,
to land DECISIONS entries as specified below, and to edit spec-layer documents.

`AGENTS.md` binds you. Read it first, then this. Where this prompt and
`AGENTS.md` disagree, the disagreement is a deviation to declare — this round
*changes* `AGENTS.md`, so a conflict is either intended (listed under Rulings)
or a mistake in this prompt (report it).

## What this round is

Two things are wrong with the workspace's epistemic machinery and both are rule
defects, not effort defects.

1. `DECISIONS.md` *Awaiting the author* holds 18 entries against its own
   "should normally be short." Rounds reserve what they could decide, because
   §10 governs how a reserved item is *listed* and nothing governs what may be
   *reserved*. The queue also holds decisions already made in conversation that
   never landed.
2. Epistemic debt accumulates in forms that are free to pay and unpaid
   (kernel-checked theorems unregistered; a handoff note describing a superseded
   theorem), or untracked (rounds consume earlier ci-only results as hypotheses
   and nothing records the chain), or compounding (residual-blocker lists carried
   forward inside REPORT prose, growing round over round).

This round lands the rulings below as rules, applies them once to the present
state, and stops. It does not compress `PRIORITIES.md`, revise wiki content,
touch the legitimacy or deference research, or pressure-test anything. Those
are later rounds and this one exists so they run under corrected rules.

## Rulings (the maintainer's; land them, do not relitigate)

**R1 — The reservation bar.** An entry enters *Awaiting the author* only if the
round is genuinely low-confidence in its own recommendation **and** can name
what the maintainer has that the round lacks: taste, an idea nobody has yet, or
external knowledge (what a collaborator will accept, what a paper needs, where
the program is going). The entry states, in one line, what the decision turns
on. An entry that cannot state that is a recommendation the round declined to
adopt, and is rejected at review. "Cost of deciding now: low" is a symptom, not
a field; drop that field.

**R2 — Recommend-and-adopt.** A round that has a recommendation adopts it: the
decision lands as a dated `DECISIONS.md` entry marked **agent-decided,
reversible**, naming the rejected alternative in one line. The maintainer
reverses by re-ruling. Under no-negative-ontologies only the live entry
survives, so reversal is cheap and adoption is the default.

**R3 — Merge is never a decision.** Merging is a pull-request fact. Dispatches
either leave auto-merge on (the existing convention) or reserve merge as a
PR-level note. A merge never appears in *Awaiting the author*.

**R4 — Naming ships.** Rounds choose names and ship them marked provisional
(§6's marking rule stands). Naming enters the queue only when the name is about
to propagate into Lean identifiers or wiki vocabulary *and* the round cannot
choose between two candidates. The maintainer's naming authority is exercised
as a periodic **naming audit** — a single batched item the maintainer runs when
wanted — not per-round entries.

**R5 — Lean headlines register at merge.** A round that ships a Lean theorem it
presents as a headline files the registry entry (`kind: lean`, class
`lean-proved`) in the same pull request; the maintainer's merge is the
registration. "Whether X is worth registering" is not a decision. "What is worth
proving" stays reserved and is exercised through priority-item filing scope,
as now.

**R6 — Chat rulings land or are not in force.** A ruling made in conversation
is in force only once it is a dated `DECISIONS.md` entry. The next round
dispatched from that conversation lands it as its first commit. The queue
carries a standing line saying so.

**R7 — Test-supported is the ceiling for finite-model work.** Finite-model
Python results carry their round verdict and the class `test-supported` (or
`witness-checked` / `enumeration-verified` where the house harness actually
adjudicates), and this is not a defect to be repaired by harness growth. A
finite result becomes load-bearing by Lean port, and the dependency view (R9)
is how ports are prioritized. The Aug-12 standing item about new harness
property forms is retired as a goal; new forms are still permitted when a
round needs one.

**R8 — Closed means a statement of record.** A round may report a component
as **closed** only when the thing closed has a statement of record (a Lean
declaration or a checker invocation) and the reopening condition, if any, is
stated as a checkable event. Anything else is **open** or a **living note**.
"Closed provisionally" is retired as a verdict form. Residual blockers named by
a round are filed as priority items under the consuming line, each naming the
round that would consume the answer; they do not live only in REPORT prose.

**R9 — Consumption is recorded.** Every round record in `state/rounds.json`
carries `depends_on`: the round ids whose results it consumes as hypotheses
(not merely cites). The state emitter derives, per round, the set of ci-only
rounds it transitively rests on. This tracks the debt; it does not pay it.

**R10 — Contained friction is fixed by the round that hits it.** A friction
item whose fix is contained (non-retroactive, one gate or one document, with
its own null-input case) is fixed by the round that hits it, recorded as
agent-decided. Only friction whose fix changes a spec-layer rule waits for the
maintainer, under R1.

## Work packages

### WP1 — The rules, as text

Edit `AGENTS.md`, `README.md` (the "For AIs" list, item 5 and item 6 wording),
and `CONTRIBUTING.md` so that R1–R10 are stated once each, in the section where
a reader would look, and nowhere else. Specifically:

- §10 becomes the bar plus the default (R1, R2, R3) and keeps the listing rule.
- §6 becomes R4.
- The "Claims registry and epistemic classes" section gains R5 and R7 and
  loses the implication that harness growth is the path for finite results.
- §9 / §15 gain R8.
- §14 gains R10.
- Provenance section: `depends_on` (R9) is a required field of a round record.
- `CONTRIBUTING.md`: the submission format for a Lean headline includes the
  registry entry; the review section states R3.
- `README.md` "For AIs" item 5: rewrite so "what a thing is finally called" is
  exercised by audit (R4), and "what is worth proving" by filing scope.

Slop discipline applies to rules. A rule sentence that restates another is cut.
Do not add a preamble explaining why the rules changed; that goes in the
DECISIONS entry (WP2) and nowhere else.

### WP2 — `DECISIONS.md`

1. Rewrite the *Awaiting the author* preamble to state R1, R3, R6 in the
   fewest sentences that make a bad entry rejectable at review.
2. Land one dated entry, "Reservation bar and epistemic debt," recording
   R1–R10 with their rationale — this is the only place the rationale lives.
3. **Triage the current queue** under R1. For each of the 18 entries, exactly
   one of:
   - **done** — remove (e.g. the FAF #2 repin item if still present; confirm
     against `lean/lakefile` and the pinned sha).
   - **already ruled in conversation** — land it as a dated entry and remove.
     Known instances: the wiki-PR identity ruling (2026-08-16: Claude's wiki
     pull requests open under a fine-grained token on the maintainer's own
     account, this repo only, contents+PR write, days-long expiry, minted per
     session, never stored; auto-merge OFF for chat-surface wiki PRs;
     machine-account and de-spec-listing options rejected) — check whether it
     already landed before writing it. The Aug-17 friction rulings (F5 closed,
     F7 views to `state/views/`, F8 both fixes, F1+F2 merged-and-deferred): see
     WP5 for their fate.
   - **has a recommendation** — adopt under R2; land as agent-decided,
     reversible; remove from the queue. The four `NORMATIVE_SAFETY.md` items
     (account ownership, sibling clause, exhaustion behaviour, replenishment)
     are of this kind: adopt the round's recommendation on each. For
     replenishment, which the round marks highest-risk, adopt **never** — the
     option the safety theorem is proved for — and name "bounded globally" and
     "new-era allocation" as the rejected alternatives. Each adoption edits the
     clause text in `NORMATIVE_SAFETY.md` §12 (one paragraph each, as the round
     itself sized it) and, where `src/outflow.py` exposes policies, makes the
     adopted one the default.
   - **naming** — decide under R4 and record; the "admission" vocabulary item is
     decided by the round (recommend: *admission* keeps the docket-intake sense,
     since it is the oldest and the one the objection grammar reads; the
     certificate verdict becomes *admissible edit*; the response-set sense
     becomes *response class*). Apply the choice across `projects/normativity/`
     and `wiki/` only where the text is live; round records are history.
   - **not a decision** — maintainer actions that are not decisions (e.g. "read
     `checkers/`") leave the queue. Record once, in the dated entry, that
     maintainer reading is not a queued item: review is `ci-only` by design, and
     the workspace's review mechanism for consumed results is a second executor's
     audit or a Lean port, not maintainer reading.
   - **meets R1** — keep, rewritten to the R1 form: what it turns on, in one
     line. Expect this to be one to three entries. If you find yourself keeping
     more, you are reserving; recheck.
4. Report the triage as a table: entry, disposition, where it landed.

### WP3 — Registry and the traderization headlines

1. Enumerate the headline declarations of the traderized-enforcement arc
   (`2026-08-16-traderized-enforcement`, `2026-08-18-projection-enforcement`,
   `2026-08-18-maxmin-representation`, `2026-08-19-deductive-region`) from
   their REPORTs and the Lean sources under `lean/Workspace/Normativity/`.
   A headline is a theorem the round's report presents as its result, not
   every lemma. `deductive_end_to_end` and `end_to_end_effective` are headlines;
   the assessment-process lift theorems and the max–min representation are
   headlines; a helper lemma is not.
2. File a registry entry for each in `projects/normativity/CLAIMS.md`: `kind:
   lean`, class `lean-proved`, `answers_item` the priority item it answers
   (39–46 or as the report says), provenance from the round, `docs` pointing at
   `projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md`. The registry
   checker must pass; confirm each declaration name greps in the library and
   that `python3 tests/audit_axioms.py` lists nothing beyond the three allowed
   axioms for these declarations.
3. Reconcile `GENERALIZED_LI_PAPER_HANDOFF.md` with the declarations actually
   registered. The note predates PR #41 and describes a theorem with the
   `ComputableMarket` premise and the extra effective-stage hypothesis; the
   registered theorems do not have them. The note states the theorem as proved,
   names each declaration inline, and says what the earlier statement had that
   the current one does not. Do not extend the note beyond what the Lean
   establishes.
4. Update `wiki/Normativity.md`'s status block so the traderization headlines
   are the line's registered results, using the state-binding markers per
   `wiki/CONVENTIONS.md`; the "substantive results are currently unregistered"
   sentences on `Home.md` and `Normativity.md` become false and are rewritten.
   No other wiki content changes.
5. Update `wiki/Roadmap.md`: remove "clearer account of the market-maker
   modification" and "move toward an infinite construction" as open items,
   stating in one line each that the traderized construction superseded the
   modified market-maker and is the infinite-setting form. Everything else on
   the page stays.

### WP4 — `depends_on` and the debt view

1. Add `depends_on: [round ids]` to the round-record schema; `workspace_state.py
   --check` fails on an id that does not resolve.
2. Backfill for every round from `2026-08-11-phi-regret-prep` onward, from what
   each REPORT says it consumes as a hypothesis. Cite-only relations are not
   dependencies. Where a report is silent, the field is `[]` and the report is
   not edited (history). List in your REPORT the rounds you left empty for
   silence rather than for independence.
3. Emitter: a derived `rests_on` section — per round, the transitive set of
   ci-only rounds it depends on, and the count. Demand-seeded per the
   wiki-bindings decision: emit it; bind nothing to it in this round.
4. Null-input fixture for the new check (a record with an unresolvable id
   fails; a cycle fails).

### WP5 — Residuals, vocabulary, friction

1. Under R8, file the residual blockers of the legitimacy rounds
   `2026-08-21` through `2026-08-23` (the five rounds) as priority items under
   `projects/normativity/legitimacy/`, one per distinct blocker, each naming the
   round that would consume it. Known ones: May-rule→scope compiler;
   defeater-uptake completeness (`LostBasis` blind to un-taken-up defeaters);
   Due connection; `Licensed` citation discipline; applicability-in-source
   checker; R→O compiler; composition with the record calculus. Deduplicate
   against `PRIORITIES.md` first. Do not edit REPORTs.
2. Under R8, the "closed provisionally" verdicts in `state/rounds.json` are not
   rewritten — round records are history — but the wiki's Legitimacy status
   block, where it repeats them, says *open* or *living note* per R8.
3. Friction F1–F10 under R10: for each, either fix it in this round with its
   null-input case, or record why it is spec-layer and leave it under R1 form.
   Determine the fate of `round/2026-08-17-lean-gate-scope`: if its two
   commits (`tests/lean_scope.py`; the F8 fixes — `tests/round_records.py` in
   delta form plus the append-beneath-same-dated convention) pass the suite on
   current main, land them; if not, record that the branch was dropped and
   why, and re-file F8's checker as a priority item. Either way the branch's
   fate becomes a DECISIONS line and the draft PR is closed.
4. Dead squash-merge branch remnants on origin: list them in the REPORT. Delete
   them only if your environment permits; a previous round was refused by its
   permission classifier, and the refusal is a REPORT line, not a failure.

## Non-goals

`PRIORITIES.md` compression (next round). Wiki content beyond WP3.4–5 and
WP5.2. Any research edit. Deference. Anything in `frozen`-status trees.

## Acceptance

- `python3 tests/run.py`, `python3 tests/audit_axioms.py`, the registry
  checker, `workspace_state.py --check`, and every gate in `ci.yml` pass; Lean
  builds (`WORKSPACE_LEAN=1`) — WP3 touches nothing in Lean but registers
  against it, so the build is the proof the names resolve.
- `Awaiting the author` has no entry lacking a "turns on" line, no merge, no
  naming item outside R4's exception, no done item.
- Every new gate has a null-input fixture that fails.
- The new registry entries are class `lean-proved` with resolving declarations.
- `rests_on` emits for every round and no id fails to resolve.
- `name_lint` clean; no names in prose.

## Report

`prompts/2026-08-24-reservation-bar-and-debt/REPORT.md`, and the round record
in `state/rounds.json` with `depends_on: []`. Sections, in this order: what
changed in the rules (diff-level, not narrative); the queue triage table; the
registered declarations with their `answers_item`; the `depends_on` backfill
with the silent-report list; friction dispositions and the branch fate;
deviations with reasons; what was not shown — in particular, that recording
dependencies pays no debt, that adopted recommendations are reversible and
were adopted on the rounds' own reasoning, and that the registry now asserts
exactly the traderization headlines and the scaffolding smoke tests.

Attribution: PR body carries the Model-attribution block with
`Prompt-author-model: Claude Fable 5` and your own executor Model line. Squash
auto-merge **off** for this round — the maintainer reads regulation changes.
That is a PR-level note, not a queue entry.
