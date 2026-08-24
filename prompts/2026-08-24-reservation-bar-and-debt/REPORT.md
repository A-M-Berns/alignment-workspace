# Report — reservation bar and epistemic debt

**Attribution.** Prompt author: Claude Fable 5 (Anthropic). Executor: Claude
Opus 5 (Anthropic). Dispatched and executed 2026-08-24. Branch
`round/2026-08-24-reservation-bar-and-debt`, cut from `origin/main` at
`3ebd33b`, in an isolated worktree.

**Verdict.** Rules landed and applied once: the queue goes from thirty-seven
entries to three, and twenty-four kernel-checked headlines enter the registry.

## 1. What changed in the rules

`AGENTS.md`:

- **§6** — retitled *Names ship provisional*. The round chooses the name and
  marks it; the queue takes a naming item only when the name is about to reach
  Lean identifiers or wiki vocabulary and the round cannot choose between two
  candidates; naming authority is exercised as a batched **naming audit**. The
  gates-table row is retitled to match.
- **§9** — gains *Closed means a statement of record*: a component is closed
  only when a Lean declaration or a checker invocation stands for it and its
  reopening condition is a checkable event, and **open** and **living note** are
  the only other verdict forms.
- **§10** — keeps the listing rule and the standing example; loses the
  *cost of deciding / cost of waiting* framing and the "should normally be
  short" diagnostic; gains three paragraphs: *What may be reserved* (the bar,
  with the turns-on line), *Otherwise the round adopts its own recommendation*
  (agent-decided, reversible, rejected alternative named), and *Merging is a
  pull-request fact*.
- **§14** — *Reporting is the obligation; fixing is not* is replaced by *A
  contained fix belongs to the round that hits it*, with the dead-pointer case
  kept as the smallest instance rather than as a separate exception.
- **§15** — gains *A residual blocker is filed, not narrated*.
- *Provenance* — gains *What a round consumed*: `depends_on` as a required
  field, the two failure directions the check covers, and the derived
  `rests_on`. The model-attribution paragraph now states the per-commit trailer
  check and its scope.
- *Claims registry and epistemic classes* — gains *A Lean headline registers at
  merge* and *`test-supported` is the ceiling for finite-model work*, the second
  saying that the ceiling is the vocabulary working rather than a defect, that a
  finite result becomes load-bearing by Lean port, and that a round needing a
  new property form may still add one.
- *Demand-gating* — the *Naming is not relaxed with it* paragraph is cut; §6
  holds the rule and that paragraph now contradicted it.
- Gates table — three rows added or retitled: the Lean scope decision, the
  round-record check, and the per-commit trailer.

`README.md` *For AIs*: item 5 says naming is settled by batched audit and that
*what is worth proving* is exercised through filing scope, so a kernel-checked
headline registers rather than waiting for a ruling; item 6 asks for the
contained fix as well as the report.

`CONTRIBUTING.md`: the Lean row of the submission table asks for the `CLAIMS.md`
entry alongside a headline; *Review* gains one paragraph saying a merge is never
a queue entry; the local-command list gains the two new gates and its
"two gates have no local form" sentence becomes five.

`DECISIONS.md`: the queue preamble is four paragraphs — the single queue, the
turns-on requirement with the adopt-instead default, merge is never an entry,
and chat rulings are in force only once dated. The file preamble gains the
append-beneath-same-dated convention.

## 2. The queue triage

Thirty-seven entries, not the eighteen the dispatch expected — see *Deviations*.
Three are kept.

| entry | disposition | where it landed |
|---|---|---|
| Merge PR #51 | **done** — merged at `3ebd33b`, and a merge is never an entry | removed |
| Who owns the enforcement outflow account | **adopted** — market-owned; source-owned rejected | `NORMATIVE_SAFETY.md` §12; `outflow.py` docstring |
| Whether the outflow clause broadens `P2` | **adopted** — sibling clause under the stated shared principle; broadening rejected | `NORMATIVE_SAFETY.md` §12 |
| The exhaustion behaviour | **adopted** — quarantine plus tolling, and the API default; refusal-at-admission rejected | §§10, 12; `force_api.py` default; one test retargeted |
| Whether the account may be replenished | **adopted** — never; bounded-global and new-era-into-the-same-account rejected | §12; `outflow.replenish` docstring |
| Vocabulary for "admission" | **naming, decided** — *admission* keeps docket intake; *admissible edit*; *response class* | `wiki/Glossary.md` |
| Read `checkers/` | **not a decision** — maintainer reading is not a queued item | removed; recorded once in the dated entry |
| The Stage V review surface | **adopted** — all three rulings, which is how `PRIORITIES.md` already marks them | dated entry |
| A second theorem-facing interface in structured state | **adopted** — the emitter reads a list | `checkers/workspace_state.py`; friction entry retired |
| The traderized force interface as a living note | **adopted** — it is one | dated entry; §9's living-note form |
| Two-channel architecture, Coverage–Liability, where force is published | **adopted** — architecture yes; names to the audit; one paper with force as a module | dated entry |
| Whether `P1` names an obligation | **adopted** — an obligation; naming a mechanism rejected | dated entry |
| Fourteen provisional names, traderized enforcement | **naming** — to the audit | removed |
| `world-inclusive region` and `coverage(Due)` | **adopted** — not related; a later identification must exhibit the map | dated entry |
| Whether the traderized inequalities are worth registering | **registration** — not a decision | `CLAIMS.md` |
| The deck's path-gate entry | **adopted** — it stands; reverting rejected | dated entry |
| The deck's review status | **adopted** — the field takes two values; the qualification moves to the notes | `PROVENANCE.md` |
| F4, the answerability layer's code | **kept** | queue |
| Pinning the Cartesian frames formalization | **done** — the pin is `c0d885bf`, on the upstream default branch, carrying `CartesianFrames/`; the mirror deletion is filed | item 52 |
| Q3 graduation, and the successor to item 28 | **kept** | queue |
| The source line's frontier in this line's ledger | **stale** — the ledger was compressed to five lines on 2026-08-15 and has no Movement I | removed |
| Whether endpoint-preservation is a target | **kept** | queue |
| The identity a wiki pull request opens under | **already ruled** in conversation, 2026-08-16 | dated entry |
| Counterfactual-legitimacy vocabulary | **naming** — to the audit | removed |
| Whether that round's open questions become items | **filed** | item 59 |
| The two formalization obligations | **filed** — the erasure discharged and registered; `DistanceComplete` open | items 48, 49 |
| Assessment-process vocabulary | **naming** — to the audit | removed |
| Whether the per-commit `Model:` trailer is enforced | **adopted** — enforced where the body names a model; dropping the requirement rejected | `tests/attribution.py` |
| Projection round names | **naming** — to the audit | removed |
| Merge upstream Formalized-Agent-Foundations #2 | **done** — merged at `c0d885bf`, which is the pin | removed |
| Whether the projection results are worth registering | **registration** | `CLAIMS.md` |
| Whether the deductive region is registered, and against which item | **registration** | `CLAIMS.md`, item 51 |
| Names for the deductive region's constructions | **naming** — to the audit | removed |
| Whether the max–min development is promoted | **registration**; names to the audit; the adapter exists | `CLAIMS.md`, item 50 |
| The reason-state/record naming split | **naming, decided** — `𝓡_n` and `N_{≤n}`; the wiki edit is the next round to touch the page | dated entry |
| Transition-certificate vocabulary and the freeze | **adopted** — names to the audit; the freeze enacted with its reopening condition | dated entry |
| Whether the reason-state interface becomes a living note | **adopted** — it is one, at its round path | dated entry |

## 3. The registered declarations

Twenty-four entries, all `kind: lean`, class `lean-proved`, `docs.verification`
pointing at `projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md`. Every
declaration is named in full in a `#print axioms` line in the library, so each is
one the axiom audit re-elaborates.

| declaration (under `Workspace.Normativity.Contrib.`) | `answers_item` |
|---|---|
| `AssessmentProcess.BudgeterAt_value_eq_of_safe` | 47 |
| `AssessmentProcess.budgetedTrader_netWorth_floor` | 47 |
| `AssessmentProcess.exists_budgetedTrader_exploits` | 47 |
| `AssessmentFirm.trading_firm_dominance` | 47 |
| `AssessmentFirm.no_efficient_trader_exploits` | 47 |
| `EnforcementStrategy.marketValueRat_enforcementStrategy` | 41 |
| `EnforcementStrategy.rowViolation_le_of_intensity_ge` | 41 |
| `EnforcementPreservation.no_efficient_trader_exploits` | 41 |
| `DeductiveEnforcement.enforcement_day_value_nonneg` | 41 |
| `DeductiveEnforcement.enforcement_netWorth_nonneg` | 41 |
| `DeductiveEnforcement.no_efficient_trader_exploits_of_worldInclusive` | 41 |
| `DeductiveEnforcement.isLogicalInductor_of_computableMarket` | 41 |
| `DeductiveEnforcement.witness_market_not_exploited` | 41 |
| `CoherenceModulus.gap_le_of_mixture` | 42 |
| `CoherenceModulus.gap_le_of_net_cover` | 42 |
| `EnforcedCompiler.ProjectionSchedule.end_to_end_effective` | 48 |
| `EffectiveRepresentation.end_to_end_of_constraints_effective` | 48 |
| `DeductiveEffective.deductive_end_to_end` | 48 |
| `MaxMinRepresentation.exists_maxMin_representation` | 50 |
| `MaxMinRepresentation.isPiecewiseAffineOn_maxMin` | 50 |
| `DeductiveRegion.admissiblePatterns_sound` | 51 |
| `DeductiveRegion.admissiblePatterns_complete` | 51 |
| `DeductiveRegion.admissiblePatterns_ne_nil_iff` | 51 |
| `DeductiveRegion.deductiveRegion_eq_convexHull` | 51 |

Items 47, 48, 50 and 51 are filed by this round for the demand these answer;
item 49 is filed open, for `DistanceComplete`. The two coherence-modulus entries
carry `answers_item` 42 with a note saying which half of that item's narrowing
they establish and that the item stays open — the closest honest fit, and the
weakest link in this table.

The handoff note now states Theorem 5 unqualified, names the three end-to-end
declarations, and carries one debt rather than two. Its Theorem 1 no longer says
the market-computability premise is carried.

## 4. The `depends_on` backfill

Sixty records, every one carrying the field. Fifteen carry a non-empty list; the
deepest transitive rest is the certified-interactive-service round, on ten
`ci-only` rounds.

| round | depends_on |
|---|---|
| `2026-08-11-phi-regret-applicability` | phi-regret-prep |
| `2026-08-11-phi-regret-bridge` | phi-regret-prep, phi-regret-applicability |
| `2026-08-11-phi-regret-learner` | phi-regret-prep, phi-regret-bridge |
| `2026-08-13-procedural-legitimacy` | legitimacy-reorganization |
| `2026-08-13-relational-scorekeeping-refinement` | relational-scorekeeping-bridge |
| `2026-08-13-local-regret-normative-learning` | relational-scorekeeping-bridge |
| `2026-08-13-crown-jewel-learning-theorem-refinement` | crown-jewel-learning-theorem |
| `2026-08-13-crown-jewel-learning-theorem-final` | crown-jewel-learning-theorem, -refinement |
| `2026-08-18-projection-enforcement` | traderized-enforcement |
| `2026-08-19-deductive-region` | traderized-enforcement |
| `2026-08-21-internal-answerability` | procedural-legitimacy, relational-scorekeeping-bridge, crown-jewel-learning-theorem, traderized-enforcement, counterfactual-legitimacy, projection-enforcement |
| `2026-08-22-role-parametric-answerability` | internal-answerability |
| `2026-08-23-afoundational-inquiry` | role-parametric-answerability |
| `2026-08-23-transition-certificates` | internal-answerability, reason-representation |
| `2026-08-23-certified-interactive-service` | afoundational-inquiry |

**Empty for silence, not for independence.** These reports say nothing about
what they consume, so the field records nothing rather than this round's guess:
`2026-08-11-phi-regret-prep`, `2026-08-11-stage-iii-fud`,
`2026-08-11-stage-v-li-native`, `2026-08-12-cartesian-frames`,
`2026-08-12-corpus-reconciliation`, `2026-08-12-legitimacy-reorganization`,
`2026-08-13-relational-scorekeeping-bridge`,
`2026-08-13-crown-jewel-learning-theorem`, `2026-08-16-traderized-enforcement`,
`2026-08-17-counterfactual-legitimacy`, `2026-08-23-reason-representation`. The
crown-jewel and counterfactual-legitimacy cases are the ones most likely to be
wrong: both plainly build on earlier rounds, and both describe what they build
on in their dispatches rather than in their reports.

**Empty for independence**, on the report's own words:
`2026-08-18-maxmin-representation` (its source is Ovchinnikov's paper and
Mathlib), `2026-08-11-stage-iv-future-agent` ("the previous round is not
weakened … a different model rather than a correction"), and
`2026-08-12-reachable-corrective-control` ("#26's findings are cited here and
are not reproduced here"). The remaining records are workspace and scaffolding
rounds with no research hypotheses.

The check fails on an unresolvable id, a self-reference, a cycle, and a missing
field; `rests_on` is derived after the cycle check, so the walk terminates. Six
new self-test cases, four of them null inputs.

## 5. Friction, and the branch

| entry | disposition |
|---|---|
| documented-command check; root-document layer check | **merged** into one entry, deferred as the maintainer ruled; both audited clean by hand on 2026-08-17 |
| the deference line has no claims registry | **kept**, with a line saying the headline rule reaches new work and not this backlog |
| a layer's theory is authoritative and its code is disposable | **kept**; the decision is in the queue under R1 |
| a pointer into a superseded tree still resolves | **kept**; the check it needs has a null-input case and nobody has built it |
| upstream work on a feature branch | **retired** — ruled closed on 2026-08-17; mirror-plus-cross-check is the pattern |
| a generated view lives inside a round's directory | **fixed** — `state/views/`, with the three pointers into the old location repaired |
| a merge can drop a ledger entry | **fixed** — `tests/round_records.py` plus the append-beneath-same-dated convention |
| the structured state holds one theorem-facing interface | **fixed** — the emitter globs `state/theorem_interface*.json`, and an empty match fails |
| agent worktrees are not ignored | **kept** — the `.gitignore` half has no null-input case and the gitlink check is a new gate, so this stays filed rather than half-taken |

`round/2026-08-17-lean-gate-scope` is **landed, not dropped**. Both scripts pass
their self-tests unmodified on current `main`; they are taken verbatim, wired
into `ci.yml` and `tests/run.py`, and `GATE COVERAGE` now reports ten gate
scripts with five self-test-only. The branch's own `PRIORITIES.md` renumbering
is not taken: two friction entries were filed after it was cut, so the list is
renumbered here against the current one. Its draft pull request should be closed
as landed.

**Dead branch remnants on `origin`, listed and not deleted.** Deleting a remote
branch is not reversible from here and several of these are checked out in other
sessions' worktrees on this machine, so this is a list for the maintainer rather
than an action taken.

Fast-forwardable into `main`, so certainly redundant (13): `claude/constraint-schedule`,
`claude/deductive-region`, `claude/deductive-schedule`, `claude/fourier-motzkin`,
`claude/fourier-motzkin-uniform`, `claude/maxmin-representation`,
`claude/polyhedral-coverage`, `claude/projection-bridge`,
`claude/projector-generator`, `projection-enforcement`,
`round/2026-08-21-internal-answerability`,
`round/2026-08-22-role-parametric-answerability`,
`round/2026-08-23-afoundational-inquiry`.

Ahead of `main` but whose round is indexed in `state/rounds.json`, so
squash-merge remnants (24): `admin/cleanup`, `agent/legitimacy-research-findings`,
`agent/normative-learning-interface`, `agent/phi-regret-applicability`,
`agent/phi-regret-bridge`, `agent/phi-regret-learner`, `agent/wiki-normativity`,
`claude/leverage-legitimacy-reorganization-u4l0fi`,
`claude/reachable-corrective-control-f4hiw2`,
`integration/2026-08-11-current-state`, `patch/attribution-provenance-names`,
`patch/priorities-and-slop`, `research/phi-regret-prep-20260811`,
`retire/frozen`, `round/2026-08-11-deference-corrigibility`,
`round/2026-08-11-stage-iv`, `round/2026-08-11-stage-v`,
`round/2026-08-12-cartesian-frames-bridge`,
`round/2026-08-12-corpus-reconciliation`,
`round/2026-08-12-time-indexed-corrective-capability`,
`round/2026-08-13-crown-jewel-learning-theorem`,
`round/2026-08-13-local-regret-normative-learning`,
`round/2026-08-13-relational-scorekeeping-bridge`,
`round/2026-08-16-wiki-in-repo-sync`, `round/2026-08-16-wiki-state-bindings`,
`round/2026-08-17-counterfactual-legitimacy`, `round/stage-iv-and-front-door`,
`traderized-enforcement`.

**Not remnants, and not to be deleted:** `round/2026-08-17-lean-gate-scope`
(closable once this lands), `round/2026-08-18-principal-mediated-corrigibility`,
`round/2026-08-24-enforcement-affordability`,
`feat/traderized-constraints-paper`, `claude/for-ais-refinement`, and
`A-M-Berns-patch-1` through `-3` — each carries work no round record indexes.

## 6. Deviations

1. **The queue held thirty-seven entries, not eighteen.** The dispatch's count
   is wrong. Every entry was triaged; §2 is the full table.

2. **Three entries are kept where the dispatch expects one to three, having
   rechecked.** F4 turns on whether the program will keep building on the
   answerability layer; Q3 turns on whether the missing idea has arrived; and
   endpoint-preservation says of itself that it is *what is worth proving*. The
   fourth candidate — the reason-state naming split — was adopted instead, on
   the ground that the round that raised it proposed a specific assignment, so
   R4's "cannot choose between two candidates" does not apply.

3. **The Lean build did not run, and neither did the axiom audit.** The
   resource guard reported `LOADED` (swap at a 92% high-water mark) and
   `safe-lake.sh` refused after its full 900-second wait. Running `lake`
   directly is what the machine-load rule forbids, and the attempt was refused
   by the permission classifier, correctly. The substitutes: this branch changes
   no file under `lean/`, so the build status is whatever `main`'s required
   `lean` job established; the registry checker confirms every registered
   declaration resolves in the library source; and a separate pass confirmed all
   twenty-four appear in full in a `#print axioms` line, so each is covered by
   the audit that will run in CI. A built `lean/.lake` is seeded in the worktree
   (gitignored) if the maintainer wants to run it locally.

4. **The Aug-12 standing item about new harness property forms does not
   exist.** R7 asks for it to be retired as a goal; nothing in `PRIORITIES.md`,
   `DECISIONS.md`, `AGENTS.md` or `checkers/README.md` states it. R7's substance
   is landed in the registry section, including the clause permitting a new
   property form where a round needs one.

5. **No sentence in the claims-registry section implied that harness growth is
   the path for finite results**, so nothing was cut there. The nearest thing —
   the *two ways out of `contributor-checked`* paragraph in the Python regime —
   is about a contributor's own checker being read, which is a different
   mechanism, and it stands.

6. **The legitimacy window holds six rounds, not five**
   (`2026-08-23` carries four). All six were read; the seven named blockers plus
   the counterfactual-legitimacy round's load-bearing question are filed as
   items 53–59, minus the `R → O` compiler, which deduplicates against item 39
   and is recorded there as a narrowing instead.

7. **No `state/rounds.json` verdict said "closed provisionally"**, so none
   needed leaving alone. The phrase lives in the transition-certificates round's
   own `README.md` and `MEMO.md`, which are history. The wiki's Legitimacy
   status block did not repeat it either; what did was one sentence on
   `Normative-Record-and-Inquiry.md`, which now says *living note*, and the
   Legitimacy block gains a living-note paragraph with the freeze's reopening
   condition.

8. **The exhaustion-behaviour adoption changed a default and one test.**
   `compile_safe_force` and `compile_funded_force` defaulted to `refuse`; the
   adopted behaviour is `quarantine`, so the default moved and
   `test_an_unaffordable_request_refuses_by_default` became two tests — the new
   default, and refusal on request. The dispatch names `src/outflow.py`, which
   exposes the policies as functions with no default; the default lives in
   `src/force_api.py`, and changing it there rather than nowhere is the reading
   that makes the instruction do something.

9. **The corrigibility-ledger entry was stale rather than decidable.** The
   dispatch's *has a recommendation* class does not fit it: the document it
   names lost the section the entry is about when the 2026-08-15 consolidation
   compressed it from 471 lines to five.

10. **`.gitignore` was not changed.** The worktree friction entry's cheap fix is
    a one-line ignore rule with no null-input case, which is not *contained* as
    R10 defines it, so the entry stays filed rather than half-taken.

11. **The trailer check shipped matching nothing, and was fixed before the
    pull request was reviewed.** Its body-declaration pattern was anchored to
    the start of a line; the pull-request template's dispatched-round option puts
    `Model:` on a continuation line after `and`, so the check would have skipped
    the very pull request that introduced it and reported green. Found by running
    the gate against the actual body rather than against its own fixtures — which
    is the failure mode `AGENTS.md`'s null-input section says this repository has
    already shipped twice. The pattern now finds the label anywhere on a line and
    excludes a backticked mention, so prose about the gate is not read as a
    declaration, and two self-test cases pin both directions.

## 7. What this does not establish

**Recording a dependency pays no debt.** `rests_on` says the
certified-interactive-service round rests on ten `ci-only` rounds. It has said
nothing about whether any of those ten is right. The view makes an existing
quantity visible and creates no new evidence; a round with a large count is not
thereby suspect, and one with a count of zero is not thereby sound — its
hypotheses may simply come from the frozen consolidation, which the field does
not track.

**The backfill is a reading of reports, and eleven of them are silent.** For
those the field is `[]`, which is weaker than "independent" and is recorded as
such in §4. Two of the eleven — the crown-jewel theorem and the
counterfactual-legitimacy round — almost certainly consume earlier work; their
reports do not say so, and this round did not infer it, because a dependency
graph built from inference would be a graph of this round's guesses wearing the
authority of a checked field.

**Every adoption in §2 is reversible, and none rests on this round's judgment of
the mathematics.** Each was taken on the recommending round's own reasoning:
where that round recommended, this one adopted; where it was indifferent between
options and its own implementation had already chosen, this one adopted the
implemented choice and said so. Under *no negative ontologies* a re-ruling
leaves only the new entry standing, which is why adoption was cheap enough to be
the default. It also means the ledger now asserts, in the maintainer's voice,
fifteen positions no maintainer has read.

**The registry now asserts exactly the traderization headlines and the
scaffolding smoke tests, and nothing else.** Twenty-four theorems from four
rounds, plus two smoke results and one worked enumeration example. It does not
assert the coherence bridge's exactness half, which is `derived` plus
exhaustive-finite and is item 49; it does not assert anything from the deference
line, whose kernel-verified results remain unregistered; it does not assert any
Python result from any round; and it does not assert the safety theorem's
necessity direction, which is item 40 and open. What a headline entry claims is
that the kernel checked that statement, not that the statement is the right one.

**The bar is not self-enforcing.** Nothing gates an entry that lacks a turns-on
line, and nothing detects a round that reserves what it could have adopted; both
are review matters, as the gates table says. The queue is short today because
this round emptied it, not because the rules prevented it from growing.

**The rules were applied once, to the present state.** They have not been tested
against a round that disagrees with them, and the first genuine test is a round
that would rather reserve something than adopt it.

**The Lean build did not run here.** §6.3 states what was checked instead, and
what was not: no declaration was re-elaborated in this round, and the axiom
audit's verdict on the twenty-four registered declarations is inherited from
`main` rather than reproduced.
