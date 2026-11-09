# Follow-up on PR #140 — fix what the external review and the maintainer's check found

Continue on the existing branch `round/2026-11-07-score-side-binding` of `A-M-Berns/alignment-workspace`, in the worktree `/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding`. PR #140 is open against `main` at `d3d3542e`. **Do not merge it and do not enable auto-merge.** Do not rebase or squash; add commits.

An independent review of the PR by GPT-6 Astra (OpenAI) ran on 2026-11-08 and is at `/Users/anson/hub/scratch/dispatch-2026-11-07-score-side-binding/astra-review.md`. Read it in full first. The maintainer's check of its findings against the Lean source agrees with its three blocking defects and disputes two of its notes; the dispositions are fixed below. Its verdict was fix-then-merge, and the aim of this follow-up is that the next review finds nothing blocking.

The round's own report and wiki text currently say more than the theorems do. The rule for every fix below: **either prove what the prose says, or cut the prose to what is proved.** Where you narrow, say so in the report under deviations.

## 1. The score-side test (`WarrantInductorScoreSide.lean`)

**(a) Tie the shortfall sentence to the assessment.** `ShortfallAt` ignores its date, is proved live at every date, and enters no scoring proof; the priced sentence `σ` is an arbitrary `Sentence` with no stated relation to it. Make the dependence honest and explicit: the obligation carries a shortfall sentence per date, and a named hypothesis (provisional name `Assessed`) states what the assessment settles it to — true at `n` iff `ShortfallAt n`, with `ShortfallAt` read off the accounted state at `n` (if the fixture's state is constant across dates, say so in a docstring rather than ignoring the argument). The theorems `before`, `after` and `same_question_two_realizations` take the hypothesis and whatever price bound they need, named. Do not build an assessment theory; the hypothesis is the deliverable, and the report lists it as typed.

**(b) Prove the necessity, or narrow the claim.** The report's outcome (b) says the reversal *needs* the epistemic strength row. The Lean shows sufficiency only. Either prove a necessity witness — a market or bundle at date 4 lacking the specialized strength row at which the charged gate's mass on acting is below `24/25` (or the realized decision differs), with the same charge bound — or remove every statement that the test discriminates outcomes (a), (b), (c), in the report, the wiki, the claim notes and the PR body, and say the round establishes a conditional sufficiency result and leaves (a) versus (b) open. Prefer the witness if it is a day's work; narrow if not.

**(c) Label the trivialities.** `market_unchanged` is `rfl` because `scoreSide` stores `WB`. That is the right design, since the charge adds no trader, and it is not a result. Say so in the docstring, the report and the wiki. `no_conduct_row` shows the chosen row is absent, not that no conduct row is present; state it that way.

**(d) The charge bound.** `before` needs `ϖ · price ≤ 19/240`; carry the qualification into the wiki and the claim notes wherever the 24/25 figure appears. Drop the report's "vacuity" scenario for the charge, which is impossible since prices lie in `[0, 1]`.

## 2. Solvency and the robust reading (`WarrantSolvency.lean`, `RobustWarrant.lean`)

**(a)** Fix `wiki/Normativity.md` line 225: "a conflict among solvent rows cannot occur" is false — two contradictory rows each enforced on one instance have bounded cumulative liability. What excludes a valid conflict certificate is validity of all rows at one point. Rewrite the sentence; check `wiki/Normative-Inductor.md` line 76 says only that.

**(b)** State the conflict audit as what `suspect_in_bundle` proves: at every cube point some positively weighted bundle row is violated — not one row violated everywhere. Where the prose says a conflict "proves a mis-admission", add the premise that admission demands validity at the point in question.

**(c)** Add the theorem that applies the repository's grounded survivor rule (`Grounds.survivors`) to the eight-world fixture at the contrary-challenge record, so "neither rebuttal nor undercut removes the row" is a statement about the actual rule and not only about `settleForm` and `undercut` separately.

**(d)** The graph bridge `graph/nodes/robust.eight-world-strengths.bridge.md` credits both strengths to a statement of record that proves only `3/5`. Register the conjunction (`robustStrength_all ∧ robustStrength_defeated`, or a theorem stating both) as the statement of record, or narrow the bridge to what the registered declaration proves.

## 3. Admission by standing (`AdmissionByStanding.lean`)

`standing.reallocated-entitles-nothing` is registered without a term inhabiting its hypothesis package under `protocolS₁`. Construct it: an `Initial` and `ObligationState` over `protocolS₁`, and an `Entitlement` on the witness's grounds with every origin at obligation `1` (admitted under `J₁`, account live, `Expresses := True`). Register the witness beside the claim and add it to the axiom-audit list. If the construction fails for a reason you can state, deregister the claim and say why.

Correct `graph/nodes/item-128.md`: the node carries `item_status: closed` while only the admission half of clause (a) landed and `Expresses` remains typed. Set the status and the narrowing note to what is true, and regenerate `ATTENTION.md` with `python3.12 -m checkers.attention_render --write`.

## 4. The report and the registry

- Remove the correction at `REPORT.md` line 16 claiming the dispatch cites `PRIORITIES.md`; the committed dispatch does not. Check every other correction against the committed `PROMPT.md` before keeping it.
- Declare the deviation that the gate is `GatedChoice.softGate` on charged scores rather than the dispatch's named `DecisionComponent.permWeight` / `cgate` or `BRIACorrigibility.evalOf`, with the reason.
- Extend *What this round does not establish* with whatever of the following survives your fixes: the assessment interpretation of the shortfall sentence; the strength row's necessity; the survivor-rule theorem; the reallocated witness.
- Cut repetition: the exposition inventory and the merge recommendation restate earlier sections. The report should be shorter after this follow-up than before it.
- Add a section **External review** recording the GPT-6 Astra review: commit its text verbatim as `prompts/2026-11-07-score-side-binding/REVIEW-astra-2026-11-08.md`, attributed to GPT-6 Astra (OpenAI) via `codex`, and list each of its findings with its disposition: *fixed* (with the commit), or *disputed* with the reason. Two dispositions are already decided: the missing `Prompt-author-model:` trailer is **disputed** — `AGENTS.md` requires it only where prompt author and executor differ, and both are the same model here; the "new `softGate` construction" is **disputed** as to novelty — it is the consolidation round's existing machinery — and the deviation is declared instead under this section's second bullet.
- Update the claim notes in `projects/normativity/CLAIMS.md` for `scoreside.same-question-two-realizations` and `solvency.conflict-names-suspects` to the narrowed phrasing. Do not change any class.
- Update the PR body to match: the round's result as narrowed or as strengthened, the new witness, the external review and its dispositions. Keep the **Model attribution** section and the closing line `🤖 Generated with [Claude Code](https://claude.com/claude-code)`.

## Scope

Nothing beyond the list. No new matters, no changes to the consolidated theorem, no specification-layer files, no reopening of landed rulings. The queued exposure-rule entry stands as the maintainer's.

## Verification

Full Lean build with `~/.claude/scripts/safe-lake.sh build Workspace` from `lean/` (never `lake` directly; `~/.claude/scripts/resource-guard.sh check` before every build and sweep, and `wait 3600` if LOADED). Then `python3.12 tests/audit_axioms.py`, `python3.12 tests/run.py` (with `lean/.lake` set aside and new files added), `python3.12 -m checkers.run`, `python3.12 -m checkers.workspace_state --check`, `python3.12 -m checkers.wiki_state_bindings`, `python3.12 -m checkers.wiki_links`, `python3.12 -m checkers.attention_render --check`, `python3.12 -m checkers.graph`. Record exact results in the report's verification section as a dated second run. Push, watch `gh pr checks 140`, and report each check.

## Mechanics

Commit after each numbered section and push each time. Trailers in order: `Model: <your model, accurately self-identified> (<provider>)`, `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`, `Signed-off-by: A. M. Berns <ansonberns@gmail.com>`. Work in the foreground only; no background agents. Finish by printing: the head commit, the CI results, whether 1(b) was proved or narrowed, and your merge recommendation. Then stop.
