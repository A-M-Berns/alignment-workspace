# Where obligations bind — the score-side test, solvency as soundness, admission by standing

A new round on `A-M-Berns/alignment-workspace`, branched from the current `origin/main`. Open a pull request against `main`. **Do not merge it and do not enable auto-merge.**

## Where things stand

PR #129 (merged 2026-10-21) left one consolidated conditional theorem, `WarrantInductor.warrant_inductor`, with two runs (`WarrantInductorWitness`, `WarrantInductorRebuttal`). Its grounds are *entitled* (`WarrantInductor.Entitlement`: origin exposed, `Protocol.Admitted` at the boundary's history, a live leaf in the origin's account, the form expressing the anchor under a declared `Expresses`). Of those four conditions only liveness has content at the fixtures; admission and expression are typed inputs. `compileAt` returns a typed outcome on the compiler's `CompileResult`; `conflict_region_empty` is the Farkas side.

Since then the maintainer and a model worked through what makes an inequality one the reasoner *ought* to hold rather than one it *can be made* to hold. The conclusions this round is to test, not assume:

1. **Soundness as stated fails.** Read a warrant as "the posterior satisfies the row at every record where the warrant is undefeated". On the eight-world model of `ThinLegitimacy` (`lean/Workspace/Deference/Contrib/ThinLegitimacy.lean`; a binary quantity, a signal of accuracy 3/4, a challenge of accuracy 2/3, independent given the quantity), the warrant "the signal is a reason for the quantity, strength 3/4" is exactly true at admission; after a contrary challenge the posterior is 3/5, the row still demands 3/4, and neither undercut nor rebuttal by settlement fires. Registering the challenge as an opposing warrant at 2/3 makes the region empty and compilation withholds everything although the answer 3/5 is determinate.
2. **A repaired reading holds, cheaply.** A warrant is a constraint on her model over undefeated extensions: `Pr_M(Y | A ∧ E) ≥ c` for every undefeated `E`. Then strength is the worst case over undefeated extensions (3/5 here, or 3/4 with the contrary challenge declared a defeater); refutation of the consequent must be a defeater, or the family is satisfiable only by contraposition; and sound rows cannot conflict, so a valid Farkas conflict proves a mis-admission among the rows its certificate supports.
3. **On settling matters, force is only cheap at finite dates.** `DecisionComponent.liability_identity` and `bounded_iff_not_outperformed` (`lean/Workspace/Deference/Contrib/DecisionComponent.lean`) are stated over two bare real sequences: an enforcer holding prices to one source and settling against another owes the source's realized shortfall, bounded exactly when the source is not systematically outperformed. For a warrant schema with timely-settling instances this should instantiate directly: bounded liability iff the frequency on undefeated instances is not systematically below the strength.
4. **Authority that does not rest on being right cannot live in beliefs.** The corrigibility kernel puts it in what the chooser is scored on (`Corrigibility` §4: no authority row enters the enforcer; the permission layer reads prices and adds no trader, `DecisionComponent.noninterference`). The October stack compiles every obligation into rows on prices. For an obligation on *conduct* the kernel's pattern is: leave the market free, price the event "this will be assessed a shortfall", charge the chooser for that price.

The standard for this round:

> After merging, the program should say, with a theorem or a fixture behind each clause, where each kind of obligation binds — on prices, on the score, or nowhere — and why; and the admission predicate should have the content the authority module already supplies.

Three matters, and a short exposition task. Do not start a broad research round.

## 1. The score-side test

The rebuttal run poses one decision question before and after a strength is refuted: `WarrantInductorRebuttal.same_question` gives the soft gate at least 24/25 on acting at date 4 and exactly 0 at date 9, following the pinned price of the refuted conclusion.

### Tasks

Classify every row that the October bundles enforce (`WarrantInductorWitness`, `WarrantInductorRebuttal`, and the forms of `SeedStatics.Form`) by what settles it: **deductive** (the deductive process settles the sentence), **assessed** (an evaluation settles it — an account answered or closed, her later evaluation, a declared violation), or **none**. State the classification as a table in the report and, where a row is about conduct rather than credence, say so.

Then build the score-side counterpart of the rebuttal run's decision on the *same* market history: no row that expresses an obligation on conduct is enforced; the only enforced rows are deductive pins, coherence rows, and whatever epistemic strength rows the classification keeps. The obligation reaches the decision as a priced assessed-shortfall event with a charge `ϖ`, using the existing decision component (`DecisionComponent.permWeight` / `cgate`, or `BRIACorrigibility.evalOf` if that is the smaller fit). If the fixture has no obligation on conduct — if every warrant in it is epistemic — add the smallest one: refrain while the originating obligation's account is live, assessed by the account's fate.

Determine whether the same reversal obtains. Report whichever of these is the case, with the Lean behind it:

- (a) the reversal obtains with no conduct row enforced — the practical content never needed force on beliefs;
- (b) the reversal needs the epistemic strength row and nothing else — then the practical part is score-side and the belief part is an epistemic warrant;
- (c) the reversal needs a conduct row on prices — say why, and what the score-side realization loses.

Deliverable: one Lean module under `lean/Workspace/Normativity/Contrib/` (provisional name `WarrantInductorScoreSide.lean`), building on the rebuttal run's definitions rather than copying them, with the decision stated as a theorem in each of the two realizations and the market shown to be the same in both. Prove, for the score-side realization, that the enforcer's bundle contains no conduct row and that the market's prices are those of the rebuttal run (`noninterference` is the shape).

## 2. Solvency as soundness

### Tasks

**(a) The instantiation.** State and prove, by instantiating `liability_identity` / `bounded_iff_not_outperformed` or by the smallest new lemma if they do not instantiate cleanly, that for a warrant schema whose instances settle in a timely way the enforcer's cumulative liability is bounded iff the schema is not systematically outperformed: the frequency of the consequent on undefeated instances is not systematically below the strength. If the instantiation needs an assumption on the enforcer's trade beyond what the identity already carries (the calibrated intensity of `WarrantForce`, settlement to the ordinary valuation), name it as a hypothesis; do not weaken the identity. Say in the report whether this is new mathematics or a renaming of the deference result, plainly.

**(b) The conflict audit.** From `NormativeInductorComposition.conflict_sound` / `WarrantInductor.conflict_region_empty`: for every price vector some row with positive multiplier in a valid Farkas certificate is violated at it; hence if every admitted row is valid at a point, no valid conflict certificate exists, and a conflict names its suspects. Prove it in the generality the existing certificate type allows.

**(c) The eight-world fixture.** Put the counterexample of the preamble into Lean on the `ThinLegitimacy` model (reuse its world type and measure if they are exposed; otherwise state the model locally with exact rationals and say so). Show: the strength row at 3/4 is valid at the record with the signal alone and invalid at the record with the contrary challenge; neither `settleForm` rebuttal nor undercut removes it there; the robust strength (the infimum over the undefeated extensions) is 3/5, or 3/4 with the contrary challenge declared a defeater; the robust rows for and against meet at 3/5. Define the robust reading of a warrant as a constraint on the model over undefeated extensions, provisionally named, and prove the one-line soundness lemma that follows from it. Do not build a general defeat semantics; the fixture and the definition are the deliverable.

The home for (a) is item 61 (a normative source with summable enforcement liability); (c) bears on items 113 and 127. Narrow those items only to what is proved. Do not file more than two new items.

## 3. Admission by standing

`Protocol.Admitted` is the typed admission predicate `Entitlement` consumes. The authority module (`lean/Workspace/Deference/Contrib/AuthorityModule.lean`) allocates matters to holders and already says who may put a decision on which matter.

### Tasks

Instantiate `Protocol.Admitted` with the allocation: an obligation is admitted at history `h` when its issuer holds the obligation's matter under the allocation current at `h`. First-person commitments are matters the reasoner holds itself. Exhibit `Entitlement` inhabited with this admission on one fixture — the witness's `state₀` or the decision component's, whichever is smaller — and state which of entitlement's four conditions now carry content and which remain typed (`Expresses` will).

If the authority module's types do not meet the protocol's `Admitted` signature without substantial adaptation, do not force it: report the mismatch, the adapter it would need, and stop there. The deliverable in that case is the report's statement of the gap, filed as an item.

## 4. Exposition

Write to these pages only, and label as Established only what this round registers:

- `wiki/Normative-Inductor.md`: the sections *Entitlement, not licence* and *What remains*, and the architecture line if the score-side test moves obligations on conduct out of the enforcer. Say where each kind of obligation binds and which theorem says so.
- `wiki/Normativity.md`: the *Current status* and *operative force* sections: three kinds of settlement, force as finite-time binding on settling matters, solvency as the discipline on epistemic warrants. The exposure rule — a constraint is enforceable only if some settlement or assessment could show it wrong, or the reasoner authored it — is a **proposal**; state it as one.
- `wiki/Theorem-Spine.md`: entries for what registers.
- A round `THEOREM.md` only if a theorem of record results from matter 1 or 2; otherwise none.

Keep "warrants constrain prices" apart from "warrants produce warranted guidance", as the consolidation round did.

## Scope and stop conditions

- No strength learning beyond the solvency statement of 2(a). No dynamics of warrant wealth.
- No new legitimacy theory, and no change to the kernel. The specification-layer Lean (`Headline.lean`, the spec files listed in `tests/path_gate.py`) is not touched. Do not alter the consolidated theorem's statement; add beside it.
- The rulings M1 and M2 of the warrant-enforcement-semantics round and the entitlement liveness reading stand as landed; do not reopen them. If 2(c) bears on them, say so in the report and in the queue entry's text, nothing more.
- No convergence results, no BRIA auction dynamics, no Hoffman constants (item 125 stays where it is).
- Eight questions to answer about each new theorem, in the report: what is the hypothesis package; what inhabits it; what is typed; what does the conclusion say at the fixture; what would make it vacuous; what is the same theorem under another name elsewhere in the repository, if anything; what does it not show; what reopens it.

## Deliverables

- `prompts/2026-11-07-score-side-binding/PROMPT.md` — this file, verbatim — and `REPORT.md` with the pointer and attribution table.
- `projects/normativity/rounds/2026-11-07-score-side-binding/`: `README.md` (verdict line without backticks), `REPORT.md` (deviations declared, what is not established, outstanding maintainer actions numbered), `PROVENANCE.md`, tests if any Python is theorem-bearing (exact rationals only).
- Lean modules under `lean/Workspace/Normativity/Contrib/`, each with its `#print axioms` list; claims in `projects/normativity/CLAIMS.md` for the headline theorems, `kind: lean`, each against an item.
- Structured state in the same PR: the round record in `state/rounds.json` with `depends_on`; `PROVENANCE.md` rows; `DECISIONS.md` entries — agent-decided and reversible where the round adopts its recommendation, queued under *Awaiting the author* only with a *turns on* line.
- **The map.** This is the first research round since the map became the canonical index (`AGENTS.md`, *The argument map under `graph/`*; `graph/PROTOCOL.md`). File the round's node, each registered claim as a formal result, the narrowed items by editing their nodes (`graph/nodes/item-61.md` and so on; `ATTENTION.md` is a render, regenerate it with `python3 -m checkers.attention_render --write`), and each new `DECISIONS.md` entry's anchor line. Run `python3 -m checkers.graph` and commit what it regenerates. Where the protocol is unclear for a research round, do the minimum the checker requires, file the friction under *Workspace friction* per standard 14, and do not improvise structure.
- A pull request against `main` with the template filled: new names introduced, provenance entries, and a non-empty **Model attribution** section. The body ends with the line `🤖 Generated with [Claude Code](https://claude.com/claude-code)`.

## Verification

Run the full Lean build, the axiom audit (`python3 tests/audit_axioms.py`), `python3 tests/run.py`, `python3 -m checkers.run`, `python3 -m checkers.workspace_state --check`, `python3 -m checkers.wiki_state_bindings`, `python3 -m checkers.wiki_links`, `python3 -m checkers.attention_render --check`, and `python3 -m checkers.graph`. Report exact results. Do not silently promote claim statuses. Watch the PR's CI and report each check's result.

## Mechanics

- Repository checkout: `/Users/anson/hub/repos/alignment-workspace`. Its working tree is on another branch; do not touch it. Create a worktree: `git fetch origin && git worktree add -b round/2026-11-07-score-side-binding .claude/worktrees/round-2026-11-07-score-side-binding origin/main`, and work only there.
- Lean: in the worktree, `mkdir -p lean/.lake && ln -s /Users/anson/hub/repos/alignment-workspace/lean/.lake/packages lean/.lake/packages`. Mathlib's pin is unchanged; the agent-foundations package and two small dependencies will update to main's pins on the first build. Build with `~/.claude/scripts/safe-lake.sh build Workspace` from `lean/`. **Never call `lake` directly.** Before every build and every test sweep run `~/.claude/scripts/resource-guard.sh check`; if it reports LOADED, run `~/.claude/scripts/resource-guard.sh wait 3600` and do not push through. Run heavy commands one at a time.
- `python3 tests/run.py` needs the `lean/.lake` directory set aside while it runs and new files `git add`ed; restore the symlink afterwards.
- Commit after each matter and push the branch each time, so a cut run loses little. Commit trailers, in this order: `Model: <your model, accurately self-identified> (<provider>)`, `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`, `Signed-off-by: A. M. Berns <ansonberns@gmail.com>`. The report's attribution block: prompt-author model Claude Fable 5.1 (Anthropic), drafted in conversation with the maintainer on 2026-11-07; executor model yours.
- Do all work in the foreground; do not spawn background agents.
- Finish by printing the PR URL, the path of the round report, and the merge recommendation.

Then stop. At the end, give your considered merge recommendation, not merely a statement that the tests passed.
