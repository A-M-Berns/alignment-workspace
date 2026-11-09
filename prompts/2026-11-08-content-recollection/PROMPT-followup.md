# Follow-up on PR #142 — finite memory, decisions on the record, change as an answerable act

Continue on the existing branch `round/2026-11-08-content-recollection`, in the worktree `/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection`. PR #142 is open against `main` at `f62e38dd`, green. **Do not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

This is an **extension and refinement** of the round, still exploratory. The first pass found that two tools fit (conservativity; incompatibility semantics with `Expresses` by role) and two fit in part (recollection as a map, which checks and cannot choose; precedent, which allows and cannot rank, and has no decision object to read a case from). Its own first not-shown line is that nothing in it shows a later stage *recollecting* an earlier one.

## The idea under test

The maintainer's proposal: the eventual theory should not assume an ever-growing record. With unbounded memory, retelling the past is optional; with bounded memory a retelling is all there is, so finite memory is where recollection does work. The program today assumes the opposite — Integrity says nothing entered has left, and thin legitimacy's sufficiency needs the later record to contain the earlier.

Conjectures from the conversation, each to be proved, refuted or narrowed. None is established; a refutation with its fixture is a result.

- **(C1) A holding is a sufficient statistic.** Whether a continuation is permitted depends on the case base only through the relation on reason sets it induces, so the cases may be forgotten and the relation kept, and its size is bounded by the vocabulary of reasons, not the length of history.
- **(C2) Forgetting a sentence is projection**, exact on the retained fragment; what it costs is the response to a later settlement of the forgotten sentence. Settled sentences (kept as their effect on live rows) and closed accounts (kept as receipts) are safe to forget; a live obligation is not.
- **(C3) Forgetting with loss composes as slack**, and a schedule with summable slack loses a bounded amount in total.
- **(C4) Choosing what to forget is steering**: a reasoner that picks what to drop after seeing the record can obtain what a policy fixed in advance cannot.
- **(C5) A change of vocabulary should be an act on the docket** — owned, licensed by a conservativity certificate, challengeable by a broken-commitment witness — so that recollection is answerable rather than chosen by a formal procedure.
- **(C6) Decisions belong on the record**: a case is an act with its grounds plus its later assessment, the assessment setting the precedent; then conduct can be held to consistency with its own assessed past, and an order among reasons can accumulate.

Matters in priority order. Do 1 and 3 properly, 2 and 4 to fixture level, 5 as far as it is cheap. Report what was not reached.

## 1. The holding (C1)

In `PrecedentConstraint.lean`, `Permitted Γ c` is `Rationalizable (c :: Γ)`.

### Tasks

Define the **holding** of a case base (provisional name): the object on reason sets that `Permitted` actually reads — `Dominates Γ`, its transitive closure, or a normal form of it. Prove that two case bases with the same holding permit exactly the same continuations, or exhibit two with the same holding that do not. State what the holding's size is bounded by. `Covers` compares strengths, so reason sets range over a strength scale: if the holding is not finitely bounded as it stands, find the normal form that is (per kind, a threshold; an antichain of minimal winners and maximal losers) or say exactly why none exists. A bound that needs a finite strength grid is acceptable if stated as a hypothesis.

Then accumulation: under permitted continuations the holding only grows, and over a finite vocabulary it is eventually constant (the shape of `SeedStatics.eventually_const_of_finite`). One fixture of **merged discord**: two rationalizable case bases whose union is not, the two-reasoner analogue of the hidden discord of item 119; say whether it is the same phenomenon or only resembles it.

## 2. Decisions on the record (C6)

`DecisionComponent.ActCertificate` carries an act's grounds, licence and lineage. PR #140's `WarrantInductorScoreSide` has an assessment of an act through the hypothesis `Assessed`.

### Tasks

Define the case of an **assessed act**: the act's grounds and the surviving grounds against it, with the *assessment* fixing which side won — an act assessed adequate makes its grounds the winners; an act assessed a shortfall makes them the losers. The precedent is set by the assessor, not by the chooser. If `ActCertificate`'s types do not meet `Case`'s without substantial adaptation, state the adapter and stop there.

State **consistency of conduct** (provisional): each choice is permitted by the holding of the reasoner's own assessed past. One exact fixture in which a later choice is forbidden by an earlier assessed act, one in which it is permitted by distinguishing. Then answer in the report: does an assessed case base give any notion of a *better* continuation, now that an assessor's verdicts enter, or still only an allowed one?

## 3. Forgetting (C2, C3, C4)

### Tasks

**(a) Projection is computed.** The first pass says no procedure computes the image of a region and `SeedStatics.project` is not connected to `Conservativity.projection`. Connect them: Fourier–Motzkin elimination of a coordinate computes the projection along the coordinate map that drops it, sound and complete. Then state forgetting's exactness: a row over the retained coordinates is forced by the full bundle iff it is forced by the projected one.

**(b) What may be forgotten.** A pinned coordinate after specialization: dropping it preserves the forced region on the rest. A closed or answered account: read what `OpenIntegrityEvolution` actually requires to persist (its `faithful` transport and the receipts) and state the minimal data that satisfies it. A live coordinate: one exact fixture in which forgetting it changes a later forced interval once it settles — the cost of forgetting, with numbers.

**(c) Loss as slack.** Using `Recollection.approx_step` and the composition lemmas, state the summability theorem for a forgetting schedule if it is cheap; if it is not, state the two-step case and what the general one needs.

**(d) Selective forgetting.** One exact fixture: the same record, a policy fixed in advance and a choice made after seeing the record, and an interval the second obtains that the first cannot. Find the omission result of the non-capture rounds (the deference contrib modules around `li_noncapture`) and say whether this is an instance of it; do not force the instantiation.

Close the matter with one paragraph on what a bounded reasoner must retain on these results — the live docket, the specialized rows on live coordinates, the holding, receipts — and what is not known. No general space bound.

## 4. A vocabulary change as an act (C5)

### Tasks

Define the docket occurrence (provisional `VocabularyChange`): its owner, the translation, its licence — a certificate of refinement or conservativity on a declared protected fragment — and its challenge, a `Broken` witness. Prove that a licensed change admits no valid challenge on the protected fragment and that a challenge is a finite object checkable in the row logic. Say who may issue one in the authority module's terms, or that this is not determined.

The queued entry `open--broken-commitment-bars-or-accounts` asks whether a broken commitment bars a change or is accounted. **The maintainer has not ruled; do not adopt either reading.** One candidate from the conversation is a split: a broken commitment whose obligation is *live* bars the change, and any other is accounted with its loss charged as slack. Implement the three readings as predicates (bars; accounted; the split), show what each does on the split and abandonment fixtures and on one fixture with a live obligation, and rewrite the queue entry's text with that comparison. The entry stays queued.

## 5. Refinements

- **The adapter's certificates.** From `certEntails_iff_sem`, derive that the `Excludes` and `Margins` certificates of `WarrantInductor.Problem` exist whenever the region excludes or marks, or say what stands in the way.
- **The row logic, stated once.** A short section of the round's `THEOREM.md`: syntax (rational rows over the cube), semantics, consequence (certificates), soundness and completeness, and the predicates now defined in it.
- **This pull request's digest.** `state/prs.json`, entry 142: the `merged` field is empty. By the ruling of 2026-11-08 now on `main`, a round's digest is dated the day its pull request opened: set it to `2026-11-09` and extend the summary and `state_after` to cover this follow-up.

## Scope

Still no wiki. No change to the consolidated theorem, to specification-layer Lean, or to the kernel. Nothing about the memory of the market or the inductor itself. No strength learning. The literature in the dispatch and in this document — Le Cam's deficiency, the reason model of precedent, Hegel's and Brandom's recollection — is recalled, unverified; state content, cite only what you verify.

## External review

As in the first pass: when verification passes, one GPT-6 Astra review through `codex exec -m gpt-6-astra -s read-only`, its text committed verbatim as `prompts/2026-11-08-content-recollection/REVIEW-astra-followup.md`, every finding fixed or disputed with a reason in the report's table. One review pass, one fix pass.

## Deliverables

- `prompts/2026-11-08-content-recollection/PROMPT-followup.md` — this file, verbatim — recorded in the prompts-directory `REPORT.md`.
- The round's `REPORT.md` gains a dated follow-up: a section per matter ending *fits / fits in part / does not fit*, each conjecture marked *proved / refuted / narrowed / not reached*, deviations, what is not established, the review table, outstanding actions. Keep the first pass's text; do not rewrite it except where this pass corrects it, and say where.
- Lean under `lean/Workspace/Normativity/Contrib/`, extending the round's modules or adding beside them, each with its `#print axioms` list. Claims against existing items (117, 119, 134, 118 are the candidates); at most one new item. Structured state, provenance, map pointers and decisions as in the first pass.
- The PR description updated to cover both passes, with the attribution section and the closing line kept.

## Verification

Full Lean build; `python3.12 tests/audit_axioms.py`; `python3.12 tests/run.py`; `python3.12 -m checkers.run`; `python3.12 -m checkers.workspace_state --check`; `python3.12 -m checkers.wiki_state_bindings`; `python3.12 -m checkers.wiki_links`; `python3.12 -m checkers.attention_render --check`; `python3.12 -m checkers.graph --root .`; `python3.12 tests/freshness.py`. The axiom audit and `tests/run.py` each outlast one foreground command: run each as a single background command with a long timeout and wait for it. Report exact results. Watch the PR's CI and report each check.

## Mechanics

- Lean: `lean/.lake/packages` should be a symlink to `/Users/anson/hub/repos/alignment-workspace/lean/.lake/packages`; restore it if a test run left it aside. Build with `~/.claude/scripts/safe-lake.sh build Workspace` from `lean/`; never `lake` directly; `~/.claude/scripts/resource-guard.sh check` before each build and sweep, `wait 3600` if LOADED; one heavy command at a time.
- Commit after each matter and push each time. Trailers in order: `Model: <your model, accurately self-identified> (<provider>)`, `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`, `Signed-off-by: A. M. Berns <ansonberns@gmail.com>`.
- No background agents.
- **Before you finish, write your closing summary to `/Users/anson/hub/scratch/dispatch-2026-11-08-content-recollection/FINAL-followup.md`** — the PR head, CI results, each conjecture's outcome, the review's merge word and yours, and which results you would build on — and then print the same. The first pass's closing message was lost when its process exited.

Then stop.
