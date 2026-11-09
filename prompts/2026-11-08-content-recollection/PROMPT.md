# Content recollection — an exploratory round

A new round on `A-M-Berns/alignment-workspace`, branched from the current `origin/main` (which includes PR #140, merged 2026-11-08 as `fca35075`). Open a pull request against `main`. **Do not merge it and do not enable auto-merge.**

**This round is exploratory.** Its deliverable is a judgment, with small theorems and exact fixtures behind it, about which formal tools give the program a notion of *content* that survives change. A tool that turns out not to fit is a result; say why with the evidence that killed it. Depth over coverage: matters 1 and 2 are to be done properly, matter 3 to fixture level, matter 4 as far as it honestly goes. Report what was not reached.

## Why this round

The program's account of normativity is now: to be bound by a norm is to be answerable for it, to an assessor one cannot steer, on a matter where that assessor has standing. `WarrantInductor.Entitlement` carries four conditions; after PR #140 three have content (exposure, admission by standing, liveness). The fourth, `Expresses` — that a formal row faithfully expresses the obligation's anchored requirement — is `fun _ _ => True` at every fixture. `Integrity` requires that "live content is transported faithfully" and the repository has composition lemmas for transport steps with a Lipschitz constant and a slack (`NormativeInductor.affine_transport_compose`, `NormativeInductorComposition.chain_transport`), but nothing says what makes a transport of *content* faithful, and `wiki/Normativity.md` records that an audit transport object for liabilities stated across vocabulary change is absent.

The philosophical reading the maintainer is testing is Brandom's: a later stage improves on an earlier one when it can *recollect* it — retell the earlier commitments in its own terms as a partial grasp of what it now holds, carrying the old obligations forward and explaining the old errors. The question for this round is whether that has a formal counterpart on the program's own objects (rational rows, forced regions, Farkas and bound certificates, the accounted state with immutable anchors, seeds), in three parts: carrying old commitments into a new vocabulary; exhibiting the earlier view as a coarsening of the later; and constraining which continuations are permissible.

Do not treat the reading as established. The round succeeds if it says which parts hold, which fail, and what each tool can and cannot deliver.

## 1. Conservativity: the first theorem

A vocabulary change that only **adds** coordinates is the cheapest case. `SeedStatics` already eliminates coordinates by Fourier–Motzkin (`project`, `forcedInterval`).

### Tasks

Define the extension of a seed along an embedding of the old coordinates into the new, and the projection of the new forced region onto the old coordinates. State and prove: the extension is **conservative** on the old fragment iff the projected new region equals the old forced region, and a **refinement** iff it is contained in it. Determine whether `seed_independence_strict` is an instance of conservativity and say so either way.

Two exact fixtures: a conservative extension, and a non-conservative one in which a new term's introduction and elimination rows together force a bound on old coordinates that the old seed did not (the inferentialist's bad concept). In the second, exhibit the forced bound and its certificate.

## 2. Incompatibility semantics and `Expresses`

Compilation already decides when a finite set of forms is jointly infeasible, with a certificate. That is an incompatibility relation.

### Tasks

Define incompatibility of a finite set of forms as a valid conflict from compilation, and **incompatibility entailment**: `f` entails `g` when every set incompatible with `g` is incompatible with `f`. Prove that it coincides with certificate entailment (`BoundCert`, the Farkas side) on the rational row language: soundness in general, completeness where the region is nonempty. If completeness needs a form of Farkas' lemma the pinned Mathlib does not supply, prove soundness, state completeness as open with exactly what is missing, and narrow item 118 to that.

Then define `Expresses` by incompatibility role, in two strengths: the row has the same role as the requirement, and the row demands *no more than* the requirement. The requirement needs a denotation: use the robust reading of PR #140 (`RobustWarrant.Robust`) for a defeasible warrant. Show on a fixture that (i) `Entitlement` is inhabited with this `Expresses` non-trivially, (ii) the plain linear strength row fails "no more than" against a defeasible warrant because it contraposes (item 113's phenomenon, now as a statement about expression), and (iii) the row the rebuttal rule keeps passes.

## 3. Recollection as a map between world spaces

The proposal: one object does the transport, the coarsening and the accounting of what a change broke — a stochastic map from the new world space to the old (a function between worlds in the deterministic case).

### Tasks

Find the cleanest finite formulation; the level of world distributions is likely easier than the level of sentence prices, since an old sentence pulls back along a stochastic map to a `[0,1]`-valued function on new worlds, which need not be a new sentence. Say which level you chose and why. Then, to fixture level with exact rationals:

- the pullback of an old row and its soundness (valid at the pushed-forward credence iff its pullback is valid at the new credence);
- composition, and that a recollection is a transport step with constant `1` and slack `0` in the sense of `affine_transport_compose`; an approximate version whose slack is the mass on which the map fails, if it comes cheaply;
- the relation to `ThinLegitimacy`'s sufficiency: whether the existence of such a map exhibits the earlier record as a garbling of the later in that file's own terms. If the types do not meet, state the relation in prose with the mismatch and stop;
- the **broken commitments**: the old rows whose pullback fails on the new forced region. State what `Integrity`'s faithful-transport condition actually requires in Lean, and whether a recollection supplies it, strengthens it, or is a different thing.

Two fixtures: a concept **split** (one old sentence becomes two new ones) and a concept **abandonment** (an old sentence with no exact image). Say plainly what the formalism reports in the second case; "it reports nothing useful" is an acceptable finding.

## 4. Precedent as the constraint on continuation

Sections 1–3 can show a change was faithful and better informed. None says a continuation was *permissible*. Brandom's own model for that is the common-law judge, and the formal model the maintainer has in mind is the reason model of precedential constraint attributed to John Horty: past cases induce a priority order among reasons, and a new decision is allowed only if one consistent order still rationalizes every case.

### Tasks

Build the smallest exact model of that constraint over the program's own objects — occurrences, grounds, undercut and rebuttal, strengths — in Lean if it is small, in Python with exact rationals otherwise. One fixture where a continuation is forbidden because no consistent order rationalizes it with the past, one where it is permitted by distinguishing. Then answer in the report: does the constraint give any notion of a *better* continuation, or only of an *allowed* one? Does it interact with the grounded survivor rule, or sit beside it?

This matter is the most speculative. If the model does not fit the program's objects, say what would have to change for it to fit, file that as an item, and stop.

## Standards particular to this round

- **Citations.** The literature named here and in the maintainer's notes (institutions; functorial data migration; refinement mappings; abstract interpretation; Horty on precedent; conservativity and harmony; Markov categories and Blackwell's theorem) was recalled from memory by the prompt's author and is **unverified**. Do not cite a label you cannot verify. State the mathematical content directly; where you can verify a source, cite it; where you cannot, write that the attribution is unverified.
- **No wiki.** This is exploration. Put interpretation in the pull request description, not in `wiki/`. The one permitted wiki edit is a claim-count binding a checker requires.
- **Registry.** A Lean headline registers against an existing item (118, 128, 113, 133, 115 are the candidates) in the same PR. File at most two new items. Names are provisional and listed.
- **What it does not show.** For each matter, the report says whether the tool *checks* a proposed recollection or *chooses* one, and what remains a declared input.

## The site

`state/prs.json` holds the per-PR digests the site's concept pages show as merged work, and it currently ends at PR #131. Add a digest for PR #140 and, after you open it, for this round's PR, following the existing entries' shape and `site/README.md`. Add or touch `state/concepts.json` only if the contract plainly calls for an entry for something this round introduces. If either needs a judgment the contract does not settle, skip it and say so in the report; do not improvise.

## External review before the recommendation

After your own verification passes and the PR is open, run one independent review by a different model family and act on it:

    codex exec -m gpt-6-astra -s read-only -C <worktree> -o <scratch>/astra-review.md "<your review prompt>"

Write the review prompt yourself on the model of `/Users/anson/hub/scratch/dispatch-2026-11-07-score-side-binding/astra-review-prompt.md`: give the reviewer this dispatch and your report as the task specification, not your conclusions; ask whether each theorem says what the report says, whether each registered claim's hypothesis package is inhabited, and what the report oversells; require ranked defects and one merge word. Commit the review verbatim under `prompts/2026-11-08-content-recollection/` attributed to GPT-6 Astra (OpenAI). Fix each finding or dispute it with a reason, in a table in the report. One review pass and one fix pass; do not loop.

## Deliverables

- `prompts/2026-11-08-content-recollection/PROMPT.md` — this file, verbatim — and `REPORT.md` with the pointer and attribution table.
- `projects/normativity/rounds/2026-11-08-content-recollection/`: `README.md` (verdict line without backticks), `REPORT.md` (deviations; a section per matter ending in a one-line verdict *fits / fits in part / does not fit*; what is not established; the review table; outstanding maintainer actions numbered), `PROVENANCE.md`, tests for any theorem-bearing Python.
- Lean modules under `lean/Workspace/Normativity/Contrib/`, each with its `#print axioms` list.
- Structured state in the same PR: the round record in `state/rounds.json` with `depends_on`; provenance rows; claims; `DECISIONS.md` entries, agent-decided and reversible where you adopt your recommendation, queued under *Awaiting the author* only with a *turns on* line. The map: the previous round found the protocol has no node kind for a round (friction item F10) and filed `work` pointers of kind `round` on the nodes standing for its results and items; do the same. Edit item nodes under `graph/nodes/`, never the `ATTENTION.md` render; regenerate it.
- A pull request with the template filled, a non-empty **Model attribution** section, and the closing line `🤖 Generated with [Claude Code](https://claude.com/claude-code)`.

## Verification

Full Lean build; `python3.12 tests/audit_axioms.py`; `python3.12 tests/run.py`; `python3.12 -m checkers.run`; `python3.12 -m checkers.workspace_state --check`; `python3.12 -m checkers.wiki_state_bindings`; `python3.12 -m checkers.wiki_links`; `python3.12 -m checkers.attention_render --check`; `python3.12 -m checkers.graph`. The system `python3` is 3.9 and cannot parse the checkers. Report exact results. Watch the PR's CI and report each check.

## Mechanics

- Repository checkout: `/Users/anson/hub/repos/alignment-workspace`; its working tree is on another branch and is not to be touched. Create a worktree: `git fetch origin && git worktree add -b round/2026-11-08-content-recollection .claude/worktrees/round-2026-11-08-content-recollection origin/main`, and work only there.
- Lean: `mkdir -p lean/.lake && ln -s /Users/anson/hub/repos/alignment-workspace/lean/.lake/packages lean/.lake/packages`; build with `~/.claude/scripts/safe-lake.sh build Workspace` from `lean/`. **Never call `lake` directly.** Before every build and sweep run `~/.claude/scripts/resource-guard.sh check`; if LOADED, `~/.claude/scripts/resource-guard.sh wait 3600`. One heavy command at a time. `tests/run.py` needs `lean/.lake` set aside while it runs and new files `git add`ed; restore the symlink afterwards.
- Commit after each matter and push each time. Trailers in order: `Model: <your model, accurately self-identified> (<provider>)`, `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`, `Signed-off-by: A. M. Berns <ansonberns@gmail.com>`. Attribution block: prompt-author model Claude Fable 5.1 (Anthropic), drafted in conversation with the maintainer on 2026-11-08; executor model yours.
- Work in the foreground; no background agents.
- Finish by printing the PR URL, the per-matter verdicts, the review's merge word and yours.

Then stop. Give your considered merge recommendation, and separately your recommendation on which of the four tools the program should build on.
