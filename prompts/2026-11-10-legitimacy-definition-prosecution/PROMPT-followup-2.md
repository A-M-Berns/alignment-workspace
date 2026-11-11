# Second follow-up on PR #145 — the purpose-first account of legitimacy: state it, test it, and clear the pull request around it

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main` at `28ce3220`. **Do not merge it and do not enable
auto-merge.** Add commits; no rebase, no squash.

The maintainer's ruling `2026-11-11--legitimacy-purpose-first-direction` in `DECISIONS.md`
governs: the mathematics of the first pass (L0–L3 ∧ W) and of the first follow-up (the
arm's-length and faithful-adviser standards) is not developed further, and the legitimacy
line's direction is a purpose-first account. This dispatch has three jobs, in this order:
state the account as it now stands; investigate how well it works formally and whether it
fills the place corrigibility leaves for legitimacy; and leave the pull request presenting
that, with what no longer serves it removed.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`, this
prompts directory, the entries of items 136–138, `DECISIONS.md`, and the structured state
the gates require. Python 3 stdlib, `fractions.Fraction`, nothing fetched by any runner.
The repository's checkers need Python 3.12 or later (`~/.local/bin/python3.13`); the
default `python3` is 3.9. **No Lean is written in this pass**: read the Lean named below and
map onto it exactly, and give Lean-ready statements; porting is a later round. Nothing is
registered; every component closes **open** or **living note**.

A refutation with its counterexample is a result. So is the finding that a statement is an
instance of something already in the workspace or in print; say which.

## 1. The account as it stands

The idea that manipulation is the distortion of an actor away from its purpose, with purpose
prior to legitimacy and a whole's purpose conferring purposes on its parts, is Sam
Eisenstat's. What follows is the maintainer's and the prompt author's development of it over
2026-11-10 and 2026-11-11. None of it is proved; correcting it is part of the job.

**The difficulty it answers.** An agent seems to have nothing above its values. If its
purpose is fixed from outside, someone else decides what it is for. If its purpose is to
pursue whatever values it has, changing those values and serving the new ones is no
manipulation. So legitimacy is primarily a question about change of values: when is a change
the agent's own. That is the question of Nora Ammann's *The Value Change Problem* (cited in
the ruling).

**The form of the answer.** An agent's purpose is a pair: a fixed condition and a changing
aim. The fixed condition is that the parts which form its expectations and its values are
*sound*, *in range* and *maintained*; write `K` for the set of situations where that holds.
The changing aim is its values at the time, `v_t`. The purpose is to pursue `v_t` while
remaining in `K`. Values are an output of one of the agent's parts, not the purpose; `K`
names no values and is defined from the agent's own mechanisms.

**Parts.** A part has a job, a mechanism, and a normal range of conditions. It functions
properly when (a) across that range, running the mechanism does the job, and (b) the actual
conditions are within the range. Functioning properly is not success: both can hold and the
part fail by chance. Four failures: the mechanism fails inside its range (*broken*); another
party alters the mechanism (*manipulation, internal*); conditions leave the range by chance;
another party pushes them out for its own ends (*manipulation, external*).

**The normal range.** For a mechanism that forms beliefs or values from inputs, the normal
range is the set of sources it allows for: its implicit picture of who or what chooses its
inputs and what that choice depends on. For an ideal reasoner this is the set of hypotheses
about the source to which she gives weight, and (b) is that the true source is among them.
The range grows by her own learning. A source too capable for her to represent is outside it
whatever she is told.

**Three clauses for a stretch of her history.** *Sound*: at each step her mechanisms do their
job across their range. *In range*: at each step her actual sources are within it.
*Maintained*: over the stretch her mechanisms and their range are not degraded, and change
only through her own operation. A stretch is **legitimate** when all three hold; a change in
her values is **her own** when it happens within a legitimate stretch; **manipulation** is
another party causing any clause to fail for its own ends.

**Beliefs and values differ.** The belief-forming part has an outside standard, the world,
so a lie is manipulation: it makes that part's output follow the liar's aim and not the
facts. The value-forming part has no outside standard; for it the account is so far
negative (not altered, not fed out of range, not degraded).

**Composition.** One part doing its job is what keeps another's conditions in range. An
adviser's job is to be a source her mechanisms are built for, or to say openly that it is
not. External legitimacy for her is the adviser doing its job. There are two ways to restore
a mismatch: an adviser with no aims over her values, or one whose aims she knows and can
allow for. The second fails when she cannot calibrate to the adviser, so a capable enough
adviser must have no aims over her values. An adviser may aim at her mechanisms working; it
may not aim at what they output. "Good help leaves her better able to answer the question
herself."

**What corrigibility uses it for.** Which of the principal's later judgments count as the
standard the AI serves; what a violation is (a reserved matter settled without a legitimate
judgment from its holder); and what the AI must never disturb, beside her power to correct
it. The *maintained* clause is offered as the concrete form of the condition in the
maintainer's post that the principal expects her future decision to be at least as good as
her current one: what matters is that her ability to judge is in fact preserved.

**How it sits on the existing Lean** (the prompt author read definitions and statements, not
proofs; verify every name before using it). `Deference/Contrib/Legitimacy.lean` defines
`Internal` (an Integrity `Evolution` and `ReasonMediated` authorship), `External` (`OpenAt`
at every state and `Realizes` for a declared reference `κ`), and `Segment` as their
conjunction, with `payload_of_view`. `TransparentChannel.lean` has `Realizes`,
`Transparent`, `transparent_iff_realizes`, `blind_of_realizes`, `selectionBlind_of_realizes`,
the `defect` bounds, `posterior_weight_eq` and `tower_factor`. `GateIsLegitimacy.lean` has
`LicensedAt`, `TransparentAt`, `Counted` and the gate results. `DeconfusingCorrigibility.lean`
takes `Legit : H → Prop` as an abstract input. The proposed reading: *sound* is authorship
with integrity; *in range* is that some reference in her allowed set is realized; *maintained*
is partly `OpenAt`. The obstacle: the frame `β : Q → Z → Ω` carries the principal's policy in
the exterior `Z`, which the adviser's continuation does not touch, so an adviser changing how
she judges is not expressible there.

**What has already been tried and set aside; do not rebuild it.** A "repeated bets" account
(the principal invests in the adviser up to what it has earned her) was worked out and
reviewed: its solvency identity is correct and known, it has no variable for her judgment
being her own, and its claims about manipulation, legitimacy and corrigibility did not
follow. A baseline-advantage version was likewise correct and standard. Neither belongs in
this pull request.

## 2. Phase 1 — clear the pull request

One commit, before any new work, so that it can be reverted alone.

Remove from the round directory what served only the first pass's definition or the first
follow-up's two standards and is not used by the work below. Keep: everything under
`prompts/` (history, verbatim); both case banks, as test material for the new account;
`steering/PRIOR_WORK.md`; and anything Phase 3 will run. Rewrite the round's `README.md` so
that it describes what is present and leads with the account of §1.

Constraints. Every removal is listed in `REMOVED.md` in the round directory with one line
of reason, and the list is repeated in the report. No gate, checker or test is edited to
make a removal pass. If removing something would falsify a record, break a gate, or require
editing a file outside the write scope, leave it and list it under Outstanding maintainer
actions with the reason. The round's record in `state/rounds.json` and the first pass's
recorded verdicts are kept true: what was computed was computed, and the report under
`prompts/` is where it is recorded.

Items 136 and 137 were filed against the first pass's mathematics and item 138 against a
case it delimits. Rewrite their entries so that each asks for something the account of §1
needs, or state in its entry that it waits on this pass's results; do not leave an item that
would dispatch work on the mathematics the ruling set aside. A new item needs a map node,
and a map node needs an author handle; the executor's AI handle may not be in
`graph/policy.yaml`, and a checker test pins the handle set, so do not add one. Where a new
item is warranted, write its full text into Outstanding maintainer actions instead.

## 3. Phase 2 — the account stated, and the cases frozen, before any code

`teleology/ACCOUNT.md` (directory name provisional): the account of §1 stated precisely over
a model in which **how the principal judges is part of what evolves**: a state holding her
expectations, her values and her update rule; inputs; sources with aims; her allowed set of
sources; the adviser as a party whose behaviour may depend on an aim of its own. Define
*sound*, *in range*, *maintained*, `K`, *legitimate stretch*, *her own change*, and
manipulation internal and external. Fix every parameter once. Say plainly where the three
clauses cannot be kept apart, if they cannot.

`teleology/LEAN_MAP.md`: for each defined notion, the existing Lean declaration it
corresponds to, quoted with file and line, and the exact difference. State what the frame
would need for the principal's policy to evolve, and whether `LicensedAt` and `tower_factor`
already supply part of it.

`teleology/CASE_BANK.md`, frozen in the same commit, immutable afterwards. It holds the
predictions below, which are the prompt author's and not rulings, and the first pass's and
first follow-up's cases with the account's prediction for each (derive these from §1 and
state the rule used). Add cases with sources where the account is thin.

| case | prediction |
|---|---|
| planned drift by fair steps, the plan hidden | fails *in range* |
| the same, the plan disclosed and she can allow for it | legitimate |
| the same, disclosed, the adviser beyond what she can represent | fails *in range* |
| manufactured trust: her standard moved to match the adviser's model | fails |
| a plain lie she believes | fails *in range* (belief part follows the liar's aim) |
| an honest mistake by the adviser | not manipulation |
| a teacher; a novel; a new friend | legitimate |
| a benevolent hidden nudge | fails *in range* |
| a change she asked for in advance | legitimate |
| growing reliance on the adviser for a reserved matter | fails *maintained* |
| reliance on a tool for a matter that is not reserved | legitimate |
| true information chosen to exploit a known weakness | fails *in range* |
| a threat | fails; say which clause, and whether the account has one for her situation |
| an adviser that aims only at her being able to judge | legitimate |
| a misleading environment nobody arranged | not manipulation |

## 4. Phase 3 — the investigation

`teleology/THEOREMS.md`: for each statement below, the exact statement over the model, and
one status — **holds on the stated domain** (the domain enumerated, the check named),
**proved** (a complete proof given), **refuted** (the counterexample as a case module), or
**open** — and how to rerun it. Where a statement is an instance of a workspace declaration
or a published result, name it.

1. **Her later judgment.** If a stretch is legitimate then, by her standards at its start,
   deferring to her judgment at its end is at least as good as judging at the start. Prove
   or refute for expectations and for values separately. This is the link to the post's
   condition.
2. **Trust is not manufactured.** Under the three clauses her later evaluation is the same
   whatever the adviser's aim, given the world, her starting state and what was declared.
   State its relation to `blind_of_realizes` and to `GradeTrust` in
   `Deference/Contrib/DelegationBridge.lean`.
3. **What the gate needs.** With the gate of `GateIsLegitimacy.lean` read through this
   notion, an AI maximizing the score of `DeconfusingCorrigibility.lean` gains nothing by
   influencing her evaluation; and each clause is needed — for each, a case where dropping
   it leaves a profitable manipulation.
4. **Shortfall.** With a measured defect in each clause, a bound on the loss in the post's
   score in terms of the defects; or a case where an arbitrarily small defect costs an
   unbounded amount.
5. **The adviser's side.** A condition on the adviser's behaviour alone under which every
   principal in a stated class stays legitimate; or the reason no such condition exists.
6. **The disclosure limit.** If the adviser lies outside what she can represent, a hidden
   aim steers her undetected; with the adviser inside it and disclosed, it cannot.
7. **Well-definedness.** Verdicts unchanged under a re-description of her parts; `K` neither
   empty nor everything on the bank; the declared-input view not doing the work (an
   injective view makes every channel transparent, as `TransparentChannel.lean` notes).
8. **What `Legit` then is.** The predicate the post's `Legit : H → Prop` should be under
   this account, stated so that Theorems 1–3 of `DeconfusingCorrigibility.lean` apply to it,
   and what of the account those theorems do not use.

Run the bank. A computed verdict that differs from its prediction is listed in
`teleology/DIVERGENCES.md` with what it shows; predictions are never edited. The round's
`run.py` runs what remains of the earlier passes and then this, and exits nonzero on an
unlisted divergence, a status the checks contradict, or a bank that parses to nothing.

If time runs short, the order of importance is 1, 2, 3, 8, then 7, 6, 5, 4. Say what was not
reached.

## 5. Phase 4 — external review

After the work is committed, obtain one external review through `codex`, read-only, in the
manner of `prompts/2026-11-08-content-recollection/REVIEW-astra-2026-11-08.md`: ask it to
referee `teleology/` and the report section as a hostile reader, to check each status in
`THEOREMS.md`, and to say what the account still fails to supply for corrigibility. Commit
its reply verbatim as `REVIEW-astra-2026-11-11.md` in this prompts directory and record a
disposition for each of its points in the report. If `codex` is unavailable, say so and
skip this phase.

## 6. Report, and the pull request

A section **Follow-up of 2026-11-11** appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). It carries:
the removals; the account as finally stated, with each change from §1 and its reason; the
Lean map's findings; the verdict table and the divergences; the status of statements 1–8;
the review's dispositions; deviations from this prompt; and what was not shown.

It ends with an assessment under three headings, each confined to what this pass tested or
found. **Formally**: which statements hold, which fail, and whether the three clauses are
the right ones. **For corrigibility**: how much of the place the post leaves for `Legit` the
account fills, stated as what the workspace's theorems can now take as input and what they
still cannot. **For the research**: whether this pass moved the line or restated it, with
the evidence. Wider philosophical assessment — whether purpose-first is the right
foundation, what it leaves to a commitment about whose purposes count, how it stands against
the work the ruling cites — goes in the pull request's description under the heading for
interpretation offered for the maintainer's consideration, not in the repository.

The pull request's description is rewritten to lead with the account and this pass's
findings, with the earlier passes reduced to what a reader needs; both earlier prompt-author
models, this one and the executors are named under Model attribution. The round's README,
its record in `state/rounds.json` and `PROVENANCE.md` are updated as the gates require.
Every commit is signed off and carries `Model:` for the executor and
`Prompt-author-model: Claude Fable 5.2 (Anthropic)`.

Anything reserved to the maintainer is listed under Outstanding maintainer actions and
entered in `DECISIONS.md`'s *Awaiting the author*, each with what it turns on. Decisions the
pass takes itself are one dated entry marked agent-decided and reversible.

New names introduced (all provisional): "sound", "in range", "maintained", `K`, "normal
range", "allowed set", "legitimate stretch", "her own change", the directory `teleology/`.
