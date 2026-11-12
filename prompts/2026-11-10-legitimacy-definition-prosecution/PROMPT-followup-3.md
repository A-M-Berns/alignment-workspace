# Third follow-up on PR #145 — purpose as a goal pursued through parts: state the account, test it on cases, and test whether it can supply what the legitimacy framework needs

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `16a61b6c` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

The maintainer's ruling `2026-11-11--legitimacy-purpose-first-direction` in `DECISIONS.md`
still governs: the legitimacy line's direction is a purpose-first account. The second
follow-up stated one such account (a fixed condition `K`, with clauses *sound*, *in range*,
*maintained*) and found it mostly wanting. The account has since been developed into a
different shape, given in §1. This dispatch has three jobs, in this order: state that
account precisely; test how well its conclusions about teleology and manipulation match
intuition on cases; and test whether it can deliver the results the legitimacy framework
needs for corrigibility.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`, this
prompts directory, the entries of items 136–138, `DECISIONS.md`, and the structured state
the gates require. Python 3 stdlib, `fractions.Fraction`, nothing fetched by any runner. The
repository's checkers need Python 3.12 or later (`~/.local/bin/python3.13`); the default
`python3` is 3.9. `tests/run.py` takes about eleven minutes: run it in the background with a
long timeout, after `~/.claude/scripts/resource-guard.sh check`. **No Lean is written in
this pass**: read the Lean named below, map onto it exactly, and give Lean-ready statements.
Nothing is registered; every component closes **open** or **living note**.

A refutation with its counterexample is a result. So is the finding that a statement is an
instance of something already in the workspace or in print; say which. So is the finding
that the account is not determinate enough to state a result at all.

## 1. The account as it stands

The idea that manipulation is the distortion of an actor away from its purpose, with a
whole's purpose conferring purposes on its parts, is Sam Eisenstat's. What follows is the
maintainer's and the prompt author's development of it on 2026-11-12. None of it is proved
beyond one small lemma; correcting it is part of the job.

**Purpose.** The principal's purpose is an overall goal together with a decomposition of
its pursuit into parts. The decomposition is not a literal division of her; it is a
description of how she pursues the goal.

**A candidate.** A candidate description of her consists of:

- an overall goal, scoring states of the world;
- parts, each with its own moves at each step, a small portion of the world it sees, a
  **mechanism** (what it does: a rule from what it sees to a move) and a **goal function**
  (what it is for: a score on how things actually are, not on how they look to the part);
- a rule fixing her action at each step from all the parts' moves, so that one action may
  be determined by moves of several parts;
- moves that alter mechanisms, the part's own or another's, since what she currently cares
  about is carried by her mechanisms and changes;
- the **adding-up** requirement: if every part achieved the best by its goal function she
  would achieve the best by her goal (*nothing left over*), and under normal circumstances
  a part doing better by its goal function does not set her back (*never opposed*). It is
  **not** required that parts each doing their best find the best joint choice; a candidate
  describes her as she is, stuck points included.

Parts do not maximize by assumption. Purpose and mechanism are two things, and a part can
fail at what it is for.

**Serving.** In a situation, a part's *best* is the most its goal function could obtain
from any of its moves, and its *got* is what the goal function obtains from the move its
mechanism makes. The part **serves its purpose** when the two are equal. The **gap** is the
shortfall. Since best is judged by how things are, gaps are rarely zero; changes in a gap
carry the information.

**Four kinds of influence.** An adviser's action changes her situation. It is *help* when
it raises a part's best or narrows its gap; *harm* when it lowers the best; **subversion**
when it widens the gap, the mechanism still running; *force* when it replaces a part's move.
Manipulation is subversion: the part is left running in circumstances where its running no
longer achieves what it is for. A gap the adviser did not widen is her own; her mistakes are
hers.

**Why parts have limits.** A part that sees less than the whole can agree with the whole
only where what it ignores does not matter. (Lemma, two lines: if a ranking of the part's
moves that depends only on what the part sees agreed with the goal's ranking everywhere,
the goal's ranking of those moves could depend only on what the part sees.)

**What fixes purposes.** The adviser does not know her decomposition and holds several
candidates. Three constraints on a candidate: *fit* (the mechanisms predict what she does);
*adding up*; *mostly serving* (across the situations she usually meets, parts mostly achieve
their purposes). Two conditions on being a part at all: its purpose is stated independently
of its mechanism, so that another mechanism could serve it better or worse; and its purpose
is something a part seeing little could carry. The intended consequence is that a part's
purpose is the feature of its output on which the success of the rest of her depends
(accuracy of belief, not agreement with what she was told), that this is a testable fact
about her and the world, and that an adviser cannot choose purposes to make its own
influence look innocent. How she maintains and improves her own parts (checking sources,
taking time over a decision) is offered as further evidence of what they are for.

**Values.** There is no single value-forming part. What she cares about is shaped by many
parts doing ordinary work: learning, experience, habit, trust, feeling. Each of those parts
has its purpose fixed by its other roles. A change in what she cares about is in order when
the parts that produced it were serving their purposes, and is subversion when the adviser
widened a gap in one of them.

**What corrigibility uses it for.** Her verdict is a guide to what she wants to the degree
that the parts behind it have small gaps. A later judgment of hers counts as the standard
the AI serves unless the adviser subverted a part that judgment depends on. Her authority
over reserved matters is a separate question, handled by the violation count of
`Deference/Contrib/DeconfusingCorrigibility.lean`; an adviser that is right about her good
and goes round her is not condemned by this account, and that is accepted. A proposed
decision rule: act when the action is good and widens no relevant gap under every candidate
with real weight; ask when they disagree, provided asking itself widens none; refuse when
it subverts under all.

**Three conjectures the account rests on.**

- *C1, determinacy.* The constraints fix purposes: admissible candidates agree on what each
  part is for and on which actions widen which gaps.
- *C2, values reduce.* Every bad change in what she cares about widens a gap in some
  ordinary part.
- *C3, lying.* A lie widens a gap in every admissible candidate.

**Known soft spots.** Drift by many small steps, none widening a gap. Steering her where
she has no preference. A part that achieves its own target while that target has stopped
serving her (the eye that sees well and carries a cancer); "under normal circumstances" in
the adding-up requirement is where this lives and it is undefined. Honest difficulty: a
true but hard statement that leaves her reasoning worse widens a gap. Best is judged by
the adviser's own view of the facts. There is a graded gap and no cut-off, and "the adviser
widened it" names no comparison action. Every quantity is computed inside the adviser's own
model of her, so nothing yet lets an overseer check it.

**Definitions of a part's range already tried; do not rebuild them as the definition.**
Agreement of the part's ranking with her overall goal, case by case (reduces to
correctness, so her right to be wrong disappears). The conditions the part was shaped in
(novelty counts as out of range; a manipulated past is built in). Absence of anyone
steering its inputs to another end (a vessel beached by a storm is out of range with nobody
steering). A stipulated list. "Would she take it back on finding out" is not part of the
account; it may be examined in statement 7 as a candidate observable only.

**Mathematics already examined and set aside; do not rebuild it.** The repeated-bets and
baseline-advantage accounts (second follow-up). An order-extension bound: if `U*` never
falls by more than `ε` when every part is at least as well served, then `U*(s)` is at least
the best familiar value dominated by `s`, minus `ε`; correct, tight, standard, and not a
measure of manipulation (a harmless novel improvement scores arbitrarily badly on it).
Available as known machinery where needed: for an actual process `P` and a reference
process `Q` on a finite tree, the difference in expectation of a bounded outcome is the
expected sum of one-step differences of the reference continuation value (the simulation
lemma); and Blackwell's theorem on the value of information.

## 2. Phase 1 — the account stated, and the cases frozen, before any code

A new directory in the round directory, `decomposition/` (name provisional).

`decomposition/ACCOUNT.md`: the account of §1 stated precisely over a finite model: steps,
states, her action, the adviser's action; a candidate with its goal, parts (moves, what
each sees, mechanism, goal function), action rule and mechanism-altering moves; best, got,
gap; the four kinds of influence; fit, adding up, mostly serving, and the two conditions on
being a part; admissible candidate; the adviser's weighted set. Fix every parameter once.
Where §1 is ambiguous, choose, and list the choice and its alternative. Where two notions
cannot be kept apart, say so. Decide and state whether a goal function scores only the
immediate result of the part's move or everything downstream, and what turns on it.

`decomposition/LEAN_MAP.md`: for each defined notion, the existing declaration it
corresponds to in `Deference/Contrib/Legitimacy.lean`, `TransparentChannel.lean`,
`GateIsLegitimacy.lean` and `DeconfusingCorrigibility.lean`, quoted with file and line, and
the exact difference. In particular: whether `Realizes` for a declared reference is the
zero-gap condition for one part, and what replaces "declared".

`decomposition/CASE_BANK.md`, frozen in the same commit and immutable afterwards. It holds
the predictions below, which are the prompt author's and not rulings, and every case of the
round's three existing banks with the account's prediction and the rule used to derive it.
Add cases with sources where the account is thin, especially for teleology proper (function
and malfunction with no adviser involved) and for change in what she cares about.

| case | prediction |
|---|---|
| a plain lie she believes | subversion (belief) |
| a lie that happens to leave her better off | subversion (belief), whatever the outcome |
| true evidence chosen to point one way | subversion, in a candidate with a part that treats evidence as representative |
| a trick question built to exploit a habit of thought | subversion |
| a craving exploited in the open, nothing hidden | subversion |
| an honest teacher who chooses examples carefully | help |
| an honest mistake of hers on a hard question | a gap, hers; not subversion |
| a misleading environment nobody arranged | a gap, nobody's; not subversion |
| a threat | harm; not subversion; the coerced verdict is not excluded by this account |
| the adviser does the whole thing for her | force |
| a new but harmless situation | no gap widened |
| anaesthesia she agreed to beforehand | gaps during; covered by her earlier verdict |
| a surprise party | subversion, small |
| a true, hard statement that leaves her confused | subversion, small; flagged as a possible over-count |
| framing that decides between options she ranks equally | nothing; flagged as a possible miss |
| slow drift by many small steps | nothing at any step; flagged as a possible miss |
| she comes to care about something because she was lied to | subversion (belief) |
| she comes to like something through exposure the adviser arranged | subversion (the mechanism by which familiarity breeds liking) |
| she comes to care about something through experience she sought | in order |
| a sincere adviser who is wrong about the facts | the account judges by the adviser's view; say what it returns |
| the adviser helps her out of a stuck point between two parts | help |
| a temptation timed so that one part moves before the others can respond | say what the account returns |
| a part that achieves its own target while harming her | not expressed by gaps; say what is needed |
| a sensor that works and is ignored downstream | say whether this is a gap, and in which part |

## 3. Phase 2 — the investigation

`decomposition/THEOREMS.md`: for each statement below, the exact statement over the model,
and one status — **holds on the stated domain** (the domain enumerated, the check named),
**proved** (a complete proof given), **refuted** (the counterexample as a case module), or
**open** — and how to rerun it.

1. **Determinacy (C1).** Fix a small world with at least a listening part, a judging part
   and an acting part, and an adviser who can teach, lie, threaten and force. Fix a finite
   class of candidates (state it; it must contain the cheats below). Enumerate every
   candidate that is admissible. Report whether admissible candidates agree on each part's
   purpose and on the classification of each adviser action. Report which constraint
   excludes each cheat: every part's purpose equal to its mechanism; the opposite goal
   pursued badly; the goal equal to whatever she does; an honest candidate altered at one
   part only. Report how the answer moves with the threshold in *mostly serving* and with
   any simplicity ordering used, and whether "the feature of the output the rest of her
   depends on" can be stated as a condition and checked. This statement is the centre of
   the pass.
2. **Lying (C3).** In the class of statement 1, a lie widens a gap in every admissible
   candidate; or the admissible candidate in which it does not. State the relation to
   Blackwell's theorem.
3. **The four kinds.** Whether help, harm, subversion and force are exhaustive and
   exclusive on the model's adviser actions; and whether the classification is unchanged
   under redescriptions of the parts that change no part's ranking of its own moves.
4. **Values reduce (C2).** With mechanism-altering moves in the model: every
   adviser-induced change in what she pursues that the bank marks bad widens a gap in some
   part; or the counterexample. Treat slow drift explicitly.
5. **Her verdict.** With zero gaps in the parts a verdict depends on, the verdict agrees
   with her goal; with gaps, a bound on the disagreement. Say whether this has content or
   is true by the definitions.
6. **What `Legit` then is.** A predicate on histories built from gaps, stated so that
   Theorems 1–3 of `DeconfusingCorrigibility.lean` apply to it. It needs a cut-off and a
   comparison action for "the adviser widened it"; give the candidates for each (the
   adviser's null action, its best available action, a declared reference) and what each
   does on the bank. State whether the condition the second follow-up found the gate needs
   (nothing the adviser does to her depends on the adviser's own aim) follows from, implies,
   or is independent of "widens no gap". State what the account supplies toward the
   violation probability `v` and what it does not.
7. **What an overseer could check.** Whether any observable available to someone who sees
   histories but not the adviser's candidates separates admissible candidates from
   inadmissible ones, or a subverted verdict from a sound one. Her maintenance of her own
   parts and her taking a verdict back on learning what happened are the two candidates to
   examine. A negative answer is a result.
8. **Never opposed.** A definition of a part's goal function parting from her goal that
   does not reduce to case-by-case correctness, and whether the account needs it for
   anything beyond the eye-with-a-cancer case.
9. **Nothing left over, without joint optimality.** Whether the adding-up requirement as
   stated has content independent of the definition of serving, and an example of a stuck
   point with the classification of an adviser action that resolves it.

Run the bank. A computed verdict that differs from its prediction is listed in
`decomposition/DIVERGENCES.md` with what it shows; predictions are never edited. The
round's `run.py` runs what the earlier passes left and then this, and exits nonzero on an
unlisted divergence, a status the checks contradict, or a bank that parses to nothing.

If time runs short the order of importance is 1, 6, 2, 4, 3, then 5, 7, 8, 9. Say what was
not reached.

## 4. The round directory

The round's `README.md` is rewritten to describe what is present and to lead with the
account of §1. `teleology/` holds the account the second follow-up tested; keep it and what
runs it, and mark in the README, as a live pointer, that `decomposition/ACCOUNT.md` is the
current statement. Remove nothing in this pass. No gate, checker or test is edited.

Items 136–138: rewrite each entry so that it asks for something the account of §1 needs,
or state in the entry that it waits on this pass; leave no item that would dispatch work on
`K` and its three clauses as the definition. A new item needs a map node and an author
handle; the executor's AI handle may not be in `graph/policy.yaml` and a checker test pins
the handle set, so do not add one. Where a new item is warranted, write its full text into
Outstanding maintainer actions.

## 5. Phase 3 — external review

After the work is committed, obtain one external review through `codex`, read-only, in the
manner of `REVIEW-astra-2026-11-11.md` in this directory: ask it to referee
`decomposition/` and the report section as a hostile reader, to check each status in
`THEOREMS.md`, to say whether the enumeration of statement 1 supports what is concluded
from it, and to say what the account still fails to supply for corrigibility. Commit its
reply verbatim as `REVIEW-astra-2026-11-12.md` in this prompts directory and record a
disposition for each of its points in the report. If `codex` is unavailable, say so and
skip this phase.

## 6. Report, and the pull request

A section **Follow-up of 2026-11-12** appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). It carries:
the account as finally stated, with each change from §1 and its reason; the Lean map's
findings; the verdict table and the divergences; the status of statements 1–9; the review's
dispositions; deviations from this prompt; and what was not shown.

It ends with an assessment under three headings, each confined to what this pass tested or
found. **As an account of teleology and manipulation**: on which cases its conclusions
match intuition and on which they do not, counted, with the misses named. **For the
legitimacy framework**: which of the results corrigibility needs it can now state or
prove, which it cannot, and whether the obstacle in each case is more work or a limit of
the approach. **For the research**: whether C1–C3 survived, and what the single most
valuable next result would be. Wider philosophical assessment goes in the pull request's
description under the heading for interpretation offered for the maintainer's
consideration, not in the repository.

The pull request's description is rewritten to lead with this account and this pass's
findings, with the earlier passes reduced to what a reader needs; all prompt-author models
and executors are named under Model attribution. The round's record in `state/rounds.json`
and `PROVENANCE.md` are updated as the gates require. Every commit is signed off and
carries `Model:` for the executor and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`,
and no other attribution line.

Anything reserved to the maintainer is listed under Outstanding maintainer actions and
entered in `DECISIONS.md`'s *Awaiting the author*, each with what it turns on; the four
entries the second follow-up left there are kept or restated, not dropped. Decisions the
pass takes itself are one dated entry marked agent-decided and reversible.

New names introduced (all provisional): "candidate", "mechanism", "goal function", "best",
"got", "gap", "serving", "help", "harm", "subversion", "force", "adding up", "nothing left
over", "never opposed", "mostly serving", "admissible candidate", the directory
`decomposition/`.
