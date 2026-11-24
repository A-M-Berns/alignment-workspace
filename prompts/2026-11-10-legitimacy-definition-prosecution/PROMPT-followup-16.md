# Sixteenth follow-up: the three-sentence statement, its Lean model, and a ledger of what stands

Dispatched 2026-11-24 by the maintainer through a Claude Fable 5.2 session, which wrote this
prompt. You are the executor. You have write scope on this branch
(`round/2026-11-10-legitimacy-definition-prosecution-followup-15`, pull request #149) for the
paths named below. Read `AGENTS.md` first; it binds you. This follow-up puts on record the work
done in conversation on 22–24 November, which replaced the foundation the fifteenth follow-up
recorded, and it ends with a ledger. **The ledger is the point of the round**: when you return,
the maintainer must be able to read off exactly how much of this line is stable and where the
remaining work should go.

## 1. What happened, in brief

The fifteenth follow-up's account (gain through her mistakes, *avoidable gain*) was abandoned as
the foundation. The diagnosis: every earlier definition measured her against the truth or against
a hidden version of herself. What replaced it:

- Mistakes are judged **by the adviser's lights**; his view is used only to say what he owes her,
  never as where she ought to end up, and never with an assumption that he is more accurate.
- Legitimacy is **three sentences** (nothing untold that matters; nothing done to her behind her
  back and nothing against her own judgement; she can stop it), with a formal statement meant to
  match them.
- **What he does to her** is separated from **what he does to her options**. The second is her
  authority's business: what stopping costs her, bundling, penalties, payments, threats, starting
  something over her refusal.
- The statement was pressed by nine outside reviews and tested blind against a bank of cases from
  Noggle's book. A Lean model derives every object the clauses use from one structure and proves
  redescription invariance of the whole statement, that a move which changes nothing in her bears
  no effect, four refutations and a non-trivial witness.

## 2. Inputs

All under `/Users/anson/hub/scratch/legit-2026-11-20/` unless a full path is given. Nothing there
is in the repository yet.

- `STATEMENT-frozen-1124.md` — **read this first, in full.** The informal statement (frozen by the
  maintainer on 24 November), the formal setting and statement, the accepted consequences, what is
  open, and the standing. It is a private working page: it names private paths and has a private
  register. You rewrite its content for the repository; you do not copy it.
- `worked/LegitModel.lean` — the temporal model. It typechecks against this branch with
  `~/.claude/scripts/safe-lake.sh --dir=lean env lean <file>` and audits to the three standard
  axioms. `worked/Plug.lean` and `worked/Round1.lean` — earlier scratch files: a scoring in the
  sense of `DeconfusingCorrigibility.Scoring` built from any decidable legitimacy predicate through
  `Legitimacy.gateValue`, and the gate theorem (soundness and completeness errors of a gate against
  the size of the penalty window). `worked/Legit7.lean`, `worked/Legit5.lean` — superseded
  one-decision transcriptions, for the record of what was tried.
- `vc2/eighth_checks.py` — 41 exact cases of the formal statement on a small model, expectations
  fixed before running. `vc2/cost_checks.py` — 20 exact cases of a candidate cost-of-stopping
  clause that is **not** part of legitimacy (see §3, ruling 9). `vc2/seventh_checks*.py`,
  `sixth_checks.py`, `fifth_checks.py`, `model_check*.py` — earlier versions.
- `noggle-bank/two-est/` — the blind case runs. `CODING11.md`, `coded11_{A,B,C}.json`,
  `score11.py`, `RESULTS_RULE.md`: the disclosure rule of 23 November. `lapse_split.py`: the lapse
  clause alone. `CODING14.md`, `coded14.json`, `score14.py`: prohibiting against regulating
  pressure. `CODING15.md`, `coded15.json`, `score15.py`: the earlier-rating clause, first sheet.
  `CODING16.md`, `coded16.json`, `score16.py`: the same with her earlier rating read as of her last
  settled decision. The `blind*.json` and `../part_*.json` files hold paraphrases of the book's
  cases and **stay outside the repository**; the repository's
  `account/noggle_bank.json` already carries each case's id, place in the book and the author's
  verdict, which is all a scorer needs.
- `review-1123/` — nine briefs (`BRIEF.md` … `BRIEF9.md`) and the outside model's replies
  (`REPLY.md`, `REPLY2.md`, `REPLY4.md` … `REPLY9.md`; `CASES3.json` is its answer to `BRIEF3.md`).
  Access conditions, which the record must state: review 1 was a fresh session on a neutral brief;
  reviews 2 to 7 resumed that session, which ran with this worktree as its working directory and
  with write access, and during the seventh the reviewer read files of this repository and ran a
  workspace command, so reviews 2 to 7 are not blind to the project; reviews 8 and 9 were fresh
  sessions in an empty folder with a read-only sandbox, and their logs show one command each,
  reading the brief.
- `/Users/anson/hub/notes/Value-change test (2026-11-23).md` and `vc2/RESULTS_VC2.md`,
  `RESULTS_ADV.md`, `RESULTS_V3.md` — a value-change test of an earlier form of the statement.

## 3. The maintainer's positions (Anson Berns, 22–24 November 2026)

Record these in `DECISIONS.md` as one dated entry of working positions, each marked as held for
testing unless it says ruled. They are his, stated in conversation; the words in quotation marks
are his.

1. Mistakes are classed by whether the adviser takes them to be mistakes. "I want to ensure we're
   not ever smuggling in an idea that like the advisor is always accurate or even more accurate
   than the principal." Noggle's definition "is absolutely what we should stick with as much as we
   can".
2. The bank of cases from Noggle's book is the standard a definition is tested against, in
   preference to his own case-by-case intuitions.
3. Disclosure is "a prerequisite to any deal with someone you think is misvaluing the relevant
   concerns". For every estimate of hers it is assumed open to him to tell her his own estimate
   and how sure he is.
4. Legitimacy is non-manipulation together with openness about what his conduct does to what she
   values. There is no separate clause for value change and no limit of substance on what she may
   come to value.
5. Slow drift in which each step is consented to is legitimate where there is no other wrong.
   Legitimacy must not turn on classifying a change as discovery or as change; robustness to
   redescription is "important/indispensable". The earlier value has priority, and this must not
   become an incentive to lock her values in.
6. Starting a stoppable influence without her agreement is acceptable where it violates no
   authority of hers; starting it over her refusal is a violation of her authority, not a failure
   of legitimacy.
7. A primitive of "response to content" or of her judgment is to be avoided; her response to being
   told his views is the one primitive of that kind kept.
8. Accepted consequences 1 to 5 of the frozen page (foreseen drift disclosed at the start; an
   influence that makes her want it to continue is legitimate if told, as later narrowed; he must
   say he has something relevant and she may decline; unannounced help in acting on her own rating
   is legitimate; a sincere adviser who is wrong satisfies the statement).
9. Ruled 24 November: the cost of stopping, bundling and coercion belong to the authority side,
   "as long as it can easily" handle them.
10. Ruled 24 November: "akratic mistake pressure is relevantly different from coercion", and
    "open, stoppable nagging should fail legitimacy".
11. Ruled 24 November: "her own rating" in the pressure clause is her rating as of her last
    decision before he began; a passing state is not a decision. This is the check-in of the
    positions `2026-11-16--presumed-check-in-and-moving-baseline` and
    `2026-11-17--gate-on-her-state`, and he may not count on her ratifying afterwards.
12. The informal statement is frozen for testing in the form on the frozen page. The formal
    statement is not frozen.

Not ruled, and to be recorded as open, not as positions: whether an adviser must mention an option
he believes she would rate above those she has, including someone else's; whether "unless she
asked" is the right exception, given the view that consented manipulation is still manipulation;
what the bound on the cost of a decision of hers is for a service paid for by its influence, and
for an exit penalty she knowingly agreed to that he can no longer call off.

## 4. Deliverables

Work in the order given. **Commit and push to `origin` after each lettered deliverable**, so that
what is done survives if the run is cut short.

**A. The statement.** `account/LEGITIMACY_STATEMENT.md` in the round's directory: the three
sentences, what is understood with them, the formal setting and statement, the accepted
consequences, in the repository's verification register. No private paths, no account of how it
was reached. Then mark `account/MISTAKES_ACCOUNT.md` and whatever else the fifteenth follow-up
presented as the governing account in the way this round's directory already marks an earlier
attempt (see the banner on `account/VALUE_CHANGE.md` and the `earlier-attempts/` tree), saying what
replaced it.

**B. The Lean.** `lean/Workspace/Deference/Contrib/LegitimacyModel.lean`, from
`worked/LegitModel.lean`: a repository namespace, a header in the register of the neighbouring
files, `#print axioms` on every theorem. Do not weaken a statement; a definition changed for any
reason is a declared deviation with the reason. Then, in the same file or a second one, the link
to the corrigibility result: for a `Model`, the scoring obtained from `Legit` through
`Legitimacy.gateValue` is a `DeconfusingCorrigibility.Scoring` (port from `worked/Plug.lean`), and
the gate theorem (port from `worked/Round1.lean`). State plainly in the header the five respects
in which the model is simpler than the statement of A: a view's bearing is computed per view, not
jointly; the adviser has one belief, not one per time; "beyond what plainly telling would do" is a
set of moves marked as tellings; "silent where she had no earlier rating" is not represented; what
is on offer is a set he designates and proves proper, not the largest such set. Build with
`~/.claude/scripts/safe-lake.sh`, never `lake` directly, after
`~/.claude/scripts/resource-guard.sh check`. No `maxHeartbeats` option. Registration follows the
precedent of the fourteenth follow-up on this line (read its report section and
`followup-14-registration.patch`): prepare what the maintainer would apply; do not edit a claims
registry yourself unless that precedent did.

**C. The exact checks.** `eighth_checks.py` and `cost_checks.py` into `account/` under names of
your choosing, wired into the round's `run.py`, each failing on any case that differs from its
expectation. A short results document for each that the runner recomputes, saying which
quantities a case supplies and which the script computes: in `eighth_checks.py` the chance that she
goes against her earlier rating is supplied per case, and the document says so.

**D. The case runs.** The coding sheets, the codings keyed by case id with no case text, and the
scorers for runs 11, 14, 15 and 16, the scorers reading verdicts from the repository's
`account/noggle_bank.json` and wired into `run.py`. One results document the runner recomputes.
It reports counts as counts, never as rates of a population, and states for each run what the
scorer was fixed before, which predictions were written in advance and which of them failed (in
run 14 the prediction that regulating pressure would miss a third or more of the settled cases
was wrong; in runs 15 and 16 the prediction about cases of bent judgement could not be tested,
because the coder found two such cases in 152). For the value-change test of 23 November, include
what is ours or the outside model's and exclude any text drawn from a published source; say which
is which.

**E. The reviews.** `REVIEW-astra-followup-16.md` beside the earlier ones: each brief followed by
its reply, verbatim, except that local filesystem paths are replaced by `[path]`, with the number
of replacements stated at the top; and the access conditions of §2 stated at the top. For each of
reviews 8 and 9, a table in the report: finding, whether it holds against the statement as it then
stood (check it yourself; do not take this prompt's word or the frozen page's), and what was done.

**F. The ledger.** `account/LEDGER.md`. One row per component of the line, each with:

- a verdict in the three forms standard 9 allows: **closed** (name the Lean declaration or the
  checker invocation that stands for it, and its reopening condition as a checkable event),
  **open**, or **living note**;
- the evidence behind it and its kind (kernel-checked; exact check with supplied inputs; blind
  coding by one language model against a pre-written scorer; outside review, blind or not;
  reasoning only);
- what would move it, as a checkable event;
- the `ATTENTION.md` item that carries it, filed or revised in this round.

Components, at least: the diagnosis (by his lights); sentence 1 as worded; its formal counterpart
(what is untold, proper offers, declines); the line between legitimacy and authority; sentence 2's
first half (what he does to her; picking it out); the pressure clause (her earlier rating); the
case of judgement bent for a while; sentence 3; each theorem of B; each of the five
simplifications of B; the gate theorem and the scoring link; composition with the sequential
corrigibility theorems; coverage of value change; soundness of the gate (whether legitimacy can be
evaluated at all); the cost of stopping on the authority side, including the candidate clause of
`cost_checks.py` and whether `EffectiveAuthority.lean` already expresses it; the quality of the
evidence (every coder and reviewer a language model, the statement and its exact checks by one
hand, how often anything was coded twice); the accounts this one replaced.

Then a section **Where the remaining work should go**: the open rows ranked, each with what done
looks like as a checkable event, a rough size, and whether it needs the maintainer or can be
dispatched. The prompt author's ranking, which you check against the evidence and correct where it
is wrong, saying so: an outside review of the Lean statement itself; the cost of a decision of
hers modelled on the authority side; the five simplifications removed from the model; a second
coder and a set of cases of bent judgement; composition with the sequential theorems; soundness of
the gate. End the ledger with three counts: rows closed, open, living note.

**G. The current state and the record.** `CURRENT.md` rewritten to this state. The `DECISIONS.md`
entry of §3; the two entries the fifteenth follow-up left in *Awaiting the author* are each either
answered by a position of §3, in which case they leave the queue under standard 10, or restated;
a new queue entry only where standard 10's bar is met, and otherwise the round adopts its own
recommendation as agent-decided, reversible. `ATTENTION.md` items filed for every open ledger row
that has none, through their item nodes; items 139 and 148 to 152 revised to the present state.
`VERDICTS.md`, the round's and the root `PROVENANCE.md`, `state/rounds.json`, the generated
`graph/` files from a plain checker run.

**H. The report.** A section *Sixteenth follow-up* in
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`: what was tried and withdrawn on
22–24 November (the frozen page and the review replies carry it; keep it short), the review
tables of E, corrections to this prompt, deviations, what was not shown, the attribution block,
outstanding maintainer actions. The ledger is not restated there; it is pointed to.

**I. The pull request.** Retitle #149 and rewrite its body to cover the fifteenth and sixteenth
follow-ups as the branch now stands, keeping the template's sections. The merge stays reserved to
the maintainer and auto-merge stays off. Do not merge.

**J. The gates.** The round's `run.py`; `python3 tests/run.py` and the axiom audit, each of which
runs longer than ten minutes, so run them in the background with a long timeout and wait for
them; `python3 -m checkers.graph --root .`; `python3 -m checkers.workspace_state --check`. Report
each result as it was. A gate that fails for a reason you cannot fix within your scope is reported
with its output and filed, not worked around.

## 5. Constraints

- No text of Noggle's book or of any supplied paper enters the repository. Cite only what a public
  reader can open; the private page and the conversation are not cited, quoted or dated beyond
  what §3 gives you.
- You edit no checker, test or workflow. If one stands in your way, file it.
- Do not contact the outside model. Its reviews are done.
- This worktree's hook refuses compound shell commands and heredocs: run single commands, and put
  anything longer in a script file under `/tmp`. Python is `~/.local/bin/python3.13`, run with
  `-I`. Subagents you start must be waited for in the foreground.
- Commits are signed off (`git commit -s`) and carry the trailers `Model: Claude Fable 5.2
  (Anthropic)` and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no co-author line.
  Push to `origin` only.
- New names ship provisional and are listed in the report and the pull request.

## 6. On return

Your last message states, in this order: the commits you made; each gate's result; the ledger's
three counts; the first three entries of *Where the remaining work should go*; anything you could
not do and why.
