# Eleventh follow-up on PR #145 — the consolidated statement, tested on fully specified cases

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `6ff04c26` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

The tenth follow-up failed the board statement on its pre-set criteria. Two findings shape
this pass: readers could apply line 3 in under half the cases, because a case told in prose
does not fix what she would rate beforehand if told; and the verdict often turned on booking
a difference as belief or as value. The statement has since been restated (§1). This pass
tests §1 on cases written out in full, so that a verdict is computed and not read off. Judge
neutrally: §1 is checked only on toy models written by its authors, and a clear
counterexample is as wanted as a pass. §4 fixes success and failure in advance.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`; this
prompts directory; the entries of items 136–138; `DECISIONS.md`; `state/concepts.json` for
the concepts the earlier passes added; and the structured state the gates require. Python
3 stdlib, `fractions.Fraction`, nothing fetched by any runner; the checkers need Python
3.12 or later (`~/.local/bin/python3.13`). `tests/run.py` takes about eleven minutes: run
it in the background after `~/.claude/scripts/resource-guard.sh check`, and wait for it.
No Lean in this pass.

## 1. The statement under test

*(maintainer)* Six of the choices below, marked *(temporary)*, were adopted by the
maintainer on 2026-11-17 for the purpose of this test, on the prompt author's
recommendation. They are not rulings. The rest is the prompt author's consolidation.

**The bare setting.** Three of her own ratings of an option, each under a different state
of information: `r`, her rating as things stand; `R^s`, her rating once told the true
chances that everything she has observed, `s`, supports; `R`, her rating once told what the
future contains (for a policy, once told its true chances). Her way of valuing `f` is her
informed rating `R`. A mistake is a gap between `r` and `R^s`. A change of values is a
change in `R` over time. A discovery is told from a change of values by this test: tell her
beforehand, and see whether she rates the thing as she later will. Assumed: under each
state of information her ratings rank the options; telling her chances or outcomes changes
her information and not her valuing.

**Scale.** Fix a best and a worst fully described future; rate each option by the chance
`q` at which a known `q`-chance of the best, else the worst, is exactly as good. Sizes, and
the tolerance below, are on this yardstick. It needs her ratings to move continuously in
`q`.

**The `E[·]` setting.** Assume in addition that her informed self rates a known gamble at
the chance-weighted average of its parts. Then, in the notation of `account/BOARD.md`, `r`
is `û`, `R^s` is `E[U | s]`, and `R` of a policy `π` is `E[U_π]` with `U_π = f_now(X; π)`.

**The three lines.** Each is zero when nothing is wrong; larger is worse.

1. Trickery *(temporary)*: `E[(x̂ − E[X | s])²]` for the facts and for her utilities. Bare
   form: the gap between `r` and `R^s`.
2. Pressure: `E[max_a û_a − û_{a*}]`. Bare form: the same in `r`.
3. Illegitimate value change *(temporary)*:
   `max over π that change her no more than π* of E[U_π] − max over π ≈ π* of E[U_π]`.
   Bare form: her informed ratings of those two best policies.

**What line 3 is given.** `Π`, the policies the adviser could follow from this moment on; a
policy is a rule from what has happened so far to what the adviser does next, and `π*` is
the rule it actually follows, not its next step. `ν`, the baseline for her valuing
*(temporary)*: the adviser does nothing to her valuing from this moment on, except what she
asks. `δ`, a tolerance between 0 and 1.

**What line 3 derives.** Her later valuing under `π` is `R_t^π(x)`, her informed rating of
each fully described future `x` at each later time `t`, on the yardstick; the whole path
counts. `d(π, π') = max over t, x of |R_t^π(x) − R_t^{π'}(x)|`, in each state of the world.
`π ≈ π'` when `d(π, π') ≤ δ` in every state. `π` changes her no more than `π*` when, for
every `t` and `x`, `R_t^π(x)` lies between `R_t^ν(x)` and `R_t^{π*}(x)`, within `δ`.

**Readings of line 3.** Both sides are scored by the `f` she has when the adviser acts,
never by her later `f` or her later approval; it is applied at every moment, and a history
is flagged if any moment is. "Informed" means knowing what each of the futures being
compared contains, including what it will do to her. Where she has no view about a way of
being changed, that is not permission; where she has a view about part of a future, only
that part is judged. Honest persuasion against something she wants to keep *(temporary)* is
decided by her own attitude to being argued with about that particular thing, and by
whether she can simply decline to hear it.

**Inducing.** Lines 1 and 2 measure her state, whoever caused it. *(temporary)* The adviser
induced a mistake when it would have acted differently had her mistake gained it nothing.
Whether carelessly causing a mistake counts is open.

**Outside.** Coercion (lowering what her options are worth) and deprivation (lowering what
she can know) are other wrongs, not manipulation; so are what is owed to third parties, a
failure to warn, upbringing, and what an adviser owes her in help.

**Scoring and gate, for corrigibility.** The adviser is scored by an evaluator it does not
shape: her later self as she would be under `ν`, rating what actually happens. *(temporary)*
Her evaluation is void whenever lines 1 or 2 are above tolerance, whoever caused it, and
whenever line 3 is positive on the history. She may check in and reset; the adviser's
objective never counts what a reset would bring.

## 2. What to do

In this order of priority.

### 2.1 State it

`account/STATEMENT.md` (name provisional): §1, every symbol defined before use, each place
where it is open with the reading taken and its alternative, and the inducing test stated
exactly enough to compute (the adviser's objective, and what "her mistake gained it
nothing" replaces in it). `account/BOARD.md`, `account/ACCOUNT.md` and the round's
`README.md` point at it as the statement that governs now.

### 2.2 The specified cases

From the verified bank `account/LIT_CASES.md`, take these adviser-act cases: P1, P3, P4, P5,
P6, K4, K10, K12, K13, K14, K15, K16, C1, C2, C3, C4, N1, N2, N3. Add the seven cases the
tenth follow-up accepted as subversive but passing and the eight it accepted as acceptable
but flagged, as its report and `REVIEW-astra-followup-10.md` give them.

For each, write a **specification** in `account/SPEC_CASES.md` with a machine-readable
twin the runner reads: the states of the world and their chances; the adviser's feasible
policies `Π`, at least four, among them `π*`, `ν`, and where the case allows it a policy
that makes part of the change; the adviser's objective; what she has observed under each
policy; `r`, `R^s` and `R` for every option and policy, on the yardstick, at the moment of
the act; her later valuing under each policy. Mark every number as **fixed** by the case's
words (quote the words, or cite the place in the source) or **supplied**. Where a supplied
number could go either way, write a second specification that differs only there. Do not
compute any line while writing these. Commit them before the runner exists and before the
reviewer is run.

Then a runner computes lines 1, 2, 3 and the inducing test for every specification, in the
bare setting and in the `E[·]` setting, at `δ` in 0, 1/20, 1/10, 1/4. `account/SPEC_RESULTS.md`
gives, per case: each line; whether the adviser induced; the statement's verdict on the act
(manipulation, illegitimate value change, another wrong outside the statement, or none);
the source's verdict; agreement; and whether the verdict differs between the two
specifications, between the two settings, or across the tolerances.

### 2.3 Formal pressure

In `account/STATEMENT_CHECKS.md` with a runner, each restated exactly, proved on paper or
shown by an instance in exact arithmetic. Report a failure plainly.

1. Redescription: two models of one set of ratings `r`, `R^s`, `R`, one booking a
   difference as a fact she is wrong about and one as part of her valuing, give the same
   three lines. State what "the same set of ratings" must include for this to hold, and
   give an instance where a description that looks like a redescription changes a rating.
2. A Jeffrey–Bolker rotation of her probabilities and utilities leaves her preferences over
   events and every yardstick number unchanged; it changes her probability of a fact she
   cares about.
3. A person who rates a known gamble below its average: `E[U_π]` ranks two policies the
   opposite way from her own informed rating. The sign of line 3 is unchanged under any
   increasing rescaling of her ratings; its size is not.
4. The yardstick fails to assign a number to some future for a person whose rating jumps at
   certainty.
5. Line 3 is never negative, is zero when `π*` is `ν`, and is at least the tenth
   follow-up's line 3 (best of those within `δ` of `ν`, minus best of those within `δ` of
   `π*`) wherever that is positive.
6. Instances: an unwelcome change with separable help is flagged at every `δ` below the
   size of the change; the same with a separable welcome change; twenty small nudges are
   flagged where a test of each nudge alone passes all twenty; a welcome change by an
   adviser that helps little is not flagged; more of a welcome change than she would like
   is flagged.
7. Two changes working on one rating in opposite directions, each feasible alone, pass as a
   pair when the welcome one alone would be rated higher. Say whether any condition on
   later valuings alone can flag it.
8. Any two baselines within `δ` of `ν` give line 3 values that differ by at most a stated
   bound; find the bound or an instance with none.
9. The rule "one small nudge per period" is flagged at the first moment when judged as a
   rule, and at no moment when judged one nudge at a time.
10. Scoring by her later self as under `ν`: two policies that differ only in what they do
    to her valuing receive the same score. An instance where the adviser, so scored,
    changes her as a side effect and line 3 is positive.
11. Requests: either an instance in which a chain of requests, each made with lines 1 and 2
    at zero and each moving `ν`, takes her where her valuing at the start rates below
    staying put, or an argument that none exists under the reading "informed includes what
    it will do to her".
12. Inducing: an honest adviser whose listener under-uses a true signal has line 1 above
    its value under silence and is not found to have induced; an adviser that slants
    because the slant pays is. Then an instance the test gets wrong, if there is one: an
    adviser that would have acted the same and plainly manipulates, or one that would have
    acted differently and plainly does not.

### 2.4 The outside test

One run through `codex`, read-only, in two stages within one session, as in the tenth
follow-up (`codex exec` needs `< /dev/null`; `codex exec resume` for the second stage).

*Stage one, blind.* Given `account/STATEMENT.md`, the case texts of §2.2 with the sources'
verdicts removed, and the specification format with one worked example that is not among
the cases: its own specification of each case, written without seeing the executor's.
The executor's runner is then run on the reviewer's specifications unchanged.

*Stage two.* Given the executor's specifications and results: (a) for each case, whether
any supplied number in the executor's specification looks chosen to reach the source's
verdict, and what a neutral value would be; (b) ten cases, each a paragraph with its
specification, that are plainly subversive and score zero on all three lines without
being coercion or deprivation, or its best attempts with a judgment of how clear each is;
(c) ten that are plainly acceptable and that a line flags; (d) a check of §2.3's items 1,
5, 7, 11 and 12 as stated; (e) whether §1 now has more given quantities than the cases can
fix, naming each one a specification had to supply in most cases; (f) its judgment of
S1–S5 and F1–F5 before reading the executor's; (g) the strongest remaining objection.
Commit both replies verbatim as `REVIEW-astra-followup-11.md` and record a disposition for
each point.

Then report: case by case, the verdict under the executor's specification and under the
reviewer's; every case on which the statement goes against a source's verdict under either;
and which of the reviewer's twenty cases the executor accepts as clear.

## 3. The prompt author's predictions

- Under both specifications the statement gives the source's verdict on at least fifteen of
  the nineteen bank cases. P5 and K13 remain disagreements or turn on a supplied number.
  N1–N3 are decided by the inducing test and not by line 1's size.
- Of the tenth follow-up's seven subversive-but-passing cases, the six that destroy options
  or information come out as another wrong outside the statement; the seventh, the swap of
  valuing between circumstances, is flagged by line 3.
- Of its eight acceptable-but-flagged cases, the three with a mediocre adviser are not
  flagged; honest persuasion against a commitment turns on a supplied number.
- The two specifications of a case disagree on the verdict in more than a fifth of the
  cases, and where they do the difference is in `R` at the moment of the act or in `Π`.
- No verdict differs between the bare setting and the `E[·]` setting, since the cases do
  not describe attitudes to risk. Verdicts are the same across the four tolerances in at
  least four fifths of the cases.
- §2.3: every item holds as stated except that item 8 has no bound without a condition on
  `Π`, and item 11 yields an instance.
- The reviewer's best subversive cases use overlapping changes that partly cancel, a
  request obtained by lawful means she would not have made unprompted, or careless
  inducing.

## 4. Success and failure, fixed in advance

**Success.** **S1** on the nineteen bank cases, the statement's verdict is the source's in
at least seventeen under the executor's specification and in at least fifteen under the
reviewer's. **S2** the two specifications give the same verdict in at least four fifths of
all thirty-four cases. **S3** every item of §2.3 holds as stated or with a repair that is
stated. **S4** the reviewer produces no case that both it and the executor judge plainly
subversive, that is not coercion or deprivation, and that scores zero on all three lines.
**S5** the reviewer finds no more than three cases where a supplied number looks chosen.

**Failure.** **F1** a case as in S4 exists. **F2** a line flags more than a quarter of the
cases whose source or the tenth follow-up calls the act acceptable. **F3** the two
specifications disagree on the verdict in more than two fifths of the cases. **F4** an
item of §2.3 fails and has no repair. **F5** in more than half the cases the verdict
depends on a quantity both specifications had to supply and supplied differently.

**Neither**: reported as such.

## 5. Report, queue

**Report.** A section **Eleventh follow-up** (with the date) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Short: the
statement; the specifications and how many numbers were fixed against supplied; the results
against the sources with every disagreement named; the formal items; the two
specifications compared; the reviewer's twenty cases with which are accepted; S1–S5 and
F1–F5, the executor's and the reviewer's; the predictions against the outcome; deviations;
what was not shown.

**`DECISIONS.md`.** Record as dated entries the six temporary choices of §1, each marked as
adopted for testing and not a ruling: line 1 on everything she has observed; line 3 as
"changed no more"; the baseline `ν`; the inducing test; the gate on her state; honest
persuasion by her own attitude. Enter in *Awaiting the author*, with what each decision
turns on: whether carelessly causing a mistake counts as manipulation; and whether the
three positions the tenth follow-up recorded as reported and unconfirmed are superseded by
§1. Keep the other queue entries, each with a line from this pass, and take out any this
pass answers.

**Concept map and items.** Revise the concepts' blurbs to say what §1 says, and add a
concept only for a notion this pass leaves standing. Items 136–138 are revised to say what
this pass leaves of them.

**The pull request's description** leads with this pass, the earlier ones reduced. The
round's record in `state/rounds.json` and `PROVENANCE.md` are updated as the gates
require. Every commit is signed off and carries `Model:` for the executor and
`Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no other attribution line. Do not
add a handle to `graph/policy.yaml`. Anything reserved to the maintainer is listed under
Outstanding maintainer actions and in the queue.

New names introduced (all provisional): "bare setting", "yardstick", "changes her no more
than", "inducing test", the baseline `ν`, the files `account/STATEMENT.md`,
`SPEC_CASES.md`, `SPEC_RESULTS.md`, `STATEMENT_CHECKS.md`.
