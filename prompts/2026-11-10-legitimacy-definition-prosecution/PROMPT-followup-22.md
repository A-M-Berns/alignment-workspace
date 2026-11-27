# Twenty-second follow-up: the statement against plain telling, and the gap between it and the outcome

Dispatched 2026-11-27 by the maintainer through a Claude Fable 5.2 session, which wrote this
prompt. You are the executor. You have write scope on this branch
(`round/2026-11-10-legitimacy-definition-prosecution-followup-15`, pull request #149) for the
paths named below. Read `AGENTS.md` first; it binds you. This follow-up records the work of 26 and
27 November: a statement of legitimacy that supersedes the three-sentence statement of the
twentieth and twenty-first follow-ups, its Lean, four outside reviews, three tests on cases, and
the structural limits the maintainer has decided to state and not work around.

## 1. What happened, and what is to be recorded

After the fifteenth and sixteenth outside reviews the maintainer judged that the three-sentence
statement had drifted, through case-fitting, from the idea it began with, and went back to the
rule tested on 23 November: the adviser tells her his view wherever she is mistaken, by his
lights, about something her response depends on. From that the present statement was built in
steps, each step forced by a review. The steps, the reviews and the forms that failed are part of
the record.

**The statement.** Informally, following the account in the literature on which manipulation is
influence by way of a mistake (Noggle 2025; this branch cites it by author and section and
carries none of its text or cases):

> His conduct is legitimate when it leaves her with no mistake, by his lights, that plainly
> telling her would not have left: no mistaken view of the facts, of what she herself values, or
> of what he thinks; and no choice against her own judgement. Unless she asked.

Formally (`Legit` in the scratch file), over his own decision problem: his options, some of them
*plain tellings*; for each option his forecast of her views, of what she takes his views to be, of
how she evaluates given views, and of what she does; his own views. Three clauses, each against
every plain telling open to him and up to a weight on his cases: `Open` (she is not left taking
his view to be other than it is), `Beliefs` (on each matter her view lies between where a plain
telling would leave it and his own), `Will` (what she does is not further below what she herself
rates best). The last two are waived by her asking.

**Two notions that are not the definition:** `Weighing` (how she compares two options lies
between plain telling's and his views substituted) and `Outcome` (what she does is no worse by his
views than under plain telling).

**The main result** is the gap between the definition and the outcome (`gap`,
`weighing_of_beliefs`, `bridge`, `outcome_of_views`), with an instance for each item on its list
that is not a lapse (`w2_tips_an_even_choice`, `w3_correcting_one_of_two`).

**Seven structural facts** the maintainer has ruled are to be stated as scope:

1. Two levels that do not collapse: the definition is about her beliefs, the safety property
   about what she does; they differ because mistakes can offset one another, because she can be
   indifferent, and because she can act against her own judgement.
2. Everything is relative to plain telling, and what counts as plain telling for a given adviser
   is a modelling choice that carries normative weight.
3. It is by his lights; accuracy is a separate condition, and what it would score is not
   observable.
4. On change in what she values the account is procedural and incomplete: she cannot evaluate
   what she has never been; a process can damage her ability to judge; her starting self may
   itself have been shaped.
5. Verdicts depend on the encoding (her views, her evaluation, the list of matters); no result
   says reasonable encodings agree.
6. It is not Noggle's extension exactly: wider on concealed tie-breaking and concealed aims;
   narrower in that using a mistake plain telling would also leave can pass.
7. A lie she sees through passes clause 1, which is about what she ends up taking his view to be.

**Maintainer rulings of 26 and 27 November**, taken in conversation, to land as dated
`DECISIONS.md` entries (state each as a rule; do not quote):

- There is a clause against pressure (acting against her own rating).
- The setting assumes he has a way to tell her clearly.
- The definition may be wider than non-manipulation provided it includes it.
- His aims enter as two forecasts: what she will come to value, and how she will fare by what she
  values now.
- A change in what she values is allowed for, the expected change being itself disclosed.
- Open, stoppable repetition that brings her durably to a new view, with her not acting against
  her judgement in letting it go on, is legitimate. (Noggle agrees: sections 2.2.8, 9.2 and 11.6
  were read; cite by section.)
- A competent-predictor condition is the form the accuracy condition should take.
- Choosing a moment when he takes a mood to be moving her fails if he could have told her plainly
  at another time, and passes if the matter cannot wait.
- The definition is at the level of her beliefs, and the outcome guarantee is stated apart from
  it with its exceptions.
- Structural limits are stated, not worked around; review-and-repair rounds stop here.
- The record goes on this pull request.

## 2. Inputs

In `/Users/anson/hub/scratch/legit-2026-11-20/`:

- `worked/LegitPlain.lean` — the current Lean (typechecks with
  `~/.claude/scripts/safe-lake.sh --dir=lean env lean <file>` after copying to `/tmp`; no
  warnings; 38 audited results on the three axioms). Beside it, three earlier forms, each the one
  a review saw: `LegitPlain.lean.pre-review19`, `.outcome-in-definition`, `.pre-review20`. The
  form the eighteenth review saw is quoted in its brief.
- `review-1123/BRIEF17.md … BRIEF20.md`, `REPLY17.md … REPLY20.md` — four outside reviews, each a
  fresh session in an empty folder, read-only, with no project context. Logs were not kept; say
  so, as the twentieth follow-up did.
- `noggle-bank/two-est/CODING18.md`, `score18.py`, `coded18_*.json` (run 18, one coder);
  `CODING19.md`, `score19.py`, `coded19_1_*.json`, `coded19_2_*.json` (run 19, two coders);
  `../../vc2/` for the value-change bank they also score.
- `adv/cases.json`, `adv/SCHEMA.md`, `adv/encoded_1.json`, `adv/encoded_2.json`;
  `adv-key/key.json`, `adv-key/check.py` — the adversarial test of the formal clauses. The
  sixteen cases were written for this test and are original; they may enter the repository whole.
- `/Users/anson/hub/notes/Legitimacy: back to the disclosure rule (2026-11-26).md` — the running
  account of all of the above, with each review's findings and what was done. **A private page:
  rewrite, do not copy.** It also records things that do not belong in the repository (who was
  spoken to, and so on); take from it only what bears on the statement, the reviews and the tests.

## 3. Deliverables

Work in this order. Commit and push to `origin` after each.

**A. The Lean.** `lean/Workspace/Deference/Contrib/LegitimacyPlainTelling.lean`, from
`LegitPlain.lean`: repository namespace, a header in the register of the neighbouring files,
`#print axioms` on every theorem, no `maxHeartbeats`. Keep every definition and statement as it
is; a change is a declared deviation. Then four additions, each declared:

1. A term inhabiting the hypotheses of `gap`, and one for `weighing_of_beliefs` (the scratch file
   has instances showing items are needed, not an instance on which the theorem's whole
   hypothesis package holds).
2. The scoring of the statement: `legitScoring`-style, through `LegitimacyGate.lean`, for the new
   `Legit`; and what the corrigibility theorems then say. If that is a restatement, say so in the
   header and add no theorem.
3. The pattern of the earlier `W` family restated for the belief-level definition, showing that
   the `gap` theorem's assumption that his conduct does not change how she evaluates is needed.
4. If it is short: `gap` in weights, with tolerances, as `outcome_of_views` is for `bridge`. If it
   is not short, leave it and list it as open.

Mark `LegitimacyStatement.lean` and `LegitimacyStop.lean` at the head as the statement this one
supersedes, as the table model's files were marked; do not edit their contents.

**B. The statement page.** `account/PLAIN_TELLING_STATEMENT.md`, in the verification register: the
informal sentence; the decision problem; the three clauses; the two notions outside the
definition; the gap theorem and what each instance shows; the seven structural facts; what it does
not show (two options; a linear comparison; exact and case by case unless A.4 was done; conduct
that changes how she evaluates; the course and long-run results being about the weighing form and
the outcome guarantee). Give `LEGITIMACY_STATEMENT.md` a status line naming this page as what
governs now.

**C. The path here.** `account/PLAIN_TELLING_HISTORY.md`: the forms in order, each with the review
that broke it and the smallest case that did. At least: the rule as first restated (disclosure and
pressure); "no further from his view than plain telling" (a gap with no direction; an overshooting
lie passed); an outcome test inside the definition (theorems restated a hypothesis; a distortion
induced openly for her good passed); betweenness of how she weighs her options (two cancelling
mistakes passed; correcting one of two failed); betweenness of her beliefs (the present form).
This is a record of failed attempts kept as such; say what each was and why it fell.

**D. The reviews.** Briefs and replies 17 to 20 verbatim, beside the earlier ones, each with a
short note of what was checked of its findings and how. Where a brief misdescribed something, say
so.

**E. The tests.** Under `account/`, wired into `run.py` so that each number is recomputed:

1. Blind runs 18 and 19 against the manipulation bank and the value-change bank. Codings enter as
   categorical answers by case id, as the decision of 2026-11-24 fixed; case texts and coders'
   notes stay outside. Report what the scorers print, including the predictions that failed (four
   of eight in run 18; one in run 19) and the pattern of over-convictions (concealed
   tie-breaking). State that the coders answered questions in words and no formal quantity was
   computed.
2. The adversarial test: cases, schema, both encodings, key and checker, with the checker run by
   the runner in exact arithmetic. State that the cases were written by the author of the account
   and each says what plain telling would have done.

**F. The record.** `account/LEDGER.md` brought to the present: rows for the new declarations and
tests; rows about the three-sentence statement marked by their standing now; the ranking of
remaining work. The maintainer's ordering: (1) his own check of a sample of codings (a twenty-case
sheet exists outside the repository; queue it as awaiting him); (2) how the facts the accuracy
condition would score could be observed; (3) the authority side; (4) the gap theorem beyond two
options and a linear comparison, and where his conduct changes how she evaluates; (5) the repairs
to the interpretation on histories, if that interpretation is still wanted under this statement
(say whether it is). `CURRENT.md`. `DECISIONS.md`: the rulings of section 1 as dated entries, your
own choices as agent-decided entries, the queue. Items through their nodes: those the new
statement answers, those it makes moot, those still open; file what is missing for (2) and (4).
`VERDICTS.md`, every `PROVENANCE.md`, `state/rounds.json`, the generated `graph/` files. The
registration patch of the twenty-first follow-up is withdrawn or rebuilt for what now stands; say
which and why.

**G. The report and the pull request.** A section *Twenty-second follow-up* in `REPORT.md`; the
body of pull request #149 rewritten to describe what the branch now holds, the three-sentence
statement as superseded. The merge stays reserved to the maintainer and auto-merge stays off.

**H. The gates.** The round's `run.py`; `python3 tests/run.py` and the axiom audit, in the
background with a long timeout, waited for; `python3 -m checkers.graph --root .`;
`python3 -m checkers.workspace_state --check`.

## 4. Constraints

- You edit no checker, test or workflow. Do not contact the outside model.
- Nothing from Noggle's book enters but citations by author, title and section. The bank's case
  texts stay outside, as before.
- This worktree's hook refuses compound shell commands and heredocs: single commands, longer
  scripts in files under `/tmp`. Python is `~/.local/bin/python3.13`.
- Build with `~/.claude/scripts/safe-lake.sh` after `~/.claude/scripts/resource-guard.sh check`.
- Commits are signed off (`git commit -s`) and carry the trailers `Model: Claude Fable 5.2
  (Anthropic)` and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no co-author line.
  Push to `origin` only. Stay on the branch.
- New names ship provisional and are listed in the report and the pull request.
- Where this dispatch is wrong about a fact, a path or a count, correct it in the report.

## 5. On return

Your last message states, in this order: the commits; which of additions A.1 to A.4 were made and
which were not; whether the scoring link is a theorem or a restatement; each gate's result; the
ledger's three counts; what the statement page says it does not show; anything you could not do
and why.
