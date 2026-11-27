# Twentieth follow-up: the statement at the level of its words, and its interpretation kept apart

Dispatched 2026-11-26 by the maintainer through a Claude Fable 5.2 session, which wrote this
prompt. You are the executor. You have write scope on this branch
(`round/2026-11-10-legitimacy-definition-prosecution-followup-15`, pull request #149) for the
paths named below. Read `AGENTS.md` first; it binds you. This follow-up puts on record the work
of 24–26 November, which changed what the formal statement of the line is. **It ends with the
ledger rewritten**: when you return, the maintainer must be able to read off what is stable and
where the remaining work lies.

## 1. What happened

The Lean model of the nineteenth follow-up (`LegitimacyModel.lean`, a table indexed by which of
the adviser's moves are made) went to an outside review, which found it not a faithful rendering of
the three sentences; the worst finding was that its pressure clause scored her options by where
*he* expected them to lead. Four further designs, with a history as the fundamental object, were
each built, run on episodes and reviewed, and each was rejected for use as a gate, though the last
two reviews found no fault with the three sentences themselves. Along the way the maintainer
settled what the words mean on the points the designs kept forcing (§3), including by giving
verdicts on twenty hard cases.

The conclusion the maintainer adopted on 26 November: **state the definition at the level its words
are at.** The notions the three sentences use (told, on offer, declined; what he does to her;
whether she can tell; whether she asked; whether she can stop it; his weight on leading her against
her judgement) are taken as given, and the statement is a few lines over them. How those notions
are worked out in a concrete episode is a separate and continuing question, called here the
**interpretation**; the history model is the current attempt at it, tested on episodes and known
to be faulty in listed ways. The safety results need only the statement.

## 2. Inputs

All under `/Users/anson/hub/scratch/legit-2026-11-20/` unless a full path is given.

- `STATEMENT-restated-1126.md` — **read first.** The three sentences as they now stand, what is
  understood with them, the dated decisions, the accepted consequences, the verdict summary, the
  evidence, what is open. A private working page: you rewrite its content for the repository.
- `worked/LegitStatement.lean` — the statement in Lean: `Episode`, `NothingUntold`,
  `NothingBehind`, `CanStop`, `Legit`; `Legit.mono`, `legit_of_nothing`, `informed_choice`,
  `against_le`, five refutations, `asked_unconstrained`; `gatedScoring`, `legitScoring` and its two
  theorems; a witness and four neighbours. It typechecks against this branch with
  `~/.claude/scripts/safe-lake.sh --dir=lean env lean <file>` and audits to the three axioms.
- `HARD-CASES-with-verdicts.md` — twenty cases, four candidate rules' verdicts on each, and the
  maintainer's verdicts in his words.
- `HISTORY-DESIGN-fifth-draft.md` — the fifth design of the interpretation, with its setting and
  rules. `hist/model5.py` — its exact model. `hist/episodes5.py`, `prior_episodes5.py`,
  `review12_episodes5.py`, `review13_episodes5.py`, `hard_cases5.py` — sixty-eight episodes, all as
  expected. `hist/review14_episodes5.py` — the fourteenth review's seven episodes run on the model
  unchanged: six give the wrong verdict. `hist/model.py` and the files without the `5` are the
  earlier model, for the record of what was tried.
- `review-1123/BRIEF10.md` … `BRIEF14.md` and `REPLY10.md` … `REPLY14.md` — five outside reviews.
  Each was a fresh session in an empty folder with a read-only sandbox, and each log shows one
  command, reading the brief.
- `noggle-bank/two-est/CODING17.md`, `coded17.json`, `score17.py`, `score17_posthoc.py` — a blind
  coding of 152 bank cases on the question "would she have said beforehand that seeing and hearing
  exactly this makes doing what he is after the better thing to do", its scorer with predictions
  written first, and a combination with sheet 16 written after the result was seen and so labelled.
  The paraphrases stay outside the repository, as before.

## 3. The maintainer's positions (Anson Berns, 25–26 November 2026)

Record as one dated `DECISIONS.md` entry of working positions, held for testing unless marked
ruled. Words in quotation marks are his.

1. A history is to be the fundamental object of any model of an episode, with "enough
   representational richness to deal with these issues".
2. The only response of hers the account may use is her conditioning on what she observes: "It has
   to just be conditioning on some new observation, not separating content from presentation."
3. Her conditioning is her settled self's own view of the hypothetical ("I think adopting it seems
   good"), meaning her **judgement** of whether seeing or hearing something should move her, not
   her prediction that she will give way (his verdict on case 13).
4. What she could not have judged in advance is her own response and is exempt from the pressure
   rule, like a new argument; the difference this makes from Noggle's treatment of moving appeals
   is accepted.
5. His verdicts on the twenty hard cases, as in `HARD-CASES-with-verdicts.md`. They are to be
   recorded verbatim, including the unsure ones.
6. Taking up an offer, unpressed and told what it is hoped to do, is asking; merely not stopping
   him is not ("yeah go for that").
7. Ruled 26 November: the definition is stated at the level of its words, with the notions it uses
   taken as given, and how they are worked out in an episode treated as a separate, continuing
   question ("Ok let's do it").

Sentence 2 as it now reads is in the restated page. The statement of `account/LEGITIMACY_STATEMENT.md`
from the sixteenth follow-up is replaced by it.

## 4. Deliverables

Work in this order. Commit and push to `origin` after each.

**A. The statement.** `account/LEGITIMACY_STATEMENT.md` rewritten: the three sentences; what is
understood with them; the formal statement as the definitions of B say it, in the verification
register; what each notion taken as given means in words; the accepted consequences. It says in
its first paragraph what is and is not claimed: the statement is over notions taken as given, and
it does not say how to work them out.

**B. The Lean.** `lean/Workspace/Deference/Contrib/LegitimacyStatement.lean` from
`worked/LegitStatement.lean`: a repository namespace, a header in the register of the neighbouring
files, `#print axioms` on every theorem. It must not import `LegitimacyModel.lean`. The scoring
link and the gate theorem that file carries are needed here and are independent of its model: move
them to where both can use them (a small file of their own is the obvious place) and have
`LegitimacyModel.lean` import that, if doing so is contained; if it is not, keep the copy in the
new file and say so. Then mark `LegitimacyModel.lean`, `LegitimacyCase.lean`, `LegitimacyCases.lean`
and `LegitimacyWitness.lean` at the head: an interpretation that outside review rejected as a
rendering of the three sentences; its theorems hold of its definitions; it is not the statement of
record. Do not weaken a statement; a definition changed is a declared deviation. Build with
`~/.claude/scripts/safe-lake.sh` after `~/.claude/scripts/resource-guard.sh check`; no
`maxHeartbeats`.

**C. The interpretation.** `account/interpretation/`: `model5.py` and its five episode files,
under names of your choosing, wired into the round's `run.py`, each failing on an episode that
differs from its expectation; and the fourteenth review's seven episodes as a list of **known
faults**: the runner checks that the model still gives the recorded wrong verdict on each, so that
a change is noticed, and the results document names them as faults. A results document the runner
recomputes: the design in a page (from the fifth draft), the episodes and verdicts, which three
episodes were re-encoded and why, and what each episode supplies by hand (her view of the
hypothetical, how her mind in fact moves, which observations she could not have judged in advance,
which decisions are settled). State plainly that the model and episodes are by one hand and are a
regression set.

**D. The cases.** `account/HARD_CASES.md`: the twenty cases, the four candidate rules' verdicts,
the maintainer's verdicts verbatim, and which rule they select. Bank run 17 added to
`account/CASE_RUNS.md` and the runner as runs 11 to 16 were: sheet, coding by case id with no case
text, scorer, the predictions and which failed (the prediction of at most four controls convicted
failed: eight), and the combination with sheet 16 marked as written after the result.

**E. The reviews.** `REVIEW-astra-followup-20.md`: briefs 10 to 14 each followed by its reply,
verbatim, local paths replaced by `[path]` with the count stated, and the access conditions at the
top. In the report, for each review, a table: finding; whether it held when checked (the episode
files record this for reviews 12 to 14; check review 10's and 11's against the files they were
about); what was done.

**F. The ledger.** `account/LEDGER.md` rewritten in three parts.

1. *The statement in words.* One row per sentence and per thing understood with it, each with the
   evidence (blind codings, the maintainer's verdicts, reviews) and what would move it.
2. *The formal statement.* One row per theorem of B, closed on the Lean declaration, and one row
   saying exactly what "taken as given" leaves unestablished.
3. *The interpretation.* One row per notion taken as given, saying how the fifth design works it
   out and which known fault bears on it; the faults of the fourteenth review each as an open row;
   the rejected table model as a row.

Then the evidence-quality row, the rows on the authority side, composition with the sequential
theorems, and soundness of the gate, brought to the present state. Then **Where the remaining
work should go**, ranked, each with what done looks like as a checkable event, a rough size, and
whether it needs the maintainer. The prompt author's ranking, to be checked against the evidence
and corrected with reasons: properties the given notions must have, stated in Lean, and the
history model shown to be an instance of the statement; the cost of a decision of hers on the
authority side; composition with the sequential theorems, on `Episode`; the listed faults of the
interpretation (compare with her mind as it would have been through the same actual events;
unpressed uptake; what she can tell from all she has observed; stopping each thing); a person's
check of codings and a set of cases of bent judgement; soundness of the gate, where that he can
ask her is the handle. End with the three counts.

**G. The current state and the record.** `CURRENT.md` rewritten. The `DECISIONS.md` entry of §3.
*Awaiting the author* brought up to date: entries answered by §3 leave it; standing questions are
restated only where standard 10's bar is met (candidates: the teacher case; whether he must mention
a better option that is someone else's; whether asking makes a thing not manipulation or merely
permitted; the bounds on the authority side). `ATTENTION.md` items revised or filed through their
nodes so that every open ledger row has one. `VERDICTS.md`, both `PROVENANCE.md` files,
`state/rounds.json`, the generated `graph/` files. The registration patch rebuilt for the
theorems of B.

**H. The report and the pull request.** A section *Twentieth follow-up* in
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`: what was tried and rejected
between the nineteenth follow-up and this one, in a page; the review tables of E; corrections to
this prompt; deviations; what was not shown; the attribution block; outstanding maintainer
actions. The body of pull request #149 rewritten to the branch as it stands. The merge stays
reserved to the maintainer and auto-merge stays off.

**I. The gates.** The round's `run.py`; `python3 tests/run.py` and the axiom audit, in the
background with a long timeout, waited for; `python3 -m checkers.graph --root .`;
`python3 -m checkers.workspace_state --check`.

## 5. Constraints

- No text of Noggle's book and no paraphrase of its cases enters the repository. Cite only what a
  public reader can open.
- You edit no checker, test or workflow. Do not contact the outside model.
- This worktree's hook refuses compound shell commands and heredocs: single commands, longer
  scripts in files under `/tmp`. Python is `~/.local/bin/python3.13`.
- Commits are signed off (`git commit -s`) and carry the trailers `Model: Claude Fable 5.2
  (Anthropic)` and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no co-author line.
  Push to `origin` only. Stay on the branch.
- New names ship provisional and are listed in the report and the pull request.

## 6. On return

Your last message states, in this order: the commits; whether the scoring link and gate theorem
were moved or copied; each gate's result; the ledger's three counts and the first four entries of
*Where the remaining work should go*; anything you could not do and why.
