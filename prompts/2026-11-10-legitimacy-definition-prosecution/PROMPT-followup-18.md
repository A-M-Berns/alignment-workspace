# Eighteenth follow-up: a second coding of the bank

Dispatched 2026-11-24 by the maintainer through a Claude Fable 5.2 session, which wrote this
prompt. You are the executor. You have write scope on this branch
(`round/2026-11-10-legitimacy-definition-prosecution-followup-15`, pull request #149) for the
paths named below. Read `AGENTS.md` first; it binds you. This follow-up answers the first half of
`ATTENTION.md` item 154 and bears on rows 3, 7 and 35 of `account/LEDGER.md` in the round's
directory. The second half of item 154, a set of cases of bent judgement, is not in scope.

## 1. Why

The disclosure rule (214 of 219 settled bank cases) and the clause on her earlier rating (33 of
33, one control convicted) each rest on one coding of the bank by one language model. This round
codes each sheet a second time, by a different reader, and counts.

## 2. Inputs

The paraphrases the coders read are outside the repository and stay there:
`/Users/anson/hub/scratch/legit-2026-11-20/noggle-bank/two-est/blind5_A.json`, `blind5_B.json`,
`blind5_C.json`, each a list of `{id, case}`. Sheet 11 was coded on all of them. Sheet 16 was
coded on the 152 cases whose ids are in `account/bank_coded_16.json`. The sheets are
`account/BANK_CODING_11.md` and `account/BANK_CODING_16.md`; the scorers are in
`account/case_runs.py`.

## 3. Deliverables

Work in this order; commit and push to `origin` after each.

**A. What is fixed first.** Before any second coding exists, commit `account/SECOND_CODING.md`
stating: the measures (for each field of each sheet, the number of cases on which the two codings
give the same answer; for each sheet, the number on which the rule's verdict is the same, counting
"unsettled" as a verdict; the second coding's own counts against the author's verdicts, by the
unchanged scorer); and predictions for each as numbers, with your reasons in a sentence each.
The scorers are not changed in this round.

**B. The second coding.** Each sheet coded once more by a subagent that is given a folder outside
the repository holding only the sheet and the cases in a fresh random order, is told to read
nothing else and to use no web, and is a **different model from the first coder's family member
where the harness offers one** (record exactly which model coded; if only the same model is
available, say so and proceed). The subagent is waited for in the foreground. The coding enters
the repository as `account/bank_coded_11_second.json` and `account/bank_coded_16_second.json`,
keyed by case id, with categorical answers only and no case text.

**C. The counts.** The measures of A computed by a script wired into `run.py`, and a section of
`account/CASE_RUNS.md` the runner recomputes: each measure beside its prediction, the predictions
that failed named, and every case on which the rule's verdict differs between the two codings
listed by id with both codings' answers. Counts as counts, not rates of a population.

**D. The record.** Rows 3, 7 and 35 of `account/LEDGER.md` brought to what was shown, verdicts
changed only where standard 9 allows; the ledger's counts and ranking corrected to match. Item 154
revised through its node to what remains (the cases of bent judgement). `CURRENT.md` where it
states the evidence. The round's and the root `PROVENANCE.md`, `state/rounds.json`, the generated
`graph/` files.

**E. The report and the pull request.** A section *Eighteenth follow-up* in
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`: the counts, the failed
predictions, what the disagreements have in common if anything, corrections to this prompt, what
was not shown (both coders are language models; one second coding is not a rate of agreement
among readers), the attribution block, outstanding maintainer actions. The body of pull request
#149 updated to the branch as it stands. The merge stays reserved to the maintainer and auto-merge
stays off.

**F. The gates.** The round's `run.py`; `python3 tests/run.py` in the background with a long
timeout, waited for; `python3 -m checkers.graph --root .`;
`python3 -m checkers.workspace_state --check`. This round touches no Lean; say so.

## 4. Constraints

- No text of Noggle's book and no paraphrase of its cases enters the repository.
- You edit no checker, test or workflow. Do not contact the outside model.
- This worktree's hook refuses compound shell commands and heredocs: single commands, longer
  scripts in files under `/tmp`. Python is `~/.local/bin/python3.13`.
- Commits are signed off (`git commit -s`) and carry the trailers `Model: Claude Fable 5.2
  (Anthropic)` and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no co-author line.
  Push to `origin` only. Stay on the branch.
- New names ship provisional and are listed in the report and the pull request.

## 5. On return

Your last message states, in this order: the commits; which model did the second coding; for each
sheet the rule-verdict agreement and the second coding's counts against the author; which
predictions failed; each gate's result; the ledger's three counts; anything you could not do and
why.
