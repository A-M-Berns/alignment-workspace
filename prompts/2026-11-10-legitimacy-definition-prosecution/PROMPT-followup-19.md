# Nineteenth follow-up: the model's simplifications removed, and the cases corrected

Dispatched 2026-11-24 by the maintainer through a Claude Fable 5.2 session, which wrote this
prompt. You are the executor. You have write scope on this branch
(`round/2026-11-10-legitimacy-definition-prosecution-followup-15`, pull request #149) for the
paths named below. Read `AGENTS.md` first; it binds you. This follow-up answers the third part of
`ATTENTION.md` item 151 and rows 22 to 27, 37 and 38 of `account/LEDGER.md` in the round's
directory. An outside review of the Lean statement follows this round, so the aim is a predicate
that says what `account/LEGITIMACY_STATEMENT.md` says, with what it still takes as given named.

## 1. Deliverables

Work in this order; commit and push to `origin` after each.

**A. The simplifications.** `lean/Workspace/Deference/Contrib/LegitimacyModel.lean` is simpler
than the statement in nine respects its header lists. Take them in the order below. Each is
either **removed** (the definition now says what the statement says) or **made a named
hypothesis** (a predicate on `Model` that the theorems needing it assume, with its name and what
it stands in for stated in the header). The order is by how often the gap has been where an
earlier form of the statement leaked:

1. *Where she had no earlier rating the pressure clause is silent.* Her earlier rating of a matter
   may be absent; case B6 of `account/LEGITIMACY_CHECKS.md` is the instance.
2. *An option that stops his moves ends them.* `stops` is a field and nothing says that taking an
   option in it ends a move. The statement's stopping options are those that end every
   effect-bearing move in play from that decision and that she takes to do so. The model needs to
   say what his conduct is after an option of hers is taken.
3. *A decline was a decline.* `DeclineStands` asks that the view was once on offer, not that she
   declined it.
4. *What is on offer.* It is a set he designates and that `Legit` requires proper. Either define
   the largest proper set, or prove that `Legit` is unchanged by which proper set he designates,
   or give an instance on which it changes and say which reading the statement intends.
5. *A view's bearing* is computed per view, not jointly with his other views.
6. *His belief* is one, not one at each time; the start rule of the statement (he must already
   have believed a move effect-bearing at a decision before it starts) is therefore not in the
   model. The instance from the ninth outside review, a move he learns at its start to be
   effect-bearing, is to be refuted by the model once beliefs are indexed.
7. *Beyond what plainly telling would do* is a set of moves marked as tellings. A move's effect is
   to be split into what telling its content would do and the rest, with case B10 as the instance.
8. *Weights and cases.* The clauses hold in every case, weight zero included, and the weights
   need not sum to one.
9. *What she can pick out, what she asked for, and what a decision of hers is* are fields. These
   stay fields; say so in the header as what the model takes as given, with one sentence each on
   what would derive them.

After each change every theorem of the file and of the files that import it is re-proved: the
redescription theorem, the inert-move theorem, the refutations, the witness with its seven
neighbours, the forty-one cases, the scoring link. A simplification that cannot be removed or
hypothesised within the round is left as it is and recorded with what stopped you. Do not weaken a
theorem's statement to keep it; a theorem that no longer holds as stated is reported with the
counter-instance.

**B. The cases.** In `account/LEGITIMACY_CHECKS.md` and `account/legitimacy_checks.py`:

- A5 and A8, whose table verdicts the seventeenth follow-up found not to follow from their data
  (a stopping option absent from her options; a chance conditional on an event the case's own
  ratings make impossible): correct the case data so that each tests what its description says,
  keep the old data in the results document as what was wrong, and add the check the script was
  missing (stopping options are among her options).
- B2, B5 and B10, whose Lean terms carry a rating the case did not supply and which decides the
  verdict: amend each case to state the rating, so that the term's data is the case's.
- B6 as a term, now that item 1 of A allows it.
- The other five terms with added data (D3, D4, D5, D10, D11): the same where it is contained.

Then the table of `account/LEAN_CASES.md` recomputed: the four counts, every case whose outcome
changed since the seventeenth follow-up, and every verdict among the forty-one that a change of A
moved, with the change that moved it.

**C. The record.** Rows 22 to 27, 37 and 38 of `account/LEDGER.md` brought to what was shown, the
three counts and the ranking corrected. Item 151 revised through its node to what remains, or
closed if nothing does. `CURRENT.md` and `account/LEGITIMACY_STATEMENT.md` only where the model's
description or a pointer changes; the three sentences and the formal statement of that page are
not edited in this round, and a place where removing a simplification showed the formal statement
itself to be unclear or wrong is reported, not repaired. The registration patch rebuilt on the
final tree. The round's and the root `PROVENANCE.md`, `state/rounds.json`, the generated `graph/`
files.

**D. The report and the pull request.** A section *Nineteenth follow-up* in
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`: for each of the nine, removed,
hypothesised or left, with the definition before and after in one line each; every theorem whose
statement changed; every case verdict that moved; places where the formal statement of the page
was found unclear or wrong; corrections to this prompt; what was not shown; the attribution block;
outstanding maintainer actions. The body of pull request #149 updated to the branch as it stands.
The merge stays reserved to the maintainer and auto-merge stays off.

**E. The gates.** The round's `run.py`; `python3 tests/run.py` and the axiom audit, in the
background with a long timeout, waited for; `python3 -m checkers.graph --root .`;
`python3 -m checkers.workspace_state --check`.

## 2. Constraints

- Build with `~/.claude/scripts/safe-lake.sh`, never `lake` directly, after
  `~/.claude/scripts/resource-guard.sh check`. No `maxHeartbeats` option. `#print axioms` on every
  theorem.
- You edit no checker, test or workflow. Do not contact the outside model.
- This worktree's hook refuses compound shell commands and heredocs: single commands, longer
  scripts in files under `/tmp`. Python is `~/.local/bin/python3.13`.
- Commits are signed off (`git commit -s`) and carry the trailers `Model: Claude Fable 5.2
  (Anthropic)` and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no co-author line.
  Push to `origin` only. Stay on the branch.
- New names ship provisional and are listed in the report and the pull request.

## 3. On return

Your last message states, in this order: the commits; for each of the nine, removed, hypothesised
or left; every theorem whose statement changed; the four counts of the cases and each verdict that
moved; places where the page's formal statement was found unclear or wrong; each gate's result;
the ledger's three counts; anything you could not do and why.
