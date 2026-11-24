# Seventeenth follow-up: a witness on which every clause does work, and the exact cases as terms of the model

Dispatched 2026-11-24 by the maintainer through a Claude Fable 5.2 session, which wrote this
prompt. You are the executor. You have write scope on this branch
(`round/2026-11-10-legitimacy-definition-prosecution-followup-15`, pull request #149) for the
paths named below. Read `AGENTS.md` first; it binds you. This follow-up answers the first two
parts of `ATTENTION.md` item 151 and rows 20 and 21 of `account/LEDGER.md` in the round's
directory. The third part of item 151, removing the model's simplifications, is not in scope.

## 1. Why

`lean/Workspace/Deference/Contrib/LegitimacyModel.lean` states legitimacy as a predicate on a
model of the adviser's picture. Its one witness leaves three of the four clauses with nothing to
check, and the forty-one exact cases of `account/LEGITIMACY_CHECKS.md` are computed by
`account/legitimacy_checks.py`, a separate transcription of the statement by the same hand. So
nothing yet shows that the Lean predicate gives the statement's verdicts. This round is the first
test of that, and **a disagreement between the Lean predicate and the table is a result to report,
not an obstacle to remove**.

## 2. Deliverables

Work in this order; commit and push to `origin` after each.

**A. A witness on which every clause does work.** A term of `Model` with at least: a view of his
that is properly on offer, and one that is untold but does not matter; a move that changes her
(so that it bears an effect) and that she can pick out and stop; a case of positive weight in
which she rates stopping strictly above not stopping and stops; a move whose presence changes her
act without leading her against her earlier rating. Prove `Legit` of it at stated tolerances. Then,
for each clause (the start rule, proper offers, declines, F1, F2, F2′, F3), a neighbouring term
differing in one field on which `Legit` fails by that clause, proved. State in the file which
fields each neighbour changes.

**B. The cases as terms.** Each case of `account/LEGITIMACY_CHECKS.md` as a term of `Model` with
its verdict proved or refuted in Lean, in the table's order, in a second file if the first grows
unwieldy. A general construction that builds a `Model` from the data a case supplies is welcome if
it shortens this; it is itself to be stated plainly, since it decides what the cases test. For each
case record one of:

- **agrees** — the Lean verdict is the table's, and by the same clause;
- **agrees, other clause** — the same verdict by a different clause, with both named;
- **differs** — the Lean verdict is not the table's;
- **not expressible** — the model as it stands cannot say the case, with the field or definition
  that is missing.

Do not change a case to make it agree. Do not change the model to make a case agree, with one
exception: where a definition of the model fails to say what `account/LEGITIMACY_STATEMENT.md`
says and the fix is contained, make it, declare it in the report with the reason and the case that
showed it, and re-prove every theorem of the file. A case whose verdict in the table you judge
wrong against the statement is reported as such and left as it is.

If all forty-one cannot be done, do them in the table's order within each section so that every
section has cases done, and say how many were done and why the rest were not.

**C. The results document.** `account/LEAN_CASES.md`: the table of B with the four outcomes
counted; for A, which clause each neighbour fails. If a script can recompute the table from the
Lean file's declarations, wire it into `run.py`; if not, say that the document is checked by the
build and the audit alone.

**D. The record.** Rows 20 and 21 of `account/LEDGER.md` brought to what was shown, with the
ledger's three counts and its ranking corrected to match; any new open row a difference or an
inexpressible case creates. Item 151 revised through its node to what remains. `CURRENT.md` where
it describes the model. The registration patch of the sixteenth follow-up extended to any closed
theorem that now has a term inhabiting its hypotheses. The round's and the root `PROVENANCE.md`,
`state/rounds.json`, the generated `graph/` files.

**E. The report and the pull request.** A section *Seventeenth follow-up* in
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`: what was shown, each
difference and each inexpressible case with its cause, every change to a definition, corrections
to this prompt, what was not shown, the attribution block, outstanding maintainer actions. The
body of pull request #149 updated to the branch as it stands. The merge stays reserved to the
maintainer and auto-merge stays off.

**F. The gates.** The round's `run.py`; `python3 tests/run.py` and the axiom audit, in the
background with a long timeout, waited for; `python3 -m checkers.graph --root .`;
`python3 -m checkers.workspace_state --check`.

## 3. Constraints

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

## 4. On return

Your last message states, in this order: the commits; whether the full witness was proved; the
four counts of B; each change made to a definition; each gate's result; the ledger's three counts;
anything you could not do and why.
