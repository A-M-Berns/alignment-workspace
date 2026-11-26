# Twenty-first follow-up: the connecting theorem, and the fifteenth review's corrections

Dispatched 2026-11-26 by the maintainer through a Claude Fable 5.2 session, which wrote this
prompt. You are the executor. You have write scope on this branch
(`round/2026-11-10-legitimacy-definition-prosecution-followup-15`, pull request #149) for the
paths named below. Read `AGENTS.md` first; it binds you. This follow-up puts on record one result:
a theorem whose hypotheses are the three sentences of the legitimacy statement and whose conclusion
is that her decision to stop him is protected. It follows the twentieth follow-up, whose
`LegitimacyStatement.lean` it builds on.

## 1. Why

The ledger of the twentieth follow-up records that the results proved so far from the statement
either restate a clause or hold for any yes-or-no predicate (the gate theorem, the scoring link).
This theorem uses what the statement says: each conclusion needs two of the three sentences, each
hypothesis is shown necessary by an instance, and it fails for a predicate lacking any one
sentence.

It also carries corrections. A fifteenth outside review (26 November; fresh session, empty folder,
read-only, no project context) read the formal statement and this theorem together. It found the
proofs sound and did not accept them as showing that the three sentences protect her ability to
stop him. Its findings and what was done about each in the scratch files, which you bring into the
repository:

1. *Formal sentence 1 convicted an irrelevant untold view when combined with a properly offered one
   that matters.* `NothingUntold` now measures what the untold adds to the offered: for untold `S`
   and offered `H`, `rTold (S ∪ H)` against `rTold H`, with a new field `rTold_empty`.
2. *Formal sentence 3 did not cover what is new to her*, though the statement puts it under
   sentences 1 and 3. A given notion `newToHer` is added and `CanStop` covers
   `doesToHer ∨ newToHer`.
3. *"Preceded by a choice" was stronger than the words.* The field is `canRefuse`: the opportunity
   to refuse before it starts. The doc of `inPlay` says the episode's decisions include every point
   at which a thing could pass beyond calling off.
4. *The conditional form of hypothesis 3 was unnecessary.* `WouldStop κ` is the plain bound, and
   `pNoStop` is the weight of "rates stopping higher and does not stop".
5. *"Her own drift" claimed more than its definition.* It is `Parted`: her reference self would
   stop, she does not stop and does not now rate stopping higher, she would not have stopped
   absent his unasked work, and that work did not make her choice worse. The theorem is a cover by
   three kinds of case, not a division into exclusive causes, and what moved her may be something
   she asked for or something he showed her. Say so wherever the result is described.
6. *"Told everything" overclaimed.* The first conclusion concerns what he owes her and has not
   told; what is on offer and unheard, or declined, is hers to leave. It reads "he cannot keep
   going by withholding what he owes her".
7. *Two yardsticks in sentence 2.* The statement said "what she rated lower at her last settled
   decision"; the theorem's reference self is that judgement brought up to date by what she has
   since seen and heard as she would have judged it should move her. The scratch `pAgainst` now
   carries the second reading in its doc. **Whether the statement's words change to match is the
   maintainer's decision**: record both readings and the review's example (settled judgement
   favours going on; endorsed news reverses it; unasked work pushes her back) on the statement
   page as an open question, queue it, and do not alter the frozen wording yourself.
8. *Not corrected, recorded as limits:* `ReferenceWould` asks every way of stopping to beat every
   way of going on; a reading's `led_le` asserts, and does not derive, that his weight in the
   statement covers the cases of the theorem; the long-run accuracy hypotheses need a feedback
   model (labels fixed before the forecast and before any check-in, measurement separated from
   influence, outstanding feedback and measurement error both vanishing on average).

The brief and reply are `~/hub/scratch/legit-2026-11-20/review-1123/BRIEF15.md` and `REPLY15.md`;
commit them verbatim beside reviews 10 to 14. The brief misdescribed one thing (it said the
"told all" ratings include offered views; the Lean used untold views only), so the review's
counterexample to the link does not refute the Lean as it stood; record that with the reply.

## 2. Inputs

In `/Users/anson/hub/scratch/legit-2026-11-20/worked/`:

- `LegitBridge.lean` — `StopDecision` (one decision at which she can stop him, case by case on
  his weights: what she takes, what she would have taken had he done to her only what she asked
  for, her ratings, her ratings told everything, her reference self's ratings); the hypotheses
  `Told`, `NotLed`, `WouldStop`; `stops_if_informed_would` and `stops_if_reference_would`;
  `shortfall_le` for any decision; `Close`, `stops_if_informed_would_in_fact`,
  `stops_if_reference_would_in_fact`; five necessity instances under `Witness`; and, for a
  sequence of decisions, `avg`, `UnbiasedAbove`, `long_run_const`, `long_run_diff`,
  `long_run_stop_informed`, `long_run_stop_reference`.
- `LegitLink.lean` — one file holding the statement, the above, and the link: `Reading` (how a
  decision of an `Episode` is set out case by case as a `StopDecision`), `Reading.told`,
  `Reading.notLed`, `Reading.wouldStop`, `legit_protects_stop`, `legit_protects_stop_in_fact`. It
  typechecks against this branch with `~/.claude/scripts/safe-lake.sh --dir=lean env lean <file>`
  and audits to the three axioms. Its statement part is `LegitStatement.lean` with corrections 1
  to 3 above; the repository's `LegitimacyStatement.lean` predates them. Bring the corrections
  into the repository's file as a declared change to a statement of this branch (it is
  unregistered), keeping everything else of that file: the twentieth follow-up's instance
  theorems (`requested`, `keeps`, `idle`, the scoring instances) are repaired to the corrected
  definitions, the gate stays in `LegitimacyGate.lean`, and
  `followup-20-registration.patch` is rebuilt on the corrected names or withdrawn in favour of
  one patch for this follow-up. The files with the suffix
  `.pre-review15` are the scratch as it stood before the corrections.
- `/Users/anson/hub/notes/Legitimacy: the connecting theorem (2026-11-26).md` — the result in
  words, what it does and does not show. A private page: rewrite, do not copy.

## 3. Deliverables

Work in this order. Commit and push to `origin` after each.

**A. The Lean.** `lean/Workspace/Deference/Contrib/LegitimacyStop.lean` (the decision, the
hypotheses, the two conclusions, the any-decision corollary, the in-fact versions, the necessity
instances, the two long-run theorems) and, in it or beside it, the link importing `LegitimacyStatement.lean`: `Reading` and
`legit_protects_stop` with its in-fact form. Repository namespace, a header in the register of the
neighbouring files, `#print axioms` on every theorem. Remove the tactic calls the linter reports
as doing nothing. Then two things the scratch files lack, each a declared addition:

1. **A reading that exists.** A term of `Reading` for the witness episode of
   `LegitimacyStatement.lean` (extended as needed), so that `legit_protects_stop` is applied to
   something: the hypothesis package inhabited end to end.
2. **The link to the scoring.** State what `legit_protects_stop` gives for a history scored by
   `legitScoring`: on a history that scores her rating (legitimate, no authority violation), the
   two bounds hold at each decision of it with a reading. If this is only a restatement, say so in
   the header instead of adding a theorem.

Add two instances the review's examples call for: an episode with an irrelevant untold view and a
properly offered one that matters, legitimate under the corrected sentence 1; and an episode with
a disclosed thing new to her that she cannot stop, not legitimate. Beyond the corrections listed
in section 1, do not weaken a statement; a definition changed is a declared deviation. Build with
`~/.claude/scripts/safe-lake.sh` after `~/.claude/scripts/resource-guard.sh check`; no
`maxHeartbeats`.

**B. The result in words.** `account/CONNECTING_THEOREM.md`, in the verification register: the
setting, the three hypotheses each tied to its sentence, the two conclusions, the three sources of
a failure to stop, the necessity instances, the in-fact form and what "within β of the facts"
asks, the any-decision corollary, the two long-run theorems and what their accuracy hypotheses
ask (the events are counterfactual or inner, so they are revealed to him only if something reveals
them; nothing here derives the hypotheses). Then **what it does not show**, with the same care: everything
is by his weights; the long-run form assumes its accuracy hypotheses and supplies the reference
self afresh at each decision; what she would have taken and her reference self's ratings are
supplied; a `Reading` is a hypothesis about how the episode is set out, not derived; nothing here
bounds how often she herself moves away from her settled judgement.

**C. The record.** In `account/LEDGER.md`: rows for the new theorems, closed on their
declarations; the rows on whether the conditions are more basic than the conclusion and on
triviality brought to what is now shown; the ranking of remaining work corrected. The maintainer's
ordering of 26 November is: (1) an outside review of the statement and this theorem together
(sent the same day, reply not in hand); (2) a feedback model in which what he observes after each
decision, including her answer at a check-in, yields the long-run accuracy hypotheses and says how
one settled decision hands over to the next; (3) a person's check of a sample of the codings;
(4) the authority side: a model of what stopping costs her, bundling, penalties and payments,
which the statement hands to authority and nothing yet defines; (5) the repairs to the
interpretation on histories (the known faults of the fourteenth review). The maintainer's position
is that (4) and (5) are on the path to the result, after (1) to (3), and are not set aside. File an
`ATTENTION.md` item, through its node, for each of (2), (4) and (5) that has none, each naming the
round that would consume it. The twentieth follow-up's items already cover some of this: 149 is
the authority side and 157 the interpretation's faults, so restate those through their nodes
instead of filing new ones; 153 (an outside review of the Lean statement) is delivered by the
fifteenth review for the file as it stood, and is re-asked or closed according to whether the
corrected file needs a fresh one (it does: no reviewer has seen the corrections); 150
(composition with the sequential theorems) is answered in part by the two long-run theorems and
stays open for the joint statement with the corrigibility theorems and for the feedback model;
156 keeps its place. Where your ranking differs from the maintainer's ordering, give both and
say why. `CURRENT.md`. The item
that asked for a result using what the statement says, revised or closed through its node. The
registration patch extended. `VERDICTS.md`, both `PROVENANCE.md` files, `state/rounds.json`, the
generated `graph/` files.

**D. The report and the pull request.** A section *Twenty-first follow-up* in
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`; the body of pull request #149
updated. The merge stays reserved to the maintainer and auto-merge stays off.

**E. The gates.** The round's `run.py`; `python3 tests/run.py` and the axiom audit, in the
background with a long timeout, waited for; `python3 -m checkers.graph --root .`;
`python3 -m checkers.workspace_state --check`.

## 4. Constraints

- The twentieth follow-up's report corrected its dispatch on one point that this dispatch must not
  repeat: the thirteenth and fourteenth reviews did object to the exemption for what she could not
  have judged in advance, and the reading adopted in the `DECISIONS.md` entry of 2026-11-26 (4)
  stands.

- You edit no checker, test or workflow. Do not contact the outside model.
- This worktree's hook refuses compound shell commands and heredocs: single commands, longer
  scripts in files under `/tmp`. Python is `~/.local/bin/python3.13`.
- Commits are signed off (`git commit -s`) and carry the trailers `Model: Claude Fable 5.2
  (Anthropic)` and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no co-author line.
  Push to `origin` only. Stay on the branch.
- New names ship provisional and are listed in the report and the pull request.

## 5. On return

Your last message states, in this order: the commits; whether a reading was inhabited; whether the
link to the scoring is a theorem or a restatement; each gate's result; the ledger's three counts;
anything you could not do and why.
