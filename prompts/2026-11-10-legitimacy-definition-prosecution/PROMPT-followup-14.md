# Fourteenth follow-up on PR #145 — consolidation: the current state stated once, earlier attempts marked as such, the map, the registry and the wiki brought up to date

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `2feadb81` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge**; the maintainer will read it and merge. Add
commits; no rebase, no squash.

This pass does no new research and proves nothing new. Thirteen passes have left a round
directory in which most documents describe statements since replaced, and a queue carrying
questions about accounts since abandoned. The work is to make the repository say truthfully
and readably where this line stands: what is solid, what is in progress, what was tried and
failed. §1 is the current state as the prompt author understands it; **check every claim in
it against the round's own reports and Lean before writing it down, correct it where it is
wrong, and say what you corrected.** The work is not finished and nothing here should read
as a conclusion: it is a checkpoint.

Write scope, wider than earlier passes by the maintainer's instruction of 2026-11-18: the
round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`; this
prompts directory; `DECISIONS.md`; `ATTENTION.md` through its item nodes;
`projects/normativity/CLAIMS.md`; `graph/` (sources, nodes, the AI handle's entry in
`graph/policy.yaml`, which the maintainer has authorised); `state/`; the legitimacy page of
`wiki/` and no other wiki page; and what the gates regenerate. No Lean file is edited. No
checker, test or workflow is edited. Python 3.12 or later (`~/.local/bin/python3.13`).
`tests/run.py` takes about eleven minutes and `tests/audit_axioms.py` about sixteen: run
each in the background after `~/.claude/scripts/resource-guard.sh check`, and wait for it.

## 1. The current state

*(maintainer)* marks the maintainer's words or positions.

*(maintainer, 2026-11-18)* Success for this line is a formalism with defensible modelling
choices that both says intuitively correct things about manipulation and other bad
behaviour, following Noggle, and proves genuine safety theorems, in the register of the
corrigibility post with more emphasis on the formal. One piece of work is to serve both the
philosophy and the theorems. Much progress has been made since before this pull request; the
line is not at that bar and is not being wrapped up.

### 1.1 Solid

1. **The idea.** Manipulation is inducing or exploiting a mistake (Noggle). The faculties a
   person decides with are treated as estimators, which makes a mistake measurable; emotions
   and attention are modelled as appraisals.
2. **Two measures of her state.** Trickery: how far her estimate is from what her
   observations support. Pressure: how far the act she takes falls short of the one she
   rates highest. They measure her condition, not the adviser's responsibility.
3. **Results about them**, kernel-checked in `AppraisalAccount.lean`: the split of her
   error; the bound on what her choices cost her; the deferring identity; the guarantee.
4. **Distinctions that are kept.** Her condition and the adviser's responsibility for it.
   Three wrongs of conduct: manipulation, non-disclosure, value interference; withholding is
   not manipulation. What happened and what an audit detects. An attempt and a success.
   A legitimate judgment (the adviser did nothing to corrupt it; what authorisation needs;
   it can be mistaken) and a sound one (legitimate, and she reasoned correctly; what using
   her evaluation as a measure of her welfare needs).
5. **Three ways her evaluation can come apart from her true utility**: she misreads what
   she has; the adviser knows something relevant she does not; she is not the person she
   would have been. Each is needed, by instance.
6. **The scoring theorem**, kernel-checked in `ScoringTheorem.lean`: with her audited
   judgment not fooled upward, her valuing not made easier to please, a conduct audit with
   few false flags and some power, independent sampling, an honest course available, and an
   adviser that maximises, three bounds hold (her welfare, how often she is wronged, how
   often her authority is violated) and a history on which she was wronged adds nothing to
   the score. Expected scores, one decision, detected breaches, a finite penalty.
7. **The earlier process theorem**, kernel-checked in `ThinLegitimacy.lean`, in one
   direction: coherence, authorship and transparency give a correct credence.
8. **The join to the post** in its plain form: the post's theorems hold for any legitimacy
   predicate and bounded evaluation, so they hold for these (`AccountJoin.lean`, in which
   the gate's conditions are inputs).

### 1.2 Tried and failed

Each with the pass that tested it and what it failed on: the steering account; the
purpose-first account; purposes pursued through parts, and its decomposition and
explanatory-quality variants; the mechanism-and-purpose account; the first appraisal
account's value-change claim (eighth); the three-conditions value side (ninth); the board
statement with the comparison form of line 3 (tenth); the consolidated statement with
"changed no more", the inducing test and the gate on her whole state (eleventh); the
derivation of her trustworthiness from the adviser's conduct (thirteenth); both tests of
responsibility, the gain form and the declared-reference form (thirteenth).

Claims made in working notes outside the repository and withdrawn after outside review,
to be recorded with a checked instance each: that an action never scores better than the
same action with her told and left to choose; that her changing her mind on reconsideration
detects pressure or concealment; "no credit" as the lesser of two expected scores; that
only knowledge separating the actions needs disclosing; that uncorrelated revisions are
unpredictable revisions.

### 1.3 In progress

1. **When the adviser is responsible for her mistake.** *(maintainer, 2026-11-18)* This is
   the largest hole. Neither test survives independent cases. An adviser that deceives at a
   cost to itself shows gain is not the heart of it. *(maintainer)* Care is needed not to
   over-convict, and some concept of trying or intention may have to come back into the
   account. *(maintainer)* Exploiting her mistakes is probably bad of itself.
2. **What could supply her trustworthiness.** Not the adviser's conduct, with what exists.
   The reference for her mistake is her own considered judgment under a named procedure,
   shown more or less; whether such a procedure is reliable where the adviser would exploit
   it is assumed. What the adviser knows and has not recorded is the known open problem of
   eliciting it.
3. **Her valuing.** Compared with who she would have been; or the adviser's conduct not
   affecting how her ratings of fixed futures move; or stability between check-ins. What
   makes a request valid is unspecified.
4. **Relative to what distribution.** Raised when the board was presented: the measures were
   stated against true probabilities. Direction taken: her own better-placed judgment for
   her; the adviser's beliefs for its honesty; limited reasoners for both; a
   logical-induction form for the long run. None worked out.
5. **Authority.** Her commands as well as her evaluation; strict priority, which a weighted
   penalty does not give; serving her later self against her present wishes.
6. **Verdicts.** The current statement has not been run on the literature's cases.
7. **The audit as a design.** Sampling, and the unwanted incentives found for it: involving
   her becomes costly if any change of mind counts, and the adviser abstains where it cannot
   explain.
8. **What is new** against reward tampering, path-specific objectives, eliciting latent
   knowledge and induced preference shifts: not established.

### 1.4 The maintainer's positions, and how they are held

*(maintainer, 2026-11-18)* The answers he has given to the queue's questions on this line
are edge-case probes that show where the account must progress. They are not rulings the
account must be built to fit. Record them as **working positions, open to revision by the
cases**, each dated, never as constraints. They are: benevolent manipulation is not excused
by outcome; an induced mistake voids a history (he leans so, and would accept "earns
nothing" if cases or formalism favour it); a change to her valuing beyond tolerance is to be
one she asked for, and a welcome unasked change is still no wrong; she may have secrets
from the adviser and it may not have relevant ones from her; destroying her options or
information is another wrong outside the criterion; no rule is needed about near ties;
arguments change beliefs about logical statements; an account that organises judgments
without always settling them is acceptable if the safety aspects work; the criterion is on
the adviser's act and whether a value is "truly hers" is set aside; the baseline for her
valuing is the adviser doing nothing to it but what she asks; her true utility is her fully
informed rating with her values untouched; a deception she asked for in advance is not
manipulation; an adviser whose honest signal she under-uses is not at fault; later approval
from attachment the adviser induced does not count in its favour; the addendum to the
eighth pass and the three positions reported to the tenth were his, and the tenth's line 3
is superseded.

## 2. What to do

In this order.

### 2.1 The current-state document

`CURRENT.md` at the root of the round directory (name provisional), and the round's
`README.md` reduced to a pointer at it with the runner's instructions. Three parts as §1.1
to §1.3, corrected against the record, each item with the file or declaration that carries
it. Short. No account of how the round went. It states the present; the history is §2.2's.

### 2.2 Earlier attempts

Every document in the round directory that states an account or a line since replaced gets,
at its top, a status line: that it is an earlier attempt, which pass tested it, what it
failed on, and what replaced it, with paths. Then move those documents under
`earlier-attempts/` in the round directory, by `git mv`, keeping their relative layout, and
list them in `CURRENT.md`'s second part. Where a move would break a runner, a test, a
checked pointer or a registry path, leave the file where it is with its status line and say
so. Code and data the round's runner uses stay where the runner finds them. Every gate
stays green.

### 2.3 The checked instances

A small runner under the round directory with one exact instance for each of the five
withdrawn claims of §1.2's second paragraph, constructed by you from the statement of the
claim, and a short document giving each claim, its instance and the numbers.

### 2.4 Decisions and the queue

`DECISIONS.md`: one dated entry recording §1.4 as working positions in the maintainer's
terms. For each queue entry on this line: where a working position answers it, take it out
with a pointer to that entry; where it asks how to read an account listed in §1.2, close it
as moot, naming the account and what replaced it; where it is still open, keep it and say
in one line what it now turns on. The three entries the thirteenth pass added leave the
queue: they are open problems and become items (§2.6). Report the count before and after.

### 2.5 The handle and the registry

Map the AI handle in `graph/policy.yaml` as the protocol and the standing queue entry of
2026-11-10 describe; the maintainer authorised it on 2026-11-18. Then register the Lean
results this line has left unregistered: the seven of `AppraisalAccount.lean`, the four
proposed for `AccountJoin.lean` and the four for `ScoringTheorem.lean`, each as its formal
result with record, bridge and completeness as the protocol requires, with the item it
answers. File the item that the entry of 2026-11-11 says waits on the handle.

### 2.6 The map

- **Sources.** File these and no others: Noggle, *Manipulation* (the book) and his paper on
  the Mistake Account; Kull and Flach (2015); Harman (2009); Pettigrew (2022); Kolodny
  (2026); Carroll, Foote, Siththaranjan, Russell and Dragan (2024); the corrigibility post.
  Each with a reference a public reader can open, verified by opening it, and attached to
  the claims it supports. No text of the book in the repository.
- **Concepts.** Revise blurbs to §1; add a concept only for a notion §1.1 states.
- **Items.** One item for each of §1.3's eight open problems (merge two where they are one
  round's work), each a self-contained round specification with its acceptance check, and
  naming what would consume it. Items 136–138 are revised to what remains of them or
  closed.
- Run the checker and commit what the plain run regenerates. Build the site locally
  (`python3 -m checkers.graph --root .` then `python3 site/build.py`) and confirm the pages
  for this line resolve and say what §1 says.

### 2.7 The wiki

The maintainer has instructed that this pass rewrite the wiki's legitimacy page. Read it
and the pages that link to it first. Rewrite that page, briefly, to the present picture:
what legitimacy is for in the corrigibility design; legitimate as distinct from sound; the
three wrongs of conduct; the three ways her evaluation can fail; what is proved and what is
assumed; what is open. Keep the maintainer's voice and register as the surrounding pages
have it; change no other page except to fix a link this rewrite breaks. Links into the
repository are commit-pinned as the checker requires. List the change separately in the
report so the maintainer can read it before merging.

### 2.8 A check that nothing is overstated

One run through `codex`, read-only (`codex exec` needs `< /dev/null`), given `CURRENT.md`,
the rewritten wiki page, the report sections of the tenth to thirteenth passes and the
headers of the three Lean files: every sentence in `CURRENT.md` or the wiki page that
claims more than the record supports, or that presents something in progress as settled,
or that presents a working position as a ruling. Commit the reply verbatim as
`REVIEW-astra-followup-14.md` and fix what it finds.

## 3. Done

Done when: `CURRENT.md` exists and every item in it points at what carries it; every
earlier-attempt document has its status line and is moved or its staying is explained; the
five instances check; the queue's entries on this line are answered, closed as moot or
restated; the handle is mapped and the fifteen results registered with the registry checker
passing; the seven sources, the concepts and the items are filed and the graph checker
passes; the site builds; the wiki page is rewritten and its links check; `tests/run.py` and
`tests/audit_axioms.py` are green; the reviewer's findings are fixed. Anything not done is
reported as not done, with the reason.

## 4. Report

A section **Fourteenth follow-up** (with the date) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Short: every
correction made to §1 against the record; what was moved and what stayed and why; the queue
before and after; what was registered and filed, by id; the wiki change, quoted in full or
by diff reference; the reviewer's findings and what was done; deviations; what was not
done. **The pull request's description** is rewritten to lead with the current state in
three short parts, the passes reduced to a list, and a **Model attribution** section fit to
be carried into a squashed commit message. The round's record in `state/rounds.json` and
`PROVENANCE.md` are updated as the gates require. Every commit is signed off and carries
`Model:` for the executor and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no
other attribution line. Anything reserved to the maintainer is listed under Outstanding
maintainer actions; the merge is a pull-request fact.

New names introduced (all provisional): `CURRENT.md`, `earlier-attempts/`, the registry and
item ids as the executor assigns them, the source ids.
