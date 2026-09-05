# Report — author consolidation, 2026-09-05

A maintainer-dispatched consolidation pass with write scope. Not a research round: no
theorem added, no claim registered, no epistemic class moved. The prompt is
`PROMPT.md` beside this file, verbatim.

## 1. Merges

| pull request | branch | landed as | method |
|---|---|---|---|
| Defeat Principle landing, Horty check, standing repair | `round/2026-09-03-defeat-landing-horty-standing` | `f7489cf5a610927b9e85e33d5d42228cd64da7de` | squash, Model attribution carried |
| Normative Inductor realization | `round/2026-09-04-normative-inductor-realization` | `caa3ad083e2d6d8120fbb54120219e907502ad28` | rebased onto `f7489cf`, retargeted from the stacked base to `main`, squash |

Both branches were already rebased onto the squash of the unified-grounds round
(`198a86a`) when the pass began; neither rebase produced a conflict. GitHub classifies
the pair as a stack and refuses its ordinary merge endpoints for them; both merges went
through the asynchronous merge endpoint. All seven required checks were green on each
head before merging, and the Python runner, the two Lean modules and the axiom audit
were also run locally.

## 2. Corrections made before merging

**Defeat-landing round.** The Pollock 1987 URL the round recorded as dead on
2026-09-03 redirects, as of 2026-09-05, to a host that serves the paper; the PDF was
fetched and its first page checked against the bibliographic data. `PRIOR_ART.md`
carries the resolving address and the DOI and keeps the caution that Horty credits the
distinction to Pollock 1970. The round's `REPORT.md` and `HORTY.md` are annotated with
that fact and with the landing of its dependency; outstanding actions 1 and 3 are closed.
The round's findings and verdict are unchanged.

**Normative Inductor round.** One substantive addition, requested by the dispatch and
absent from the head: joint price-space feasibility does not imply joint
practical-response compatibility. One service occurrence realizes one decision
distribution, so every exposure matched to it needs its own anchored response
certificate against that same distribution; incompatible demands are separated into
distinct service contexts, adjudicated under a licensed upstream rule, given a common
adequate response, or left as residual mass. Recorded as a realization obligation in the
realization document (admissible-edge row, a new §6 subsection, a spine row, and the
remaining-work list), the presentation note, `THEOREMS.md`'s *what is not shown*, and
`REPORT.md`. The abstract admissible-edge relation already admits an edge only when its
certificate exists, so no abstract-contract change was made. The `exact_carry_left`
docstring now states that it consumes an already certified identity edge and does not
establish the semantic premise. `PROVENANCE.md` names the governing contract files
without a local filesystem path. The pull-request body was rewritten to match the head:
stack metadata removed, evidence classes stated once, the "author must decide" list
reduced to the one genuine decision.

## 3. The wiki

Five new pages: `Settlement-Interface`, `Integrity`,
`Openness-Coverage-and-Non-Capture`, `Normative-Induction`, `Normative-Inductor`. Two
rewritten: `Legitimacy`, `Diachronic-Answerability`. Fourteen amended: `Home`,
`_Sidebar`, `Roadmap`, `Glossary`, `Progress`, `Normativity`,
`Actionability-and-Normative-Force`, `Why-Normativity`, `Prior-Art`, `Architecture`,
`Deference`, `Corrigibility`, `Normative-Record-and-Inquiry`, and the state-bound views
regenerated. The architecture the wiki now presents, and the superseded prose it
replaced, are itemized in the `DECISIONS.md` entry of this date.

## 4. Deviations (standard 8)

1. **Merge method.** The dispatch said to use the repository's normal method. The
   normal method — squash through the ordinary merge endpoint — was refused by GitHub
   for both pull requests because it classifies them as a stack; the asynchronous
   endpoint was used with the same squash method and message.
2. **Pollock link.** The dispatch asked for broken links to be fixed. The link was not
   broken on the day of the pass; it had been recorded as dead two days earlier. The
   record was corrected rather than the link replaced, and the round's own statement
   that it did not resolve during that round was left standing as history.
3. **A defect of this pass, found and fixed after the wiki merge.** To reuse another
   checkout's Lean build cache the pass planted a symlink at `lean/.lake`; the ignore
   rule matched directories only, so the symlink was staged with everything else and
   reached `main` in the Normative Inductor squash. Removed, with the ignore rule
   widened, in the follow-up commit recorded in `DECISIONS.md` under this date.
4. **Prompts record.** The dispatch did not ask for a round directory. One is committed
   because standard 12 requires the prompt verbatim, and the round record and provenance
   rows follow from the gates that check them.

## 5. What this does not establish (standard 9)

- Nothing here is a registered claim, and no evidence class changed. The wiki labels
  every legitimacy page open / unregistered.
- The Normative Inductor's end-to-end theorem remains conditional; the wiki says so and
  lists its hypotheses by owner through a pinned link.
- The Defeat Principle's licensing content — which rules of a practice license contesting
  which debts — is not supplied; the three maintainer reservations from the defeat rounds
  (load discount, settlement independence, protected participant) remain in the queue.
- The wiki's conceptual decomposition is a sanctioned shape, not a predicate, exactly as
  the 2026-09-01 ruling distinguished.

## 6. Outstanding maintainer actions (standard 10)

1. **Whether to adopt the bounded-domain coercive-modulus repair in the abstract
   contract** before freezing it. The contract lives outside the repository; every
   in-repo summary already uses the repaired form.
2. **The three defeat-round reservations** already in `DECISIONS.md`'s queue.
3. **Whether item 77's prior-art deliverable is discharged** on the 2006 paper, or the
   2012 book is to be obtained.

## Attribution

- Prompt author: the maintainer, outside this repository.
- Executor: Claude Fable 5.1 (Anthropic).
- Dates: 2026-09-05.
