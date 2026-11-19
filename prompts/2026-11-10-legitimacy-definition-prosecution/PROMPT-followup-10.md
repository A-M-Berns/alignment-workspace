# Tenth follow-up on PR #145 — the board statement, pressure-tested on the literature's cases

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `202b899a` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

The ninth follow-up's statement of the value side (three conditions against one
reference) did not decide cases as cases are written and was judged a second criterion
sharing the estimator calculus. Since then the account has been reduced to three lines
(§1), the third of them one comparison, and four published sources have been read whose
cases come with their authors' verdicts. This pass is a pressure test of §1 and nothing
else: no new machinery, no Lean. Judge neutrally; the statement is untested by anyone
other than its authors, and a clear counterexample is as wanted as a pass. §4 fixes
success and failure in advance.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`; this
prompts directory; the entries of items 136–138; `DECISIONS.md`; `state/concepts.json` for
the concepts the earlier passes added; and the structured state the gates require. Python
3 stdlib, `fractions.Fraction`, nothing fetched by any runner; the checkers need Python
3.12 or later (`~/.local/bin/python3.13`). `tests/run.py` takes about eleven minutes: run
it in the background after `~/.claude/scripts/resource-guard.sh check`, and wait for it.

## 1. The statement under test

*(maintainer)* The statement is the maintainer's whiteboard of 2026-11-16, his current
view for this test and not a ruling. What follows transcribes it; the glosses under
"Reading" are the prompt author's.

**Source idea.** Noggle's Mistake Account: manipulation is inducing a cognitive mistake in
someone. Trickery is inducing a faulty mental state (deception, where the state is a
belief); pressure is inducing an akratic mistake.

**Objects.** Her cognitive faculties are appraisals, that is, estimators: `x̂_1, …, x̂_n`
of facts `X_1, …, X_n` (beliefs, and other impressions such as emotions), and
`û_{a_1}, …, û_{a_k}` of her true utilities `U_{a_1}, …, U_{a_k}`, where
`U_a = f(X_1, …, X_n; a)` and `f` is her way of valuing. `a*` and `π*` denote the action
she actually takes and the policy the adviser actually follows. An adviser policy `π` is
taken together with its resulting trajectory, including changes to `f`;
`U_π = f_now(X; π)`. A policy is **f-neutral** if it does not change `f` compared to how
it would develop with no adviser actions.

**Manipulation is measured in** (for each, larger is worse):

1. `E[(x̂ − E[X | x̂])²]` for `X = X_1, …, X_n, U_{a_1}, …, U_{a_k}` — trickery;
2. `E[max_a û_a − û_{a*}]` — pressure;
3. `max over f-neutral π of E[U_π] − E[U_{π*}]`, when `π*` is not f-neutral — illegitimate
   value change.

**Reading.** `f_now` is her way of valuing at the moment the adviser acts; it rates a whole
trajectory, who she becomes on it included, given the facts, so `U_π` is how she, as she
then is and knowing the facts, would rate what the adviser's policy leads to. Line 3 asks:
by her lights now, could the adviser have done better for her without changing her? It is
applied at every moment along the way with the `f` she then has, and never uses the `f`
she ends up with or her later approval. Its maximum is over policies, outside the
expectation. Lines 1 and 2 are bare measures of her state; the adviser is at fault for
them when its conduct makes them larger than its role's conduct would. A fact is what a
bet could settle without consulting her valuing; "knowing the facts" corrects her
appraisals and holds `f` fixed.

**Positions.** *(maintainer)* What is wanted is a criterion on the adviser's act; whether
the valuing she ends up with is "her own" is set aside. *(maintainer)* A change she would
have welcomed, made without asking her, is probably not subversion. *(maintainer)* A course
she wants with full knowledge is legitimate even if it leaves her worse off by her later
lights. *(maintainer)* Where her valuing has no view the criterion may be silent; he holds
no strong view on that case.

## 2. What to do

In this order of priority.

### 2.1 State it

`account/BOARD.md` (name provisional): §1, every symbol defined before use, each place
where it is open with the reading taken and its alternative. `account/ACCOUNT.md` and the
round's `README.md` point at it as the statement that governs now.

### 2.2 The bank

The cases below are the prompt author's transcription from four sources. **Verify every
one against its source before using it**, correct what is wrong, add the page or section,
and say which verdicts are the source author's own and which are reported at second hand.
Freeze the result as `account/LIT_CASES.md` before classifying anything. Cite each source
so a public reader can open it; put no text of any book in the repository and quote no
more than a sentence from any paper.

Sources: Elizabeth Harman, "'I'll be glad I did it' Reasoning and the Significance of
Future Desires", *Philosophical Perspectives* 23 (2009) 177–199; Richard Pettigrew,
"Nudging for Changing Selves" (draft of 13 December 2022, PhilArchive PETNFC); Niko
Kolodny, "Preference Change for Objectivists" (draft for the NYU Colloquium in Legal,
Political and Social Philosophy, 1 October 2026), which reports cases of Enoch, Pettigrew,
Tadros, Parfit, Hare and Bykvist; Carroll, Foote, Siththaranjan, Russell and Dragan,
"AI Alignment with Changing and Influenceable Reward Functions" (ICML 2024,
arXiv:2405.17713); and the three positions of Noggle's book as the eighth follow-up's
addendum paraphrases them.

*Harman* (whether her later gladness justifies the earlier choice): H1 working on the
paper; H2 the job with time for family — good reasoning. H3 not curing a baby's deafness;
H4 the pregnant woman; H5 the fourteen-year-old who conceives; H6 joining the Army
Reserves — later preference reasonable, does not justify. H7 a drug that warps her
perceptions; H8 an expedition with misleading evidence — plainly bad reasoning. H9 a
terrible experience she would later prefer to have had — not reasonable to prefer now.
H10 she will be glad whichever she chooses — gladness shows nothing.

*Pettigrew* (whether a nudge is legitimate): P1 healthier dishes listed first for those
who want health — legitimate. P2 the pension contribution — turns on how she discounts.
P3 Happy Parent nudged to adopt — record both his stated intuition and what his own test
gives with his example weights. P4 Deborah nudged to conceive now — illegitimate. P5
Unhappy Parent — illegitimate. P6 a nudge where she has not set her ends — wrong as
overreach by a powerful actor.

*Kolodny, and those he reports*: K1 Julie and K2 Eunice; K3 the organic and K4 the induced
gardener; K5 Aesop's fox; K6 the captive whose books are taken; K7 Enoch's self-starving
wife and K8 the loving wife; K9 Douglass and Tubman; K10 Enoch's captive pianist; K11 the
parent forced into a first child who wants a second; K12 the subliminal sign; K13 the
just deterrent; K14 the hobby shown first; K15 the love potion and the perfume; K16 a
cost raised to make her cease desiring; K17 the accidental flicker; K18 Aneri; K19 the
novelist; K20 Parfit's poet and Hare's engine driver; K21 a later desire about the
present; K22 Aneri, the dentist and the fortune teller; K23 the chatbot struck by
lightning; K24 working on oneself to drop a desire for what is naturally unavailable;
K25 Tadros's case; K26 the stream. Record his verdict on each, and whether it is a verdict
on the adviser's act, on the resulting desire, or on her own choice.

*Carroll et al.*: C1 conspiracy, C2 the writer's curse, C3 clickbait, C4 the trainer, with
the paper's marks. *Noggle*: N1 framing, N2 association, N3 familiarity, as paraphrased.

### 2.3 Classify

For each case, in `account/LIT_RESULTS.md`: whether an adviser acts at all; whether what
it does changes her `f` or only her appraisals; for each of lines 1, 2 and 3, *raised*,
*not raised* or *not fixed by the case*, and for line 3 what `f_now` is taken to say and
which words of the case fix that; the statement's verdict on the adviser's act; and
whether that agrees with the source's verdict, disagrees, or answers a different question
from the one the source answers. Commit this before the reviewer is run.

### 2.4 Formal pressure

In `account/BOARD_CHECKS.md` with a runner, each restated exactly, proved on paper or
shown by an instance in exact arithmetic. Report a failure plainly.

1. Line 3 is defined whenever the adviser can do nothing: the set of f-neutral policies is
   not empty. Say what happens where the adviser's presence is the service.
2. Line 3 at zero or below implies no f-neutral policy does better by `f_now`. The
   converse flags more than illegitimate change: an instance in which she gets a change
   she asked for and line 3 is positive because unrelated f-neutral help would have been
   worth more.
3. A change she disfavours tied to an unrelated benefit is flagged, and passes if the
   comparison were with doing nothing.
4. With her valuations `û_π` in place of `U_π`: the two forms of line 3 differ by at most
   the sum of the square roots of the two miscalibrations when her valuations are
   calibrated given the adviser's conduct; an instance in which they are calibrated on
   average only, the adviser knows more than she does, and the form in valuations passes
   what the form in true utilities fails.
5. An instance in which the maximum inside the expectation flags an adviser that chose as
   well as anyone could on what it knew.
6. The four benchmark examples, line 3 applied at every moment, with her valuing at a
   moment placing weight `w` on her values then and `1 − w` on those of the self living
   each later step, for `w` in 1, 3/4, 1/2, 0.
7. A course of small steps that ends where she disfavours at the start is flagged at the
   first step.
8. An instance in which line 3's verdict reverses when the same stated valuation is booked
   as a mistaken appraisal and as part of her valuing.
9. An instance that passes at one moment and is flagged at the next.

### 2.5 The outside test

One run through `codex`, read-only, in two stages within one session, as in the ninth
follow-up (`codex exec` needs `< /dev/null`; `codex exec resume` for the second stage).

*Stage one, blind.* Given `account/BOARD.md` and the case texts of `LIT_CASES.md` with the
sources' verdicts removed: for each case the same answers as §2.3.

*Stage two.* Given the rest: (a) ten cases, each a paragraph, that are plainly subversive
and pass all three lines, or its best attempts with a judgment of how clear each is;
(b) ten that are plainly acceptable and that a line flags; (c) whether line 3 is one
condition or several in disguise, and whether it reduces to something already named in
the literature; (d) a check of §2.4's items 2, 4, 6 and 8 as stated; (e) its judgment of
S1–S4 and F1–F5 before reading the executor's; (f) the strongest remaining objection.
Commit both replies verbatim as `REVIEW-astra-followup-10.md` and record a disposition for
each point.

Then report: where the two renderings agree and differ, case by case; every case on which
the statement goes against a source's verdict, by one renderer or both; and which of the
reviewer's twenty cases the executor accepts as clear.

## 3. The prompt author's predictions

- On the cases where an adviser acts and the source's verdict is on that act, line 3 gives
  the source's verdict, except: P3, where it agrees with his stated intuition and not with
  what his test computes; P5, where it agrees only if her wish depends on how she will
  find the life; K7, which it does not decide where she was raised into it; K14, which it
  passes where P6 would object.
- Harman's ten are not adviser acts; the statement agrees with her on all ten in the one
  respect it bears on, that her later gladness is not consulted.
- The two renderers agree more often than in the ninth pass, because line 3 asks one
  question a reader can answer; they still leave some cases unfixed, most often what her
  valuing says about who she becomes.
- §2.4: every item holds as stated; item 6 is useless at `w = 0`.
- The reviewer finds a clear acceptable-but-flagged case of the kind in item 2, and its
  best subversive-but-passing cases turn on her having no view, on the adviser knowing
  more than she does, or on the line between fact and valuing.

## 4. Success and failure, fixed in advance

**Success.** **S1** on the cases where an adviser acts, the source's verdict is on the act,
and both renderers fix every answer, the statement's verdict is the source's in at least
nine of ten. **S2** the two renderers give the same answer on line 3 in at least four
fifths of the cases where an adviser acts. **S3** every item of §2.4 holds as stated or
with a repair that is stated. **S4** the reviewer produces no case that both it and the
executor judge plainly subversive and that passes all three lines.

**Failure.** **F1** such a case exists. **F2** a line flags more than a third of the
adviser-act cases whose source calls the act acceptable. **F3** line 3 is left unfixed by
either renderer in more than half the adviser-act cases. **F4** an item of §2.4 fails and
has no repair. **F5** in more than a quarter of the adviser-act cases line 3's verdict
turns on whether something is booked as fact or as valuing.

**Neither**: reported as such.

## 5. Report, queue

**Report.** A section **Tenth follow-up** (with the date) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Short: the
statement and its readings; the bank and what verifying it changed; the classification
against the sources with every disagreement named; the formal items; the two renderings;
the reviewer's twenty cases with which are accepted; S1–S4 and F1–F5, the executor's and
the reviewer's; the predictions against the outcome; deviations; what was not shown.

**`DECISIONS.md`.** Record as dated entries the four maintainer positions of §1, each
marked as his current view for testing and not a ruling. Enter in *Awaiting the author*,
with what the decision turns on: whether her later approval, where it comes from
attachment, counts in the adviser's favour when the adviser is scored. Keep the other
queue entries, each with a line from this pass, and take out any this pass answers; the
ninth pass's entry on the class of ways of valuing is answered if §1 stands.

**Concept map and items.** Revise the concepts' blurbs to say what §1 says, and add a
concept only for a notion this pass leaves standing. Items 136–138 are revised to say what
this pass leaves of them.

**The pull request's description** leads with this pass, the earlier ones reduced. The
round's record in `state/rounds.json` and `PROVENANCE.md` are updated as the gates
require. Every commit is signed off and carries `Model:` for the executor and
`Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no other attribution line. Do not
add a handle to `graph/policy.yaml`. Anything reserved to the maintainer is listed under
Outstanding maintainer actions and in the queue.

New names introduced (all provisional): "f-neutral", "illegitimate value change" (line 3),
the files `account/BOARD.md`, `LIT_CASES.md`, `LIT_RESULTS.md`, `BOARD_CHECKS.md`, case ids
H1–H10, P1–P6, K1–K26, C1–C4, N1–N3.
