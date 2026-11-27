# Legitimacy against plain telling: the forms that failed

A record of failed attempts, kept as such. Between 26 and 27 November 2026 the statement of
`PLAIN_TELLING_STATEMENT.md` was reached through five forms. Each section says what a form was,
what broke it, and the smallest case that did. Four outside reviews did most of the breaking;
their briefs and replies are verbatim in `REVIEW-astra-followup-22.md` in the round's prompts
directory, where each finding is listed with how it was checked. The forms that reviews 18 to
20 read are quoted in full in their briefs. `review_cases.json` holds the smallest cases of
reviews 19 and 20 that fit the test's format, and the round's runner computes the present
clauses on them (`PLAIN_TELLING_TESTS.md` §3). Paths are relative to this directory.

Throughout: one case of weight 1, one plain telling, no request, nothing declined, zero
tolerances, unless a line says otherwise. `a` and `b` are her two options.

## 1. Where it started

The three sentences of `LEGITIMACY_STATEMENT.md` rest on what she, at her last settled
decision, would have judged that seeing and hearing a thing should move her. No described
case supplies that, and each formal object built on it (reviews 10 to 15, `LEDGER.md` rows 16,
29 and 50) was found to differ from the sentences. After the fifteenth outside review and a
sixteenth, which is not on record in this repository, the maintainer judged that the
sentences had drifted, through fitting to cases, from the idea they began with, and went back
to the rule tested on 23 November (`CASE_RUNS.md`, run 11). From here on
every notion is either part of his own decision problem, his options and his forecasts for
each, or something she said.

## 2. The rule restated: disclosure and pressure (26 November)

**The form.** His conduct is legitimate when (1) he tells her his view wherever she is
mistaken, by his lights, about something her response depends on, a thing being owed only if
she would respond differently knowing it and unless she has declined to hear it; and (2) he
does not get her to act against her own considered rating, unless she asked. It was meant to
imply a core: no fault of hers, by his lights, is his means.

**Broken by** review 17, which read the form in words.

- *A mistake he brings about and announces.* He states a number and says he expects it to
  shift her estimate. She understands, and it shifts her considered rating; he takes the shift
  to be a bias and chose the number for that. He has told her everything and she acts on her
  rating. Clause 1 made him tell her of the mistake; nothing forbade his causing it.
- *What is owed is not defined item by item.* She buys only if the product is both safe and
  compatible, believes both, and both are false. Correcting either makes her decline; once one
  is corrected the other no longer changes what she does. "Owed only if she would respond
  differently" has no answer for either alone.
- *The clauses do not imply the core as worded.* He takes her susceptibility to familiarity to
  be a fault, shows her one design repeatedly, says what he expects, and she lets it go on and
  comes to prefer it. Both clauses hold and the fault is his means.
- *A sentence in the brief was false*: that what no competent predictor foresees is not his
  doing. He tosses a coin to choose which way to condition her.

**What was done.** "He tells her" became a comparison: his conduct leaves her with no mistake
that plainly telling her would not have left. That covers a mistake he brings about, and takes
what is owed all at once. "Fault" became "mistake": a false belief or impression, or a choice
against her own judgement. A liking produced by familiarity with no false impression is not a
mistake, so the third case is within the statement by the maintainer's ruling
(`DECISIONS.md`, `2026-11-27--legitimacy-statement-against-plain-telling`, rule 6); the review's
main recommendation, a separate condition that she authorise the method and its course, was
not taken, and stands as a disagreement with outside readers. The sentence about predictors
was withdrawn.

## 3. No further from his view than plain telling (27 November)

**The form.** *Gap* on a set of matters: how far her rating would move were her views on those
matters replaced by his. Clause 1 (`Belief`): on no set of undeclined matters is the gap under
his conduct larger than under any plain telling. Clause 2 (`Will`): his weight on her lapsing
through his conduct is small, unless she asked. Two versions were reviewed.

**The first version, broken by** review 18. The gap was on the absolute rating of an option,
her rating with views replaced was a supplied table, and a lapse was his when she lapsed and
under some plain telling would have taken a different act.

- *A lapse he creates without changing her act.* Ratings of `(a, b)`: `(1, 0)` after plain
  telling, `(0, 1)` under his conduct; she takes `a` under both. She acts against her
  judgement only under his conduct, and the clause passes it because the act is the same.
- *Help convicted.* Three options rated 2, 0, 1; after plain telling she takes the second,
  under his conduct the third. Both fall short and he has moved her to the better; the clause
  fails him because the act differs.
- *A common shift counted as a gap.* Replacement adds 1 to her rating of both options under his
  conduct and nothing after plain telling. No comparison changes and clause 1 fails.
- *No plain telling.* With the set of plain tellings empty every conduct passed.

**What was done.** Clause 2 compares how far short of her own rating she falls (`Worse`). The
gap is on the difference between two options. Her rating with views replaced is built from her
views, his views and her evaluation (`rate`). At least one plain telling is required.

**The second version, broken by** review 19.

- *A gap has no direction.* She rates `a` at her view `v` of one matter and `b` at 0. His view
  is −1. Plain telling leaves her at −3, and she takes `b`. He gives her a false assurance that
  leaves her at 1, and she takes `a`. Both gaps are 2, she falls short of her own rating under
  neither, and the conduct passes. By his view she now takes the worse option, through a false
  belief he created.
- *Her own weakness excused running a course.* Stopping is rated 0 and where the course ends
  −1; she knows it and goes on, under his conduct and after plain telling alike. Both
  shortfalls are 1 and running the course passes.

Also reported and corrected in the comments: a shortfall she would have under every plain
telling was described as his not being the cause; the result on signals was described as
two-sided and is one-sided.

**What was done.** The gap clause was removed. Clause 1 became `Open`, about what she takes
his view to be. In a course, plain telling means the course is not run.

## 4. An outcome test inside the definition (27 November, some hours)

**The form.** `Open`, `Outcome` and `Will`: she is not left wrong about what he thinks; what
she does is no worse by his views than under a plain telling; what she does is no worse by her
own rating.

**Broken by** its author; no review read it.

- *The theorems restated a clause.* `chooses_as_informed`, `gain_le`, `not_led_astray` and the
  long-run results take `Outcome` as their hypothesis. With `Outcome` a clause of the
  definition, each said that conduct which leaves her doing no worse leaves her doing no
  worse.
- *A distortion induced openly, for her good, passed.* She rates `a` at her view of one matter
  and `b` at 0. His view is 1, and plain telling would leave her agreeing with him. His conduct
  leaves her at 5; she knows his view and takes `a` either way. Nothing is hidden, what she
  does is what his view rates best, and she takes what she rates best. By arithmetic on the
  problem of `Witness.w2_for_her_good_by_distortion`, not a Lean theorem; that theorem shows
  the same problem failing `Between`, and 5 is not between 1 and 1.

**What was done.** The outcome test left the definition and stands beside it as `Outcome`. A
clause on her views took its place.

## 5. Betweenness of how she weighs her options (27 November)

**The form.** Clause 2 (`Views` then; `Weighing` now, and the form built on it `LegitW`): how
she compares any two of her options lies between how a plain telling would leave her comparing
them and how she would with his views substituted. With it came `bridge` and
`outcome_of_views`: for two options and an unchanged evaluation, the clause gives the outcome
up to her own lapses and choices she rates nearly even.

**Broken by** review 20. The clause measured the combined effect of her views on a comparison,
not her views.

- *Two mistakes that cancel passed.* She rates `a` at `x + y − 1` and `b` at 0. His views are
  `(0, 0)`. Plain telling leaves her at `(0, 3)`, taking `a`. His conduct, an anchor he
  announces, leaves her at `(−2, 2)`, taking `b`. Her comparison is 2 after plain telling, −1
  under his conduct and −1 with his views: between. The mistake he induced on `x` is his means.
- *Correcting one of two failed.* She rates `a` at `x + y` and `b` at 0. His views are
  `(0, 0)`; plain telling leaves `(1, −1)`; his conduct corrects the first and leaves
  `(0, −1)`. Her comparison is 0 after plain telling, −1 under his conduct and 0 with his
  views: not between. He removed a mistake and introduced none.
- *A new mistake that moves no comparison passed.* She rates `a` at `v² − 1/2`. His view and
  hers after plain telling are 1; his conduct leaves her at −1. Every comparison is 1/2.

Also reported: a lie she sees through passes `Open`; several comments named clause 2 where the
hypothesis was `Outcome`; the comment on the course result needed `lam ≥ τ`; with more than
two options a near-even exception must be about the options in play; and the brief's remark
that no instance showed the unchanged-evaluation assumption needed was wrong, the pattern of
`Witness.worse_by_him_fails` with `Witness.legit_W` showing it.

This was the fourth review running to find a hole at one joint, between a condition on her
views and what she does. The conclusion drawn, with the maintainer's agreement: stop looking
for one clause that is both faithful to the sentence and yields the outcome; state the two
levels and prove what lies between (`DECISIONS.md`, the same entry, rules 9 and 10).

## 6. Betweenness of her beliefs (the present form)

Clause 2 is `Beliefs`: on each matter her view lies between where a plain telling would leave
it and his own. On review 20's three cases: the cancelling pair fails (−2 is not between 0 and
0); correcting one of two passes, and is `Witness.w3_correcting_one_of_two`; the new mistake
fails (−1 is not between 1 and 1). The second is legitimate conduct with a worse outcome by
his views, and `gap` says that is one of four ways the outcome can fail while the statement
holds. The comments were corrected, the course comment states its condition, and clause 1's
comment says what it does with a lie she sees through.

No outside review has read this form. What it leaves open is `PLAIN_TELLING_STATEMENT.md` §7
and §8. By the maintainer's ruling there is no further round of review and repair: a
structural limit found from here is stated.

## 7. Reported by the reviews and not repaired

- A condition that she authorise the method by which she is changed, and that approval after a
  change not authorise the process that produced it (reviews 17 and 18; reviews 13 and 14 of
  the three sentences pressed the same).
- Ratings need one cardinal scale across his options; a positive rescaling of her ratings
  under one option changes verdicts (reviews 19 and 20).
- Comparing with every plain telling can leave nothing legitimate when tellings trade off
  (reviews 18 and 19).
- Matters can be left out of `matters`, and partial replacement can produce views no one holds
  (review 19); a change can be put in `views` or in `eval` (reviews 19 and 20).
- A lie she sees through passes (review 20).
- Deliberate use of a mistake that plain telling would also leave can pass (reviews 18 and 20).
- The cross-counterfactual evaluation, her evaluation under his conduct applied to the views a
  plain telling would leave, is not identified by forecasts of what she will believe and do
  under each option (review 20).
- What the long-run results score is not observed (review 19).
