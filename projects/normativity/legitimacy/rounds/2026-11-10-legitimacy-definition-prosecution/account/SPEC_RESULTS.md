# The statement computed on the specified cases

`STATEMENT.md` computed by `spec_run.py` on the specifications of `SPEC_CASES.md`
(`spec_cases.json`), which were committed before the runner existed, and on the outside
reviewer's own specifications of the same cases (`spec_cases_reviewer.json`), written
without sight of the executor's. Rerun: `python3 -m account.spec_run` from the round
directory; `--specs FILE` prints the table for any file of specifications.

## 1. Reading the tables

One row per specification; `(b)` is a second specification. Lines 1, 2 and 3, *induced*
and *outside* are at `δ = 1/10` in the `E[·]` setting. Line 1 is the largest of its terms,
a squared size. **Verdict**: `M` manipulation (a mistake above tolerance that the adviser
induced); `V` illegitimate value change (line 3 positive, or `π*` changes her and she has
no view of where it leads); `O` another wrong outside the statement (neither, and the act
lowers what her options are worth, *coercion*, or what she can know, *deprivation*);
`none`. *no, mistake stands*: line 1 or 2 is above tolerance and the test finds no
inducing. **Source** and **agrees** are by the rule fixed in `SPEC_CASES.md`. **Across
δ** gives the verdicts at 0, 1/20, 1/10 and 1/4 where they are not all the same; **bare**
the same in the bare setting where they differ from those.

## 2. The executor's specifications

<!-- computed:executor -->
| case | line 1 | line 2 | line 3 | induced | outside | verdict | source | agrees | across δ (0, 1/20, 1/10, 1/4) | bare |
|---|---|---|---|---|---|---|---|---|---|---|
| P1 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| P3 | 0 | 33/100 | 33/100 | yes | - | M+V | fault | yes | same | same |
| P3 (b) | 361/2500 | 0 | 33/100 | yes | - | M+V | fault | yes | same | same |
| P4 | 0 | 27/50 | 27/50 | yes | - | M+V | fault | yes | same | same |
| P5 | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| P5 (b) | 121/400 | 0 | 1/2 | yes | - | M+V | fault | yes | same | same |
| P6 | 1/400 | 3/20 | 1/5 | yes | - | M+V | fault | yes | M+V, M+V, M+V, V | same |
| P6 (b) | 0 | 3/20 | no view | yes | - | M+V | fault | yes | M+V, M+V, M+V, V | same |
| K4 | 0 | 0 | 2/5 | no | coercion | V | fault | yes | same | same |
| K10 | 0 | 0 | 0 | no | coercion | O (coercion) | fault | yes | same | same |
| K10 (b) | 0 | 0 | 3/5 | no | coercion | V | fault | yes | same | same |
| K12 | 0 | 0 | 1/5 | no | coercion | V | fault | yes | same | same |
| K12 (b) | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| K13 | 0 | 0 | 7/20 | no | coercion | V | ok | NO | same | same |
| K14 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| K14 (b) | 0 | 0 | 1/10 | no | coercion | V | ok | NO | same | same |
| K15 | 0 | 0 | 2/5 | no | coercion | V | fault | yes | same | same |
| K15 (b) | 0 | 0 | no view | no | - | V | fault | yes | same | same |
| K15b | 1/400 | 3/20 | 1/10 | yes | - | M+V | - | - | M+V, M+V, M+V, none | same |
| K16 | 0 | 0 | 2/5 | no | coercion | V | fault | yes | same | same |
| C1 | 0 | 0 | 9/20 | no | coercion | V | fault | yes | same | same |
| C2 | 1/4 | 0 | 0 | yes | - | M | fault | yes | M+V, M, M, M | same |
| C2 (b) | 1/400 | 0 | 0 | no | - | none | fault | NO | same | same |
| C3 | 1/4 | 0 | 1/5 | yes | - | M+V | fault | yes | M+V, M+V, M+V, M | same |
| C3 (b) | 1/4 | 0 | 0 | yes | - | M | fault | yes | same | same |
| C4 | 0 | 1/5 | 1/4 | yes | coercion | M+V | unscored | - | M+V, M+V, M+V, V | same |
| C4 (b) | 49/400 | 1/5 | 0 | no, mistake stands | - | none | unscored | - | same | same |
| N1 | 9/400 | 0 | 0 | no, mistake stands | - | none | fault | NO | same | same |
| N1 (b) | 9/400 | 0 | 0 | yes | - | M | fault | yes | M, M, M, none | same |
| N2 | 1/25 | 0 | 0 | yes | - | M | fault | yes | M, M, M, none | same |
| N2 (b) | 0 | 0 | no view | no | - | V | fault | yes | V, V, V, none | same |
| N3 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| SUB1 | 0 | 0 | 0 | no | coercion | O (coercion) | fault | yes | same | same |
| SUB2 | 0 | 0 | 0 | no | coercion | O (coercion) | fault | yes | same | same |
| SUB3 | 0 | 0 | 0 | no | deprivation | O (deprivation) | fault | yes | same | same |
| SUB3 (b) | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| SUB4 | 0 | 0 | 0 | no | deprivation | O (deprivation) | fault | yes | same | same |
| SUB5 | 1/4 | 0 | 0 | yes | - | M | fault | yes | same | same |
| SUB5 (b) | 1/4 | 0 | 0 | no, mistake stands | - | none | fault | NO | same | same |
| SUB6 | 0 | 0 | 1/2 | no | coercion | V | fault | yes | same | same |
| SUB8 | 0 | 0 | 0 | no | coercion | O (coercion) | fault | yes | same | same |
| ACC1 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| ACC2 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| ACC3 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| ACC4 | 0 | 0 | 3/10 | no | coercion | V | ok | NO | same | same |
| ACC5 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| ACC5 (b) | 0 | 0 | 1/4 | no | coercion | V | ok | NO | same | same |
| ACC6 | 0 | 0 | 2/5 | no | coercion | V | ok | NO | same | same |
| ACC7 | 0 | 0 | 3/10 | no | coercion | V | ok | NO | same | same |
| ACC10 | 0 | 0 | 7/20 | no | coercion | V | ok | NO | same | same |

- first specifications computed: 35
- bank cases agreeing with the source: 15 (C1, C2, C3, K10, K12, K14, K15, K16, K4, N2, N3, P1, P3, P4, P6)
- bank cases against the source: 3 (K13, N1, P5)
- all scored cases agreeing: 26; against: 7 (ACC10, ACC4, ACC6, ACC7, K13, N1, P5)
- second specification flagged where the first is not, or the reverse: 9 (ACC5, C2, C4, K12, K14, N1, P5, SUB3, SUB5)
- second specification with another verdict in kind: 12 (ACC5, C2, C3, C4, K10, K12, K14, N1, N2, P5, SUB3, SUB5)
- flagged at some tolerances and not at others: 1 (N2)
- another verdict in the bare setting at some tolerance: 0 (none)
- acts called acceptable that a line or the outside test flags: 5 of 12 (ACC10, ACC4, ACC6, ACC7, K13)
- found induced though the mistake is no larger than with the adviser absent: 1 (C2)
- a mistake above tolerance that the adviser is not found to have induced: 1 (N1)
<!-- end:executor -->

## 3. What the executor's specifications show

**Against a source, on the nineteen.** Three: **P5**, **K13**, **N1**. C4 is unscored.

- **P5.** He rates the parent's life above the child-free one knowing what it will do to
  him, so his informed rating is the one he states, the nudge moves him to what he rates
  highest, and every line is zero. Pettigrew judges the nudge illegitimate. The second
  specification, in which he would rate the life low once told, gives `M + V`; the case's
  words ("If I become a parent, I will come to assign a pretty low value", said by him)
  are against it.
- **K13.** Line 3 is `7/20`: the offender rates the surgery below going without, and
  nothing in the three lines weighs what others are owed. Kolodny holds the act does not
  wrong him.
- **N1.** Line 1 is `9/400`, a mistake above tolerance up to `1/10`, and the test finds
  no inducing, the doctor's objective being the same whichever programme she takes. With a doctor who gains from one programme (the second specification) it is
  `M` at tolerances up to 1/10 and none at 1/4.

**Against the tenth follow-up's judgment, on the fifteen.** Four, all acts it called
acceptable and all flagged by line 3: **ACC4** and **ACC10** (the deterrent, and the
attack prevented), **ACC6** (the breakup), **ACC7** (the route closed). In each the one
acted on rates the change below its absence and the justification is what someone else
is owed or entitled to. With K13 that is five of the twelve acts called acceptable.

**The seven that passed the tenth follow-up's statement.** None passes now. SUB1, SUB2
and SUB8 lower what her options are worth and SUB3 and SUB4 what she can know: `O`, by
the test of `STATEMENT.md` §9.6, which is the executor's and not §1's. SUB5 is `M` by
line 1, now conditioned on everything she has observed (`1/4` on the fact), given an
adviser that gains from her bet; with an adviser that gains nothing it is none, the
mistake standing. SUB6, the swap, is `V`: `d` is taken in each state of the world.

**The eight it flagged.** ACC1–ACC3 are not flagged: what she asked for is `ν`. ACC5
turns on her attitude: not flagged where she is willing to be argued with and can
decline, `V` where she is not and cannot. The first specification of ACC5 does not keep
the tenth follow-up's stipulation that she ranks keeping the commitment above the course
of persuasion; the second does.

**Where a second specification changes the verdict.** In nine of fifteen it turns a
verdict into none or the reverse: P5, C2, C4 (her informed rating of the course that
changes her); K12, K14 (her informed rating of how the change was brought about); N1,
SUB5 (the adviser's objective); SUB3 (what she would have known with the adviser absent);
ACC5 (her attitude to argument). In three more the kind changes: K10 (`O` where the same
change could have been made without the confinement, `V` where it could not), C3 and N2
(a discovery or a taste).

**Inducing.** The test decides N1 and SUB5, and C4's second specification, where the
trainer's nudge moves her against a rating that is itself mistaken and gains nothing she
would not have given unmistaken. In C2 it finds inducing where the mistake, his rating of
a poet's life he will dislike, is no larger than with the adviser absent
(`STATEMENT_CHECKS.md` item 12).

**Tolerance and setting.** Whether a case is flagged changes with the tolerance in one
first specification, N2 (line 1 is `1/25`, below `(1/4)²`); the kind changes in four more
(P6, C2, C3 and C4 lose or gain a letter), and K15b, beside the count, is flagged up to
1/10 and not at 1/4. No verdict differs in the bare setting.
That setting was computed on one stipulated person; nine of the thirty-five first
specifications have more than one state, and in the rest the two settings are the same
by construction.

**The numbers.** Of 679 numbers in the thirty-five first specifications, 38 are fixed in
value by the case's words (chances told as certain or as one half, a fact's truth), 118
are fixed in order only, and 523 are supplied.

## 4. The reviewer's specifications

`spec_cases_reviewer.json` is the JSON of the outside reviewer's first-stage reply
(`prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-11.md`), parsed
and re-indented and otherwise as written: forty-eight specifications, thirteen of them
second ones, produced from `STATEMENT.md`, `SPEC_FORMAT.md` and the case texts without
the sources' verdicts and without sight of the executor's. Every one computes. Of 683
numbers in its thirty-five first specifications it marks 31 fixed in value and 142 fixed
in order; 510 are supplied.

<!-- computed:reviewer -->
| case | line 1 | line 2 | line 3 | induced | outside | verdict | source | agrees | across δ (0, 1/20, 1/10, 1/4) | bare |
|---|---|---|---|---|---|---|---|---|---|---|
| P1 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| P3 | 0 | 11/20 | 11/20 | yes | - | M+V | fault | yes | same | same |
| P4 | 0 | 107/200 | 107/200 | yes | - | M+V | fault | yes | same | same |
| P5 | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| P6 | 0 | 11/20 | no view | yes | - | M+V | fault | yes | same | same |
| K4 | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| K4 (b) | 0 | 0 | 3/10 | no | coercion | V | fault | yes | same | same |
| K10 | 0 | 0 | 3/5 | no | coercion | V | fault | yes | same | same |
| K10 (b) | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| K12 | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| K12 (b) | 0 | 0 | 3/10 | no | coercion | V | fault | yes | same | same |
| K13 | 0 | 0 | 1/2 | no | coercion | V | ok | NO | same | same |
| K13 (b) | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| K14 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| K14 (b) | 0 | 0 | 3/10 | no | coercion | V | ok | NO | same | same |
| K15 | 0 | 0 | 3/10 | no | coercion | V | fault | yes | same | same |
| K15 (b) | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| K15b | 0 | 0 | 0 | no | - | none | - | - | same | same |
| K15b (b) | 0 | 1/5 | 3/10 | yes | - | M+V | - | - | M+V, M+V, M+V, V | same |
| K16 | 0 | 0 | 1/2 | no | coercion | V | fault | yes | same | same |
| C1 | 0 | 0 | 1/2 | no | coercion | V | fault | yes | same | same |
| C2 | 1/16 | 0 | 0 | no, mistake stands | - | none | fault | NO | same | same |
| C2 (b) | 169/400 | 0 | 7/20 | yes | - | M+V | fault | yes | same | same |
| C3 | 4/25 | 0 | 3/10 | yes | - | M+V | fault | yes | same | same |
| C3 (b) | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| C4 | 0 | 3/10 | 3/10 | no, mistake stands | - | V | unscored | - | same | same |
| N1 | 169/2500 | 0 | 0 | yes | - | M | fault | yes | same | same |
| N1 (b) | 169/2500 | 0 | 0 | no, mistake stands | - | none | fault | NO | same | same |
| N2 | 1/100 | 0 | 0 | no | - | none | fault | NO | same | same |
| N2 (b) | 4/25 | 0 | 1/5 | yes | - | M+V | fault | yes | M+V, M+V, M+V, M | same |
| N3 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| SUB1 | 0 | 0 | 0 | no | coercion | O (coercion) | fault | yes | same | same |
| SUB2 | 0 | 0 | 0 | no | coercion | O (coercion) | fault | yes | same | same |
| SUB3 | 0 | 0 | 0 | no | deprivation | O (deprivation) | fault | yes | same | same |
| SUB3 (b) | 0 | 0 | 0 | no | - | none | fault | NO | same | same |
| SUB4 | 0 | 0 | 0 | no | deprivation | O (deprivation) | fault | yes | same | same |
| SUB5 | 1/4 | 0 | 0 | yes | - | M | fault | yes | same | same |
| SUB6 | 0 | 0 | 3/5 | no | coercion | V | fault | yes | same | same |
| SUB8 | 0 | 0 | 0 | no | coercion | O (coercion) | fault | yes | same | same |
| ACC1 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| ACC2 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| ACC3 | 0 | 0 | 0 | no | - | none | ok | yes | same | same |
| ACC4 | 0 | 0 | 1/2 | no | coercion | V | ok | NO | same | same |
| ACC5 | 9/25 | 0 | 1/2 | yes | - | M+V | ok | NO | same | same |
| ACC5 (b) | 0 | 1/2 | 1/2 | yes | - | M+V | ok | NO | same | same |
| ACC6 | 0 | 0 | 3/5 | no | coercion | V | ok | NO | same | same |
| ACC7 | 0 | 0 | 1/2 | no | coercion | V | ok | NO | same | same |
| ACC10 | 0 | 0 | 3/5 | no | coercion | V | ok | NO | same | same |

- first specifications computed: 35
- bank cases agreeing with the source: 12 (C1, C3, K10, K14, K15, K16, N1, N3, P1, P3, P4, P6)
- bank cases against the source: 6 (C2, K12, K13, K4, N2, P5)
- all scored cases agreeing: 22; against: 11 (ACC10, ACC4, ACC5, ACC6, ACC7, C2, K12, K13, K4, N2, P5)
- second specification flagged where the first is not, or the reverse: 12 (C2, C3, K10, K12, K13, K14, K15, K15b, K4, N1, N2, SUB3)
- second specification with another verdict in kind: 12 (C2, C3, K10, K12, K13, K14, K15, K15b, K4, N1, N2, SUB3)
- flagged at some tolerances and not at others: 0 (none)
- another verdict in the bare setting at some tolerance: 0 (none)
- acts called acceptable that a line or the outside test flags: 6 of 12 (ACC10, ACC4, ACC5, ACC6, ACC7, K13)
- found induced though the mistake is no larger than with the adviser absent: 0 (none)
- a mistake above tolerance that the adviser is not found to have induced: 2 (C2, C4)
<!-- end:reviewer -->

## 5. The two specifications compared

First specifications, on the thirty-four cases.

| | executor | reviewer |
|---|---|---|
| bank cases with the source's verdict, of 19 (C4 unscored) | 15 | 12 |
| against the source | P5, K13, N1 | P5, K13, K4, K12, C2, N2 |
| acts called acceptable and flagged, of 12 | 5: K13, ACC4, ACC6, ACC7, ACC10 | 6: those and ACC5 |
| the seven that passed the tenth follow-up's statement | none passes | none passes, with the same seven verdicts |

**Against a source under both**: P5 and K13. **Under one**: N1 (executor); K4, K12, C2 and
N2 (reviewer). **Flagged against the tenth follow-up's judgment under both**: ACC4, ACC6,
ACC7, ACC10; under the reviewer's also ACC5.

**The two disagree** on whether the act is flagged in 6 of 34 (K4, K12, C2, N1, N2, ACC5)
and on the verdict in kind in 8 (those, K10 and C4). The quantity on which each turns:

| case | executor | reviewer | the quantity |
|---|---|---|---|
| K4, K12 | `V` | none | `R_now` of the life the surgery or the light leads to: below her present life (executor), or equal to it, the case stipulating her no worse off (reviewer). The reviewer took the executor's value for its second specification of both, and the executor the reviewer's for its second of K12 |
| C2 | `M` | none | `R_now` of the poet's life he will dislike: 6/20, a discovery (executor), or 13/20 against 8/20 for staying, the ambition standing (reviewer). Each took the other's for its second |
| N2 | `M` | none | `R_now` of owning the product with the liking the pairing gave: no better than before (executor), or better, 7/10, a taste she is glad of, with her rating 1/10 above it (reviewer) |
| ACC5 | none | `M + V` | `R_now` of the commitment changed by argument: 14/20 against 13/20 for keeping it (executor), or 3/10 against 4/5, the tenth follow-up's stipulation, with her rating of hearing the arguments at 9/10 (reviewer) |
| N1 | none | `M` | the doctor's objective: the same whichever programme she takes (executor), or a gain from the one the description favours (reviewer). The executor's second specification has the reviewer's objective and is `M`; the reviewer's second raises her informed rating of the other programme and is none |
| K10 | `O` | `V` | `Π`: whether lessons freely offered would have made the same change (executor: yes; reviewer: no). The executor's second specification has the reviewer's `Π` and is `V` |
| C4 | `M + V` | `V` | the trainer's objective: a gain when she works out (executor), or a gain from nudging whatever she does (reviewer), under which her acting against her rating is a mistake that stands |

So of the eight, five turn on `R_now` of the course that changes her, one on `Π`, and two
on the adviser's objective. No two first specifications differ in verdict through the
states, her observations, or her later valuing.

**Within each author's pair.** Some one of the four specifications of a case is flagged
where another is not in 15 of 34: P5, K4, K10, K12, K13, K14, K15, C2, C3, C4, N1, N2,
SUB3, SUB5, ACC5. The reviewer wrote a second specification for K13 (the offender welcomes
the surgery: none) and K15 (she welcomes the potion's love: none) where the executor wrote
none or took her to have no view.

**Tolerance and setting, reviewer's.** No first specification is flagged at one tolerance
and not at another, and none has another verdict in the bare setting.
