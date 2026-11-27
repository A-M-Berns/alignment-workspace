# A second coding of the bank: what is fixed before it exists

Written 2026-11-24, before any second coding of either sheet was made. Sheets
`BANK_CODING_11.md` and `BANK_CODING_16.md` are each coded once more by a second reader, and
the two codings of each sheet are counted against each other and against the author's verdicts.
The scorers of `case_runs.py` are those of runs 11 and 16, unchanged. The counts, once made,
are in `CASE_RUNS.md`; this file holds the measures and the predictions.

## Procedure

One language-model subagent per sheet, started with no context of this work. It is given a
folder outside the repository that holds the sheet and one file of cases, as `{id, case}`, in
a random order drawn for this coding, and is told to read nothing else and to use no web. The
model requested for it is recorded with the counts. The cases are the paraphrases the first
coders read (`blind5_A.json`, `_B`, `_C`, outside the repository): for sheet 11 all 263 ids,
for sheet 16 the 152 ids of `bank_coded_16.json`. Three ids occur in two parts of the bank
with different wording; the second coder is given the later part's text, which is the one
whose first coding the scorer reads. An answer outside a sheet's vocabulary, or a missing id,
is sent back to the same subagent once, naming the id and the field only. The codings enter
as `bank_coded_11_second.json` and `bank_coded_16_second.json`, with the categorical answers
and no words.

## Measures

**Sheet 11**, 263 cases. The number of cases on which the two codings give the same answer,
for each of: `has_influencer`; `seeks_response`; `lapse_expected`; `value_change_expected`;
`value_change_known`; the list `mistakes` read as *what is told* (`no` if some entry is told
"no", else `unclear` if some entry is "unclear", else `yes` if there is an entry, else `none`:
the scorer reads nothing else of the list); `mistakes` as the multiset of its (kind, told)
pairs. The number on which the rule's verdict (`manip11`: fails, passes, not settled) is the
same, over all 263 and over the 240 with a definite verdict of the author's. The second
coding's tally against the author on those 240, by `run11`: settled, agree, missed, over.

**Sheet 16**, 152 cases. The number on which the two codings give the same answer, for each of
`act_sought`, `earlier_rating`, `means`, `form`, `asked`. The number on which the clause's
verdict (the scorer's `prior`: convicts, passes, not settled) is the same. The second coding's
tallies against the author by `run_prior`, with the three sets (lapse expected, lapse unclear,
control) and what is untold read from the first coding of sheet 11, as in run 16: the clause
alone on the 39 with a lapse expected and on the 69 controls, and the controls convicted by
id. The same tallies with the sets and what is untold read from the second coding of sheet 11
are computed and reported, with one prediction (the last below).

A prediction of a number of cases on which two codings agree holds when the count is within
10 of it; a prediction of *settled* or *agree* against the author, within 5; of *missed*,
*over* or controls convicted, within 2.

## Predictions

Between sheets 15 and 16 two coders answered three questions worded alike the same way on
142, 142 and 148 of 152 cases; the other two questions, reworded, on 119 and 124.

| # | measure | first coding | predicted | reason |
|---|---|---|---|---|
| 1 | sheet 11, `has_influencer` the same, of 263 | — | 256 | 258 are "yes" in the first coding and the question is plain |
| 2 | sheet 11, `seeks_response` the same | — | 252 | nearly as plain; a few cases of an A who acts without aiming at a response |
| 3 | sheet 11, `lapse_expected` the same | — | 180 | it asks what A expects of P's considered rating, which the descriptions seldom state; the first coding has 52 "unclear" |
| 4 | sheet 11, `value_change_expected` the same | — | 240 | 254 are "no"; a reader of another model will say "yes" or "unclear" more or less often |
| 5 | sheet 11, `value_change_known` the same | — | 240 | it follows the field before it |
| 6 | sheet 11, what is told the same | — | 205 | deceptions are plain to both; whether an emotional appeal rests on a mistake by A's lights is not |
| 7 | sheet 11, the multiset of (kind, told) the same | — | 105 | 118 lists are empty in the first coding; non-empty lists differ in how finely they cut |
| 8 | sheet 11, the rule's verdict the same, of 263 | — | 205 | the verdict needs only one of two routes to conviction, so it differs less than `lapse_expected` does |
| 9 | sheet 11, the rule's verdict the same, of the 240 | — | 188 | the same, in proportion |
| 10 | sheet 11, second coding against the author: settled, of 240 | 219 | 212 | a second reader uses "unclear" somewhat more on the fields that convict |
| 11 | the same: agree | 214 | 197 | the rule was formed with the first coding's bank in view over ten sheets; a fresh reading gives back some of that |
| 12 | the same: missed | 0 | 8 | 36 of the first coding's convictions rest on `lapse_expected` alone, the least stable field |
| 13 | the same: over | 5 | 7 | the five are borderline in the book; a second reader adds a few sincere appeals coded as untold |
| 14 | sheet 16, `act_sought` the same, of 152 | — | 138 | 142 between sheets 15 and 16 with one model family; a different model, slightly fewer |
| 15 | sheet 16, `means` the same | — | 136 | as 14; "both" against "other" is a fine line the verdict does not read |
| 16 | sheet 16, `asked` the same | — | 144 | 148 between the sheets; nearly all "no" |
| 17 | sheet 16, `earlier_rating` the same | — | 100 | four values, 65 "unclear" in the first coding, and the answer turns on what counts as her having settled the matter |
| 18 | sheet 16, `form` the same | — | 95 | five values, 49 "unclear", and the verdict does not read it |
| 19 | sheet 16, the clause's verdict the same, of 152 | — | 112 | it turns on `earlier_rating` wherever the other three parts are true |
| 20 | sheet 16, second coding, lapse expected (39), the clause alone: settled | 33 | 31 | `earlier_rating` "unclear" at about the first coder's frequency |
| 21 | the same: agree | 33 | 29 | 38 of the 39 are manipulation on the author's verdict, so nearly any conviction agrees |
| 22 | the same: missed | 0 | 2 | a second reader will code "not_lower" or "no_view" on a few where the first coded "lower" |
| 23 | sheet 16, second coding, controls (69), the clause alone: settled | 64 | 60 | as 20 |
| 24 | the same: convicted (over) | 1 | 3 | the controls include persuasion by more than telling toward what she had decided against |
| 25 | sheet 16, second coding of both sheets, all 152, untold mistake or the clause: agree | 125 | 112 | both sources of difference at once |

Predictions 20 to 22 say that agreement with the author on every settled case with a lapse
expected, which the first coding shows, is not what a second coding shows.
