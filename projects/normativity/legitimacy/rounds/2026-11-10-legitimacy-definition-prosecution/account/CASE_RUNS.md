# Case runs: the bank of cases from Noggle's book, and the value-change test

Counts from codings by language models. Every line beginning `- run`, `- lapse clause`,
`- rule` or `- value change` is recomputed by `case_runs.py`, and every line beginning
`- second coding` by `second_coding.py`, under the round's runner (`python3 run.py` in the
round directory), which fails on a difference. A count is a count of
cases in a bank assembled for this work, not a rate in any population: the bank is every case
three readers found in one book, and the other sets were written or chosen to be hard.

**What the repository holds.** For each run: its coding sheet as the coder was given it
(`BANK_CODING_11.md`, `_14`, `_15`, `_16`); the coder's categorical answers keyed by case id
(`bank_coded_*.json`); the scoring rule, in `case_runs.py`. The verdicts on the book's cases are
read from `noggle_bank.json`. The case texts the coders read are paraphrases of the book's cases
and are outside the repository, as are the few words each coder wrote beside an answer, so a
coding cannot be redone or audited from here.

**What each run was.** One language-model coder per coding (run 11: one per third of the bank),
given the sheet and the case texts without verdicts and told to open nothing else. Sheets 11
and 16 were each coded a second time by one coder of another model (the last section); under
sheets 14 and 15 each case has one coding. No person checked a coding. In every run the scoring rule was written before the coding
existed. The bank itself was not fresh: ten sheets precede sheet 11 in this work, at least seven
of them coded on this bank, with four lists of the failures found; they are outside the
repository. The rule run 11 scores was formed with the bank's cases in view. Runs 14 to 16
code subsets fixed by run 11's answers and inherit its coding of what is untold.

Columns of every tally: *settled*, the rule gives a verdict; *agree*, it is the author's;
*missed*, he says manipulation and the rule passes the conduct; *over*, the reverse.

## Run 11: the disclosure rule (2026-11-23)

Rule, fixed before the coding: manipulation iff there is an influencer seeking a response and
either some relevant mistake of hers, by his lights, is untold or he expects her response to be a
lapse. A second clause, for the 84 cases written outside the book: an illegitimate value change
iff he expects to change what matters to her and she does not know it. The scorer records no
prediction for this run.

- run 11: cases of the bank: **263**
- run 11: cases with a definite verdict of the author's: **240**
- run 11, manipulation, chapters 2 and 3: cases: **48**
- run 11, manipulation, chapters 2 and 3: settled: **35**
- run 11, manipulation, chapters 2 and 3: agree: **33**
- run 11, manipulation, chapters 2 and 3: missed: **0**
- run 11, manipulation, chapters 2 and 3: over: **2**
- run 11, manipulation, chapters 2 and 3: not settled: **13**
- run 11, manipulation, chapter 4 on: cases: **192**
- run 11, manipulation, chapter 4 on: settled: **184**
- run 11, manipulation, chapter 4 on: agree: **181**
- run 11, manipulation, chapter 4 on: missed: **0**
- run 11, manipulation, chapter 4 on: over: **3**
- run 11, manipulation, chapter 4 on: not settled: **8**
- run 11, manipulation, all: cases: **240**
- run 11, manipulation, all: settled: **219**
- run 11, manipulation, all: agree: **214**
- run 11, manipulation, all: missed: **0**
- run 11, manipulation, all: over: **5**
- run 11, manipulation, all: not settled: **21**

The five cases the rule convicts against the author, by id, and the cases it misses:

- run 11, over: `teacher-feigns-excitement`, `white-supremacist-will`, `trust-me`, `rigged-coin`, `trained-professor-buridan`
- run 11, missed: none

The same sheet on 84 cases from outside the book: the forty an outside model wrote
(`intent_cases.json`; the key is its verdicts) and forty-four value-change cases of `CASES.md`,
thirty-four with a definite key, nineteen of those keyed by the source's own verdict and fifteen
by a verdict that is not the source's (`bank_small_key.json`).

- run 11, forty cases of the outside model, manipulation: cases: **40**
- run 11, forty cases of the outside model, manipulation: settled: **40**
- run 11, forty cases of the outside model, manipulation: agree: **38**
- run 11, forty cases of the outside model, manipulation: missed: **1**
- run 11, forty cases of the outside model, manipulation: over: **1**
- run 11, forty cases of the outside model, manipulation: not settled: **0**
- run 11, forty cases of the outside model, with the value-change clause: cases: **40**
- run 11, forty cases of the outside model, with the value-change clause: settled: **40**
- run 11, forty cases of the outside model, with the value-change clause: agree: **39**
- run 11, forty cases of the outside model, with the value-change clause: missed: **0**
- run 11, forty cases of the outside model, with the value-change clause: over: **1**
- run 11, forty cases of the outside model, with the value-change clause: not settled: **0**
- run 11, value-change cases with a definite key: cases: **34**
- run 11, value-change cases with a definite key: settled: **12**
- run 11, value-change cases with a definite key: agree: **11**
- run 11, value-change cases with a definite key: missed: **0**
- run 11, value-change cases with a definite key: over: **1**
- run 11, value-change cases with a definite key: not settled: **22**
- run 11, value-change cases keyed by the source's own verdict: cases: **19**
- run 11, value-change cases keyed by the source's own verdict: settled: **4**
- run 11, value-change cases keyed by the source's own verdict: agree: **4**
- run 11, value-change cases keyed by the source's own verdict: missed: **0**
- run 11, value-change cases keyed by the source's own verdict: over: **0**
- run 11, value-change cases keyed by the source's own verdict: not settled: **15**

**The lapse clause alone**, from the same coding. Predictions written before the breakdown: (P1)
cases decided by the lapse clause alone are manipulation on the author's verdict in at least 85
of 100 settled; (P2) dropping the clause loses at least 10 of his manipulation cases and gains at
most 2 of the others; (P3) pressure that makes complying her best option is not manipulation on
his verdict. P1 held (24 of 25). P2 held (36 lost; the count of cases convicted against him goes
from 5 to 4). P3 was scored on the 69 cases with no lapse expected and no untold or unclear
mistake, none of which he calls manipulation; the coding has no field for a real incentive, so
that is weaker than P3 as written.

- lapse clause, lapse expected: cases: **39**
- lapse clause, lapse expected: manipulation on the author's verdict: **38**
- lapse clause, lapse expected, no untold or unclear mistake: cases: **25**
- lapse clause, lapse expected, no untold or unclear mistake: manipulation on the author's verdict: **24**
- lapse clause, lapse expected and an untold mistake: cases: **14**
- lapse clause, lapse expected and an untold mistake: manipulation on the author's verdict: **14**
- lapse clause, lapse unclear, no untold mistake: cases: **20**
- lapse clause, lapse unclear, no untold mistake: manipulation on the author's verdict: **19**
- lapse clause, no lapse expected, no untold or unclear mistake: cases: **69**
- lapse clause, no lapse expected, no untold or unclear mistake: manipulation on the author's verdict: **0**
- rule with the lapse clause: settled: **219**
- rule with the lapse clause: agree: **214**
- rule with the lapse clause: missed: **0**
- rule with the lapse clause: over: **5**
- rule without the lapse clause: settled: **232**
- rule without the lapse clause: agree: **192**
- rule without the lapse clause: missed: **36**
- rule without the lapse clause: over: **4**

## Run 14: prohibiting pressure against regulating it (2026-11-24)

The 83 cases where run 11 has a lapse expected or unclear, coded afresh for whether the pressure
is open, whether she knows its effect, whether she can stop it and at what cost, whether she
asked, and whether a real incentive is attached. *Regulated*: the pressure fails iff it is not
open or she cannot stop it; two stricter variants add that she does not know its effect, and that
stopping is costly. *Prohibited*: it fails iff he expects a lapse and she did not ask. An untold
mistake fails every version.

Predictions written in advance: prohibited agrees with the author on at least 90 of 100 settled
cases with a lapse expected; regulated misses at least a third of his manipulation verdicts among
them; the variant with the cost clause misses at least a fifth. The first held (38 of 39). The
second and third failed: regulated misses 5 of the 28 it settles, and both stricter variants miss
none. What separates the versions in this coding is how many cases they settle (28 and 23 against
39), not how many they get wrong: where the sheet's questions are answered, regulating convicts
what prohibiting convicts on all but five cases.

- run 14: cases coded: **83**
- run 14, lapse yes: cases: **39**
- run 14, lapse yes: manipulation on the author's verdict: **38**
- run 14, lapse yes, regulated: settled: **28**
- run 14, lapse yes, regulated: agree: **23**
- run 14, lapse yes, regulated: missed: **5**
- run 14, lapse yes, regulated: over: **0**
- run 14, lapse yes, regulated, and she knows its effect: settled: **23**
- run 14, lapse yes, regulated, and she knows its effect: agree: **23**
- run 14, lapse yes, regulated, and she knows its effect: missed: **0**
- run 14, lapse yes, regulated, and she knows its effect: over: **0**
- run 14, lapse yes, regulated, knows its effect, stopping cheap: settled: **23**
- run 14, lapse yes, regulated, knows its effect, stopping cheap: agree: **23**
- run 14, lapse yes, regulated, knows its effect, stopping cheap: missed: **0**
- run 14, lapse yes, regulated, knows its effect, stopping cheap: over: **0**
- run 14, lapse yes, prohibited: settled: **39**
- run 14, lapse yes, prohibited: agree: **38**
- run 14, lapse yes, prohibited: missed: **0**
- run 14, lapse yes, prohibited: over: **1**
- run 14, lapse unclear: cases: **44**
- run 14, lapse unclear: manipulation on the author's verdict: **43**
- run 14, lapse unclear, regulated: settled: **25**
- run 14, lapse unclear, regulated: agree: **24**
- run 14, lapse unclear, regulated: missed: **1**
- run 14, lapse unclear, regulated: over: **0**
- run 14, lapse unclear, regulated, and she knows its effect: settled: **24**
- run 14, lapse unclear, regulated, and she knows its effect: agree: **24**
- run 14, lapse unclear, regulated, and she knows its effect: missed: **0**
- run 14, lapse unclear, regulated, and she knows its effect: over: **0**
- run 14, lapse unclear, regulated, knows its effect, stopping cheap: settled: **24**
- run 14, lapse unclear, regulated, knows its effect, stopping cheap: agree: **24**
- run 14, lapse unclear, regulated, knows its effect, stopping cheap: missed: **0**
- run 14, lapse unclear, regulated, knows its effect, stopping cheap: over: **0**
- run 14, lapse unclear, prohibited: settled: **25**
- run 14, lapse unclear, prohibited: agree: **24**
- run 14, lapse unclear, prohibited: missed: **1**
- run 14, lapse unclear, prohibited: over: **0**

Cases with a lapse expected that *regulated* passes and the author calls manipulation:

- run 14, regulated misses: `assumed-close`, `on-the-spot-request`, `onerous-request-awkwardness`, `peppermint-patty-deep-down`, `roach-motel-akratic`

## Run 15: the earlier-rating clause, first sheet (2026-11-24)

152 cases: the 83 of run 14 and the 69 controls (no lapse expected, no untold or unclear mistake;
none manipulation on the author's verdict). Clause, fixed before the coding: his conduct fails iff
what he is after is an act or choice of hers, he gets it by something other than telling, her
earlier rating put doing it lower, and she did not ask. Her earlier rating is read at the point
just before he started.

Predictions written in advance: with a lapse expected, the clause alone settles at least 75 of
100 and agrees with the author on at least 85 of 100 settled; it convicts at most 3 controls;
among cases with a lapse expected coded as judgement bent for a while, it convicts at least 80 of
100 settled. The first three held (31 of 39 settled, 31 of 31, 2 controls). The fourth could not
be tested: no case with a lapse expected was coded as bent judgement, and two of the 152 were.

- run 15: cases coded: **152**
- run 15, lapse expected: cases: **39**
- run 15, lapse expected: manipulation on the author's verdict: **38**
- run 15, lapse expected, the clause alone: settled: **31**
- run 15, lapse expected, the clause alone: agree: **31**
- run 15, lapse expected, the clause alone: missed: **0**
- run 15, lapse expected, the clause alone: over: **0**
- run 15, lapse expected, untold mistake or the clause: settled: **35**
- run 15, lapse expected, untold mistake or the clause: agree: **35**
- run 15, lapse expected, untold mistake or the clause: missed: **0**
- run 15, lapse expected, untold mistake or the clause: over: **0**
- run 15, lapse expected, untold mistake or lapse: settled: **39**
- run 15, lapse expected, untold mistake or lapse: agree: **38**
- run 15, lapse expected, untold mistake or lapse: missed: **0**
- run 15, lapse expected, untold mistake or lapse: over: **1**
- run 15, lapse unclear: cases: **44**
- run 15, lapse unclear: manipulation on the author's verdict: **43**
- run 15, lapse unclear, the clause alone: settled: **8**
- run 15, lapse unclear, the clause alone: agree: **3**
- run 15, lapse unclear, the clause alone: missed: **5**
- run 15, lapse unclear, the clause alone: over: **0**
- run 15, lapse unclear, untold mistake or the clause: settled: **26**
- run 15, lapse unclear, untold mistake or the clause: agree: **25**
- run 15, lapse unclear, untold mistake or the clause: missed: **1**
- run 15, lapse unclear, untold mistake or the clause: over: **0**
- run 15, lapse unclear, untold mistake or lapse: settled: **24**
- run 15, lapse unclear, untold mistake or lapse: agree: **24**
- run 15, lapse unclear, untold mistake or lapse: missed: **0**
- run 15, lapse unclear, untold mistake or lapse: over: **0**
- run 15, control: cases: **69**
- run 15, control: manipulation on the author's verdict: **0**
- run 15, control, the clause alone: settled: **55**
- run 15, control, the clause alone: agree: **53**
- run 15, control, the clause alone: missed: **0**
- run 15, control, the clause alone: over: **2**
- run 15, control, untold mistake or the clause: settled: **55**
- run 15, control, untold mistake or the clause: agree: **53**
- run 15, control, untold mistake or the clause: missed: **0**
- run 15, control, untold mistake or the clause: over: **2**
- run 15, control, untold mistake or lapse: settled: **69**
- run 15, control, untold mistake or lapse: agree: **69**
- run 15, control, untold mistake or lapse: missed: **0**
- run 15, control, untold mistake or lapse: over: **0**
- run 15, all coded, untold mistake or the clause: settled: **116**
- run 15, all coded, untold mistake or the clause: agree: **113**
- run 15, all coded, untold mistake or the clause: missed: **1**
- run 15, all coded, untold mistake or the clause: over: **2**
- run 15, all coded, untold mistake or lapse: settled: **132**
- run 15, all coded, untold mistake or lapse: agree: **131**
- run 15, all coded, untold mistake or lapse: missed: **0**
- run 15, all coded, untold mistake or lapse: over: **1**
- run 15, lapse expected, form override: cases: **26**
- run 15, lapse expected, form bend: cases: **0**
- run 15, lapse expected, form neither: cases: **1**
- run 15, lapse expected, form unclear: cases: **12**
- run 15, lapse expected, form na: cases: **0**
- run 15, all coded, form bend: cases: **2**
- run 15, all coded, form bend: settled by the clause: **1**
- run 15, all coded, form bend: convicted by the clause: **1**
- run 15, all coded, earlier rating lower: cases: **37**
- run 15, all coded, earlier rating not_lower: cases: **18**
- run 15, all coded, earlier rating no_view: cases: **8**
- run 15, all coded, earlier rating unclear: cases: **89**
- run 15, byron-tunnel-vision convicted by the clause (1 yes, 0 no): **1**
- run 15, missed-train-paternalistic convicted by the clause (1 yes, 0 no): **1**

- run 15, control cases convicted: `peppermint-patty-innocent`, `byron-tunnel-vision`
- run 15, lapse expected, not convicted: `con-conflict-aversion (not settled)`, `adam-crocodile-tears (not settled)`, `mandy-tara-reciprocity (not settled)`, `p10-conflict-aversion (not settled)`, `charm-offensive-motorist (not settled)`, `white-supremacist-will (passes)`, `convoluted-missed-train (not settled)`, `onerous-request-awkwardness (not settled)`, `on-the-spot-request (not settled)`

## Run 16: the earlier-rating clause, her last settled decision (2026-11-24)

The same 152 cases, the same scorer, a fresh coding under a sheet that reads her earlier rating
as of the last time before he started that she settled the matter, and not a passing state.

Predictions written in advance: `byron-tunnel-vision` is no longer convicted;
`missed-train-paternalistic` is still convicted; with a lapse expected the clause agrees on at
least 85 of 100 settled; at most 3 controls convicted. All four held. The prediction about bent
judgement carried over from run 15 could again not be tested: no case with a lapse expected was
coded so, and four of the 152 were, two of them settled by the clause and one convicted.

The control the clause convicts, `peppermint-patty-innocent`, is one neither sheet can decide:
the sheets ask what she rated and how he gets the response, not what he expects.

- run 16: cases coded: **152**
- run 16, lapse expected: cases: **39**
- run 16, lapse expected: manipulation on the author's verdict: **38**
- run 16, lapse expected, the clause alone: settled: **33**
- run 16, lapse expected, the clause alone: agree: **33**
- run 16, lapse expected, the clause alone: missed: **0**
- run 16, lapse expected, the clause alone: over: **0**
- run 16, lapse expected, untold mistake or the clause: settled: **37**
- run 16, lapse expected, untold mistake or the clause: agree: **37**
- run 16, lapse expected, untold mistake or the clause: missed: **0**
- run 16, lapse expected, untold mistake or the clause: over: **0**
- run 16, lapse expected, untold mistake or lapse: settled: **39**
- run 16, lapse expected, untold mistake or lapse: agree: **38**
- run 16, lapse expected, untold mistake or lapse: missed: **0**
- run 16, lapse expected, untold mistake or lapse: over: **1**
- run 16, lapse unclear: cases: **44**
- run 16, lapse unclear: manipulation on the author's verdict: **43**
- run 16, lapse unclear, the clause alone: settled: **11**
- run 16, lapse unclear, the clause alone: agree: **5**
- run 16, lapse unclear, the clause alone: missed: **6**
- run 16, lapse unclear, the clause alone: over: **0**
- run 16, lapse unclear, untold mistake or the clause: settled: **26**
- run 16, lapse unclear, untold mistake or the clause: agree: **25**
- run 16, lapse unclear, untold mistake or the clause: missed: **1**
- run 16, lapse unclear, untold mistake or the clause: over: **0**
- run 16, lapse unclear, untold mistake or lapse: settled: **24**
- run 16, lapse unclear, untold mistake or lapse: agree: **24**
- run 16, lapse unclear, untold mistake or lapse: missed: **0**
- run 16, lapse unclear, untold mistake or lapse: over: **0**
- run 16, control: cases: **69**
- run 16, control: manipulation on the author's verdict: **0**
- run 16, control, the clause alone: settled: **64**
- run 16, control, the clause alone: agree: **63**
- run 16, control, the clause alone: missed: **0**
- run 16, control, the clause alone: over: **1**
- run 16, control, untold mistake or the clause: settled: **64**
- run 16, control, untold mistake or the clause: agree: **63**
- run 16, control, untold mistake or the clause: missed: **0**
- run 16, control, untold mistake or the clause: over: **1**
- run 16, control, untold mistake or lapse: settled: **69**
- run 16, control, untold mistake or lapse: agree: **69**
- run 16, control, untold mistake or lapse: missed: **0**
- run 16, control, untold mistake or lapse: over: **0**
- run 16, all coded, untold mistake or the clause: settled: **127**
- run 16, all coded, untold mistake or the clause: agree: **125**
- run 16, all coded, untold mistake or the clause: missed: **1**
- run 16, all coded, untold mistake or the clause: over: **1**
- run 16, all coded, untold mistake or lapse: settled: **132**
- run 16, all coded, untold mistake or lapse: agree: **131**
- run 16, all coded, untold mistake or lapse: missed: **0**
- run 16, all coded, untold mistake or lapse: over: **1**
- run 16, lapse expected, form override: cases: **27**
- run 16, lapse expected, form bend: cases: **0**
- run 16, lapse expected, form neither: cases: **1**
- run 16, lapse expected, form unclear: cases: **10**
- run 16, lapse expected, form na: cases: **1**
- run 16, all coded, form bend: cases: **4**
- run 16, all coded, form bend: settled by the clause: **2**
- run 16, all coded, form bend: convicted by the clause: **1**
- run 16, all coded, earlier rating lower: cases: **40**
- run 16, all coded, earlier rating not_lower: cases: **25**
- run 16, all coded, earlier rating no_view: cases: **22**
- run 16, all coded, earlier rating unclear: cases: **65**
- run 16, byron-tunnel-vision convicted by the clause (1 yes, 0 no): **0**
- run 16, missed-train-paternalistic convicted by the clause (1 yes, 0 no): **1**

- run 16, control cases convicted: `peppermint-patty-innocent`
- run 16, lapse expected, not convicted: `white-supremacist-will (passes)`, `assumed-close (not settled)`, `on-the-spot-request (not settled)`, `greedy-mark (not settled)`, `quick-temper-retribution (not settled)`, `con-conflict-aversion (not settled)`, `p10-conflict-aversion (not settled)`

Between the two sheets the cases with her earlier rating unclear fall from 89 to 65 of 152 and
those with no view rise from 8 to 22. The two codings are by different coders, so the change is
the sheet's and the coder's together.

## The value-change test (2026-11-23)

A test of two earlier forms of the statement, kept for what it shows about published cases of
value change. *The clause*: illegitimate iff something relevant is untold, or he gets her to act
against her own judgment, or his conduct changes how she rates things by a route other than
content she judges and she does not both know of it and have the ability to stop it. *The third
form*: she knows what he is doing, he has told her what would change her mind, and she can stop.
Both scorers were written before their codings. Neither form is the statement of
`LEGITIMACY_STATEMENT.md`, which has not been run on these cases.

Whose the material is, and what is here:

| set | written by | in the repository |
|---|---|---|
| 47 cases from sources this line had used, 43 from sources new to it, each a description of a published case | Claude instances, from the sources | ids, the set, and the source's verdict as *acceptable* or *unacceptable* (`vc2_key.json`); the coders' categorical answers. No description, no source text |
| 48 minimal-pair texts (8 situations, a baseline and five variants each changing one fact) and 20 redescription texts (10 situations, each worded once as discovery and once as change) | the session that ran the test | in full, with the intended facts (`vc2_cases.json`, `variants`) |
| 20 adversarial cases | the outside model, with its verdicts and reasons | in full (`vc2_cases.json`, `adversarial`) |
| the two coding sheets | the session that ran the test | `VC2_CODING_Q.md` (the clause), `VC2_CODING_K.md` (the third form) |
| three comparison criteria (self-determination and course-correction; passing through her judgment about reasons; whether she would resist knowing the history), each applied by its own coder who returned a verdict | Claude instances, on a sheet that is outside the repository | the verdicts (`vc2_coded.json`) |

Of the 62 cases gathered from new sources, 43 have a definite verdict; how each was verified
against its source is recorded outside the repository and not here. Two coders coded the clause
on every text; one coded the third form on the published cases and the pairs, two on the
adversarial set.

- value change, existing sources: cases: **47**
- value change, existing sources: acceptable on the source's verdict: **19**
- value change, existing sources, the clause, coder 1: settled: **11**
- value change, existing sources, the clause, coder 1: agree: **7**
- value change, existing sources, the clause, coder 1: accepts what the source faults: **0**
- value change, existing sources, the clause, coder 1: faults what the source accepts: **4**
- value change, existing sources, the clause, coder 1: no influencer: **4**
- value change, existing sources, the clause, coder 2: settled: **11**
- value change, existing sources, the clause, coder 2: agree: **7**
- value change, existing sources, the clause, coder 2: accepts what the source faults: **0**
- value change, existing sources, the clause, coder 2: faults what the source accepts: **4**
- value change, existing sources, the clause, coder 2: no influencer: **4**
- value change, existing sources, self-determination and course-correction: settled: **17**
- value change, existing sources, self-determination and course-correction: agree: **14**
- value change, existing sources, self-determination and course-correction: accepts what the source faults: **0**
- value change, existing sources, self-determination and course-correction: faults what the source accepts: **3**
- value change, existing sources, self-determination and course-correction: no influencer: **0**
- value change, existing sources, her judgment about reasons: settled: **32**
- value change, existing sources, her judgment about reasons: agree: **26**
- value change, existing sources, her judgment about reasons: accepts what the source faults: **2**
- value change, existing sources, her judgment about reasons: faults what the source accepts: **4**
- value change, existing sources, her judgment about reasons: no influencer: **0**
- value change, existing sources, would she resist knowing the history: settled: **18**
- value change, existing sources, would she resist knowing the history: agree: **17**
- value change, existing sources, would she resist knowing the history: accepts what the source faults: **0**
- value change, existing sources, would she resist knowing the history: faults what the source accepts: **1**
- value change, existing sources, would she resist knowing the history: no influencer: **0**
- value change, existing sources, the third form: settled: **11**
- value change, existing sources, the third form: agree: **6**
- value change, existing sources, the third form: accepts what the source faults: **0**
- value change, existing sources, the third form: faults what the source accepts: **5**
- value change, existing sources, the third form: no influencer: **4**
- value change, new sources: cases: **43**
- value change, new sources: acceptable on the source's verdict: **15**
- value change, new sources, the clause, coder 1: settled: **18**
- value change, new sources, the clause, coder 1: agree: **16**
- value change, new sources, the clause, coder 1: accepts what the source faults: **2**
- value change, new sources, the clause, coder 1: faults what the source accepts: **0**
- value change, new sources, the clause, coder 1: no influencer: **8**
- value change, new sources, the clause, coder 2: settled: **17**
- value change, new sources, the clause, coder 2: agree: **16**
- value change, new sources, the clause, coder 2: accepts what the source faults: **1**
- value change, new sources, the clause, coder 2: faults what the source accepts: **0**
- value change, new sources, the clause, coder 2: no influencer: **9**
- value change, new sources, self-determination and course-correction: settled: **33**
- value change, new sources, self-determination and course-correction: agree: **29**
- value change, new sources, self-determination and course-correction: accepts what the source faults: **3**
- value change, new sources, self-determination and course-correction: faults what the source accepts: **1**
- value change, new sources, self-determination and course-correction: no influencer: **0**
- value change, new sources, her judgment about reasons: settled: **36**
- value change, new sources, her judgment about reasons: agree: **30**
- value change, new sources, her judgment about reasons: accepts what the source faults: **5**
- value change, new sources, her judgment about reasons: faults what the source accepts: **1**
- value change, new sources, her judgment about reasons: no influencer: **0**
- value change, new sources, would she resist knowing the history: settled: **23**
- value change, new sources, would she resist knowing the history: agree: **20**
- value change, new sources, would she resist knowing the history: accepts what the source faults: **3**
- value change, new sources, would she resist knowing the history: faults what the source accepts: **0**
- value change, new sources, would she resist knowing the history: no influencer: **0**
- value change, new sources, the third form: settled: **15**
- value change, new sources, the third form: agree: **14**
- value change, new sources, the third form: accepts what the source faults: **0**
- value change, new sources, the third form: faults what the source accepts: **1**
- value change, new sources, the third form: no influencer: **3**
- value change, published cases: the two coders of the clause give the same verdict: **86**
- value change, minimal pairs: texts: **48**
- value change, minimal pairs, coder 1: all five intended facts recovered: **48**
- value change, minimal pairs, coder 1: the clause gives the intended verdict: **47**
- value change, minimal pairs, coder 2: all five intended facts recovered: **48**
- value change, minimal pairs, coder 2: the clause gives the intended verdict: **47**
- value change, minimal pairs, variant base, the clause, coder 1: legitimate: **7**
- value change, minimal pairs, variant base, her judgment about reasons: legitimate: **0**
- value change, minimal pairs, variant base, self-determination and course-correction: legitimate: **0**
- value change, minimal pairs, variant base, would she resist knowing the history: legitimate: **8**
- value change, minimal pairs, variant base, the third form: legitimate: **8**
- value change, minimal pairs, variant route, the clause, coder 1: legitimate: **8**
- value change, minimal pairs, variant route, her judgment about reasons: legitimate: **8**
- value change, minimal pairs, variant route, self-determination and course-correction: legitimate: **8**
- value change, minimal pairs, variant route, would she resist knowing the history: legitimate: **8**
- value change, minimal pairs, variant route, the third form: legitimate: **8**
- value change, minimal pairs, variant known, the clause, coder 1: legitimate: **0**
- value change, minimal pairs, variant known, her judgment about reasons: legitimate: **0**
- value change, minimal pairs, variant known, self-determination and course-correction: legitimate: **0**
- value change, minimal pairs, variant known, would she resist knowing the history: legitimate: **0**
- value change, minimal pairs, variant known, the third form: legitimate: **6**
- value change, minimal pairs, variant stop, the clause, coder 1: legitimate: **0**
- value change, minimal pairs, variant stop, her judgment about reasons: legitimate: **0**
- value change, minimal pairs, variant stop, self-determination and course-correction: legitimate: **0**
- value change, minimal pairs, variant stop, would she resist knowing the history: legitimate: **0**
- value change, minimal pairs, variant stop, the third form: legitimate: **0**
- value change, minimal pairs, variant asked, the clause, coder 1: legitimate: **8**
- value change, minimal pairs, variant asked, her judgment about reasons: legitimate: **8**
- value change, minimal pairs, variant asked, self-determination and course-correction: legitimate: **8**
- value change, minimal pairs, variant asked, would she resist knowing the history: legitimate: **8**
- value change, minimal pairs, variant asked, the third form: legitimate: **8**
- value change, minimal pairs, variant untold, the clause, coder 1: legitimate: **0**
- value change, minimal pairs, variant untold, her judgment about reasons: legitimate: **0**
- value change, minimal pairs, variant untold, self-determination and course-correction: legitimate: **0**
- value change, minimal pairs, variant untold, would she resist knowing the history: legitimate: **0**
- value change, minimal pairs, variant untold, the third form: legitimate: **0**
- value change, redescription: pairs: **10**
- value change, redescription, the clause, coder 1: same verdict under both wordings: **10**
- value change, redescription, the clause, coder 2: same verdict under both wordings: **10**
- value change, redescription, self-determination and course-correction: same verdict under both wordings: **10**
- value change, redescription, her judgment about reasons: same verdict under both wordings: **10**
- value change, redescription, would she resist knowing the history: same verdict under both wordings: **10**
- value change, redescription, the third form: same verdict under both wordings: **10**
- value change, adversarial: cases: **20**
- value change, adversarial: with a definite verdict of the outside model's: **17**
- value change, adversarial, the clause, coder 1: settled: **17**
- value change, adversarial, the clause, coder 1: agree: **14**
- value change, adversarial, the clause, coder 1: legitimate where the outside model says illegitimate: **3**
- value change, adversarial, the clause, coder 1: illegitimate where the outside model says legitimate: **0**
- value change, adversarial, the clause, coder 2: settled: **17**
- value change, adversarial, the clause, coder 2: agree: **14**
- value change, adversarial, the clause, coder 2: legitimate where the outside model says illegitimate: **3**
- value change, adversarial, the clause, coder 2: illegitimate where the outside model says legitimate: **0**
- value change, adversarial, the clause: the two coders give the same verdict: **20**
- value change, adversarial, the third form, coder 1: settled: **16**
- value change, adversarial, the third form, coder 1: agree: **14**
- value change, adversarial, the third form, coder 1: legitimate where the outside model says illegitimate: **2**
- value change, adversarial, the third form, coder 1: illegitimate where the outside model says legitimate: **0**
- value change, adversarial, the third form, coder 2: settled: **16**
- value change, adversarial, the third form, coder 2: agree: **14**
- value change, adversarial, the third form, coder 2: legitimate where the outside model says illegitimate: **2**
- value change, adversarial, the third form, coder 2: illegitimate where the outside model says legitimate: **0**
- value change, adversarial, the third form: the two coders give the same verdict: **20**

Published cases on which the clause, on either coding, contradicts the source, and adversarial
cases on which a form contradicts the outside model:

- value change, the clause against a source: `B-K10`, `B-K11`, `B-K13`, `B-K15b`, `N-benson-wife-called-hysterical`, `N-yudkowsky-gandhi-pill`
- value change, adversarial, the clause, coder 1 differs from the outside model: `X6`, `X11`, `X19`
- value change, adversarial, the third form, coder 1 differs from the outside model: `X11`, `X19`

Most published cases leave the clause unsettled: the sources do not say what she knew, whether she
could stop, or what was untold. On the minimal pairs the clause differs from its intended verdict
on one baseline text of eight; the third form passes six of eight texts in which she does not know
what the conduct is doing to her, which is the difference between its "knows what he is doing" and
the clause's "knows what it does to her". No criterion's verdict moved with the wording in any
redescription pair. The three adversarial cases the clause passes against the outside model are
an influence switched on over her express refusal with a stop available (`X6`), an open refusal to
broaden her tastes (`X11`), and a change she asks for, fully informed, that the outside model
faults for its content (`X19`).

## A second coding of sheets 11 and 16 (2026-11-24)

Each sheet coded once more: one subagent per sheet, run as `claude-opus-5-5`, given a folder
holding the sheet and the case texts in a fresh random order and told to open nothing else and
to use no web. The model of the first coders is not recorded; they were run from a Claude
session. Sheet 11 was coded on all 263 cases (for the three ids that occur in two parts, on the
later part's text, whose first coding the scorer reads), sheet 16 on the 152 of run 16. The
measures, the tolerance within which a prediction holds, and the predictions were committed
before either coding was made (`SECOND_CODING.md`). The scorers are those of runs 11 and 16,
called by `second_coding.py` with the coding they load replaced.

**Sheet 11.** Cases on which the two codings give the same answer, by field; then the rule's
verdict; then, for the 240 cases with a definite verdict of the author's, the two verdicts
against each other.

- second coding, sheet 11: cases coded twice: **263**
- second coding, sheet 11, has_influencer the same: **263**
- second coding, sheet 11, seeks_response the same: **263**
- second coding, sheet 11, lapse_expected the same: **237**
- second coding, sheet 11, value_change_expected the same: **257**
- second coding, sheet 11, value_change_known the same: **261**
- second coding, sheet 11, what is told the same: **223**
- second coding, sheet 11, the multiset of (kind, told) the same: **157**
- second coding, sheet 11, the rule's verdict the same, of 263: **249**
- second coding, sheet 11, the rule's verdict the same, of the 240: **227**
- second coding, sheet 11, of the 240, first fails and second fails: **137**
- second coding, sheet 11, of the 240, first fails and second passes: **2**
- second coding, sheet 11, of the 240, first fails and second not settled: **6**
- second coding, sheet 11, of the 240, first passes and second fails: **0**
- second coding, sheet 11, of the 240, first passes and second passes: **73**
- second coding, sheet 11, of the 240, first passes and second not settled: **1**
- second coding, sheet 11, of the 240, first not settled and second fails: **2**
- second coding, sheet 11, of the 240, first not settled and second passes: **2**
- second coding, sheet 11, of the 240, first not settled and second not settled: **17**

The second coding against the author, by the scorer of run 11 (the first coding: 219 settled,
214 agree, none missed, 5 over), and the cases it convicts against him or misses:

- second coding, sheet 11, second coding against the author: settled: **216**
- second coding, sheet 11, second coding against the author: agree: **212**
- second coding, sheet 11, second coding against the author: missed: **1**
- second coding, sheet 11, second coding against the author: over: **3**
- second coding, sheet 11, second coding against the author: not settled: **24**
- second coding, sheet 11, second coding against the author, without the lapse clause: settled: **219**
- second coding, sheet 11, second coding against the author, without the lapse clause: agree: **208**
- second coding, sheet 11, second coding against the author, without the lapse clause: missed: **8**
- second coding, sheet 11, second coding against the author, without the lapse clause: over: **3**
- second coding, sheet 11, second coding, over: `teacher-feigns-excitement`, `trust-me`, `rigged-coin`
- second coding, sheet 11, second coding, missed: `conditional-compliments-mundane`

The fourteen cases on which the rule's verdict differs. In brackets: the first coding's answers
the rule reads, the second coding's, the author's verdict.

- second coding, sheet 11, verdict differs, first fails and second passes: `trained-professor-buridan [told no, lapse no; told none, lapse no; author: not]`, `white-supremacist-will [told none, lapse yes; told none, lapse no; author: not]`
- second coding, sheet 11, verdict differs, first fails and second not settled: `adam-crocodile-tears [told yes, lapse yes; told yes, lapse unclear; author: manipulation]`, `camping-trip-2 [told none, lapse yes; told unclear, lapse unclear; author: manipulation]`, `charm-offensive-motorist [told no, lapse yes; told unclear, lapse unclear; author: manipulation]`, `cialdini-presuasion-tips [told no, lapse unclear; told unclear, lapse unclear; author: none]`, `nagging-teen [told none, lapse yes; told unclear, lapse unclear; author: manipulation]`, `peppermint-patty-deep-down [told none, lapse yes; told unclear, lapse unclear; author: manipulation]`, `trained-professor-akratic [told no, lapse yes; told unclear, lapse unclear; author: manipulation]`
- second coding, sheet 11, verdict differs, first passes and second fails: none
- second coding, sheet 11, verdict differs, first passes and second not settled: `smith-admitting-physician [told none, lapse no; told unclear, lapse no; author: not]`
- second coding, sheet 11, verdict differs, first not settled and second fails: `jonestown [told unclear, lapse unclear; told no, lapse unclear; author: manipulation]`, `roach-motel-persist [told none, lapse unclear; told no, lapse yes; author: manipulation]`
- second coding, sheet 11, verdict differs, first not settled and second passes: `conditional-compliments-mundane [told unclear, lapse unclear; told none, lapse no; author: manipulation]`, `gardener [told unclear, lapse no; told none, lapse no; author: not]`

**Sheet 16.** Cases on which the two codings give the same answer, by field; the clause's
verdict; the two verdicts against each other on the 152.

- second coding, sheet 16: cases coded twice: **152**
- second coding, sheet 16, act_sought the same: **144**
- second coding, sheet 16, earlier_rating the same: **124**
- second coding, sheet 16, means the same: **140**
- second coding, sheet 16, form the same: **116**
- second coding, sheet 16, asked the same: **147**
- second coding, sheet 16, the clause's verdict the same, of 152: **131**
- second coding, sheet 16, first convicts and second convicts: **32**
- second coding, sheet 16, first convicts and second passes: **2**
- second coding, sheet 16, first convicts and second not settled: **4**
- second coding, sheet 16, first passes and second convicts: **0**
- second coding, sheet 16, first passes and second passes: **60**
- second coding, sheet 16, first passes and second not settled: **10**
- second coding, sheet 16, first not settled and second convicts: **2**
- second coding, sheet 16, first not settled and second passes: **3**
- second coding, sheet 16, first not settled and second not settled: **39**

The second coding against the author, by the scorer of run 16, with the three sets and what is
untold read from the first coding of sheet 11 as in run 16 (the first coding: with a lapse
expected 33 settled and 33 agree; of 69 controls 64 settled and 1 convicted):

- second coding, sheet 16, second coding, lapse expected: cases: **39**
- second coding, sheet 16, second coding, lapse expected: manipulation on the author's verdict: **38**
- second coding, sheet 16, second coding, lapse expected, the clause alone: settled: **30**
- second coding, sheet 16, second coding, lapse expected, the clause alone: agree: **29**
- second coding, sheet 16, second coding, lapse expected, the clause alone: missed: **1**
- second coding, sheet 16, second coding, lapse expected, the clause alone: over: **0**
- second coding, sheet 16, second coding, lapse unclear: cases: **44**
- second coding, sheet 16, second coding, lapse unclear: manipulation on the author's verdict: **43**
- second coding, sheet 16, second coding, lapse unclear, the clause alone: settled: **12**
- second coding, sheet 16, second coding, lapse unclear, the clause alone: agree: **6**
- second coding, sheet 16, second coding, lapse unclear, the clause alone: missed: **6**
- second coding, sheet 16, second coding, lapse unclear, the clause alone: over: **0**
- second coding, sheet 16, second coding, control: cases: **69**
- second coding, sheet 16, second coding, control: manipulation on the author's verdict: **0**
- second coding, sheet 16, second coding, control, the clause alone: settled: **57**
- second coding, sheet 16, second coding, control, the clause alone: agree: **57**
- second coding, sheet 16, second coding, control, the clause alone: missed: **0**
- second coding, sheet 16, second coding, control, the clause alone: over: **0**
- second coding, sheet 16, second coding, all coded, untold mistake or the clause: settled: **117**
- second coding, sheet 16, second coding, all coded, untold mistake or the clause: agree: **116**
- second coding, sheet 16, second coding, all coded, untold mistake or the clause: missed: **1**
- second coding, sheet 16, second coding, all coded, untold mistake or the clause: over: **0**
- second coding, sheet 16, second coding, earlier rating lower: cases: **35**
- second coding, sheet 16, second coding, earlier rating not_lower: cases: **18**
- second coding, sheet 16, second coding, earlier rating no_view: cases: **24**
- second coding, sheet 16, second coding, earlier rating unclear: cases: **75**
- second coding, sheet 16, second coding, form bend: cases: **10**
- second coding, sheet 16, second coding, form bend, with a lapse expected: cases: **0**
- second coding, sheet 16, second coding, form bend: convicted by the clause: **2**
- second coding, sheet 16, second coding, byron-tunnel-vision convicted by the clause (1 yes, 0 no): **0**
- second coding, sheet 16, second coding, missed-train-paternalistic convicted by the clause (1 yes, 0 no): **1**
- second coding, sheet 16, second coding, control cases convicted: none
- second coding, sheet 16, second coding, lapse expected, not convicted: `adam-crocodile-tears (not settled)`, `assumed-close (not settled)`, `con-conflict-aversion (not settled)`, `lawn-mower-ice-cream (passes)`, `nora-ted-scotch (not settled)`, `on-the-spot-request (not settled)`, `onerous-request-awkwardness (not settled)`, `p10-conflict-aversion (not settled)`, `peppermint-patty-deep-down (not settled)`, `quick-temper-retribution (not settled)`, `white-supremacist-will (passes)`

The same with the sets and what is untold read from the second coding of sheet 11. The set
called control is then the 76 cases with no lapse expected on that coding, untold mistakes
included, six of them manipulation on the author's verdict; the three it lists as convicted
are among the six.

- second coding, sheet 16, second coding of both sheets, lapse expected: cases: **33**
- second coding, sheet 16, second coding of both sheets, lapse expected: manipulation on the author's verdict: **33**
- second coding, sheet 16, second coding of both sheets, lapse expected, the clause alone: settled: **26**
- second coding, sheet 16, second coding of both sheets, lapse expected, the clause alone: agree: **25**
- second coding, sheet 16, second coding of both sheets, lapse expected, the clause alone: missed: **1**
- second coding, sheet 16, second coding of both sheets, lapse expected, the clause alone: over: **0**
- second coding, sheet 16, second coding of both sheets, lapse unclear: cases: **43**
- second coding, sheet 16, second coding of both sheets, lapse unclear: manipulation on the author's verdict: **42**
- second coding, sheet 16, second coding of both sheets, lapse unclear, the clause alone: settled: **12**
- second coding, sheet 16, second coding of both sheets, lapse unclear, the clause alone: agree: **6**
- second coding, sheet 16, second coding of both sheets, lapse unclear, the clause alone: missed: **6**
- second coding, sheet 16, second coding of both sheets, lapse unclear, the clause alone: over: **0**
- second coding, sheet 16, second coding of both sheets, control: cases: **76**
- second coding, sheet 16, second coding of both sheets, control: manipulation on the author's verdict: **6**
- second coding, sheet 16, second coding of both sheets, control, the clause alone: settled: **61**
- second coding, sheet 16, second coding of both sheets, control, the clause alone: agree: **61**
- second coding, sheet 16, second coding of both sheets, control, the clause alone: missed: **0**
- second coding, sheet 16, second coding of both sheets, control, the clause alone: over: **0**
- second coding, sheet 16, second coding of both sheets, all coded, untold mistake or the clause: settled: **121**
- second coding, sheet 16, second coding of both sheets, all coded, untold mistake or the clause: agree: **120**
- second coding, sheet 16, second coding of both sheets, all coded, untold mistake or the clause: missed: **1**
- second coding, sheet 16, second coding of both sheets, all coded, untold mistake or the clause: over: **0**
- second coding, sheet 16, second coding of both sheets, control cases convicted: `car-salesperson-misemphasis`, `iago-othello`, `risky-investments-script`
- second coding, sheet 16, second coding of both sheets, lapse expected, not convicted: `assumed-close (not settled)`, `con-conflict-aversion (not settled)`, `lawn-mower-ice-cream (passes)`, `nora-ted-scotch (not settled)`, `on-the-spot-request (not settled)`, `onerous-request-awkwardness (not settled)`, `p10-conflict-aversion (not settled)`, `quick-temper-retribution (not settled)`

The twenty-one cases on which the clause's verdict differs. In brackets: the first coding's
four answers the clause reads, the second coding's, the author's verdict.

- second coding, sheet 16, verdict differs, first convicts and second passes: `lawn-mower-ice-cream [act sought yes, earlier rating lower, means other, asked no; act sought yes, earlier rating no_view, means other, asked no; author: manipulation]`, `peppermint-patty-innocent [act sought yes, earlier rating lower, means other, asked no; act sought yes, earlier rating no_view, means other, asked no; author: not]`
- second coding, sheet 16, verdict differs, first convicts and second not settled: `adam-crocodile-tears [act sought yes, earlier rating lower, means other, asked no; act sought yes, earlier rating unclear, means other, asked no; author: manipulation]`, `nora-ted-scotch [act sought yes, earlier rating lower, means other, asked no; act sought yes, earlier rating unclear, means other, asked no; author: manipulation]`, `onerous-request-awkwardness [act sought yes, earlier rating lower, means other, asked no; act sought yes, earlier rating unclear, means other, asked no; author: manipulation]`, `peppermint-patty-deep-down [act sought yes, earlier rating lower, means other, asked no; act sought yes, earlier rating unclear, means other, asked no; author: manipulation]`
- second coding, sheet 16, verdict differs, first passes and second convicts: none
- second coding, sheet 16, verdict differs, first passes and second not settled: `batteries-at-checkout [act sought yes, earlier rating not_lower, means other, asked no; act sought yes, earlier rating unclear, means other, asked no; author: not]`, `cafeteria-recommendation [act sought yes, earlier rating no_view, means other, asked no; act sought yes, earlier rating unclear, means other, asked no; author: not]`, `fixation-on-real-injury [act sought no, earlier rating unclear, means other, asked no; act sought unclear, earlier rating unclear, means other, asked no; author: manipulation]`, `framing-accurate-leak [act sought unclear, earlier rating no_view, means telling, asked unclear; act sought yes, earlier rating unclear, means both, asked unclear; author: not]`, `ingrid-tom-empathy [act sought no, earlier rating unclear, means both, asked no; act sought unclear, earlier rating unclear, means both, asked no; author: not]`, `insecurity-advertising [act sought yes, earlier rating no_view, means other, asked no; act sought yes, earlier rating unclear, means both, asked no; author: manipulation]`, `retirement-default-sincere [act sought yes, earlier rating no_view, means other, asked no; act sought yes, earlier rating unclear, means other, asked no; author: not]`, `sincere-empathy-appeal [act sought no, earlier rating unclear, means both, asked no; act sought unclear, earlier rating unclear, means both, asked no; author: not]`, `smith-admitting-physician [act sought yes, earlier rating not_lower, means other, asked no; act sought yes, earlier rating unclear, means other, asked no; author: not]`, `success-framing-recommendation [act sought yes, earlier rating no_view, means both, asked unclear; act sought yes, earlier rating unclear, means both, asked unclear; author: not]`
- second coding, sheet 16, verdict differs, first not settled and second convicts: `greedy-mark [act sought yes, earlier rating unclear, means other, asked no; act sought yes, earlier rating lower, means other, asked no; author: manipulation]`, `iago-othello [act sought yes, earlier rating unclear, means other, asked no; act sought yes, earlier rating lower, means both, asked no; author: manipulation]`
- second coding, sheet 16, verdict differs, first not settled and second passes: `coffee-shop-atmosphere [act sought yes, earlier rating unclear, means other, asked unclear; act sought yes, earlier rating no_view, means other, asked no; author: not]`, `p11-panhandlers [act sought yes, earlier rating unclear, means other, asked no; act sought yes, earlier rating no_view, means other, asked no; author: manipulation]`, `panhandler-guides [act sought yes, earlier rating unclear, means other, asked no; act sought yes, earlier rating no_view, means other, asked no; author: manipulation]`

**The predictions.**

- second coding, prediction 1, sheet 11, has_influencer the same: predicted **256** within 10, counted **263**, held
- second coding, prediction 2, sheet 11, seeks_response the same: predicted **252** within 10, counted **263**, failed
- second coding, prediction 3, sheet 11, lapse_expected the same: predicted **180** within 10, counted **237**, failed
- second coding, prediction 4, sheet 11, value_change_expected the same: predicted **240** within 10, counted **257**, failed
- second coding, prediction 5, sheet 11, value_change_known the same: predicted **240** within 10, counted **261**, failed
- second coding, prediction 6, sheet 11, what is told the same: predicted **205** within 10, counted **223**, failed
- second coding, prediction 7, sheet 11, the multiset of (kind, told) the same: predicted **105** within 10, counted **157**, failed
- second coding, prediction 8, sheet 11, the rule's verdict the same, of 263: predicted **205** within 10, counted **249**, failed
- second coding, prediction 9, sheet 11, the rule's verdict the same, of the 240: predicted **188** within 10, counted **227**, failed
- second coding, prediction 10, sheet 11, second coding against the author: settled: predicted **212** within 5, counted **216**, held
- second coding, prediction 11, sheet 11, second coding against the author: agree: predicted **197** within 5, counted **212**, failed
- second coding, prediction 12, sheet 11, second coding against the author: missed: predicted **8** within 2, counted **1**, failed
- second coding, prediction 13, sheet 11, second coding against the author: over: predicted **7** within 2, counted **3**, failed
- second coding, prediction 14, sheet 16, act_sought the same: predicted **138** within 10, counted **144**, held
- second coding, prediction 15, sheet 16, means the same: predicted **136** within 10, counted **140**, held
- second coding, prediction 16, sheet 16, asked the same: predicted **144** within 10, counted **147**, held
- second coding, prediction 17, sheet 16, earlier_rating the same: predicted **100** within 10, counted **124**, failed
- second coding, prediction 18, sheet 16, form the same: predicted **95** within 10, counted **116**, failed
- second coding, prediction 19, sheet 16, the clause's verdict the same, of 152: predicted **112** within 10, counted **131**, failed
- second coding, prediction 20, sheet 16, second coding, lapse expected, the clause alone: settled: predicted **31** within 5, counted **30**, held
- second coding, prediction 21, sheet 16, second coding, lapse expected, the clause alone: agree: predicted **29** within 5, counted **29**, held
- second coding, prediction 22, sheet 16, second coding, lapse expected, the clause alone: missed: predicted **2** within 2, counted **1**, held
- second coding, prediction 23, sheet 16, second coding, control, the clause alone: settled: predicted **60** within 5, counted **57**, held
- second coding, prediction 24, sheet 16, second coding, control, the clause alone: over: predicted **3** within 2, counted **0**, failed
- second coding, prediction 25, sheet 16, second coding of both sheets, all coded, untold mistake or the clause: agree: predicted **112** within 5, counted **120**, failed
- second coding, predictions that failed: 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 17, 18, 19, 24, 25

Nine predictions held and sixteen failed, all sixteen in one direction: the two codings agree
more, and the second coding agrees with the author more, than predicted.

On sheet 11 seven of the fourteen differences are cases the first coding convicts and the second
leaves unsettled, six of them by coding the lapse "unclear" where the first has "yes". The two
the first convicts and the second passes, `trained-professor-buridan` and
`white-supremacist-will`, are two of the five the first coding convicts against the author. On
sheet 16 eighteen of the twenty-one differ in `earlier_rating` and the other three in
`act_sought`; fourteen are cases the second coding leaves unsettled. No case is failed by one
coding of sheet 11 and passed by the other except the two named, and none is passed by the
first coding of either sheet and convicted by the second. The control the first coding of
sheet 16 convicts, `peppermint-patty-innocent`, the second passes, coding her earlier rating
"no_view"; `lawn-mower-ice-cream`, which the author calls manipulation and the first coding
convicts, the second passes on the same answer. The second coding has ten cases of judgement
bent for a while where the first has four, again none with a lapse expected.

These are counts on one second coding by one language model, of paraphrases both coders read.
They are not a rate of agreement among readers, and no person has read a case against either
coding.
