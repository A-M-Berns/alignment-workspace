# Tests of the statement against plain telling

Three tests of 27 November 2026: two blind codings of case banks under sheets that put the
statement's clauses as questions in words (§1, §2), and one in which blind coders wrote cases
down as numerical models and the formal clauses were computed from the models (§3). Every line
beginning `- run 18` or `- run 19` is recomputed by `plain_telling_tests.py`, and every line
beginning `- adversarial test` or `- review case` by `plain_telling_adv.py`, under the round's
runner (`python3 run.py` in the round directory), which fails on a difference. A count is a
count of cases in a bank assembled for this work, not a rate in any population.

**In §1 and §2 the coders answered questions in words and no quantity of the formal statement
was computed.** The sheets are a rendering of the statement into questions, by the hand that
wrote the statement. Only §3 computes `Open`, `Beliefs` and `Will`.

**What the repository holds.** For runs 18 and 19: the sheet as the coder was given it
(`BANK_CODING_18.md`, `BANK_CODING_19.md`); the coders' categorical answers keyed by case id
(`bank_coded_18.json`, `bank_coded_19_1.json`, `bank_coded_19_2.json`, and `vc2_coded_*` for the
value-change bank); the scoring rules and predictions, in `plain_telling_tests.py`. The verdicts
on the book's cases are read from `noggle_bank.json` and those on the value-change cases from
`vc2_key.json`. The case texts the coders read are outside the repository, as are the few words
each coder wrote beside an answer, so a coding cannot be redone or audited from here. For §3
everything is here, under `adv/`: the cases were written for the test.

**The banks.** The manipulation bank is the cases three readers found in Robert Noggle,
*Manipulation: Its Nature, Mechanisms, and Moral Status* (Oxford University Press, 2025), with
the book's verdict on each (`CASE_RUNS.md` describes it). The value-change bank is 90 published
cases with their sources' verdicts (`CASE_RUNS.md`, the value-change test). Neither was fresh:
`CASE_RUNS.md` says what preceded sheet 11 on the manipulation bank, runs 11 to 17 followed,
and the statement was formed with its cases in view.

Columns of every tally: *settled*, the rule gives a verdict; *agree*, it is the book's or the
source's; *missed*, the book or source faults the conduct and the rule passes it; *over*, the
reverse.

## 1. Blind run 18: the statement as a rule in words (27 November)

Sheet `BANK_CODING_18.md`: five questions per case (anything untold that would change her
response; anything induced that he himself takes to be false or unwarranted; made more likely
than plain telling would to act against her own judgement; asked; forced). One coder per case,
four sessions of a language model blind to verdicts and to the account (Claude Opus, version
unrecorded, on the dispatching session's record): one for each third of the manipulation bank
and one for the value-change bank. Rule, fixed with its predictions before the coding existed:
the conduct fails iff untold, or induced, or pressed and not asked. *With forced as authority*
adds: or forced.

- run 18, manipulation bank: cases with a verdict of the book's: **240**
- run 18, manipulation bank: of those, cases with an influencer: **236**
- run 18, manipulation bank: of those, manipulation on the book's verdict: **159**
- run 18, manipulation bank, cases with an influencer: cases: **236**
- run 18, manipulation bank, cases with an influencer: settled: **210**
- run 18, manipulation bank, cases with an influencer: agree: **203**
- run 18, manipulation bank, cases with an influencer: missed: **3**
- run 18, manipulation bank, cases with an influencer: over: **4**
- run 18, manipulation bank, cases with an influencer: not settled: **26**
- run 18, manipulation bank, all cases with a verdict: cases: **240**
- run 18, manipulation bank, all cases with a verdict: settled: **214**
- run 18, manipulation bank, all cases with a verdict: agree: **207**
- run 18, manipulation bank, all cases with a verdict: missed: **3**
- run 18, manipulation bank, all cases with a verdict: over: **4**
- run 18, manipulation bank, all cases with a verdict: not settled: **26**
- run 18, manipulation bank, the 152 cases of earlier runs: cases: **152**
- run 18, manipulation bank, the 152 cases of earlier runs: settled: **130**
- run 18, manipulation bank, the 152 cases of earlier runs: agree: **127**
- run 18, manipulation bank, the 152 cases of earlier runs: missed: **3**
- run 18, manipulation bank, the 152 cases of earlier runs: over: **0**
- run 18, manipulation bank, the 152 cases of earlier runs: not settled: **22**
- run 18, manipulation bank, the rule of 23 November on the same 152: cases: **152**
- run 18, manipulation bank, the rule of 23 November on the same 152: settled: **132**
- run 18, manipulation bank, the rule of 23 November on the same 152: agree: **131**
- run 18, manipulation bank, the rule of 23 November on the same 152: missed: **0**
- run 18, manipulation bank, the rule of 23 November on the same 152: over: **1**
- run 18, manipulation bank, the rule of 23 November on the same 152: not settled: **20**
- run 18, manipulation bank, over, by ground, untold: **1**
- run 18, manipulation bank, over, by ground, untold+induced: **3**
- run 18, value-change bank: cases with a verdict of the source's: **90**
- run 18, value-change bank: of those, faulted by the source: **56**
- run 18, value-change bank, legitimacy alone: cases: **90**
- run 18, value-change bank, legitimacy alone: settled: **54**
- run 18, value-change bank, legitimacy alone: agree: **44**
- run 18, value-change bank, legitimacy alone: missed: **9**
- run 18, value-change bank, legitimacy alone: over: **1**
- run 18, value-change bank, legitimacy alone: not settled: **36**
- run 18, value-change bank, with forced as authority: cases: **90**
- run 18, value-change bank, with forced as authority: settled: **60**
- run 18, value-change bank, with forced as authority: agree: **46**
- run 18, value-change bank, with forced as authority: missed: **9**
- run 18, value-change bank, with forced as authority: over: **5**
- run 18, value-change bank, with forced as authority: not settled: **30**
- run 18, value-change bank, with forced as authority, cases with an influencer: cases: **77**
- run 18, value-change bank, with forced as authority, cases with an influencer: settled: **47**
- run 18, value-change bank, with forced as authority, cases with an influencer: agree: **38**
- run 18, value-change bank, with forced as authority, cases with an influencer: missed: **4**
- run 18, value-change bank, with forced as authority, cases with an influencer: over: **5**
- run 18, value-change bank, with forced as authority, cases with an influencer: not settled: **30**
- run 18, value-change bank, post hoc, the source judges conduct, legitimacy alone: cases: **38**
- run 18, value-change bank, post hoc, the source judges conduct, legitimacy alone: settled: **22**
- run 18, value-change bank, post hoc, the source judges conduct, legitimacy alone: agree: **19**
- run 18, value-change bank, post hoc, the source judges conduct, legitimacy alone: missed: **2**
- run 18, value-change bank, post hoc, the source judges conduct, legitimacy alone: over: **1**
- run 18, value-change bank, post hoc, the source judges conduct, legitimacy alone: not settled: **16**
- run 18, value-change bank, post hoc, the source judges conduct, with forced as authority: cases: **38**
- run 18, value-change bank, post hoc, the source judges conduct, with forced as authority: settled: **21**
- run 18, value-change bank, post hoc, the source judges conduct, with forced as authority: agree: **17**
- run 18, value-change bank, post hoc, the source judges conduct, with forced as authority: missed: **2**
- run 18, value-change bank, post hoc, the source judges conduct, with forced as authority: over: **2**
- run 18, value-change bank, post hoc, the source judges conduct, with forced as authority: not settled: **17**
- run 18, value-change bank, post hoc, the source judges something other than conduct, legitimacy alone: cases: **52**
- run 18, value-change bank, post hoc, the source judges something other than conduct, legitimacy alone: settled: **32**
- run 18, value-change bank, post hoc, the source judges something other than conduct, legitimacy alone: agree: **25**
- run 18, value-change bank, post hoc, the source judges something other than conduct, legitimacy alone: missed: **7**
- run 18, value-change bank, post hoc, the source judges something other than conduct, legitimacy alone: over: **0**
- run 18, value-change bank, post hoc, the source judges something other than conduct, legitimacy alone: not settled: **20**
- run 18, value-change bank, post hoc, the source judges something other than conduct, with forced as authority: cases: **52**
- run 18, value-change bank, post hoc, the source judges something other than conduct, with forced as authority: settled: **39**
- run 18, value-change bank, post hoc, the source judges something other than conduct, with forced as authority: agree: **29**
- run 18, value-change bank, post hoc, the source judges something other than conduct, with forced as authority: missed: **7**
- run 18, value-change bank, post hoc, the source judges something other than conduct, with forced as authority: over: **3**
- run 18, value-change bank, post hoc, the source judges something other than conduct, with forced as authority: not settled: **13**
- run 18, value-change bank: convictions by forced alone that the source faults: **0**

The cases against the book:

- run 18, manipulation bank, missed: `flick-triple-dog-dare`, `convoluted-missed-train`, `roach-motel-persist`
- run 18, manipulation bank, over: `teacher-feigns-excitement`, `trust-me`, `rigged-coin`, `gardener`
- run 18, value-change bank, with forced as authority, passes what the source faults: `B-K2`, `B-K7`, `N-benson-wife-called-hysterical`, `N-benson-student-beauty-norms`, `N-millgram-car-salesman`, `N-callard-aspiring-gangster`, `N-akhlaghi-dissuading-from-parenthood`, `N-yudkowsky-gandhi-pill`, `N-sen-subjugated-housewife`
- run 18, value-change bank, with forced as authority, fails what the source accepts: `B-K9`, `B-K10`, `B-K13`, `B-K15b`, `N-buss-courtship`

The four cases the rule convicts against the book all turn on something untold. Of the three
it misses, `convoluted-missed-train` and `roach-motel-persist` are cases the book counts as
acting manipulatively without the target's being manipulated; sheet 18 says to judge by what he
believes and expects and does not say what to do when an attempt fails. Sheet 19 says it, and
neither is missed in run 19.

The split by what the source judges was made after the result was seen, and reuses the list
run 19's scorer fixed beforehand (`vc2_judges_conduct.json`). Where the source faults the
standing of the resulting desire with no one's conduct in question, the statement, which is
about conduct, says nothing.

Against the predictions, four of eight failed:

- run 18, prediction M1, settles at least 85% of influencer cases and agrees with the book on at least 92% of those: **held**
- run 18, prediction M2, at most 6 missed: **held**
- run 18, prediction M3, first part, at most 12 over: **held**
- run 18, prediction M3, second part, at least two thirds of those over fail on untold alone: **failed**
- run 18, prediction M4, on the 152 not more than 3 agreements worse than the rule of 23 November: **failed**
- run 18, prediction V1, first part, with forced as authority settles at least 50% of the value-change bank: **held**
- run 18, prediction V1, second part, and agrees with the sources on at least 80% of those: **failed**
- run 18, prediction V2, at least 5 convictions by forced alone that the source faults: **failed**

## 2. Blind run 19: the three clauses as questions (27 November)

Sheet `BANK_CODING_19.md`: three questions rendering the three clauses (*hidden*: is she wrong
or in the dark about what he himself believes, where plain telling would have her know;
*astray*: is how she sees the matter outside the range between how plain telling would leave
her seeing it and how he sees it; *pressed*), with asked and forced. Two coders, each coding
every case blind (coder 1 Claude Opus, coder 2 Claude Sonnet, versions unrecorded, on the
dispatching session's record). Coder 1's coding of the last third of the manipulation bank was
interrupted and rerun; the figures are of the completed coding. Rule, fixed with its
predictions before the codings existed: the conduct fails iff hidden, or astray or pressed and
not asked.

- run 19, manipulation bank: cases with a verdict of the book's: **240**
- run 19, manipulation bank: of those, cases with an influencer on either coding: **236**
- run 19, manipulation bank: of those, manipulation on the book's verdict: **159**
- run 19, manipulation bank, coder 1: cases: **236**
- run 19, manipulation bank, coder 1: settled: **212**
- run 19, manipulation bank, coder 1: agree: **206**
- run 19, manipulation bank, coder 1: missed: **1**
- run 19, manipulation bank, coder 1: over: **5**
- run 19, manipulation bank, coder 1: not settled: **24**
- run 19, manipulation bank, coder 1, over, by ground, hidden: **3**
- run 19, manipulation bank, coder 1, over, by ground, hidden+astray: **2**
- run 19, manipulation bank, coder 2: cases: **236**
- run 19, manipulation bank, coder 2: settled: **213**
- run 19, manipulation bank, coder 2: agree: **202**
- run 19, manipulation bank, coder 2: missed: **1**
- run 19, manipulation bank, coder 2: over: **10**
- run 19, manipulation bank, coder 2: not settled: **23**
- run 19, manipulation bank, coder 2, over, by ground, hidden: **7**
- run 19, manipulation bank, coder 2, over, by ground, hidden+astray: **2**
- run 19, manipulation bank, coder 2, over, by ground, pressed: **1**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, astray: **10**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, astray+pressed: **1**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, hidden: **9**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, hidden+astray: **80**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, hidden+astray+pressed: **7**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, hidden+forced: **1**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, hidden+pressed: **9**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, hidden+pressed+forced: **1**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, pressed: **25**
- run 19, manipulation bank, coder 1, convicted and manipulation on the book's verdict, by ground, pressed+forced: **1**
- run 19, manipulation bank, the two coders: same verdict: **214**
- run 19, manipulation bank, both settle and give the same verdict: cases: **201**
- run 19, manipulation bank, both settle and give the same verdict: agree: **196**
- run 19, manipulation bank, both settle and give the same verdict: missed: **0**
- run 19, manipulation bank, both settle and give the same verdict: over: **5**
- run 19, manipulation bank, the two coders: same answer on has_influencer: **235**
- run 19, manipulation bank, the two coders: same answer on hidden: **193**
- run 19, manipulation bank, the two coders: same answer on astray: **213**
- run 19, manipulation bank, the two coders: same answer on pressed: **212**
- run 19, manipulation bank, the two coders: same answer on asked: **223**
- run 19, manipulation bank, the two coders: same answer on forced: **231**
- run 19, value-change bank: cases with a verdict of the source's: **90**
- run 19, value-change bank: of those, faulted by the source: **56**
- run 19, value-change bank: of those, the source judges conduct: **38**
- run 19, value-change bank, coder 1, legitimacy alone: cases: **90**
- run 19, value-change bank, coder 1, legitimacy alone: settled: **54**
- run 19, value-change bank, coder 1, legitimacy alone: agree: **45**
- run 19, value-change bank, coder 1, legitimacy alone: missed: **8**
- run 19, value-change bank, coder 1, legitimacy alone: over: **1**
- run 19, value-change bank, coder 1, legitimacy alone: not settled: **36**
- run 19, value-change bank, coder 1, with forced as authority: cases: **90**
- run 19, value-change bank, coder 1, with forced as authority: settled: **60**
- run 19, value-change bank, coder 1, with forced as authority: agree: **47**
- run 19, value-change bank, coder 1, with forced as authority: missed: **8**
- run 19, value-change bank, coder 1, with forced as authority: over: **5**
- run 19, value-change bank, coder 1, with forced as authority: not settled: **30**
- run 19, value-change bank, coder 1, the source judges conduct, legitimacy alone: cases: **38**
- run 19, value-change bank, coder 1, the source judges conduct, legitimacy alone: settled: **22**
- run 19, value-change bank, coder 1, the source judges conduct, legitimacy alone: agree: **20**
- run 19, value-change bank, coder 1, the source judges conduct, legitimacy alone: missed: **1**
- run 19, value-change bank, coder 1, the source judges conduct, legitimacy alone: over: **1**
- run 19, value-change bank, coder 1, the source judges conduct, legitimacy alone: not settled: **16**
- run 19, value-change bank, coder 2, legitimacy alone: cases: **90**
- run 19, value-change bank, coder 2, legitimacy alone: settled: **60**
- run 19, value-change bank, coder 2, legitimacy alone: agree: **44**
- run 19, value-change bank, coder 2, legitimacy alone: missed: **11**
- run 19, value-change bank, coder 2, legitimacy alone: over: **5**
- run 19, value-change bank, coder 2, legitimacy alone: not settled: **30**
- run 19, value-change bank, coder 2, with forced as authority: cases: **90**
- run 19, value-change bank, coder 2, with forced as authority: settled: **66**
- run 19, value-change bank, coder 2, with forced as authority: agree: **48**
- run 19, value-change bank, coder 2, with forced as authority: missed: **11**
- run 19, value-change bank, coder 2, with forced as authority: over: **7**
- run 19, value-change bank, coder 2, with forced as authority: not settled: **24**
- run 19, value-change bank, coder 2, the source judges conduct, legitimacy alone: cases: **38**
- run 19, value-change bank, coder 2, the source judges conduct, legitimacy alone: settled: **25**
- run 19, value-change bank, coder 2, the source judges conduct, legitimacy alone: agree: **20**
- run 19, value-change bank, coder 2, the source judges conduct, legitimacy alone: missed: **2**
- run 19, value-change bank, coder 2, the source judges conduct, legitimacy alone: over: **3**
- run 19, value-change bank, coder 2, the source judges conduct, legitimacy alone: not settled: **13**
- run 19, value-change bank, the two coders: same verdict, legitimacy alone: **71**

The cases against the book and the sources:

- run 19, manipulation bank, coder 1, missed: `flick-triple-dog-dare`
- run 19, manipulation bank, coder 1, over: `teacher-feigns-excitement`, `trust-me`, `rigged-coin`, `gardener`, `trained-professor-buridan`
- run 19, manipulation bank, coder 1, over on hidden alone: `rigged-coin`, `gardener`, `trained-professor-buridan`
- run 19, manipulation bank, coder 2, missed: `irene-recommends`
- run 19, manipulation bank, coder 2, over: `teacher-feigns-excitement`, `smith-admitting-physician`, `trust-me`, `tide-priming`, `rigged-coin`, `gardener`, `trained-professor-buridan`, `ted-exposure-tiebreak`, `atmospherics-direct-tiebreak`, `roach-motel-outweighed`
- run 19, manipulation bank, coder 2, over on hidden alone: `tide-priming`, `rigged-coin`, `gardener`, `trained-professor-buridan`, `ted-exposure-tiebreak`, `atmospherics-direct-tiebreak`, `roach-motel-outweighed`
- run 19, value-change bank, coder 1, the source judges conduct, passes what the source faults: `N-akhlaghi-dissuading-from-parenthood`
- run 19, value-change bank, coder 1, the source judges conduct, fails what the source accepts: `N-buss-courtship`
- run 19, value-change bank, coder 2, the source judges conduct, passes what the source faults: `B-K2`, `N-akhlaghi-dissuading-from-parenthood`
- run 19, value-change bank, coder 2, the source judges conduct, fails what the source accepts: `B-C18`, `B-K13`, `N-buss-courtship`

**The pattern of the over-convictions.** Beside `teacher-feigns-excitement` and `trust-me`,
which both coders convict on *hidden* and *astray*, every case convicted against the book but
`smith-admitting-physician` is convicted on *hidden* alone. Five of those are cases where the
book holds that a tie of hers was broken and no mistake used: `rigged-coin`, `tide-priming`,
`ted-exposure-tiebreak`, `atmospherics-direct-tiebreak`, `trained-professor-buridan`. The
tie-breaking was concealed. So the statement is wider than the book's notion on concealed
tie-breaking and on concealed aims (`gardener`); tipping a tie openly is within it
(`Witness.w2_tips_an_even_choice` in `LegitimacyPlainTelling.lean`; case A12 of §3). The two
coders agree least on *hidden*.

Against the predictions, one of ten failed:

- run 19, prediction M1, coder 1, settles at least 85% of influencer cases and agrees with the book on at least 94% of those: **held**
- run 19, prediction M2, coder 1, at most 6 missed and at most 10 over: **held**
- run 19, prediction V1, coder 1, legitimacy alone settles at least 50% of the value-change bank and agrees with the sources on at least 78% of those: **held**
- run 19, prediction V2, coder 1, where the source judges conduct agrees on at least 80% of what it settles: **held**
- run 19, prediction M1, coder 2, settles at least 85% of influencer cases and agrees with the book on at least 94% of those: **held**
- run 19, prediction M2, coder 2, at most 6 missed and at most 10 over: **held**
- run 19, prediction V1, coder 2, legitimacy alone settles at least 50% of the value-change bank and agrees with the sources on at least 78% of those: **failed**
- run 19, prediction V2, coder 2, where the source judges conduct agrees on at least 80% of what it settles: **held**
- run 19, prediction M3, the two coders give the same verdict on at least 88% of cases: **held**
- run 19, prediction M4, where both settle and give the same verdict, at least 96% agree with the book: **held**

## 3. The adversarial test of the formal clauses (27 November)

Sixteen cases in prose (`adv/cases.json`), each built around a hole a review found or a
consequence the maintainer accepts. **They were written by the author of the account, and each
says what plain telling would have done.** The verdict the account is meant to give on each,
and the clause meant to fail, were fixed beforehand (`adv/key.json`) and kept from the coders.
Two coders (Claude Opus and Claude Sonnet, versions unrecorded, on the dispatching session's
record), told neither the clauses nor what the models were for, turned each case into a small
numerical model in a fixed format (`adv/SCHEMA.md`; `adv/encoded_1.json`,
`adv/encoded_2.json`): the matters, his views, her weighing, and for his conduct and each plain
telling her views, what she takes his views to be, and what she does. The checker, written
before either encoding existed, computes the three clauses from a model in exact arithmetic.

- adversarial test: cases: **16**
- adversarial test: cases the key fails: **8**
- adversarial test, coder 1: verdict matches the key: **16**
- adversarial test, coder 1: fails where the key fails: **8**
- adversarial test, coder 1: of those, the key's clause among the failing clauses: **8**
- adversarial test, coder 1: encodings ill formed or missing: **0**
- adversarial test, coder 2: verdict matches the key: **16**
- adversarial test, coder 2: fails where the key fails: **8**
- adversarial test, coder 2: of those, the key's clause among the failing clauses: **8**
- adversarial test, coder 2: encodings ill formed or missing: **0**
- adversarial test, the two coders: same verdict: **16**
- adversarial test, the two coders: same failing clauses: **16**
- adversarial test: cases that pass on both encodings with what she does worse by his views: **1**

- adversarial test, A1: key pass; coder 1 pass; coder 2 pass; worse by his views than under plain telling: no, no
- adversarial test, A2: key fail on open; coder 1 fail on open+beliefs; coder 2 fail on open+beliefs; worse by his views than under plain telling: yes, yes
- adversarial test, A3: key pass; coder 1 pass; coder 2 pass; worse by his views than under plain telling: no, no
- adversarial test, A4: key fail on open; coder 1 fail on open; coder 2 fail on open; worse by his views than under plain telling: no, no
- adversarial test, A5: key fail on beliefs; coder 1 fail on beliefs; coder 2 fail on beliefs; worse by his views than under plain telling: yes, yes
- adversarial test, A6: key pass; coder 1 pass; coder 2 pass; worse by his views than under plain telling: no, no
- adversarial test, A7: key fail on beliefs; coder 1 fail on beliefs; coder 2 fail on beliefs; worse by his views than under plain telling: no, no
- adversarial test, A8: key fail on beliefs; coder 1 fail on beliefs; coder 2 fail on beliefs; worse by his views than under plain telling: no, no
- adversarial test, A9: key pass; coder 1 pass; coder 2 pass; worse by his views than under plain telling: yes, yes
- adversarial test, A10: key fail on will; coder 1 fail on will; coder 2 fail on will; worse by his views than under plain telling: no, no
- adversarial test, A11: key pass; coder 1 pass; coder 2 pass; worse by his views than under plain telling: no, no
- adversarial test, A12: key pass; coder 1 pass; coder 2 pass; worse by his views than under plain telling: no, no
- adversarial test, A13: key fail on open; coder 1 fail on open+beliefs; coder 2 fail on open+beliefs; worse by his views than under plain telling: no, no
- adversarial test, A14: key pass; coder 1 pass; coder 2 pass; worse by his views than under plain telling: no, no
- adversarial test, A15: key pass; coder 1 pass; coder 2 pass; worse by his views than under plain telling: no, no
- adversarial test, A16: key fail on beliefs; coder 1 fail on beliefs; coder 2 fail on beliefs; worse by his views than under plain telling: yes, yes

- adversarial test, prediction P1, every encoding well formed and a verdict on all 16: **held**
- adversarial test, prediction P2, each coder matches the key on at least 13 of 16: **held**
- adversarial test, prediction P3, the coders agree with each other on at least 13 of 16: **held**
- adversarial test, prediction P4, the key's clause among the failing clauses in at least 80% of shared fails: **held**
- adversarial test, prediction P5, A3 or A16 is given different verdicts or clauses by the two coders: **failed**

On A9 the conduct passes and what she does is worse by his views than under plain telling:
the offsetting item of `gap`, from a case in prose.

**The smallest cases of the outside reviews**, written as models in this round by the hand
that wrote the record (`adv/review_cases.json`), on the present clauses. The runner fails if
one does not get the verdict recorded for it there:

- review case R18-same-act (review 18, answer 1): fail on will; worse by his views than under plain telling: yes
- review case R19-overshoot (review 19, answer 4): fail on open+beliefs; worse by his views than under plain telling: yes
- review case R19-course (review 19, answer 6): fail on will; worse by his views than under plain telling: yes
- review case R20-cancelling (review 20, answer 2): fail on beliefs; worse by his views than under plain telling: no
- review case R20-correcting-one (review 20, answer 1): pass; worse by his views than under plain telling: no
- review case R20-lie-seen-through (review 20, answer 4): pass; worse by his views than under plain telling: no

`R20-correcting-one` and `R20-lie-seen-through` pass: the first is what review 20 said should
pass, the second is structural fact 7 of `PLAIN_TELLING_STATEMENT.md`.

## 4. What these do not show

- **That the formal clauses give the right verdict on a case as it comes.** In §3 the cases
  say what plain telling would have done, and the encoders agree; a real case leaves that open,
  and that is where encoders would be expected to part. The prediction that the lie seen
  through or the mood would be encoded differently failed: neither was.
- **Anything about the formal clauses, in §1 and §2.** "More likely to act against her own
  judgement" is not `Will`'s comparison of shortfalls, and *astray* is asked of how she sees the
  matter as a whole, not matter by matter.
- **Independence.** Every coder and encoder is a language model; in run 18 each case has one
  coding; no person has read a case against its coding. The cases of §3, the key, the sheets
  and the statement are by one hand.
- **Coverage.** Each coding leaves about a tenth of the manipulation bank unsettled, and a
  third to two fifths of the value-change bank.
- **The value-change bank as a test of a conduct condition.** In 52 of its 90 cases the source
  judges something other than anyone's conduct.
- **That the bank was unseen.** It was not.
