# Two blind runs on the literature's cases of value change

The fifty-two cases are those of `LIT_CASES.md` Part A, given to each reader as case texts
without verdicts. Two fresh Claude readers, one per run, each coded all fifty-two against
one formulation and nothing else of this round.

- **First run.** `VC_FORMULATION.md`: the account of `MISTAKES_ACCOUNT.md` in words, with an
  unasked shift in her valuing as the third kind of gain. Coding: `vc_coded.json`.
- **Second run.** `VC_FORMULATION_B.md`: a variant with two tests. An unauthorised change in
  what she values is a violation of her authority whether or not the adviser gains
  (authorised: she validly asked; or it is open and she can stop it; or it is trifling);
  separately, exploitation is taking gain through a mistake, her not knowing or an unasked
  change that the adviser could have done without. Coding: `vc_coded_B.json`.

`value_runs.py` scores both against the sets `LIT_CASES.md` fixed before anything was
classified: five cases whose source calls the act acceptable and fourteen whose source
faults it. A coding agrees with an acceptable source when its verdict is *legitimate* and
with a faulting one when it is *illegitimate*, *violation* or *exploitation*.

| | the source | first run | | second run | |
|---|---|---|---|---|---|
| P1 | acceptable | legitimate | agrees | legitimate | agrees |
| P3n | acceptable | legitimate | agrees | violation | contradicts |
| K13 | acceptable | legitimate | agrees | silent | silent |
| K14 | acceptable | depends | depends | depends | depends |
| N3 | acceptable | legitimate | agrees | exploitation | contradicts |
| P3 | faulted | illegitimate | agrees | violation | agrees |
| P4 | faulted | illegitimate | agrees | violation | agrees |
| P5 | faulted | depends | depends | violation | agrees |
| P5n | faulted | illegitimate | agrees | violation | agrees |
| P6 | faulted | illegitimate | agrees | violation | agrees |
| K2 | faulted | silent | silent | violation | agrees |
| K4 | faulted | illegitimate | agrees | violation | agrees |
| K12 | faulted | illegitimate | agrees | violation | agrees |
| K26 | faulted | depends | depends | violation | agrees |
| C1 | faulted | illegitimate | agrees | violation | agrees |
| C2 | faulted | depends | depends | depends | depends |
| C3 | faulted | depends | depends | exploitation | agrees |
| N1 | faulted | depends | depends | depends | depends |
| N2 | faulted | illegitimate | agrees | exploitation | agrees |

- adviser acts, first run: **34**
- adviser acts, second run: **33**
- first run, source acceptable, agrees: **4**
- first run, source acceptable, contradicts: **0**
- first run, source acceptable, depends: **1**
- first run, source faulted, agrees: **8**
- first run, source faulted, contradicts: **0**
- first run, source faulted, depends: **5**
- first run, source faulted, silent: **1**
- second run, source acceptable, agrees: **1**
- second run, source acceptable, contradicts: **2**
- second run, source acceptable, depends: **1**
- second run, source acceptable, silent: **1**
- second run, source faulted, agrees: **12**
- second run, source faulted, contradicts: **0**
- second run, source faulted, depends: **2**

**First run.** 12 of 19 agree and none contradicts. Its seven without a verdict either way:
K14, P5, K26, C2, C3 and N1 *depend* on a fact the story does not give (whether the adviser
knows, gains, or chooses the description to steer), and K2 is *silent*, the cause being a
diffuse society with no objective to measure gain against. The formulation reaches a
faulted case only where an objective of the adviser's is stated or inferred.

**Second run.** 12 of 14 faulted cases agree, and of the five the sources accept one
agrees and two contradict: P3n, where the source's own test passes a nudge whose result he
foresees and would welcome, is a violation because he did not ask; N3, an advertiser making
a brand familiar, passes the first test as trifling and fails the second, which counts gain
through any unasked change. Eleven of the twelve agreements are *violation*: the first test
decides nearly everything, and decides it by whether she asked.

Both readers count H3, where doctors inform the parents, as a case in which an adviser
acts; `LIT_CASES.md` does not, and the second reader does not count K25.

On the two cases `LIT_CASES.md` sets apart, P2 (conditional) is *illegitimate* in the first run and
*exploitation* in the second; C4 (marked hard to assess) is *depends* and *violation*.

**What the runs can show.** That the account's value-change part, applied in words by one
reader, contradicts no source verdict on the nineteen and is undecided on seven; and that
treating an unauthorised change as a violation decides more of the faulted cases at the
cost of two acceptable ones. **What they cannot.** Each run is one reader's single coding;
the two runs had different readers, so a difference between them is not only a difference
between formulations. The source verdicts are the sources' own and, for two of the
nineteen, the eighth pass's record. The case texts are this round's paraphrases. The second
formulation has no clause for a change she knowingly brings on herself, and applies the
trifling exemption in its first test only; a run with both is item 149. No person has
checked a coding.
