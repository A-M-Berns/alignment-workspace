# Results — the case bank under the revised definition

Every figure is computed by `rerun/run.py` from `rerun/cases.py`. The lines beginning
`COUNT`, `WRONG` and `QUESTION` at the end are read back by the runner, which fails if
one differs from what it computes. The scenes are renderings: the sixth follow-up's
scene for each banked case with the details of `PREDICTIONS.md` added, and the verdicts
are facts about those scenes. "Right" means the computed answers match the evident
character recorded in `PREDICTIONS.md` before the code, which is the executor's.

## 1. The counts, beside the sixth follow-up's

Both definitions are scored against the same table of evident characters, on the three
questions. Five cases have no question settled and are not counted (NP1, NP2, K14, K24,
Q4).

| | right | wrong | wrong, strict table |
|---|---|---|---|
| revised, *start* | 98 | 5 | 5 |
| revised, *end* | 97 | 6 | 14 |
| revised, *learning* | 95 | 8 | 8 |
| sixth follow-up, *start* | 87 | 16 | 20 |
| sixth follow-up, *end* | 89 | 14 | 24 |
| sixth follow-up, adjusted, *start* | 92 | 11 | 15 |
| sixth follow-up, adjusted, *end* | 91 | 12 | 22 |

By question, cases right over cases the question is settled for. Seven cases (K15, K21,
K23, X1, X2b, X3b, D1) ask only that manipulation or another wrong hold, and are in
their own column.

| | manipulation | covered | another wrong | manipulation or another wrong |
|---|---|---|---|---|
| revised, *start* | 85/90 | 3/3 | 89/89 | 7/7 |
| revised, *end* | 84/90 | 3/3 | 89/89 | 7/7 |
| revised, *learning* | 82/90 | 3/3 | 89/89 | 7/7 |
| sixth follow-up, *start* | 78/90 | 0/3 | 86/89 | 6/7 |
| sixth follow-up, *end* | 80/90 | 0/3 | 89/89 | 6/7 |

The sixth follow-up's own count, 76 of 96 under *start*, was on its standard, which
counted a case routed to coercion or alteration apart from the right ones. Its
definition had no covered column, and under *start* it gave K17, K19 and L14 no verdict;
the unadjusted rows count both against it. The adjusted rows answer "none" for a case
with no adviser and credit Q6 and Q7, whose rows state the permission, as covered: what
is left is the difference in classification (the external review's point 16).

The strict table (`PREDICTIONS.md`) asks that taste-shaping, the camp, the drug, a lie
she allows for and dependence be manipulation and not merely another wrong; it moves the
revised definition under *end* from 6 wrong to 14 and the others little. The covered
question is settled for three cases, all positive. Four banked cases are right on
*another wrong* alone, manipulation being contested: NP5, NP14, Q10, K31.

**The evident characters are the executor's, and three of them move the count** (the
external review's point 15). With NP13's manipulation contested and not "yes": 4, 5, 7
wrong. With Q10 (an honest adviser picks the option she overrates) required to be
manipulation: 6, 7, 9. With K31 (a lie she allows for) required to be manipulation: 6,
7, 9.

## 2. The wrong cases

| case | computed | why |
|---|---|---|
| K13 buried information | none | she ends at the prior, calibrated; she is less informed, which is no shortfall. Manipulation when only the bad news is buried (W21) |
| K2 a lie that leaves her better off | none | clause 1 holds in belief; clause 2 is unanswered, because every other conduct listed leaves her valuation of treatment worse than the lie does |
| Q3 a lie that offsets a bias | none | her one counted estimate improves |
| Q3b the same, the reading counted | none | clause 1 holds for the reading; the truthful report leaves the outside quantity worse than the lie does |
| NP13 feigned excitement | none | as K2: plain teaching leaves her estimate of the material's worth short |
| K29 every end revised in turn, *end* only | none, no other wrong | her rating at the end is her utility at the end; the scene has no alteration |
| K22, L10, L15 changes she asked for, *learning* only | manipulation in valuation, covered | a change that is not learning leaves her rating above her utility under this candidate |

K2, Q3b and NP13 are one pattern: **a lie that is the only listed way to keep another
faculty right is not manipulation**, because the truthful conduct "leaves another
counted faculty worse than the actual conduct does". Each turns on a detail its row does
not fix (§7).

## 3. What changed from the sixth follow-up, and why

Under *start*, twelve cases the sixth follow-up had wrong are right, and one it had
right is wrong.

| cases | now | by what |
|---|---|---|
| N8b, Q11 pressure and a cue from a policy the same toward everyone | manipulation in action, not "intentional" | the basic notion compares with no act, not with the conduct toward another type. The definition, on the sixth's scene |
| K9, Q2 an undisclosed advocate, strategic silence | manipulation in belief | clause 2 ranges over every available conduct, the forthright report among them; the sixth compared with a truthful counterpart that was the same conduct. The definition, together with the added detail that she was calibrated before: K9 is acquitted when she started out worse (W10) |
| Q6, Q7 a magician, a bluff | manipulation, covered | a column the sixth's definition did not have; its verdict of manipulation is unchanged |
| Q5 a surprise party | manipulation, covered | the same column, and the added detail that a practice covers it |
| K17, K19, L14 changes nobody caused | none | with no adviser no verdict needs her utility; the sixth's model stopped at "unfixed" |
| X3 a narrowing feed | manipulation in belief | the added detail that she was right before, and a one-state scene in which showing no feed cannot leave her less informed |
| D1 dependence | manipulation in forecast | the forecast faculty, with the added details that she does not foresee the decay and that telling her works. Neither follows from the row |
| NP13 feigned excitement | none (was manipulation) | clause 2's condition on other faculties, on a tradeoff already in the sixth's scene |

So: four repairs are a difference in classification on the sixth's scene (N8b, Q11) or
on that scene with a baseline added (K9, Q2); five are a column or a verdict the sixth's
definition did not produce (Q6, Q7, K17, K19, L14); three rest on added details (Q5, X3,
D1). Against the adjusted sixth, the revised definition repairs seven (K9, Q2, N8b, Q11,
Q5, X3, D1) and loses one (NP13). K13, K2, Q3 and Q3b are wrong under both.

## 4. The review's four honest scenes

R1–R4 are not manipulation under any candidate. In R1–R3 clause 1 holds and clause 2 is
unanswered: saying nothing would leave her less informed, and the scene lists no better
telling. In R4 clause 1 fails on the calibrated expectation: reminded, her expected
regret is 1/10 against 1/2. Under the any-conduct variant R1–R3 are manipulation. With
a less confusing lesson listed as available, R1 is manipulation (W17), and not
"intentional", the twin being taught the same.

## 5. The new scenes

| # | scene | evident | computed | |
|---|---|---|---|---|
| W1 | fails to correct a mistake she already had | no | none | right |
| W2 | a hard truth that cannot be told another way | no | none; manipulation under any-conduct | right |
| W3 | a hard truth told bluntly, a gentle telling available | no | manipulation in emotion, 1/8 | **wrong** |
| W4 | a clumsy honest explanation, the best the adviser can give | no | none | right |
| W5 | a clumsy honest explanation, a clear one available | no | manipulation in belief, 1/4 | **wrong** |
| W6 | the truth told to a known contrarian | contested | manipulation in belief, 1 | not counted on manipulation |
| W7 | a falsehood told to her | contested | none | not counted on manipulation |
| W8 | the truth, the adviser taking her for ordinary | no | none; she is in fact left worse | right |
| W9 | a falsehood, the adviser taking her for ordinary | contested | manipulation in belief, "intentional"; she in fact ends right | not counted on manipulation |
| W10 | an undisclosed advocate, she holding 0 until shown something | yes | none: 1/12 after against 1/4 before | **wrong** |
| W11 | a cruel lie about a matter no decision depends on | yes | none; manipulation if every quantity is counted | **wrong** |
| W12 | the same lie, a later decision depending on it | yes | manipulation in belief, "intentional" | right |
| W13 | an honest disclosure after which she distrusts the adviser | no | manipulation in the reliability of a rule, 1/4 | **wrong** |
| W14 | the same, the commission bearing on a decision | no | none | right |
| W15 | a cue, the adviser knowing she craves | yes | manipulation in action | right |
| W16 | the same conduct, the adviser taking her for ordinary | no | none; she is in fact left worse | right |
| W17 | a remedial lesson, a less confusing one available | no | manipulation in belief; not "intentional" | **wrong** |
| W18 | a requested reminder sent knowing it will backfire | no | manipulation in action, covered; not "intentional" | **wrong** |
| W19 | dependence she foresees | no | none | right |
| W20 | dependence she does not foresee | objectionable | manipulation in forecast | right |
| W21 | bad news buried, good news shown | yes | manipulation in belief | right |
| W22 | a lie that leaves her better off, the adviser able to explain | yes | manipulation in belief, "intentional" | right |
| W23 | the truth told to a population one in ten contrarian | no | none; manipulation under any-conduct | right |
| W24 | she tries something at a suggestion and likes it, unendorsed | no | manipulation in valuation under *start*; none under *end*, *learning* | **wrong** under *start* |
| W25 | unasked exposure her starting values endorse | contested | alteration; under *learning* also manipulation in valuation | not counted |

Eight wrong under *start*, seven under *end* and *learning*, of 24 counted. Every one was
predicted wrong before the code. They are four patterns:

- **A better conduct was available** (W3, W5, W17, and W18 with her request). The
  definition reads no intention, so an honest adviser who tells bluntly, explains
  clumsily or teaches confusingly where the scene lists a better way manipulates her.
  Where the scene lists none it does not (W2, W4, R1).
- **A baseline already wrong** (W10). An undisclosed advocate leaves her better
  calibrated than the habit she started with, so clause 1 fails.
- **The restriction to what bears on a decision** (W11, W13). It acquits a cruel lie
  about an idle matter, and it convicts an honest disclosure whose content is idle while
  her distrust is not.
- **The candidate** (W24): under *start*, a suggestion she follows and learns from is
  manipulation when her starting values do not endorse where it leads.

## 6. Variants

- **Any-conduct clause 2.** Adds as manipulation K25 (a sincere adviser who is wrong),
  K27b (a hard truth that leaves her wrong on average), R1–R3, W2, W4, W14, W23; removes
  nothing. Each is honest conduct whose only better alternative is to say nothing.
- **"No less informed" at her estimate** in place of at what she observes: adds K27b
  and W4. There she makes nothing of what she is told, so her estimate is as uninformed
  as under silence, and silence then answers clause 2.
- **The answering conduct must return the faculty to its shortfall before**: no verdict
  changes in any banked or new scene. The readings do differ: where the only better
  conduct repairs part of the damage, the graded reading convicts and this one acquits
  (the external review's scene A4, §11).
- **One faculty per kind**: no verdict changes in any scene with the quantities in the
  units written; see §8.
- **Every quantity counted**: W11 becomes manipulation; nothing else changes.

## 7. Verdicts that turn on a detail the row does not fix

Each line changes one added detail of a banked case and gives manipulation under
*start*; the bank's verdict is in brackets.

| case | detail changed | computed |
|---|---|---|
| K9 | before she holds 0, the estimate she gives when shown nothing | none [belief] |
| K2 | the adviser knows treatment pays either way and could say so | belief [none] |
| NP13 | told the reason, she takes the material at its worth | belief [none] |
| Q3b | told of her bias she drops it | belief [none] |
| K31 | the adviser takes her for an ordinary advisee, who believes it | belief, though she is not misled [none] |
| Q12 | the fact bears on a decision of hers and cannot be told another way | none [emotion] |
| Q8 | she was calibrated before, and saying nothing is available | belief [none] |
| D1 | she foresees the decay | none [forecast] |
| K13 | only bad news is buried | belief [none] |
| Q5 | no practice covers it | belief, not covered [belief, covered] |
| X3 | telling her is not available; showing no feed is | belief [belief] |

Ten of the eleven change the verdict. Nine of those change one detail. The Q8 line
changes two (her state before, and whether saying nothing is available), and neither
alone changes the verdict; the Q12 line replaces the one-state scene with a two-state
one. The details are of four sorts: her state before; her response to a conduct the
adviser did not choose, `tell` above all; what the adviser knows of her; whether a fact
bears on a decision.

## 8. Well-definedness

- **Units.** Rescaling one quantity by a constant multiplies its shortfall under every
  conduct and before by the constant squared; every comparison in the definition is
  within one quantity; no verdict moves (checked on every scene, three factors per
  quantity). The degree is in the square of the quantity's units and is not comparable
  across faculties.
- **Re-expression by a map that is not affine** moves verdicts. With `X` equal to 1/2
  three times in four and otherwise 1 with probability 3/4, an adviser that sends the
  coarse signal where it could have sent `X` leaves her estimate of `X` calibrated
  before and after: no manipulation. With the quantity written as `X²` and her estimate
  its square, the shortfall is 225/65536 before and 9/1024 after, the full report
  answers clause 2, and the same conduct is manipulation. Calibration of a mean is not
  preserved by squaring, so which parametrization a quantity is "really" in is a datum.
- **Relabelling.** Which kind a quantity is tagged with changes nothing: the kind is a
  label. Merging the quantities of one kind into one faculty changes no verdict in the
  scenes as written, and makes verdicts depend on units: Q3b becomes manipulation with
  the reading in units half the size, or the outside quantity in units three times the
  size.
- **"No less informed" is a surrogate.** The expected variance of each counted target
  given what she observes does not see information about how targets are related: for
  two independent binary targets, being shown their parity and being shown nothing leave
  each variance at 1/4 (the external review's point 14; not computed here). Listing the
  parity as a quantity repairs it and makes the list of quantities decide.
- **Confidence.** Conditioning on an estimate together with its stated confidence can
  convict where the value alone does not (the review's scene A8, §11). §1 does not say
  what a confidence asserts.
- **Which decisions she could face.** Read from the scene, the restriction decides W11
  and W13 against W14. Read as any decision that can be described, every quantity is
  counted and the restriction does nothing.
- **Clause 2.** Of the bank's 86 scenes with an adviser, clause 1 holds in some faculty
  in 50, and clause 2 is unanswered in 5 of those (K2, NP13, Q3b, K25, K27b). It cannot
  be answered in a scene listing one conduct (9 scenes, none with clause 1). In a scene
  with one state nothing is withheld by doing nothing, so there clause 2 is "worse than
  doing nothing". It is never satisfied by honest conduct that reveals everything the
  adviser knows unless the scene lists a telling she reads better.

## 9. The three candidates

Fourteen scenes get different verdicts under the candidates: NP8, E6, K15, K21, K23,
K29, X1, X2b, X3b, K22, L10, L15 in the bank, W24 and W25 among the new. All are scenes
with an adviser in which what she values changes. In nine more, with no adviser, only
her own shortfall differs (E1, E3, E4, K17, K19, K20, K24, L13, L14); for K17, K19, K24
and L14 the *start* shortfall is not fixed by the row.

| | *start* | *end* | *learning* |
|---|---|---|---|
| taste shaped without her say (NP8, E6, K15, K21, K23, K29, X1, X2b, X3b) | manipulation in valuation | none | manipulation in valuation |
| a change she asked for (K22, L10, L15) | none | none | manipulation in valuation, covered |
| a suggestion she learns from, unendorsed (W24) | manipulation in valuation | none | none |
| unasked exposure she endorses (W25) | none | none | manipulation in valuation |

*Learning* decides otherwise than both of the others in K22, L10, L15 and W25. In every
scene, as rendered here with a two-valued utility of what she ends with, its verdict is
fixed by the annotation and one scene fact: annotated learning, it
is *end*'s; annotated not, it is what *start* gives for a trajectory she does not
endorse. For K15, X1, L10 and K29 the annotation is not settled by the row. No candidate
is right on all of K29, W24 and K22: *start* misses W24, *end* misses K29 (and, on the
strict table, every taste case), *learning* misses K22, L10 and L15.

## 10. "Intentional"

Computed for every case and not scored. It holds where manipulation does and the scene
gives a different conduct toward the twin: the responsive pressures and cues, taste
shaped for her in particular, and the lies, for which the bank's rows do not say what
the adviser does toward one who would not believe it; the added detail is that it does
not lie. It does not hold for the undisclosed advocate, strategic silence, the feed,
blanket pressure, dependence, or any of the honest scenes the definition convicts (W3,
W5, W13, W17, W18). In no scene is honest conduct "intentional" manipulation.

## 11. Six of the external review's scenes

The review wrote ten scenes before reading the work (`REVIEW-astra-followup-7.md`,
points 2–11). Six are reproduced by the runner as it states them; three of the others
are W6, W11 and the re-expression example of §8 in other numbers, and the tenth is W23's
pattern with the actual recipient helped.

| | scene | computed | |
|---|---|---|---|
| A1 | a lie repeated to one who already believes it; telling her would correct it | none: her shortfall was 1 before and is 1 after | maintaining a deception is not seen; "before" is the moment before this conduct |
| A2 | an honest slip that moves a right estimate to 1/2; a checked explanation was available | manipulation in belief, 1/4 | ordinary imperfect advising, convicted |
| A4 | the conduct takes her estimate from 0 to 1; telling her would leave 1/2 | manipulation in belief, 3/4, "intentional"; none if the answering conduct must return her to before | the two readings of clause 2 differ |
| A5 | the conduct makes her certain of one falsehood; every other conduct makes her certain of another | none | clause 2's condition on other faculties acquits a choice between two deceptions |
| A8 | her estimate is 1/2 either way, with a confidence that tracks the truth | manipulation in belief, 1/4; none if confidence is ignored | the conditioning on confidence decides |
| A9 | complying is made better and refusing worse; she complies, rightly | no other wrong: the most she can attain rises | the test for coercion by the most attainable misses a threat joined to an offer |

## What was not shown

- **The count is consistency with renderings and with evident characters the executor
  wrote.** Each scene is a few numbers; §7 shows ten verdicts changing with a detail, and
  §1 shows three evident characters moving the count.
- **"Available" is a list.** No scene derives what the adviser could have done. `tell`
  is listed in 12 of the 115 scenes with an adviser and `none` not in all; a conduct
  not listed is not available in that scene. Every conviction of honest conduct, and
  every acquittal by clause 2, is a fact about the list.
- **Four cases with no adviser** (K5, K6, K26, K30) carry the sixth follow-up's scene
  for her own shortfall; E5, K18 and L17 are empty scenes.
- **The pooled calibration** of §3.4's alternative, and the adviser's own law of
  §3.1's, were not computed.
- **No sequential scene.** K4c, K21 and D1 are single-step renderings; "before" in a
  scene where the adviser has already acted is tested only by the review's A1.
- **Coercion** is tested by the most she can attain, which misses A9; the dispatch's
  words, "changing what her moves lead to in order to obtain compliance", were not
  given another reading.
- **Nothing here bears on the post's theorems.**

## Machine-checked lines

```
COUNT start primary: right 98, wrong 5, not counted 5
WRONG start primary: K13 K2 NP13 Q3 Q3b
COUNT start strict: right 98, wrong 5, not counted 5
WRONG start strict: K13 K2 K31 Q3 Q3b
COUNT end primary: right 97, wrong 6, not counted 5
WRONG end primary: K13 K2 K29 NP13 Q3 Q3b
COUNT end strict: right 89, wrong 14, not counted 5
WRONG end strict: E6 K13 K15 K2 K21 K23 K29 K31 NP8 Q3 Q3b X1 X2b X3b
COUNT learning primary: right 95, wrong 8, not counted 5
WRONG learning primary: K13 K2 K22 L10 L15 NP13 Q3 Q3b
COUNT learning strict: right 95, wrong 8, not counted 5
WRONG learning strict: K13 K2 K22 K31 L10 L15 Q3 Q3b
COUNT review-start primary: right 4, wrong 0, not counted 0
WRONG review-start primary: 
COUNT review-start strict: right 4, wrong 0, not counted 0
WRONG review-start strict: 
COUNT review-end primary: right 4, wrong 0, not counted 0
WRONG review-end primary: 
COUNT review-end strict: right 4, wrong 0, not counted 0
WRONG review-end strict: 
COUNT review-learning primary: right 4, wrong 0, not counted 0
WRONG review-learning primary: 
COUNT review-learning strict: right 4, wrong 0, not counted 0
WRONG review-learning strict: 
COUNT new-start primary: right 16, wrong 8, not counted 1
WRONG new-start primary: W10 W11 W13 W17 W18 W24 W3 W5
COUNT new-start strict: right 16, wrong 8, not counted 1
WRONG new-start strict: W10 W11 W13 W17 W18 W24 W3 W5
COUNT new-end primary: right 17, wrong 7, not counted 1
WRONG new-end primary: W10 W11 W13 W17 W18 W3 W5
COUNT new-end strict: right 17, wrong 7, not counted 1
WRONG new-end strict: W10 W11 W13 W17 W18 W3 W5
COUNT new-learning primary: right 17, wrong 7, not counted 1
WRONG new-learning primary: W10 W11 W13 W17 W18 W3 W5
COUNT new-learning strict: right 17, wrong 7, not counted 1
WRONG new-learning strict: W10 W11 W13 W17 W18 W3 W5
COUNT sixth-start primary: right 87, wrong 16, not counted 5
WRONG sixth-start primary: D1 K13 K17 K19 K2 K9 L14 N8b Q11 Q2 Q3 Q3b Q5 Q6 Q7 X3
COUNT sixth-start strict: right 83, wrong 20, not counted 5
WRONG sixth-start strict: D1 E6 K13 K17 K19 K2 K31 K9 L14 N8b NP13 Q11 Q2 Q3 Q3b Q5 Q6 Q7 X3 X3b
COUNT sixth-end primary: right 89, wrong 14, not counted 5
WRONG sixth-end primary: D1 K13 K2 K29 K9 N8b Q11 Q2 Q3 Q3b Q5 Q6 Q7 X3
COUNT sixth-end strict: right 79, wrong 24, not counted 5
WRONG sixth-end strict: D1 E6 K13 K15 K2 K21 K23 K29 K31 K9 N8b NP13 NP8 Q11 Q2 Q3 Q3b Q5 Q6 Q7 X1 X2b X3 X3b
COUNT sixth-adjusted-start primary: right 92, wrong 11, not counted 5
WRONG sixth-adjusted-start primary: D1 K13 K2 K9 N8b Q11 Q2 Q3 Q3b Q5 X3
COUNT sixth-adjusted-start strict: right 88, wrong 15, not counted 5
WRONG sixth-adjusted-start strict: D1 E6 K13 K2 K31 K9 N8b NP13 Q11 Q2 Q3 Q3b Q5 X3 X3b
COUNT sixth-adjusted-end primary: right 91, wrong 12, not counted 5
WRONG sixth-adjusted-end primary: D1 K13 K2 K29 K9 N8b Q11 Q2 Q3 Q3b Q5 X3
COUNT sixth-adjusted-end strict: right 81, wrong 22, not counted 5
WRONG sixth-adjusted-end strict: D1 E6 K13 K15 K2 K21 K23 K29 K31 K9 N8b NP13 NP8 Q11 Q2 Q3 Q3b Q5 X1 X2b X3 X3b
QUESTION start: M 85/90, C 3/3, W 89/89, M or W 7/7
QUESTION end: M 84/90, C 3/3, W 89/89, M or W 7/7
QUESTION learning: M 82/90, C 3/3, W 89/89, M or W 7/7
QUESTION review-start: M 4/4, C 0/0, W 4/4, M or W 0/0
QUESTION review-end: M 4/4, C 0/0, W 4/4, M or W 0/0
QUESTION review-learning: M 4/4, C 0/0, W 4/4, M or W 0/0
QUESTION new-start: M 12/20, C 0/0, W 23/23, M or W 1/1
QUESTION new-end: M 13/20, C 0/0, W 23/23, M or W 1/1
QUESTION new-learning: M 13/20, C 0/0, W 23/23, M or W 1/1
QUESTION sixth-start: M 78/90, C 0/3, W 86/89, M or W 6/7
QUESTION sixth-end: M 80/90, C 0/3, W 89/89, M or W 6/7
```
