# Legitimacy and manipulation: where the line stands (2026-11-24)

A checkpoint. The line aims at a formalism with defensible modelling choices that says
intuitively correct things about manipulation, following Noggle, and proves safety theorems
for the corrigibility design. It is not at that bar. The statement of legitimacy as it stands
is `account/LEGITIMACY_STATEMENT.md`; the standing of each of its parts, with the evidence and
what would move it, is `account/LEDGER.md`, and §3 below is a guide to the two. Paths are
relative to this directory; Lean files are under `lean/Workspace/Deference/Contrib/`. Every
Lean result named is kernel-checked. Those of §1 are registered `lean-proved` in
`projects/normativity/CLAIMS.md` under the id beside each; those of §3 are not registered. A
result is what its declaration states and no more.

## 1. Solid

1. **The idea.** An adviser manipulates when it tries to influence her by getting her to
   make a mistake (Noggle's Mistake Account; his definition is kept as the definition). The
   faculties she decides with are treated as estimators, so a mistake is measurable;
   emotions and attention are treated as appraisals. This is a modelling choice and nothing
   proves it right. Whether a state of hers is a mistake is judged by the adviser's lights
   (§3); the measures of item 2 compare her with what her observations support and are
   measures of her condition, not the test of his conduct.
2. **Two measures of her state.** Trickery: how far her estimate is from what her
   observations support (`AppraisalAccount.valuationError`: her `miscalibration` given the
   estimate's own value, plus her unused information). Pressure: how
   far the act she takes falls short of the one she rates highest
   (`AppraisalAccount.regret`). They measure her condition, not the adviser's
   responsibility for it. Pressure so measured does not see an adviser that decides which
   of two options she rates the same she takes.
3. **Results about them**, in `AppraisalAccount.lean`, on a finite space: the split of her
   squared error (`mse_split`, `appraisal.mse-split`; `strong_split`,
   `appraisal.strong-split`); what she attains as the best attainable less what she cannot
   know less what her choice loses (`three_channels`, `appraisal.three-channels`); the
   bound on what her choice loses, with her miscalibration taken given everything she
   observed (`misuse_le`, `appraisal.cost-of-mistakes`; it fails at the two weaker
   strengths, `account/RESULTS.md` result 3); the deferring identity (`deferring_identity`,
   `appraisal.deferring`); the guarantee, with the options condition a hypothesis
   (`guarantee`, `appraisal.guarantee`; `options_of_hull`, `appraisal.options-hull`).
4. **Distinctions kept**, as vocabulary (`PROMPT-followup-13.md` §2 in the prompts
   directory; `account/AGENDA.md` §4). Her condition, and the adviser's responsibility for
   it. Three wrongs of conduct: manipulation, non-disclosure, value interference;
   withholding is not manipulation, and destroying her options or her information is a
   further wrong outside all three. What happened, and what an audit detects (`C` and `D`
   in `ScoringTheorem.Audit`). An attempt, and a success. Legitimate and sound: a history
   is legitimate by a condition on the adviser's conduct alone, which is what authorisation
   needs, and can contain her mistakes; her judgment is sound when in addition she
   reasoned correctly, which is what using her evaluation as a measure of her welfare
   needs. The condition proposed for legitimacy is in §3. Lean has a gate predicate (`AccountJoin.Gate.Legit`) and a quantitative
   soundness predicate (`SoundModel.Sound`); nothing establishes that either captures these
   distinctions, and in the scoring theorem a wrong and its detection are data.
5. **Her evaluation comes apart from her true utility in three ways**, each with an
   instance: she misreads what she has, with no wrong done (I2, an honest slip; I4,
   selection; `account/DERIVATION.md`); the adviser knows something relevant that its
   record does not carry, where the wrong is non-disclosure and not manipulation (I3); her
   valuing is not what it would have been (`Witness.d2a_needed`, read as a welcome change
   she did not ask for; the reading is an interpretation). That
   the welfare bound needs the first and third is in Lean (`Witness.d1a_needed`,
   `d2a_needed`); I2–I4 are exact instances in Python.
6. **The scoring theorem**, in `ScoringTheorem.lean` (`account/SCORING.md` reads it). One
   audited decision, expected scores. Hypotheses: her audited evaluation does not run above
   what she would say shown everything, and that not above her verdict with her valuing
   unshaped, at the course taken (D1a, D2a), with the reverse at an honest course (D1b,
   D2b); a conduct audit with few false flags and some power (D3); independent sampling
   (D4); an honest course available (D5); an adviser within a tolerance of the best
   expected score (D6). Then: a bound on her expected true utility (`Audit.welfare_bound`,
   `scoring.welfare-bound`); a bound on the chance she is wronged (`Audit.conduct_bound`,
   `scoring.conduct-bound`), which uses neither D1a nor D2a; a bound on expected *detected*
   violations of her authority (`Audit.authority_bound`, `scoring.authority-bound`), which
   uses neither those nor detection; and, where the penalty times the detection rate is at
   least one, a course's expected score is at most its audited evaluation on the histories
   without a wrong (`Audit.no_credit`, `scoring.no-credit`). Whether she was wronged,
   whether an audit would flag it, and her verdicts are data: the theorem does not define
   them. D6 compares actual expected scores and has no object for what the adviser
   believes. Nothing is said at the realised history, over more than one decision, or
   about undetected violations; the penalty is finite, so authority has no strict priority.
7. **The process theorem**, in `ThinLegitimacy.lean`, from the round
   `2026-10-01-thin-legitimacy-and-effective-authority`: coherence, authorship and
   transparency give a correct credence (`correct_of_coherent_authorship_transparent`), one
   direction. From it, if her evaluation is her credence's expectation of a fixed
   function of the world, the evaluation is unbiased for that function under her prior and
   the actual process (`ScoringTheorem.eval_unbiased_of_process`). That gives the scoring
   theorem's first assumption only where her prior is the law of the world and the
   adviser's record carries what it knows.
8. **The join to the post**, in `AccountJoin.lean` (`account/BRIDGE_LEAN.md` reads it). The
   post's Theorems 1 and 3 hold for any legitimacy predicate and any evaluation in the
   ranges the post asks, so they hold for a gate built from the account's components, the
   ranges being fields of the gate (`Gate.theorem1_join`, `Gate.theorem3_join`). Theorem 3's
   maximisation, feedback and alternative hypotheses stay hypotheses; Theorem 2 is not
   instantiated. The gate's conditions are inputs: a gate on which every history is
   legitimate satisfies every theorem (`Witness.blind`). The join does not model the
   inducing test, her counterfactual later self, or line 3 at every moment; it has no
   statement that worsening her options lowers her evaluation or that overriding her choice
   between options she rates the same is a violation; and nothing relates its predicate to
   `Legitimacy.Segment`.
   Registered beside it: what deferring to her verdict costs (`deferring_cost_le`,
   `appraisal.deferring-cost`); the guarantee from soundness, under a hypothesis linking
   what she observes to what the adviser knows (`guarantee_of_given`,
   `appraisal.guarantee-from-soundness`); when the post's feedback hypothesis transfers
   (`unbiased_of_feedback`, `corrigibility.feedback-transfer`); and the range of the third
   line of the statement of 2026-11-17 (`ValueChange.line3Old_le_line3`,
   `legitimacy.line3-range`), a fact about a quantity of a statement that failed its test, unconnected to the
   gate's own `line3` field. The deferring and guarantee bounds are expectations in her true
   utility, not statements at the realised history, and `SoundModel` gets its bound by
   defining soundness as the error bound.

## 2. Tried and not kept

Each row is a statement of the account, the pass that tested it, and what it failed on.
Each document of a row carries a status line at its top. Statements that no code reads are
under `earlier-attempts/`, in their old layout; banks, results and code stay where the
runner reads them.

| statement | pass | what it failed on | where |
|---|---|---|---|
| channel confinement, factorization, access, ownership (L0–L3 ∧ W) | first | matched its own bank; a plain lie passes it; set aside by the ruling of 2026-11-11 | `CASE_BANK.md` |
| the steering account | follow-up of 2026-11-10 | restates published notions; its stricter standard convicts honest advisers who differ, and an offer | `steering/` |
| the purpose-first account | follow-up of 2026-11-11 | trust can be manufactured and the gate gains; a threat fails no clause; verdicts follow the allowed set a case is given | `earlier-attempts/teleology/ACCOUNT.md`, `teleology/` |
| purposes pursued through parts | third | the constraints do not fix purposes; a lie widens no gap where she was already wrong | `earlier-attempts/decomposition/`, `decomposition/` |
| candidates weighted by explanatory quality | fourth | weight goes to candidates that give her judging part no purpose; a lie told at every aim passes | `earlier-attempts/scored/ACCOUNT.md`, `scored/` |
| a part as a mechanism and a purpose | fifth | a chain of steps each in range carries her from her best outcome to her worst; adds permission and attribution, no protection | `earlier-attempts/blocks/SETTING.md`, `blocks/` |
| manipulation as induced miscalibration | sixth | wrong on fourteen or fifteen of about a hundred cases; convicts honest help | `earlier-attempts/estimates/`, `estimates/` |
| worse than before, and avoidably | seventh | convicts honest conduct that leaves her worse; acquits a lie that keeps another estimate right | `earlier-attempts/rerun/SETTING.md`, `rerun/` |
| the account with a baseline; an illegitimate change of what she values runs through a mistake or an alteration | eighth | candidate counterexamples under its renderings, none clear; verdicts turn on details the cases do not fix; not shown independent of encoding | `earlier-attempts/account/BASELINE_ACCOUNT.md`, `account/VALUE_CHANGE.md` |
| the value side as three conditions against a reference | ninth | neither passed nor failed: the cases do not fix its comparisons; it bounds neither what she can know nor her unused information | `earlier-attempts/account/ACCOUNT.md`, `account/VALUE_RESULTS.md` |
| the board statement, with the comparison form of its third line | tenth | failed its criteria: seven cases of plain subversion pass; the third line turns on how a want is booked | `earlier-attempts/account/BOARD.md`, `account/LIT_RESULTS.md` |
| the statement of three ratings: "changes her no more than", the inducing test, a gate on her whole state | eleventh | failed its criteria: flags acts called acceptable; misses control of her act between equals; the inducing test wrong on two instances; three quarters of each case supplied | `earlier-attempts/account/STATEMENT.md`, `account/SPEC_RESULTS.md` |
| her trustworthiness derived from the adviser's conduct | thirteenth | clean conduct supplies neither assumption about her (I2, I4, `d2a_needed`) | `account/DERIVATION.md` |
| two tests of responsibility: the adviser's gain; a declared reference | thirteenth | wrong on 8 and 14 of twenty cases written against them | `account/RESP_RESULTS.md` |
| tests of intent on one mistake: the mistake is how the course serves the adviser's aim; the course makes it more likely (F); and is worth more with it (D); it is better than every alternative, which would do as well were the mistake granted (R2) | fifteenth | the first wrong on 7 of twenty-four cases by the reviewer's own count, which is not recomputed here; F, D and R2 wrong on 11, 13 and 7 of forty; the reviewer: a named aim can be chosen after the fact | `account/INTENT_RESULTS.md`; the first two replies of `REVIEW-astra-followup-15.md` |
| the strict "would choose otherwise" test: without the mistake the adviser would not have chosen the course (R1, R1s, R4) | fifteenth | wrong on 21, 19 and 17 of forty; each is right on 3 of the 12 cases adapted from the literature | `account/INTENT_RESULTS.md` |
| the "twin" definition of what conduct is for: conduct is on account of gain when a copy of the adviser that gives gain no weight would not have produced it | fifteenth | it is a property of an optimal choice, not of purpose: an attempt to mislead with a second sufficient reason is the copy's choice too, and ties make the copy's choice ambiguous | the fourth reply of `REVIEW-astra-followup-15.md`, §1 and §3 |
| the first idealisation read as correct reasoning from her evidence (deception shows as her distance from the best estimate her observations allow) | fifteenth | a listener who correctly allows for a source that lies one time in five has that distance zero and is deceived on the lying occasions | `account/mistakes_setting.py` (the listener); the third reply, §2 |
| the first idealisation as undoing only what moved her further from the truth | fifteenth | a move from −1 past a truth of 0 to +1 leaves her distance unchanged and is not undone | the fourth reply, §3 |
| the rule that a request is valid unless conduct on account of gain brought it about | fifteenth | circular: for a plan that induces a request and then grants it, counting the request valid and counting it invalid both satisfy the rule | the fourth reply, §4 |
| legitimacy as the absence of avoidable gain: the adviser took no advantage of her being fooled, uninformed or altered that it could have done without | fifteenth; set aside 22–24 November | it measures her against the facts and against idealised versions of herself, which takes a standpoint more accurate than hers; its quantities were supplied numbers on every case | `account/MISTAKES_ACCOUNT.md` |
| the disclosure rule with a lapse clause: manipulation iff a relevant mistake of hers, by his lights, is untold, or he expects her response to be a lapse from her considered rating | sixteenth | not failed on the bank (214 of 219 settled cases); its first half is sentence 1; the lapse clause gave way to the clause on her earlier rating after the ninth review's case of a judgement bent for a while | `account/CASE_RUNS.md`, run 11 |
| a clause for value change: a change in how she rates things by a route other than content she judges must be known to her and stoppable | sixteenth | needs her judging of content as a primitive, which the maintainer's position 7 avoids; passes three of an outside model's twenty adversarial cases that it faults; settles a third of ninety published cases | `account/CASE_RUNS.md`, the value-change test |
| the cost of stopping as part of sentence 3 | sixteenth | the cost is zero where the best option's influence-free counterpart is impossible though another could be supplied; two influences each cheap to stop are costly to stop together; moved to her authority by the ruling of 2026-11-24 | the eighth reply of `REVIEW-astra-followup-16.md` in the prompts directory |
| the pressure clause read on her rating of the moment | sixteenth | an open, stoppable presentation that reverses her ranking for a while passes | the ninth reply |
| regulating open pressure (it fails only where hidden or unstoppable) in place of prohibiting it | sixteenth | ruled out by the maintainer; on the bank it settles 28 of 39 cases with a lapse expected and passes 5 the author calls manipulation | `account/CASE_RUNS.md`, run 14 |

Five claims made in working notes and withdrawn, each with an exact instance:
`withdrawn/WITHDRAWN.md`.

## 3. In progress

**The statement as it stands** is `account/LEGITIMACY_STATEMENT.md`. Noggle's definition is
kept as the definition of manipulation, with a mistake judged by the adviser's lights: his
view says what he owes her and is never where she ought to end up, and he is not assumed more
accurate than she is. An adviser's conduct is legitimate when, by his own lights, nothing
that matters is untold; nothing is done to her behind her back and nothing against her own
judgement; and she can stop it. The three sentences are the maintainer's, frozen for testing
on 2026-11-24; a formal statement (F1, F2, F2′, F3) accompanies them and is open to revision.
What he does to her options, as against to her, is counted under her authority: what stopping
costs her, bundling, penalties, payments, threats, starting something over her refusal.

What stands behind it, none of it a statement of record:

- **A Lean model**, `LegitimacyModel.lean`: the adviser's picture of one episode, with the
  statement as a predicate `Model.Legit`. Proved: the predicate is unchanged by any bijective
  re-description of her state; a move that changes nothing in her bears no effect; no moves
  and nothing untold is legitimate; a failure of F1, of either half of F2, or of F2′ refutes
  it; one open, stoppable influence is legitimate and the same done covertly is not; the
  scoring it gives through `Legitimacy.gateValue` is a `DeconfusingCorrigibility.Scoring`;
  and a gate with soundness error `ρ` and completeness error `ρ'` gives legitimate conduct the
  higher expected score when `ρ(1 − w) < −w(1 − ρ')`. The model is simpler than the statement
  in nine respects its header lists, and on its one witness only the start rule and F2 do
  work.
- **Exact cases**, in the runner: 41 of the formal statement (`account/LEGITIMACY_CHECKS.md`)
  and 20 of a candidate clause for what stopping costs her, which is the authority side's
  (`account/STOPPING_COST.md`). Expectations were fixed first; statement and cases are by one
  hand; the chance that she goes against her earlier rating is supplied to each case.
- **Case runs** (`account/CASE_RUNS.md`), each one blind coding by a language model against a
  scorer written first. On the 240 cases of Noggle's book with a definite verdict the
  disclosure rule settles 219 and agrees on 214, the rule having been formed with the bank in
  view. The clause on her earlier rating settles 33 of the 39 cases where a lapse is expected
  and agrees on all 33, convicting 1 of 69 controls. A judgement bent for a while occurs in
  four cases of 152 as coded. The statement has not been run on a case of value change.
- **Nine outside reviews** by one model (`REVIEW-astra-followup-16.md` in the prompts
  directory), two of them blind to the project. Each found errors of form in the version it
  saw; none has seen the present statement or the Lean.

**Open.** `account/LEDGER.md` has 36 rows: 11 closed, each a Lean declaration; 19 open; 6
living notes. Its last section ranks the open work. By `ATTENTION.md` item:

1. **A witness on which every clause does work, the 41 cases as terms of the model, the
   simplifications removed** (item 151).
2. **An outside review of the Lean statement** (item 153).
3. **A second coding of the bank, and a set of cases of bent judgement** (item 154); a
   person's check of a sample (item 148).
4. **The cost of a decision of hers on the authority side** (item 149).
5. **Composition with the sequential corrigibility theorems** (item 150).
6. **Whether a gate can evaluate legitimacy at all** (item 147).
7. **The statement on cases of value change** (item 155).
8. **The verdict when conduct is cut into finer moves, and what a decision of hers is**
   (item 152).
9. **What the adviser believes and expects, for a trained system** (item 139).

Open from before and not touched by the statement: what supplies her trustworthiness (item
140); her valuing and what makes a request valid (item 141); relative to what distribution
the measures of §1 are taken (item 142); authority beyond a finite penalty (item 143);
verdicts on the literature's cases by two authors (item 144); the audit as a design (item
145); what is new against prior work (item 146).

The maintainer's positions are working positions, open to revision by the cases:
`DECISIONS.md`, `2026-11-24--legitimacy-statement-working-positions`, with those of
`2026-11-18--legitimacy-working-positions` and `2026-11-21--manipulation-working-positions`
where the later entry does not replace them. Three questions on this line are queued for him
there: whether a practice's rules cover a deception she did not herself ask for; whether her
asking makes legitimate what would otherwise be manipulation; and what bounds the cost of a
decision of hers where the influence is the price or she agreed to the penalty.
