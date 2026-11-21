# Legitimacy and manipulation: where the line stands (2026-11-21)

A checkpoint. The line aims at a formalism with defensible modelling choices that says
intuitively correct things about manipulation, following Noggle, and proves safety theorems
for the corrigibility design. It is not at that bar. The account as it stands is
`account/MISTAKES_ACCOUNT.md`; §3 below says what of it is checked and how. Paths are relative to this directory;
Lean files are under `lean/Workspace/Deference/Contrib/`. Every Lean result named is
kernel-checked. Those of this round are registered `lean-proved` in
`projects/normativity/CLAIMS.md` under the id beside each. A result is what its declaration
states and no more.

## 1. Solid

1. **The idea.** An adviser manipulates when it tries to influence her by getting her to
   make a mistake (Noggle's Mistake Account; his definition is kept as the definition). The
   faculties she decides with are treated as estimators, so a mistake is measurable;
   emotions and attention are treated as appraisals. This is a modelling choice, stated in
   `account/MISTAKES_ACCOUNT.md` §1, and nothing proves it right.
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

Five claims made in working notes and withdrawn, each with an exact instance:
`withdrawn/WITHDRAWN.md`.

## 3. In progress

**The account as it stands** is `account/MISTAKES_ACCOUNT.md`. Noggle's definition is the
definition of manipulation, and "trying to" is not formalised. The formal part is a
quantity and a property. The quantity is what the adviser's conduct gains through mistakes
it caused in her, through her not knowing what it knows, and through an unasked shift in
her valuing, found by comparing what the conduct achieves with her as she is and with her
*undamaged*, *informed* and *unshifted* in turn. The property is *avoidable gain*: another
option open to the adviser was as good otherwise and had less such gain. A history is
legitimate when none of the adviser's conduct on it takes avoidable gain: the adviser took
no advantage of her being fooled, uninformed or altered that it could have done without.
That gloss is proposed and queued. Legitimacy so defined is narrower than the absence of
manipulation in Noggle's sense.

What supports it, none of it a statement of record:

- **Paper proofs with exact searches** (`account/mistakes_setting.py`,
  `mistakes_sequential.py`, `mistakes_longrun.py`, in the runner). For a maximiser over
  finitely many options: no avoidable gain gives the best value gain aside; what it gives
  up is at most the extra gain it took; a gate that scores avoidable gain below every
  other score is maximised without it; removing gain from the reward protects that value
  and does not stop the adviser taking gain. Over many decisions, extending the post's
  Theorem 3 on paper: authority as in the post; no avoidable gain in the adviser's picture
  at every decision; her informed interest under a second calibration hypothesis; rarity of
  illegitimate histories in fact under a third and a floor on the gate. Each hypothesis has
  an exact instance in which it alone fails. The idealisations are not computed from a
  causal model in any of these: `h`, `G` and `L` are given numbers.
- **Case runs**, each one coding by language models, no person having checked an encoding.
  Three readers coded 266 cases of Noggle's book against a formal statement of his account:
  224 agree, 17 disagree, 25 give no comparison (`account/NOGGLE_RESULTS.md`; the
  paraphrases are outside the repository). On forty cases an outside model wrote, an
  earlier form of the avoidable-gain test agrees with its verdicts on 37
  (`account/INTENT_RESULTS.md`), and a reader given the stories and the account in words on
  39 as to manipulative or not (`account/BLIND_RESULTS.md`). On the nineteen cases of
  `account/LIT_CASES.md` whose source judges an act, a reader applying the account's
  value-change part agrees on 12 and contradicts none; a variant that makes an
  unauthorised change of her values a violation of her authority agrees on 12 of the 14
  faulted and contradicts two of the five accepted (`account/VC_RESULTS.md`).
- **Three outside reviews** of earlier versions
  (`REVIEW-astra-followup-15.md` in the prompts directory). The last, of the version before
  this one, accepted the first idealisation for a single estimate, the rule for requests
  and two of the four long-run conclusions as stated, and gave the range condition the
  other two now carry; it holds that the weight of the fourth conclusion is in its third
  hypothesis, and that who would establish that hypothesis is the main thing missing.

**Open.** `ATTENTION.md` items 139–146 carry problems 1–8, in order, and items 148–152
problems 9–13.

1. **When the adviser is responsible for her mistake**. Avoidable gain is the candidate for
   the checkable part; what "believes" and "is trying to" mean for a trained system is not
   settled, and the candidate has not been run on the twenty cases of
   `account/RESP_RESULTS.md` or computed from a causal model of any case.
2. **What supplies her trustworthiness**. The adviser's good conduct alone does not: that is
   shown by instances, and conduct helping under further assumptions is not excluded. Whether a
   named procedure for her considered judgment is reliable where an adviser would exploit
   it is assumed, and what the adviser knows and has not recorded is the problem of
   eliciting it.
3. **Her valuing**. The account compares her with how she would have been left alone and
   counts an unasked shift as gain; the rule for a valid request is stated and needs a
   convention for requests made together and for an idealised self that could answer more
   than one way. Whether an unauthorised change belongs with her authority is queued.
4. **Relative to what distribution**. The measures are stated for a supplied
   weight and the derivations for her prior; taking either as the true law is a further
   premise. The long-run statement separates the adviser's picture from the facts and
   leaves open what that picture is for a trained system.
5. **Authority**. Her commands as well as her evaluation; strict priority,
   which a finite penalty does not give; her later self against her present wishes.
6. **Verdicts on the literature's cases**. Two single codings exist
   (`account/VC_RESULTS.md`); none by two authors independently, and seven of nineteen are
   undecided for facts the stories do not give.
7. **The audit as a design**. Sampling, and what the audit pays the adviser to
   do besides behave; who establishes the long-run statement's second and third hypotheses.
8. **What is new** against reward tampering, path-specific objectives,
   eliciting latent knowledge and induced preference shifts: not established, and by the
   maintainer's working position not a gate on the line.
9. **A person's check of the encodings** (item 148).
10. **The authority variant**, with a clause for changes she knowingly brings on herself
    and the trifling exemption in both tests (item 149).
11. **The long-run statement in Lean**, with its witnesses (item 150).
12. **The causal model behind the three idealisations**, for one worked interaction
    (item 151).
13. **Whole plans compared**, for an adviser that plans ahead and removes her later honest
    options (item 152).

The maintainer's answers to the questions this line has queued are working positions, open
to revision by the cases: `DECISIONS.md`, `2026-11-18--legitimacy-working-positions` and
`2026-11-21--manipulation-working-positions`. Three questions on this line are queued for
him there: whether a practice's rules cover a deception she did not herself ask for;
whether the gloss above is the single reading of legitimacy; and whether an unauthorised
change in her values belongs with her authority or inside legitimacy.
