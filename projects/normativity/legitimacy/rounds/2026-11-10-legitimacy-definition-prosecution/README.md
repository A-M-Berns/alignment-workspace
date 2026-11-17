# Legitimacy: manipulation as induced mistake; a change of what she values judged against a reference

Round `2026-11-10-legitimacy-definition-prosecution`.

## The account

`account/STATEMENT.md` is the statement that governs now: the prompt author's consolidation
of 2026-11-17, six of its choices adopted by the maintainer for testing and none a ruling.
She has three ratings of an option, each her own on one **yardstick**: `r` as things stand,
`R^s` once told the chances her observations support, `R` once told what the future
contains; her way of valuing is `R`. Three lines: **trickery**, the gap between `r` and
`R^s`; **pressure**, her regret in `r`; **illegitimate value change**, how much better, by
her informed rating when the adviser acts, the best policy that **changes her no more
than** the one followed is than the best that makes the whole of its change. The adviser
**induced** a mistake when it would have acted differently had the mistake gained it
nothing; coercion and deprivation are other wrongs. `account/SPEC_CASES.md` is thirty-four
cases written out in full, `account/SPEC_RESULTS.md` what the statement computes on them,
`account/STATEMENT_CHECKS.md` the formal checks.

`account/BOARD.md` is the statement the tenth follow-up tested: the maintainer's whiteboard of
2026-11-16. Her faculties are estimators of facts and
of her true utilities, and manipulation is measured in three quantities: the
miscalibration of an estimator (**trickery**), her regret by her own valuations
(**pressure**), and, for an adviser whose policy is not **f-neutral** (it changes her way
of valuing from how it would develop with no adviser actions), how much better the best
f-neutral policy would have been by her way of valuing at the moment the adviser acts
(**illegitimate value change**). `account/LIT_CASES.md` is the bank of the literature's
cases it was tested on, `account/LIT_RESULTS.md` the classification, and
`account/BOARD_CHECKS.md` the formal checks.

`account/ACCOUNT.md` is the statement the ninth follow-up tested. At a moment she has an
**appraisal**, a probability over the possible joint values of the **facts**, and a **way
of valuing**, a number for each move at each value of the facts; her **valuation** of a
move is the one averaged by the other, and her **true utility** is her way of valuing at
the true facts, among them where the move leads and who she becomes on it. Three
measures: a valuation's **miscalibration**, her **unused information**, her **regret by
her own lights**; being less informed is none of them. On the belief side an adviser's
policy **manipulates** her when some counted appraisal's miscalibration, or her regret,
is larger under it than under the **permitted policies** its role stipulates. On the
value side the question arises when her later way of valuing is distributed differently
under the policy than under the **idle** one, and there is no issue exactly when a single
permitted policy is matched on **options** (the best she can do, for each way of valuing
in a class read **narrow** or **wide**), on **accuracy** (each valuation's
miscalibration) and on **self-command** (her regret). A failure of the last two is
manipulation; a failure of the first is the adviser settling what was hers to settle.
The belief side is held with some confidence; the value side is the prompt author's
statement, tested in this round only. All names are provisional.

The account is a formalisation of Robert Noggle's Mistake Account (*Manipulation: Its
Nature, Mechanisms, and Moral Status*, OUP 2025; "The Mistake Account of Manipulation",
*Journal of Practical Ethics* 14(1), 2026, doi:10.3998/jpe.9951); that a faculty is for
something and manipulation distorts her away from it is Sam Eisenstat's idea; the
statement in symbols is the maintainer's and the prompt author's. Closely related work on
the same problem: Nora Ammann, *The Value Change Problem*
(<https://www.alignmentforum.org/s/3QXNgNKXoLrdXJwWE>). Direction: `DECISIONS.md`,
`2026-11-11--legitimacy-purpose-first-direction`.

Each other document or directory states and tests one candidate statement and keeps its own
content; on every question `account/BOARD.md` also answers, `account/BOARD.md` governs:
`account/ACCOUNT.md` (three conditions against one permitted policy; tested by
`account/VALUE_RESULTS.md`, `account/RENDERINGS.md`, `account/BRIDGE.md`),
`account/BASELINE_ACCOUNT.md` (a baseline way of valuing that follows her through clean
steps; tested by `account/RESULTS.md`, `account/VALUE_CHANGE.md`, `account/BENCHMARK.md`),
`rerun/SETTING.md` (worse than before, and avoidably), `estimates/SETTING.md` (worse than
under the adviser's honest conduct), `blocks/SETTING.md` (a part as a mechanism and a
purpose on the world), `scored/ACCOUNT.md`, `decomposition/ACCOUNT.md`,
`teleology/ACCOUNT.md`.

## What was found

For the board statement: `account/LIT_CASES.md` is the bank of 52 cases from Harman,
Pettigrew, Kolodny, Carroll et al. and Noggle, verified against the sources, with each
source's verdict and what it is a verdict on; `account/LIT_RESULTS.md` the executor's
classification; `account/LIT_RENDERING_REVIEWER.md` an outside renderer's;
`account/LIT_RENDERINGS.md` their comparison; and `account/BOARD_CHECKS.md` sixteen formal
items on the third measure, on a variant of it and on f-neutrality, with a status each.
The report's section *Tenth follow-up* says what they show.

`account/VALUE_RESULTS.md` carries the nine results the value side rests on with a status
each, `account/BRIDGE.md` its join to the post's Lean, `account/TEST_CASES.md` the 64
cases of its test with how a rendering is recorded and compared,
`account/RENDERING_EXECUTOR.md` and `account/RENDERING_REVIEWER.md` the two renderings,
`account/RENDERINGS.md` their comparison, and `account/LEAN.md` the map to the Lean
declarations. For the statement with a baseline, `account/RESULTS.md` carries eleven
results with a status each, `account/VALUE_CHANGE.md` and `account/CASES.md` the test of
the claim its value side rests on, and `account/BENCHMARK.md` that statement on a
published benchmark. The report's sections *Ninth follow-up* and *Eighth follow-up*
carry the external reviews and what was done with each of their points.

Follow-up verdict (the board statement on the literature's cases, 2026-11-16):
FAILS-ITS-TEST — the maintainer's board statement measures manipulation in the
miscalibration of her estimators, her regret by her own valuations and, for an adviser that
changes her way of valuing, how much better the best policy that leaves it alone would have
been by her valuing at the time. On 52 cases from Harman, Pettigrew, Kolodny, Carroll et al.
and Noggle, verified against their sources and rendered twice, the two renderers agree on
the third measure in 16 of the 33 cases in which an adviser acts, in all ten where both fix
it and with no opposite answers; one leaves it unfixed in 21, the cases not saying how she
rated beforehand the course that changed her; its answer turns on booking a want as valuing
or as discovery in 9 and 13. By the executor's rendering the statement gives the source's
verdict on the act in 15 of 18 and goes against it on Pettigrew's unhappy parent, Kolodny's
just deterrent and framing. Nine formal items hold, four with a stated repair; the third
measure never flags the benchmark's clickbait. Seven constructed cases of plain subversion
pass all three measures, six without a change of what she values. A variant comparing the
best way of making the same change with the best way of leaving her alone removes the flags
on requested changes and lets a harmful means borrow a better one's merits; how 'the same
change' is drawn decides it. No Lean; nothing registered.

Follow-up verdict (the value side as three conditions against a reference): MIXED — the value side is restated without a baseline: a change of what she values raises no issue exactly when one permitted policy of her adviser's role, the idle one always among them, is matched on options, accuracy and self-command. Of the nine results it rests on, five hold as stated; the guarantee holds with the value of a move read as that of taking it whatever she observes and fails read as its value given that she takes it; that a second way of valuing with the same valuations has a different true utility needs a value of the facts that can occur outside the span of her appraisals; that the division between appraisal and way of valuing is observable rests on her valuations as numbers and on a stake worth the same at every value of the fact; and the three conditions bound neither what she can know nor her unused information, so an adviser that leaves her knowing less, or using less of what she knows, passes them. The split of full miscalibration, the guarantee and the convex-hull form of the options condition in both directions are kernel-checked with witnesses and ship unregistered. Joined to the post on paper: a legitimacy predicate with a tolerance exists on histories that carry the policy; the tolerance gives non-inflation and self-trust for each move's valuation, relative to the reference, and not for her verdict on the move she takes; no hypothesis of the post's theorems is discharged; the options condition has no counterpart of the authority module's requirement that a resolution be the holder's; and after an illegitimate change the segment gate scores a later clean run by her changed verdicts. On 64 cases rendered twice, independently, the renderers agree on whether the conduct changes her valuing or her beliefs in 54 and on each of the three conditions in 14 or 15: the external renderer found the comparisons not fixed by the cases in all but about ten and decided thirteen, the executor's verdicts rest on stated readings in a third to a half of its answers, and no case goes against a recorded verdict in both renderings. Whether the statement classifies cases was not measured. The external review judges the value side a second criterion sharing the estimator calculus, and its strongest objection is that keeping her options open does not show a decision about herself remained hers. Nothing registered; every component open or a living note.

Follow-up verdict (the consolidated account): MIXED — the account is stated once (appraisals with a true value each, a way of valuing applied to them, a baseline that follows her through every step in which her adviser neither induced a mistake nor altered her, a reference given by the adviser's role) and its belief side and value side are tested apart. Of eleven worked results nine hold as stated; the bound on what her choice costs holds with her valuations' miscalibration taken given everything she observed and fails at the two weaker strengths, since a principal who ignores an informative observation has no regret and no such miscalibration and still loses; that an appraisal which responds to conduct can be miscalibrated fails as stated, because a variable's true value may depend on the conduct, and holds if the appraisal is not exactly right under both conducts; calibration at every step gives a vanishing mean inflation along a run only with her true utility fed back. The split of mean squared error, the three channels, that bound and the deferring identity are kernel-checked with witnesses and ship unregistered, their registration waiting on a handle only the maintainer can map. The claim the value side rests on, that an illegitimate change of what she values runs through a mistake of hers or is an alteration, has on 34 counted cases, under renderings the executor wrote, two illegitimate changes with neither in the rendering used (a preference reversed by framing; addictive design with everything disclosed and foreseen, a rendering that changes the facts its evident verdict was recorded on), two more that are another wrong (a preference that follows the removal of options), and one legitimate change with a mistake (a teacher's feigned enthusiasm); eleven of the 34 verdicts turn on a detail the case does not fix, and a conversion through a false belief sincerely argued for counts as illegitimate. An external review judges the counterexamples conditional on their renderings and the test as one of renderings and not of the account on the cases as their sources state them. An invariance clause added by an addendum convicts framing and adaptation and also two innocent exposures, on an annotation of what she counts as irrelevant. On four examples of Carroll et al., reproduced against the paper's table except for two cells, the account extended by details the paper does not have leaves the conspiracy example's person alone, refuses clickbait, leaves the writer where he is and nudges the trainer's client, agreeing with none of the paper's eight objectives on all four; the verdicts reverse where a change is one of taste with no truth, with whether a change she registers and did not choose is an alteration, and on one example with how true utility is totalled over steps. The value side is a conjecture; under the definitions as frozen and the renderings used it has candidate counterexamples, and the classification is not shown to be independent of how a case is encoded. Nothing registered; every component open or a living note.

`estimates/RESULTS.md` carries the statements of this pass with a status each, by the
dispatch's eight questions, the case counts and the map onto the existing Lean;
`estimates/NEGATIVE_RESULTS.md` carries four negative results on the earlier accounts
with proofs; the report's section *Sixth follow-up* carries the external review and what
was done with each of its points.

Follow-up verdict (manipulation as induced miscalibration): MIXED — C1, C2 and C5 hold as stated; C3 holds with a constant that is not tight (the tight one is the square root of two) and bounds her loss in true utility when her choice is a function of her information; C4's threshold holds and its last clause fails when "right on average" means over options taken at random, since an honest adviser that maximizes her verdict selects what she overrates; C6 is an identity that needs a third term when the honest report would change what she does. Of 108 cases frozen before the code, under renderings the executor wrote, 76 of 96 counted sort when her true utility is anchored at her starting values and 72 of 99 when it is that of the person she ends as; ten or eleven objectionable cases are missed (an undisclosed advocate, strategic silence, buried information, lies that leave her no worse calibrated, a narrowing feed, exploitation by a policy that treats everyone alike, dependence) and four benign deceptions are convicted. No intention is read; the bank's honest cases are not convicted, and an external review's four honest cases are, because the comparison with someone unable to make the mistake must be with someone who differs only in that, which the account does not say. Total miscalibration over listed quantities depends on their units. Reading A has a consistent model and admits the utility of whoever she ends as; calibration to her true utility is not identifiable from her verdicts, and every verdict on a change of taste is decided by which function her utility is. Expected inflation of her verdict is at most the root of her expected miscalibration; for the realized sequence the post's theorem is about, calibration at every step gives no bound, and the true-score form of Theorem 3(b) is not regret in true utility. An adviser can honestly let her judgment decay until a departure pays, and nothing in the account marks the decay; no one model joins the pieces. For belief the workspace's Correct, Transparent, Realizes and Value already give the account's conditions in a stronger form; it adds a reading of her verdict as an estimate of her own utility, graded mistakes, and manipulation as a comparison between policies. Four negative results on the earlier accounts are stated with proofs. Nothing registered; every component open or a living note.

`rerun/RESULTS.md` carries the seventh pass: the same bank under the revised definition of
`rerun/SETTING.md`, with twenty-five new scenes.

Follow-up verdict (the bank under the revised definition): MIXED — on the bank of 108 frozen by the sixth pass, scored on three questions (manipulation, covered, another wrong) against evident characters the executor recorded before the code, the revised definition is wrong on 5, 6 and 8 cases under the three candidates for her true utility (her starting values, her values at the end, her starting values as changed by learning alone), against 16 and 14 for the sixth pass's definition on the same table and 11 and 12 once two limits of its reporting are removed; a stricter table that asks taste-shaping to be manipulation and not merely alteration gives 5, 14 and 8. It repairs an undisclosed advocate, strategic silence and a policy that exploits everyone alike, records a surprise party, a magician and a bluff as covered manipulation, and does not convict the external review's four honest scenes. It is wrong on buried information and on a lie that is the only listed way to keep another estimate of hers right. Of twenty-five new scenes built against it, it is wrong on seven or eight: it convicts honest conduct that leaves her worse than before wherever the scene lists a better conduct that withholds nothing, acquits an undisclosed advocate whose listener started out worse, and by its restriction to what bears on a decision acquits a cruel lie about an idle matter. Ten banked verdicts change in variants that alter a detail the case does not fix, and three evident characters move the count. Verdicts do not move with units; they move when a quantity is re-expressed by a map that is not affine, and with the measure of being no less informed. No candidate for her true utility is right on every case of changed values, and the learning candidate's verdicts are fixed by its annotation in these renderings. Nothing registered; every component open or a living note.

`blocks/RESULTS.md` carries the fifth pass's thirty-two statements and case verdicts.

Follow-up verdict (a part as a mechanism and a purpose on the world): MIXED — with purposes given and not recovered, range and gap are stated and used once a grain is fixed, and the four kinds of influence are not: they need the adviser's null action as a comparison, typed actions, a move that carries confidence, her verdict as one part's move, the rule at other aims for ties, and a menu for each revising part. Of the dispatch's twenty-seven cases with a prediction twenty-six have the predicted verdict under renderings the executor wrote, a check of consistency and not a test; an advocate for an undisclosed side diverges because the null comparison runs her mechanism in the adviser's absence. Of thirty-two statements nine are proved on paper, eighteen hold on a stated example and five are refuted, each a fact about one formalization. Conditioning on the step catches a lie targeted in time; a lie targeted at a state is caught only by a move that carries confidence, at a size second order in the lie's probability, and none of four grains computed separates it from honest difficulty when the move is two-valued. A foreseeable shift in her verdict equals the shift in what the verdict is for up to the roots of the verdict part's two gaps, and a maintaining part in range with a menu closed under re-reading installs a mechanism in range; that every shift traces to something out of range or to the adviser is refuted, and whose a gap is rests on a stipulated comparison. A threat is told from an offer and a true warning with no aim read, and from a warning of the adviser's own standing practice only by a supplied fact about the branch not taken. Fit among her ends gives a revising part a purpose with no fixed final end, never excludes dropping an end, and does not say which of two opposed ends yields: a chain of two steps each in range carries her from the outcome her starting ends value most to the one they value least, and the rule on ties stops an aim choosing between equally fitting replacements only when the parts that later tell them apart are left out. Parts in range do not give a verdict in range unless the aggregation is itself calibrated. The post's calibration hypothesis is implied in probability, for a bounded score, by the range condition at the grain of the history of the part that estimates the score, and one existing Lean theorem applies to advisers whose signal does not vary with their aim. The decomposition adds permission and a rule of attribution and no protection. Nothing registered; every component open or a living note.

## Run

    python3 run.py          # every pass: banks, statements, the addenda's facts, the account and its value side
    python3 run.py --json   # the same as data

About two minutes. Exit nonzero when a bank parses to nothing, when a computed verdict
diverges from its bank without a line in that pass's `DIVERGENCES.md`, when a listed
divergence does not occur, or when a status in any `THEOREMS.md`, in `blocks/RESULTS.md` or
under `estimates/` is not the one its check supports, or when a count in `rerun/RESULTS.md` is not the one computed. Python 3.9+ standard library; exact rationals; no
network. `tests/run.py` hands over to `run.py` so the repository-level runner finds it.

## Layout

| path | what |
|---|---|
| `rerun/SETTING.md` | the revised definition, each choice with its alternative, and the devices found needed |
| `rerun/PREDICTIONS.md` | frozen before the code: for each of the 108 cases of `estimates/CASE_BANK.md` the details the revised definition asks for, the evident character on three questions and the prediction; the review's four honest scenes; twenty-five new scenes |
| `rerun/RESULTS.md` | the counts beside the sixth pass's, the wrong cases, the new scenes, the variants, the verdicts that turn on an unfixed detail, well-definedness, the three candidates for her true utility |
| `rerun/DIVERGENCES.md` | the three cases whose computed verdict differs from its prediction |
| `rerun/model.py`, `cases.py`, `run.py` | the definition over a finite scene; the cases as scenes; this pass's runner |
| `estimates/SETTING.md` | the account in words and symbols, each choice with its alternative, and the devices found needed |
| `estimates/CASE_BANK.md` | 108 cases frozen before the code, each with its evident character and the executor's prediction |
| `estimates/RESULTS.md` | statements by question, each with one status and its proof or example; the case counts; the map onto the Lean |
| `estimates/NEGATIVE_RESULTS.md` | four negative results on recovering legitimacy from a decomposition into purposive parts, with proofs |
| `estimates/DIVERGENCES.md` | the seven cases whose computed verdict differs from its prediction |
| `estimates/ONE_PAGE.md` | the account on one page, with what survived and what did not |
| `estimates/model.py`, `cases.py`, `bank.py`, `checks.py`, `run.py` | the model; the cases as scenes; the bank's reader; the checks; this pass's runner |
| `blocks/SETTING.md` | the setting the fifth pass tested: a part as a mechanism and a purpose on the world |
| `blocks/CASE_BANK.md` | thirty-seven rows frozen before the code: the dispatch's twenty-eight cases with its predictions, and eight added |
| `blocks/RESULTS.md` | statements by question, each with one status and its proof or example; the verdict on each case |
| `blocks/DIVERGENCES.md` | the one row whose computed verdict differs from its prediction |
| `blocks/model.py`, `cases.py`, `bank.py`, `results.py`, `run.py` | the model; the cases as scenes; the bank's reader; the checks; this pass's runner |
| `scored/` | the account with candidates weighted as explanations and influence judged against the adviser's aim (`ACCOUNT.md`), its bank of ninety-four cases, its nine statements and what runs them |
| `decomposition/` | the account as a goal pursued through parts with yes-or-no constraints on candidates (`ACCOUNT.md`), its Lean map, its bank of eighty-nine cases, its nine statements, two addenda (`TWO_DECOMPOSITIONS.md`, `ADVISER_AS_PART.md`) and what runs them; `scored/` builds on its model and scenes |
| `teleology/` | an earlier statement of the purpose-first account (a fixed condition `K` with clauses *sound*, *in range*, *maintained*), its bank of fifty-five cases, its eight statements and what runs them; an earlier statement than `decomposition/ACCOUNT.md` |
| `CASE_BANK.md` | nineteen cases, B1–B6 and T1–T13, each with a scenario and a source |
| `steering/CASE_BANK.md` | fourteen further cases, N1–N14, on one scene template |
| `steering/PRIOR_WORK.md` | survey of published work on manipulation, persuasion, function and fiduciary duty, by source |
| `steering/DIVERGENCES.md` | seven computed verdicts that differ from `steering/CASE_BANK.md`'s predictions; cited from `DECISIONS.md`, *Awaiting the author* |
| `REMOVED.md` | files removed from this directory on 2026-11-11, each with its reason |
| `run.py`, `tests/run.py` | the runner and its hand-over |

## Recorded verdicts

Each bank carries, beside its cases, verdicts pre-registered for a definition of legitimacy
tested on it. What was computed against them is recorded in
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, §1–§8 and *Follow-up of
2026-11-10*, and summarized by the lines the round's record in `state/rounds.json` quotes.

Verdict: DEFINITION-SURVIVES-THE-BANK — nineteen computed verdicts match their pre-registrations with no forced revision; every clause is forced by a banked case, W under the free vocabulary only; the honest class factors through an explicit replay F; the coarsened L convicts B4 and the refined L acquits T10. L0 must read the transition function, the replay F absorbs L0 and L3 on this bank, and L1 and L3 overlap on every direct standards write so that T5 alone forces L3. Nothing registered; every component open or a living note.

Follow-up verdict (the steering account): CLARIFIES and REDUCES-TO-KNOWN, a mixture — the steering account's proper drivers, its broken/steered distinction and its two standards restate published notions (malfunction of a function; pathology against manipulation by a parasite; arm's length against fiduciary duty; no effect of the adviser's aim on a delicate state), and C1, C2 and C7 are instances or corollaries of known results. What the follow-up adds: on 38 variants of 33 cases the faithful-adviser standard's acquittals lie inside the arm's-length standard's, which lie inside those of L0–L3 ∧ W, with the replay form comparable to none of the three; and C4, following the proper driver is a guarantee against an adviser who may be opposed and fails against one whose aim is hers when she cannot take in everything it knows. C3 and C5 are refuted as written; C8 is open. Twenty-seven of 33 cases match their predictions in every column, seven verdicts on six cases diverge, and no per-case choice was needed. Nothing registered; every component open or a living note.

Follow-up verdict (the purpose-first account): MIXED — of nine statuses on eight statements about the account, two are proved, two hold on a stated domain, four are refuted and one is open. Her later judgment is at least as good by her own lights for expectations (the value-of-information inequality, which needs her values fixed) and not for values. That trust is not manufactured, and that the gate gains nothing, are refuted for in range as the account states it, and for an adviser whose aim she knows when her evaluation is a verdict; they hold when nothing the adviser does to her depends on its aim, which is close to the class-level transparency the workspace's Lean already asks. A departure of small probability costs the gated score a fixed amount. The verdicts follow the allowed set a case is given: nineteen of twenty-one in-range failures become legitimate once she allows for every aim, the other two being the two whose source she cannot represent. A threat fails no clause. Fifty-four of fifty-five banked predictions match, which is fit. Nothing registered; every component open or a living note.

Follow-up verdict (purpose as a goal pursued through parts): MIXED — of nine statements about the account, four are refuted and five hold on a stated domain, each as a fact about one formalization. The constraints do not fix purposes in it: in a class of 3,000 candidates over a three-part chain eight are admissible, no two classifying the adviser's actions alike, and a candidate whose goal is whatever she does is excluded only by a condition no extensional test captures (fifteen are admissible without it). Read pairwise, never opposed excludes all eight, and leaves two once the situations where her own judging part reverses a right belief are not counted usual. A lie widens no gap where she was already wrong, and none under four of the eight where it concerns a matter nothing reads. The four kinds are not exclusive, and only the step from serving to not serving survives redescription. That every bad change in what she cares about widens a gap holds in the one scene enumerated, close to by construction; her goal can fall through her parts' coordination with no gap widened. A legitimacy predicate built from gaps has the shapes of the post's scoring and decision, depends on the comparison action (27, 33, 46 or 38 of 57 renderings convicted), and under none gives the gate's no-gain property, since harm is not subversion. Eighty-four of eighty-five banked predictions match, which is fit. Nothing registered; every component open or a living note.

Follow-up verdict (candidates weighted, influence judged against the adviser's aim): MIXED — of nine statements about the account, five are refuted and four hold on a stated domain, each a conditional calculation in one formalization: a small scene, three stipulated principals, two tabulated description languages, one cost for a missed move. Scoring candidates by parsimony, fit and handles, read by a second predictor, concentrates the weight in mass (the ten heaviest of 4,000 hold 0.84 to 0.98) and not on agreeing candidates: at 0.95 or more of the weight her judging part is given no purpose or one naming its own mechanism, its behaviour carried as a table of her history, and the heavy candidates split on which adviser inputs are illegitimate; a purpose equal to its mechanism is charged as a rule by intersubjectivity and is not removed as a table; the score is a loss, not a code length. Read as the best move on what a part sees, a purpose for the belief part follows her corrections and the judging part's does not. Judged against the adviser's aim under stated candidates and assigned aim structures, 77 of 89 cases match their evident character against 66 by a changed standard, and a threat is illegitimate; a lie told at every aim passes, and the weights do not favour the stated candidates. Between actions that harm, subvert and force nothing against each other her choice is the same under the stated candidate and not under the candidates tied at the top for two principals; no maximizing adviser was analysed. The condition is strictly weaker than aim-freedom of the adviser's whole intervention, to whose guarantee the decomposition adds nothing; it adds a rule for which aim-dependent variation to permit. Eighty-nine of ninety-three banked rows match, which is fit. Nothing registered; every component open or a living note.
