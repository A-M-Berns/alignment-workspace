# Ledger of the legitimacy line (2026-11-26)

One row per component of the line. The line has three layers, and the ledger a part for each:
the statement in words (`LEGITIMACY_STATEMENT.md` §1, §2), the formal statement over notions
taken as given (§3; `LegitimacyStatement.lean`), and the interpretation, which works those
notions out on histories (`interpretation/INTERPRETATION.md`). **What is stable**: the three
sentences, held by the maintainer and selected by his verdicts on twenty hard cases; the
formal statement's theorems, which are kernel-checked. **What is not**: any way of deciding,
for a concrete episode, whether the statement holds of it.

A verdict is **closed** (a Lean declaration or a checker invocation stands for it, with the
event that reopens it), **open**, or **living note** (a position or a description, held and
revisable, that no check adjudicates). *Lean* files are under
`lean/Workspace/Deference/Contrib/`; `LegitimacyStatement.lean` has the namespace
`Workspace.Deference.Contrib.LegitimacyStatement` and `LegitimacyGate.lean` the namespace
`Workspace.Deference.Contrib.LegitimacyGate`; no declaration of either is registered. *The
runner* is `python3 run.py` in the round directory. Items are those of `ATTENTION.md`. Paths
are relative to this directory.

Kinds of evidence, strongest first: **kernel** (kernel-checked, of the declaration as
stated); **exact** (an exact check whose inputs an episode supplies); **coding** (a blind
coding by one language model against a scorer written first); **verdict** (the maintainer's
verdict on a written case, `HARD_CASES.md`); **review** (the outside model; reviews 8 to 14
each a fresh session that read only its brief, reviews 2 to 7 not blind; the replies are in
`REVIEW-astra-followup-16.md` and `REVIEW-astra-followup-20.md` in the round's prompts
directory); **reasoning** (argument only).

Closed rows share one reopening event unless they name another: `python3 tests/audit_axioms.py`
fails on the declaration, or a commit changes its statement or the statement of a definition
it mentions.

## 1. The statement in words

| # | component | verdict | evidence, and its kind | what would move it | item |
|---|---|---|---|---|---|
| 1 | Sentence 1: nothing untold that matters | living note | Held by the maintainer since 24 November, unchanged in substance. *Coding*, run 11, two codings of one sheet by coders of different models (`CASE_RUNS.md`): of 240 bank cases with a definite verdict the disclosure rule settles 219 and agrees on 214 on the first coding, 216 and 212 on the second; the rule was formed with the bank in view. *Review*: 13 and 14 report that "told" is permanent, so making her forget what he told her leaves it told, and that a view's bearing "and how much" needs to be relative to what else she has heard; neither is taken into the words. Not ruled: whether he must mention an option of someone else's that he believes she would rate higher (the sentence says yes) | The maintainer's rewording; a person's reading of a sample of cases against the two codings; the ruling | 148 |
| 2 | Sentence 2: he does something to her when her mind moves otherwise than she, at her last settled decision, would have judged that seeing and hearing it should; each such thing, and each withholding of what comes from someone else, she can pick out; and none that he expects to lead her to choose what she rated lower then, unless she asked | living note | The maintainer's positions 2 to 4 of 25–26 November. *Verdict*: on the twenty hard cases this rule (A) differs from no verdict he gave; the three alternatives differ on 2, 4 and 3 of them (`HARD_CASES.md`). *Coding*: run 16, the clause on her earlier rating, two codings: with a lapse expected it settles 33 of 39 and agrees on all 33, convicting 1 of 64 settled controls; on the second coding 30, 29, and none of 57. Run 17, her judgement read as her prior view of the hypothetical, one coding: 36 of 39 settled, all 36 agreeing; 8 of 60 settled controls convicted, where the prediction was at most 4; sheet 17 has no question about her earlier rating, and with sheet 16's answer added after the result was seen, 1 of 64. *Exact*: in the interpretation's model twelve episodes pair the same events with different judgements of hers and get different verdicts (`episodes_views`). *Review*: 13 found that "would have said she would respond" let a foreseen and disowned weakness pass, answered by the wording "would have judged"; 14 calls her judgement of the hypothetical a coherent object, a partial normative response map, and names four things the words do not fix: whether it is about a kind of observation or an occurrence, whether it speaks of ratings only, how far inability to judge one aspect reaches, and how it applies to options that did not exist at her last settled decision. No coding asks whether she can pick a thing out | A case, published or written, on which the sentence gives a verdict the maintainer rejects; a person's reading of the cases on which the codings differ; a coding of the first half | 148, 154 |
| 3 | Sentence 3: she can stop each thing he does to her, from before he starts until he could no longer call it off, and he expects she would if she rated stopping strictly above going on | living note | Held by the maintainer; what stopping costs her is her authority's (row 13). *Review* 14: the sentence gives control over each thing he does, which a single option ending everything is stronger than; an act whose effect falls between two of her decisions has no stop asked of it. No coding and no hard case tests it: all twenty assume she can stop | A case on which "each thing" and "a way to stop" come apart from what the maintainer wants | 157 |
| 4 | Her own response is hers; nothing separates what is said from how it is said | living note | Position 2, the maintainer's words: "It has to just be conditioning on some new observation, not separating content from presentation." *Verdict*: cases 4 and 14 fine; rule C ("what he says is always hers") is rejected by 2 and 3 | A verdict of his that needs what is said to be treated apart from how | — |
| 5 | What she could not have judged in advance is hers too, governed by sentences 1 and 3 | living note | Position 4; the difference from Noggle on moving appeals is accepted (consequence 9). *Verdict*: 5 ("fine i guess? somewhat unsure"), 6 ("lean fine"), 7, 8, 9 fine; rule B, which withdraws the exemption where she wants to keep her view, is rejected by 5 and 6. *Review*: 13 objects to the exemption itself, since an engineered procedure and an illuminating argument are treated alike; 14 asks that the words say an unfamiliar experience does not make every effect delivered with it her own response. That reading is adopted (`DECISIONS.md`, `2026-11-26--legitimacy-twentieth-followup-readings`); the words are unchanged. Nothing tests where "could not have judged" falls: it is as he takes her to be | His verdict on a case where the unfamiliar thing and a separate effect come together; a case on which he withdraws "lean fine" on 6 | 152 |
| 6 | Her judgement, not her prediction | living note | Position 3; confirmed on case 13, "wrong", where the prediction reading says fine | — | — |
| 7 | Taking up an offer, unpressed and told what it is hoped to do, is asking; merely not stopping him is not | living note | Position 6 ("yeah go for that"). *Verdict*: 8 ("fine, as long as he doesn't force her to go (and tells her the point of the trip)"), 12 ("seems fine to me (again no force, she agrees to taste)"), 20. Not ruled: whether her asking makes a thing not manipulation or merely permitted | A case of pressed uptake on which he says fine; the ruling | — |
| 8 | A passing state is not a settled decision | living note | Positions of 24 November. *Verdict*: 16 ("Hmmm i feel unsure here but lean wrong"), 17 fine. *Coding*: run 16, where `byron-tunnel-vision` is not convicted and `missed-train-paternalistic` is | His verdict on 16 hardening the other way | — |
| 9 | What makes a decision of hers settled | open | None. It is supplied in every episode and every coding sheet. One candidate, untested: a check-in settles it | A stated criterion, applied to the hard cases and the interpretation's episodes with the verdicts unchanged | 152 |
| 10 | Help is not counted; breaking a tie is not leading her against her judgement | living note | Consequence 4. *Verdict*: 17. *Coding*: of the 8 controls run 17 convicts, sheet 16 codes her earlier rating as not lower or as no view on 6 | A case of help he calls wrong | — |
| 11 | Whose view is used where: his for what he owes her, hers for what counts as working on her; everything as he takes it to be | living note | Positions of 22–23 November. *Review*: 12, 13 and 14, each asked, report no necessary appeal to external truth, to his accuracy or to good values; 12 adds that the mechanisms of her mind must be part of his picture for a sincere adviser who is wrong about them to pass; 13 that "settled", "could not have judged" and "asked" are choices about whose judgement governs | A case whose verdict changes with the facts while his beliefs are held fixed | 139 |
| 12 | He can ask: her view of the hypothetical is a question that can be put to her, and asking both elicits and settles it | living note | *Reasoning*. It is what makes the cost of the rule on a single repetition (consequence 11) one he can avoid. *Review* 13: mixing her state in one course with observations from another needs answers to questions that could not be put to her in either | A case where asking is itself the pressure | 147 |
| 13 | What he does to her options is her authority's: what stopping costs her, bundling, penalties, payments, threats, starting over her refusal | living note | Ruled 24 November, on the condition that the authority side can carry it easily. *Review* 14, episode B: an uptake obtained by a threat is licensed as asking unless "unpressed" is enforced, so the line leans on that word | Row 52 delivered, or shown not deliverable | 149 |
| 14 | Accepted consequences 1 to 11 of `LEGITIMACY_STATEMENT.md` §5 | living note | The maintainer's positions. *Exact*: the interpretation's episodes include one for each of 2, 3, 4, 6, 7, 8, 9, 10 and 11 (`interpretation/INTERPRETATION.md` §2). Consequences 1 and 5 have none: no episode has a drift over many decisions or an adviser who is wrong about her | A case on which a consequence gives a verdict he rejects | 154 |
| 15 | What his lights are, for a trained system: what it believes and expects | open | None. Consequence 5 makes the verdict rest on his picture entirely | A stated procedure that reads his picture off a system, with an instance in which a system that misreports it is caught and one in which it is not | 139 |

## 2. The formal statement

`LegitimacyStatement.lean`. A closed row says the declaration is kernel-checked as stated;
each names the term that inhabits its hypotheses.
`followup-20-registration.patch` in the round's prompts directory prepares rows 17 to 28 for
the registry.

| # | component | verdict | evidence, and its kind | what would move it | item |
|---|---|---|---|---|---|
| 16 | The five definitions (`Episode`, `NothingUntold`, `NothingBehind`, `CanStop`, `Legit`) as a rendering of the three sentences | open | *Reasoning*: each clause is a sentence's with its notions as fields. No review has seen the file; the five formal objects that reviews have seen were each found not to say what the sentences say. Renderings chosen here: sets on offer count with untold ones in sentence 1; the stop is asked at her decisions; "from before he starts" is a field | An outside review of the file against `LEGITIMACY_STATEMENT.md` §1 and §2 that finds no difference, or each difference repaired or recorded | 153 |
| 17 | Larger tolerances only loosen it | closed | *Kernel*: `Episode.Legit.mono`; inhabited by `Witness.legit_looser` | The shared event | — |
| 18 | No conduct and every view told is legitimate at every tolerance | closed | *Kernel*: `Episode.legit_of_nothing`; inhabited by `Witness.idle_legit` | The shared event | — |
| 19 | What his silence cannot cost her: under sentence 1, an option within `ε` of the best she rates is within `ε + 2θ` of the best she would rate on being told anything untold, and within `ε + 3θ` of any option the telling would show her | closed | *Kernel*: `Episode.informed_choice`; its first half inhabited by `Witness.informed_instance`. No term has an option revealed, so the second half has no instance. It is a statement in her ratings as he takes them, at one decision | The shared event | — |
| 20 | Under sentence 2 his weight on any non-empty set of unasked things he does to her leading her against her judgement is at most `κ` | closed | *Kernel*: `Episode.against_le`; inhabited by `Witness.against_instance`. It restates the clause; `pAgainst` is a field | The shared event | — |
| 21 | Something untold that would move a rating by more than `θ` refutes legitimacy | closed | *Kernel*: `Episode.not_legit_of_untold`; inhabited by `Witness.not_legit_untold` | The shared event | — |
| 22 | A thing he does to her that she cannot pick out refutes it | closed | *Kernel*: `Episode.not_legit_of_covert`; inhabited by `Witness.not_legit_covert` | The shared event | — |
| 23 | Keeping from her something from someone else, where she cannot pick that out, refutes it | closed | *Kernel*: `Episode.not_legit_of_withheld`; inhabited by `Witness.not_legit_keeps` | The shared event | — |
| 24 | His weight beyond `κ` on unasked things he does to her leading her against her judgement refutes it | closed | *Kernel*: `Episode.not_legit_of_against`; inhabited by `Witness.not_legit_against` | The shared event | — |
| 25 | A thing he does to her, in play at a decision at which she cannot stop it, refutes it | closed | *Kernel*: `Episode.not_legit_of_unstoppable`; inhabited by `Witness.not_legit_unstoppable` | The shared event | — |
| 26 | Where she asked for everything he does, sentence 2's second half imposes nothing | closed | *Kernel*: `Episode.asked_unconstrained`; inhabited by `Witness.requested_behind`, with `Witness.requested_legit`: his weight on leading her against her judgement is 1 and the episode is legitimate, where unasked a weight of 1/2 is not | The shared event | — |
| 27 | The statement is inhabited, and each sentence can fail alone | closed | *Kernel*: `Witness.legit` at `θ = κ = 1/10`, with the four neighbours of rows 21, 22, 24 and 25, each differing from it in one value. The witness has one decision, no view on offer or declined, no option revealed | The shared event | — |
| 28 | The scoring link: histories read as episodes give a `DeconfusingCorrigibility.Scoring` whose predicate is `Legit`, scoring her rating on a legitimate history and in `[−δ, 0)` on an illegitimate one | closed | *Kernel*: `legitScoring`, `legitScoring_S_of_legit`, `legitScoring_S_of_not_legit`, through `LegitimacyGate.gatedScoring`; inhabited by `Witness.scoring_open`, `Witness.scoring_covert`. The map from histories to episodes, the violation count and her rating are data, and `Scoring`'s theorems hold for any predicate | The shared event | — |
| 29 | What "taken as given" leaves unestablished | open | The statement relates the fields by the three definitions and nothing else. Not established, and not required by any theorem: that `told`, `offered`, `declined` lie within `views`; that a view in `offered` is properly on offer or a decline in `declined` stands; that `pAgainst` and `pNoStop` lie in `[0, 1]`, or that `pAgainst` does not fall when a thing is added to the set; that `inPlay` is an interval beginning before the thing starts; that `canStop` is of an option she has; that `asked` was unpressed; that `doesToHer` is false of what she could not have judged in advance or of help. So an episode with `doesToHer` false throughout satisfies sentences 2 and 3 whatever he does, and the theorems of rows 17 to 28 say nothing against it. Nothing shows that any procedure producing the fields from a history yields an `Episode` on which `Legit` is the verdict the sentences give | Lean statements of the properties each field must have, with the witness satisfying them and a term violating each; then row 49 | 156 |

## 3. The interpretation

`interpretation/`: the fifth design, on histories, with its exact model. One row per notion
the statement takes as given, saying how the design works it out and which known fault bears
on it (rows 30 to 39); one per fault (rows 40 to 46, the letters those of
`interpretation/INTERPRETATION.md` §3); then the model's standing.

| # | component | verdict | evidence, and its kind | what would move it | item |
|---|---|---|---|---|---|
| 30 | A decision of hers, and which are settled | open | Every step of hers is a choice; the settled ones are a supplied set of steps. *Review* 13: whether "settled" is a property of a state or a list of times, and which decision is the last settled one when the comparison course has different decisions, are not fixed | Row 9 | 152 |
| 31 | Her rating, and her rating were she told a set of his views | open | Her state gives a rating of an option, possibly absent; being told is conditioning on the observation of his stating the views. *Review* 12, 13, 14: a set of views does not fix an observation, manner and order being part of what she observes; ratings are on one fixed cardinal scale, against which the tolerances are compared; what an absent rating does in a difference or a maximum is not stated everywhere | A specified telling act for each set of views, or the rule quantified over tellings; a statement invariant under a change of scale, or the scale convention stated | 157 |
| 32 | Told, properly on offer, declined | open | Computed from the history: told if some act stated it; properly on offer if hearing is on her menu, the bearing told is still accurate and asking to hear leaves her as telling would, her other options still there; declined if she took the act of declining and the bearing is as told. *Exact*: `episodes_core` 28 to 32. Not handled: making her forget what was told; a view he comes to hold later; a bearing that depends on what else she has heard (*review* 13) | Episodes for each of the three with the verdict the sentence gives | 157 |
| 33 | A thing he does, and that it does something to her | open | A site, one act at one step. It bears an effect if it is needed for some difference between the actual course and the course rerun with her mind moving by her conditioning alone at a set of sites. Faults A, C and D | Rows 40, 42, 43 | 157 |
| 34 | That it keeps something from her | open | After the act an item or option from someone else is missing that would have been there had he done nothing at that step. *Exact*: `episodes_review12` 3, 4. *Review* 14: the act of doing nothing is not defined | The null act defined | 157 |
| 35 | She can pick it out | open | What she observes at the site is something she would not observe, in any case he gives weight to, had he done nothing to her at that step. Fault F. *Review* 14: that an observation differs does not give her knowledge of what it means | Row 45 | 157 |
| 36 | She asked | open | She took the option of asking for the act, or took up his offer of it, before it. Fault B: whether she was pressed is not looked at | Row 41 | 157 |
| 37 | His weight on leading her against her judgement | open | The weight, by his belief at the first site of a set she did not ask for, of the cases in which her shortfall against her reference self exceeds that in the comparison course by more than `η`. Faults D and E. *Review* 14: his belief is his starting weights conditioned on the record of acts, so what he privately observes is not in it | Rows 43, 44; his information represented | 157 |
| 38 | In play, and she can stop it | open | A covered site (one bearing an effect, or one whose observation she could not have judged in advance) still to come; an option she takes to stop him after which he acts at no further covered site. Faults G and H. An effect that falls between two of her steps has no stop asked of it | Row 46 | 157 |
| 39 | His weight on her not stopping | open | The share, by his belief at the step, of the cases where the best stopping option is rated strictly above her other options and she does not take one. *Exact*: `episodes_core` 10, `episodes_review12` 9. No fault known | An episode on which it gives the wrong verdict | 157 |
| 40 | Fault A: an unfamiliar observation exempts the whole site, so a hidden mechanism delivered with it passes | open | *Exact*: `known_faults` A; the sentences say fails, the model gives holds. The reading of row 5 is what the model does not implement | The response to what is observed represented apart from other effects of the act, with A failing and `episodes_views` 5, 10 and `episodes_review13` 3 still holding | 157 |
| 41 | Fault B: uptake obtained by a threat counts as asking | open | *Exact*: `known_faults` B; fails, holds | "Unpressed" computed, with B failing and the hard cases 8 and 12 still holding | 157 |
| 42 | Fault C: a hidden act disabling a response of hers shows only against a supplied list of what others might show her | open | *Exact*: `known_faults` C; fails, holds; with the warning on the list (`episodes_review12` 5) it fails as it should | The probes exhaustive for a stated domain, or equivalence of her future responses defined directly | 157 |
| 43 | Fault D: what she later learns by her own choice is counted as an effect of his earlier aid | open | *Exact*: `known_faults` D; holds, fails, by three clauses | His act compared with her mind as it would have been through the same actual events, in place of a whole course rerun | 157 |
| 44 | Fault E: an aid that brings her to a better menu on which she takes the second best counts as leading her against her judgement | open | *Exact*: `known_faults` E; holds, fails | A comparison of what she chooses, not of regret against the menu each course reaches | 157 |
| 45 | Fault F: she can tell only by what she observes at that step | open | *Exact*: `known_faults` F; holds, fails | What she can tell from all she has observed, with F holding and `episodes_review13` 10 still failing | 157 |
| 46 | Faults G, H: a stop must end everything; two influences each with its own working switch fail | open | *Exact*: `known_faults` H; holds, fails. G, the review's own encoding, holds for a reason beside the point (`interpretation/INTERPRETATION.md` §3) | Stopping indexed by the thing stopped, with H holding and `episodes_core` 8 still failing | 157 |
| 47 | Five things the design leaves undetermined | open | *Review* 14, none an episode: a conditioning of her whole state from a judgement about ratings; an observation from a set of views; the act of doing nothing; his information beyond the record of acts; the supplied functions on histories only the comparison course reaches | Each defined, or the design restricted to where it is determined | 157 |
| 48 | The model's verdicts on its episodes | closed | *Exact*, the runner: 68 episodes each with the expected verdict, and 8 of known faults each with the recorded one. The model was corrected against 64 of the 68, three episodes were re-encoded when a rule changed, and model and episodes are by one hand: this row says the model has not moved, not that it is right | The runner fails on `interpretation/INTERPRETATION.md` | — |
| 49 | The history model as an instance of the formal statement | open | None. The model is in Python; no map from a history to an `Episode` is written; with seven known wrong verdicts a proof that the model's verdict is `Legit` of such an episode would carry the faults into the instance | A Lean construction of an `Episode` from a history, after rows 40 to 46, with the properties of row 29 proved of it | 156 |
| 50 | The model on a table of his moves (`LegitimacyModel.lean`, with `LegitimacyCase.lean`, `LegitimacyWitness.lean`, `LegitimacyCases.lean`) | living note | An earlier interpretation, in Lean. *Kernel*: its theorems hold of its definitions, among them its verdicts on the 41 cases of `LEGITIMACY_CHECKS.md`. *Review* 10 rejected it as a rendering of the three sentences: its pressure clause scores, with her scoring from before he began, the courses he expects her options to lead to, and never reads her rating of them, so that on fields no clause forbids open nagging passes and a reminder that helps her fails; it compares net weights, so harm in one case is offset by help in another; and a change in her that is restored before her next decision is unseen. Forty-four claims of the reply were checked by hand against the definitions and all held (the report, AH.2). It is not repaired, and each file says so at its head | — | — |

## Around the statement

| # | component | verdict | evidence, and its kind | what would move it | item |
|---|---|---|---|---|---|
| 51 | The quality of the evidence | living note | Every coder and every reviewer is a language model; no person has read a case against its coding. The only judgements by a person are the maintainer's twenty verdicts, of which he marks two unsure and four as leanings. The three sentences, both formal statements, the interpretation's design, model and 68 episodes, and the twenty hard cases with the four rules' verdicts are by one hand, sessions of one model with the maintainer. Sheets 11 and 16 are coded twice, by coders of different models who read the same paraphrases; sheets 14, 15 and 17 once, sheet 17's coder's model unrecorded. Run 17's one failed prediction was repaired by a combination written after the result. Each outside review saw only its brief, and reviews 10 to 14 each found the formal object before it unfaithful; none has seen `LegitimacyStatement.lean`. The model was corrected against the episodes that now pass | Items 148 and 153 delivered | 148, 153 |
| 52 | The cost of a decision of hers, on the authority side: what stopping costs her, bundling, penalties, payments, threats, starting something over her refusal | open | *Kernel*, of an earlier round: `EffectiveAuthority.lean` has the cost of an exercise of hers against a bound and a shortfall the agent caused; it has no cost he attaches to one of her options, no bundle and no refusal. *Exact*: a candidate clause, `STOPPING_COST.md`, 20 cases by one hand, connected to no Lean. Not ruled: a free service paid for by its influence, and an exit penalty she agreed to in advance | A Lean statement on `AuthorityModule`'s objects under which a penalty, a payment to continue, a bundle and a threat are each a caused shortfall or shown not to be; the two rulings | 149 |
| 53 | Composition with the sequential corrigibility theorems | open | None. `legitScoring` gives the one-decision `Scoring`; nothing relates `Episode`, which is his picture of one stretch, to `DeconfusingCorrigibility.Sequential`, whose evaluations are realised | A structure instantiating `Sequential` from a sequence of episodes, with `theorem3a` applied and the hypothesis relating his picture to the realised evaluation named | 150 |
| 54 | The gate theorem: a gate passing illegitimate conduct with probability at most `ρ` and legitimate conduct with probability at least `1 − ρ'` gives legitimate conduct the strictly higher expected gated score when `ρ(1 − w) < −w(1 − ρ')` | closed | *Kernel*: `LegitimacyGate.gate_gives_behaviour`, with `gate_threshold_delta`, `gate_threshold_sharp` and the instance `gate_instance`. A statement about seven real numbers | The shared event | — |
| 55 | Soundness of the gate: whether legitimacy can be evaluated at all | open | None. `Legit` is a property of his picture, so a gate needs that picture or a proxy for it, and by consequence 5 nothing in her record refutes a sincere adviser. One handle, untried: sentence 2 is fixed by her answers to questions that can be put to her (row 12), so a gate may ask her | For one stated observation model, the error probabilities a stated procedure attains, or an instance in which two pictures with different verdicts leave the same record | 147 |
| 56 | Judgement bent for a while: she gives in thinking it best then | open | *Coding*: 4 of 152 cases coded so on sheet 16 and 10 on its second coding, none with a lapse expected. *Verdict*: cases 2, 10 and 16. *Exact*: `episodes_review12` 1 | A set of cases of bent judgement with published verdicts, coded twice under sheet 17 with her earlier rating asked, and scored | 154 |
| 57 | Coverage of value change | open | The statement has no clause for value change and has not been run on a value-change case. *Coding*, of two earlier forms (`CASE_RUNS.md`): on 90 published cases the clause settles 28 or 29 and agrees on 23. *Verdict*: cases 6, 18 and 20 are changes of what she values | The statement coded on those sets under a sheet written for it | 155 |
| 58 | The accounts this one replaced | living note | `CURRENT.md` §2 lists each with what it failed on. The fifteen results registered from earlier follow-ups are statements about her condition and about scoring, do not mention a replaced definition of legitimacy, and stand | A registered claim found to depend on a replaced definition | — |

## Where the remaining work should go

The open rows, ranked. *Size*: S a day's round, M several, L a programme of its own.

1. **Properties the given notions must have, stated in Lean** (row 29; item 156, first
   part). Done when `LegitimacyStatement.lean` or a file beside it states each property of
   row 29 as a predicate on `Episode`, the witness is proved to satisfy them, a term is given
   violating each, and the `lean` job is green. S to M. Dispatchable.
2. **An outside review of the Lean statement** (row 16; item 153). Done when a fresh,
   sandboxed session given `LegitimacyStatement.lean` and `LEGITIMACY_STATEMENT.md` §1 and §2
   has answered where they differ, and each finding is checked and repaired or recorded. S.
   Needs the maintainer to run the outside model. After entry 1.
3. **The cost of a decision of hers on the authority side** (rows 13, 52; item 149). Done
   when a Lean statement over the authority module's objects decides a penalty, a payment, a
   bundle and a threat, with the 20 cases of `STOPPING_COST.md` as instances. M. Needs two
   rulings for its edge cases; the four named kinds do not wait on them.
4. **Composition with the sequential theorems, on `Episode`** (row 53; item 150). Done when
   `Sequential` is instantiated from a sequence of episodes with `theorem3a` applied. M.
   Dispatchable.
5. **The interpretation's faults** (rows 31 to 47; item 157). Done when each of the eight
   episodes of `known_faults.py` gets the verdict the sentences give, the 68 keep theirs, and
   an outside review of the repaired design is on record. In order of what the fourteenth
   review ranks: the response to an unfamiliar thing apart from other effects of the act
   (A); his act compared with her mind as it would have been through the same actual events
   (D, E); unpressed uptake (B); what she can tell from all she has observed (F); stopping
   each thing (G, H); the probes (C). M to L. Dispatchable; the review needs the maintainer.
6. **The history model shown to be an instance of the statement** (row 49; item 156, second
   part). Done when a Lean construction gives an `Episode` from a history and the properties
   of entry 1 are proved of it. M. Dispatchable, after entry 5.
7. **What makes a decision settled** (rows 9, 30; item 152). Done when a criterion is stated
   and the hard cases and episodes keep their verdicts under it. S once there is a
   criterion. Needs the maintainer: it is a choice about whose judgement governs.
8. **Cases of bent judgement, and of value change** (rows 56, 57; items 154, 155). Done when
   each set is coded twice and scored. S each. Dispatchable; the cases must be gathered from
   published sources.
9. **A person's check of a sample of the codings** (rows 1, 2, 51; item 148). Done when one
   person has answered a sample before seeing the recorded answers and the agreement is
   counted. S. Needs a person and the book.
10. **Soundness of the gate** (row 55; item 147). Done as row 55 says. L. Dispatchable as
    stated; that he can ask her is the handle to try first.
11. **What his lights are for a trained system** (row 15; item 139). L. Needs the maintainer.

The dispatch of this follow-up ranked: properties of the given notions in Lean together with
the history model as an instance; the authority-side cost; composition; the interpretation's
faults; a person's check and the cases of bent judgement; soundness of the gate. This ranking
differs in four ways. The first entry is split and its second half put after the faults: a
proof that the model's verdict is `Legit` of an episode would, with seven known wrong
verdicts, prove the faults into the instance. A review of the Lean statement is added at
second place: each of the five formal objects a review has seen was found unfaithful, this
one has been seen by none, and it is a day's work. What makes a decision settled is added:
every verdict of sentence 2 turns on it and it is supplied everywhere. And a person's check
is below the two case sets because no round can do it.

## Counts

Rows closed: **14**. Rows open: **28**. Rows a living note: **16**.
