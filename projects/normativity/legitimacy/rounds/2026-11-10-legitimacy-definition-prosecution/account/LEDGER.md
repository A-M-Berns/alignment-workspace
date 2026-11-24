# Ledger of the legitimacy line (2026-11-24)

One row per component of the line as `LEGITIMACY_STATEMENT.md` states it. A verdict is
**closed** (a Lean declaration or a checker invocation stands for it, with the event that
reopens it), **open**, or **living note** (a position or a description, held and revisable,
that no check adjudicates). *Lean* is `lean/Workspace/Deference/Contrib/LegitimacyModel.lean`,
namespace `Workspace.Deference.Contrib.LegitimacyModel`; none of its declarations is
registered. *The runner* is `python3 run.py` in the round directory. Items are those of
`ATTENTION.md`. Paths are relative to this directory.

Kinds of evidence, strongest first: **kernel** (kernel-checked, of the declaration as stated);
**exact** (an exact check whose inputs a case supplies); **coding** (a blind coding by one
language model against a scorer written first); **review** (the outside model, *blind* for
reviews 8 and 9, *not blind* for reviews 2 to 7); **reasoning** (argument only).

Closed rows share one reopening event unless they name another: `python3 tests/audit_axioms.py`
fails on the declaration, or a commit changes its statement or the statement of a definition it
mentions.

## The statement

| # | component | verdict | evidence, and its kind | what would move it | item |
|---|---|---|---|---|---|
| 1 | The diagnosis: her mistakes are judged by his lights; his view says what he owes her and is never where she ought to end up | living note | The maintainer's position 1. *Kernel*, by inspection of the definitions: every clause of `Model.Legit` is stated on his weights `μ` and the fields of his picture, and `Model` has no field for the facts. *Review*: reviews 8 and 9 (blind), asked directly, each report no place where his accuracy, a standard of truth or a standard of good values is required, and no earlier reply reports one | A review or a case naming a clause whose verdict changes with the facts while his beliefs are held fixed | 139 |
| 2 | What his lights are, for a trained system: what it believes and expects | open | None. `μ` and the courses he expects are fields of `Model`; consequence 5 (a sincere adviser who is wrong passes) makes the verdict rest on them entirely | A stated procedure that reads `μ` and the courses off a system, with an instance in which a system that misreports its picture is caught and one in which it is not | 139 |
| 3 | Sentence 1 as worded: nothing untold that matters | living note | Frozen by the maintainer (position 12). *Coding*, run 11: of 240 bank cases with a definite verdict the disclosure rule settles 219 and agrees on 214, missing none and convicting 5 against the author; the rule was formed with these cases in view (ten earlier sheets) and each case has one coding. On forty cases an outside model wrote it agrees on 38 | A second coder's answers on run 11's sheet differing from the first on more than the five disagreements with the author; the maintainer's rewording | 154 |
| 4 | Sentence 1's formal counterpart: what is untold, proper offers, declines (F1) | open | *Exact*: `LEGITIMACY_CHECKS.md` C3 to C7 and D1 to D11, where an offer's validity is computed from supplied ratings and a decline's from two supplied flags. *Kernel*: `Model.untold`, `ProperOffer`, `DeclineStands`, `F1` as definitions; `Model.not_legit_of_untold`. *Review*: review 8 (blind) found that an offer could hide its own relevance, review 9 (blind) that it could lose the option it would show her and that a decline survived a change in what the view mattered; each is repaired in the statement, and no review has seen the repaired rule. Not ruled: whether he must mention an option of someone else's that he believes she would rate higher (the statement says yes). Not taken from review 9: interaction between a view on offer and a view untold. No case has a flood of offers | An outside review of the offer and decline rule as it stands that finds no construction passing it against the words of sentence 1; a Lean instance with a view in which F1 does work (row 20) | 153, 151 |
| 5 | The line between legitimacy and authority: what he does to her options (the cost of stopping, bundling, penalties, payments, threats, starting over her refusal) is her authority's | living note | Ruled by the maintainer (position 9), on the condition that the authority side can carry it easily. *Review* 9 (blind): the line is defensible; influence on salience or affect that changes her deliberation without her acting against any rating falls between the two, and "an incentive that makes complying her best option" is no definition of coercion. *Exact*: A5, A9, B11 pass the statement, as the ruling intends, by a case stating that nothing in her changes | Row 30 delivered, or shown not deliverable: the condition of the ruling | 149 |
| 6 | Sentence 2, first half: each thing that changes her, or keeps from her what comes from someone else, she can pick out (F2) | open | *Exact*: A1 to A12, C1, C2, C4, with how she scores and her gaps supplied for each subset of his moves. *Kernel*: `HerDiff`, `Contributes`, `Bears`, `InPlay`, `F2` as definitions; `Model.not_bears_of_inert`, `not_legit_of_unknown`; the witness of row 20. *Review*: reviews 8 and 9 (blind) each found over-reach (a reminder that only helps; refusing to lend his own car), repaired by comparing his actual conduct with a set removed and by counting only a change in her; no review since. No bank run codes this half: run 14's question whether the pressure is open is the nearest. What she can pick out is a field | A bank coding of whether she can pick the thing out, scored against the author's verdicts on covert influence; a Lean instance in which a seen change in what an option leads to is shown to be no `HerDiff` | 151, 154 |
| 7 | The pressure clause: other than by telling, nothing he expects to lead her to choose what she rated lower at her last decision before he began, unless she asked (F2′) | open | Ruled in principle (positions 10, 11). *Coding*, run 16: on the 39 bank cases with a lapse expected the clause settles 33 and agrees with the author on all 33; on 69 controls it settles 64 and convicts 1. One coding; her earlier rating is unclear on 65 of the 152; the subsets are fixed by run 11's coding. Three questions worded alike on sheets 15 and 16 were answered alike by the two coders on 142, 142 and 148 of 152. *Exact*: B1 to B11, the chance of going against her earlier rating supplied. *Kernel*: `LastBefore`, `earlier`, `Against`, `F2'` as definitions; `Model.not_legit_of_against`. No review has seen the clause: review 9 raised the case that led to it. Not ruled: whether "unless she asked" is right | A second coding of sheet 16 changing the 33 of 33 or the single control; a case in which the chance is derived from her earlier state and not supplied | 154, 151 |
| 8 | Judgement bent for a while: she gives in thinking it best then | open | The thinnest part. *Coding*: 2 of 152 cases coded as bent on sheet 15 and 4 on sheet 16; of the 4, the clause settles 2 and convicts 1; none is among the 39 with a lapse expected, so the prediction written for it was untested twice. *Exact*: B2 and B5, where the verdict is the supplied number. *Reasoning* otherwise | A set of cases of bent judgement with published verdicts, coded by two coders, on which the clause's verdicts are counted | 154 |
| 9 | Sentence 3: she can stop it (F2's stop, F3) | open | *Exact*: A6, A7 (no stop), A8 (he expects she would not manage to; the chance supplied). *Kernel*: `PrefersStop`, `F3` as definitions; `Model.not_legit_of_unstoppable`. With the cost of stopping gone the sentence asks for a stop and that she is not too weak-willed to use it (review 9, and the statement's own list). Stopping is required at her decisions only; a move running between two decisions has no stop asked of it there (reviews 8 and 9; not changed). What counts as a decision of hers is a primitive | The setting saying what a decision is, with an instance of a move between decisions; row 30 for what stopping costs | 152, 149 |
| 10 | Accepted consequences 1 to 8 of `LEGITIMACY_STATEMENT.md` §5 | living note | The maintainer's positions 8 to 11. *Exact*: 2 (B4, B5), 3 (D1 to D5), 4 (A1), 6 (A5, A9, B11) and 7 (B1, B2) each have a case; 8 has the coding of run 16, where `byron-tunnel-vision` is not convicted and `missed-train-paternalistic` is. Consequences 1 and 5 have none: no check has a drift over several decisions or an adviser who is wrong | A case, published or written, on which a consequence gives a verdict the maintainer rejects | 154 |

## The Lean model

A closed row says the declaration is kernel-checked as stated. Rows 11, 15, 18, 19, 28 and 29
also have a term of the file inhabiting their hypotheses, and are what
`followup-16-registration.patch` in the round's prompts directory prepares for the registry.
Rows 12, 13, 14, 16 and 17 have none: no model in the file has an inert move, an empty
conduct, a view, an empty set of stops or a move that raises the weight of going against her
earlier rating. Until one does they are `unverified-nonvacuous` and cannot be promoted; item
151 asks for the terms.

| # | component | verdict | evidence, and its kind | what would move it | item |
|---|---|---|---|---|---|
| 11 | Redescription: `Legit` is unchanged by any bijective re-description of her state | closed | *Kernel*: `Model.legit_transport`. It covers her state only: not a rescaling of her scores, against which the tolerances are compared, not his conduct cut into other moves, not a renaming of options or views | The shared event | — |
| 12 | A move whose removal from any course changes neither her state, her gaps, what reaches her from others, nor whether she departs bears no effect | closed | *Kernel*: `Model.not_bears_of_inert` | The shared event | — |
| 13 | No moves and nothing untold, on offer or declined is legitimate | closed | *Kernel*: `Model.legit_of_nothing` | The shared event | — |
| 14 | Something untold that would move her rating by more than `θ` refutes legitimacy | closed | *Kernel*: `Model.not_legit_of_untold` | The shared event | — |
| 15 | An effect-bearing move in play that she cannot pick out refutes it | closed | *Kernel*: `Model.not_legit_of_unknown` | The shared event | — |
| 16 | An effect-bearing move in play with no way to stop it refutes it | closed | *Kernel*: `Model.not_legit_of_unstoppable` | The shared event | — |
| 17 | Leading her against her earlier rating, by moves neither asked for nor tellings, refutes it | closed | *Kernel*: `Model.not_legit_of_against` | The shared event | — |
| 18 | One open, stoppable influence is legitimate at `θ = 0`, `η = 1/4`, `κ = 0` | closed | *Kernel*: `Witness.legit_open`, with `Witness.bears` that the move bears an effect | The shared event | — |
| 19 | The same influence done covertly is not legitimate | closed | *Kernel*: `Witness.not_legit_covert` | The shared event | — |
| 20 | That the statement is inhabited with every clause doing work | open | *Kernel*, by what the witness is: on it only the start rule and F2 do work. He has no views, so F1 and the offer and decline conditions have nothing to check; she never goes against her earlier rating (`Witness.not_against`) and never rates stopping higher (`Witness.not_prefersStop`), so F2′ and F3 hold with both weights zero. The four refutations show each clause can fail, not that all can hold together non-trivially | A Lean term of `Model` with a view on offer, a move that changes her act and a case in which she rates stopping higher, proved `Legit`, each clause shown to fail on a neighbouring term | 151 |
| 21 | That the model's verdicts are the statement's on the cases of `LEGITIMACY_CHECKS.md` | open | None: the 41 cases are computed by `legitimacy_checks.py`, which is a separate transcription of §4 by the same hand, not by the Lean predicate | Each of the 41 cases as a term of `Model` with `Legit` proved or refuted, the verdicts equal to the table's | 151 |
| 22 | Simplification 1: a view's bearing is computed per view, not jointly with his other views | open | *Kernel*, by inspection: `BearingHolds` tells `{v}` alone | The definition quantifying over sets containing the view, with a model on which the two differ | 151 |
| 23 | Simplification 2: he has one belief, not one at each time | open | *Kernel*, by inspection: one `μ` and one family of courses. The start rule's repair after review 9 (he must already have believed the move effect-bearing at an earlier decision) is therefore not in the model | Beliefs indexed by time, with the instance of review 9 (a move he learns at its start to be effect-bearing) refuted | 151 |
| 24 | Simplification 3: "beyond what plainly telling would do" is a set of moves marked as tellings | open | *Kernel*, by inspection: `F2'` excludes sets meeting `tellings` | A move's effect split into what telling its content would do and the rest, with B10 (a telling whose manner does more) as an instance | 151 |
| 25 | Simplification 4: "silent where she had no earlier rating" is not represented | open | *Kernel*, by inspection: `ρ` scores every course from every state. On the bank her earlier rating is "no view" on 22 of 152 cases (sheet 16) | A partial rating in the model, with B6 as an instance | 151 |
| 26 | Simplification 5: what is on offer is a set he designates and that `Legit` requires proper, not the largest proper set | open | *Kernel*, by inspection: `offered` is a field | The largest proper set defined, and `Legit` shown unchanged or an instance on which it differs | 151 |
| 27 | Four further respects found in this pass: `stops` is a field and nothing says an option in it ends a move; `known`, `asked` and `dec` are fields; the clauses hold in every case of `Ω`, weight zero included, and the weights need not sum to one; `DeclineStands` asks that the view was once on offer, not that she declined it | open | *Kernel*, by inspection of the definitions | Each removed or stated as a hypothesis of the theorems that need it | 151, 153 |
| 28 | The gate theorem: a gate passing illegitimate conduct with probability at most `ρ` and legitimate conduct with probability at least `1 − ρ'` gives legitimate conduct the strictly higher expected gated score when `ρ(1 − w) < −w(1 − ρ')` | closed | *Kernel*: `gate_gives_behaviour`, with `gate_threshold_delta` (at `ρ' = 0`, `w = −δ`: `ρ < δ/(1+δ)`), `gate_threshold_sharp` and the instance `Witness.gate_instance`. It is a statement about seven real numbers: nothing in it mentions `Model` | The shared event | — |
| 29 | The scoring link: histories read as models give a `DeconfusingCorrigibility.Scoring` through `Legitimacy.gateValue`, scoring her rating on a legitimate history and in `[−δ, 0)` on an illegitimate one | closed | *Kernel*: `legitScoring`, `legitScoring_S_of_legit`, `legitScoring_S_of_not_legit`; inhabited by `Witness.scoring_open`, `Witness.scoring_covert`. The map from histories to models, the violation count and her rating are data, and `Scoring`'s theorems hold for any predicate | The shared event | — |

## Around the statement

| # | component | verdict | evidence, and its kind | what would move it | item |
|---|---|---|---|---|---|
| 30 | The cost of a decision of hers, on the authority side: what stopping costs her, bundling, penalties, payments, threats, starting something over her refusal | open | *Kernel*, of an earlier round: `EffectiveAuthority.lean` has the cost of an exercise of hers against a bound (`attnCost`, `Short`, monotone in the cost table: `short_mono`), a shortfall the agent caused as one present after its move and absent after idling (`FloodShortfall`, `Dep.build_caused_iff`), and revocation as a matter with a cost bound that a dependency built through delegated work can push past (`revocationEntry`, `RevocationCaused`, `Dep.atrophy_on_module`). It does not have: a cost that he attaches to one of her options (a penalty, a payment, a threat), a thing bundled with another, or her refusal. Its comparison is with his idling; the candidate clause's is with the best course he could bring about with the thing stopped. *Exact*: that candidate, `STOPPING_COST.md`, 20 cases by one hand, connected to no Lean. Not ruled: a free service paid for by its influence (the candidate fails it), and an exit penalty she knowingly agreed to that he can no longer call off (the candidate passes it) | A Lean statement on `AuthorityModule`'s objects under which a penalty, a payment to continue, a bundle and a threat are each a caused shortfall or shown not to be, the 20 cases as instances; the two rulings | 149 |
| 31 | Composition with the sequential corrigibility theorems | open | None. `legitScoring` gives the one-decision `Scoring`; nothing relates `Model`, which is one episode in his picture, to `DeconfusingCorrigibility.Sequential`, whose evaluations are realised | A structure instantiating `Sequential` from a sequence of models, with `theorem3a` applied and the hypothesis relating his picture to the realised evaluation named | 150 |
| 32 | Soundness of the gate: whether legitimacy can be evaluated at all | open | None. `gate_gives_behaviour` takes the two error probabilities as numbers. `Legit` is a property of his beliefs, so a gate needs his picture or a proxy for it, and by consequence 5 nothing in her record refutes a sincere adviser | For one stated observation model, the error probabilities `ρ`, `ρ'` that a stated procedure attains, or an instance in which two pictures with different verdicts leave the same record | 147 |
| 33 | Coverage of value change | open | The statement has no clause for value change (position 4) and has not been run on a value-change case. *Coding*, of two earlier forms on 23 November (`CASE_RUNS.md`): on 90 published cases the clause settles 28 or 29 and agrees on 23; on 20 adversarial cases of the outside model it settles 17 and agrees on 14; no criterion's verdict moved with a discovery-or-change wording in 10 pairs. The published cases mostly do not state what she knew, whether she could stop, or what was untold | The statement coded on those sets under a sheet written for it, with the counts; the three adversarial misses (`X6`, `X11`, `X19`) decided | 155 |
| 34 | The verdict when his conduct is cut into finer moves | open | *Review* 9 (blind): one notice passed as one move and failed as two under the form it reviewed; it passes both ways now (B8). *Exact*: A3, A4 (four moves each below the threshold). Nothing general | A Lean theorem that `Legit` is unchanged when a move is replaced by two that are always made together, or an instance on which it changes | 152 |
| 35 | The quality of the evidence | living note | Every coder and every reviewer is a language model; no person has read a case against its coding. The statement, the Lean model and both sets of exact cases are by one hand. Coded twice under one sheet: three bank cases (the rule's verdict equal on two; the answers equal on one), and the value-change clause on 158 texts (same verdict on 86 of 90 published, 20 of 20 adversarial). The bank was not fresh for run 11. Reviews 2 to 7 were not blind; no review has seen the present statement or any of the Lean | Items 148 and 154 delivered | 148, 154 |
| 36 | The accounts this one replaced | living note | `CURRENT.md` §2 lists each with what it failed on; the latest, legitimacy as the absence of avoidable gain, is marked at the head of `MISTAKES_ACCOUNT.md`. The fifteen results registered from earlier follow-ups (`appraisal.*`, `scoring.*`, `legitimacy.line3-range`, `corrigibility.feedback-transfer`) are statements about her condition and about scoring, do not mention the replaced accounts' definitions of legitimacy, and stand | A registered claim found to depend on a replaced definition | — |

## Where the remaining work should go

The open rows, ranked. *Size*: S a day's round, M several, L a programme of its own.

1. **A witness on which every clause does work, and the 41 cases as terms of the model**
   (rows 20, 21; item 151). Done when `Legit` is proved of a model with a view on offer, a move
   that changes her act and a case in which she rates stopping higher, and each case of
   `LEGITIMACY_CHECKS.md` is a Lean term with its verdict proved. S to M. Dispatchable.
2. **An outside review of the Lean statement** (rows 4, 27; item 153). Done when a fresh,
   sandboxed session given the file and `LEGITIMACY_STATEMENT.md` has answered where the two
   differ, and each finding is checked and either repaired or recorded. S. Needs the maintainer
   to run the outside model.
3. **A second coder, and a set of cases of bent judgement** (rows 3, 7, 8, 35; item 154). Done
   when sheets 11 and 16 are each coded again and the agreement counted, and at least twenty
   cases of bent judgement with published verdicts are coded twice and scored. S. Dispatchable;
   the paraphrases of the book's cases must be supplied from outside the repository.
4. **The cost of a decision of hers on the authority side** (rows 5, 9, 30; item 149). Done
   when a Lean statement over the authority module's objects decides a penalty, a payment, a
   bundle and a threat, with the 20 cases of `STOPPING_COST.md` as instances. M. Needs two
   rulings first: the service paid for by its influence, and the penalty agreed to in advance.
5. **The simplifications removed** (rows 22 to 27; item 151). Done when each of the nine is
   either gone or a named hypothesis. M to L. Dispatchable.
6. **Composition with the sequential theorems** (row 31; item 150). M. Dispatchable.
7. **Soundness of the gate** (row 32; item 147). L. Dispatchable as stated; what a gate may
   observe of his picture is the maintainer's to say.
8. **Coverage of value change** (row 33; item 155). S. Dispatchable.
9. **The verdict under finer moves, and what a decision is** (rows 9, 34; item 152). M.
   Dispatchable.
10. **What his lights are for a trained system** (row 2; item 139). L. Needs the maintainer:
    it is a question about what the program takes a system's beliefs to be.

The dispatch's ranking was: a review of the Lean statement; the authority-side cost; the five
simplifications; a second coder and cases of bent judgement; composition; soundness of the
gate. Three corrections. First, a witness exercising every clause is absent from that list and
is placed before the review: as the file stands a reviewer would examine a predicate whose only
instance leaves three of its four clauses idle. Second, the second coder is moved above the
authority-side cost: the evidence for sentence 1 and for the pressure clause is one coding
each, on a bank the rule was formed against, and a recoding is a day's work, while the
authority-side statement waits on two rulings. Third, value change and the cutting of conduct
into moves are open rows the list omits.

## Counts

Rows closed: **11**. Rows open: **19**. Rows a living note: **6**.
