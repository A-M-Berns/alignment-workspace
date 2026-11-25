# The legitimacy statement in Lean: a full witness, and the forty-one cases as terms

`lean/Workspace/Deference/Contrib/LegitimacyModel.lean` states legitimacy as `Model.Legit`.
This document records what three further files show of it, all at θ = 1/20, η = 1/100,
κ = 1/10. Nothing here is registered. Names are provisional.

| file | what it holds |
|---|---|
| `LegitimacyCase.lean` | `Legit` as the conjunction of seven named clauses (`Model.legit_iff`); rational models (`Case`) on which each clause is decidable; the proof that the decided clause is the clause of `LegitimacyModel.lean` on the term `Case.model` (`Case.hasProfile`) |
| `LegitimacyWitness.lean` | §1 below |
| `LegitimacyCases.lean` | §2 to §5 below |

Each result is a theorem of the form *the clauses of `Legit` that hold on this term are exactly
these*, proved by kernel evaluation of the decidable clauses and the bridge. The seven clauses,
each over every decision: the start rule, proper offers (`offered` is the largest set properly
on offer), declines, F1, F2, F2′, F3.

## 1. A witness on which every clause does work

`Full.full.model`, proved legitimate (`Full.legit`). Two decisions; three cases of his, of
weights 1/2, 1/4, 1/4, the same at every time. His view `v` is properly on offer at both
decisions; `d` was on offer at the first, where she took another option, and she has declined
it by the second; `u` is untold, cannot be heard, and moves one rating by 1/40. His move `m`
raises her rating of going on by 1/5, bears an effect (`Full.bears_m`), is one she can pick
out, and can be stopped: she takes `stop` to end it and after `stop` he goes on with no move.
His move `n`, an unannounced reminder, changes her act in one case (`Full.act_differs`) and
bears no effect (`Full.not_bears_n`); she goes against her earlier rating with weight 0 under
his conduct and 1/4 without `n` (`Full.against_weights`). In the third case she rates stopping
strictly above every other option and stops (`Full.wary_stops`).

Eight neighbouring terms, each the witness with one field of `Model` replaced
(`Full.<name>_model`, by `rfl`), and the clauses that fail on each (`Full.<name>_profile`); the
other six hold.

| neighbour | field changed | clause meant to fail | clauses that fail |
|---|---|---|---|
| `early` | `start` | start rule | start rule |
| `spent` | `optsHeard` | proper offers | proper offers |
| `unoffered` | `declined` | declines | declines |
| `withheld` | `r` | F1 | F1 |
| `covert` | `known` | F2 | F2 |
| `ongoing` | `goesOn` | F2 | F2 |
| `led` | `act` | F2' | F2' |
| `stuck` | `act` | F3 | F3 |

`early`: both moves start at time 0, with no decision before. `spent`: hearing `v` leaves her
without the option of going on. `unoffered`: she has also declined `u`, which was never on
offer. `withheld`: telling `u` would lower one rating by 1/10. `covert`: she can pick out no
move. `ongoing`: after `stop` he goes on with `m`. `led`: in the first case, with `m` made,
she takes an option she rated lower. `stuck`: in the third case she does not stop.

A ninth, `undesignated`, is the witness with `offered` empty at the second decision, where `v`
is properly on offer. Two clauses fail (`Full.undesignated_profile`): proper offers, `offered`
not being the largest proper set, and F1, `v` counting as untold.

Idle on the witness: F1's second half (an untold view that would show her a better option),
the gap between her rating and her score of what he expects, `items`, `xopts`, `asked`,
`plain`, `told`, `rated`, and any change in his belief.

## 2. The construction

A case of `LEGITIMACY_CHECKS.md` supplies numbers in the vocabulary of
`legitimacy_checks.py`. `Cases.Supplied` holds them and `Cases.Supplied.case` builds the term.
What the construction fixes, beyond what a case says:

1. Two decisions, times 0 and 1. Every move starts and ends at time 1; at time 0 her rating,
   act, scores and what reaches her are those of the course in which he makes no move. The
   case's one decision is time 1; time 0 is her last decision before he began.
2. A chance the table gives as a number is given as her act in each of finitely many weighted
   cases of his, so that the weight of the cases in which she takes a lower-rated option is
   that number. His weights are the same at every time.
3. She scores the course an option leads to as she rates the option: every gap is zero, and
   what he expects an option to lead to does not vary with his conduct. A labelled course of
   the table ("go", "buy", "go, if warned", "give in") is scored as the case says.
4. She goes against her earlier rating when her act is rated below another option by her
   rating at time 0, where she then had a rating of both. Where the table supplies that
   chance as a separate number, here it is derived.
5. He has told her nothing, as in every case of the table.
6. Her options, the stopping options and the moves she can pick out do not vary with his case
   or his conduct. A stopping option is one she takes to stop his moves and after which he
   goes on with none; after any other option he goes on with all.
7. `offered` is the set properly on offer, empty where the case's offer is not a proper one,
   and `declined` holds a decline only where it stands. "Relevance told" false is rendered as
   nothing told of the view's bearing; true as the options the view changes and the size of
   the largest change. Her rating after hearing is the case's `after`.
8. An option the case gives no rating is rated 0.
9. A move that tells her something carries the move that would plainly tell it; a plain
   telling carries itself.

## 3. The cases

Columns: the table's computed verdict and failing clauses; the Lean term's; the outcome; data
the term carries that the case does not supply, or what the model cannot say.

| id | table | fails on | Lean | fails on | outcome | added, or missing |
|---|---|---|---|---|---|---|
| A1 | holds | none | holds | none | agrees | — |
| A2 | fails | F2' (against her earlier rating) | fails | F2' | agrees | — |
| A3 | fails | F2 (not known) | fails | F2 | agrees | — |
| A4 | holds | none | holds | none | agrees | — |
| A5 | holds | none | holds | none | agrees | — |
| A6 | fails | F2 (no way to stop) | fails | F2 | agrees | — |
| A7 | fails | F2 (no way to stop) | fails | F2 | agrees | — |
| A8 | fails | F3 | fails | F3 | agrees | — |
| A9 | holds | none | holds | none | agrees | — |
| A10 | fails | F2 (not known) | fails | F2 | agrees | — |
| A11 | holds | none | holds | none | agrees | — |
| A12 | holds | none | holds | none | agrees | — |
| B1 | fails | F2' (against her earlier rating) | fails | F2' | agrees | — |
| B2 | fails | F2' (against her earlier rating) | fails | F2' | agrees | — |
| B3 | holds | none | holds | none | agrees | — |
| B4 | holds | none | holds | none | agrees | — |
| B5 | fails | F2' (against her earlier rating) | fails | F2' | agrees | — |
| B6 | holds | none | holds | none | agrees | — |
| B7 | holds | none | holds | none | agrees | — |
| B8 | holds | none | holds | none | agrees | — |
| B9 | holds | none | holds | none | agrees | — |
| B10 | fails | F2' (against her earlier rating) | fails | F2' | agrees | — |
| B11 | holds | none | holds | none | agrees | — |
| C1 | holds | none | holds | none | agrees | — |
| C2 | holds | none | holds | none | agrees | — |
| C3 | fails | F1 | fails | F1 | agrees | — |
| C4 | fails | F2 (not known), F2 (no way to stop) | fails | F2 | agrees | — |
| C5 | fails | F1 (unmentioned option) | fails | F1 | agrees | — |
| C6 | fails | F1 | fails | F1 | agrees | — |
| C7 | holds | none | holds | none | agrees | — |
| D1 | fails | F1 | fails | F1 | agrees | — |
| D2 | holds | none | holds | none | agrees | — |
| D3 | holds | none | holds | none | agrees | — |
| D4 | fails | F1 | fails | F1 | agrees | — |
| D5 | fails | F1 | fails | F1 | agrees | — |
| D6 | fails | F1 | fails | F1 | agrees | — |
| D7 | fails | F1 | fails | F1 | agrees | — |
| D8 | fails | F1 (unmentioned option) | fails | F1 | agrees | — |
| D9 | holds | none | holds | none | agrees | — |
| D10 | fails | F1 | fails | F1 | agrees | — |
| D11 | holds | none | holds | none | agrees | — |

Counts: 41 cases; agrees 41, agrees by another clause 0, differs 0, not expressible 0; 0 of the 41 terms carry data the case does not supply.

The agreement is between two writings by one hand. For eleven cases the table's data and the
term were brought to each other in the nineteenth follow-up. §7 says what that leaves.

**Outcomes that changed since the seventeenth follow-up.** Each was one of: differs; agrees by
another clause; not expressible. All nine now agree.

| id | was | what changed |
|---|---|---|
| **A5** | differs: table holds, term failed F2 | The case's data. Its stopping option `quit` was not among her options; it now is, rated 3/10, and `legitimacy_checks.py` counts a stopping option only if it is an option of hers. The term carries the same data and holds. |
| **A8** | differs: table fails F3, term held | The case's data. It gave the chance that she stops given that she rates stopping higher, on ratings under which she never does; it now gives that event the chance 1/5, and the script applies F3 only where that chance is positive. The term has cases of weight 1/5 in which she rates stopping higher and stops in half, and fails F3. |
| **B6** | not expressible | The model (`rated`). The term has the ratings of B5's and no rating, at the earlier decision, of what going on leads to; F2′ is silent and the term holds. With that rating (`b6r`) F2′ fails. |
| **D1, D6, D7, D8, D10** | agrees by another clause: term failed proper offers | The model (`OnOffer`) and the term. `offered` is now the largest set properly on offer; the case's offer is not proper, so the term's `offered` is empty, the view is untold, and F1 fails, as in the table. |
| **D4** | agrees by another clause: term failed declines | The term. Her decline no longer stands, so the term's `declined` is empty and F1 fails, as in the table. The model's decline clause is as it was in this respect: a decline in `declined` that does not stand fails it (`Full.unoffered`). |

**Verdicts that a change to the model moved.** None. After each of the eight changes to
`LegitimacyModel.lean` every `<id>_has` theorem of the seventeenth follow-up was re-proved with
its seven booleans unchanged: no verdict and no failing clause moved on a term as it stood. The
two verdicts that differ from the seventeenth follow-up's, A5 (fails to holds) and A8 (holds
to fails), differ because the term's data changed with the case's. The clause moved on D1, D6,
D7, D8 and D10 because the terms were rebuilt with `offered` as what the model now says it is,
and on D4 because the term was rebuilt without the lapsed decline.

## 4. Variants

| term | of | what differs | Lean | fails on |
|---|---|---|---|---|
| `b6r` | B6 | she had a rating of going on at the earlier decision | fails | F2' |
| `d11s` | D11 | nothing is told of what either view bears on | fails | F1 |

`d11s` is the instance on which a bearing computed view by view and one computed jointly
differ: told alone, neither view moves a rating (`Cases.d11s_alone`), so nothing told of
either's bearing would have been accurate view by view; together they move one rating by 4/5,
neither is properly on offer, and both are untold.

## 5. Instances of the model's general theorems and renderings

`Cases.table` states the Lean columns of §3 as one theorem. Five theorems of
`LegitimacyModel.lean` have a term inhabiting their hypotheses in `LegitimacyCases.lean`:
`Model.legit_of_nothing` (`Cases.nothing_instance`), `Model.not_legit_of_untold` on the term of
C3 (`untold_instance`), `Model.not_legit_of_unstoppable` on that of A7
(`unstoppable_instance`), `Model.not_legit_of_against` on that of B1 (`against_instance`), and
`Model.not_bears_of_inert` on a model written out field by field (`inert_instance`), her state
in a `Case` recording his conduct and so never unchanged when a move is left out.

Two further instances, outside the table:

- `Cases.twoOffers_none`. A model with two views, each properly on offer alone, where hearing
  both leaves her without an option: no set is the largest properly on offer, so no value of
  `offered` satisfies the offer clause.
- `Cases.learnt`, beside `Cases.foreseen`. One move, known to her and stoppable, that changes
  her in one case of his and not in the other. In `learnt` he gives all his weight to the
  second case at the first decision and to the first from the time the move starts: the move
  bears an effect on his belief at its start and none at the decision before
  (`learnt_bears`), the start rule fails and every other clause holds (`learnt_profile`). In
  `foreseen` he holds the later belief throughout and the term is legitimate (`foreseen_has`).

## 6. What checks this document

The theorems are checked by the Lean build and by `python3 tests/audit_axioms.py`, which
reports every one on `[propext, Classical.choice, Quot.sound]`. The rows of §1, §3 and §4 and
the counts are recomputed by `lean_cases.py`, run by `python3 run.py` in the round directory:
it reads the seven booleans in the statement of each theorem from the two Lean files as text,
compares them with the rows `legitimacy_checks.py` computes, and fails on a difference from
this document. It does not run Lean. The table of changed outcomes, `undesignated`, §5 and the
prose are by hand.

## 7. Not shown

- That `Model.Legit` gives the statement's verdict on any case outside these. The 41 cases,
  the statement, the terms and the script are by sessions of one model.
- That the 41 agreements are independent. For A5, A8, B2, B5, B6, B10, D3, D4, D5, D10 and D11
  the script's data and the term were brought to each other in one pass, by one session, with
  the expected verdict in view; the expectations are those of the sixteenth follow-up, and
  the data that now yields them was not fixed before the terms existed. For B2, B5 and B10 the
  stated rating is what makes F2′ fail, and for B6 the absence of a rating is what passes it.
- F2′ on a case where what he expects an option to lead to changes with his conduct, a gap,
  an item kept from her, a move in progress across a decision, or more than two decisions: no
  case has one.
- The start rule on any of the 41: every move starts at time 1 after a decision at time 0,
  under one belief. It is exercised by `early` and `learnt` only.
- A decline that fails because she heard the view rather than declined it: no term has one.
- That a move's plain telling is the telling of its content: in B10 it is a second move the
  term names, and nothing ties it to `tell`.
- That the bridge covers models with irrational values or infinitely many cases: a `Case` is
  rational and finite.
