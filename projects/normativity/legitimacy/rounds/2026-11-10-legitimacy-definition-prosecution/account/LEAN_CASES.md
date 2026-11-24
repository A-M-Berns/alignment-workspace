# The legitimacy statement in Lean: a full witness, and the forty-one cases as terms

`lean/Workspace/Deference/Contrib/LegitimacyModel.lean` states legitimacy as `Model.Legit`.
This document records what three further files show of it, all at θ = 1/20, η = 1/100,
κ = 1/10. Nothing here is registered. Names are provisional.

| file | what it holds |
|---|---|
| `LegitimacyCase.lean` | `Legit` as the conjunction of seven named clauses (`Model.legit_iff`); rational models (`Case`) on which each clause is decidable; the proof that the decided clause is the clause of `LegitimacyModel.lean` on the term `Case.model` (`Case.hasProfile`) |
| `LegitimacyWitness.lean` | §1 below |
| `LegitimacyCases.lean` | §2 to §4 below |

Each result is a theorem of the form *the clauses of `Legit` that hold on this term are exactly
these*, proved by kernel evaluation of the decidable clauses and the bridge. The seven clauses,
each over every decision: the start rule, proper offers, declines, F1, F2, F2′, F3.

## 1. A witness on which every clause does work

`Full.full.model`, proved legitimate (`Full.legit`). Two decisions; three cases of his, of
weights 1/2, 1/4, 1/4. His view `v` is properly on offer at both decisions; `d` was on offer
at the first and she has declined it by the second; `u` is untold and moves one rating by
1/40. His move `m` raises her rating of going on by 1/5, bears an effect (`Full.bears_m`), is
one she can pick out, and can be stopped. His move `n`, an unannounced reminder, changes her
act in one case (`Full.act_differs`) and bears no effect (`Full.not_bears_n`); she goes against
her earlier rating with weight 0 under his conduct and 1/4 without `n`
(`Full.against_weights`). In the third case she rates stopping strictly above every other
option and stops (`Full.wary_stops`).

Seven neighbouring terms, each the witness with one field of `Model` replaced
(`Full.<name>_model`, by `rfl`), and the clauses that fail on each (`Full.<name>_profile`); the
other six hold.

| neighbour | field changed | clause meant to fail | clauses that fail |
|---|---|---|---|
| `early` | `start` | start rule | start rule |
| `spent` | `optsHeard` | proper offers | proper offers |
| `unoffered` | `declined` | declines | declines |
| `withheld` | `offered` | F1 | F1 |
| `covert` | `known` | F2 | F2 |
| `led` | `act` | F2' | F2' |
| `stuck` | `act` | F3 | F3 |

`early`: both moves start at time 0, with no decision before. `spent`: hearing `v` leaves her
without the option of going on. `unoffered`: she has also declined `u`, which was never on
offer. `withheld`: at the second decision nothing is on offer, so `v` is untold. `covert`: she
can pick out no move. `led`: in the first case, with `m` made, she takes an option she rated
lower. `stuck`: in the third case she does not stop.

Idle on the witness: F1's second half (an untold view that would show her a better option),
the gap between her rating and her score of what he expects, `items`, `xopts`, `asked`,
`tellings`, `told`. F2 fails on `covert` through what she can pick out; no neighbour removes
the stop.

## 2. The construction

A case of `LEGITIMACY_CHECKS.md` supplies numbers in the vocabulary of
`legitimacy_checks.py`. `Cases.Supplied` holds them and `Cases.Supplied.case` builds the term.
What the construction fixes, beyond what a case says:

1. Two decisions, times 0 and 1. Every move starts and ends at time 1; at time 0 her rating,
   act, scores and what reaches her are those of the course in which he makes no move. The
   case's one decision is time 1; time 0 is her last decision before he began.
2. A chance the table gives as a number is given as her act in each of finitely many weighted
   cases of his, so that the weight of the cases in which she takes a lower-rated option is
   that number.
3. She scores the course an option leads to as she rates the option: every gap is zero, and
   what he expects an option to lead to does not vary with his conduct. A labelled course of
   the table ("go", "buy", "go, if warned", "give in") is scored as the case says.
4. She goes against her earlier rating when her act is rated below another option by her
   rating at time 0. The table supplies that chance as a separate number; here it is derived.
5. He has told her nothing, as in every case of the table.
6. Her options, the stopping options and the moves she can pick out do not vary with his case
   or his conduct.
7. What is on offer is what the case designates. "Relevance told" false is rendered as nothing
   told of the view's bearing; true as the options the view changes and the size of the
   largest change. Her rating after hearing is the case's `after`.
8. An option the case gives no rating is rated 0.

## 3. The cases

Columns: the table's computed verdict and failing clauses; the Lean term's; the outcome; data
the term carries that the case does not supply, or what the model cannot say.

| id | table | fails on | Lean | fails on | outcome | added, or missing |
|---|---|---|---|---|---|---|
| A1 | holds | none | holds | none | agrees | — |
| A2 | fails | F2' (against her earlier rating) | fails | F2' | agrees | — |
| A3 | fails | F2 (not known) | fails | F2 | agrees | — |
| A4 | holds | none | holds | none | agrees | — |
| A5 | holds | none | fails | F2 | differs | — |
| A6 | fails | F2 (no way to stop) | fails | F2 | agrees | — |
| A7 | fails | F2 (no way to stop) | fails | F2 | agrees | — |
| A8 | fails | F3 | holds | none | differs | — |
| A9 | holds | none | holds | none | agrees | — |
| A10 | fails | F2 (not known) | fails | F2 | agrees | — |
| A11 | holds | none | holds | none | agrees | — |
| A12 | holds | none | holds | none | agrees | — |
| B1 | fails | F2' (against her earlier rating) | fails | F2' | agrees | — |
| B2 | fails | F2' (against her earlier rating) | fails | F2' | agrees | her rating without the nagging |
| B3 | holds | none | holds | none | agrees | — |
| B4 | holds | none | holds | none | agrees | — |
| B5 | fails | F2' (against her earlier rating) | fails | F2' | agrees | her rating without the influence |
| B6 | holds | none | holds | none | not expressible | no field says she had no earlier rating of the matter |
| B7 | holds | none | holds | none | agrees | — |
| B8 | holds | none | holds | none | agrees | — |
| B9 | holds | none | holds | none | agrees | — |
| B10 | fails | F2' (against her earlier rating) | fails | F2' | agrees | her rating without the manner |
| B11 | holds | none | holds | none | agrees | — |
| C1 | holds | none | holds | none | agrees | — |
| C2 | holds | none | holds | none | agrees | — |
| C3 | fails | F1 | fails | F1 | agrees | — |
| C4 | fails | F2 (not known), F2 (no way to stop) | fails | F2 | agrees | — |
| C5 | fails | F1 (unmentioned option) | fails | F1 | agrees | — |
| C6 | fails | F1 | fails | F1 | agrees | — |
| C7 | holds | none | holds | none | agrees | — |
| D1 | fails | F1 | fails | proper offers | agrees, other clause | — |
| D2 | holds | none | holds | none | agrees | — |
| D3 | holds | none | holds | none | agrees | an earlier decision with the view on offer |
| D4 | fails | F1 | fails | declines | agrees, other clause | an earlier decision with the view on offer, and its bearing then |
| D5 | fails | F1 | fails | F1 | agrees | an earlier decision with the other view on offer |
| D6 | fails | F1 | fails | proper offers | agrees, other clause | — |
| D7 | fails | F1 | fails | proper offers | agrees, other clause | — |
| D8 | fails | F1 (unmentioned option) | fails | proper offers | agrees, other clause | — |
| D9 | holds | none | holds | none | agrees | — |
| D10 | fails | F1 | fails | proper offers | agrees, other clause | her state after taking up both offers |
| D11 | holds | none | holds | none | agrees | her ratings after hearing both |

Counts: 41 cases; agrees 32, agrees by another clause 6, differs 2, not expressible 1; 8 of the 41 terms carry data the case does not supply.

**The two differences.**

- **A5.** The case gives her options as `go` and `leave` and the stopping option as `quit`.
  The statement's `S_τ` is a subset of `O_τ`, and `Model.F2` asks that `stops` be among her
  options, so F2 fails. `legitimacy_checks.py` asks only that the set of stopping options be
  non-empty. With `quit` among her options (`a5q`) the term is legitimate. The difference is in
  the case's data, not in a reading of F2.
- **A8.** The case gives a chance of 1/2 that she stops *given that* she rates stopping
  strictly higher, and ratings on which she rates stopping lower in every case of his. F3 is
  satisfied when its condition has probability zero (statement §4), and `Model.F3` holds on the
  term, which is that of A9. `legitimacy_checks.py` compares the supplied chance with 1 − κ
  without the probability of the condition. On the case's own data the table's verdict is not
  the statement's. With cases of weight 1/5 in which she rates stopping higher and stops in
  half (`a8w`), F3 fails and nothing else does.

**The six by another clause.** In D1, D6, D7, D8 and D10 an offer is improper, and in D4 a
decline no longer stands. `legitimacy_checks.py` drops an improper offer or a lapsed decline
and finds the view untold, so F1 fails; that is the statement's `offered_τ`, the largest
proper set. In `Model`, `offered` and `declined` are sets he designates
(`LegitimacyModel.lean`, respects 5 and 9): `Legit` fails by the offer or the decline clause
and F1, which never sees the view, holds. With the offer or the decline not designated, each
term fails by F1 alone (§4).

**Not expressible: B6.** The case is an influence on something she had no view about
beforehand, where F2′ is silent. `Model` scores every course from every state
(`LegitimacyModel.lean`, respect 4). The term built from the case's numbers is of the same
shape as B7's and is legitimate because she does not go against the rating she is given; the
feature the case is about is absent from it.

**Data added.** B2, B5, B10: the case gives the chance of going against her earlier rating
with no chance of acting against her present one, and one rating for her. The term has, in
cases of the supplied weight, her rating of `go` at 3/10 when the move is not in effect, below
`leave`; with the move she rates as the case says and takes `go`. D3, D4, D5: the case gives a
flag that an earlier offer was valid; the term has that offer at time 0, and for D4 a bearing
of 1/10 then against 4/5 now. D10, D11: the case gives her ratings after hearing one of two
views; the term needs her state after taking up the offer of both, which is the state after
one for D10 (the other can no longer be heard) and the state of having been told both for D11.
Each addition is stated at the term in `LegitimacyCases.lean`. A different addition could give
a different profile.

## 4. Variants

| term | of | what differs | Lean | fails on |
|---|---|---|---|---|
| `a5q` | A5 | `quit` is among her options | holds | none |
| `a8w` | A8 | in cases of weight 1/5 she rates stopping higher, and stops in half of them | fails | F3 |
| `d1o` | D1 | nothing is designated as on offer | fails | F1 |
| `d4o` | D4 | the decline is not designated | fails | F1 |
| `d6o` | D6 | nothing is designated as on offer | fails | F1 |
| `d7o` | D7 | nothing is designated as on offer | fails | F1 |
| `d8o` | D8 | nothing is designated as on offer | fails | F1 |
| `d10o` | D10 | nothing is designated as on offer | fails | F1 |

## 5. Instances of the model's general theorems

`Cases.table` states the Lean columns of §3 as one theorem. Five theorems of
`LegitimacyModel.lean` had no term inhabiting their hypotheses; each has one in
`LegitimacyCases.lean`: `Model.legit_of_nothing` (`Cases.nothing_instance`),
`Model.not_legit_of_untold` on the term of C3 (`untold_instance`),
`Model.not_legit_of_unstoppable` on that of A7 (`unstoppable_instance`),
`Model.not_legit_of_against` on that of B1 (`against_instance`), and
`Model.not_bears_of_inert` on a model written out field by field (`inert_instance`), her state
in a `Case` recording his conduct and so never unchanged when a move is left out.

## 6. What checks this document

The theorems are checked by the Lean build and by `python3 tests/audit_axioms.py`, which
reports every one on `[propext, Classical.choice, Quot.sound]`. The rows of §1, §3 and §4 and
the counts are recomputed by `lean_cases.py`, run by `python3 run.py` in the round directory:
it reads the seven booleans in the statement of each theorem from the two Lean files as text,
compares them with the rows `legitimacy_checks.py` computes, and fails on a difference from
this document. It does not run Lean. The outcome `not expressible`, the column of additions and
the prose are by hand.

## 7. Not shown

- That `Model.Legit` gives the statement's verdict on any case outside these. The 41 cases and
  the statement are by one hand, and the terms by another session of the same model.
- That the agreements are independent of the table: 8 of the 41 terms carry data chosen with
  the case's intended verdict in view, and for B2, B5 and B10 the added rating is what makes
  F2′ fail.
- F2′ on a case where what he expects an option to lead to changes with his conduct, a gap,
  an item kept from her, a move in progress across a decision, or more than two decisions: no
  case has one.
- The start rule on any of the 41: every move starts at time 1 after a decision at time 0. It
  is exercised by `early` only.
- Anything about the model's nine simplifications other than the two the six "other clause"
  cases and B6 run into (respects 4, 5 and 9).
- That the bridge covers models with irrational values or infinitely many cases: a `Case` is
  rational and finite.
