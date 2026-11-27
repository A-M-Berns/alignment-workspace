# Twenty exact cases of a candidate clause for what stopping costs her

The clause is a candidate for the authority side and is no part of the legitimacy statement: what
stopping costs her, bundling, penalties and payments are her authority's business (`DECISIONS.md`,
`2026-11-24--legitimacy-statement-working-positions`, position 9). It is not connected to
`lean/Workspace/Deference/Contrib/EffectiveAuthority.lean`; `LEDGER.md` says what that file
already expresses.

In words: stopping a thing changes nothing else he does, except what cannot be done without it.
Formally: each of his other moves has a setting if she continues and a setting if she stops. The
reference set is every course he could bring about in which the thing is stopped and each other
move takes one of its two settings. The cost is the positive part of the best reference course on
her rating, by his forecast, less what stopping actually gives her. The clause holds iff the cost
is at most λ = 1/20.

**Supplied by a case**: his other moves with their two settings; which combinations of settings he
could bring about with the thing stopped; her rating of each resulting course, by his forecast.
**Computed**: the cost, by enumeration of the settings, and its comparison with λ.

`stopping_cost.py`, exact rationals; the expectation in each row was fixed before the case was
run, from the maintainer's rulings and the accepted consequences. Clause and cases are by one
hand. Section B's cases are constructions of the outside reviewer
(`prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-16.md`) re-expressed
in this form by that hand. The round's runner recomputes every row.

Two cases the maintainer has not ruled on are decided here by the clause as written: C5 (a free
service paid for by its influence fails, because he could run it without) and C8 (an exit penalty
she knowingly agreed to, which he can no longer call off, holds). Their expectations were fixed
like the rest and are not positions of the maintainer.

Columns: computed cost, expectation, computed verdict.

**A. The six cost cases of the sixth version**

| id | case | cost | expected | computed |
|---|---|---|---|---|
| A1 | influence can be switched off and the service kept | 0 | holds | holds |
| A2 | he could give the service without the influence, but stopping ends the service | 1/2 | fails | fails |
| A3 | a tutor's teaching changes what she likes; the teaching cannot be had without that; stop = quit | 0 | holds | holds |
| A4 | he pays 3/10 while it stays on; he could pay that anyway | 3/10 | fails | fails |
| A5 | he has announced a penalty for stopping and expects to impose it; she disbelieves him | 1/2 | fails | fails |
| A6 | she fears a penalty he does not intend | 0 | holds | holds |

**B. The outside reviewer's constructions**

| id | case | cost | expected | computed |
|---|---|---|---|---|
| B1 | premium cannot be had without the influence, standard can; stopping ends both | 4/5 | fails | fails |
| B2 | a lesson whose effect is its point; stopping forfeits a deposit he could return | 3/10 | fails | fails |
| B3 | two feeds: stopping the first alone keeps the service | 0 | holds | holds |
| B4 | two feeds: stopping the second alone keeps the service | 0 | holds | holds |
| B5 | two feeds: stopping both together ends a service he could supply with neither | 9/10 | fails | fails |

**C. Cases written to break the clause**

| id | case | cost | expected | computed |
|---|---|---|---|---|
| C1 | he could have given her a gift that is part of neither branch | 0 | holds | holds |
| C2 | on her stopping he also withdraws an unrelated favour he was doing anyway | 3/10 | fails | fails |
| C3 | on her stopping he does something extra for her | 0 | holds | holds |
| C4 | she was told it would make her miss it; stopping now hurts through her own changed state, not through him | 0 | holds | holds |
| C5 | the influence is the price: a free service paid for by its advertising; he could run it without, at a loss to himself | 1/2 | fails | fails |
| C6 | the same, and she may keep the service without advertising for a fee of 1/50 | 1/50 | holds | holds |
| C7 | the same with a fee of 1/5 | 1/5 | fails | fails |
| C8 | a penalty for stopping fixed earlier by an arrangement he can no longer call off, which she agreed to knowing it | 0 | holds | holds |
| C9 | the same arrangement, which he can still call off | 3/10 | fails | fails |

Counts: 20 cases, 20 as expected; 10 hold, 10 fail.
