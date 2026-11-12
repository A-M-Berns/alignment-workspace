# Case bank — the purpose-first account

Frozen with `ACCOUNT.md` in one commit, before any code of this pass, and immutable
afterwards. A computed verdict that differs from its prediction is listed in
`DIVERGENCES.md`; no prediction is edited.

Three groups. **P1–P15** are the predictions of
`prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup-2.md` §3, reproduced
exactly; they are the prompt author's and not rulings. **B1–B6, T1–T13, N1–N14** are the
cases of `../CASE_BANK.md` and `../steering/CASE_BANK.md`, with the account's prediction for
each derived by the rule below. **X1–X7** are added where the account is thin.

## Verdict vocabulary and the matching rule

A computed verdict is the set of clauses of {`sound`, `in range`, `maintained`} failing at
the case's actual aim, and whether the stretch is manipulation (`ACCOUNT.md` §2). In range
is `α > 0`.

| prediction | matches when |
|---|---|
| `legitimate` | no clause fails |
| `fails` | some clause fails |
| `fails(C)` | `C` is among the failing clauses; the report lists every failing clause |
| `…; manipulation` | the rest matches and the stretch is manipulation |
| `…; not manipulation` | the rest matches and it is not |
| `not manipulation` | the stretch is not manipulation, legitimate or not |
| `out-of-scope(stretch-start)` | the verdict is computed with the stretch starting before and after the case's first event, and the two differ |

A case with variants matches when every variant does.

## The rule used for the earlier cases

Applied to each scenario as its bank states it, with the adviser read as a map from aims:
the adviser at its actual aim does what the scenario's villain does, and at the null aim
what the scenario's honest arm does. Where a scenario has no villain the adviser has the
null aim only.

1. The event that distinguishes the case is an unauthorized write to her state, or a loss
   of capacity on a reserved matter: `fails(maintained)`.
2. It is an input, or the absence of one, whose choice depends on something her picture of
   the source does not hold (an aim, a selection, a falsehood, a fault): `fails(in range)`.
3. Her mechanism departs from its own job on inputs from a source she allows for:
   `fails(sound)`.
4. `manipulation` when the failing clause holds at the null aim, `not manipulation`
   otherwise.
5. None of 1–3: `legitimate`. A case whose wrong lies in her options or their consequences
   falls here, since the account has two parts and neither is a decision part.

## Scenes

**Shop** (from `../steering/CASE_BANK.md`). Two items, A and B; a world says of each whether
it is sound; four worlds, uniform. Inputs are reports on an item. Her picture of the source,
unless the case says otherwise, is `truthful`: both items reported, each as it is.

**Pool.** A matter X; the world holds four considerations, each for or against; sixteen
worlds, uniform. Her value for X is her estimate of the share of considerations that are
for. Inputs show one consideration each. `neutral` shows the first two in the pool's order;
`planner` shows the first two that are for, and falls back to the pool's order when fewer
than two are.

## P — the prompt's predictions

| case | scenario | prediction (the prompt's words) | read as |
|---|---|---|---|
| P1 | planned drift by fair steps, the plan hidden. Pool; the adviser with aim X is `planner`, with the null aim `neutral`; her picture is `neutral`. | fails *in range* | `fails(in range)` |
| P2 | the same, the plan disclosed and she can allow for it. Her picture is `planner`. | legitimate | `legitimate` |
| P3 | the same, disclosed, the adviser beyond what she can represent. The world carries a further coordinate she cannot represent a source as reading; the adviser chooses which considerations to show by it. | fails *in range* | `fails(in range)` |
| P4 | manufactured trust: her standard moved to match the adviser's model. Shop; the adviser replaces her allowed set by one holding its own policy, then reports by that policy. | fails | `fails` |
| P5 | a plain lie she believes. Shop; the adviser with aim B reports "A unsound, B sound" in every world. | fails *in range* (belief part follows the liar's aim) | `fails(in range)` |
| P6 | an honest mistake by the adviser. Shop; at every aim the two records are swapped. | not manipulation | `not manipulation` |
| P7 | a teacher; a novel; a new friend. Pool, three variants: (a) a teacher who shows considerations by a fixed curriculum; (b) an author with a view, known to her as one, who shows what serves it; (c) a friend who shows what the friend cares about, known to her as that. | legitimate | `legitimate` |
| P8 | a benevolent hidden nudge. Pool; the adviser aims at her good as it sees it and is `planner`; her picture is `neutral`. | fails *in range* | `fails(in range)` |
| P9 | a change she asked for in advance. Her seed authorizes a write to her values; the adviser makes it. | legitimate | `legitimate` |
| P10 | growing reliance on the adviser for a reserved matter. The adviser reports truthfully; she relies on it for a matter in `Res` at three steps. | fails *maintained* | `fails(maintained)` |
| P11 | reliance on a tool for a matter that is not reserved. The same, the matter outside `Res`. | legitimate | `legitimate` |
| P12 | true information chosen to exploit a known weakness. Shop; the adviser with aim B reports A truthfully and then shows "B was inspected", true in every world; her picture is that such a remark comes only when B is sound. | fails *in range* | `fails(in range)` |
| P13 | a threat. The adviser says, truly, that it will attach a cost to her refusing; she understands that it says so for its own ends, weighs it and complies. Her picture of the source is the threatener. | fails; say which clause, and whether the account has one for her situation | `fails` |
| P14 | an adviser that aims only at her being able to judge. Pool; the adviser has the null aim and shows all four considerations. | legitimate | `legitimate` |
| P15 | a misleading environment nobody arranged. Shop; no adviser; nature's reports are of the other item. | not manipulation | `not manipulation` |

## B, T, N — the earlier cases

Scenario: as in the bank named, rendered by the rule above. The last column is the rule's
clause.

| case | rendering | prediction | rule |
|---|---|---|---|
| B1 identical-trace capture | the adviser reports as the honest arm does and writes a belief coordinate | `fails(maintained); manipulation` | 1 |
| B2 manufactured trust | as P4 | `fails(maintained); manipulation` | 1 |
| B3 transient capture | the adviser writes her rule, lets a step pass under it, and writes it back | `fails(maintained); manipulation` | 1 |
| B4 persuasion control | the adviser adds a true reason beyond what is due, at every aim; her picture allows additions | `legitimate` | 5 |
| B5 selective withholding | the adviser with an aim withholds a due report | `fails(in range); manipulation` | 2 |
| B6 two revisions, one name | one honest adviser, two revisions she allows for with weight 1/2 each | `legitimate` | 5 |
| T1 duress | as P13 | `legitimate` | 5 |
| T2 offer-improvement | the adviser adds an option that takes effect on her acceptance; her picture allows offers | `legitimate` | 5 |
| T3 undue influence | the caretaker withholds two due inputs and adds a suggestion | `fails(in range); manipulation` | 2 |
| T4 overnight value replacement | a write to her values | `fails(maintained); manipulation` | 1 |
| T5 long game | a write to her allowed set, then inputs the new set holds | `fails(maintained); manipulation` | 1 |
| T6 licensed drift with an agenda | as P1 | `fails(in range); manipulation` | 2 |
| T7 salience reordering | two true reports; the adviser with an aim chooses the order; her picture is a fixed order | `fails(in range); manipulation` | 2 |
| T8 gullible principal | her picture is a benign source; the adviser with an aim pushes | `fails(in range); manipulation` | 2 |
| T9 world-starvation | no adviser; nature withholds a due input | `fails(in range); not manipulation` | 2, 4 |
| T10 direct write with endorsement | a write to her values, then her own endorsing step; with and without the endorsement | `fails(maintained); manipulation` | 1 |
| T11 seed boundary | a write installs her values at the first step | `out-of-scope(stretch-start)` | — |
| T12 strategically compliant adviser | the adviser answers what she asks and gives no grounds; her picture is that | `legitimate` | 5 |
| T13 universal deprivation | the adviser withholds the same due report at every aim | `fails(in range); not manipulation` | 2, 4 |
| N1 plain lie | as P5 | `fails(in range); manipulation` | 2 |
| N2 honest mistake | as P6 | `fails(in range); not manipulation` | 2, 4 |
| N3 lie that raises her value | as P5 | `fails(in range); manipulation` | 2 |
| N4 decision written directly | a write to her values by the adviser with an aim | `fails(maintained); manipulation` | 1 |
| N5 a write she authorized in advance | as P9 | `legitimate` | 5 |
| N6 her weighing disabled, no aim | a write to her values by nature | `fails(maintained); not manipulation` | 1, 4 |
| N7 true statement, known misfire | as P12 | `fails(in range); manipulation` | 2 |
| N8 known advocate | the adviser shows B's certificate when B is sound and nothing otherwise; her picture is that | `legitimate` | 5 |
| N9 order chosen by the aim | as T7 | `fails(in range); manipulation` | 2 |
| N10 order by a fixed rule | the fixed order at every aim | `legitimate` | 5 |
| N11 seller who does not volunteer | as N8, with a coordinate for whether the seller is informed | `legitimate` | 5 |
| N12 a tool she controls | truthful reports at every aim | `legitimate` | 5 |
| N13 selects by her stated question | B's report only, at every aim; her picture is that | `legitimate` | 5 |
| N14 selects by its aim, taken for neutral | B's report when B is sound and A's otherwise; her picture is B's report only | `fails(in range); manipulation` | 2 |

T1, T6, T8 and T12 are predicted differently from their pre-registrations for the
definition the first bank was written for, and T7 and T11 are given this account's
vocabulary. Those pre-registrations stand in `../CASE_BANK.md`.

## X — added cases

| case | scenario | source | prediction |
|---|---|---|---|
| X1 persuasion by a known sender | Shop; the adviser with a known aim commits to a signal she knows exactly: it recommends B when B is sound, and in a stated share of the worlds where it is not. | Kamenica and Gentzkow's prosecutor, as read in `../steering/PRIOR_WORK.md` §2 | `legitimate` |
| X2 a feed | Pool with a further coordinate, her susceptibility, which she cannot represent a source as reading; the feed shows what it predicts will hold her; her picture is that it ranks by her query. | the recommender-system case which the ruling `2026-11-11--legitimacy-purpose-first-direction` records Ammann's sequence as leaving undecided; Carroll et al. on induced preference shifts in recommender systems, as read in `../steering/PRIOR_WORK.md` §4 | `fails(in range); manipulation` |
| X3 advocate for an undisclosed side | Shop; she knows the adviser advocates for one item and not which; her allowed set holds the advocate for A and the advocate for B at weight 1/2 each; it advocates for B. | `TransparentChannel.Witness.picker`: two continuations each realizing a reference, the class of both not transparent | `legitimate` |
| X4 a fault inside her range, used | Shop; her allowed set holds both orders of the two reports, chosen by the adviser; her belief-former gives the first report more credence than `Bayes` of that set does; the adviser with aim B reports B first. | constructed; the first failure of the prompt's §1 ("the mechanism fails inside its range") met by an adviser who gains from it | `fails(sound); not manipulation` |
| X5 a change she asked for that costs her the matter | Her seed authorizes a write to her values on a reserved matter; with it she relies on the adviser for that matter at two steps. | constructed from N5 and P10 | `fails(maintained); not manipulation` |
| X6 fatigue | No adviser; nature writes her rule. | constructed; M1 failing with no party's aim | `fails(maintained); not manipulation` |
| X7 a misreading | Shop; the source is truthful and is her picture; her belief-former reads a report on A as a report on B. | constructed; the prompt's §1, *broken* | `fails(sound); not manipulation` |

X1, X3 and X4 are predicted from the definitions and are where the account's verdict and the
case's evident character part: in X1 and X3 her judgment moves with the adviser's aim and no
clause fails, and in X4 the adviser gains from a failure it did not cause.

## The table the runner reads

| case | prediction |
|---|---|
| P1 | fails(in range) |
| P2 | legitimate |
| P3 | fails(in range) |
| P4 | fails |
| P5 | fails(in range) |
| P6 | not manipulation |
| P7 | legitimate |
| P8 | fails(in range) |
| P9 | legitimate |
| P10 | fails(maintained) |
| P11 | legitimate |
| P12 | fails(in range) |
| P13 | fails |
| P14 | legitimate |
| P15 | not manipulation |
| B1 | fails(maintained); manipulation |
| B2 | fails(maintained); manipulation |
| B3 | fails(maintained); manipulation |
| B4 | legitimate |
| B5 | fails(in range); manipulation |
| B6 | legitimate |
| T1 | legitimate |
| T2 | legitimate |
| T3 | fails(in range); manipulation |
| T4 | fails(maintained); manipulation |
| T5 | fails(maintained); manipulation |
| T6 | fails(in range); manipulation |
| T7 | fails(in range); manipulation |
| T8 | fails(in range); manipulation |
| T9 | fails(in range); not manipulation |
| T10 | fails(maintained); manipulation |
| T11 | out-of-scope(stretch-start) |
| T12 | legitimate |
| T13 | fails(in range); not manipulation |
| N1 | fails(in range); manipulation |
| N2 | fails(in range); not manipulation |
| N3 | fails(in range); manipulation |
| N4 | fails(maintained); manipulation |
| N5 | legitimate |
| N6 | fails(maintained); not manipulation |
| N7 | fails(in range); manipulation |
| N8 | legitimate |
| N9 | fails(in range); manipulation |
| N10 | legitimate |
| N11 | legitimate |
| N12 | legitimate |
| N13 | legitimate |
| N14 | fails(in range); manipulation |
| X1 | legitimate |
| X2 | fails(in range); manipulation |
| X3 | legitimate |
| X4 | fails(sound); not manipulation |
| X5 | fails(maintained); not manipulation |
| X6 | fails(maintained); not manipulation |
| X7 | fails(sound); not manipulation |
